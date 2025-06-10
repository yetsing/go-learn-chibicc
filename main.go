package main

import (
	"fmt"
	"os"
	"os/exec"
	"strings"
)

var optS bool
var optCC1 bool
var optHashHashHash bool
var optOutput string

var inputPath string
var tmpfiles []string

func usage(status int) {
	fmt.Fprintf(os.Stderr, "Usage: chibicc [ -o <path> ] <file>\n")
	os.Exit(status)
}

func parseArgs() {
	for i := 1; i < len(os.Args); i++ {
		if os.Args[i] == "-###" {
			optHashHashHash = true
			continue
		}

		if os.Args[i] == "-cc1" {
			optCC1 = true
			continue
		}

		if os.Args[i] == "--help" {
			usage(0)
		}

		if os.Args[i] == "-o" {
			if i+1 >= len(os.Args) {
				usage(1)
			}
			optOutput = os.Args[i+1]
			i++
			continue
		}

		if strings.HasPrefix(os.Args[i], "-o") {
			optOutput = strings.TrimPrefix(os.Args[i], "-o")
			continue
		}

		if os.Args[i] == "-S" {
			optS = true
			continue
		}

		if strings.HasPrefix(os.Args[i], "-") && os.Args[i] != "-" {
			fmt.Fprintf(os.Stderr, "Unknown option: %s\n", os.Args[i])
			panic("Unknown option")
		}

		inputPath = os.Args[i]
	}

	if inputPath == "" {
		fmt.Fprintln(os.Stderr, "No input file specified.")
		usage(1)
	}
}

// Replace file extension
func replaceExtn(tmpl, extn string) string {
	if i := strings.LastIndex(tmpl, "."); i >= 0 {
		return tmpl[:i] + extn
	}
	return tmpl + extn
}

func cleanup() {
	for _, f := range tmpfiles {
		if err := os.Remove(f); err != nil {
			fmt.Fprintf(os.Stderr, "Error removing temporary file %s: %s\n", f, err)
		}
	}
}

func createTmpfile() string {
	f, err := os.CreateTemp("", "chibicc-")
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error creating temporary file: %s\n", err)
		panic("Failed to create temporary file")
	}
	defer f.Close()
	name := f.Name()
	tmpfiles = append(tmpfiles, name)
	return name
}

func runSubprocess(args []string) {
	// If -### is given, dump the subprocess's command line.
	if optHashHashHash {
		fmt.Fprintln(os.Stderr, strings.Join(args, " "))
	}

	cmd := exec.Command(args[0], args[1:]...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	cmd.Stdin = os.Stdin
	if err := cmd.Run(); err != nil {
		fmt.Fprintf(os.Stderr, "Error running command: %s\n", err)
		panic("Subprocess failed")
	}

	// Wait for the subprocess to finish.
	if cmd.ProcessState.ExitCode() != 0 {
		fmt.Fprintf(os.Stderr, "Subprocess exited with non-zero status: %d\n", cmd.ProcessState.ExitCode())
		panic("Subprocess failed")
	}
}

func runCC1(args []string, input string, output string) {
	args = append(args, "-cc1")

	if input != "" {
		args = append(args, input)
	}

	if output != "" {
		args = append(args, "-o", output)
	}

	runSubprocess(args)
}

func cc1() {
	// Tokenize and parse.
	tok := tokenizeFile(inputPath)
	prog := parse(tok)

	// Traverse the AST to emit assembly code.
	var out *os.File
	if optOutput == "" || optOutput == "-" {
		out = os.Stdout
	} else {
		var err error
		out, err = os.Create(optOutput)
		check(err)
	}
	fmt.Fprintf(out, ".file 1 \"%s\"\n", inputPath)
	codegen(prog, out)
}

func assemble(input string, output string) {
	cmd := []string{"as", "-c", input, "-o", output}
	runSubprocess(cmd)
}

func main() {
	defer cleanup()
	parseArgs()

	if optCC1 {
		cc1()
		return
	}

	var output string
	if optOutput != "" {
		output = optOutput
	} else if optS {
		output = replaceExtn(inputPath, ".s")
	} else {
		output = replaceExtn(inputPath, ".o")
	}

	// If -S is given, assembly text is the final output.
	if optS {
		runCC1(os.Args, inputPath, output)
		return
	}

	// Otherwise, run the assembler to assemble our output.
	tmpfile := createTmpfile()
	runCC1(os.Args, inputPath, tmpfile)
	assemble(tmpfile, output)
}
