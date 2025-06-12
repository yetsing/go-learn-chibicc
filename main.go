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
var optO string

var baseFile string
var outputFile string

var inputPaths []string
var tmpfiles []string

func usage(status int) {
	fmt.Fprintf(os.Stderr, "Usage: chibicc [ -o <path> ] <file>\n")
	os.Exit(status)
}

func taskArg(arg string) bool {
	return arg == "-o"
}

func parseArgs() {
	for i := 1; i < len(os.Args); i++ {
		// Make sure that all command line options that take an argument
		// have an argument.
		if taskArg(os.Args[i]) {
			if i+1 >= len(os.Args) {
				usage(1)
			}
			i++
		}
	}

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
			optO = os.Args[i+1]
			i++
			continue
		}

		if strings.HasPrefix(os.Args[i], "-o") {
			optO = strings.TrimPrefix(os.Args[i], "-o")
			continue
		}

		if os.Args[i] == "-S" {
			optS = true
			continue
		}

		if os.Args[i] == "-cc1-input" {
			baseFile = os.Args[i+1]
			i++
			continue
		}

		if os.Args[i] == "-cc1-output" {
			outputFile = os.Args[i+1]
			i++
			continue
		}

		if strings.HasPrefix(os.Args[i], "-") && os.Args[i] != "-" {
			fmt.Fprintf(os.Stderr, "Unknown option: %s\n", os.Args[i])
			panic("Unknown option")
		}

		inputPaths = append(inputPaths, os.Args[i])
	}

	if len(inputPaths) == 0 {
		fmt.Fprintln(os.Stderr, "no input files")
		usage(1)
	}
}

func openFile(path string) *os.File {
	if path == "" || path == "-" {
		return os.Stdout
	}
	f, err := os.Create(path)
	if err != nil {
		fmt.Fprintf(os.Stderr, "cannot open output file: %s: %s\n", path, err)
		panic("Failed to open file")
	}
	return f
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
	var args1 []string
	args1 = append(args1, args...)

	args1 = append(args1, "-cc1")

	if input != "" {
		args1 = append(args1, "-cc1-input", input)
	}

	if output != "" {
		args1 = append(args1, "-cc1-output", output)
	}

	runSubprocess(args1)
}

func cc1() {
	// Tokenize and parse.
	tok := tokenizeFile(baseFile)
	prog := parse(tok)

	// Traverse the AST to emit assembly code.
	out := openFile(outputFile)
	defer out.Close()
	_, err := fmt.Fprintf(out, ".file 1 \"%s\"\n", baseFile)
	check(err)
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

	if len(inputPaths) > 1 && optO != "" {
		fmt.Fprintf(os.Stderr, "cannot specify '-o' with multiple files\n")
		panic("Invalid argument combination")
	}

	for _, input := range inputPaths {

		var output string
		if optO != "" {
			output = optO
		} else if optS {
			output = replaceExtn(input, ".s")
		} else {
			output = replaceExtn(input, ".o")
		}

		// If -S is given, assembly text is the final output.
		if optS {
			runCC1(os.Args, input, output)
			continue
		}

		// Otherwise, run the assembler to assemble our output.
		tmpfile := createTmpfile()
		runCC1(os.Args, input, tmpfile)
		assemble(tmpfile, output)
	}
}
