package main

import (
	"fmt"
	"os"
	"os/exec"
	"strings"
)

var optCC1 bool
var optHashHashHash bool
var optOutput string
var optInput string

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

		if strings.HasPrefix(os.Args[i], "-") && os.Args[i] != "-" {
			fmt.Fprintf(os.Stderr, "Unknown option: %s\n", os.Args[i])
			os.Exit(1)
		}

		optInput = os.Args[i]
	}

	if optInput == "" {
		fmt.Fprintln(os.Stderr, "No input file specified.")
		usage(1)
	}
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
		os.Exit(1)
	}

	// Wait for the subprocess to finish.
	if cmd.ProcessState.ExitCode() != 0 {
		fmt.Fprintf(os.Stderr, "Subprocess exited with non-zero status: %d\n", cmd.ProcessState.ExitCode())
		os.Exit(1)
	}
}

func runCC1(args []string) {
	args = append(args, "-cc1")
	runSubprocess(args)
}

func cc1() {
	// Tokenize and parse.
	tok := tokenizeFile(optInput)
	prog := parse(tok)

	// Traverse the AST to emit assembly code.
	out, err := os.Create(optOutput)
	check(err)
	fmt.Fprintf(out, ".file 1 \"%s\"\n", optInput)
	codegen(prog, out)
}

func main() {
	parseArgs()

	if optCC1 {
		cc1()
		return
	}

	runCC1(os.Args)
}
