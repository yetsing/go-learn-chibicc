package main

import (
	"fmt"
	"os"
)

var optOutput string
var optInput string

func usage(status int) {
	fmt.Fprintf(os.Stderr, "Usage: chibicc [ -o <path> ] <file>\n")
	os.Exit(status)
}

func parseArgs() {
	for i := 1; i < len(os.Args); i++ {
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

		optInput = os.Args[i]
	}

	if optInput == "" {
		fmt.Fprintln(os.Stderr, "No input file specified.")
		usage(1)
	}
}

func main() {
	parseArgs()

	// Tokenize and parse.
	tok := tokenizeFile(optInput)
	prog := parse(tok)

	// Traverse the AST to emit assembly code.
	out, err := os.Create(optOutput)
	check(err)
	codegen(prog, out)

}
