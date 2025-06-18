package main

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

var optS bool
var optC bool
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

		if os.Args[i] == "-c" {
			optC = true
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
	if tok == nil {
		fmt.Fprintf(os.Stderr, "Failed to tokenize file: %s\n", baseFile)
		panic("Tokenization failed")
	}

	tok = preprocess(tok)
	prog := parse(tok)

	// Traverse the AST to emit assembly code.
	out := openFile(outputFile)
	defer out.Close()
	codegen(prog, out)
}

func assemble(input string, output string) {
	cmd := []string{"as", "-c", input, "-o", output}
	runSubprocess(cmd)
}

func findFile(pattern string) (string, error) {
	matches, err := filepath.Glob(pattern)
	if err != nil {
		return "", err
	}
	if len(matches) > 0 {
		return matches[len(matches)-1], nil
	}
	return "", nil
}

// Returns true if a given file exists.
func fileExists(path string) bool {
	_, err := os.Stat(path)
	return !os.IsNotExist(err)
}

func findLibpath() string {
	if fileExists("/usr/lib/x86_64-linux-gnu/crti.o") {
		return "/usr/lib/x86_64-linux-gnu"
	}
	if fileExists("/usr/lib64/crti.o") {
		return "/usr/lib64"
	}
	panic("library path not found")
}

func findGCCLibpath() string {
	paths := []string{
		"/usr/lib/gcc/x86_64-linux-gnu/*/crtbegin.o",
		"/usr/lib/gcc/x86_64-pc-linux-gnu/*/crtbegin.o", // For Gentoo
		"/usr/lib/gcc/x86_64-redhat-linux/*/crtbegin.o", // For Fedora
	}

	for _, pattern := range paths {
		path, err := findFile(pattern)
		if err == nil && path != "" {
			return filepath.Dir(path)
		}
	}

	panic("gcc library path is not found")
}

func runLinker(inputs []string, output string) {
	var arr []string

	arr = append(arr, "ld", "-o", output, "-m", "elf_x86_64", "-dynamic-linker", "/lib64/ld-linux-x86-64.so.2")
	libpath := findLibpath()
	gccLibpath := findGCCLibpath()

	arr = append(
		arr,
		fmt.Sprintf("%s/crt1.o", libpath),
		fmt.Sprintf("%s/crti.o", libpath),
		fmt.Sprintf("%s/crtbegin.o", gccLibpath),
		fmt.Sprintf("-L%s", gccLibpath),
		fmt.Sprintf("-L%s", libpath),
		fmt.Sprintf("-L%s/..", libpath),
		"-L/usr/lib64",
		"-L/lib64",
		"-L/usr/lib/x86_64-linux-gnu",
		"-L/usr/lib/x86_64-pc-linux-gnu",
		"-L/usr/lib/x86_64-redhat-linux",
		"-L/usr/lib",
		"-L/lib",
	)

	arr = append(arr, inputs...)

	arr = append(
		arr,
		"-lc",
		"-lgcc",
		"--as-needed",
		"-lgcc_s",
		"--no-as-needed",
		fmt.Sprintf("%s/crtend.o", gccLibpath),
		fmt.Sprintf("%s/crtn.o", libpath),
	)

	runSubprocess(arr)
}

func main() {
	defer cleanup()
	parseArgs()

	if optCC1 {
		cc1()
		return
	}

	if len(inputPaths) > 1 && optO != "" && (optC || optS) {
		fmt.Fprintf(os.Stderr, "cannot specify '-o' with '-c' or '-S' with multiple files\n")
		panic("Invalid argument combination")
	}

	ldArgs := []string{}

	for _, input := range inputPaths {
		var output string
		if optO != "" {
			output = optO
		} else if optS {
			output = replaceExtn(input, ".s")
		} else {
			output = replaceExtn(input, ".o")
		}

		// Handle .o
		if strings.HasSuffix(input, ".o") {
			ldArgs = append(ldArgs, input)
			continue
		}

		// Handle .s
		if strings.HasSuffix(input, ".s") {
			if !optS {
				assemble(input, output)
			}
			continue
		}

		// Just compile
		if optS {
			runCC1(os.Args, input, output)
			continue
		}

		// Compile and assemble
		if optC {
			tmp := createTmpfile()
			runCC1(os.Args, input, tmp)
			assemble(tmp, output)
			continue
		}

		// Compile, assemble, and link
		tmp1 := createTmpfile()
		tmp2 := createTmpfile()
		runCC1(os.Args, input, tmp1)
		assemble(tmp1, tmp2)
		ldArgs = append(ldArgs, tmp2)
		continue
	}

	if len(ldArgs) > 0 {
		output := "a.out"
		if optO != "" {
			output = optO
		}
		runLinker(ldArgs, output)
	}
}
