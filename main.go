package main

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

type FileType int

const (
	FILE_NONE FileType = iota // No file type
	FILE_C                    // C source file
	FILE_ASM                  // Assembly file
	FILE_OBJ                  // Object file
	FILE_AR
	FILE_DSO
)

var includePaths []string
var optFcommon bool = true

var optX FileType
var optInclude []string
var optE bool
var optM bool
var optMD bool
var optMP bool
var optS bool
var optC bool
var optCC1 bool
var optHashHashHash bool
var optMF string
var optMT string
var optO string

var ldExtraArgs []string

var baseFile string
var outputFile string

var inputPaths []string
var tmpfiles []string

func usage(status int) {
	fmt.Fprintf(os.Stderr, "Usage: chibicc [ -o <path> ] <file>\n")
	os.Exit(status)
}

func takeArg(arg string) bool {
	options := []string{"-o", "-I", "-idirafter", "-include", "-x", "-MF", "-MT"}

	for _, opt := range options {
		if arg == opt {
			return true
		}
	}
	return false
}

func addDefaultIncludePaths(argv0 string) {
	// We expect that chibicc-specific include files are installed
	// to ./include relative to argv[0].
	includePaths = append(includePaths, fmt.Sprintf("%s/include", filepath.Dir(argv0)))

	// Add standard include paths.
	includePaths = append(includePaths, "/usr/local/include")
	includePaths = append(includePaths, "/usr/include/x86_64-linux-gnu")
	includePaths = append(includePaths, "/usr/include")
}

func define(name string) {
	idx := strings.IndexRune(name, '=')
	if idx != -1 {
		value := name[idx+1:]
		name = name[:idx]
		defineMacro(name, value)
	} else {
		defineMacro(name, "1")
	}
}

func parseOptX(arg string) FileType {
	switch arg {
	case "c":
		return FILE_C
	case "assembler":
		return FILE_ASM
	case "none":
		return FILE_NONE
	}
	panic(fmt.Sprintf("<command line>: unknown argument for -x: %s", arg))
}

func quoteMakefile(s string) string {
	var sb strings.Builder
	for i, r := range s {
		switch r {
		case '$':
			sb.WriteString("$$")
		case '#':
			sb.WriteString("\\#")
		case ' ', '\t':
			for k := i - 1; k >= 0 && s[k] == '\\'; k-- {
				sb.WriteByte('\\')
			}
			sb.WriteByte('\\')
			sb.WriteRune(r)
		default:
			sb.WriteRune(r)
		}
	}
	return sb.String()
}

func parseArgs() {
	for i := 1; i < len(os.Args); i++ {
		// Make sure that all command line options that take an argument
		// have an argument.
		if takeArg(os.Args[i]) {
			if i+1 >= len(os.Args) {
				usage(1)
			}
			i++
		}
	}

	var idirafter []string

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

		if os.Args[i] == "-fcommon" {
			optFcommon = true
			continue
		}

		if os.Args[i] == "-fno-common" {
			optFcommon = false
			continue
		}

		if os.Args[i] == "-c" {
			optC = true
			continue
		}

		if os.Args[i] == "-E" {
			optE = true
			continue
		}

		if strings.HasPrefix(os.Args[i], "-I") {
			includePaths = append(includePaths, strings.TrimPrefix(os.Args[i], "-I"))
			continue
		}

		if os.Args[i] == "-D" {
			define(os.Args[i+1])
			i++
			continue
		}

		if strings.HasPrefix(os.Args[i], "-D") {
			define(strings.TrimPrefix(os.Args[i], "-D"))
			continue
		}

		if os.Args[i] == "-U" {
			undefMacro(os.Args[i+1])
			i++
			continue
		}

		if strings.HasPrefix(os.Args[i], "-U") {
			undefMacro(strings.TrimPrefix(os.Args[i], "-U"))
			continue
		}

		if os.Args[i] == "-include" {
			optInclude = append(optInclude, os.Args[i+1])
			i++
			continue
		}

		if os.Args[i] == "-x" {
			optX = parseOptX(os.Args[i+1])
			i++
			continue
		}

		if strings.HasPrefix(os.Args[i], "-x") {
			optX = parseOptX(os.Args[i][2:])
			continue
		}

		if strings.HasPrefix(os.Args[i], "-l") {
			inputPaths = append(inputPaths, os.Args[i][2:])
			continue
		}

		if os.Args[i] == "-s" {
			ldExtraArgs = append(ldExtraArgs, "-s")
			continue
		}

		if os.Args[i] == "-M" {
			optM = true
			continue
		}

		if os.Args[i] == "-MF" {
			optMF = os.Args[i+1]
			i++
			continue
		}

		if os.Args[i] == "-MP" {
			optMP = true
			continue
		}

		if os.Args[i] == "-MT" {
			if optMT == "" {
				optMT = os.Args[i+1]
			} else {
				optMT = fmt.Sprintf("%s %s", optMT, os.Args[i+1])
			}
			i++
			continue
		}

		if os.Args[i] == "-MD" {
			optMD = true
			continue
		}

		if os.Args[i] == "-MQ" {
			if optMT == "" {
				optMT = quoteMakefile(os.Args[i+1])
			} else {
				optMT = fmt.Sprintf("%s %s", optMT, quoteMakefile(os.Args[i+1]))
			}
			i++
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

		if os.Args[i] == "-idirafter" {
			idirafter = append(idirafter, os.Args[i+1])
			i++
			continue
		}

		if os.Args[i] == "-hashmap-test" {
			// golang has built-in hashmap, so
			// we don't need to test it.
			os.Exit(0)
		}

		// These options are ignored for now.
		if strings.HasPrefix(os.Args[i], "-O") ||
			strings.HasPrefix(os.Args[i], "-W") ||
			strings.HasPrefix(os.Args[i], "-g") ||
			strings.HasPrefix(os.Args[i], "-std=") ||
			os.Args[i] == "-ffreestanding" ||
			os.Args[i] == "-fno-builtin" ||
			os.Args[i] == "-fno-omit-frame-pointer" ||
			os.Args[i] == "-fno-stack-protector" ||
			os.Args[i] == "-fno-strict-aliasing" ||
			os.Args[i] == "-m64" ||
			os.Args[i] == "-mno-red-zone" ||
			os.Args[i] == "-w" {
			continue
		}

		if strings.HasPrefix(os.Args[i], "-") && os.Args[i] != "-" {
			fmt.Fprintf(os.Stderr, "Unknown option: %s\n", os.Args[i])
			panic("Unknown option")
		}

		inputPaths = append(inputPaths, os.Args[i])
	}

	includePaths = append(includePaths, idirafter...)

	if len(inputPaths) == 0 {
		fmt.Fprintln(os.Stderr, "no input files")
		usage(1)
	}

	// -E implies that the input is the C macro language.
	if optE {
		optX = FILE_C
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
		fmt.Fprintf(os.Stderr, "Error running command(%v): %s\n", args, err)
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

func efprintf(w io.Writer, format string, a ...any) {
	_, err := fmt.Fprintf(w, format, a...)
	check(err)
}

// Print tokens to stdout. Used for -E.
func printTokens(tok *Token) {
	out := openFile(optO)

	line := 1
	for ; tok.kind != TK_EOF; tok = tok.next {
		if line > 1 && tok.atBol {
			efprintf(out, "\n")
		}
		if tok.hasSpace && !tok.atBol {
			efprintf(out, " ")
		}
		efprintf(out, "%s", tok.literal)
		line++
	}
	efprintf(out, "\n")
}

// If -M options is given, the compiler write a list of input files to
// stdout in a format that "make" command can read. This feature is
// used to automate file dependency management.
func printDependencies() {
	path := ""
	if optMF != "" {
		path = optMF
	} else if optMD {
		if optO != "" {
			path = replaceExtn(optO, ".d")
		} else {
			path = replaceExtn(baseFile, ".d")
		}
	} else if optO != "" {
		path = optO
	} else {
		path = "-"
	}

	out := openFile(path)
	if optMT != "" {
		fmt.Fprintf(out, "%s:", optMT)
	} else {
		fmt.Fprintf(out, "%s:", quoteMakefile(replaceExtn(filepath.Base(baseFile), ".o")))
	}

	files := getInputFiles()

	for _, file := range files {
		fmt.Fprintf(out, " \\\n  %s", file.name)
	}
	fmt.Fprintf(out, "\n\n")

	if optMP {
		for i := 1; i < len(files); i++ {
			fmt.Fprintf(out, "%s:\n\n", quoteMakefile(files[i].name))
		}
	}
}

func mustTokenizeFile(path string) *Token {
	tok := tokenizeFile(path)
	if tok == nil {
		fmt.Fprintf(os.Stderr, "Failed to tokenize file: %s\n", path)
		panic("Tokenization failed")
	}
	return tok
}

func appendTokens(tok1 *Token, tok2 *Token) *Token {
	if tok1 == nil || tok1.kind == TK_EOF {
		return tok2
	}

	t := tok1
	for t.next.kind != TK_EOF {
		t = t.next
	}
	t.next = tok2
	return tok1
}

func cc1() {
	var tok *Token

	// Process -include option
	for _, incl := range optInclude {
		var path string
		if fileExists(incl) {
			path = incl
		} else {
			path = searchIncludePaths(incl)
			if path == "" {
				fmt.Fprintf(os.Stderr, "include file not found: %s\n", incl)
				panic("Include file not found")
			}
		}

		tok2 := mustTokenizeFile(path)
		tok = appendTokens(tok, tok2)
	}

	// Tokenize and parse.
	tok2 := mustTokenizeFile(baseFile)
	tok = appendTokens(tok, tok2)
	tok = preprocess(tok)

	// If -M or -MD are given, print file dependencies.
	if optM || optMD {
		printDependencies()
		if optM {
			return
		}
	}

	// If -E is given, print out preprocessed C code as a result.
	if optE {
		printTokens(tok)
		return
	}

	prog := parse(tok)

	// Open a temporary output buffer.
	var buf bytes.Buffer

	// Traverse the AST to emit assembly code.
	codegen(prog, &buf)

	out := openFile(outputFile)
	defer out.Close()
	if _, err := out.Write(buf.Bytes()); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing to output file: %s\n", err)
		// panic("Failed to write output")
	}
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

	arr = append(arr, ldExtraArgs...)

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

func getFileType(filename string) FileType {
	if optX != FILE_NONE {
		return optX
	}

	if strings.HasSuffix(filename, ".a") {
		return FILE_AR
	}
	if strings.HasSuffix(filename, ".so") {
		return FILE_DSO
	}
	if strings.HasSuffix(filename, ".o") {
		return FILE_OBJ
	}
	if strings.HasSuffix(filename, ".c") {
		return FILE_C
	}
	if strings.HasSuffix(filename, ".s") {
		return FILE_ASM
	}

	panic(fmt.Sprintf("<command line>: unknown file extension: %s", filename))
}

func main() {
	defer cleanup()
	initMacros()
	parseArgs()

	if optCC1 {
		addDefaultIncludePaths(os.Args[0])
		cc1()
		return
	}

	if len(inputPaths) > 1 && optO != "" && (optC || optS || optE) {
		fmt.Fprintf(os.Stderr, "cannot specify '-o' with '-c,' '-S' or '-E' with multiple files\n")
		panic("Invalid argument combination")
	}

	ldArgs := []string{}

	for _, input := range inputPaths {
		if strings.HasPrefix(input, "-l") {
			// If the input starts with -l, it is a library name.
			ldArgs = append(ldArgs, input)
			continue
		}

		var output string
		if optO != "" {
			output = optO
		} else if optS {
			output = replaceExtn(input, ".s")
		} else {
			output = replaceExtn(input, ".o")
		}

		ftype := getFileType(input)

		// Handle .o or .a
		if ftype == FILE_OBJ || ftype == FILE_AR || ftype == FILE_DSO {
			ldArgs = append(ldArgs, input)
			continue
		}

		// Handle .s
		if ftype == FILE_ASM {
			if !optS {
				assemble(input, output)
			}
			continue
		}

		if ftype != FILE_C {
			panic(fmt.Sprintf("unknown file extension: %s", input))
		}

		// Just preprocess
		if optE || optM {
			runCC1(os.Args, input, "")
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
