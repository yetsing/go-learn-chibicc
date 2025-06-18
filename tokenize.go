package main

import (
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"
	"unicode"
)

// #region util functions

// Input file
var currentFile *File

// A list of all input files
var inputFiles []*File

// True if the current position is at the beginning of a line.
var tAtBol bool

func check(err error) {
	if err != nil {
		panic(err)
	}
}

// Reports an error message in the following format and exit.
//
// foo.c:10: x = y + 1;
// .             ^ <error message here>
func verrorAt(filename string, input string, pos int, format string, args ...interface{}) {
	// Find the line number and column for the error position
	line := 1
	lineStart := 0
	for i := range pos {
		if i >= len(input) {
			break
		}
		if input[i] == '\n' {
			line++
			lineStart = i + 1
		}
	}
	col := pos - lineStart

	// Find the end of the current line
	lineEnd := lineStart
	for lineEnd < len(input) && input[lineEnd] != '\n' {
		lineEnd++
	}

	// Extract the line content
	lineContent := input[lineStart:lineEnd]

	// Print the formatted error location and line content
	n, _ := fmt.Fprintf(os.Stderr, "%s:%d: ", filename, line)
	fmt.Fprintf(os.Stderr, "%s\n", lineContent)

	// Print spaces up to the error position
	fmt.Fprint(os.Stderr, strings.Repeat(" ", col+n))

	// Print caret and error message
	fmt.Fprintf(os.Stderr, "^ ")
	fmt.Fprintf(os.Stderr, format, args...)
	fmt.Fprintln(os.Stderr)
}

func errorAt(pos int, format string, args ...interface{}) {
	verrorAt(currentFile.name, currentFile.contents, pos, format, args...)
	panic("error occurred, exiting")
}

func errorTok(tok *Token, format string, args ...interface{}) {
	verrorAt(tok.file.name, tok.file.contents, tok.pos, format, args...)
	panic("error occurred, exiting")
}

func ispunct(ch rune) bool {
	return unicode.IsPrint(ch) && !unicode.IsLetter(ch) && !unicode.IsDigit(ch) && !unicode.IsSpace(ch)
}

func readFile(filename string) string {
	if filename == "-" {
		// read from stdin
		data, err := io.ReadAll(os.Stdin)
		check(err)
		return string(data)
	} else {
		data, err := os.ReadFile(filename)
		check(err)
		return string(data)
	}
}

// startswith2 is a case-insensitive version of startswith.
func startswith2(s, prefix string) bool {
	if len(s) < len(prefix) {
		return false
	}
	p := s[:len(prefix)]
	return strings.EqualFold(p, prefix)
}

// #endregion

// #region Tokenizer
type TokenKind int

const (
	TK_IDENT   TokenKind = iota // identifiers
	TK_PUNCT                    // punctuation
	TK_KEYWORD                  // keywords
	TK_STR                      // string literals
	TK_NUM                      // numbers literals
	TK_EOF                      // end of file
)

type File struct {
	name     string // File name
	fileNo   int    // File number
	contents string // File contents
}

type Token struct {
	kind    TokenKind
	next    *Token
	literal string

	pos    int
	lineno int

	val  int64
	fval float64
	ty   *Type  // Used if TK_NUM or TK_STR
	str  string // String literal contents

	file  *File // Source location
	atBol bool  // True if this token is at the beginning of a line
}

func (t *Token) equal(op string) bool {
	return t.literal == op
}

func (t *Token) consume(op string) *Token {
	if !t.equal(op) {
		errorTok(t, "expected '%s', but got '%s'", op, t.literal)
	}
	return t.next
}

func (t *Token) getNumber() int64 {
	if t.kind != TK_NUM {
		errorTok(t, "expected number, but got '%s'", t.literal)
	}
	return t.val
}

// Returns true if c is valid as the first character of an identifier.
func isIdent1(ch rune) bool {
	return unicode.IsLetter(ch) || ch == '_'
}

// Returns true if c is valid as a non-first character of an identifier.
func isIdent2(ch rune) bool {
	return isIdent1(ch) || unicode.IsDigit(ch)
}

func readPunct(input string, p int) int {
	kw := []string{
		"<<=", ">>=", "...",
		"==", "!=", "<=", ">=", "->", "+=", "-=", "*=", "/=", "++", "--", "%=", "&=", "|=", "^=", "&&", "||",
		"<<", ">>",
	}
	s := input[p:]
	for _, k := range kw {
		if strings.HasPrefix(s, k) {
			return len(k)
		}
	}
	if ispunct(rune(input[p])) {
		return 1
	}
	return 0
}

func ishexdigit(ch rune) bool {
	return '0' <= ch && ch <= '9' || 'a' <= ch && ch <= 'f' || 'A' <= ch && ch <= 'F'
}

func readEscapedChar(input string, p int) (byte, int) {
	if input[p] >= '0' && input[p] <= '7' {
		// Octal escape sequence
		// Read up to 3 octal digits
		octal := 0
		i := 0
		for ; i < 3 && p+i < len(input) && input[p+i] >= '0' && input[p+i] <= '7'; i++ {
			octal = octal*8 + int(input[p+i]-'0')
		}
		return byte(octal), i
	}

	if input[p] == 'x' {
		// Hexadecimal escape sequence
		p++
		hex := 0
		i := 0
		for ; p+i < len(input) && ishexdigit(rune(input[p+i])); i++ {
			if '0' <= input[p+i] && input[p+i] <= '9' {
				hex = hex*16 + int(input[p+i]-'0')
			} else if 'a' <= input[p+i] && input[p+i] <= 'f' {
				hex = hex*16 + int(input[p+i]-'a'+10)
			} else if 'A' <= input[p+i] && input[p+i] <= 'F' {
				hex = hex*16 + int(input[p+i]-'A'+10)
			}
		}
		return byte(hex), i + 1
	}

	// Escape sequences are defined using themselves here. E.g.
	// '\n' is implemented using '\n'. This tautological definition
	// works because the compiler that compiles our compiler knows
	// what '\n' actually is. In other words, we "inherit" the ASCII
	// code of '\n' from the compiler that compiles our compiler,
	// so we don't have to teach the actual code here.
	//
	// This fact has huge implications not only for the correctness
	// of the compiler but also for the security of the generated code.
	// For more info, read "Reflections on Trusting Trust" by Ken Thompson.
	// https://github.com/rui314/chibicc/wiki/thompson1984.pdf
	switch input[p] {
	case 'a':
		return '\a', 1
	case 'b':
		return '\b', 1
	case 't':
		return '\t', 1
	case 'n':
		return '\n', 1
	case 'v':
		return '\v', 1
	case 'f':
		return '\f', 1
	case 'r':
		return '\r', 1
	// [GNU] \e for the ASCII escape character is a GNU C extension.
	case 'e':
		return 27, 1
	default:
		return byte(input[p]), 1
	}

}

// Find a closing double-quote
func stringLiteralEnd(input string, p int) int {
	for p <= len(input)-1 && input[p] != '"' {
		if input[p] == '\n' {
			errorAt(p, "unclosed string literal")
		}
		if input[p] == '\\' {
			p++
		}
		p++
	}
	if p > len(input)-1 {
		errorAt(p, "unclosed string literal")
	}
	return p
}

func readStringLiteral(input string, p int) *Token {
	start := p
	end := stringLiteralEnd(input, p+1)

	sb := strings.Builder{}
	for p = start + 1; p < end; p++ {
		if input[p] == '\\' {
			b, n := readEscapedChar(input, p+1)
			sb.WriteByte(b)
			p += n
		} else {
			sb.WriteByte(input[p])
		}
	}

	tok := NewToken(TK_STR, input[start:end+1], start)
	tok.str = sb.String()
	tok.ty = arrayOf(charType(), len(tok.str)+1) // +1 for null terminator
	return tok
}

func NewToken(kind TokenKind, literal string, pos int) *Token {
	v := tAtBol
	tAtBol = false
	return &Token{
		kind:    kind,
		next:    nil,
		val:     0,
		literal: literal,
		pos:     pos,
		file:    currentFile,
		atBol:   v,
	}
}

func readCharLiteral(input string, p int) *Token {
	start := p
	p++
	if p >= len(input) {
		errorAt(p, "unclosed character literal")
	}

	var c byte
	if input[p] == '\\' {
		var n int
		c, n = readEscapedChar(input, p+1)
		p += n + 1
	} else {
		c = input[p]
		p++
	}

	if p >= len(input) || input[p] != '\'' {
		errorAt(p, "unclosed character literal")
	}

	tok := NewToken(TK_NUM, input[start:p+1], start)
	tok.val = int64(int8(c))
	tok.ty = intType()
	return tok
}

func hasCasePrefix(input string, prefix string) bool {
	if len(input) < len(prefix) {
		return false
	}
	start := strings.ToLower(input[:len(prefix)])
	prefix = strings.ToLower(prefix)
	return start == prefix
}

func isNumChar(b byte) bool {
	return (b >= '0' && b <= '9') || (b >= 'a' && b <= 'f') || (b >= 'A' && b <= 'F')
}

func isNumChar2(base int, b byte) bool {
	switch base {
	case 2:
		return b == '0' || b == '1'
	case 8:
		return b >= '0' && b <= '7'
	case 10:
		return b >= '0' && b <= '9'
	case 16:
		return (b >= '0' && b <= '9') || (b >= 'a' && b <= 'f') || (b >= 'A' && b <= 'F')
	default:
		return false
	}
}

func readIntLiteral(input string, start int) *Token {
	p := start

	// Read a binary, octal, decimal or hexadecimal number.
	base := 10
	if hasCasePrefix(input[p:], "0x") && isNumChar(input[p+2]) {
		base = 16
		p += 2
	} else if hasCasePrefix(input[p:], "0b") && isNumChar(input[p+2]) {
		base = 2
		p += 2
	} else if input[p] == '0' {
		// if !isNumChar(input[p+1]) {
		// 	// 0
		// 	tok := NewToken(TK_NUM, input[start:p+1], start)
		// 	tok.val = 0
		// 	return tok
		// }
		if isNumChar(input[p+1]) {
			base = 8
			p++
		}
	}

	numStart := p
	for p < len(input) && isNumChar2(base, input[p]) {
		p++
	}

	val, err := strconv.ParseUint(input[numStart:p], base, 64)
	check(err)

	// Read U, L or LL suffixes.
	l := false
	u := false

	if startswith2(input[p:], "LLU") || startswith2(input[p:], "ULL") {
		p += 3
		l = true
		u = true
	} else if startswith2(input[p:], "UL") || startswith2(input[p:], "LU") {
		p += 2
		l = true
		u = true
	} else if startswith2(input[p:], "LL") {
		p += 2
		l = true
	} else if input[p] == 'L' || input[p] == 'l' {
		p++
		l = true
	} else if input[p] == 'U' || input[p] == 'u' {
		p++
		u = true
	}

	// Infer a type.
	var ty *Type
	if base == 10 {
		if l && u {
			ty = ulongType()
		} else if l {
			ty = longType()
		} else if u {
			val2 := val >> 32
			if val2 != 0 {
				ty = ulongType()
			} else {
				ty = uintType()
			}
		} else {
			val2 := val >> 31
			if val2 != 0 {
				ty = longType()
			} else {
				ty = intType()
			}
		}
	} else {
		if l && u {
			ty = ulongType()
		} else if l {
			val2 := val >> 63
			if val2 != 0 {
				ty = ulongType()
			} else {
				ty = longType()
			}
		} else if u {
			val2 := val >> 32
			if val2 != 0 {
				ty = ulongType()
			} else {
				ty = uintType()
			}
		} else if (val >> 63) != 0 {
			ty = ulongType()
		} else if (val >> 32) != 0 {
			ty = longType()
		} else if (val >> 31) != 0 {
			ty = uintType()
		} else {
			ty = intType()
		}
	}

	tok := NewToken(TK_NUM, input[start:p], start)
	tok.val = int64(val)
	tok.ty = ty
	return tok
}

func readNumber(input string, p int) *Token {
	tok := &Token{}
	if input[p] != '.' {
		// Try to parse as an integer constant.
		tok = readIntLiteral(input, p)
		if !strings.ContainsRune(".eEfF", rune(input[p+len(tok.literal)])) {
			return tok
		}
	}

	numEnd := p + len(tok.literal)
	for numEnd < len(input) && strings.ContainsRune("0123456789.eEp", rune(input[numEnd])) {
		numEnd++
		if numEnd < len(input) && (input[numEnd-1] == 'e' || input[numEnd-1] == 'E') && (input[numEnd] == '+' || input[numEnd] == '-') {
			numEnd++
		}
	}

	// If it's not an integer, it must be a floating point constant.
	val, err := strconv.ParseFloat(input[p:numEnd], 64)
	check(err)

	var ty *Type
	if input[numEnd] == 'f' || input[numEnd] == 'F' {
		numEnd++
		ty = floatType()
	} else if input[numEnd] == 'l' || input[numEnd] == 'L' {
		numEnd++
		ty = doubleType()
	} else {
		ty = doubleType()
	}

	tok = NewToken(TK_NUM, input[p:numEnd], p)
	tok.fval = val
	tok.ty = ty
	return tok
}

var keywords = map[string]TokenKind{
	"return":       TK_KEYWORD,
	"if":           TK_KEYWORD,
	"else":         TK_KEYWORD,
	"for":          TK_KEYWORD,
	"while":        TK_KEYWORD,
	"int":          TK_KEYWORD,
	"sizeof":       TK_KEYWORD,
	"char":         TK_KEYWORD,
	"struct":       TK_KEYWORD,
	"union":        TK_KEYWORD,
	"short":        TK_KEYWORD,
	"long":         TK_KEYWORD,
	"void":         TK_KEYWORD,
	"typedef":      TK_KEYWORD,
	"_Bool":        TK_KEYWORD,
	"enum":         TK_KEYWORD,
	"static":       TK_KEYWORD,
	"goto":         TK_KEYWORD,
	"break":        TK_KEYWORD,
	"continue":     TK_KEYWORD,
	"switch":       TK_KEYWORD,
	"case":         TK_KEYWORD,
	"default":      TK_KEYWORD,
	"extern":       TK_KEYWORD,
	"_Alignof":     TK_KEYWORD,
	"_Alignas":     TK_KEYWORD,
	"do":           TK_KEYWORD,
	"signed":       TK_KEYWORD,
	"unsigned":     TK_KEYWORD,
	"const":        TK_KEYWORD,
	"volatile":     TK_KEYWORD,
	"auto":         TK_KEYWORD,
	"register":     TK_KEYWORD,
	"restrict":     TK_KEYWORD,
	"__restrict":   TK_KEYWORD,
	"__restrict__": TK_KEYWORD,
	"_Noreturn":    TK_KEYWORD,
	"float":        TK_KEYWORD,
	"double":       TK_KEYWORD,
}

func convertKeywords(tok *Token) {
	for t := tok; t != nil; t = t.next {
		if _, ok := keywords[t.literal]; ok {
			t.kind = TK_KEYWORD
		}
	}
}

// Initialize line info for all tokens.
func addLineNumbers(tok *Token) {
	line := 1
	lineStart := 0
	for t := tok; t != nil; t = t.next {
		for i := lineStart; i < t.pos; i++ {
			if currentFile.contents[i] == '\n' {
				line++
				lineStart = i + 1
			}
		}
		t.lineno = line
	}
}

// Tokenize the input string and return a linked list of tokens.
func tokenize(file *File) *Token {
	currentFile = file

	input := file.contents
	var head Token
	cur := &head

	tAtBol = true

	p := 0
	for p < len(input) {
		ch := input[p]

		// Skip line comments.
		if strings.HasPrefix(input[p:], "//") {
			p += 2
			for p < len(input) && input[p] != '\n' {
				p++
			}
			continue
		}

		// Skip block comments.
		if strings.HasPrefix(input[p:], "/*") {
			q := strings.Index(input[p+2:], "*/")
			if q == -1 {
				errorAt(p, "unclosed block comment")
			}
			p += 2 + q + 2
			continue
		}

		// Skip newline.
		if ch == '\n' {
			p++
			tAtBol = true
			continue
		}

		// Skip whitespace characters.
		if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' {
			p++
			continue
		}

		// Handle numbers
		start := p
		if (ch >= '0' && ch <= '9') || (ch == '.' && p+1 < len(input) && (input[p+1] >= '0' && input[p+1] <= '9')) {
			cur.next = readNumber(input, p)
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// Handle string literals
		if ch == '"' {
			cur.next = readStringLiteral(input, p)
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// Handle character literals
		if ch == '\'' {
			cur.next = readCharLiteral(input, p)
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// Handle identifiers or keywords
		if isIdent1(rune(ch)) {
			for p < len(input) && isIdent2(rune(input[p])) {
				p++
			}
			cur.next = NewToken(TK_IDENT, input[start:p], start)
			cur = cur.next
			continue
		}

		// Handle punctuation
		punctLen := readPunct(input, p)
		if punctLen > 0 {
			cur.next = NewToken(TK_PUNCT, input[p:p+punctLen], start)
			cur = cur.next
			p += punctLen
			continue
		}

		errorAt(p, "unexpected character: '%c'", ch)
	}
	cur.next = NewToken(TK_EOF, "", p)
	addLineNumbers(head.next)
	return head.next
}

// #endregion

func getInputFiles() []*File {
	return inputFiles
}

func newFile(name string, fileNo int, contents string) *File {
	return &File{
		name:     name,
		fileNo:   fileNo,
		contents: contents,
	}
}

var fileNo int = 0

func tokenizeFile(filename string) *Token {
	p := readFile(filename)

	file := newFile(filename, fileNo+1, p)

	// Save the filename for assembler .file directive
	inputFiles = append(inputFiles, file)

	fileNo++

	return tokenize(file)
}
