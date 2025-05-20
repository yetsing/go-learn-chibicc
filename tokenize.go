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
var currentFilename string
var currentInput string

func check(err error) {
	if err != nil {
		panic(err)
	}
}

// Reports an error message in the following format and exit.
//
// foo.c:10: x = y + 1;
// .             ^ <error message here>
func errorAt(pos int, format string, args ...interface{}) {
	// Find the line number and column for the error position
	line := 1
	lineStart := 0
	for i := range pos {
		if i >= len(currentInput) {
			break
		}
		if currentInput[i] == '\n' {
			line++
			lineStart = i + 1
		}
	}
	col := pos - lineStart

	// Find the end of the current line
	lineEnd := lineStart
	for lineEnd < len(currentInput) && currentInput[lineEnd] != '\n' {
		lineEnd++
	}

	// Extract the line content
	lineContent := currentInput[lineStart:lineEnd]

	// Print the formatted error location and line content
	n, _ := fmt.Fprintf(os.Stderr, "%s:%d: ", currentFilename, line)
	fmt.Fprintf(os.Stderr, "%s\n", lineContent)

	// Print spaces up to the error position
	fmt.Fprint(os.Stderr, strings.Repeat(" ", col+n))

	// Print caret and error message
	fmt.Fprintf(os.Stderr, "^ ")
	fmt.Fprintf(os.Stderr, format, args...)
	fmt.Fprintln(os.Stderr)
	os.Exit(1)
}

func errorTok(tok *Token, format string, args ...interface{}) {
	errorAt(tok.pos, format, args...)
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

type Token struct {
	kind    TokenKind
	next    *Token
	literal string

	pos    int
	lineno int

	val int64
	ty  *Type  // Used if TK_STR
	str string // String literal contents
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
	kw := []string{"==", "!=", "<=", ">=", "->", "+=", "-=", "*=", "/=", "++", "--", "%=", "&=", "|=", "^=", "&&", "||"}
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
	tok.ty = arrayOf(charType(), p-start)
	tok.str = sb.String()
	return tok
}

func NewToken(kind TokenKind, literal string, pos int) *Token {
	return &Token{
		kind:    kind,
		next:    nil,
		val:     0,
		literal: literal,
		pos:     pos,
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

func readIntLiteral(input string, start int) *Token {
	p := start

	base := 10
	if hasCasePrefix(input[p:], "0x") && isNumChar(input[p+2]) {
		base = 16
		p += 2
	} else if hasCasePrefix(input[p:], "0b") && isNumChar(input[p+2]) {
		base = 2
		p += 2
	} else if input[p] == '0' {
		if !isNumChar(input[p+1]) {
			// 0
			tok := NewToken(TK_NUM, input[start:p+1], start)
			tok.val = 0
			return tok
		}
		base = 8
		p++
	}

	numStart := p
	for p < len(input) && isNumChar(input[p]) {
		p++
	}

	val, err := strconv.ParseInt(input[numStart:p], base, 64)
	check(err)
	tok := NewToken(TK_NUM, input[start:p], start)
	tok.val = val
	return tok
}

var keywords = map[string]TokenKind{
	"return":   TK_KEYWORD,
	"if":       TK_KEYWORD,
	"else":     TK_KEYWORD,
	"for":      TK_KEYWORD,
	"while":    TK_KEYWORD,
	"int":      TK_KEYWORD,
	"sizeof":   TK_KEYWORD,
	"char":     TK_KEYWORD,
	"struct":   TK_KEYWORD,
	"union":    TK_KEYWORD,
	"short":    TK_KEYWORD,
	"long":     TK_KEYWORD,
	"void":     TK_KEYWORD,
	"typedef":  TK_KEYWORD,
	"_Bool":    TK_KEYWORD,
	"enum":     TK_KEYWORD,
	"static":   TK_KEYWORD,
	"goto":     TK_KEYWORD,
	"break":    TK_KEYWORD,
	"continue": TK_KEYWORD,
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
			if currentInput[i] == '\n' {
				line++
				lineStart = i + 1
			}
		}
		t.lineno = line
	}
}

// Tokenize the input string and return a linked list of tokens.
func tokenize(filename, input string) *Token {
	currentFilename = filename
	currentInput = input
	var head Token
	cur := &head

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

		// Skip whitespace
		if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' {
			p++
			continue
		}

		// Handle numbers
		start := p
		if ch >= '0' && ch <= '9' {
			cur.next = readIntLiteral(input, p)
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
	convertKeywords(head.next)
	return head.next
}

// #endregion

func tokenizeFile(filename string) *Token {
	return tokenize(filename, readFile(filename))
}
