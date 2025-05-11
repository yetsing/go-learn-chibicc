package main

import (
	"fmt"
	"os"
	"strconv"
	"strings"
	"unicode"
)

// #region util functions
var currentInput string

func check(err error) {
	if err != nil {
		panic(err)
	}
}

func errorf(format string, args ...interface{}) {
	fmt.Fprintf(os.Stderr, format, args...)
	fmt.Fprintln(os.Stderr)
	os.Exit(1)
}

func errorAt(pos int, format string, args ...interface{}) {
	fmt.Fprintln(os.Stderr, currentInput)
	for range pos {
		fmt.Fprint(os.Stderr, " ")
	}
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

func sout(format string, args ...interface{}) {
	fmt.Printf(format, args...)
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
	val     int
	literal string
	pos     int
	ty      *Type  // Used if TK_STR
	str     string // String literal contents
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

func (t *Token) getNumber() int {
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
	s := input[p:]
	if strings.HasPrefix(s, "==") || strings.HasPrefix(s, "!=") ||
		strings.HasPrefix(s, "<=") || strings.HasPrefix(s, ">=") {
		return 2
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
		for i := 0; i < 3 && p+i < len(input) && input[p+i] >= '0' && input[p+i] <= '7'; i++ {
			octal = octal*8 + int(input[p+i]-'0')
		}
		return byte(octal), 3
	}

	if input[p] == 'x' {
		// Hexadecimal escape sequence
		p++
		hex := 0
		for i := 0; p+i < len(input) && ishexdigit(rune(input[p+i])); i++ {
			if '0' <= input[p+i] && input[p+i] <= '9' {
				hex = hex*16 + int(input[p+i]-'0')
			} else if 'a' <= input[p+i] && input[p+i] <= 'f' {
				hex = hex*16 + int(input[p+i]-'a'+10)
			} else if 'A' <= input[p+i] && input[p+i] <= 'F' {
				hex = hex*16 + int(input[p+i]-'A'+10)
			}
		}
		return byte(hex), 3
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
		return '\a', 2
	case 'b':
		return '\b', 2
	case 't':
		return '\t', 2
	case 'n':
		return '\n', 2
	case 'v':
		return '\v', 2
	case 'f':
		return '\f', 2
	case 'r':
		return '\r', 2
	// [GNU] \e for the ASCII escape character is a GNU C extension.
	case 'e':
		return 27, 2
	default:
		return input[p], 2
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
			p += n - 1
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

var keywords = map[string]TokenKind{
	"return": TK_KEYWORD,
	"if":     TK_KEYWORD,
	"else":   TK_KEYWORD,
	"for":    TK_KEYWORD,
	"while":  TK_KEYWORD,
	"int":    TK_KEYWORD,
	"sizeof": TK_KEYWORD,
	"char":   TK_KEYWORD,
}

func convertKeywords(tok *Token) {
	for t := tok; t != nil; t = t.next {
		if _, ok := keywords[t.literal]; ok {
			t.kind = TK_KEYWORD
		}
	}
}

// #endregion

// Tokenize the input string and return a linked list of tokens.
func tokenize(input string) *Token {
	currentInput = input
	var head Token
	cur := &head

	p := 0
	for p < len(input) {
		ch := input[p]

		// Skip whitespace
		if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' {
			p++
			continue
		}

		// Handle numbers
		start := p
		if ch >= '0' && ch <= '9' {
			start := p
			for p < len(input) && input[p] >= '0' && input[p] <= '9' {
				p++
			}
			numStr := input[start:p]
			cur.next = NewToken(TK_NUM, numStr, start)
			val, err := strconv.Atoi(numStr)
			check(err)
			cur.next.val = val
			cur = cur.next
			continue
		}

		// Handle string literals
		if ch == '"' {
			cur.next = readStringLiteral(input, p)
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
	convertKeywords(head.next)
	return head.next
}
