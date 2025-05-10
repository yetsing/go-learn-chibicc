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

func readStringLiteral(input string, p int) *Token {
	start := p
	p++
	for input[p] != '"' {
		if p == len(input)-1 || input[p] == '\n' {
			errorAt(start, "unclosed string literal")
		}
		p++
	}
	tok := NewToken(TK_STR, input[start:p+1], start)
	tok.ty = arrayOf(charType(), p-start)
	tok.str = input[start+1 : p]
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
