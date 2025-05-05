package main

import (
	"fmt"
	"os"
	"strconv"
)

func check(err error) {
	if err != nil {
		panic(err)
	}
}

func errorf(format string, args ...interface{}) {
	panic(fmt.Sprintf(format, args...))
}

// #region Token
type TokenKind int

const (
	TK_PUNCT TokenKind = iota
	TK_NUM
	TK_EOF
)

type Token struct {
	kind    TokenKind
	next    *Token
	val     int
	literal string
}

func (t *Token) equal(op string) bool {
	return t.literal == op
}

func (t *Token) consume(op string) *Token {
	if !t.equal(op) {
		errorf("expected '%s', but got '%s'", op, t.literal)
	}
	return t.next
}

func (t *Token) getNumber() int {
	if t.kind != TK_NUM {
		errorf("expected number, but got '%s'", t.literal)
	}
	return t.val
}

func NewToken(kind TokenKind, literal string) *Token {
	return &Token{
		kind:    kind,
		next:    nil,
		val:     0,
		literal: literal,
	}
}

func tokenize(input string) *Token {
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
		if ch >= '0' && ch <= '9' {
			start := p
			for p < len(input) && input[p] >= '0' && input[p] <= '9' {
				p++
			}
			numStr := input[start:p]
			cur.next = NewToken(TK_NUM, numStr)
			val, err := strconv.Atoi(numStr)
			check(err)
			cur.next.val = val
			cur = cur.next
			continue
		}

		// Handle punctuation
		if ch == '+' || ch == '-' {
			cur.next = NewToken(TK_PUNCT, string(ch))
			cur = cur.next
			p++
			continue
		}

		errorf("unexpected character: '%c'", ch)
	}
	cur.next = NewToken(TK_EOF, "")
	return head.next
}

// #endregion

func sout(format string, args ...interface{}) {
	fmt.Printf(format, args...)
}

func main() {
	args := os.Args
	if len(args) != 2 {
		fmt.Println("Usage: ./chibicc <expression>")
		return
	}

	tok := tokenize(args[1])

	sout("  .global main\n")
	sout("main:\n")

	// The first token must be a number
	sout("  mov $%d, %%rax\n", tok.getNumber())
	tok = tok.next

	// next token must be a '+' or '-'
	for tok.kind != TK_EOF {
		if tok.equal("+") {
			sout("  add $%d, %%rax\n", tok.next.getNumber())
			tok = tok.next.next
			continue
		}

		tok = tok.consume("-")
		sout("  sub $%d, %%rax\n", tok.getNumber())
		tok = tok.next
	}

	sout("  ret\n")
}
