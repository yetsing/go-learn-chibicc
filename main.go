package main

import (
	"fmt"
	"os"
	"strconv"
	"unicode"
)

var currentInput string

func check(err error) {
	if err != nil {
		panic(err)
	}
}

func errorAt(pos int, format string, args ...interface{}) {
	fmt.Println(currentInput)
	for i := 0; i < pos; i++ {
		fmt.Print(" ")
	}
	fmt.Printf("^ ")
	fmt.Printf(format, args...)
	fmt.Println()
	os.Exit(1)
}

func errorTok(tok *Token, format string, args ...interface{}) {
	errorAt(tok.pos, format, args...)
}

func ispunct(ch rune) bool {
	return unicode.Is(unicode.Punct, ch)
}

func sout(format string, args ...interface{}) {
	fmt.Printf(format, args...)
}

// #region Tokenizer
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
	pos     int
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

func NewToken(kind TokenKind, literal string, pos int) *Token {
	return &Token{
		kind:    kind,
		next:    nil,
		val:     0,
		literal: literal,
		pos:     pos,
	}
}

func tokenize() *Token {
	input := currentInput
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

		// Handle punctuation
		if ispunct(rune(ch)) {
			cur.next = NewToken(TK_PUNCT, string(ch), start)
			cur = cur.next
			p++
			continue
		}

		errorAt(p, "unexpected character: '%c'", ch)
	}
	cur.next = NewToken(TK_EOF, "", p)
	return head.next
}

// #endregion

// #region Parser
var gtok *Token

type NodeKind int

const (
	ND_ADD NodeKind = iota
	ND_SUB
	ND_MUL
	ND_DIV
	ND_NUM
)

// AST node type
type Node struct {
	kind NodeKind // Node kind
	lhs  *Node    // Left-hand side
	rhs  *Node    // Right-hand side
	val  int      // Used if kind is ND_NUM
}

func NewNode(kind NodeKind) *Node {
	return &Node{
		kind: kind,
		lhs:  nil,
		rhs:  nil,
		val:  0,
	}
}

func NewBinary(kind NodeKind, lhs, rhs *Node) *Node {
	return &Node{
		kind: kind,
		lhs:  lhs,
		rhs:  rhs,
		val:  0,
	}
}
func NewNumber(val int) *Node {
	return &Node{
		kind: ND_NUM,
		lhs:  nil,
		rhs:  nil,
		val:  val,
	}
}

// expr = mul ( ('+' | '-') mul)*
func expr() *Node {
	node := mul()
	for {
		if gtok.equal("+") {
			gtok = gtok.next
			node = NewBinary(ND_ADD, node, mul())
			continue
		}
		if gtok.equal("-") {
			gtok = gtok.next
			node = NewBinary(ND_SUB, node, mul())
			continue
		}

		return node
	}
}

// mul = primary ( ('*' | '/') primary)*
func mul() *Node {
	node := primary()
	for {
		if gtok.equal("*") {
			gtok = gtok.next
			node = NewBinary(ND_MUL, node, primary())
			continue
		}
		if gtok.equal("/") {
			gtok = gtok.next
			node = NewBinary(ND_DIV, node, primary())
			continue
		}

		return node
	}
}

// primary = "(" expr ")" | num
func primary() *Node {
	if gtok.equal("(") {
		gtok = gtok.next
		node := expr()
		gtok = gtok.consume(")")
		return node
	}

	if gtok.kind == TK_NUM {
		node := NewNumber(gtok.getNumber())
		gtok = gtok.next
		return node
	}

	errorTok(gtok, "expected an expression")
	return nil
}

// #endregion

// #region Code generator
var depth int

func push() {
	sout("  push %%rax\n")
	depth++
}

func pop(arg string) {
	sout("  pop %s\n", arg)
	depth--
}

func genExpr(node *Node) {
	if node.kind == ND_NUM {
		sout("  mov $%d, %%rax\n", node.val)
		return
	}

	genExpr(node.lhs)
	push()
	genExpr(node.rhs)
	pop("%rdi")

	switch node.kind {
	case ND_ADD:
		sout("  add %%rdi, %%rax\n")
		return
	case ND_SUB:
		sout("  sub %%rdi, %%rax\n")
		return
	case ND_MUL:
		sout("  imul %%rdi, %%rax\n")
		return
	case ND_DIV:
		sout("  cqo\n")
		sout("  idiv %%rdi\n")
	default:
		errorTok(gtok, "unknown node kind: %d", node.kind)
	}
}

// #endregion

func main() {
	args := os.Args
	if len(args) != 2 {
		fmt.Println("Usage: ./chibicc <expression>")
		return
	}

	currentInput = args[1]
	tok := tokenize()
	gtok = tok
	node := expr()
	if gtok.kind != TK_EOF {
		errorTok(gtok, "extra tokens at the end")
	}

	sout("  .global main\n")
	sout("main:\n")

	// Traverse the AST to emit assembly
	genExpr(node)
	sout("  ret\n")

	if depth != 0 {
		panic("stack depth mismatch")
	}
}
