package main

// #region Parser
var gtok *Token

type NodeKind int

const (
	ND_ADD NodeKind = iota // +
	ND_SUB                 // -
	ND_MUL                 // *
	ND_DIV                 // /
	ND_NEG                 // unary -
	ND_EQ                  // ==
	ND_NE                  // !=
	ND_LT                  // <
	ND_LE                  // <=
	ND_NUM                 // Integer
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

func NewUnary(kind NodeKind, expr *Node) *Node {
	return &Node{
		kind: kind,
		lhs:  expr,
		rhs:  nil,
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

// expr = equality
func expr() *Node {
	return equality()
}

// equality = relational ("==" relational | "!=" relational)*
func equality() *Node {
	node := relational()
	for {
		if gtok.equal("==") {
			gtok = gtok.next
			node = NewBinary(ND_EQ, node, relational())
			continue
		}
		if gtok.equal("!=") {
			gtok = gtok.next
			node = NewBinary(ND_NE, node, relational())
			continue
		}

		return node
	}
}

// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
func relational() *Node {
	node := add()
	for {
		if gtok.equal("<") {
			gtok = gtok.next
			node = NewBinary(ND_LT, node, add())
			continue
		}
		if gtok.equal("<=") {
			gtok = gtok.next
			node = NewBinary(ND_LE, node, add())
			continue
		}
		if gtok.equal(">") {
			gtok = gtok.next
			node = NewBinary(ND_LT, add(), node)
			continue
		}
		if gtok.equal(">=") {
			gtok = gtok.next
			node = NewBinary(ND_LE, add(), node)
			continue
		}

		return node
	}
}

// add = mul ("+" mul | "-" mul)*
func add() *Node {
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

// mul = unary ( ('*' | '/') unary)*
func mul() *Node {
	node := unary()
	for {
		if gtok.equal("*") {
			gtok = gtok.next
			node = NewBinary(ND_MUL, node, unary())
			continue
		}
		if gtok.equal("/") {
			gtok = gtok.next
			node = NewBinary(ND_DIV, node, unary())
			continue
		}

		return node
	}
}

// unary = ( ("+" | "-") unary ) | primary
func unary() *Node {
	if gtok.equal("+") {
		gtok = gtok.next
		return unary()
	}
	if gtok.equal("-") {
		gtok = gtok.next
		return NewUnary(ND_NEG, unary())
	}

	return primary()
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

func parse(tok *Token) *Node {
	gtok = tok
	// Parse the expression
	node := expr()

	// Check for extra tokens at the end
	if gtok.kind != TK_EOF {
		errorTok(gtok, "extra tokens at the end")
	}

	return node
}
