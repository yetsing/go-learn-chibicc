package main

// #region Parser
var gtok *Token

type NodeKind int

const (
	ND_ADD       NodeKind = iota // +
	ND_SUB                       // -
	ND_MUL                       // *
	ND_DIV                       // /
	ND_NEG                       // unary -
	ND_EQ                        // ==
	ND_NE                        // !=
	ND_LT                        // <
	ND_LE                        // <=
	ND_EXPR_STMT                 // Expression statement
	ND_NUM                       // Integer
)

// NodeKind string
func (nk NodeKind) String() string {
	switch nk {
	case ND_ADD:
		return "ND_ADD"
	case ND_SUB:
		return "ND_SUB"
	case ND_MUL:
		return "ND_MUL"
	case ND_DIV:
		return "ND_DIV"
	case ND_NEG:
		return "ND_NEG"
	case ND_EQ:
		return "ND_EQ"
	case ND_NE:
		return "ND_NE"
	case ND_LT:
		return "ND_LT"
	case ND_LE:
		return "ND_LE"
	case ND_EXPR_STMT:
		return "ND_EXPR_STMT"
	case ND_NUM:
		return "ND_NUM"
	default:
		panic("Unknown NodeKind")
	}
}

// AST node type
// all nodes are linked in a list
type Node struct {
	kind NodeKind // Node kind
	next *Node    // Next node in the list
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

// stmt = expr-stmt
func stmt() *Node {
	return exprStmt()
}

// expr-stmt = expr ";"
func exprStmt() *Node {
	node := NewUnary(ND_EXPR_STMT, expr())
	gtok = gtok.consume(";")
	return node
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

	var head Node
	cur := &head
	for gtok.kind != TK_EOF {
		cur.next = stmt()
		cur = cur.next
	}
	return head.next
}
