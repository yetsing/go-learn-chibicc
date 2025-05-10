package main

// #region Local variable

// Local variable
type Obj struct {
	next   *Obj   // Next local variable
	name   string // Variable name
	ty     *Type  // Variable type
	offset int    // Offset from RBP
}

// All local variable instances created during parsing are
// accumulated to this list.
// 所有的本地变量通过链表连接在一起
var locals *Obj

// Find a local variable by name
func findVar(name string) *Obj {
	for l := locals; l != nil; l = l.next {
		if l.name == name {
			return l
		}
	}
	return nil
}

// Create a new local variable
func newLVar(name string, ty *Type) *Obj {
	l := &Obj{
		name:   name,
		offset: 0,
		next:   locals,
		ty:     ty,
	}
	locals = l
	return l
}

// #endregion

// #region AST Node

// Function 所有的函数都通过链表连接在一起
type Function struct {
	next   *Function
	name   string // Function name
	params *Obj   // Function parameters

	body      *Node // Function body
	locals    *Obj  // Local variables
	stackSize int   // Stack size
}

type NodeKind int

// AST node kinds
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
	ND_ASSIGN                    // =
	ND_ADDR                      // unary &
	ND_DEREF                     // unary *
	ND_RETURN                    // return
	ND_IF                        // if
	ND_FOR                       // for or while
	ND_BLOCK                     // Block { ... }
	ND_FUNCALL                   // Function call
	ND_EXPR_STMT                 // Expression statement
	ND_VAR                       // Variable
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
	case ND_ASSIGN:
		return "ND_ASSIGN"
	case ND_ADDR:
		return "ND_ADDR"
	case ND_DEREF:
		return "ND_DEREF"
	case ND_RETURN:
		return "ND_RETURN"
	case ND_IF:
		return "ND_IF"
	case ND_FOR:
		return "ND_FOR"
	case ND_BLOCK:
		return "ND_BLOCK"
	case ND_FUNCALL:
		return "ND_FUNCALL"
	case ND_EXPR_STMT:
		return "ND_EXPR_STMT"
	case ND_VAR:
		return "ND_VAR"
	case ND_NUM:
		return "ND_NUM"
	default:
		panic("unknown NodeKind")
	}
}

// AST node
// all nodes are linked in a list
type Node struct {
	kind NodeKind // Node kind
	next *Node    // Next node in the list
	ty   *Type    // Type of the node
	tok  *Token   // Representative token

	lhs *Node // Left-hand side
	rhs *Node // Right-hand side

	// "if" or "for" statement
	cond *Node // if/for Condition
	then *Node // if/for Then branch
	els  *Node // if Else branch
	init *Node // for Initialization
	inc  *Node // for Increment

	body *Node // Used if kind is ND_BLOCK

	// Function call
	funcname string
	args     *Node

	variable *Obj // Used if kind is ND_VAR

	val int // Used if kind is ND_NUM
}

func NewNode(kind NodeKind, tok *Token) *Node {
	return &Node{
		kind: kind,
		lhs:  nil,
		rhs:  nil,
		val:  0,
		tok:  tok,
	}
}

func NewBinary(kind NodeKind, lhs, rhs *Node, tok *Token) *Node {
	return &Node{
		kind: kind,
		lhs:  lhs,
		rhs:  rhs,
		val:  0,
		tok:  tok,
	}
}

func NewUnary(kind NodeKind, expr *Node, tok *Token) *Node {
	return &Node{
		kind: kind,
		lhs:  expr,
		rhs:  nil,
		val:  0,
		tok:  tok,
	}
}

func NewNumber(val int, tok *Token) *Node {
	return &Node{
		kind: ND_NUM,
		lhs:  nil,
		rhs:  nil,
		val:  val,
		tok:  tok,
	}
}

func NewVarNode(variable *Obj, tok *Token) *Node {
	return &Node{
		kind:     ND_VAR,
		lhs:      nil,
		rhs:      nil,
		variable: variable,
		tok:      tok,
	}
}

// In C, `+` operator is overloaded to perform the pointer arithmetic.
// If p is a pointer, p+n adds not n but sizeof(*p)*n to the value of p,
// so that p+n points to the location n elements (not bytes) ahead of p.
// In other words, we need to scale an integer value before adding to a
// pointer value. This function takes care of the scaling.
func newAdd(lhs, rhs *Node, tok *Token) *Node {
	addType(lhs)
	addType(rhs)

	// num + num
	if lhs.ty.isInteger() && rhs.ty.isInteger() {
		return NewBinary(ND_ADD, lhs, rhs, tok)
	}

	if lhs.ty.base != nil && rhs.ty.base != nil {
		errorTok(tok, "invalid operands")
	}

	// Canonicalize `num + ptr` to `ptr + num`.
	if lhs.ty.base == nil && rhs.ty.base != nil {
		lhs, rhs = rhs, lhs
	}

	// ptr + num
	rhs = NewBinary(ND_MUL, rhs, NewNumber(8, tok), tok)
	return NewBinary(ND_ADD, lhs, rhs, tok)
}

// Like `+`, `-` is overloaded for the pointer type.
func newSub(lhs, rhs *Node, tok *Token) *Node {
	addType(lhs)
	addType(rhs)

	// num - num
	if lhs.ty.isInteger() && rhs.ty.isInteger() {
		return NewBinary(ND_SUB, lhs, rhs, tok)
	}

	// ptr - num
	if lhs.ty.base != nil && rhs.ty.isInteger() {
		rhs = NewBinary(ND_MUL, rhs, NewNumber(8, tok), tok)
		addType(rhs)
		node := NewBinary(ND_SUB, lhs, rhs, tok)
		node.ty = lhs.ty
		return node
	}

	// ptr - ptr, which returns how many elements are between the two.
	if lhs.ty.base != nil && rhs.ty.base != nil {
		node := NewBinary(ND_SUB, lhs, rhs, tok)
		node.ty = intType()
		return NewBinary(ND_DIV, node, NewNumber(8, tok), tok)
	}

	errorTok(tok, "invalid operands")
	return nil
}

// #endregion

// #region Parser

// #region Token

// 使用全局变量 gtok 来保存当前的 token
var gtok *Token

func tryConsume(s string) bool {
	if gtok.equal(s) {
		gtok = gtok.next
		return true
	}
	return false
}

// #endregion

// declspec = "int"
func declspec() *Type {
	gtok = gtok.consume("int")
	return intType()
}

// type-suffix = ("(" func-params? ")")?
// func-params = param ("," param)*
// param       = declspec declarator
func typeSuffix(ty *Type) *Type {
	if gtok.equal("(") {
		gtok = gtok.next

		var head = Type{}
		cur := &head

		for !gtok.equal(")") {
			if cur != &head {
				gtok = gtok.consume(",")
			}

			// param = declspec declarator
			basety := declspec()
			ty := declarator(basety)
			cur.next = ty
			cur = cur.next
		}

		gtok = gtok.consume(")")
		ty = funcType(ty)
		ty.params = head.next
		return ty
	}
	return ty
}

// declarator = "*"* ident type-suffix
func declarator(ty *Type) *Type {
	for tryConsume("*") {
		ty = pointerTo(ty)
	}

	if gtok.kind != TK_IDENT {
		errorTok(gtok, "expected a variable name")
	}

	name := gtok
	gtok = gtok.next
	ty = typeSuffix(ty)
	ty.name = name
	return ty
}

// declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
func declaration() *Node {
	st := gtok
	basety := declspec()

	var head Node
	cur := &head

	i := 0
	for !gtok.equal(";") {
		if i > 0 {
			gtok = gtok.consume(",")
		}
		i++

		ty := declarator(basety)
		variable := newLVar(ty.name.literal, ty)

		if !gtok.equal("=") {
			continue
		}

		// lhs = rhs
		lhs := NewVarNode(variable, ty.name)
		gtok = gtok.next
		rhs := expr()
		node := NewBinary(ND_ASSIGN, lhs, rhs, st)
		cur.next = NewUnary(ND_EXPR_STMT, node, st)
		cur = cur.next
	}

	node := NewNode(ND_BLOCK, st)
	node.body = head.next
	gtok = gtok.consume(";")
	return node
}

// stmt = "return" expr ";"
// .    | if-stmt
// .    | for-stmt
// .    | while-stmt
// .    | "{" compound-stmt
// .    | expr-stmt
func stmt() *Node {
	if gtok.equal("return") {
		st := gtok
		gtok = gtok.next
		node := NewUnary(ND_RETURN, expr(), st)
		gtok = gtok.consume(";")
		return node
	}

	if gtok.equal("if") {
		return ifStmt()
	}

	if gtok.equal("for") {
		return forStmt()
	}

	if gtok.equal("while") {
		return whileStmt()
	}

	if gtok.equal("{") {
		return compoundStmt()
	}

	return exprStmt()
}

// while-stmt = "while" "(" expr ")" stmt
func whileStmt() *Node {
	st := gtok
	gtok = gtok.consume("while")
	gtok = gtok.consume("(")
	node := NewNode(ND_FOR, st)
	node.cond = expr()
	gtok = gtok.consume(")")
	node.then = stmt()
	return node
}

// for-stmt = "for" "(" expr-stmt expr? ";" expr? ")" stmt
func forStmt() *Node {
	st := gtok
	gtok = gtok.consume("for")
	gtok = gtok.consume("(")
	node := NewNode(ND_FOR, st)

	node.init = exprStmt()
	if !gtok.equal(";") {
		node.cond = expr()
	}
	gtok = gtok.consume(";")

	if !gtok.equal(")") {
		node.inc = expr()
	}
	gtok = gtok.consume(")")

	node.then = stmt()
	return node
}

// if-stmt = "if" "(" expr ")" stmt ("else" stmt)?
func ifStmt() *Node {
	st := gtok
	gtok = gtok.consume("if")
	gtok = gtok.consume("(")
	node := NewNode(ND_IF, st)
	node.cond = expr()
	gtok = gtok.consume(")")
	node.then = stmt()
	if gtok.equal("else") {
		gtok = gtok.next
		node.els = stmt()
	}
	return node
}

// compound-stmt = "{" ( declaration | stmt )*  "}"
func compoundStmt() *Node {
	st := gtok
	gtok = gtok.consume("{")
	var head Node
	cur := &head
	for !gtok.equal("}") {
		if gtok.equal("int") {
			cur.next = declaration()
		} else {
			cur.next = stmt()
		}
		cur = cur.next
		addType(cur)
	}

	node := NewNode(ND_BLOCK, st)
	node.body = head.next
	gtok = gtok.consume("}")
	return node
}

// expr-stmt = expr ";"
func exprStmt() *Node {
	st := gtok
	if gtok.equal(";") {
		gtok = gtok.next
		return NewNode(ND_BLOCK, st)
	}
	node := NewUnary(ND_EXPR_STMT, expr(), st)
	gtok = gtok.consume(";")
	return node
}

// expr = assign
func expr() *Node {
	return assign()
}

// assign = equality ("=" assign)?
func assign() *Node {
	node := equality()
	if gtok.equal("=") {
		st := gtok
		gtok = gtok.next
		node = NewBinary(ND_ASSIGN, node, assign(), st)
	}
	return node
}

// equality = relational ("==" relational | "!=" relational)*
func equality() *Node {
	node := relational()
	for {
		st := gtok
		if gtok.equal("==") {
			gtok = gtok.next
			node = NewBinary(ND_EQ, node, relational(), st)
			continue
		}
		if gtok.equal("!=") {
			gtok = gtok.next
			node = NewBinary(ND_NE, node, relational(), st)
			continue
		}

		return node
	}
}

// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
func relational() *Node {
	node := add()
	for {
		st := gtok
		if gtok.equal("<") {
			gtok = gtok.next
			node = NewBinary(ND_LT, node, add(), st)
			continue
		}
		if gtok.equal("<=") {
			gtok = gtok.next
			node = NewBinary(ND_LE, node, add(), st)
			continue
		}
		if gtok.equal(">") {
			gtok = gtok.next
			node = NewBinary(ND_LT, add(), node, st)
			continue
		}
		if gtok.equal(">=") {
			gtok = gtok.next
			node = NewBinary(ND_LE, add(), node, st)
			continue
		}

		return node
	}
}

// add = mul ("+" mul | "-" mul)*
func add() *Node {
	node := mul()
	for {
		st := gtok
		if gtok.equal("+") {
			gtok = gtok.next
			node = newAdd(node, mul(), st)
			continue
		}
		if gtok.equal("-") {
			gtok = gtok.next
			node = newSub(node, mul(), st)
			continue
		}

		return node
	}
}

// mul = unary ( ('*' | '/') unary)*
func mul() *Node {
	node := unary()
	for {
		st := gtok
		if gtok.equal("*") {
			gtok = gtok.next
			node = NewBinary(ND_MUL, node, unary(), st)
			continue
		}
		if gtok.equal("/") {
			gtok = gtok.next
			node = NewBinary(ND_DIV, node, unary(), st)
			continue
		}

		return node
	}
}

// unary = ( ("+" | "-" | "*" | "&") unary ) | primary
func unary() *Node {
	if gtok.equal("+") {
		gtok = gtok.next
		return unary()
	}
	st := gtok
	if gtok.equal("-") {
		gtok = gtok.next
		return NewUnary(ND_NEG, unary(), st)
	}

	if gtok.equal("&") {
		gtok = gtok.next
		return NewUnary(ND_ADDR, unary(), st)
	}

	if gtok.equal("*") {
		gtok = gtok.next
		return NewUnary(ND_DEREF, unary(), st)
	}

	return primary()
}

// funcall = ident "(" (assign ("," assign)*)? ")"
func funcall() *Node {
	st := gtok
	gtok = gtok.next.next // skip ident "("

	var head Node
	cur := &head

	for !gtok.equal(")") {
		if cur != &head {
			gtok = gtok.consume(",")
		}
		cur.next = assign()
		cur = cur.next
	}

	gtok = gtok.consume(")")

	node := NewNode(ND_FUNCALL, st)
	node.funcname = st.literal
	node.args = head.next
	return node
}

// primary = "(" expr ")" | ident | funcall | num
func primary() *Node {
	if gtok.equal("(") {
		gtok = gtok.next
		node := expr()
		gtok = gtok.consume(")")
		return node
	}

	st := gtok
	if gtok.kind == TK_IDENT {
		// Function call
		if gtok.next.equal("(") {
			return funcall()
		}

		variable := findVar(gtok.literal)
		if variable == nil {
			errorTok(gtok, "undefined variable: %s", gtok.literal)
		}
		node := NewVarNode(variable, st)
		gtok = gtok.next
		return node
	}

	if gtok.kind == TK_NUM {
		node := NewNumber(gtok.getNumber(), st)
		gtok = gtok.next
		return node
	}

	errorTok(gtok, "expected an expression")
	return nil
}

// 为函数参数创建局部变量
func createParamLvars(param *Type) {
	if param != nil {
		createParamLvars(param.next)
		newLVar(param.name.literal, param)
	}
}

func function() *Function {
	ty := declspec()
	ty = declarator(ty)

	locals = nil

	fn := &Function{}
	fn.name = ty.name.literal
	createParamLvars(ty.params)
	fn.params = locals

	fn.body = compoundStmt()
	fn.locals = locals
	return fn
}

// program = function-definition*
func program() *Function {
	var head Function
	cur := &head

	for gtok.kind != TK_EOF {
		cur.next = function()
		cur = cur.next
	}

	return head.next
}

// #endregion

func parse(tok *Token) *Function {
	gtok = tok
	return program()
}
