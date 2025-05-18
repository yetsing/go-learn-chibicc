package main

import "fmt"

// #region Scope

// Scope for local, global variables or typedefs.
type VarScope struct {
	next     *VarScope // Next scope
	name     string    // Scope name
	variable *Obj      // Variable
	typedef  *Type     // Typedef
}

// Scope for struct or union tags (结构体/union 名字)
type TagScope struct {
	next *TagScope // Next scope
	name string    // Tag name
	ty   *Type     // Type
}

// Represents a block scope.
type Scope struct {
	next *Scope // Next scope

	// C has two block scopes; one is for variables and the other is
	// for struct tags.
	vars *VarScope
	tags *TagScope
}

// Variable attributes such as typedef or extern.
type VarAttr struct {
	isTypedef bool
}

var scope = &Scope{}

func enterScope() {
	s := &Scope{}
	s.next = scope
	scope = s
}

func leaveScope() {
	scope = scope.next
}

// #endregion

// #region Local variable

// Variable or function
type Obj struct {
	next    *Obj   // Next local variable
	name    string // Variable name
	ty      *Type  // Variable type
	isLocal bool   // local or global/function

	// Local variable
	offset int // Offset from RBP

	// Global variable or function
	isFunction   bool
	isDefinition bool

	// Global variable
	initData string

	// Function
	params    *Obj
	body      *Node
	locals    *Obj
	stackSize int // Stack size
}

// All local variable instances created during parsing are
// accumulated to this list.
// 所有的本地变量通过链表连接在一起
var locals *Obj

// Likewise, global variables are accumulated to this list.
var globals *Obj

// Points to the function object the parser is currently parsing.
var pcurrentFn *Obj

// Find a local variable by name
func findVar(name string) *VarScope {
	for sc := scope; sc != nil; sc = sc.next {
		for vsc := sc.vars; vsc != nil; vsc = vsc.next {
			if vsc.name == name {
				return vsc
			}
		}
	}

	return nil
}

func findTag(tok *Token) *Type {
	// 第一层链表是 scope
	for sc := scope; sc != nil; sc = sc.next {
		// 第二层链表是 scopy 里面的 tag
		for vsc := sc.tags; vsc != nil; vsc = vsc.next {
			if vsc.name == tok.literal {
				return vsc.ty
			}
		}
	}

	return nil
}

// Create a new local variable
func newLVar(name string, ty *Type) *Obj {
	l := &Obj{
		name:    name,
		offset:  0,
		next:    locals,
		ty:      ty,
		isLocal: true,
	}
	pushScope(name).variable = l
	locals = l
	return l
}

func newGVar(name string, ty *Type) *Obj {
	g := &Obj{
		name:    name,
		next:    globals,
		ty:      ty,
		isLocal: false,
	}
	pushScope(name).variable = g
	globals = g
	return g
}

var uid int = 0

func newUniqueName() string {
	s := fmt.Sprintf(".L..%d", uid)
	uid++
	return s
}

func newAnonGvar(ty *Type) *Obj {
	return newGVar(newUniqueName(), ty)
}

func newStringLiteral(s string, ty *Type) *Obj {
	variable := newAnonGvar(ty)
	variable.initData = s
	return variable
}

func findTypedef(tok *Token) *Type {
	if tok.kind == TK_IDENT {
		sc := findVar(tok.literal)
		if sc != nil {
			return sc.typedef
		}
	}
	return nil
}

// Struct member
type Member struct {
	next   *Member // Next member
	ty     *Type
	name   *Token
	offset int
}

// #endregion

// #region AST Node

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
	ND_COMMA                     // ,
	ND_MEMBER                    // . (struct member access)
	ND_ADDR                      // unary &
	ND_DEREF                     // unary *
	ND_RETURN                    // return
	ND_IF                        // if
	ND_FOR                       // for or while
	ND_BLOCK                     // Block { ... }
	ND_FUNCALL                   // Function call
	ND_EXPR_STMT                 // Expression statement
	ND_STMT_EXPR                 // Statement expression
	ND_VAR                       // Variable
	ND_NUM                       // Integer
	ND_CAST                      // Type cast
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
	case ND_COMMA:
		return "ND_COMMA"
	case ND_MEMBER:
		return "ND_MEMBER"
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
	case ND_STMT_EXPR:
		return "ND_STMT_EXPR"
	case ND_VAR:
		return "ND_VAR"
	case ND_NUM:
		return "ND_NUM"
	default:
		return "UNKNOWN"
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

	// Block or statement expression
	body *Node

	// Struct member access
	member *Member

	// Function call
	funcname string
	args     *Node

	variable *Obj // Used if kind is ND_VAR

	val int64 // Used if kind is ND_NUM
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

func NewNumber(val int64, tok *Token) *Node {
	return &Node{
		kind: ND_NUM,
		lhs:  nil,
		rhs:  nil,
		val:  val,
		tok:  tok,
	}
}

func NewLong(val int64, tok *Token) *Node {
	return &Node{
		kind: ND_NUM,
		lhs:  nil,
		rhs:  nil,
		val:  val,
		tok:  tok,
		ty:   longType(),
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

func NewCast(expr *Node, ty *Type) *Node {
	addType(expr)

	node := &Node{
		kind: ND_CAST,
		tok:  expr.tok,
		lhs:  expr,
		rhs:  nil,
		ty:   ty,
	}
	return node
}

func pushScope(name string) *VarScope {
	vsc := &VarScope{
		name: name,
		next: scope.vars,
	}
	scope.vars = vsc
	return vsc
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
	rhs = NewBinary(ND_MUL, rhs, NewLong(int64(lhs.ty.base.size), tok), tok)
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
		rhs = NewBinary(ND_MUL, rhs, NewLong(int64(lhs.ty.base.size), tok), tok)
		addType(rhs)
		node := NewBinary(ND_SUB, lhs, rhs, tok)
		node.ty = lhs.ty
		return node
	}

	// ptr - ptr, which returns how many elements are between the two.
	if lhs.ty.base != nil && rhs.ty.base != nil {
		node := NewBinary(ND_SUB, lhs, rhs, tok)
		node.ty = intType()
		return NewBinary(ND_DIV, node, NewNumber(int64(lhs.ty.base.size), tok), tok)
	}

	errorTok(tok, "invalid operands")
	return nil
}

// #endregion

// #region Parser Token

// 使用全局变量 gtok 来保存当前的 token
var gtok *Token

func tryConsume(s string) bool {
	if gtok.equal(s) {
		gtok = gtok.next
		return true
	}
	return false
}

// Returns true if a given token represents a type.
func isTypename(tok *Token) bool {
	kw := []string{"void", "char", "short", "int", "long", "struct", "union", "typedef"}
	for _, k := range kw {
		if tok.equal(k) {
			return true
		}
	}
	return findTypedef(tok) != nil
}

// #endregion

// #region Parser

func pushTagScope(tok *Token, ty *Type) {
	sc := &TagScope{
		name: tok.literal,
		ty:   ty,
		next: scope.tags,
	}
	scope.tags = sc
}

// declspec = ("void" | "char" | "short" | "int" | "long"
// .           | struct-decl | union-decl)+
//
// The order of typenames in a type-specifier doesn't matter. For
// example, `int long static` means the same as `static long int`.
// That can also be written as `static long` because you can omit
// `int` if `long` or `short` are specified. However, something like
// `char int` is not a valid type specifier. We have to accept only a
// limited combinations of the typenames.
//
// In this function, we count the number of occurrences of each typename
// while keeping the "current" type object that the typenames up
// until that point represent. When we reach a non-typename token,
// we returns the current type object.
func declspec(attr *VarAttr) *Type {
	// We use a single integer as counters for all typenames.
	// For example, bits 0 and 1 represents how many times we saw the
	// keyword "void" so far. With this, we can use a switch statement
	// as you can see below.
	VOID := 1 << 0
	CHAR := 1 << 2
	SHORT := 1 << 4
	INT := 1 << 6
	LONG := 1 << 8
	OTHER := 1 << 10

	ty := intType()
	counter := 0

	for isTypename(gtok) {
		// Handle "typedef" keyword
		if gtok.equal("typedef") {
			if attr == nil {
				errorTok(gtok, "storage class specifier is not allowed in this context")
			}
			attr.isTypedef = true
			gtok = gtok.next
			continue
		}

		// Handle user-defined types.
		ty2 := findTypedef(gtok)
		if gtok.equal("struct") || gtok.equal("union") || ty2 != nil {
			if counter != 0 {
				break
			}

			if gtok.equal("struct") {
				gtok = gtok.next
				ty = structDecl()
			} else if gtok.equal("union") {
				gtok = gtok.next
				ty = unionDecl()
			} else {
				ty = ty2
				gtok = gtok.next
			}

			counter += OTHER
			continue
		}

		// Handle built-in types.
		if gtok.equal("void") {
			counter += VOID
		} else if gtok.equal("char") {
			counter += CHAR
		} else if gtok.equal("short") {
			counter += SHORT
		} else if gtok.equal("int") {
			counter += INT
		} else if gtok.equal("long") {
			counter += LONG
		} else {
			unreachable()
		}

		switch counter {
		case VOID:
			ty = voidType()
		case CHAR:
			ty = charType()
		case SHORT:
			ty = shortType()
		case SHORT + INT:
			ty = shortType()
		case INT:
			ty = intType()
		case LONG:
			ty = longType()
		case LONG + INT:
			ty = longType()
		case LONG + LONG:
			ty = longType()
		case LONG + LONG + INT:
			ty = longType()
		default:
			errorTok(gtok, "invalid type specifier")
		}

		gtok = gtok.next
	}

	return ty
}

// func-params = (param ("," param)*)? ")"
// param       = declspec declarator
func funcParams(ty *Type) *Type {
	var head = Type{}
	cur := &head

	for !gtok.equal(")") {
		if cur != &head {
			gtok = gtok.consume(",")
		}

		// param = declspec declarator
		basety := declspec(nil)
		ty := declarator(basety)
		cur.next = ty
		cur = cur.next
	}

	gtok = gtok.consume(")")
	ty = funcType(ty)
	ty.params = head.next
	return ty
}

// type-suffix = "(" func-params
// .           | "[" num "]" type-suffix
// .           | ε
func typeSuffix(ty *Type) *Type {
	if gtok.equal("(") {
		gtok = gtok.next
		return funcParams(ty)
	}

	if gtok.equal("[") {
		gtok = gtok.next
		length := gtok.getNumber()
		gtok = gtok.next.consume("]")
		ty = typeSuffix(ty)
		return arrayOf(ty, int(length))
	}
	return ty
}

// ref: https://www.sigbus.info/compilerbook#type
// declarator = "*"* ( "(" ident ")" | "(" declarator ")" | ident ) type-suffix
func declarator(ty *Type) *Type {
	for tryConsume("*") {
		ty = pointerTo(ty)
	}

	if gtok.equal("(") {
		st := gtok
		var dummy Type = Type{}
		gtok = st.next
		declarator(&dummy)
		gtok = gtok.consume(")")
		ty := typeSuffix(ty)
		end := gtok
		// 把括号外的类型填入括号里面
		gtok = st.next
		ty = declarator(ty)
		gtok = end
		return ty
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

// abstract-declarator = "*"* ("(" abstract-declarator ")")? type-suffix
func abstractDeclarator(ty *Type) *Type {
	for gtok.equal("*") {
		ty = pointerTo(ty)
		gtok = gtok.next
	}

	if gtok.equal("(") {
		st := gtok
		var dummy Type = Type{}
		gtok = st.next
		abstractDeclarator(&dummy)
		gtok = gtok.consume(")")
		ty = typeSuffix(ty)
		end := gtok
		// 把括号外的类型填入括号里面
		gtok = st.next
		ty = abstractDeclarator(ty)
		gtok = end
		return ty
	}

	return typeSuffix(ty)
}

// type-name = declspec abstract-declarator
func typename() *Type {
	ty := declspec(nil)
	return abstractDeclarator(ty)
}

// declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
func declaration(basety *Type) *Node {
	st := gtok

	var head Node
	cur := &head

	i := 0
	for !gtok.equal(";") {
		if i > 0 {
			gtok = gtok.consume(",")
		}
		i++

		ty := declarator(basety)
		if ty.kind == TY_VOID {
			errorTok(ty.name, "variable declared void")
		}
		variable := newLVar(ty.name.literal, ty)

		if !gtok.equal("=") {
			continue
		}

		// lhs = rhs
		lhs := NewVarNode(variable, ty.name)
		gtok = gtok.next
		rhs := assign()
		node := NewBinary(ND_ASSIGN, lhs, rhs, gtok)
		cur.next = NewUnary(ND_EXPR_STMT, node, gtok)
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

		addType(node)
		node.lhs = NewCast(node.lhs, pcurrentFn.ty.returnTy)
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

// compound-stmt = (typedef | declaration | stmt)* "}"
func compoundStmt() *Node {
	st := gtok
	node := NewNode(ND_BLOCK, st)
	gtok = gtok.consume("{")
	var head Node
	cur := &head

	enterScope()

	for !gtok.equal("}") {
		if isTypename(gtok) {
			var attr VarAttr = VarAttr{}
			basety := declspec(&attr)

			if attr.isTypedef {
				parseTypedef(basety)
				continue
			}

			cur.next = declaration(basety)
			cur = cur.next
		} else {
			cur.next = stmt()
			cur = cur.next
		}
		addType(cur)
	}

	leaveScope()

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

// expr = assign ("," expr)?
func expr() *Node {
	node := assign()

	if gtok.equal(",") {
		st := gtok
		gtok = gtok.next
		node = NewBinary(ND_COMMA, node, expr(), st)
	}

	return node
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

// mul = cast ( ('*' | '/') cast)*
func mul() *Node {
	node := cast()
	for {
		st := gtok
		if gtok.equal("*") {
			gtok = gtok.next
			node = NewBinary(ND_MUL, node, cast(), st)
			continue
		}
		if gtok.equal("/") {
			gtok = gtok.next
			node = NewBinary(ND_DIV, node, cast(), st)
			continue
		}

		return node
	}
}

// cast = "(" type-name ")" cast | unary
func cast() *Node {
	if gtok.equal("(") && isTypename(gtok.next) {
		st := gtok
		gtok = gtok.next
		ty := typename()
		gtok = gtok.consume(")")
		node := NewCast(cast(), ty)
		node.tok = st
		return node
	}

	return unary()
}

// unary = ( ("+" | "-" | "*" | "&") cast )
// .     | postfix
func unary() *Node {
	if gtok.equal("+") {
		gtok = gtok.next
		return cast()
	}
	st := gtok
	if gtok.equal("-") {
		gtok = gtok.next
		return NewUnary(ND_NEG, cast(), st)
	}

	if gtok.equal("&") {
		gtok = gtok.next
		return NewUnary(ND_ADDR, cast(), st)
	}

	if gtok.equal("*") {
		gtok = gtok.next
		return NewUnary(ND_DEREF, cast(), st)
	}

	return postfix()
}

// struct-members = (declspec declarator (","  declarator)* ";")*
func structMembers(ty *Type) {
	var head Member
	cur := &head

	for !gtok.equal("}") {
		basety := declspec(nil)
		i := 0

		for !tryConsume(";") {
			if i != 0 {
				gtok = gtok.consume(",")
			}
			i++

			mem := &Member{}
			mem.ty = declarator(basety)
			mem.name = mem.ty.name
			cur.next = mem
			cur = cur.next
		}
	}

	gtok = gtok.consume("}")
	ty.members = head.next
}

// struct-union-decl = ident? ("{" struct-members)?
func structUnionDecl() *Type {
	// Read a tag
	var tag *Token = nil
	if gtok.kind == TK_IDENT {
		tag = gtok
		gtok = gtok.next
	}

	if tag != nil && !gtok.equal("{") {
		ty := findTag(tag)
		if ty == nil {
			errorTok(gtok, "unknown struct type: %s", tag.literal)
		}
		return ty
	}

	// Construct a struct object.
	ty := newType(TY_STRUCT, 0, 1)
	gtok = gtok.consume("{")
	structMembers(ty)
	ty.align = 1

	// Register the struct type if a name was given.
	if tag != nil {
		pushTagScope(tag, ty)
	}
	return ty
}

// struct-decl = struct-union-decl
func structDecl() *Type {
	ty := structUnionDecl()
	ty.kind = TY_STRUCT

	// Assign offsets within the struct to members.
	offset := 0
	for m := ty.members; m != nil; m = m.next {
		// 每个成员的地址必须是其类型大小的整数倍（对齐要求）
		offset = alignTo(offset, m.ty.align)
		m.offset = offset
		offset += m.ty.size

		// 结构体的整体大小必须是其最大对齐要求的整数倍
		if ty.align < m.ty.align {
			ty.align = m.ty.align
		}
	}
	ty.size = alignTo(offset, ty.align)
	return ty
}

// union-decl = struct-union-decl
func unionDecl() *Type {
	ty := structUnionDecl()
	ty.kind = TY_UNION

	// If union, we don't have to assign offsets because they
	// are already initialized to zero. We need to compute the
	// alignment and the size though.
	for mem := ty.members; mem != nil; mem = mem.next {
		if ty.align < mem.ty.align {
			ty.align = mem.ty.align
		}
		if ty.size < mem.ty.size {
			ty.size = mem.ty.size
		}
	}
	ty.size = alignTo(ty.size, ty.align)
	return ty
}

func getStructMember(ty *Type, tok *Token) *Member {
	for m := ty.members; m != nil; m = m.next {
		if m.name.equal(tok.literal) {
			return m
		}
	}
	errorTok(tok, "unknown struct member: %s", tok.literal)
	return nil
}

func structRef(lhs *Node) *Node {
	addType(lhs)
	if lhs.ty.kind != TY_STRUCT && lhs.ty.kind != TY_UNION {
		errorTok(lhs.tok, "not a struct nor a union")
	}

	node := NewUnary(ND_MEMBER, lhs, gtok)
	node.member = getStructMember(lhs.ty, gtok)
	return node
}

// postfix = primary ( "[" expr "]" | "." ident | "->" ident )*
func postfix() *Node {
	node := primary()

	for {
		for gtok.equal("[") {
			// x[y] is short for *(x+y)
			st := gtok
			gtok = gtok.next
			idx := expr()
			gtok = gtok.consume("]")
			node = NewUnary(ND_DEREF, newAdd(node, idx, st), st)
			continue
		}

		if gtok.equal(".") {
			gtok = gtok.next
			node = structRef(node)
			gtok = gtok.next
			continue
		}

		if gtok.equal("->") {
			// x->y is short for (*x).y
			node = NewUnary(ND_DEREF, node, gtok)
			gtok = gtok.next
			node = structRef(node)
			gtok = gtok.next
			continue
		}

		return node

	}
}

// funcall = ident "(" (assign ("," assign)*)? ")"
func funcall() *Node {
	st := gtok
	gtok = gtok.next.next // skip ident "("

	sc := findVar(st.literal)
	if sc == nil {
		errorTok(st, "implicit declaration of a function")
	}
	if sc.variable == nil || sc.variable.ty.kind != TY_FUNC {
		errorTok(st, "not a function: %s", st.literal)
	}

	ty := sc.variable.ty.returnTy
	var head Node
	cur := &head

	for !gtok.equal(")") {
		if cur != &head {
			gtok = gtok.consume(",")
		}
		cur.next = assign()
		cur = cur.next
		addType(cur)
	}

	gtok = gtok.consume(")")

	node := NewNode(ND_FUNCALL, st)
	node.funcname = st.literal
	node.ty = ty
	node.args = head.next
	return node
}

// primary = "(" "{" stmt+ "}" ")"
// .       | "(" expr ")"
// .       | "sizeof" "(" type-name ")"
// .       | "sizeof" unary
// .       | ident
// .       | funcall
// .       | str
// .       | num
func primary() *Node {
	st := gtok

	if gtok.equal("(") && gtok.next.equal("{") {
		// This is a GNU statement expression.
		node := NewNode(ND_STMT_EXPR, gtok)
		gtok = gtok.next // skip "("
		node.body = compoundStmt().body
		gtok = gtok.consume(")")
		return node
	}

	if gtok.equal("(") {
		gtok = gtok.next
		node := expr()
		gtok = gtok.consume(")")
		return node
	}

	if gtok.equal("sizeof") && gtok.next.equal("(") && isTypename(gtok.next.next) {
		gtok = gtok.next.next
		ty := typename()
		gtok = gtok.consume(")")
		return NewNumber(int64(ty.size), st)
	}

	if gtok.equal("sizeof") {
		gtok = gtok.next
		node := unary()
		addType(node)
		return NewNumber(int64(node.ty.size), st)
	}

	if gtok.kind == TK_IDENT {
		// Function call
		if gtok.next.equal("(") {
			return funcall()
		}

		sc := findVar(gtok.literal)
		if sc == nil || sc.variable == nil {
			errorTok(gtok, "undefined variable: %s", gtok.literal)
		}
		node := NewVarNode(sc.variable, st)
		gtok = gtok.next
		return node
	}

	if gtok.kind == TK_STR {
		variable := newStringLiteral(gtok.str, gtok.ty)
		gtok = gtok.next
		return NewVarNode(variable, st)
	}

	if gtok.kind == TK_NUM {
		node := NewNumber(gtok.getNumber(), st)
		gtok = gtok.next
		return node
	}

	errorTok(gtok, "expected an expression")
	return nil
}

func parseTypedef(basety *Type) {
	first := true

	for !tryConsume(";") {
		if !first {
			gtok = gtok.consume(",")
		}
		first = false

		ty := declarator(basety)
		pushScope(ty.name.literal).typedef = ty
	}
}

// 为函数参数创建局部变量
func createParamLvars(param *Type) {
	if param != nil {
		createParamLvars(param.next)
		newLVar(param.name.literal, param)
	}
}

func function(basety *Type) *Obj {
	ty := declarator(basety)

	fn := newGVar(ty.name.literal, ty)
	fn.isFunction = true
	fn.isDefinition = !tryConsume(";")

	if !fn.isDefinition {
		return fn
	}

	pcurrentFn = fn
	locals = nil
	enterScope()
	createParamLvars(ty.params)
	fn.params = locals

	fn.body = compoundStmt()
	fn.locals = locals
	leaveScope()
	return fn
}

func globalVariable(basety *Type) {
	first := true

	for !tryConsume(";") {
		if !first {
			gtok = gtok.consume(",")
		}
		first = false

		ty := declarator(basety)
		newGVar(ty.name.literal, ty)
	}
}

// Lookahead tokens and returns true if a given token is a start
// of a function definition or declaration.
func isFunctionDefinition() bool {
	if gtok.equal(";") {
		return false
	}

	st := gtok
	var dummy = Type{}
	ty := declarator(&dummy)
	gtok = st
	return ty.kind == TY_FUNC
}

// program = (typedef | function-definition | global-variable)*
func program() *Obj {
	globals = nil

	for gtok.kind != TK_EOF {
		var attr VarAttr = VarAttr{}
		basety := declspec(&attr)

		// Typedef
		if attr.isTypedef {
			parseTypedef(basety)
			continue
		}

		// Function
		if isFunctionDefinition() {
			function(basety)
			continue
		}

		// Global variable
		globalVariable(basety)
	}

	return globals
}

// #endregion

func parse(tok *Token) *Obj {
	gtok = tok
	return program()
}
