package main

import "fmt"

// #region Scope

// Scope for local variables, global variables, typedefs
// or enum constants
type VarScope struct {
	next     *VarScope // Next scope
	name     string    // Scope name
	variable *Obj      // Variable
	typedef  *Type     // Typedef
	enumTy   *Type     // Enum type
	enumVal  int       // Enum value
}

// Scope for struct, union or enum tags (结构体/union 名字)
type TagScope struct {
	next *TagScope // Next scope
	name string    // Tag name
	ty   *Type     // Type
}

// Represents a block scope.
type Scope struct {
	next *Scope // Next scope

	// C has two block scopes; one is for variables/typedefs and
	// the other is for struct/union/enum tags.
	vars *VarScope
	tags *TagScope
}

// Variable attributes such as typedef or extern.
type VarAttr struct {
	isTypedef bool
	isStatic  bool
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
	isStatic     bool

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

// Lists of all goto statements and labels in the curent function.
var gotos *Node
var labels *Node

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
	tok    *Token // for error message
	name   *Token
	offset int
}

// #endregion

// #region AST Node

//go:generate stringer -type=NodeKind
type NodeKind int

// AST node kinds
const (
	ND_ADD       NodeKind = iota // +
	ND_SUB                       // -
	ND_MUL                       // *
	ND_DIV                       // /
	ND_NEG                       // unary -
	ND_MOD                       // %
	ND_BITAND                    // &
	ND_BITOR                     // |
	ND_BITXOR                    // ^
	ND_EQ                        // ==
	ND_NE                        // !=
	ND_LT                        // <
	ND_LE                        // <=
	ND_ASSIGN                    // =
	ND_COMMA                     // ,
	ND_MEMBER                    // . (struct member access)
	ND_ADDR                      // unary &
	ND_DEREF                     // unary *
	ND_NOT                       // unary !
	ND_BITNOT                    // unary ~
	ND_LOGAND                    // &&
	ND_LOGOR                     // ||
	ND_RETURN                    // return
	ND_IF                        // if
	ND_FOR                       // for or while
	ND_BLOCK                     // Block { ... }
	ND_GOTO                      // "goto"
	ND_LABEL                     // Labeled statement
	ND_FUNCALL                   // Function call
	ND_EXPR_STMT                 // Expression statement
	ND_STMT_EXPR                 // Statement expression
	ND_VAR                       // Variable
	ND_NUM                       // Integer
	ND_CAST                      // Type cast
)

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
	funcTy   *Type
	args     *Node

	// Goto or labeled statement
	label       string
	uniqueLabel string
	gotoNext    *Node

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
	kw := []string{"void", "_Bool", "char", "short", "int", "long", "struct", "union", "typedef", "enum", "static"}
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

// declspec = ("void" | "_Bool" | "char" | "short" | "int" | "long"
// .           | "typedef" | "static"
// .           | struct-decl | union-decl | typedef-name
// .           | enum-specifier)+
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
	BOOL := 1 << 2
	CHAR := 1 << 4
	SHORT := 1 << 6
	INT := 1 << 8
	LONG := 1 << 10
	OTHER := 1 << 12

	ty := intType()
	counter := 0

	for isTypename(gtok) {
		// Handle storage class specifiers.
		if gtok.equal("typedef") || gtok.equal("static") {
			if attr == nil {
				errorTok(gtok, "storage class specifier is not allowed in this context")
			}

			if gtok.equal("typedef") {
				attr.isTypedef = true
			} else {
				attr.isStatic = true
			}

			if attr.isTypedef && attr.isStatic {
				errorTok(gtok, "typedef and static may not be used together")
			}
			gtok = gtok.next
			continue
		}

		// Handle user-defined types.
		ty2 := findTypedef(gtok)
		if gtok.equal("struct") || gtok.equal("union") || gtok.equal("enum") || ty2 != nil {
			if counter != 0 {
				break
			}

			if gtok.equal("struct") {
				gtok = gtok.next
				ty = structDecl()
			} else if gtok.equal("union") {
				gtok = gtok.next
				ty = unionDecl()
			} else if gtok.equal("enum") {
				gtok = gtok.next
				ty = enumSpecifier()
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
		} else if gtok.equal("_Bool") {
			counter += BOOL
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
		case BOOL:
			ty = boolType()
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

		ty2 := declspec(nil)
		ty2 = declarator(ty2)

		// "array of T" is converted to "pointer to T" only in the parameter
		// context. For example, *argv[] is converted to **argv by this.
		if ty2.kind == TY_ARRAY {
			name := ty2.name
			ty2 = pointerTo(ty2.base)
			ty2.name = name
		}

		cur.next = ty2
		cur = cur.next
	}

	gtok = gtok.consume(")")
	ty = funcType(ty)
	ty.params = head.next
	return ty
}

// array-dimensions = num? "]" type-suffix
func arrayDimensions(ty *Type) *Type {
	if gtok.equal("]") {
		gtok = gtok.next
		ty = typeSuffix(ty)
		return arrayOf(ty, -1)
	}

	sz := gtok.getNumber()
	gtok = gtok.next.consume("]")
	ty = typeSuffix(ty)
	return arrayOf(ty, int(sz))
}

// type-suffix = "(" func-params
// .           | "[" array-dimensions
// .           | ε
func typeSuffix(ty *Type) *Type {
	if gtok.equal("(") {
		gtok = gtok.next
		return funcParams(ty)
	}

	if gtok.equal("[") {
		gtok = gtok.next
		return arrayDimensions(ty)
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

// enum-specifier = ident? "{" enum-list? "}"
// .              | ident ("{" enum-list? "}")?
//
// enum-list      = ident ("=" num)? ("," ident ("=" num)?)*
func enumSpecifier() *Type {
	ty := enumType()

	// Read a struct tag.
	var tag *Token = nil
	if gtok.kind == TK_IDENT {
		tag = gtok
		gtok = gtok.next
	}

	if tag != nil && !gtok.equal("{") {
		ty = findTag(tag)
		if ty == nil {
			errorTok(tag, "unknown enum type")
		}
		if ty.kind != TY_ENUM {
			errorTok(tag, "not an enum tag")
		}
		return ty
	}

	gtok = gtok.consume("{")

	// Read an enum-list.
	i := 0
	val := 0
	for !gtok.equal("}") {
		if i > 0 {
			gtok = gtok.consume(",")
		}
		i++

		name := gtok.literal
		gtok = gtok.next

		if gtok.equal("=") {
			gtok = gtok.next
			val = int(gtok.getNumber())
			gtok = gtok.next
		}

		sc := pushScope(name)
		sc.enumTy = ty
		sc.enumVal = val
		val++
	}

	gtok = gtok.consume("}")

	if tag != nil {
		pushTagScope(tag, ty)
	}
	return ty
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
		if ty.size < 0 {
			errorTok(gtok, "variable has incomplete type")
		}
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
// .    | "goto" ident ";"
// .    | ident ":" stmt
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

	if gtok.equal("goto") {
		node := NewNode(ND_GOTO, gtok)
		node.label = gtok.next.literal
		node.gotoNext = gotos
		gotos = node
		gtok = gtok.next.next
		gtok = gtok.consume(";")
		return node
	}

	if gtok.kind == TK_IDENT && gtok.next.equal(":") {
		node := NewNode(ND_LABEL, gtok)
		node.label = gtok.literal
		node.uniqueLabel = newUniqueName()
		gtok = gtok.next.next
		node.lhs = stmt()
		node.gotoNext = labels
		labels = node
		return node
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

	enterScope()

	if isTypename(gtok) {
		basety := declspec(nil)
		node.init = declaration(basety)
	} else {
		node.init = exprStmt()
	}

	if !gtok.equal(";") {
		node.cond = expr()
	}
	gtok = gtok.consume(";")

	if !gtok.equal(")") {
		node.inc = expr()
	}
	gtok = gtok.consume(")")

	node.then = stmt()
	leaveScope()
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
		if isTypename(gtok) && !gtok.next.equal(":") {
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

// 转换 `A op= B` 为 `tmp = &A, *tmp = *tmp op B` 的主要原因是为了确保左值只被求值一次，从而避免重复计算可能带来的副作用。
//
// - 当 A 是一个复杂表达式（例如数组元素或结构体成员）时，直接写成 `A = A op B` 可能会导致 A 表达式被求值两次，从而出现不确定性或副作用。
// - 通过先取 A 的地址，将它保存到一个临时变量 tmp 中，然后通过解引用 tmp 来进行操作，可以保证 A 只被计算一次，同时保持正确的赋值语义。
//
// Convert `A op= B` to `tmp = &A, *tmp = *tmp op B`
// where tmp is a fresh pointer variable.
func toAssign(binary *Node) *Node {
	addType(binary.lhs)
	addType(binary.rhs)
	tok := binary.tok

	variable := newLVar("", pointerTo(binary.lhs.ty))

	expr1 := NewBinary(
		ND_ASSIGN,
		NewVarNode(variable, tok),
		NewUnary(ND_ADDR, binary.lhs, tok),
		tok)

	expr2 := NewBinary(
		ND_ASSIGN,
		NewUnary(ND_DEREF,
			NewVarNode(variable, tok), tok),
		NewBinary(binary.kind,
			NewUnary(ND_DEREF, NewVarNode(variable, tok), tok),
			binary.rhs,
			tok),
		tok)

	return NewBinary(ND_COMMA, expr1, expr2, tok)
}

// assign    = logor (assign-op assign)?
// assign-op = "=" | "+=" | "-=" | "*=" | "/=" | "%="
func assign() *Node {
	node := logor()
	if gtok.equal("=") {
		st := gtok
		gtok = gtok.next
		node = NewBinary(ND_ASSIGN, node, assign(), st)
	}

	st := gtok
	if gtok.equal("+=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_ADD, node, assign(), st))
	}

	if gtok.equal("-=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_SUB, node, assign(), st))
	}

	if gtok.equal("*=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_MUL, node, assign(), st))
	}

	if gtok.equal("/=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_DIV, node, assign(), st))
	}

	if gtok.equal("%=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_MOD, node, assign(), st))
	}

	if gtok.equal("&=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_BITAND, node, assign(), st))
	}

	if gtok.equal("|=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_BITOR, node, assign(), st))
	}

	if gtok.equal("^=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_BITXOR, node, assign(), st))
	}

	return node
}

// logor = logand ("||" logand)*
func logor() *Node {
	node := logand()
	for gtok.equal("||") {
		st := gtok
		gtok = gtok.next
		node = NewBinary(ND_LOGOR, node, logand(), st)
	}
	return node
}

// logand = bitor ("&&" bitor)*
func logand() *Node {
	node := bitor()
	for gtok.equal("&&") {
		st := gtok
		gtok = gtok.next
		node = NewBinary(ND_LOGAND, node, bitor(), st)
	}
	return node
}

// bitor = bitxor ("|" bitxor)*
func bitor() *Node {
	node := bitxor()
	for gtok.equal("|") {
		st := gtok
		gtok = gtok.next
		node = NewBinary(ND_BITOR, node, bitxor(), st)
	}
	return node
}

// bitxor = bitand ("^" bitand)*
func bitxor() *Node {
	node := bitand()
	for gtok.equal("^") {
		st := gtok
		gtok = gtok.next
		node = NewBinary(ND_BITXOR, node, bitand(), st)
	}
	return node
}

// bitand = equality ("&" equality)*
func bitand() *Node {
	node := equality()
	for gtok.equal("&") {
		st := gtok
		gtok = gtok.next
		node = NewBinary(ND_BITAND, node, equality(), st)
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

// mul = cast ("*" cast | "/" cast | "%" cast)*
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

		if gtok.equal("%") {
			gtok = gtok.next
			node = NewBinary(ND_MOD, node, cast(), st)
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

// unary = ( ("+" | "-" | "*" | "&" | "!" | "~") cast )
// .     | ("++" | "--") unary
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

	if gtok.equal("!") {
		gtok = gtok.next
		return NewUnary(ND_NOT, cast(), st)
	}

	if gtok.equal("~") {
		gtok = gtok.next
		return NewUnary(ND_BITNOT, cast(), st)
	}

	// Read ++i as i+=1
	if gtok.equal("++") {
		st := gtok
		gtok = gtok.next
		return toAssign(
			newAdd(unary(), NewNumber(1, st), st),
		)
	}

	// Read --i as i-=1
	if gtok.equal("--") {
		st := gtok
		gtok = gtok.next
		return toAssign(
			newSub(unary(), NewNumber(1, st), st),
		)
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
		if ty != nil {
			return ty
		}

		ty = structType()
		ty.size = -1
		pushTagScope(tag, ty)
		return ty
	}

	gtok = gtok.consume("{")

	// Construct a struct object.
	ty := structType()
	structMembers(ty)

	if tag != nil {
		// If this is a redefinition, overwrite a previous type.
		// Otherwise, register the struct type.
		for sc := scope.tags; sc != nil; sc = sc.next {
			if tag.equal(sc.name) {
				*sc.ty = *ty
				return sc.ty
			}
		}

		pushTagScope(tag, ty)
	}

	return ty
}

// struct-decl = struct-union-decl
func structDecl() *Type {
	ty := structUnionDecl()
	ty.kind = TY_STRUCT

	if ty.size < 0 {
		return ty
	}

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

	if ty.size < 0 {
		return ty
	}

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

// Convert A++ to `(typeof A)((A += 1) - 1)`
func newIncDec(node *Node, tok *Token, addend int) *Node {
	addType(node)
	add := newAdd(node, NewNumber(int64(addend), tok), tok)
	add = newAdd(toAssign(add), NewNumber(int64(-addend), tok), tok)
	return NewCast(add, node.ty)
}

// postfix = primary ("[" expr "]" | "." ident | "->" ident | "++" | "--")*
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

		if gtok.equal("++") {
			node = newIncDec(node, gtok, 1)
			gtok = gtok.next
			continue
		}

		if gtok.equal("--") {
			node = newIncDec(node, gtok, -1)
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

	ty := sc.variable.ty
	paramTy := ty.params
	var head Node
	cur := &head

	for !gtok.equal(")") {
		if cur != &head {
			gtok = gtok.consume(",")
		}
		arg := assign()
		addType(arg)

		if paramTy != nil {
			if paramTy.kind == TY_STRUCT || paramTy.kind == TY_UNION {
				errorTok(gtok, "passing struct or union is not supported yet")
			}
			arg = NewCast(arg, paramTy)
			paramTy = paramTy.next
		}

		cur.next = arg
		cur = cur.next
	}

	gtok = gtok.consume(")")

	node := NewNode(ND_FUNCALL, st)
	node.funcname = st.literal
	node.funcTy = ty
	node.ty = ty.returnTy
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

		// Variable or enum constant
		sc := findVar(gtok.literal)
		if sc == nil || (sc.variable == nil && sc.enumTy == nil) {
			errorTok(gtok, "undefined variable: %s", gtok.literal)
		}
		var node *Node
		if sc.variable != nil {
			node = NewVarNode(sc.variable, st)
		} else {
			node = NewNumber(int64(sc.enumVal), st)
		}
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

// This function matches gotos with labels.
//
// We cannot resolve gotos as we parse a function because gotos
// can refer a label that appears later in the function.
// So, we need to do this after we parse the entire function.
func resolveGotoLabels() {
	for node := gotos; node != nil; node = node.gotoNext {
		for label := labels; label != nil; label = label.gotoNext {
			if node.label == label.label {
				node.uniqueLabel = label.uniqueLabel
				break
			}
		}

		if node.uniqueLabel == "" {
			errorTok(node.tok.next, "use of undeclared label")
		}
	}

	labels = nil
	gotos = nil
}

func function(basety *Type, attr *VarAttr) *Obj {
	ty := declarator(basety)

	fn := newGVar(ty.name.literal, ty)
	fn.isFunction = true
	fn.isDefinition = !tryConsume(";")
	fn.isStatic = attr.isStatic

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
	resolveGotoLabels()
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
			function(basety, &attr)
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
