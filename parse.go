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

// This struct represents a variable initializer. Since initializers
// can be nested (e.g. `int x[2][2] = {{1, 2}, {3, 4}}`), this struct
// is a tree data structure.
type Initializer struct {
	next       *Initializer // Next initializer
	ty         *Type        // Type of the initializer
	tok        *Token
	isFlexible bool

	// If it's not an aggregate type and has an initializer,
	// `expr` has an initialization expression.
	expr *Node

	// If it's an initializer for an aggregate type (e.g. array or struct),
	// `children` has initializers for its children.
	children []*Initializer
}

// For local variable initializer.
type InitDesg struct {
	next   *InitDesg // Next initializer
	idx    int
	member *Member
	var_   *Obj // Variable
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
	initData []byte
	rel      *Relocation

	// Function
	params    *Obj
	body      *Node
	locals    *Obj
	stackSize int // Stack size
}

// Global variable can be initialized either by a constant expression
// or a pointer to another global variable. This struct represents the
// latter.
type Relocation struct {
	next   *Relocation // Next relocation
	offset int
	label  string
	addend int64 // Addend for the relocation
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

// Current "goto" and "continue" jump target.
var brkLabel string
var contLabel string

// Points to a node representing a switch if we are parsing
// a switch statement. Otherwise, NULL.
var currentSwitch *Node

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
	variable.initData = make([]byte, len(s)+1) // +1 for '\0'
	copy(variable.initData, s)
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
	idx    int
	offset int
}

// #endregion

// #region AST Node

//go:generate stringer -type=NodeKind
type NodeKind int

// AST node kinds
const (
	ND_NULL_EXPR NodeKind = iota
	ND_ADD                // +
	ND_SUB                // -
	ND_MUL                // *
	ND_DIV                // /
	ND_NEG                // unary -
	ND_MOD                // %
	ND_BITAND             // &
	ND_BITOR              // |
	ND_BITXOR             // ^
	ND_SHL                // <<
	ND_SHR                // >>
	ND_EQ                 // ==
	ND_NE                 // !=
	ND_LT                 // <
	ND_LE                 // <=
	ND_ASSIGN             // =
	ND_COND               // ?:
	ND_COMMA              // ,
	ND_MEMBER             // . (struct member access)
	ND_ADDR               // unary &
	ND_DEREF              // unary *
	ND_NOT                // unary !
	ND_BITNOT             // unary ~
	ND_LOGAND             // &&
	ND_LOGOR              // ||
	ND_RETURN             // return
	ND_IF                 // if
	ND_FOR                // for or while
	ND_SWITCH             // switch
	ND_CASE               // case
	ND_BLOCK              // Block { ... }
	ND_GOTO               // "goto"
	ND_LABEL              // Labeled statement
	ND_FUNCALL            // Function call
	ND_EXPR_STMT          // Expression statement
	ND_STMT_EXPR          // Statement expression
	ND_VAR                // Variable
	ND_NUM                // Integer
	ND_CAST               // Type cast
	ND_MEMZERO            // Zero-clear a stack variable
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

	// "break" and "continue" label
	breakLabel    string
	continueLabel string

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

	// Switch-cases
	caseNext    *Node
	defaultCase *Node

	// Variable
	variable *Obj // Used if kind is ND_VAR

	// Numeric literal
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

func newInitializer(ty *Type, isFlexible bool) *Initializer {
	init := &Initializer{}
	init.ty = ty

	if ty.kind == TY_ARRAY {
		if isFlexible && ty.size < 0 {
			init.isFlexible = true
			return init
		}

		init.children = make([]*Initializer, ty.arrayLen)
		for i := range ty.arrayLen {
			init.children[i] = newInitializer(ty.base, false)
		}
		return init
	}

	if ty.kind == TY_STRUCT || ty.kind == TY_UNION {
		// Count the number of struct members.
		length := 0
		for mem := ty.members; mem != nil; mem = mem.next {
			length++
		}

		init.children = make([]*Initializer, length)

		for mem := ty.members; mem != nil; mem = mem.next {
			if isFlexible && ty.isFlexible && mem.next == nil {
				child := &Initializer{}
				child.ty = mem.ty
				child.isFlexible = true
				init.children[mem.idx] = child
			} else {
				init.children[mem.idx] = newInitializer(mem.ty, false)
			}
		}

		return init
	}

	return init
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

func skipExcessElement() *Token {
	if gtok.equal("{") {
		gtok = gtok.next
		gtok = skipExcessElement()
		return gtok.consume("}")
	}

	assign()
	return gtok
}

// string-initializer = string-literal
func stringInitializer(init *Initializer) {
	if init.isFlexible {
		*init = *newInitializer(arrayOf(init.ty.base, gtok.ty.arrayLen), false)
	}

	length := min(init.ty.arrayLen, gtok.ty.arrayLen)
	for i := range length {
		if i >= len(gtok.str) {
			// 不再末尾直接补 0 ，是因为有这种情况：char g19[3] = "foobar";
			// 他的末尾就不是 '\0'，而是 'o'。
			// C 字符串以 '\0' 结尾
			init.children[i].expr = NewNumber(0, gtok)
		} else {
			init.children[i].expr = NewNumber(int64(gtok.str[i]), gtok)
		}
	}
	gtok = gtok.next
}

func countArrayInitElements(ty *Type) int {
	dummy := newInitializer(ty.base, false)

	i := 0
	for ; !consumeEnd(); i++ {
		if i > 0 {
			gtok = gtok.consume(",")
		}
		initializer2(dummy)
	}
	return i
}

// array-initializer1 = "{" initializer ("," initializer)* ","? "}"
func arrayInitializer1(init *Initializer) {
	gtok = gtok.consume("{")

	if init.isFlexible {
		tok := gtok
		length := countArrayInitElements(init.ty)
		gtok = tok
		*init = *newInitializer(arrayOf(init.ty.base, length), false)
	}

	for i := 0; !consumeEnd(); i++ {
		if i > 0 {
			gtok = gtok.consume(",")
		}

		if i < init.ty.arrayLen {
			initializer2(init.children[i])
		} else {
			gtok = skipExcessElement()
		}
	}
}

// array-initializer2 = initializer ("," initializer)*
func arrayInitializer2(init *Initializer) {
	if init.isFlexible {
		tok := gtok
		length := countArrayInitElements(init.ty)
		gtok = tok
		*init = *newInitializer(arrayOf(init.ty.base, length), false)
	}

	for i := 0; i < init.ty.arrayLen && !isEnd(gtok); i++ {
		if i > 0 {
			gtok = gtok.consume(",")
		}
		initializer2(init.children[i])
	}
}

// struct-initializer1 = "{" initializer ("," initializer)* ","? "}"
func structInitializer1(init *Initializer) {
	gtok = gtok.consume("{")

	mem := init.ty.members

	for !consumeEnd() {
		if mem != init.ty.members {
			gtok = gtok.consume(",")
		}

		if mem != nil {
			initializer2(init.children[mem.idx])
			mem = mem.next
		} else {
			gtok = skipExcessElement()
		}
	}
}

// struct-initializer2 = initializer ("," initializer)*
func structInitializer2(init *Initializer) {
	first := true

	for mem := init.ty.members; mem != nil && !isEnd(gtok); mem = mem.next {
		if !first {
			gtok = gtok.consume(",")
		}
		first = false
		initializer2(init.children[mem.idx])
	}
}

func unionInitializer(init *Initializer) {
	// Unlike structs, union initializers take only one initializer,
	// and that initializes the first union member.
	if gtok.equal("{") {
		gtok = gtok.next
		initializer2(init.children[0])
		tryConsume(",")
		gtok = gtok.consume("}")
	} else {
		initializer2(init.children[0])
	}
}

// initializer = string-initializer | array-initializer
// .           | struct-initializer | union-initializer
// .           | assign
func initializer2(init *Initializer) {
	if init.ty.kind == TY_ARRAY && gtok.kind == TK_STR {
		stringInitializer(init)
		return
	}

	if init.ty.kind == TY_ARRAY {
		if gtok.equal("{") {
			arrayInitializer1(init)
		} else {
			arrayInitializer2(init)
		}
		return
	}

	if init.ty.kind == TY_STRUCT {
		if gtok.equal("{") {
			structInitializer1(init)
			return
		}

		// A struct can be initialized with another struct. E.g.
		// `struct T x = y;` where y is a variable of type `struct T`.
		// Handle that case first.
		tok := gtok
		expr := assign()
		addType(expr)
		if expr.ty.kind == TY_STRUCT {
			init.expr = expr
			return
		}

		gtok = tok
		structInitializer2(init)
		return
	}

	if init.ty.kind == TY_UNION {
		unionInitializer(init)
		return
	}

	if gtok.equal("{") {
		// An initializer for a scalar variable can be surrounded by
		// braces. E.g. `int x = {3};`. Handle that case.
		gtok = gtok.next
		initializer2(init)
		gtok = gtok.consume("}")
		return
	}

	init.expr = assign()
}

func copyStructType(ty *Type) *Type {
	ty = ty.copy()

	head := Member{}
	cur := &head
	for mem := ty.members; mem != nil; mem = mem.next {
		m := &Member{}
		*m = *mem
		cur.next = m
		cur = cur.next
	}

	ty.members = head.next
	return ty
}

func initializer(ty *Type, newTy **Type) *Initializer {
	init := newInitializer(ty, true)
	initializer2(init)

	if (ty.kind == TY_STRUCT || ty.kind == TY_UNION) && ty.isFlexible {
		ty = copyStructType(ty)

		mem := ty.members
		for mem.next != nil {
			mem = mem.next
		}
		mem.ty = init.children[mem.idx].ty
		ty.size += mem.ty.size

		*newTy = ty
		return init
	}

	*newTy = init.ty
	return init
}

func initDesgExpr(desg *InitDesg, tok *Token) *Node {
	if desg.var_ != nil {
		return NewVarNode(desg.var_, tok)
	}

	if desg.member != nil {
		node := NewUnary(ND_MEMBER, initDesgExpr(desg.next, tok), tok)
		node.member = desg.member
		return node
	}

	lhs := initDesgExpr(desg.next, tok)
	rhs := NewNumber(int64(desg.idx), tok)
	return NewUnary(ND_DEREF, newAdd(lhs, rhs, tok), tok)
}

func createLvarInit(init *Initializer, ty *Type, desg *InitDesg, tok *Token) *Node {
	if ty.kind == TY_ARRAY {
		node := NewNode(ND_NULL_EXPR, tok)
		for i := range ty.arrayLen {
			desg2 := InitDesg{desg, i, nil, nil}
			rhs := createLvarInit(init.children[i], ty.base, &desg2, tok)
			node = NewBinary(ND_COMMA, node, rhs, tok)
		}
		return node
	}

	if ty.kind == TY_STRUCT && init.expr == nil {
		node := NewNode(ND_NULL_EXPR, tok)

		for mem := ty.members; mem != nil; mem = mem.next {
			desg2 := InitDesg{desg, 0, mem, nil}
			rhs := createLvarInit(init.children[mem.idx], mem.ty, &desg2, tok)
			node = NewBinary(ND_COMMA, node, rhs, tok)
		}
		return node
	}

	if ty.kind == TY_UNION {
		desg2 := InitDesg{desg, 0, ty.members, nil}
		return createLvarInit(init.children[0], ty.members.ty, &desg2, tok)
	}

	if init.expr == nil {
		return NewNode(ND_NULL_EXPR, tok)
	}

	lhs := initDesgExpr(desg, tok)
	return NewBinary(ND_ASSIGN, lhs, init.expr, tok)
}

// A variable definition with an initializer is a shorthand notation
// for a variable definition followed by assignments. This function
// generates assignment expressions for an initializer. For example,
// `int x[2][2] = {{6, 7}, {8, 9}}` is converted to the following
// expressions:
//
//	x[0][0] = 6;
//	x[0][1] = 7;
//	x[1][0] = 8;
//	x[1][1] = 9;
func lvarInitializer(var_ *Obj) *Node {
	st := gtok
	init := initializer(var_.ty, &var_.ty)
	desg := InitDesg{nil, 0, nil, var_}

	// If a partial initializer list is given, the standard requires
	// that unspecified elements are set to 0. Here, we simply
	// zero-initialize the entire memory region of a variable before
	// initializing it with user-supplied values.
	lhs := NewNode(ND_MEMZERO, st)
	lhs.variable = var_

	rhs := createLvarInit(init, var_.ty, &desg, st)
	return NewBinary(ND_COMMA, lhs, rhs, st)
}

func writeBuf(val uint64, sz int) (buf []byte) {
	buf = make([]byte, sz)
	switch sz {
	case 1:
		buf[0] = byte(val)
	case 2:
		buf[0] = byte(val)
		buf[1] = byte(val >> 8)
	case 4:
		buf[0] = byte(val)
		buf[1] = byte(val >> 8)
		buf[2] = byte(val >> 16)
		buf[3] = byte(val >> 24)
	case 8:
		buf[0] = byte(val)
		buf[1] = byte(val >> 8)
		buf[2] = byte(val >> 16)
		buf[3] = byte(val >> 24)
		buf[4] = byte(val >> 32)
		buf[5] = byte(val >> 40)
		buf[6] = byte(val >> 48)
		buf[7] = byte(val >> 56)
	default:
		unreachable()
	}
	return buf
}

func writeGvarData(cur *Relocation, init *Initializer, ty *Type, buf []byte, offset int) *Relocation {
	if ty.kind == TY_ARRAY {
		sz := ty.base.size
		for i := range ty.arrayLen {
			cur = writeGvarData(cur, init.children[i], ty.base, buf, offset+i*sz)
		}
		return cur
	}

	if ty.kind == TY_STRUCT {
		for mem := ty.members; mem != nil; mem = mem.next {
			cur = writeGvarData(cur, init.children[mem.idx], mem.ty, buf, offset+mem.offset)
		}
		return cur
	}

	if ty.kind == TY_UNION {
		return writeGvarData(cur, init.children[0], ty.members.ty, buf, offset)
	}

	if init.expr == nil {
		return cur
	}

	label := ""
	val := eval2(init.expr, &label)

	if label == "" {
		res := writeBuf(uint64(val), ty.size)
		copy(buf[offset:], res)
		return cur
	}

	rel := &Relocation{
		next:   nil,
		offset: offset,
		label:  label,
		addend: val,
	}
	cur.next = rel
	return cur.next
}

// Initializers for global variables are evaluated at compile-time and
// embedded to .data section. This function serializes Initializer
// objects to a flat byte array. It is a compile error if an
// initializer list contains a non-constant expression.
func gvarInitializer(var_ *Obj) {
	init := initializer(var_.ty, &var_.ty)

	head := Relocation{}
	buf := make([]byte, var_.ty.size)
	writeGvarData(&head, init, var_.ty, buf, 0)
	var_.initData = buf
	var_.rel = head.next
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

// array-dimensions = const-expr? "]" type-suffix
func arrayDimensions(ty *Type) *Type {
	if gtok.equal("]") {
		gtok = gtok.next
		ty = typeSuffix(ty)
		return arrayOf(ty, -1)
	}

	sz := constExpr()
	gtok = gtok.consume("]")
	ty = typeSuffix(ty)
	return arrayOf(ty, int(int32(sz)))
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

func isEnd(tok *Token) bool {
	return tok.equal("}") || (tok.equal(",") && tok.next.equal("}"))
}

func consumeEnd() bool {
	if gtok.equal("}") {
		gtok = gtok.next
		return true
	}

	if gtok.equal(",") && gtok.next.equal("}") {
		gtok = gtok.next.next
		return true
	}

	return false
}

// enum-specifier = ident? "{" enum-list? "}"
// .              | ident ("{" enum-list? "}")?
//
// enum-list      = ident ("=" num)? ("," ident ("=" num)?)* ","?
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
	for !consumeEnd() {
		if i > 0 {
			gtok = gtok.consume(",")
		}
		i++

		name := gtok.literal
		gtok = gtok.next

		if gtok.equal("=") {
			gtok = gtok.next
			val = int(constExpr())
		}

		sc := pushScope(name)
		sc.enumTy = ty
		sc.enumVal = val
		val++
	}

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
		if ty.kind == TY_VOID {
			errorTok(ty.name, "variable declared void")
		}
		variable := newLVar(ty.name.literal, ty)

		if gtok.equal("=") {
			// lhs = rhs
			st := gtok
			gtok = gtok.next
			expr := lvarInitializer(variable)
			cur.next = NewUnary(ND_EXPR_STMT, expr, st)
			cur = cur.next
		}

		if variable.ty.size < 0 {
			errorTok(ty.name, "variable has incomplete type")
		}
		if variable.ty.kind == TY_VOID {
			errorTok(ty.name, "variable declared void")
		}

	}

	node := NewNode(ND_BLOCK, st)
	node.body = head.next
	gtok = gtok.consume(";")
	return node
}

// stmt = "return" expr ";"
// .    | if-stmt
// .    | "switch" "(" expr ")" stmt
// .    | "case" const-expr ":" stmt
// .    | "default" ":" stmt
// .    | for-stmt
// .    | while-stmt
// .    | "goto" ident ";"
// .    | "break" ";"
// .    | "continue" ";"
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

	if gtok.equal("switch") {
		node := NewNode(ND_SWITCH, gtok)
		gtok = gtok.next.consume("(")
		node.cond = expr()
		gtok = gtok.consume(")")

		sw := currentSwitch
		currentSwitch = node

		brk := brkLabel // 保存当前的 break label
		node.breakLabel = newUniqueName()
		brkLabel = node.breakLabel

		node.then = stmt()

		currentSwitch = sw
		brkLabel = brk // 恢复当前的 break label
		return node
	}

	if gtok.equal("case") {
		if currentSwitch == nil {
			errorTok(gtok, "case label not within switch")
		}

		node := NewNode(ND_CASE, gtok)
		gtok = gtok.next
		val := constExpr()
		gtok = gtok.consume(":")
		node.label = newUniqueName()
		node.lhs = stmt()
		node.val = val
		node.caseNext = currentSwitch.caseNext
		currentSwitch.caseNext = node
		return node
	}

	if gtok.equal("default") {
		if currentSwitch == nil {
			errorTok(gtok, "default label not within switch")
		}

		node := NewNode(ND_CASE, gtok)
		gtok = gtok.next.consume(":")
		node.label = newUniqueName()
		node.lhs = stmt()
		currentSwitch.defaultCase = node
		return node
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

	if gtok.equal("break") {
		if brkLabel == "" {
			errorTok(gtok, "break statement not within loop")
		}
		node := NewNode(ND_GOTO, gtok)
		node.uniqueLabel = brkLabel
		gtok = gtok.next.consume(";")
		return node
	}

	if gtok.equal("continue") {
		if contLabel == "" {
			errorTok(gtok, "continue statement not within loop")
		}
		node := NewNode(ND_GOTO, gtok)
		node.uniqueLabel = contLabel
		gtok = gtok.next.consume(";")
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

func eval(node *Node) int64 {
	return eval2(node, nil)
}

// Evaluate a given node as a constant expression.
//
// A constant expression is either just a number or ptr+n where ptr
// is a pointer to a global variable and n is a postiive/negative
// number. The latter form is accepted only as an initialization
// expression for a global variable.
func eval2(node *Node, label *string) int64 {
	addType(node)

	switch node.kind {
	case ND_ADD:
		return eval2(node.lhs, label) + eval(node.rhs)
	case ND_SUB:
		return eval2(node.lhs, label) - eval(node.rhs)
	case ND_MUL:
		return eval(node.lhs) * eval(node.rhs)
	case ND_DIV:
		return eval(node.lhs) / eval(node.rhs)
	case ND_NEG:
		return -eval(node.lhs)
	case ND_MOD:
		return eval(node.lhs) % eval(node.rhs)
	case ND_BITAND:
		return eval(node.lhs) & eval(node.rhs)
	case ND_BITOR:
		return eval(node.lhs) | eval(node.rhs)
	case ND_BITXOR:
		return eval(node.lhs) ^ eval(node.rhs)
	case ND_SHL:
		return eval(node.lhs) << eval(node.rhs)
	case ND_SHR:
		return eval(node.lhs) >> eval(node.rhs)
	case ND_EQ:
		if eval(node.lhs) == eval(node.rhs) {
			return 1
		}
		return 0
	case ND_NE:
		if eval(node.lhs) != eval(node.rhs) {
			return 1
		}
		return 0
	case ND_LT:
		if eval(node.lhs) < eval(node.rhs) {
			return 1
		}
		return 0
	case ND_LE:
		if eval(node.lhs) <= eval(node.rhs) {
			return 1
		}
		return 0
	case ND_COND:
		if eval(node.cond) != 0 {
			return eval2(node.then, label)
		}
		return eval2(node.els, label)
	case ND_COMMA:
		return eval2(node.rhs, label)
	case ND_NOT:
		if eval(node.lhs) == 0 {
			return 1
		}
		return 0
	case ND_BITNOT:
		return ^eval(node.lhs)
	case ND_LOGAND:
		lhs := eval(node.lhs)
		rhs := eval(node.rhs)
		if lhs != 0 && rhs != 0 {
			return 1
		} else {
			return 0
		}
	case ND_LOGOR:
		lhs := eval(node.lhs)
		rhs := eval(node.rhs)
		if lhs != 0 {
			return 1
		} else if rhs != 0 {
			return 1
		} else {
			return 0
		}
	case ND_CAST:
		val := eval2(node.lhs, label)
		if node.ty.isInteger() {
			switch node.ty.size {
			case 1:
				return int64(uint8(val))
			case 2:
				return int64(uint16(val))
			case 4:
				return int64(uint32(val))
			}
		}
		return val
	case ND_ADDR:
		return evalRval(node.lhs, label)
	case ND_MEMBER:
		if label == nil {
			errorTok(node.tok, "not a compile-time constant")
		}
		if node.ty.kind != TY_ARRAY {
			errorTok(node.tok, "invalid initializer")
		}
		return evalRval(node.lhs, label) + int64(node.member.offset)
	case ND_VAR:
		if label == nil {
			errorTok(node.tok, "not a compile-time constant")
		}
		if node.variable.ty.kind != TY_ARRAY && node.variable.ty.kind != TY_FUNC {
			errorTok(node.tok, "invalid initializer")
		}
		*label = node.variable.name
		return 0
	case ND_NUM:
		return node.val
	}

	errorTok(node.tok, "not a compile-time constant")
	return 0
}

func evalRval(node *Node, label *string) int64 {
	switch node.kind {
	case ND_VAR:
		if node.variable.isLocal {
			errorTok(node.tok, "not a compile-time constant")
		}
		*label = node.variable.name
		return 0
	case ND_DEREF:
		return eval2(node.lhs, label)
	case ND_MEMBER:
		return evalRval(node.lhs, label) + int64(node.member.offset)
	}

	errorTok(node.tok, "invalid initializer")
	return 0
}

func constExpr() int64 {
	node := conditional()
	return eval(node)
}

// while-stmt = "while" "(" expr ")" stmt
func whileStmt() *Node {
	st := gtok
	gtok = gtok.consume("while")
	gtok = gtok.consume("(")
	node := NewNode(ND_FOR, st)
	node.cond = expr()
	gtok = gtok.consume(")")

	brk := brkLabel // 保存当前的 break label
	node.breakLabel = newUniqueName()
	cont := contLabel // 保存当前的 continue label
	node.continueLabel = newUniqueName()
	contLabel = node.continueLabel
	brkLabel = node.breakLabel

	node.then = stmt()

	brkLabel = brk   // 恢复当前的 break label
	contLabel = cont // 恢复当前的 continue label
	return node
}

// for-stmt = "for" "(" expr-stmt expr? ";" expr? ")" stmt
func forStmt() *Node {
	st := gtok
	gtok = gtok.consume("for")
	gtok = gtok.consume("(")
	node := NewNode(ND_FOR, st)

	enterScope()

	brk := brkLabel // 保存当前的 break label
	node.breakLabel = newUniqueName()
	brkLabel = node.breakLabel
	cont := contLabel // 保存当前的 continue label
	node.continueLabel = newUniqueName()
	contLabel = node.continueLabel

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

	brkLabel = brk   // 恢复当前的 break label
	contLabel = cont // 恢复当前的 continue label
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

// assign    = conditional (assign-op assign)?
// assign-op = "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^="
// .         | "<<=" | ">>="
func assign() *Node {
	node := conditional()
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

	if gtok.equal("<<=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_SHL, node, assign(), st))
	}

	if gtok.equal(">>=") {
		gtok = gtok.next
		return toAssign(NewBinary(ND_SHR, node, assign(), st))
	}

	return node
}

// conditional = logor ("?" expr ":" conditional)?
func conditional() *Node {
	cond := logor()

	if !gtok.equal("?") {
		return cond
	}

	node := NewNode(ND_COND, gtok)
	node.cond = cond
	gtok = gtok.next
	node.then = expr()
	gtok = gtok.consume(":")
	node.els = conditional()
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

// relational = shift ("<" shift | "<=" shift | ">" shift | ">=" shift)*
func relational() *Node {
	node := shift()
	for {
		st := gtok
		if gtok.equal("<") {
			gtok = gtok.next
			node = NewBinary(ND_LT, node, shift(), st)
			continue
		}
		if gtok.equal("<=") {
			gtok = gtok.next
			node = NewBinary(ND_LE, node, shift(), st)
			continue
		}
		if gtok.equal(">") {
			gtok = gtok.next
			node = NewBinary(ND_LT, shift(), node, st)
			continue
		}
		if gtok.equal(">=") {
			gtok = gtok.next
			node = NewBinary(ND_LE, shift(), node, st)
			continue
		}

		return node
	}
}

// shift = add ("<<" add | ">>" add)*
func shift() *Node {
	node := add()

	for {
		st := gtok

		if gtok.equal("<<") {
			gtok = gtok.next
			node = NewBinary(ND_SHL, node, add(), st)
			continue
		}

		if gtok.equal(">>") {
			gtok = gtok.next
			node = NewBinary(ND_SHR, node, add(), st)
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
	idx := 0

	for !gtok.equal("}") {
		basety := declspec(nil)
		first := true

		for !tryConsume(";") {
			if !first {
				gtok = gtok.consume(",")
			}
			first = false

			mem := &Member{}
			mem.ty = declarator(basety)
			mem.name = mem.ty.name
			mem.idx = idx
			idx++
			cur.next = mem
			cur = cur.next
		}
	}

	// If the last element is an array of incomplete type, it's
	// called a "flexible array member". It should behave as if
	// if were a zero-sized array.
	if cur != &head && cur.ty.kind == TY_ARRAY && cur.ty.arrayLen < 0 {
		cur.ty = arrayOf(cur.ty.base, 0)
		ty.isFlexible = true
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

	// panic("expected an expression: " + gtok.literal)
	errorTok(gtok, "expected an expression: "+gtok.literal)
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
		var_ := newGVar(ty.name.literal, ty)
		if gtok.equal("=") {
			gtok = gtok.next
			gvarInitializer(var_)
		}
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
