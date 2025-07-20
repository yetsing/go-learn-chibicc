package main

import (
	"encoding/binary"
	"fmt"
	"math"
)

// #region Scope

// Scope for local variables, global variables, typedefs
// or enum constants
type VarScope struct {
	variable *Obj  // Variable
	typedef  *Type // Typedef
	enumTy   *Type // Enum type
	enumVal  int   // Enum value
}

// Represents a block scope.
type Scope struct {
	next *Scope // Next scope

	// C has two block scopes; one is for variables/typedefs and
	// the other is for struct/union/enum tags.
	vars map[string]*VarScope
	tags map[string]*Type
}

// Variable attributes such as typedef or extern.
type VarAttr struct {
	isTypedef bool
	isStatic  bool
	isExtern  bool
	isInline  bool
	isTls     bool
	align     int
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

	// Only one member can be initialized for a union.
	// `mem` is used to clarify which member is initialized.
	mem *Member
}

// For local variable initializer.
type InitDesg struct {
	next   *InitDesg // Next initializer
	idx    int
	member *Member
	var_   *Obj // Variable
}

var scope = &Scope{
	vars: make(map[string]*VarScope),
	tags: make(map[string]*Type),
}

func alignDown(n, align int) int {
	return alignTo(n-align+1, align)
}

func enterScope() {
	s := &Scope{
		vars: make(map[string]*VarScope),
		tags: make(map[string]*Type),
	}
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
	tok     *Token // Representative token
	isLocal bool   // local or global/function
	align   int    // Alignment in bytes

	// Local variable
	offset int // Offset from RBP

	// Global variable or function
	isFunction   bool
	isDefinition bool
	isStatic     bool

	// Global variable
	isTentative bool
	isTls       bool // Thread-local storage variable
	initData    []byte
	rel         *Relocation

	// Function
	isInline     bool
	params       *Obj
	body         *Node
	locals       *Obj
	vaArea       *Obj
	allocaBottom *Obj
	stackSize    int // Stack size

	// Static inline function
	isLive bool
	isRoot bool
	refs   []string
}

// Global variable can be initialized either by a constant expression
// or a pointer to another global variable. This struct represents the
// latter.
type Relocation struct {
	next   *Relocation // Next relocation
	offset int
	label  *string
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

var pbuiltinAlloca *Obj

// Find a local variable by name
func findVar(name string) *VarScope {
	for sc := scope; sc != nil; sc = sc.next {
		if sc2, ok := sc.vars[name]; ok {
			return sc2
		}
	}

	return nil
}

func findTag(tok *Token) *Type {
	// 第一层链表是 scope
	for sc := scope; sc != nil; sc = sc.next {
		if ty, ok := sc.tags[tok.literal]; ok {
			return ty
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
		align:   ty.align,
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
		align:   ty.align,
	}
	g.isStatic = true
	pushScope(name).variable = g
	g.isDefinition = true
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
	align  int
	offset int

	// Bitfield
	isBitfield bool
	bitOffset  int
	bitWidth   int
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
	ND_DO                 // "do"
	ND_SWITCH             // switch
	ND_CASE               // case
	ND_BLOCK              // Block { ... }
	ND_GOTO               // "goto"
	ND_GOTO_EXPR          // "goto" labels-as-values
	ND_LABEL              // Labeled statement
	ND_LABEL_VAL          // [GNU] Labels-as-values
	ND_FUNCALL            // Function call
	ND_EXPR_STMT          // Expression statement
	ND_STMT_EXPR          // Statement expression
	ND_VAR                // Variable
	ND_VLA_PTR            // VLA designator
	ND_NUM                // Integer
	ND_CAST               // Type cast
	ND_MEMZERO            // Zero-clear a stack variable
	ND_ASM                // "asm"
	ND_CAS                // Atomic compare-and-swap
	ND_EXCH               // Atomic exchange
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
	funcTy      *Type
	args        *Node
	passByStack bool
	retBuffer   *Obj

	// Goto or labeled statement, or labels-as-values
	label       string
	uniqueLabel string
	gotoNext    *Node

	// Switch
	caseNext    *Node
	defaultCase *Node

	// case
	begin int64
	end   int64

	// "asm" string literal
	asmStr string

	// Atomic compare-and-swap
	casAddr *Node
	casOld  *Node
	casNew  *Node

	// Atomic op= operators
	atomicAddr *Obj
	atomicExpr *Node

	// Variable
	variable *Obj // Used if kind is ND_VAR

	// Numeric literal
	val  int64 // Used if kind is ND_NUM
	fval float64
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

func NewUlong(val int64, tok *Token) *Node {
	return &Node{
		kind: ND_NUM,
		lhs:  nil,
		rhs:  nil,
		val:  val,
		tok:  tok,
		ty:   ulongType(),
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

func newVlaPtr(variable *Obj, tok *Token) *Node {
	node := NewNode(ND_VLA_PTR, tok)
	node.variable = variable
	return node
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
	vsc := &VarScope{}
	scope.vars[name] = vsc
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
	if lhs.ty.isNumeric() && rhs.ty.isNumeric() {
		return NewBinary(ND_ADD, lhs, rhs, tok)
	}

	if lhs.ty.base != nil && rhs.ty.base != nil {
		errorTok(tok, "invalid operands")
	}

	// Canonicalize `num + ptr` to `ptr + num`.
	if lhs.ty.base == nil && rhs.ty.base != nil {
		lhs, rhs = rhs, lhs
	}

	// VLA + num
	if lhs.ty.base.kind == TY_VLA {
		rhs = NewBinary(ND_MUL, rhs, NewVarNode(lhs.ty.base.vlaSize, tok), tok)
		return NewBinary(ND_ADD, lhs, rhs, tok)
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
	if lhs.ty.isNumeric() && rhs.ty.isNumeric() {
		return NewBinary(ND_SUB, lhs, rhs, tok)
	}

	// VLA + num
	if lhs.ty.base.kind == TY_VLA {
		rhs = NewBinary(ND_MUL, rhs, NewVarNode(lhs.ty.base.vlaSize, tok), tok)
		addType(rhs)
		node := NewBinary(ND_SUB, lhs, rhs, tok)
		node.ty = lhs.ty
		return node
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
		node.ty = longType()
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

	switch init.ty.base.size {
	case 1:
		s := gtok.str
		for i := range length {
			if i >= len(gtok.str) {
				// 不再末尾直接补 0 ，是因为有这种情况：char g19[3] = "foobar";
				// 他的末尾就不是 '\0'，而是 'o'。
				// C 字符串以 '\0' 结尾
				init.children[i].expr = NewNumber(0, gtok)
			} else {
				init.children[i].expr = NewNumber(int64(s[i]), gtok)
			}
		}
	case 2:
		bs := []byte(gtok.str)
		result := make([]uint16, len(bs)/2+1) // +1 for null terminator
		for i := range len(result) - 1 {
			result[i] = binary.LittleEndian.Uint16(bs[i*2:])
		}
		for i := range length {
			init.children[i].expr = NewNumber(int64(result[i]), gtok)
		}
	case 4:
		bs := []byte(gtok.str)
		result := make([]uint32, len(bs)/4+1) // +1 for null terminator
		for i := range len(result) - 1 {
			result[i] = binary.LittleEndian.Uint32(bs[i*4:])
		}
		for i := range length {
			init.children[i].expr = NewNumber(int64(result[i]), gtok)
		}
	default:
		unreachable()
	}

	gtok = gtok.next
}

// array-designator = "[" const-expr "]"
//
// C99 added the designated initializer to the language, which allows
// programmers to move the "cursor" of an initializer to any element.
// The syntax looks like this:
//
//	int x[10] = { 1, 2, [5]=3, 4, 5, 6, 7 };
//
// `[5]` moves the cursor to the 5th element, so the 5th element of x
// is set to 3. Initialization then continues forward in order, so
// 6th, 7th, 8th and 9th elements are initialized with 4, 5, 6 and 7,
// respectively. Unspecified elements (in this case, 3rd and 4th
// elements) are initialized with zero.
//
// Nesting is allowed, so the following initializer is valid:
//
//	int x[5][10] = { [5][8]=1, 2, 3 };
//
// It sets x[5][8], x[5][9] and x[6][0] to 1, 2 and 3, respectively.
//
// Use `.fieldname` to move the cursor for a struct initializer. E.g.
//
//	struct { int a, b, c; } x = { .c=5 };
//
// The above initializer sets x.c to 5.
func arrayDesignator(ty *Type, begin *int, end *int) {
	gtok = gtok.next
	*begin = int(constExpr())
	if *begin >= ty.arrayLen {
		errorTok(gtok, "array designator index exceeds array bounds")
	}

	if gtok.equal("...") {
		gtok = gtok.next
		*end = int(constExpr())
		if *end >= ty.arrayLen {
			errorTok(gtok, "array designator index exceeds array bounds")
		}
		if *end < *begin {
			errorTok(gtok, "array designator range [%d, %d] is empty", *begin, *end)
		}
	} else {
		*end = *begin
	}

	gtok = gtok.consume("]")
}

// struct-designator = "." ident
func structDesignator(ty *Type) *Member {
	start := gtok
	gtok = gtok.consume(".")
	if gtok.kind != TK_IDENT {
		errorTok(gtok, "expected a field designator")
	}

	for mem := ty.members; mem != nil; mem = mem.next {
		// Anonymous struct member
		if mem.ty.kind == TY_STRUCT && mem.name == nil {
			if getStructMember(mem.ty, gtok) != nil {
				gtok = start
				return mem
			}
			continue
		}

		// Regular struct member
		if mem.name.literal == gtok.literal {
			gtok = gtok.next
			return mem
		}
	}

	errorTok(gtok, "struct has no such member")
	return nil
}

// designation = ("[" const-expr "]" | "." ident)* "="? initializer
func designation(init *Initializer) {
	if gtok.equal("[") {
		if init.ty.kind != TY_ARRAY {
			errorTok(gtok, "array index in non-array initializer")
		}
		var begin int
		var end int
		arrayDesignator(init.ty, &begin, &end)

		var tok2 *Token
		st := gtok
		for i := begin; i <= end; i++ {
			designation(init.children[i])
			tok2 = gtok
			gtok = st
		}
		gtok = tok2
		arrayInitializer2(init, begin+1)
		return
	}

	if gtok.equal(".") && init.ty.kind == TY_STRUCT {
		mem := structDesignator(init.ty)
		designation(init.children[mem.idx])
		init.expr = nil
		structInitializer2(init, mem.next)
		return
	}

	if gtok.equal(".") && init.ty.kind == TY_UNION {
		mem := structDesignator(init.ty)
		init.mem = mem
		designation(init.children[mem.idx])
		return
	}

	if gtok.equal(".") {
		errorTok(gtok, "field name not in struct or union initializer")
	}

	if gtok.equal("=") {
		gtok = gtok.next
	}
	initializer2(init)
}

// An array length can be omitted if an array has an initializer
// (e.g. `int x[] = {1,2,3}`). If it's omitted, count the number
// of initializer elements.
func countArrayInitElements(ty *Type) int {
	first := true
	dummy := newInitializer(ty.base, true)

	i := 0
	maxN := 0

	for !consumeEnd() {
		if !first {
			gtok = gtok.consume(",")
		}
		first = false

		if gtok.equal("[") {
			gtok = gtok.next
			i = int(constExpr())
			if gtok.equal("...") {
				gtok = gtok.next
				i = int(constExpr())
			}
			gtok = gtok.consume("]")
			designation(dummy)
		} else {
			initializer2(dummy)
		}

		i++
		maxN = max(maxN, i)
	}
	return maxN
}

// array-initializer1 = "{" initializer ("," initializer)* ","? "}"
func arrayInitializer1(init *Initializer) {
	gtok = gtok.consume("{")

	if init.isFlexible {
		orig := gtok
		len := countArrayInitElements(init.ty)
		gtok = orig
		*init = *newInitializer(arrayOf(init.ty.base, len), false)
	}

	first := true

	if init.isFlexible {
		tok := gtok
		length := countArrayInitElements(init.ty)
		gtok = tok
		*init = *newInitializer(arrayOf(init.ty.base, length), false)
	}

	for i := 0; !consumeEnd(); i++ {
		if !first {
			gtok = gtok.consume(",")
		}
		first = false

		if gtok.equal("[") {
			var begin, end int
			arrayDesignator(init.ty, &begin, &end)

			var tok2 *Token
			st := gtok
			for j := begin; j <= end; j++ {
				designation(init.children[j])
				tok2 = gtok
				gtok = st
			}
			gtok = tok2
			i = end
			continue
		}

		if i < init.ty.arrayLen {
			initializer2(init.children[i])
		} else {
			gtok = skipExcessElement()
		}
	}
}

// array-initializer2 = initializer ("," initializer)*
func arrayInitializer2(init *Initializer, i int) {
	if init.isFlexible {
		tok := gtok
		length := countArrayInitElements(init.ty)
		gtok = tok
		*init = *newInitializer(arrayOf(init.ty.base, length), false)
	}

	for ; i < init.ty.arrayLen && !isEnd(gtok); i++ {
		start := gtok
		if i > 0 {
			gtok = gtok.consume(",")
		}

		if gtok.equal("[") || gtok.equal(".") {
			gtok = start
			return
		}

		initializer2(init.children[i])
	}
}

// struct-initializer1 = "{" initializer ("," initializer)* ","? "}"
func structInitializer1(init *Initializer) {
	gtok = gtok.consume("{")

	mem := init.ty.members
	first := true

	for !consumeEnd() {
		if !first {
			gtok = gtok.consume(",")
		}
		first = false

		if gtok.equal(".") {
			mem = structDesignator(init.ty)
			designation(init.children[mem.idx])
			mem = mem.next
			continue
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
func structInitializer2(init *Initializer, mem *Member) {
	first := true

	for ; mem != nil && !isEnd(gtok); mem = mem.next {
		start := gtok

		if !first {
			gtok = gtok.consume(",")
		}
		first = false

		if gtok.equal("[") || gtok.equal(".") {
			gtok = start
			return
		}

		initializer2(init.children[mem.idx])
	}
}

func unionInitializer(init *Initializer) {
	// Unlike structs, union initializers take only one initializer,
	// and that initializes the first union member by default.
	// You can initialize other member using a designated initializer.
	if gtok.equal("{") && gtok.next.equal(".") {
		gtok = gtok.next
		mem := structDesignator(init.ty)
		init.mem = mem
		designation(init.children[mem.idx])
		gtok = gtok.consume("}")
		return
	}

	init.mem = init.ty.members

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
			arrayInitializer2(init, 0)
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
		structInitializer2(init, init.ty.members)
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
		mem := ty.members
		if init.mem != nil {
			mem = init.mem
		}
		desg2 := InitDesg{desg, 0, mem, nil}
		return createLvarInit(init.children[mem.idx], mem.ty, &desg2, tok)
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

func readBuf(buf []byte, sz int) (val uint64) {
	switch sz {
	case 1:
		val = uint64(buf[0])
	case 2:
		val = uint64(buf[0]) | (uint64(buf[1]) << 8)
	case 4:
		val = uint64(buf[0]) | (uint64(buf[1]) << 8) |
			(uint64(buf[2]) << 16) | (uint64(buf[3]) << 24)
	case 8:
		val = uint64(buf[0]) | (uint64(buf[1]) << 8) |
			(uint64(buf[2]) << 16) | (uint64(buf[3]) << 24) |
			(uint64(buf[4]) << 32) | (uint64(buf[5]) << 40) |
			(uint64(buf[6]) << 48) | (uint64(buf[7]) << 56)
	default:
		unreachable()
	}
	return val
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
			if mem.isBitfield {
				expr := init.children[mem.idx].expr
				if expr == nil {
					break
				}

				loc := buf[offset+mem.offset:]
				oldval := readBuf(loc, mem.ty.size)
				newval := uint64(eval(expr))
				mask := uint64((1 << mem.bitWidth) - 1)
				combined := (oldval | ((newval & mask) << uint64(mem.bitOffset)))
				loc = writeBuf(combined, mem.ty.size)
				copy(buf[offset+mem.offset:], loc)
			} else {
				cur = writeGvarData(cur, init.children[mem.idx], mem.ty, buf, offset+mem.offset)
			}
		}
		return cur
	}

	if ty.kind == TY_UNION {
		if init.mem == nil {
			return cur
		}
		return writeGvarData(cur, init.children[init.mem.idx], init.mem.ty, buf, offset)
	}

	if init.expr == nil {
		return cur
	}

	if ty.kind == TY_FLOAT {
		val := evalDouble(init.expr)
		bits := math.Float32bits(float32(val))
		binary.LittleEndian.PutUint32(buf[offset:], bits)
		return cur
	}

	if ty.kind == TY_DOUBLE {
		val := evalDouble(init.expr)
		bits := math.Float64bits(val)
		binary.LittleEndian.PutUint64(buf[offset:], bits)
		return cur
	}

	var label *string = nil
	val := eval2(init.expr, &label)

	if label == nil {
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
	kw := map[string]bool{
		"void":          true,
		"_Bool":         true,
		"char":          true,
		"short":         true,
		"int":           true,
		"long":          true,
		"struct":        true,
		"union":         true,
		"typedef":       true,
		"enum":          true,
		"static":        true,
		"extern":        true,
		"_Alignas":      true,
		"signed":        true,
		"unsigned":      true,
		"const":         true,
		"volatile":      true,
		"auto":          true,
		"register":      true,
		"restrict":      true,
		"__restrict":    true,
		"__restrict__":  true,
		"_Noreturn":     true,
		"float":         true,
		"double":        true,
		"typeof":        true,
		"inline":        true,
		"_Thread_local": true,
		"__thread":      true,
		"_Atomic":       true,
	}
	if _, ok := kw[tok.literal]; ok {
		return true
	}
	return findTypedef(tok) != nil
}

// #endregion

// #region Parser

func pushTagScope(tok *Token, ty *Type) {
	scope.tags[tok.literal] = ty
}

// declspec = ("void" | "_Bool" | "char" | "short" | "int" | "long"
// .           | "typedef" | "static" | "extern" | "inline"
// .           | "_Thread_local" | "__thread"
// .           | "signed" | "unsigned"
// .           | struct-decl | union-decl | typedef-name
// .           | enum-specifier | typeof-specifier
// .           | "const" | "volatile" | "auto" | "register" | "restrict"
// .           | "__restrict" | "__restrict__" | "_Noreturn")+
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
	FLOAT := 1 << 12
	DOUBLE := 1 << 14
	OTHER := 1 << 16
	SIGNED := 1 << 17
	UNSIGNED := 1 << 18

	ty := intType()
	counter := 0
	isAtomic := false

	for isTypename(gtok) {
		// Handle storage class specifiers.
		if gtok.equal("typedef") || gtok.equal("static") || gtok.equal("extern") ||
			gtok.equal("inline") || gtok.equal("_Thread_local") ||
			gtok.equal("__thread") {
			if attr == nil {
				errorTok(gtok, "storage class specifier is not allowed in this context")
			}

			if gtok.equal("typedef") {
				attr.isTypedef = true
			} else if gtok.equal("static") {
				attr.isStatic = true
			} else if gtok.equal("extern") {
				attr.isExtern = true
			} else if gtok.equal("inline") {
				attr.isInline = true
			} else {
				attr.isTls = true
			}

			if attr.isTypedef && (attr.isStatic || attr.isExtern || attr.isInline || attr.isTls) {
				errorTok(gtok, "typedef may not be used together with static, extern or inline, __thread or _Thread_local")
			}
			gtok = gtok.next
			continue
		}

		// These keywords are recognized but ignored.
		if tryConsume("const") ||
			tryConsume("volatile") ||
			tryConsume("auto") ||
			tryConsume("register") ||
			tryConsume("restrict") ||
			tryConsume("__restrict") ||
			tryConsume("__restrict__") ||
			tryConsume("_Noreturn") {
			continue
		}

		if gtok.equal("_Atomic") {
			gtok = gtok.next
			if gtok.equal("(") {
				gtok = gtok.next
				ty = typename()
				gtok = gtok.consume(")")
			}
			isAtomic = true
			continue
		}

		if gtok.equal("_Alignas") {
			if attr == nil {
				errorTok(gtok, "_Alignas is not allowed in this context")
			}
			gtok = gtok.next.consume("(")

			if isTypename(gtok) {
				attr.align = typename().align
			} else {
				attr.align = int(constExpr())
			}
			gtok = gtok.consume(")")
			continue
		}

		// Handle user-defined types.
		ty2 := findTypedef(gtok)
		if gtok.equal("struct") || gtok.equal("union") || gtok.equal("enum") || gtok.equal("typeof") || ty2 != nil {
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
			} else if gtok.equal("typeof") {
				gtok = gtok.next
				ty = typeofSpecifier()
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
		} else if gtok.equal("float") {
			counter += FLOAT
		} else if gtok.equal("double") {
			counter += DOUBLE
		} else if gtok.equal("signed") {
			counter |= SIGNED
		} else if gtok.equal("unsigned") {
			counter |= UNSIGNED
		} else {
			unreachable()
		}

		switch counter {
		case VOID:
			ty = voidType()
		case BOOL:
			ty = boolType()
		case CHAR:
			fallthrough
		case SIGNED + CHAR:
			ty = charType()
		case UNSIGNED + CHAR:
			ty = ucharType()
		case SHORT:
			fallthrough
		case SHORT + INT:
			fallthrough
		case SIGNED + SHORT:
			fallthrough
		case SIGNED + SHORT + INT:
			ty = shortType()
		case UNSIGNED + SHORT:
			fallthrough
		case UNSIGNED + SHORT + INT:
			ty = ushortType()
		case INT:
			fallthrough
		case SIGNED:
			fallthrough
		case SIGNED + INT:
			ty = intType()
		case UNSIGNED:
			fallthrough
		case UNSIGNED + INT:
			ty = uintType()
		case LONG:
			fallthrough
		case LONG + INT:
			fallthrough
		case LONG + LONG:
			fallthrough
		case LONG + LONG + INT:
			fallthrough
		case SIGNED + LONG:
			fallthrough
		case SIGNED + LONG + INT:
			fallthrough
		case SIGNED + LONG + LONG:
			fallthrough
		case SIGNED + LONG + LONG + INT:
			ty = longType()
		case UNSIGNED + LONG:
			fallthrough
		case UNSIGNED + LONG + INT:
			fallthrough
		case UNSIGNED + LONG + LONG:
			fallthrough
		case UNSIGNED + LONG + LONG + INT:
			ty = ulongType()
		case FLOAT:
			ty = floatType()
		case DOUBLE:
			ty = doubleType()
		case LONG + DOUBLE:
			ty = ldoubleType()
		default:
			errorTok(gtok, "invalid type specifier")
		}

		gtok = gtok.next
	}

	if isAtomic {
		ty = ty.copy()
		ty.isAtomic = true
	}

	return ty
}

// func-params = ("void" | param ("," param)* ("," "...")?)? ")"
// param       = declspec declarator
func funcParams(ty *Type) *Type {
	if gtok.equal("void") && gtok.next.equal(")") {
		gtok = gtok.next.next
		return funcType(ty)
	}

	var head = Type{}
	cur := &head
	isVariadic := false

	for !gtok.equal(")") {
		if cur != &head {
			gtok = gtok.consume(",")
		}

		if gtok.equal("...") {
			isVariadic = true
			gtok = gtok.next
			break
		}

		ty2 := declspec(nil)
		ty2 = declarator(ty2)

		name := ty2.name

		if ty2.kind == TY_ARRAY {
			// "array of T" is converted to "pointer to T" only in the parameter
			// context. For example, *argv[] is converted to **argv by this.
			name := ty2.name
			ty2 = pointerTo(ty2.base)
			ty2.name = name
		} else if ty2.kind == TY_FUNC {
			// Likewise, a function is converted to a pointer to a function
			// only in the parameter context.
			ty2 = pointerTo(ty2)
			ty2.name = name
		}

		cur.next = ty2
		cur = cur.next
	}

	if cur == &head {
		isVariadic = true
	}

	gtok = gtok.consume(")")
	ty = funcType(ty)
	ty.params = head.next
	ty.isVariadic = isVariadic
	return ty
}

// array-dimensions = ("static" | "restrict")* const-expr? "]" type-suffix
func arrayDimensions(ty *Type) *Type {
	for gtok.equal("static") || gtok.equal("restrict") {
		gtok = gtok.next
	}

	if gtok.equal("]") {
		gtok = gtok.next
		ty = typeSuffix(ty)
		return arrayOf(ty, -1)
	}

	expr := conditional()
	gtok = gtok.consume("]")
	ty = typeSuffix(ty)

	if ty.kind == TY_VLA || !isConstExpr(expr) {
		return vlaOf(ty, expr)
	}
	return arrayOf(ty, int(eval(expr)))
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

// pointers = ("*" ("const" | "volatile" | "restrict")*)*
func pointers(ty *Type) *Type {
	for tryConsume("*") {
		ty = pointerTo(ty)
		for gtok.equal("const") ||
			gtok.equal("volatile") ||
			gtok.equal("restrict") ||
			gtok.equal("__restrict") ||
			gtok.equal("__restrict__") {
			gtok = gtok.next
		}
	}

	return ty
}

// ref: https://www.sigbus.info/compilerbook#type
// declarator = pointers ("(" ident ")" | "(" declarator ")" | ident) type-suffix
func declarator(ty *Type) *Type {
	ty = pointers(ty)

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

	var name *Token
	namePos := gtok

	if gtok.kind == TK_IDENT {
		name = gtok
		gtok = gtok.next
	}

	ty = typeSuffix(ty)
	ty.name = name
	ty.namePos = namePos
	return ty
}

// abstract-declarator = pointers ("(" abstract-declarator ")")? type-suffix
func abstractDeclarator(ty *Type) *Type {
	ty = pointers(ty)

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

// typeof-specifier = "(" (expr | typename) ")"
func typeofSpecifier() *Type {
	gtok = gtok.consume("(")

	var ty *Type
	if isTypename(gtok) {
		ty = typename()
	} else {
		expr := expr()
		addType(expr)
		ty = expr.ty
	}
	gtok = gtok.consume(")")
	return ty
}

// Generate code for computing a VLA size.
func computeVlaSize(ty *Type, tok *Token) *Node {
	node := NewNode(ND_NULL_EXPR, tok)
	if ty.base != nil {
		node = NewBinary(ND_COMMA, node, computeVlaSize(ty.base, tok), tok)
	}

	if ty.kind != TY_VLA {
		return node
	}

	var basesz *Node
	if ty.base.kind == TY_VLA {
		basesz = NewVarNode(ty.base.vlaSize, tok)
	} else {
		basesz = NewNumber(int64(ty.base.size), tok)
	}

	ty.vlaSize = newLVar("", ulongType())
	expr := NewBinary(ND_ASSIGN, NewVarNode(ty.vlaSize, tok), NewBinary(ND_MUL, ty.vlaLen, basesz, tok), tok)
	return NewBinary(ND_COMMA, node, expr, tok)
}

func newAlloca(sz *Node) *Node {
	node := NewUnary(ND_FUNCALL, NewVarNode(pbuiltinAlloca, sz.tok), sz.tok)
	node.funcTy = pbuiltinAlloca.ty
	node.ty = pbuiltinAlloca.ty.returnTy
	node.args = sz
	addType(sz)
	return node
}

// declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
func declaration(basety *Type, attr *VarAttr) *Node {
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
		if ty.name == nil {
			errorTok(ty.namePos, "variable name omitted")
		}

		if attr != nil && attr.isStatic {
			// static local variable
			var_ := newAnonGvar(ty)
			pushScope(ty.name.literal).variable = var_
			if gtok.equal("=") {
				gtok = gtok.next
				gvarInitializer(var_)
			}
			continue
		}

		// Generate code for computing a VLA size. We need to do this
		// even if ty is not VLA because ty may be a pointer to VLA
		// (e.g. int (*foo)[n][m] where n and m are variables.)
		cur.next = NewUnary(ND_EXPR_STMT, computeVlaSize(ty, gtok), gtok)
		cur = cur.next

		if ty.kind == TY_VLA {
			if gtok.equal("=") {
				errorTok(gtok, "variable-sized object may not be initialized")
			}

			// Variable length arrays (VLAs) are translated to alloca() calls.
			// For example, `int x[n+2]` is translated to `tmp = n + 2,
			// x = alloca(tmp)`.
			var_ := newLVar(ty.name.literal, ty)
			tok := ty.name
			expr := NewBinary(ND_ASSIGN, newVlaPtr(var_, tok), newAlloca(NewVarNode(ty.vlaSize, tok)), tok)
			cur.next = NewUnary(ND_EXPR_STMT, expr, tok)
			cur = cur.next
			continue
		}

		variable := newLVar(ty.name.literal, ty)
		if attr != nil && attr.align > 0 {
			variable.align = attr.align
		}

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

// asm-stmt = "asm" ("volatile" | "inline")* "(" string-literal ")"
func asmStmt() *Node {
	node := NewNode(ND_ASM, gtok)
	gtok = gtok.next

	for gtok.equal("volatile") || gtok.equal("inline") {
		gtok = gtok.next
	}

	gtok = gtok.consume("(")
	if gtok.kind != TK_STR || gtok.ty.base.kind != TY_CHAR {
		errorTok(gtok, "expected string literal")
	}
	node.asmStr = gtok.str
	gtok = gtok.next.consume(")")
	return node
}

// stmt = "return" expr? ";"
// .    | if-stmt
// .    | "switch" "(" expr ")" stmt
// .    | "case" const-expr ("..." const-expr)? ":" stmt
// .    | "default" ":" stmt
// .    | for-stmt
// .    | while-stmt
// .    | "do" stmt "while" "(" expr ")" ";"
// .    | "asm" asm-stmt
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
		node := NewNode(ND_RETURN, st)
		if tryConsume(";") {
			return node
		}

		expr := expr()
		gtok = gtok.consume(";")

		addType(expr)
		ty := pcurrentFn.ty.returnTy
		if ty.kind != TY_STRUCT && ty.kind != TY_UNION {
			expr = NewCast(expr, pcurrentFn.ty.returnTy)
		}
		node.lhs = expr
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
			errorTok(gtok, "stray case")
		}

		node := NewNode(ND_CASE, gtok)
		gtok = gtok.next
		begin := constExpr()
		end := int64(0)

		if gtok.equal("...") {
			gtok = gtok.next
			// [GNU] Case ranges, e.g. "case 1 ... 5:"
			end = constExpr()
			if end < begin {
				errorTok(gtok, "empty case range specified")
			}
		} else {
			end = begin
		}

		gtok = gtok.consume(":")
		node.label = newUniqueName()
		node.lhs = stmt()
		node.begin = begin
		node.end = end
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

	if gtok.equal("do") {
		node := NewNode(ND_DO, gtok)

		brk := brkLabel   // 保存当前的 break label
		cont := contLabel // 保存当前的 continue label
		brkLabel = newUniqueName()
		contLabel = newUniqueName()
		node.breakLabel = brkLabel
		node.continueLabel = contLabel

		gtok = gtok.next
		node.then = stmt()

		brkLabel = brk   // 恢复当前的 break label
		contLabel = cont // 恢复当前的 continue label

		gtok = gtok.consume("while")
		gtok = gtok.consume("(")
		node.cond = expr()
		gtok = gtok.consume(")")
		gtok = gtok.consume(";")
		return node
	}

	if gtok.equal("asm") {
		return asmStmt()
	}

	if gtok.equal("goto") {
		if gtok.next.equal("*") {
			// [GNU] `goto *ptr` jumps to the address specified by `ptr`.
			node := NewNode(ND_GOTO_EXPR, gtok)
			gtok = gtok.next.next
			node.lhs = expr()
			gtok = gtok.consume(";")
			return node
		}

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
func eval2(node *Node, label **string) int64 {
	addType(node)

	if node.ty.isFlonum() {
		return int64(evalDouble(node))
	}

	switch node.kind {
	case ND_ADD:
		return eval2(node.lhs, label) + eval(node.rhs)
	case ND_SUB:
		return eval2(node.lhs, label) - eval(node.rhs)
	case ND_MUL:
		return eval(node.lhs) * eval(node.rhs)
	case ND_DIV:
		if node.ty.isUnsigned {
			return int64(uint64(eval(node.lhs)) / uint64(eval(node.rhs)))
		}
		return eval(node.lhs) / eval(node.rhs)
	case ND_NEG:
		return -eval(node.lhs)
	case ND_MOD:
		if node.ty.isUnsigned {
			return int64(uint64(eval(node.lhs)) % uint64(eval(node.rhs)))
		}
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
		if node.ty.isUnsigned && node.ty.size == 8 {
			return int64(uint64(eval(node.lhs)) >> uint64(eval(node.rhs)))
		}
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
		if node.lhs.ty.isUnsigned {
			if uint64(eval(node.lhs)) < uint64(eval(node.rhs)) {
				return 1
			}
			return 0
		}
		if eval(node.lhs) < eval(node.rhs) {
			return 1
		}
		return 0
	case ND_LE:
		if node.lhs.ty.isUnsigned {
			if uint64(eval(node.lhs)) <= uint64(eval(node.rhs)) {
				return 1
			}
			return 0
		}
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
				if node.ty.isUnsigned {
					return int64(uint8(val))
				} else {
					return int64(int8(val))
				}
			case 2:
				if node.ty.isUnsigned {
					return int64(uint16(val))
				} else {
					return int64(int16(val))
				}
			case 4:
				if node.ty.isUnsigned {
					return int64(uint32(val))
				} else {
					return int64(int32(val))
				}
			}
		}
		return val
	case ND_ADDR:
		return evalRval(node.lhs, label)
	case ND_LABEL_VAL:
		*label = &node.uniqueLabel
		return 0
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
		*label = &node.variable.name
		return 0
	case ND_NUM:
		return node.val
	}

	errorTok(node.tok, "not a compile-time constant")
	return 0
}

func evalRval(node *Node, label **string) int64 {
	switch node.kind {
	case ND_VAR:
		if node.variable.isLocal {
			errorTok(node.tok, "not a compile-time constant")
		}
		*label = &node.variable.name
		return 0
	case ND_DEREF:
		return eval2(node.lhs, label)
	case ND_MEMBER:
		return evalRval(node.lhs, label) + int64(node.member.offset)
	}

	errorTok(node.tok, "invalid initializer")
	return 0
}

func isConstExpr(node *Node) bool {
	addType(node)

	switch node.kind {
	case ND_ADD, ND_SUB, ND_MUL, ND_DIV,
		ND_BITAND, ND_BITOR, ND_BITXOR,
		ND_SHL, ND_SHR, ND_EQ, ND_NE, ND_LT, ND_LE,
		ND_LOGAND, ND_LOGOR:
		return isConstExpr(node.lhs) && isConstExpr(node.rhs)
	case ND_COND:
		if !isConstExpr(node.cond) {
			return false
		}
		if eval(node.cond) != 0 {
			return isConstExpr(node.then)
		}
		return isConstExpr(node.els)
	case ND_COMMA:
		return isConstExpr(node.rhs)
	case ND_NEG, ND_NOT, ND_BITNOT, ND_CAST:
		return isConstExpr(node.lhs)
	case ND_NUM:
		return true
	}
	return false
}

func constExpr() int64 {
	node := conditional()
	return eval(node)
}

func evalDouble(node *Node) float64 {
	addType(node)

	if node.ty.isInteger() {
		if node.ty.isUnsigned {
			return float64(uint64(eval(node)))
		}
		return float64(eval(node))
	}

	switch node.kind {
	case ND_ADD:
		return evalDouble(node.lhs) + evalDouble(node.rhs)
	case ND_SUB:
		return evalDouble(node.lhs) - evalDouble(node.rhs)
	case ND_MUL:
		return evalDouble(node.lhs) * evalDouble(node.rhs)
	case ND_DIV:
		return evalDouble(node.lhs) / evalDouble(node.rhs)
	case ND_NEG:
		return -evalDouble(node.lhs)
	case ND_COND:
		if evalDouble(node.cond) != 0 {
			return evalDouble(node.then)
		}
		return evalDouble(node.els)
	case ND_COMMA:
		return evalDouble(node.rhs)
	case ND_CAST:
		if node.lhs.ty.isFlonum() {
			return evalDouble(node.lhs)
		}
		return float64(eval(node.lhs))
	case ND_NUM:
		return node.fval
	}

	errorTok(node.tok, "not a compile-time constant")
	return 0.0
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
		node.init = declaration(basety, nil)
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

			if isFunctionDefinition() {
				function(basety, &attr)
				continue
			}

			if attr.isExtern {
				globalVariable(basety, &attr)
				continue
			}

			cur.next = declaration(basety, &attr)
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
// Convert op= operators to expressions containing an assignment.
//
// In general, `A op= C` is converted to “tmp = &A, *tmp = *tmp op B`.
// However, if a given expression is of form `A.x op= C`, the input is
// converted to `tmp = &A, (*tmp).x = (*tmp).x op C` to handle assignments
// to bitfields.
func toAssign(binary *Node) *Node {
	addType(binary.lhs)
	addType(binary.rhs)
	tok := binary.tok

	// Convert `A.x op= C` to `tmp = &A, (*tmp).x = (*tmp).x op C`.
	if binary.lhs.kind == ND_MEMBER {
		var_ := newLVar("", pointerTo(binary.lhs.lhs.ty))

		expr1 := NewBinary(ND_ASSIGN, NewVarNode(var_, tok),
			NewUnary(ND_ADDR, binary.lhs.lhs, tok), tok)

		expr2 := NewUnary(ND_MEMBER, NewUnary(ND_DEREF, NewVarNode(var_, tok), tok), tok)
		expr2.member = binary.lhs.member

		expr3 := NewUnary(ND_MEMBER, NewUnary(ND_DEREF, NewVarNode(var_, tok), tok), tok)
		expr3.member = binary.lhs.member

		expr4 := NewBinary(ND_ASSIGN, expr2, NewBinary(binary.kind, expr3, binary.rhs, tok), tok)

		return NewBinary(ND_COMMA, expr1, expr4, tok)
	}

	// If A is an atomic type, Convert `A op= B` to
	//
	// ({
	//   T1 *addr = &A; T2 val = (B); T1 old = *addr; T1 new;
	//   do {
	//    new = old op val;
	//   } while (!atomic_compare_exchange_strong(addr, &old, new));
	//   new;
	// })
	if binary.lhs.ty.isAtomic {
		var head Node
		cur := &head

		addr := newLVar("", pointerTo(binary.lhs.ty))
		val := newLVar("", binary.rhs.ty)
		old := newLVar("", binary.lhs.ty)
		new := newLVar("", binary.lhs.ty)

		cur.next = NewUnary(
			ND_EXPR_STMT,
			NewBinary(ND_ASSIGN, NewVarNode(addr, tok),
				NewUnary(ND_ADDR, binary.lhs, tok), tok),
			tok)
		cur = cur.next

		cur.next = NewUnary(
			ND_EXPR_STMT,
			NewBinary(ND_ASSIGN, NewVarNode(val, tok), binary.rhs, tok),
			tok)
		cur = cur.next

		cur.next = NewUnary(
			ND_EXPR_STMT,
			NewBinary(ND_ASSIGN, NewVarNode(old, tok),
				NewUnary(ND_DEREF, NewVarNode(addr, tok), tok), tok),
			tok)
		cur = cur.next

		loop := NewNode(ND_DO, tok)
		loop.breakLabel = newUniqueName()
		loop.continueLabel = newUniqueName()

		body := NewBinary(
			ND_ASSIGN,
			NewVarNode(new, tok),
			NewBinary(binary.kind, NewVarNode(old, tok), NewVarNode(val, tok), tok),
			tok)

		loop.then = NewNode(ND_BLOCK, tok)
		loop.then.body = NewUnary(ND_EXPR_STMT, body, tok)

		cas := NewNode(ND_CAS, tok)
		cas.casAddr = NewVarNode(addr, tok)
		cas.casOld = NewUnary(ND_ADDR, NewVarNode(old, tok), tok)
		cas.casNew = NewVarNode(new, tok)
		loop.cond = NewUnary(ND_NOT, cas, tok)

		cur.next = loop
		cur = cur.next
		cur.next = NewUnary(ND_EXPR_STMT, NewVarNode(new, tok), tok)
		cur = cur.next

		node := NewNode(ND_STMT_EXPR, tok)
		node.body = head.next
		return node
	}

	// Convert `A op= B` to ``tmp = &A, *tmp = *tmp op B`.
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

// conditional = logor ("?" expr? ":" conditional)?
func conditional() *Node {
	cond := logor()

	if !gtok.equal("?") {
		return cond
	}

	if gtok.next.equal(":") {
		start := gtok
		// [GNU] Compile `a ?: b` as `tmp = a, tmp ? tmp : b`.
		addType(cond)
		var_ := newLVar("", cond.ty)
		lhs := NewBinary(ND_ASSIGN, NewVarNode(var_, start), cond, start)
		rhs := NewNode(ND_COND, start)
		rhs.cond = NewVarNode(var_, start)
		rhs.then = NewVarNode(var_, start)
		gtok = gtok.next.next // Skip `?:`
		rhs.els = conditional()
		return NewBinary(ND_COMMA, lhs, rhs, start)
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

		// compound literal
		if gtok.equal("{") {
			gtok = st
			return unary()
		}

		// type cast
		node := NewCast(cast(), ty)
		node.tok = st
		return node
	}

	return unary()
}

// unary = ( ("+" | "-" | "*" | "&" | "!" | "~") cast )
// .     | ("++" | "--") unary
// .     | "&&" ident
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
		lhs := cast()
		addType(lhs)
		if lhs.kind == ND_MEMBER && lhs.member.isBitfield {
			errorTok(gtok, "cannot take address of a bitfield")
		}
		return NewUnary(ND_ADDR, lhs, st)
	}

	if gtok.equal("*") {
		// [https://www.sigbus.info/n1570#6.5.3.2p4] This is an oddity
		// in the C spec, but dereferencing a function shouldn't do
		// anything. If foo is a function, `*foo`, `**foo` or `*****foo`
		// are all equivalent to just `foo`.
		gtok = gtok.next
		node := cast()
		addType(node)
		if node.ty.kind == TY_FUNC {
			return node
		}
		return NewUnary(ND_DEREF, node, st)
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

	// [GNU] labels-as-values
	if gtok.equal("&&") {
		node := NewNode(ND_LABEL_VAL, gtok)
		node.label = gtok.next.literal
		node.gotoNext = gotos
		gotos = node
		gtok = gtok.next.next // Skip `&&` and the label
		return node
	}

	return postfix()
}

// struct-members = (declspec declarator (","  declarator)* ";")*
func structMembers(ty *Type) {
	var head Member
	cur := &head
	idx := 0

	for !gtok.equal("}") {
		attr := VarAttr{}
		basety := declspec(&attr)
		first := true

		// Anonymous struct member
		if (basety.kind == TY_STRUCT || basety.kind == TY_UNION) && tryConsume(";") {
			mem := &Member{}
			mem.ty = basety
			mem.idx = idx
			idx++
			if attr.align != 0 {
				mem.align = attr.align
			} else {
				mem.align = mem.ty.align
			}
			cur.next = mem
			cur = cur.next
			continue
		}

		// Regular struct members
		for !tryConsume(";") {
			if !first {
				gtok = gtok.consume(",")
			}
			first = false

			mem := &Member{}
			mem.ty = declarator(basety)
			mem.name = mem.ty.name
			mem.idx = idx
			if attr.align != 0 {
				mem.align = attr.align
			} else {
				mem.align = mem.ty.align
			}
			idx++

			if tryConsume(":") {
				mem.isBitfield = true
				mem.bitWidth = int(constExpr())
			}

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
		if ty2, ok := scope.tags[tag.literal]; ok {
			*ty2 = *ty
			return ty2
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
	bits := 0
	for m := ty.members; m != nil; m = m.next {
		// 每个成员的地址必须是其类型大小的整数倍（对齐要求）
		if m.isBitfield && m.bitWidth == 0 {
			// Zero-width anonymous bitfield has a special meaning.
			// It affects only alignment.
			bits = alignTo(bits, m.ty.size*8)
		} else if m.isBitfield {
			sz := m.ty.size
			if (bits / (sz * 8)) != (bits+m.bitWidth-1)/(sz*8) {
				bits = alignTo(bits, sz*8)
			}

			m.offset = alignDown(bits/8, sz)
			m.bitOffset = bits % (sz * 8)
			bits += m.bitWidth
		} else {
			bits = alignTo(bits, m.align*8)
			m.offset = bits / 8
			bits += m.ty.size * 8
		}

		// 结构体的整体大小必须是其最大对齐要求的整数倍
		if ty.align < m.align {
			ty.align = m.align
		}
	}

	ty.size = alignTo(bits, ty.align*8) / 8
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
		if ty.align < mem.align {
			ty.align = mem.align
		}
		if ty.size < mem.ty.size {
			ty.size = mem.ty.size
		}
	}
	ty.size = alignTo(ty.size, ty.align)
	return ty
}

// Find a struct member by name.
func getStructMember(ty *Type, tok *Token) *Member {
	for m := ty.members; m != nil; m = m.next {
		// Anonymous struct member
		if (m.ty.kind == TY_STRUCT || m.ty.kind == TY_UNION) && m.name == nil {
			if getStructMember(m.ty, tok) != nil {
				return m
			}
			continue
		}

		// Regular struct member
		if m.name.equal(tok.literal) {
			return m
		}
	}
	return nil
}

// Create a node representing a struct member access, such as foo.bar
// where foo is a struct and bar is a member name.
//
// C has a feature called "anonymous struct" which allows a struct to
// have another unnamed struct as a member like this:
//
//	struct { struct { int a; }; int b; } x;
//
// The members of an anonymous struct belong to the outer struct's
// member namespace. Therefore, in the above example, you can access
// member "a" of the anonymous struct as "x.a".
//
// This function takes care of anonymous structs.
func structRef(node *Node, tok *Token) *Node {
	addType(node)
	if node.ty.kind != TY_STRUCT && node.ty.kind != TY_UNION {
		errorTok(node.tok, "not a struct nor a union")
	}

	ty := node.ty

	for {
		mem := getStructMember(ty, tok)
		if mem == nil {
			errorTok(tok, "no such member")
		}
		node = NewUnary(ND_MEMBER, node, tok)
		node.member = mem
		if mem.name != nil {
			break
		}
		ty = mem.ty
	}
	return node
}

// Convert A++ to `(typeof A)((A += 1) - 1)`
func newIncDec(node *Node, tok *Token, addend int) *Node {
	addType(node)
	add := newAdd(node, NewNumber(int64(addend), tok), tok)
	add = newAdd(toAssign(add), NewNumber(int64(-addend), tok), tok)
	return NewCast(add, node.ty)
}

// postfix = "(" type-name ")" "{" initializer-list "}"
// .       = ident "(" func-args ")" postfix-tail*
// .       | primary postfix-tail*
//
// postfix-tail = "[" expr "]"
// .            | "(" func-args ")"
// .            | "." ident
// .            | "->" ident
// .            | "++"
// .            | "--"
func postfix() *Node {
	if gtok.equal("(") && isTypename(gtok.next) {
		// compound literal
		start := gtok
		gtok = gtok.next
		ty := typename()
		gtok = gtok.consume(")")

		if scope.next == nil {
			var_ := newAnonGvar(ty)
			gvarInitializer(var_)
			return NewVarNode(var_, start)
		}

		var_ := newLVar("", ty)
		start2 := gtok
		lhs := lvarInitializer(var_)
		rhs := NewVarNode(var_, start2)
		return NewBinary(ND_COMMA, lhs, rhs, start)
	}

	node := primary()

	for {
		if gtok.equal("(") {
			gtok = gtok.next
			node = funcall(node)
			continue
		}

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
			node = structRef(node, gtok)
			gtok = gtok.next
			continue
		}

		if gtok.equal("->") {
			// x->y is short for (*x).y
			node = NewUnary(ND_DEREF, node, gtok)
			gtok = gtok.next
			node = structRef(node, gtok)
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

// funcall = (assign ("," assign)*)? ")"
func funcall(fn *Node) *Node {
	addType(fn)

	if fn.ty.kind != TY_FUNC && (fn.ty.kind != TY_PTR || fn.ty.base.kind != TY_FUNC) {
		errorTok(fn.tok, "not a function")
	}

	var ty *Type
	if fn.ty.kind == TY_FUNC {
		ty = fn.ty
	} else {
		ty = fn.ty.base
	}
	paramTy := ty.params

	var head Node
	cur := &head

	for !gtok.equal(")") {
		if cur != &head {
			gtok = gtok.consume(",")
		}
		arg := assign()
		addType(arg)

		if paramTy == nil && !ty.isVariadic {
			errorTok(gtok, "too many arguments")
		}

		if paramTy != nil {
			if paramTy.kind != TY_STRUCT && paramTy.kind != TY_UNION {
				arg = NewCast(arg, paramTy)
			}
			paramTy = paramTy.next
		} else if arg.ty.kind == TY_FLOAT {
			// If parameter type is omitted (e.g. in "..."), float
			// arguments are promoted to double.
			arg = NewCast(arg, doubleType())
		}

		cur.next = arg
		cur = cur.next
	}

	if paramTy != nil {
		errorTok(gtok, "too few arguments")
	}

	gtok = gtok.consume(")")

	node := NewUnary(ND_FUNCALL, fn, gtok)
	node.funcTy = ty
	node.ty = ty.returnTy
	node.args = head.next

	// If a function returns a struct, it is caller's responsibility
	// to allocate a space for the return value.
	if node.ty.kind == TY_STRUCT || node.ty.kind == TY_UNION {
		node.retBuffer = newLVar("", node.ty)
	}
	return node
}

// generic-selection = "(" assign "," generic-assoc ("," generic-assoc)* ")"
//
// generic-assoc = type-name ":" assign
// .             | "default" ":" assign
func genericSelection() *Node {
	start := gtok
	gtok = gtok.consume("(")

	ctrl := assign()
	addType(ctrl)

	t1 := ctrl.ty
	if t1.kind == TY_FUNC {
		t1 = pointerTo(t1)
	} else if t1.kind == TY_ARRAY {
		t1 = pointerTo(t1.base)
	}

	var ret *Node = nil

	for !tryConsume(")") {
		gtok = gtok.consume(",")

		if gtok.equal("default") {
			gtok = gtok.next.consume(":")
			node := assign()
			if ret == nil {
				ret = node
			}
			continue
		}

		t2 := typename()
		gtok = gtok.consume(":")
		node := assign()
		if isCompatible(t1, t2) {
			ret = node
		}
	}

	if ret == nil {
		errorTok(start, "controlling expression type not compatible with any generic association type")
	}
	return ret
}

// primary = "(" "{" stmt+ "}" ")"
// .       | "(" expr ")"
// .       | "sizeof" "(" type-name ")"
// .       | "sizeof" unary
// .       | "_Alignof" "(" type-name ")"
// .       | "_Alignof" unary
// .       | "_Generic" generic-selection
// .       | "__builtin_types_compatible_p" "(" type-name, type-name, ")"
// .       | "__builtin_reg_class" "(" type-name ")"
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
		if ty.kind == TY_VLA {
			if ty.vlaSize != nil {
				return NewVarNode(ty.vlaSize, st)
			}

			lhs := computeVlaSize(ty, st)
			rhs := NewVarNode(ty.vlaSize, st)
			return NewBinary(ND_COMMA, lhs, rhs, st)
		}
		return NewUlong(int64(ty.size), st)
	}

	if gtok.equal("sizeof") {
		gtok = gtok.next
		node := unary()
		addType(node)
		if node.ty.kind == TY_VLA {
			return NewVarNode(node.ty.vlaSize, st)
		}
		return NewUlong(int64(node.ty.size), st)
	}

	if gtok.equal("_Alignof") && gtok.next.equal("(") && isTypename(gtok.next.next) {
		gtok = gtok.next.next
		ty := typename()
		gtok = gtok.consume(")")
		return NewUlong(int64(ty.align), st)
	}

	if gtok.equal("_Alignof") {
		gtok = gtok.next
		node := unary()
		addType(node)
		return NewUlong(int64(node.ty.align), st)
	}

	if gtok.equal("_Generic") {
		gtok = gtok.next
		return genericSelection()
	}

	if gtok.equal("__builtin_types_compatible_p") {
		gtok = gtok.next.consume("(")
		ty1 := typename()
		gtok = gtok.consume(",")
		ty2 := typename()
		gtok = gtok.consume(")")
		return NewNumber(int64(b2i(isCompatible(ty1, ty2))), st)
	}

	if gtok.equal("__builtin_reg_class") {
		gtok = gtok.next.consume("(")
		ty := typename()
		gtok = gtok.consume(")")

		if ty.isInteger() || ty.kind == TY_PTR {
			return NewNumber(0, st)
		}
		if ty.isFlonum() {
			return NewNumber(1, st)
		}
		return NewNumber(2, st)
	}

	if gtok.equal("__builtin_compare_and_swap") {
		node := NewNode(ND_CAS, gtok)
		gtok = gtok.next.consume("(")
		node.casAddr = assign()
		gtok = gtok.consume(",")
		node.casOld = assign()
		gtok = gtok.consume(",")
		node.casNew = assign()
		gtok = gtok.consume(")")
		return node
	}

	if gtok.equal("__builtin_atomic_exchange") {
		node := NewNode(ND_EXCH, gtok)
		gtok = gtok.next.consume("(")
		node.lhs = assign()
		gtok = gtok.consume(",")
		node.rhs = assign()
		gtok = gtok.consume(")")
		return node
	}

	if gtok.kind == TK_IDENT {
		// Variable or enum constant
		tok := gtok
		sc := findVar(gtok.literal)
		gtok = gtok.next

		// For "static inline" function
		if sc != nil && sc.variable != nil && sc.variable.isFunction {
			if pcurrentFn != nil {
				pcurrentFn.refs = append(pcurrentFn.refs, sc.variable.name)
			} else {
				sc.variable.isRoot = true
			}
		}

		if sc != nil {
			if sc.variable != nil {
				return NewVarNode(sc.variable, tok)
			}
			if sc.enumTy != nil {
				return NewNumber(int64(sc.enumVal), tok)
			}
		}
		if gtok.next.equal("(") {
			errorTok(gtok, "implicit declaration of a function")
		}
		errorTok(gtok, "undefined variable")
	}

	if gtok.kind == TK_STR {
		variable := newStringLiteral(gtok.str, gtok.ty)
		gtok = gtok.next
		return NewVarNode(variable, st)
	}

	if gtok.kind == TK_NUM {
		var node *Node
		if gtok.ty.isFlonum() {
			node = NewNode(ND_NUM, st)
			node.fval = gtok.fval
		} else {
			node = NewNumber(gtok.val, st)
		}

		node.ty = gtok.ty
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
		if ty.name == nil {
			errorTok(ty.namePos, "typedef name omitted")
		}
		pushScope(ty.name.literal).typedef = ty
	}
}

// 为函数参数创建局部变量
func createParamLvars(param *Type) {
	if param != nil {
		createParamLvars(param.next)
		if param.name == nil {
			errorTok(param.namePos, "parameter name omitted")
		}
		newLVar(param.name.literal, param)
	}
}

// This function matches gotos or labels-as-values with labels.
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

func findFunc(name string) *Obj {
	sc := scope
	for sc.next != nil {
		sc = sc.next
	}

	sc2, ok := sc.vars[name]
	if ok && sc2.variable != nil && sc2.variable.isFunction {
		return sc2.variable
	}
	return nil
}

func markLive(var_ *Obj) {
	if !var_.isFunction || var_.isLive {
		return
	}
	var_.isLive = true

	for i := 0; i < len(var_.refs); i++ {
		refname := var_.refs[i]
		fn := findFunc(refname)
		if fn != nil {
			markLive(fn)
		}
	}
}

func function(basety *Type, attr *VarAttr) *Obj {
	ty := declarator(basety)
	if ty.name == nil {
		errorTok(ty.namePos, "function name omitted")
	}

	fn := newGVar(ty.name.literal, ty)
	fn.isFunction = true
	fn.isDefinition = !tryConsume(";")
	fn.isStatic = attr.isStatic || (attr.isInline && !attr.isExtern)
	fn.isInline = attr.isInline
	fn.isRoot = !(fn.isStatic && fn.isInline)

	if !fn.isDefinition {
		return fn
	}

	pcurrentFn = fn
	locals = nil
	enterScope()
	createParamLvars(ty.params)

	// A buffer for a struct/union return value is passed
	// as the hidden first parameter.
	rty := ty.returnTy
	if (rty.kind == TY_STRUCT || rty.kind == TY_UNION) && rty.size > 16 {
		newLVar("", pointerTo(rty))
	}

	fn.params = locals

	if ty.isVariadic {
		fn.vaArea = newLVar("__va_area__", arrayOf(charType(), 136))
	}
	fn.allocaBottom = newLVar("__alloca_size__", pointerTo(charType()))

	// [https://www.sigbus.info/n1570#6.4.2.2p1] "__func__" is
	// automatically defined as a local variable containing the
	// current function name.
	pushScope("__func__").variable = newStringLiteral(fn.name, arrayOf(charType(), len(fn.name)+1))

	// [GNU] __FUNCTION__ is yet another name of __func__.
	pushScope("__FUNCTION__").variable = newStringLiteral(fn.name, arrayOf(charType(), len(fn.name)+1))

	fn.body = compoundStmt()
	fn.locals = locals
	leaveScope()
	resolveGotoLabels()
	return fn
}

func globalVariable(basety *Type, attr *VarAttr) {
	first := true

	for !tryConsume(";") {
		if !first {
			gtok = gtok.consume(",")
		}
		first = false

		ty := declarator(basety)
		if ty.name == nil {
			errorTok(ty.namePos, "variable name omitted")
		}

		var_ := newGVar(ty.name.literal, ty)
		var_.isDefinition = !attr.isExtern
		var_.isStatic = attr.isStatic
		var_.isTls = attr.isTls
		if attr.align != 0 {
			var_.align = attr.align
		}

		if gtok.equal("=") {
			gtok = gtok.next
			gvarInitializer(var_)
		} else if !attr.isExtern && !attr.isTls {
			var_.isTentative = true
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

// Remove redundant tentative definitions.
func scanGlobals() {
	var head Obj
	cur := &head

	for var_ := globals; var_ != nil; var_ = var_.next {
		if !var_.isTentative {
			cur.next = var_
			cur = cur.next
			continue
		}

		// Find another definition of the same identifier.
		var2 := globals
		for ; var2 != nil; var2 = var2.next {
			if var_ != var2 && var2.isDefinition && var_.name == var2.name {
				break
			}
		}

		// If there's another definition, the tentative definition
		// is redundant
		if var2 == nil {
			cur.next = var_
			cur = cur.next
		}
	}

	cur.next = nil
	globals = head.next
}

func declareBuiltinFunctions() {
	ty := funcType(pointerTo(voidType()))
	ty.params = intType()
	pbuiltinAlloca = newGVar("alloca", ty)
	pbuiltinAlloca.isDefinition = false
}

// program = (typedef | function-definition | global-variable)*
func program() *Obj {
	declareBuiltinFunctions()
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
		globalVariable(basety, &attr)
	}

	for var_ := globals; var_ != nil; var_ = var_.next {
		if var_.isRoot {
			markLive(var_)
		}
	}

	// Remove redundant tentative definitions.
	scanGlobals()
	return globals
}

// #endregion

func parse(tok *Token) *Obj {
	gtok = tok
	return program()
}
