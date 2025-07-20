package main

type TypeKind int

const (
	TY_VOID    TypeKind = iota // void
	TY_BOOL                    // bool
	TY_CHAR                    // char
	TY_SHORT                   // short
	TY_INT                     // int
	TY_LONG                    // long
	TY_FLOAT                   // float
	TY_DOUBLE                  // double
	TY_LDOUBLE                 // long double
	TY_ENUM                    // enum
	TY_PTR                     // pointer
	TY_FUNC                    // function
	TY_ARRAY                   // array
	TY_VLA                     // variable-length array
	TY_STRUCT                  // struct
	TY_UNION                   // union
)

type Type struct {
	kind       TypeKind // Type kind
	size       int      // sizeof() value
	align      int      // alignment
	isUnsigned bool     // unsigned or signed
	isAtomic   bool     // true if _Atomic
	origin     *Type    // for type compatibility check

	// Pointer-to or array-of type. We intentionally use the same member
	// to represent pointer/array duality(二元性) in C.
	//
	// In many contexts in which a pointer is expected, we examine this
	// member instead of "kind" member to determine whether a type is a
	// pointer or not. That means in many contexts "array of T" is
	// naturally handled as if it were "pointer to T", as required by
	// the C spec.
	base *Type

	// Declaration
	name    *Token
	namePos *Token

	// Array
	arrayLen int // array length

	// Variable-length array
	vlaLen  *Node // length expression
	vlaSize *Obj  // sizeof() value

	// Struct
	members    *Member
	isFlexible bool

	// Function Type
	returnTy   *Type
	params     *Type
	isVariadic bool
	next       *Type // next parameter type
}

func newType(kind TypeKind, size int, align int) *Type {
	t := &Type{
		kind:  kind,
		size:  size,
		align: align,
	}
	return t
}

func voidType() *Type {
	t := &Type{
		kind:  TY_VOID,
		size:  1,
		align: 1,
	}
	return t
}

func boolType() *Type {
	t := &Type{
		kind:  TY_BOOL,
		size:  1,
		align: 1,
	}
	return t
}

func charType() *Type {
	t := &Type{
		kind:  TY_CHAR,
		size:  1,
		align: 1,
	}
	return t
}

func shortType() *Type {
	t := &Type{
		kind:  TY_SHORT,
		size:  2,
		align: 2,
	}
	return t
}

func intType() *Type {
	t := &Type{
		kind:  TY_INT,
		size:  4,
		align: 4,
	}
	return t
}

func longType() *Type {
	t := &Type{
		kind:  TY_LONG,
		size:  8,
		align: 8,
	}
	return t
}

func ucharType() *Type {
	t := &Type{
		kind:       TY_CHAR,
		size:       1,
		align:      1,
		isUnsigned: true,
	}
	return t
}

func ushortType() *Type {
	t := &Type{
		kind:       TY_SHORT,
		size:       2,
		align:      2,
		isUnsigned: true,
	}
	return t
}

func uintType() *Type {
	t := &Type{
		kind:       TY_INT,
		size:       4,
		align:      4,
		isUnsigned: true,
	}
	return t
}

func ulongType() *Type {
	t := &Type{
		kind:       TY_LONG,
		size:       8,
		align:      8,
		isUnsigned: true,
	}
	return t
}

func floatType() *Type {
	t := &Type{
		kind:  TY_FLOAT,
		size:  4,
		align: 4,
	}
	return t
}

func doubleType() *Type {
	t := &Type{
		kind:  TY_DOUBLE,
		size:  8,
		align: 8,
	}
	return t
}

func ldoubleType() *Type {
	t := &Type{
		kind:  TY_LDOUBLE,
		size:  16,
		align: 16,
	}
	return t
}

func pointerTo(base *Type) *Type {
	t := &Type{
		kind:       TY_PTR,
		size:       8,
		align:      8,
		isUnsigned: true,
		base:       base,
	}
	return t
}

func funcType(returnTy *Type) *Type {
	t := newType(TY_FUNC, 1, 1)
	t.returnTy = returnTy
	return t
}

func arrayOf(base *Type, len int) *Type {
	t := &Type{
		kind:     TY_ARRAY,
		size:     base.size * len,
		align:    base.align,
		base:     base,
		arrayLen: len,
	}
	return t
}

func vlaOf(base *Type, len *Node) *Type {
	ty := newType(TY_VLA, 8, 8)
	ty.base = base
	ty.vlaLen = len
	return ty
}

func enumType() *Type {
	t := &Type{
		kind:  TY_ENUM,
		size:  4,
		align: 4,
	}
	return t
}

func (t *Type) isInteger() bool {
	return t.kind == TY_BOOL || t.kind == TY_CHAR || t.kind == TY_SHORT || t.kind == TY_INT || t.kind == TY_LONG || t.kind == TY_ENUM
}

func (t *Type) isFlonum() bool {
	return t.kind == TY_FLOAT || t.kind == TY_DOUBLE || t.kind == TY_LDOUBLE
}

func (t *Type) isNumeric() bool {
	return t.isInteger() || t.isFlonum()
}

func (t *Type) copy() *Type {
	c := &Type{
		kind:       t.kind,
		size:       t.size,
		align:      t.align,
		isUnsigned: t.isUnsigned,
		base:       t.base,
		name:       t.name,
		arrayLen:   t.arrayLen,
		members:    t.members,
		isFlexible: t.isFlexible,
		returnTy:   t.returnTy,
		params:     t.params,
		next:       t.next,
		origin:     t,
	}
	return c
}

func isCompatible(t1 *Type, t2 *Type) bool {
	if t1 == t2 {
		return true
	}

	if t1.origin != nil {
		return isCompatible(t1.origin, t2)
	}

	if t2.origin != nil {
		return isCompatible(t1, t2.origin)
	}

	if t1.kind != t2.kind {
		return false
	}

	switch t1.kind {
	case TY_CHAR:
		fallthrough
	case TY_SHORT:
		fallthrough
	case TY_INT:
		fallthrough
	case TY_LONG:
		return t1.isUnsigned == t2.isUnsigned
	case TY_FLOAT:
		fallthrough
	case TY_DOUBLE, TY_LDOUBLE:
		return true
	case TY_PTR:
		return isCompatible(t1.base, t2.base)
	case TY_FUNC:
		if !isCompatible(t1.returnTy, t2.returnTy) {
			return false
		}
		if t1.isVariadic != t2.isVariadic {
			return false
		}

		p1 := t1.params
		p2 := t2.params
		for p1 != nil && p2 != nil {
			if !isCompatible(p1, p2) {
				return false
			}
			p1 = p1.next
			p2 = p2.next
		}
		return p1 == nil && p2 == nil
	case TY_ARRAY:
		if !isCompatible(t1.base, t2.base) {
			return false
		}
		return t1.arrayLen < 0 && t2.arrayLen < 0 && t1.arrayLen == t2.arrayLen

	case TY_VOID:
		fallthrough
	case TY_BOOL:
		return true
	}
	return false
}

func structType() *Type {
	t := &Type{
		kind:  TY_STRUCT,
		size:  0,
		align: 1,
	}
	return t
}

func getCommonType(ty1 *Type, ty2 *Type) *Type {
	if ty1.base != nil {
		return pointerTo(ty1.base)
	}

	if ty1.kind == TY_FUNC {
		return pointerTo(ty1)
	}
	if ty2.kind == TY_FUNC {
		return pointerTo(ty2)
	}

	if ty1.kind == TY_LDOUBLE || ty2.kind == TY_LDOUBLE {
		return ldoubleType()
	}
	if ty1.kind == TY_DOUBLE || ty2.kind == TY_DOUBLE {
		return doubleType()
	}
	if ty1.kind == TY_FLOAT || ty2.kind == TY_FLOAT {
		return floatType()
	}

	if ty1.size < 4 {
		ty1 = intType()
	}
	if ty2.size < 4 {
		ty2 = intType()
	}

	if ty1.size != ty2.size {
		if ty1.size < ty2.size {
			return ty2.copy()
		} else {
			return ty1.copy()
		}
	}

	if ty2.isUnsigned {
		return ty2.copy()
	}
	return ty1.copy()
}

// For many binary operators, we implicitly promote operands so that
// both operands have the same type. Any integral type smaller than
// int is always promoted to int. If the type of one operand is larger
// than the other's (e.g. "long" vs. "int"), the smaller operand will
// be promoted to match with the other.
//
// This operation is called the "usual arithmetic conversion".
func usualArithmeticConversion(lhs *Node, rhs *Node) (*Node, *Node) {
	ty := getCommonType(lhs.ty, rhs.ty)
	return NewCast(lhs, ty), NewCast(rhs, ty)
}

func addType(node *Node) {
	if node == nil || node.ty != nil {
		return
	}

	addType(node.lhs)
	addType(node.rhs)
	addType(node.cond)
	addType(node.then)
	addType(node.els)
	addType(node.init)
	addType(node.inc)

	for n := node.body; n != nil; n = n.next {
		addType(n)
	}
	for n := node.args; n != nil; n = n.next {
		addType(n)
	}

	switch node.kind {
	case ND_NUM:
		node.ty = intType()
		return
	case ND_ADD:
		fallthrough
	case ND_SUB:
		fallthrough
	case ND_MUL:
		fallthrough
	case ND_DIV:
		fallthrough
	case ND_MOD:
		fallthrough
	case ND_BITAND:
		fallthrough
	case ND_BITOR:
		fallthrough
	case ND_BITXOR:
		node.lhs, node.rhs = usualArithmeticConversion(node.lhs, node.rhs)
		node.ty = node.lhs.ty
		return
	case ND_NEG:
		ty := getCommonType(intType(), node.lhs.ty)
		node.lhs = NewCast(node.lhs, ty)
		node.ty = ty
		return
	case ND_ASSIGN:
		if node.lhs.ty.kind == TY_ARRAY {
			errorTok(node.tok, "cannot assign to array")
		}
		if node.lhs.ty.kind != TY_STRUCT {
			node.rhs = NewCast(node.rhs, node.lhs.ty)
		}
		node.ty = node.lhs.ty
		return
	case ND_EQ:
		fallthrough
	case ND_NE:
		fallthrough
	case ND_LT:
		fallthrough
	case ND_LE:
		node.lhs, node.rhs = usualArithmeticConversion(node.lhs, node.rhs)
		node.ty = intType()
		return
	case ND_FUNCALL:
		node.ty = node.funcTy.returnTy
		return
	case ND_NOT:
		fallthrough
	case ND_LOGAND:
		fallthrough
	case ND_LOGOR:
		node.ty = intType()
		return
	case ND_BITNOT:
		fallthrough
	case ND_SHL:
		fallthrough
	case ND_SHR:
		node.ty = node.lhs.ty
		return
	case ND_VAR, ND_VLA_PTR:
		node.ty = node.variable.ty
		return
	case ND_COND:
		if node.then.ty.kind == TY_VOID || node.els.ty.kind == TY_VOID {
			node.ty = voidType()
		} else {
			node.then, node.els = usualArithmeticConversion(node.then, node.els)
			node.ty = node.then.ty
		}
		return
	case ND_COMMA:
		node.ty = node.rhs.ty
		return
	case ND_MEMBER:
		node.ty = node.member.ty
		return
	case ND_ADDR:
		ty := node.lhs.ty
		if ty.kind == TY_ARRAY {
			node.ty = pointerTo(ty.base)
		} else {
			node.ty = pointerTo(ty)
		}
		return
	case ND_DEREF:
		if node.lhs.ty.base == nil {
			errorTok(node.tok, "invalid pointer dereference")
		}
		if node.lhs.ty.base.kind == TY_VOID {
			errorTok(node.tok, "dereferencing a void pointer")
		}
		node.ty = node.lhs.ty.base
		return
	case ND_STMT_EXPR:
		if node.body != nil {
			stmt := node.body
			for stmt.next != nil {
				stmt = stmt.next
			}
			if stmt.kind == ND_EXPR_STMT {
				node.ty = stmt.lhs.ty
				return
			}
		}
		errorTok(node.tok, "statement expression returning void is not supported")
		return
	case ND_LABEL_VAL:
		node.ty = pointerTo(voidType())
		return
	case ND_CAS:
		addType(node.casAddr)
		addType(node.casOld)
		addType(node.casNew)
		node.ty = boolType()

		if node.casAddr.ty.kind != TY_PTR {
			errorTok(node.casAddr.tok, "pointer expected")
		}
		if node.casOld.ty.kind != TY_PTR {
			errorTok(node.casOld.tok, "pointer expected")
		}
	case ND_EXCH:
		if node.lhs.ty.kind != TY_PTR {
			errorTok(node.casAddr.tok, "pointer expected")
		}
		node.ty = node.lhs.ty.base
	}
}
