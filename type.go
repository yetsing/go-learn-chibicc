package main

type TypeKind int

const (
	TY_VOID   TypeKind = iota // void
	TY_BOOL                   // bool
	TY_CHAR                   // char
	TY_SHORT                  // short
	TY_INT                    // int
	TY_LONG                   // long
	TY_ENUM                   // enum
	TY_PTR                    // pointer
	TY_FUNC                   // function
	TY_ARRAY                  // array
	TY_STRUCT                 // struct
	TY_UNION                  // union
)

type Type struct {
	kind  TypeKind // Type kind
	size  int      // sizeof() value
	align int      // alignment

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
	name *Token

	// Array
	arrayLen int // array length

	// Struct
	members *Member

	// Function Type
	returnTy *Type
	params   *Type
	next     *Type // next parameter type
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

func pointerTo(base *Type) *Type {
	t := &Type{
		kind:  TY_PTR,
		size:  8,
		align: 8,
		base:  base,
	}
	return t
}

func funcType(returnTy *Type) *Type {
	t := &Type{
		kind:     TY_FUNC,
		returnTy: returnTy,
	}
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
	if ty1.size == 8 || ty2.size == 8 {
		return longType()
	}
	return intType()
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
		if node.val == int64(int(node.val)) {
			node.ty = intType()
		} else {
			node.ty = longType()
		}
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
		usualArithmeticConversion(node.lhs, node.rhs)
		node.ty = intType()
		return
	case ND_FUNCALL:
		node.ty = longType()
		return
	case ND_NOT:
		fallthrough
	case ND_LOGAND:
		fallthrough
	case ND_LOGOR:
		node.ty = intType()
		return
	case ND_BITNOT:
		node.ty = node.lhs.ty
		return
	case ND_VAR:
		node.ty = node.variable.ty
		return
	case ND_COMMA:
		node.ty = node.rhs.ty
		return
	case ND_MEMBER:
		node.ty = node.member.ty
		return
	case ND_ADDR:
		if node.lhs.ty.kind == TY_ARRAY {
			node.ty = pointerTo(node.lhs.ty.base)
		} else {
			node.ty = pointerTo(node.lhs.ty)
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
	}
}
