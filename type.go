package main

type TypeKind int

const (
	TY_CHAR  TypeKind = iota // char
	TY_INT                   // int
	TY_PTR                   // pointer
	TY_FUNC                  // function
	TY_ARRAY                 // array
)

type Type struct {
	kind TypeKind // Type kind
	size int      // sizeof() value

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

	// Function Type
	returnTy *Type
	params   *Type
	next     *Type // next parameter type
}

func newType(kind TypeKind) *Type {
	t := &Type{
		kind: kind,
	}
	return t
}

func intType() *Type {
	t := &Type{
		kind: TY_INT,
		size: 8,
	}
	return t
}

func charType() *Type {
	t := &Type{
		kind: TY_CHAR,
		size: 1,
	}
	return t
}

func pointerTo(base *Type) *Type {
	t := &Type{
		kind: TY_PTR,
		size: 8,
		base: base,
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
		base:     base,
		arrayLen: len,
	}
	return t
}

func (t *Type) isInteger() bool {
	return t.kind == TY_CHAR || t.kind == TY_INT
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
	case ND_ADD:
		node.ty = node.lhs.ty
		return
	case ND_SUB:
		node.ty = node.lhs.ty
		return
	case ND_MUL:
		node.ty = node.lhs.ty
		return
	case ND_DIV:
		node.ty = node.lhs.ty
		return
	case ND_NEG:
		node.ty = node.lhs.ty
		return
	case ND_ASSIGN:
		if node.lhs.ty.kind == TY_ARRAY {
			errorTok(node.tok, "cannot assign to array")
		}
		node.ty = node.lhs.ty
		return
	case ND_EQ:
		node.ty = intType()
		return
	case ND_NE:
		node.ty = intType()
		return
	case ND_LT:
		node.ty = intType()
		return
	case ND_LE:
		node.ty = intType()
		return
	case ND_VAR:
		node.ty = node.variable.ty
		return
	case ND_NUM:
		node.ty = intType()
		return
	case ND_FUNCALL:
		node.ty = intType()
		return
	case ND_ADDR:
		if node.lhs.ty.kind == TY_ARRAY {
			node.ty = pointerTo(node.lhs.ty.base)
		} else {
			node.ty = pointerTo(node.lhs.ty)
		}
		return
	case ND_DEREF:
		if node.lhs.ty.base != nil {
			node.ty = node.lhs.ty.base
		} else {
			errorTok(node.tok, "invalid pointer dereference")
		}
		return

	}
}
