// definitions.go — the chapter's definitional layer: the bilinear form,
// and the adjoint whose coordinates it reads.
//
// `dot⟨n⟩(add, mul, u, v)` folds the pointwise product `mul(u(i), v(i))`
// over the active range `{i | i < n}` with the ring's addition, through
// the fold mechanism of iterate/monoidal (the README says why the range
// and not the closed interval). The range is finite for every n, so the
// fold's laws apply with no finiteness side condition.
//
// `adjoint(zero, one, add, mul, m, n, f, y, j)` names the coordinates
// of a vector through that form: the j-th is the form, read at n, at
// the image under f of the j-th basis vector, and the ring's zero once
// j has left the range below m. The two dimensions stay separate: m
// bounds the coordinates the value has, n is the dimension the form is
// read at. `AdjointVec` reads the guard back as the membership it is.
//
// The constant is COORDINATE-valued — its last argument is the index —
// and the chapter reads it at three arities, each a partial
// application of this one equation: `adjoint(m, n, f, y, j)` is a ring
// element, `adjoint(m, n, f, y)` the vector whose entries those are,
// and `adjoint(m, n, f)` the map on sequences that `vec_linear` asks
// about. Nothing is overloaded; the shorter spellings are the longer
// one with trailing arguments left off.
//
// It declares no `Dim`. That field names the ONE argument a constant
// reads its vector arguments at, and this one has two num arguments
// doing different jobs — m bounds the value's coordinates, n is where
// the form is read — so there is no single honest answer, and a wrong
// one would have the typed surface write the wrong dimension off a
// vector.

package dot

import (
	"github.com/euc-ai/xugo/library/registry"
)

// DotDef — the sum, over the active range, of the pointwise products,
// written `⟪u, v⟫_n`.
var DotDef = dotDefThm{family.Define(registry.DefEntry{
	Name:     "DotDef",
	Key:      "prop_6145c8c120b3ce80",
	Const:    "dot",
	Type:     "(A → A → A) → (A → A → A) → num → (num → A) → (num → A) → A",
	Implicit: []string{"add", "mul"},
	Notation: "⟪u, v⟫_n",
	Dim:      "n",
	Equations: []string{"∀add mul:(A → A → A). ∀n:num. ∀u v:(num → A). " +
		"    dot⟨n⟩(add, mul, u, v) = iterated_op(add, {i:num | i < n}, λi:num. mul(u(i), v(i)))"},
})}

// AdjointDef — the adjoint of a map on sequences, one coordinate at a
// time: inside the range, the form pairing the given vector with the
// image of the basis vector at that coordinate; past it, the ring's
// zero.
var AdjointDef = adjointDefThm{family.Define(registry.DefEntry{
	Name:  "AdjointDef",
	Key:   "prop_28d7620ea8ccc0b4",
	Const: "adjoint",
	Type: "A → " +
		"A → " +
		"(A → A → A) → " +
		"(A → A → A) → " +
		"num → " +
		"num → " +
		"((num → A) → (num → A)) → " +
		"(num → A) → " +
		"num → " +
		"A",
	Implicit: []string{"zero", "one", "add", "mul"},
	Equations: []string{"∀zero one:A. " +
		"∀add mul:(A → A → A). " +
		"∀m n:num. " +
		"∀f:((num → A) → (num → A)). " +
		"∀y:(num → A). " +
		"∀j:num. " +
		"    adjoint(zero, one, add, mul, m, n, f, y, j) = " +
		"    COND(j < m, dot⟨n⟩(add, mul, f(basis_vector(zero, one, j)), y), zero)"},
	Deps: []registry.EntryLike{DotDef},
})}
