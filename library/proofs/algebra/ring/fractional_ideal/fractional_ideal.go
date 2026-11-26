// fractional_ideal.go — the chapter's definitions: the product of two
// submodules of a field over a subring of it, the inverse of one, and the
// invertible ones.

package fractional_ideal

import (
	"github.com/euc-ai/xugo/library/registry"
	// The chapter minting int_of_num and num_of_int, which the signed powers'
	// definition spells, initialized before it.
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// FractionalMulDef — `fractional_mul(L, S, M, N)`, written M · N: the
// S-submodule of L spanned by the products m · n, m in M and n in N.
var FractionalMulDef = fractionalMulDefThm{family.Define(registry.DefEntry{
	Name:     "FractionalMulDef",
	Key:      "prop_ee4829594c7c3fdb",
	Const:    "fractional_mul",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A) → set(A)",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀S M N:set(A). " +
			"    fractional_mul(R, S, M, N) = " +
			"    module_span(restrict_ring(R, S), regular_module(R), {R.mul(m, n) | m:A, n:A | m ∈ M ∧ n ∈ N})",
	},
})}

// FractionalInverseDef — `fractional_inverse(L, S, M)`, written M⁻¹ or
// (S : M): the members of L whose product with every member of M lies
// in S.
var FractionalInverseDef = fractionalInverseDefThm{family.Define(registry.DefEntry{
	Name:     "FractionalInverseDef",
	Key:      "prop_a656e662f863d19d",
	Const:    "fractional_inverse",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A)",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). ∀M:set(A). " +
			"    fractional_inverse(R, S, M) = {x:A | x ∈ R.carrier ∧ (∀m:A. m ∈ M ⇒ R.mul(x, m) ∈ S)}",
	},
})}

// InvertibleFractionalDef — `invertible_fractional(L, S, M)`: M is an
// S-submodule of L whose product with (S : M) is S. For a subring S such
// an M is not {zero} (its product with anything is {zero}, which is not
// S ∋ one) and is finitely generated; it has a common denominator in S when L is the
// field of fractions of S.
var InvertibleFractionalDef = invertibleFractionalDefThm{family.Define(registry.DefEntry{
	Name:     "InvertibleFractionalDef",
	Key:      "prop_9b3aa748e877461c",
	Const:    "invertible_fractional",
	Type:     "ring_ops(A) → set(A) → set(A) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀S M:set(A). " +
			"    invertible_fractional(R, S, M) ⇔ " +
			"    submodule(restrict_ring(R, S), regular_module(R), M) ∧ " +
			"    fractional_mul(R, S, M, fractional_inverse(R, S, M)) = S",
	},
	Deps: []registry.EntryLike{FractionalMulDef, FractionalInverseDef},
})}
