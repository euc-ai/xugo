// definitions.go — the chapter's definitional layer: independence of a
// finite family, a basis of a set of sequences, and the dimension.
//
// A family is a sequence of vectors `e : num → num → A`, and its first k
// members are the ones a statement speaks of — the convention `vec_span`
// already keeps, so a basis is a length and a family, and the span of the
// family's first k members is the set it is a basis of. Each constant
// reads the scalar structure it needs as leading components (`Implicit`),
// which a law under the ring or the field leaves out of its text.
//
// The dimension is a Hilbert choice: SOME length at which the set has a
// basis. Nothing more is asked of the definition, because the chapter
// proves that any two bases of one set have the same length — over a
// field — so where a basis exists the choice has one value it can make.
// Where none does (a set that is not a subspace, or one with no finite
// basis) the dimension is a number nothing is said about.

package basis

import (
	"github.com/euc-ai/xugo/library/registry"
)

// VecIndependentDef — the first k members of a family are linearly
// independent: the only combination of them that is the zero vector is
// the one whose every coefficient on the range is zero.
var VecIndependentDef = vecIndependentDefThm{family.Define(registry.DefEntry{
	Name:     "VecIndependentDef",
	Key:      "prop_42b8b0c0c3a505a8",
	Const:    "vec_independent",
	Type:     "(A → A → A) → A → (A → A → A) → num → (num → num → A) → bool",
	Implicit: []string{"add", "zero", "mul"},
	Equations: []string{"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀k:num. ∀e:(num → num → A). " +
		"    vec_independent(add, zero, mul, k, e) ⇔ " +
		"    (∀c:(num → A). " +
		"        iterated_op(vec_add(add), {i:num | i < k}, λi:num. vec_scalar_mul(mul, c(i), e(i))) = " +
		"        vec_zero(zero) ⇒ " +
		"        (∀i:num. i < k ⇒ c(i) = zero))"},
})}

// VecBasisDef — the first k members of a family are a basis of s: they
// are independent, and s is exactly what they span.
var VecBasisDef = vecBasisDefThm{family.Define(registry.DefEntry{
	Name:     "VecBasisDef",
	Key:      "prop_dc60efb27f6356e",
	Const:    "vec_basis",
	Type:     "(A → A → A) → A → (A → A → A) → num → (num → num → A) → set(num → A) → bool",
	Implicit: []string{"add", "zero", "mul"},
	Equations: []string{
		"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀k:num. ∀e:(num → num → A). ∀s:set(num → A). " +
			"    vec_basis(add, zero, mul, k, e, s) ⇔ " +
			"    vec_independent(add, zero, mul, k, e) ∧ vec_span(add, mul, k, e) = s",
	},
	Deps: []registry.EntryLike{VecIndependentDef},
})}

// VecDimDef — the dimension of s: a length at which s has a basis,
// chosen.
var VecDimDef = vecDimDefThm{family.Define(registry.DefEntry{
	Name:     "VecDimDef",
	Key:      "prop_6f7e582280dd8cd8",
	Const:    "vec_dim",
	Type:     "(A → A → A) → A → (A → A → A) → set(num → A) → num",
	Implicit: []string{"add", "zero", "mul"},
	Equations: []string{"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀s:set(num → A). " +
		"    vec_dim(add, zero, mul, s) = εk:num. ∃e:(num → num → A). vec_basis(add, zero, mul, k, e, s)"},
	Deps: []registry.EntryLike{VecBasisDef},
})}
