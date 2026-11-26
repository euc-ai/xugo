package boolean_degree

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/multilinear_polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/registry"
)

// BooleanCoefficientDef takes the integer multilinear coefficient of the Boolean values encoded as zero and one.
var BooleanCoefficientDef = booleanCoefficientDefThm{family.Define(registry.DefEntry{
	Name:  "BooleanCoefficientDef",
	Key:   "prop_80975c23f00d7e19",
	Const: "boolean_coefficient",
	Type:  "(set(A) → bool) → set(A) → int",
	Equations: []string{
		"∀f:(set(A) → bool). ∀S:set(A). " +
			"    boolean_coefficient(f, S) = " +
			"    multilinear_coeff(int_ring, λX:set(A). COND(f(X), int_of_num(1), int_of_num(0)), S)",
	},
})}

// BooleanDegreeDef selects the greatest size of a nonzero monomial contained in U, with zero as the degree of the zero polynomial.
var BooleanDegreeDef = booleanDegreeDefThm{family.Define(registry.DefEntry{
	Name:  "BooleanDegreeDef",
	Key:   "prop_b0e31d76889a239f",
	Const: "boolean_degree",
	Type:  "set(A) → (set(A) → bool) → num",
	Equations: []string{
		"∀U:set(A). ∀f:(set(A) → bool). " +
			"    boolean_degree(U, f) = " +
			"    εd:num. " +
			"        (d = 0 ∨ " +
			"            (∃S:set(A). S ⊆ U ∧ boolean_coefficient(f, S) ≠ int_of_num(0) ∧ card(S) = d)) ∧ " +
			"        (∀S:set(A). S ⊆ U ∧ boolean_coefficient(f, S) ≠ int_of_num(0) ⇒ card(S) ≤ d)",
	},
	Deps: []registry.EntryLike{BooleanCoefficientDef},
})}

// ParityClassDef collects the inputs on the face S where the comparison with parity has the chosen truth value.
var ParityClassDef = parityClassDefThm{family.Define(registry.DefEntry{
	Name:  "ParityClassDef",
	Key:   "prop_6c5431fb50952c8c",
	Const: "boolean_parity_class",
	Type:  "set(A) → (set(A) → bool) → bool → set(set(A))",
	Equations: []string{
		"∀S:set(A). ∀f:(set(A) → bool). ∀b:bool. " +
			"    boolean_parity_class(S, f, b) = {X:set(A) | X ⊆ S ∧ ((f(X) ⇔ nat_even(card(X))) ⇔ b)}",
	},
})}
