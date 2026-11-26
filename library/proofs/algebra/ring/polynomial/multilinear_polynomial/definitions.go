package multilinear_polynomial

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// MultilinearEvalDef evaluates a squarefree coefficient family at the indicator of X.
var MultilinearEvalDef = multilinearEvalDefThm{family.Define(registry.DefEntry{
	Name:  "MultilinearEvalDef",
	Key:   "prop_1656ed0724e62628",
	Const: "multilinear_eval",
	Type:  "ring_ops(A) → (set(B) → A) → set(B) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀c:(set(B) → A). ∀X:set(B). " +
			"    multilinear_eval(R, c, X) = module_sum(R.add, R.zero, {T:set(B) | T ⊆ X}, c)",
	},
})}

// MultilinearCoeffDef sums the values on subsets, changing the sign for each omitted variable.
var MultilinearCoeffDef = multilinearCoeffDefThm{family.Define(registry.DefEntry{
	Name:  "MultilinearCoeffDef",
	Key:   "prop_3f2e196c9c9b2f18",
	Const: "multilinear_coeff",
	Type:  "ring_ops(A) → (set(B) → A) → set(B) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀f:(set(B) → A). ∀S:set(B). " +
			"    multilinear_coeff(R, f, S) = " +
			"    module_sum(R.add, " +
			"        R.zero, " +
			"        {T:set(B) | T ⊆ S}, " +
			"        λT:set(B). COND(nat_even(card(S ∖ T)), f(T), -f(T)))",
	},
})}

// squarefreeExponentDef assigns exponent one precisely to the variables in T.
var squarefreeExponentDef = squarefreeExponentDefThm{family.Define(registry.DefEntry{
	Name:  "squarefreeExponentDef",
	Key:   "prop_dee5d7f78be3a69",
	Const: "squarefree_exponent",
	Type:  "set(B) → B → num",
	Equations: []string{
		"∀T:set(B). ∀x:B. squarefree_exponent(T, x) = COND(x ∈ T, 1, 0)",
	},
})}

// cubeRingPointDef is the zero-one assignment with ones on X.
var cubeRingPointDef = cubeRingPointDefThm{family.Define(registry.DefEntry{
	Name:  "cubeRingPointDef",
	Key:   "prop_8fdc7d2aedd3df5f",
	Const: "cube_ring_point",
	Type:  "ring_ops(A) → set(B) → B → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:set(B). ∀x:B. cube_ring_point(R, X, x) = COND(x ∈ X, R.one, R.zero)",
	},
})}

// SquarefreePolynomialDef extends a subset-indexed coefficient family by zero on all other monomials.
var SquarefreePolynomialDef = squarefreePolynomialDefThm{family.Define(registry.DefEntry{
	Name:  "SquarefreePolynomialDef",
	Key:   "prop_f4af5ce8939de08d",
	Const: "squarefree_polynomial",
	Type:  "ring_ops(A) → set(B) → (set(B) → A) → (B → num) → A",
	Deps:  []registry.EntryLike{squarefreeExponentDef},
	Equations: []string{
		"∀R:ring_ops(A). ∀U:set(B). ∀c:(set(B) → A). ∀m:(B → num). " +
			"    squarefree_polynomial(R, U, c, m) = " +
			"    COND(m ∈ image(squarefree_exponent, {T:set(B) | T ⊆ U}), c(fun_support(0, m)), R.zero)",
	},
})}
