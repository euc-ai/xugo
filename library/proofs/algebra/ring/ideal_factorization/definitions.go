package ideal_factorization

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/registry"
)

var idealChainDef = idealChainDefThm{family.Define(registry.DefEntry{
	Name:  "idealChainDef",
	Key:   "prop_3ec4d506608987c",
	Deps:  []registry.EntryLike{},
	Const: "ideal_chain",
	Type:  "ring_ops(A) → set(A) → (num → set(A)) → num → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). ∀C:(num → set(A)). ∀n:num. " +
			"    ideal_chain(R, I, C, n) ⇔ " +
			"    C(0) = I ∧ " +
			"    C(n) = R.carrier ∧ " +
			"    (∀i:num. i ≤ n ⇒ ring_ideal(R, C(i))) ∧ " +
			"    (∀i:num. i < n ⇒ C(i) ⊆ C(i + 1) ∧ C(i) ≠ C(i + 1))",
	},
})}

var FiniteIdealHeightDef = finiteIdealHeightDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteIdealHeightDef",
	Key:   "prop_62fdc11615ca90bf",
	Deps:  []registry.EntryLike{idealChainDef},
	Const: "finite_ideal_height",
	Type:  "ring_ops(A) → set(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). " +
			"    finite_ideal_height(R, I) ⇔ " +
			"    ∃h:num. ∀C:(num → set(A)). ∀n:num. ideal_chain(R, I, C, n) ⇒ n ≤ h",
	},
})}

var IdealHeightDef = idealHeightDefThm{family.Define(registry.DefEntry{
	Name: "IdealHeightDef",
	Key:  "prop_db2685a9e8102052",
	Reading: "Use only on an ideal with bounded chain length; " +
		"otherwise Hilbert choice carries no maximum assertion.",
	Deps:  []registry.EntryLike{idealChainDef},
	Const: "ideal_height",
	Type:  "ring_ops(A) → set(A) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). " +
			"    ideal_height(R, I) = " +
			"    εh:num. " +
			"        (∃C:(num → set(A)). ideal_chain(R, I, C, h)) ∧ " +
			"        (∀C:(num → set(A)). ∀n:num. ideal_chain(R, I, C, n) ⇒ n ≤ h)",
	},
})}

var IdealExponentProductDef = idealExponentProductDefThm{family.Define(registry.DefEntry{
	Name:  "IdealExponentProductDef",
	Key:   "prop_438315406ac7b52e",
	Deps:  []registry.EntryLike{},
	Const: "ideal_exponent_product",
	Type:  "ring_ops(A) → (set(A) → num) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀v:(set(A) → num). " +
			"    ideal_exponent_product(R, v) = " +
			"    set_fold(λm:set(A). λJ:set(A). ideal_mul(R, ideal_pow(R, m, v(m)), J), " +
			"        fun_support(0, v), " +
			"        R.carrier)",
	},
})}

var fractionalExponentProductDef = fractionalExponentProductDefThm{family.Define(registry.DefEntry{
	Name:  "fractionalExponentProductDef",
	Key:   "prop_1e6cbd82b4fe833c",
	Deps:  []registry.EntryLike{},
	Const: "fractional_exponent_product",
	Type:  "ring_ops(A) → set(A) → (set(A) → int) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). ∀v:(set(A) → int). " +
			"    fractional_exponent_product(R, S, v) = " +
			"    set_fold(λm:set(A). λJ:set(A). " +
			"            fractional_mul(R, " +
			"                S, " +
			"                monoid_pow(fractional_mul(R, S), " +
			"                    S, " +
			"                    COND(0 ≤ v(m), m, fractional_inverse(R, S, m)), " +
			"                    num_of_int(int_abs(v(m)))), " +
			"                J), " +
			"        fun_support(int_of_num(0), v), " +
			"        S)",
	},
})}

var maximalExponentVectorsDef = maximalExponentVectorsDefThm{family.Define(registry.DefEntry{
	Name:  "maximalExponentVectorsDef",
	Key:   "prop_1d4e22218b197fd4",
	Deps:  []registry.EntryLike{},
	Const: "maximal_exponent_vectors",
	Type:  "ring_ops(A) → set(set(A) → int)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    maximal_exponent_vectors(R) = " +
			"    {v:(set(A) → int) | " +
			"        finite(fun_support(int_of_num(0), v)) ∧ " +
			"        (∀m:set(A). v(m) ≠ 0 ⇒ maximal_ideal(R, m) ∧ m ≠ {R.zero})}",
	},
})}

var fractionalExponentsDef = fractionalExponentsDefThm{family.Define(registry.DefEntry{
	Name:  "fractionalExponentsDef",
	Key:   "prop_2673a52760c11860",
	Deps:  []registry.EntryLike{maximalExponentVectorsDef, fractionalExponentProductDef},
	Const: "fractional_exponents",
	Type:  "ring_ops(A) → set(A) → set(A) → (set(A) → int)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S I:set(A). " +
			"    fractional_exponents(R, S, I) = " +
			"    εv:(set(A) → int). " +
			"        v ∈ maximal_exponent_vectors(restrict_ring(R, S)) ∧ " +
			"        fractional_exponent_product(R, S, v) = I",
	},
})}
