package curve_zeta

import (
	_ "github.com/euc-ai/xugo/library/proofs/complex/finite_spectrum"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_formal_series"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	_ "github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

var degreeClassFibreDef = degreeClassFibreDefThm{family.Define(registry.DefEntry{
	Name:  "degreeClassFibreDef",
	Key:   "prop_23b7ad860292d070",
	Deps:  []registry.EntryLike{},
	Const: "curve_degree_classes",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → int → set(set(prod(set(A), set(A))))",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁ A₀₁:set(A). ∀n:int. " +
			"    curve_degree_classes(R, k, A₀, A₁, A₀₁, n) = " +
			"    {curve_pair_class(R, X) | " +
			"        X:prod(set(A), set(A)) | " +
			"        invertible_lattice_pair(R, A₀, A₁, A₀₁, X) ∧ curve_degree(R, k, A₀, A₁, A₀₁, X) = n}",
	},
})}

var divisorIndexDef = divisorIndexDefThm{family.Define(registry.DefEntry{
	Name:  "divisorIndexDef",
	Key:   "prop_6a480a40cb43a31b",
	Deps:  []registry.EntryLike{},
	Const: "curve_divisor_index",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁ A₀₁:set(A). " +
			"    curve_divisor_index(R, k, A₀, A₁, A₀₁) = " +
			"    εd:num. " +
			"        0 < d ∧ " +
			"        {closed_divisor_degree(R, k, A₀, A₁, D) | " +
			"            D:(prod(set(A), set(A)) → int) | " +
			"            closed_divisor(R, A₀, A₁, A₀₁, D)} = " +
			"        {d * z | z:int | true}",
	},
})}

var CurveEffectiveCountDef = curveEffectiveCountDefThm{family.Define(registry.DefEntry{
	Name:  "CurveEffectiveCountDef",
	Key:   "prop_aec81f6d660e74a9",
	Deps:  []registry.EntryLike{},
	Const: "curve_effective_count",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → int → real",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁ A₀₁:set(A). ∀n:int. " +
			"    curve_effective_count(R, k, A₀, A₁, A₀₁, n) = " +
			"    COND(n < int_of_num(0), " +
			"        real_of_num(0), " +
			"        real_of_num(weighted_count( " +
			"                {P:prod(set(A), set(A)) | curve_closed_point(R, A₀, A₁, A₀₁, P)}, " +
			"                curve_closed_degree(R, k, A₀, A₁), " +
			"                num_of_int(n))))",
	},
})}

var CurveZetaNumeratorDef = curveZetaNumeratorDefThm{family.Define(registry.DefEntry{
	Name:  "CurveZetaNumeratorDef",
	Key:   "prop_8332bf827c6466e0",
	Deps:  []registry.EntryLike{CurveEffectiveCountDef},
	Const: "curve_zeta_numerator",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → num → real",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁ A₀₁:set(A). " +
			"    curve_zeta_numerator(R, k, A₀, A₁, A₀₁) = " +
			"    zeta_numerator_coefficient(card(k), curve_effective_count(R, k, A₀, A₁, A₀₁))",
	},
})}

var CurveReciprocalRootsDef = curveReciprocalRootsDefThm{family.Define(registry.DefEntry{
	Name:  "CurveReciprocalRootsDef",
	Key:   "prop_6242d2d3d47a9a16",
	Deps:  []registry.EntryLike{CurveZetaNumeratorDef},
	Const: "curve_reciprocal_roots",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → (num → complex) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁ A₀₁:set(A). ∀a:(num → complex). " +
			"    curve_reciprocal_roots(R, k, A₀, A₁, A₀₁, a) ⇔ " +
			"    (∀i:num. i < 2 * curve_genus(R, k, A₀, A₁, A₀₁) ⇒ a(i) ≠ complex_of_real(real_of_num(0))) ∧ " +
			"    (λn:num. complex_of_real(curve_zeta_numerator(R, k, A₀, A₁, A₀₁, n))) = " +
			"    reciprocal_product(2 * curve_genus(R, k, A₀, A₁, A₀₁), a)",
	},
})}
