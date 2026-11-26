package ideal_norm

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_norm"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/registry"
)

var IdealNormDef = idealNormDefThm{family.Define(registry.DefEntry{
	Name: "IdealNormDef",
	Key:  "prop_8d0ae11943ba1bce",
	Reading: "The quotient cardinality is total; finite positive " +
		"norm laws require a nonzero integral ideal in a number field.",
	Deps:  []registry.EntryLike{},
	Const: "number_ideal_norm",
	Type:  "ring_ops(A) → set(A) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). " +
			"    number_ideal_norm(R, I) = card(left_cosets(R.add, ring_of_integers(R), I))",
	},
})}

var FractionalNormDef = fractionalNormDefThm{family.Define(registry.DefEntry{
	Name:  "FractionalNormDef",
	Key:   "prop_9e7274ca695262e1",
	Deps:  []registry.EntryLike{IdealNormDef},
	Const: "fractional_ideal_norm",
	Type:  "field_ops(A) → set(A) → real",
	Equations: []string{
		"∀F:field_ops(A). ∀I:set(A). " +
			"    fractional_ideal_norm(F, I) = " +
			"    εr:real. ∃d:A. " +
			"        d ∈ ring_of_integers(field_ring(F)) ∧ " +
			"        d ≠ F.zero ∧ " +
			"        image(F.mul(d), I) ⊆ ring_of_integers(field_ring(F)) ∧ " +
			"        r = " +
			"        real_of_num(number_ideal_norm(field_ring(F), image(F.mul(d), I))) / " +
			"        real_abs(rational_value(F, field_norm(field_ring(F), rational_image(F), d)))",
	},
})}

var FractionalNormExtension = fractionalNormExtensionThm{family.Add(registry.ProofEntry{
	Name: "FractionalNormExtension",
	Key:  "prop_f62055ad0d972622",
	Deps: []registry.EntryLike{
		FractionalNormDef,
		IdealNormMultiplicative,
		IdealNormPositive,
		PrincipalIdealIndexAbsNorm,
		field_norm.FieldNormMultiplicative,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"bounded_fractional(field_ring(L), ring_of_integers(field_ring(L)), I)",
			"bounded_fractional(field_ring(L), ring_of_integers(field_ring(L)), J)",
		},
		Conclusion: "rational(fractional_ideal_norm(L, I)) ∧ " +
			"real_of_num(0) < fractional_ideal_norm(L, I) ∧ " +
			"fractional_ideal_norm(L, " +
			"    fractional_mul(field_ring(L), ring_of_integers(field_ring(L)), I, J)) = " +
			"fractional_ideal_norm(L, I) * fractional_ideal_norm(L, J) ∧ " +
			"fractional_ideal_norm(L, " +
			"    fractional_inverse(field_ring(L), ring_of_integers(field_ring(L)), I)) = " +
			"real_of_num(1) / fractional_ideal_norm(L, I) ∧ " +
			"(∀d:A. " +
			"    d ∈ ring_of_integers(field_ring(L)) ∧ " +
			"    d ≠ L.zero ∧ " +
			"    image(L.mul(d), I) ⊆ ring_of_integers(field_ring(L)) ⇒ " +
			"    fractional_ideal_norm(L, I) = " +
			"    real_of_num(number_ideal_norm(field_ring(L), image(L.mul(d), I))) / " +
			"    real_abs(rational_value(L, field_norm(field_ring(L), rational_image(L), d))))",
	},
		"Compare two denominators by multiplying both scaled integral ideals to the "+
			"common product denominator. Integral norm multiplicativity and the principal "+
			"norm formula show independence; they also give the product and inverse formulas."),
})}
