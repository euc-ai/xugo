// The even carrier is a commutative ring; homogeneous insertion respects wedge.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var EvenFormRing = evenFormRingThm{family.Add(registry.ProofEntry{
	Name: "EvenFormRing",
	Key:  "prop_f5763ed0412db6a0",
	Deps: []registry.EntryLike{
		evenFormRingDef,
		FormModule,
		FormAboveDimension,
		WedgeForm,
		WedgeBilinear,
		WedgeAssociative,
		WedgeGradedCommutative,
		WedgeUnit,
	},
	Reading: "This is comm_ring_on of the normalized even carrier, not comm_ring on " +
		"all sequences of raw forms. No exterior derivative is claimed to stay in this ring.",
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀U:set(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)"},
		Conclusion: "comm_ring_on(vec_even_form_ring⟨n⟩(U))",
	},
		"Expand each ring law by degree and reindex the finite convolution sums. "+
			"Odd components vanish, so the graded commutation sign of surviving factors "+
			"is positive; closure and the unit follow from the homogeneous form laws."),
})}

var EvenFormTerm = evenFormTermThm{family.Add(registry.ProofEntry{
	Name: "EvenFormTerm",
	Key:  "prop_2d4c1cf0c2c59404",
	Deps: []registry.EntryLike{evenFormRingDef, formDegreeTermDef, FormModule},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"nat_even(k)", "vec_form_on⟨n⟩(U, k, ω)"},
		Conclusion: "vec_form_degree_term(k, ω) ∈ vec_even_form_ring⟨n⟩(U).carrier",
	},
		"The chosen component is the given form; every other component is a "+
			"zero form of its own degree. Evenness makes each odd component zero."),
})}

var EvenFormTermProduct = evenFormTermProductThm{family.Add(registry.ProofEntry{
	Name: "EvenFormTermProduct",
	Key:  "prop_9c571e0904200aaf",
	Reading: "An identity of the definitions: no parity, form or domain hypothesis " +
		"is read. The wedge is a finite sum of products of values, so a summand of the " +
		"convolution with a zero factor is zero whatever its other factor is.",
	Deps: []registry.EntryLike{evenFormRingDef, formDegreeTermDef, WedgeDef},
	Build: family.Card(Statement{
		Binders:    "∀n p q:num. ∀U:set(num → real). ∀α β:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{},
		Conclusion: "vec_even_form_ring⟨n⟩(U).mul(vec_form_degree_term(p, α), " +
			"    vec_form_degree_term(q, β)) = " +
			"vec_form_degree_term(p + q, vec_form_wedge⟨n⟩(U, p, q, α, β))",
	},
		"In the convolution at degree k, only the summand with index p can survive, and it survives "+
			"only when k=p+q. Every other summand has a zero factor; the p≤k range makes subtraction exact."),
})}

var EvenFormMatrixLift = evenFormMatrixLiftThm{family.Add(registry.ProofEntry{
	Name: "EvenFormMatrixLift",
	Key:  "prop_7e28518109930077",
	Deps: []registry.EntryLike{EvenFormTerm, FormMatrixOnDef, evenFormRingDef, formDegreeTermDef},
	Build: family.Card(Statement{
		Binders: "∀n k r:num. " +
			"∀U:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"nat_even(k)", "vec_form_matrix_on⟨n⟩(U, k, r, r, B)"},
		Conclusion: "matrix_over(vec_even_form_ring⟨n⟩(U), " +
			"    r, " +
			"    (λi:num. λj:num. vec_form_degree_term(k, B(i, j))))",
	},
		"Insert each active entry by EvenFormTerm. Inactive entries are zero forms, whose "+
			"insertion is the whole zero sequence, so the lifted matrix has the required padding."),
})}

var EvenFormSkewMatrixLift = evenFormSkewMatrixLiftThm{family.Add(registry.ProofEntry{
	Name: "EvenFormSkewMatrixLift",
	Key:  "prop_8d70978dcea49fc8",
	Deps: []registry.EntryLike{
		EvenFormMatrixLift,
		FormSkewMatrixOnDef,
		evenFormRingDef,
		formDegreeTermDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n k r:num. " +
			"∀U:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"nat_even(k)", "vec_form_skew_matrix_on⟨n⟩(U, k, r, B)"},
		Conclusion: "matrix_alternating(vec_even_form_ring⟨n⟩(U), " +
			"    r, " +
			"    (λi:num. λj:num. vec_form_degree_term(k, B(i, j))))",
	},
		"Lift skew symmetry componentwise. The original real-valued diagonal "+
			"is its own negative and therefore zero, giving the alternating "+
			"matrix condition even though the even-form ring has zero divisors."),
})}
