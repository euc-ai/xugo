// Pfaffians of two-form matrices have fixed degree and respect geometric operations.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/pfaffian"
	"github.com/euc-ai/xugo/library/registry"
)

var PfaffianHomogeneous = pfaffianHomogeneousThm{family.Add(registry.ProofEntry{
	Name: "PfaffianHomogeneous",
	Key:  "prop_ffc09d1cea3342bd",
	Deps: []registry.EntryLike{
		FormPfaffianDef,
		EvenFormRing,
		EvenFormMatrixLift,
		EvenFormTermProduct,
		pfaffian.PfaffianDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, 2, r, r, B)"},
		Conclusion: "pfaffian(vec_even_form_ring⟨n⟩(U), " +
			"    r, " +
			"    (λi:num. λj:num. vec_form_degree_term(2, B(i, j)))) = " +
			"vec_form_degree_term(r, vec_form_pfaffian⟨n⟩(U, r, B))",
	},
		"For even r, every matching product is concentrated in degree r, "+
			"since it has r/2 factors of degree two. Finite addition preserves "+
			"this support; for odd r the algebraic Pfaffian is the zero sequence."),
})}

var PfaffianForm = pfaffianFormThm{family.Add(registry.ProofEntry{
	Name: "PfaffianForm",
	Key:  "prop_35fe6db49585929d",
	Deps: []registry.EntryLike{
		FormPfaffianDef,
		EvenFormRing,
		EvenFormMatrixLift,
		evenFormOnDef,
		pfaffian.PfaffianInCarrier,
	},
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, 2, r, r, B)"},
		Conclusion: "vec_form_on⟨n⟩(U, r, vec_form_pfaffian⟨n⟩(U, r, B))",
	},
		"The algebraic Pfaffian belongs to the even-form carrier. Its degree-r component is "+
			"therefore a normalized smooth r-form; no skew hypothesis is needed for membership."),
})}

var PfaffianEmpty = pfaffianEmptyThm{family.Add(registry.ProofEntry{
	Name: "PfaffianEmpty",
	Key:  "prop_f78daca0dbc267b5",
	Deps: []registry.EntryLike{
		FormPfaffianDef,
		EvenFormRing,
		evenFormRingDef,
		formDegreeTermDef,
		pfaffian.PfaffianEmpty,
	},
	Reading: "On the empty domain the normalized unit is zero, consistently with the zero ring.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀U:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)"},
		Conclusion: "vec_form_pfaffian⟨n⟩(U, 0, B) = «unit»",
	},
		"The empty algebraic Pfaffian is the ring unit. Its degree-zero "+
			"component is one on U and zero off U, independent of every entry of B."),
})}

var PfaffianOdd = pfaffianOddThm{family.Add(registry.ProofEntry{
	Name: "PfaffianOdd",
	Key:  "prop_b0df34af708df88d",
	Deps: []registry.EntryLike{FormPfaffianDef, evenFormRingDef, pfaffian.PfaffianDef},
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"¬nat_even(r)"},
		Conclusion: "vec_form_pfaffian⟨n⟩(U, r, B) = «zero»",
	},
		"The odd branch of the algebraic definition is the ring zero, whose every "+
			"component is the zero form. This uses no smoothness or openness assumption."),
})}

var PfaffianPullback = pfaffianPullbackThm{family.Add(registry.ProofEntry{
	Name: "PfaffianPullback",
	Key:  "prop_ee3080cf4a2b0b6f",
	Deps: []registry.EntryLike{
		FormPfaffianDef,
		PfaffianHomogeneous,
		PullbackLinear,
		PullbackWedge,
		WedgeUnit,
		FormMatrixPullbackDef,
		pfaffian.PfaffianDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m r:num. " +
			"∀U V:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_form_matrix_on⟨m⟩(V, 2, r, r, B)",
		},
		Conclusion: "vec_form_pfaffian⟨n⟩(U, r, vec_form_matrix_pullback⟨n, m⟩(U, 2, r, r, f, B)) = " +
			"vec_form_pullback⟨n, m⟩(U, r, f, vec_form_pfaffian⟨m⟩(V, r, B))",
	},
		"Expand the finite matching polynomial and commute pullback through every sum "+
			"and wedge. Pullback carries the normalized target unit to the normalized "+
			"source unit by the image condition, which also handles order zero."),
})}

var PfaffianScale = pfaffianScaleThm{family.Add(registry.ProofEntry{
	Name: "PfaffianScale",
	Key:  "prop_ef7b83056818e95e",
	Deps: []registry.EntryLike{
		FormPfaffianDef,
		PfaffianHomogeneous,
		WedgeBilinear,
		pfaffian.PfaffianDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀U:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real). " +
			"∀t:real.",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, 2, 2 * m, 2 * m, B)"},
		Conclusion: "vec_form_pfaffian⟨n⟩(U, " +
			"    2 * m, " +
			"    (λi:num. λj:num. λx:(num → real). λP:(num → num → real). t * B(i, j, x, P))) = " +
			"(λx:(num → real). λP:(num → num → real). t ^ m * vec_form_pfaffian⟨n⟩(U, 2 * m, B, x, P))",
	},
		"Each matching has m factors. Wedge multilinearity extracts one t from each factor, "+
			"so every summand has the common factor t^m; for m=0 that factor is one, also at t=0."),
})}

var PfaffianCongruence = pfaffianCongruenceThm{family.Add(registry.ProofEntry{
	Name: "PfaffianCongruence",
	Key:  "prop_8f97f86215413623",
	Deps: []registry.EntryLike{
		FormMatrixConjugateDef,
		PfaffianHomogeneous,
		EvenFormRing,
		EvenFormSkewMatrixLift,
		EvenFormMatrixLift,
		EvenFormTermProduct,
		FormZeroDegree,
		pfaffian.PfaffianCongruence,
	},
	Reading: "H need not be invertible or orthogonal. The determinant is evaluated at " +
		"the empty frame because H has degree zero; at order zero the real determinant is " +
		"one even outside U, and the normalized Pfaffian supplies the domain guard.",
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀U:set(num → real). " +
			"∀H B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_skew_matrix_on⟨n⟩(U, 2, 2 * m, B)",
			"vec_form_matrix_on⟨n⟩(U, 0, 2 * m, 2 * m, H)",
		},
		Conclusion: "vec_form_pfaffian⟨n⟩(U, 2 * m, vec_form_matrix_conjugate⟨n⟩(U, 2, 2 * m, H, B)) = " +
			"(λx:(num → real). λP:(num → num → real). " +
			"    determinant(real_ring, 2 * m, (λi:num. λj:num. H(i, j, x, «empty frame»))) * " +
			"    vec_form_pfaffian⟨n⟩(U, 2 * m, B, x, P))",
	},
		"Lift H into degree zero and B into degree two of the even-form ring. Apply the "+
			"algebraic congruence identity and take degree 2m; the degree-zero determinant "+
			"is the pointwise real determinant on U, while normalized factors vanish off U."),
})}

var PfaffianOrientedFrame = pfaffianOrientedFrameThm{family.Add(registry.ProofEntry{
	Name: "PfaffianOrientedFrame",
	Key:  "prop_2b7193da9b7b1f12",
	Deps: []registry.EntryLike{PfaffianCongruence, PfaffianForm, FormOnDef},
	Reading: "Determinant one suffices for invariance. Positive " +
		"determinant without unit value would still rescale the Pfaffian.",
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀U:set(num → real). " +
			"∀H B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_skew_matrix_on⟨n⟩(U, 2, 2 * m, B)",
			"vec_form_matrix_on⟨n⟩(U, 0, 2 * m, 2 * m, H)",
			"∀x:(num → real). " +
				"    x ∈ U ⇒ determinant(real_ring, 2 * m, (λi:num. λj:num. H(i, j, x, «empty frame»))) = &1",
		},
		Conclusion: "vec_form_pfaffian⟨n⟩(U, 2 * m, vec_form_matrix_conjugate⟨n⟩(U, 2, 2 * m, H, B)) = " +
			"vec_form_pfaffian⟨n⟩(U, 2 * m, B)",
	},
		"The determinant factor is one on U by hypothesis. Both Pfaffians vanish "+
			"outside U by normalization, so the equality holds as whole functions."),
})}

var PfaffianUnitKernel = pfaffianUnitKernelThm{family.Add(registry.ProofEntry{
	Name: "PfaffianUnitKernel",
	Key:  "prop_7c318e024dde6580",
	Deps: []registry.EntryLike{
		FormPfaffianDef,
		EvenFormRing,
		EvenFormSkewMatrixLift,
		EvenFormTerm,
		EvenFormTermProduct,
		FormZeroDegree,
		pfaffian.PfaffianUnimodularKernel,
	},
	Reading: "No assumption on the tail of u is needed: the algebraic vector is explicitly padded. " +
		"At m=0 the unit-length hypothesis forces U empty, so the normalized empty Pfaffian also vanishes.",
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀U:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real). " +
			"∀u:(num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_skew_matrix_on⟨n⟩(U, 2, 2 * m, B)",
			"∀i:num. i < 2 * m ⇒ vec_form_on⟨n⟩(U, 0, u(i))",
			"∀x:(num → real). x ∈ U ⇒ (Σ_{i<2 * m} u(i, x, «empty frame») * u(i, x, «empty frame»)) = &1",
			"∀i:num. " +
				"    i < 2 * m ⇒ " +
				"    (λx:(num → real). λP:(num → num → real). " +
				"        Σ_{j<2 * m} vec_form_wedge⟨n⟩(U, 2, 0, B(i, j), u(j), x, P)) = " +
				"    «zero»",
		},
		Conclusion: "vec_form_pfaffian⟨n⟩(U, 2 * m, B) = «zero»",
	},
		"Insert the active u entries into degree zero and set all inactive entries to the ring zero. "+
			"The unit-length identity makes this padded vector its own dual with pairing one, while the "+
			"kernel identity lifts by degree; apply PfaffianUnimodularKernel and take degree 2m."),
})}
