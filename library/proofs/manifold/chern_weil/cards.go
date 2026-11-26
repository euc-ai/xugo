package chern_weil

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/real/real_formal_series"
	"github.com/euc-ai/xugo/library/proofs/relations/well_founded"
	"github.com/euc-ai/xugo/library/registry"
)

var ToddRecurrence = toddRecurrenceThm{family.Add(registry.ProofEntry{
	Name: "ToddRecurrence",
	Key:  "prop_7766e530eb4af827",
	Deps: []registry.EntryLike{well_founded.NatRecursion},
	Build: family.Card(
		"∀n:num. "+
			"∀T:set(set(A)). "+
			"∀𝒜:set(prod(set(A), A → num → real)). "+
			"∀P:prod(num, A → num → num → complex). "+
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). "+
			"    todd_form(n, T, 𝒜, P, Γ, 0) = manifold_form_unit⟨n⟩(T, 𝒜) ∧ "+
			"    (∀k:num. "+
			"        todd_form(n, T, 𝒜, P, Γ, suc(k)) = "+
			"        (manifold_form_module⟨n⟩(T, 𝒜, 0)).smul(&1 / real_of_num(suc(k)), "+
			"            module_sum((manifold_form_module⟨n⟩(T, 𝒜, 0)).add, "+
			"                (manifold_form_module⟨n⟩(T, 𝒜, 0)).zero, "+
			"                {j:num | j ≤ k}, "+
			"                λj:num. "+
			"                    (manifold_form_module⟨n⟩(T, 𝒜, 0)).smul(real_of_num(suc(j)) * "+
			"                        todd_log_coefficient(suc(j)) * "+
			"                        real_of_num(factorial(suc(j))), "+
			"                        manifold_form_wedge⟨n⟩(T, "+
			"                            𝒜, "+
			"                            2 * suc(j), "+
			"                            2 * (k - j), "+
			"                            chern_form(n, T, 𝒜, P, Γ, suc(j)), "+
			"                            todd_form(n, T, 𝒜, P, Γ, k - j))))))",
		"NatRecursion constructs a sequence of forms whose value at suc(k) is the "+
			"displayed sum, which reads the sequence only at the earlier degrees k − j with "+
			"j ≤ k; the epsilon-selected sequence therefore satisfies the finite recurrence."),
})}

var GrassmannConnection = grassmannConnectionThm{family.Add(registry.ProofEntry{
	Name: "GrassmannConnection",
	Key:  "prop_a646795b1ffd364",
	Deps: []registry.EntryLike{
		differential_form.FunctionForm,
		differential_form.WedgeZeroRight,
		differential_form.WedgeGradedCommutative,
		differential_form.FormModule,
		differential_form.FormModulePointwise,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))"},
		Conclusion: "projection_connection(n, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    (λi:num. λj:num. λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"        complex_of_real(&0)))",
	}, "The zero matrix is a matrix of zero one-forms (FormModule, "+
		"FormModulePointwise). In P(0·P) every term is a complex wedge with a zero factor "+
		"and a matrix entry of P, a zero-form by FunctionForm; WedgeZeroRight kills it, "+
		"and WedgeGradedCommutative turns a zero left factor into a zero right one."),
})}

// MatrixProductForm — the product of a matrix of complex p-forms and a matrix of complex
// q-forms is a matrix of complex (p + q)-forms.
var MatrixProductForm = matrixProductFormThm{family.Add(registry.ProofEntry{
	Name: "MatrixProductForm",
	Key:  "prop_8c9616d42c05e7d7",
	Deps: []registry.EntryLike{
		differential_form.WedgeForm,
		differential_form.FormAdd,
		differential_form.FormModule,
		differential_form.FormModulePointwise,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r p q:num. " +
			"∀U W:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀i j:num.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"∀k l:num. k < r ∧ l < r ⇒ complex_form_on(n, T, 𝒜, p, U(k, l))",
			"∀k l:num. k < r ∧ l < r ⇒ complex_form_on(n, T, 𝒜, q, W(k, l))",
		},
		Conclusion: "complex_form_on(n, T, 𝒜, p + q, chern_matrix_product(n, T, 𝒜, r, p, q, U, W, i, j))",
	},
		"Below r the entry is a finite complex sum of complex wedges, whose real and "+
			"imaginary parts are sums and differences of real wedges of a p-form and a "+
			"q-form (WedgeForm, FormAdd); finite sums and negatives stay in the form module "+
			"(FormModule, FormModulePointwise). At or beyond r the entry is the zero form."),
	Reading: "smooth_manifold⟨n⟩(T, 𝒜) is load-bearing: at r = 0, or at an " +
		"index at or beyond r, the entry is the zero family and the form hypotheses " +
		"are vacuous, and only the manifold makes the zero family a (p+q)-form.",
})}

var CurvatureForm = curvatureFormThm{family.Add(registry.ProofEntry{
	Name: "CurvatureForm",
	Key:  "prop_d1894517b2d97278",
	Deps: []registry.EntryLike{
		MatrixProductForm,
		differential_form.FunctionForm,
		differential_form.ExteriorDerivativeForm,
		differential_form.FormAdd,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀i j:num.",
		Hypotheses: []string{"projection_connection(n, T, 𝒜, P, Γ)"},
		Conclusion: "complex_form_on(n, T, 𝒜, 2, projection_curvature(n, T, 𝒜, P, Γ, i, j))",
	},
		"Degree bookkeeping on the three terms of the curvature. The matrix entries of P are complex "+
			"zero-forms (FunctionForm on their smooth real and imaginary parts), their differentials and "+
			"those of Γ raise the degree by one (ExteriorDerivativeForm), and MatrixProductForm gives "+
			"degree 0 + 2, 2 + 0 and 1 + 1 to the products; FormAdd sums the three complex two-forms."),
})}

var ChernClosed = chernClosedThm{family.Add(registry.ProofEntry{
	Name: "ChernClosed",
	Key:  "prop_1c5925e12757c0bc",
	Deps: []registry.EntryLike{CurvatureForm, MatrixProductForm},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀k:num.",
		Hypotheses: []string{"projection_connection(n, T, 𝒜, P, Γ)"},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, 2 * k, chern_form(n, T, 𝒜, P, Γ, k)) ∧ " +
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, 2 * k, chern_form(n, T, 𝒜, P, Γ, k)) = " +
			"(λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0)",
	},
		"By induction on k, MatrixProductForm applied to the normalized curvature (CurvatureForm) "+
			"makes every curvature power a matrix of complex 2k-forms, so the real part of its trace "+
			"over k! is a 2k-form. The Bianchi identity and the graded cyclic trace close it."),
})}

var ChernConnectionIndependent = chernConnectionIndependentThm{family.Add(registry.ProofEntry{
	Name: "ChernConnectionIndependent",
	Key:  "prop_702ea618bbdf8efd",
	Deps: []registry.EntryLike{ChernClosed, GrassmannConnection},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀k:num.",
		Hypotheses: []string{"projection_connection(n, T, 𝒜, P, Γ)"},
		Conclusion: "de_rham_class⟨n⟩(T, 𝒜, 2 * k, chern_form(n, T, 𝒜, P, Γ, k)) = " +
			"chern_class(n, T, 𝒜, P, k)",
	},
		"Interpolate connections linearly on the interval and integrate the transgression "+
			"form. The resulting exact difference identifies the component classes."),
})}

var ToddClosed = toddClosedThm{family.Add(registry.ProofEntry{
	Name: "ToddClosed",
	Key:  "prop_8e75afcaf5fbdafc",
	Deps: []registry.EntryLike{CurvatureForm, ChernClosed, ToddRecurrence},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀k:num.",
		Hypotheses: []string{"projection_connection(n, T, 𝒜, P, Γ)"},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, 2 * k, todd_form(n, T, 𝒜, P, Γ, k)) ∧ " +
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, 2 * k, todd_form(n, T, 𝒜, P, Γ, k)) = " +
			"(λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0)",
	},
		"The Bianchi identity and graded cyclic trace close every Chern "+
			"component; finite sums and wedges close every Todd component."),
})}

var ToddConnectionIndependent = toddConnectionIndependentThm{family.Add(registry.ProofEntry{
	Name: "ToddConnectionIndependent",
	Key:  "prop_9ecdc45769f10cce",
	Deps: []registry.EntryLike{ToddClosed, GrassmannConnection},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀k:num.",
		Hypotheses: []string{"projection_connection(n, T, 𝒜, P, Γ)"},
		Conclusion: "de_rham_class⟨n⟩(T, 𝒜, 2 * k, todd_form(n, T, 𝒜, P, Γ, k)) = " +
			"todd_class(n, T, 𝒜, P, k)",
	},
		"Interpolate connections linearly on the interval and integrate the transgression "+
			"form. The resulting exact difference identifies the component classes."),
})}

var ToddSeries = toddSeriesThm{family.Add(registry.ProofEntry{
	Name: "ToddSeries",
	Key:  "prop_c30aa02a4d26ab17",
	Deps: []registry.EntryLike{well_founded.NatRecursion, real_formal_series.RealFormalExpOfCounts},
	Build: family.Card(
		"∀k:num. "+
			"    real_sum({j:num | j ≤ k}, "+
			"        λj:num. "+
			"            todd_coefficient(j) * real_pow(-&1, k - j) / real_of_num(factorial(suc(k - j)))) = "+
			"    COND(k = 0, &1, &0) ∧ "+
			"    todd_log_coefficient(0) = &0 ∧ "+
			"    formal_exp_zero(real_ring, todd_log_coefficient) = todd_coefficient",
		"The denominator series has constant coefficient one, so NatRecursion solves each "+
			"coefficient of its inverse from the earlier ones. With a = todd_coefficient, "+
			"NatRecursion also solves m(n) = n·a(n) − Σ_{0<i<n} m(i)·a(n − i), which gives "+
			"series_recurrence(real_ring, a, m); the filler may promote this existence of counts "+
			"for a series with constant coefficient one to formal_series. RealFormalExpOfCounts "+
			"then makes λn. COND(n = 0, 0, m(n)/n) a zero-constant exponent of a."),
})}

var ChernIsomorphism = chernIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ChernIsomorphism",
	Key:  "prop_2f1e309e863236af",
	Deps: []registry.EntryLike{
		ChernConnectionIndependent,
		MatrixProductForm,
		smooth_projection_bundle.SmoothNormalizedInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:prod(num, A → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"smooth_projection_bundle(n, fst(Q), T, 𝒜, snd(Q))",
			"projection_isomorphic(T, P, Q)",
		},
		Conclusion: "chern_class(n, T, 𝒜, P, k) = chern_class(n, T, 𝒜, Q, k)",
	},
		"Smooth the continuous isomorphism u from P to Q into a smooth invertible one; its "+
			"normalized inverse v is smooth by SmoothNormalizedInverse in each chart. The Grassmann "+
			"connection of P carried through u and v is a projected connection on Q "+
			"(MatrixProductForm) whose curvature is u F v for P's curvature F, so the graded cyclic "+
			"trace gives it P's Chern forms, and ChernConnectionIndependent identifies the classes."),
})}

var ChernDirectSum = chernDirectSumThm{family.Add(registry.ProofEntry{
	Name: "ChernDirectSum",
	Key:  "prop_77ca74f742268361",
	Deps: []registry.EntryLike{ChernConnectionIndependent},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:prod(num, A → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"smooth_projection_bundle(n, fst(Q), T, 𝒜, snd(Q))",
		},
		Conclusion: "chern_class(n, T, 𝒜, projection_sum(P, Q), k) = " +
			"(de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * k)).add(chern_class(n, T, 𝒜, P, k), " +
			"    chern_class(n, T, 𝒜, Q, k))",
	},
		"Block diagonal connections split the trace. Exponentiating the "+
			"additive logarithmic characteristic form makes Todd multiplicative."),
})}

var ToddDirectSum = toddDirectSumThm{family.Add(registry.ProofEntry{
	Name: "ToddDirectSum",
	Key:  "prop_f777e4cb9aa20e05",
	Deps: []registry.EntryLike{ToddConnectionIndependent},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:prod(num, A → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"smooth_projection_bundle(n, fst(Q), T, 𝒜, snd(Q))",
		},
		Conclusion: "todd_class(n, T, 𝒜, projection_sum(P, Q), k) = " +
			"de_rham_class⟨n⟩(T, " +
			"    𝒜, " +
			"    2 * k, " +
			"    module_sum((manifold_form_module⟨n⟩(T, 𝒜, 0)).add, " +
			"        (manifold_form_module⟨n⟩(T, 𝒜, 0)).zero, " +
			"        {j:num | j ≤ k}, " +
			"        λj:num. " +
			"            manifold_form_wedge⟨n⟩(T, " +
			"                𝒜, " +
			"                2 * j, " +
			"                2 * (k - j), " +
			"                todd_form(n, " +
			"                    T, " +
			"                    𝒜, " +
			"                    P, " +
			"                    (λi:num. " +
			"                    λj:num. " +
			"                    λc:prod(set(A), A → num → real). " +
			"                    λy:(num → real). " +
			"                    λV:(num → num → real). " +
			"                        complex_of_real(&0)), " +
			"                    j), " +
			"                todd_form(n, " +
			"                    T, " +
			"                    𝒜, " +
			"                    Q, " +
			"                    (λi:num. " +
			"                    λj:num. " +
			"                    λc:prod(set(A), A → num → real). " +
			"                    λy:(num → real). " +
			"                    λV:(num → num → real). " +
			"                        complex_of_real(&0)), " +
			"                    k - j))))",
	},
		"Block diagonal connections split the trace. Exponentiating the "+
			"additive logarithmic characteristic form makes Todd multiplicative."),
})}

var ChernNaturality = chernNaturalityThm{family.Add(registry.ProofEntry{
	Name: "ChernNaturality",
	Key:  "prop_2521ac619caebc83",
	Deps: []registry.EntryLike{ChernConnectionIndependent},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀d:num. " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀P:prod(num, B → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, d⟩(T, 𝒜, S, ℬ, f)",
			"smooth_projection_bundle(d, fst(P), S, ℬ, snd(P))",
		},
		Conclusion: "chern_class(n, T, 𝒜, projection_pullback(T, f, P), k) = " +
			"de_rham_pullback⟨n, d⟩(T, 𝒜, S, ℬ, 2 * k, f, chern_class(d, S, ℬ, P, k))",
	},
		"Pull back a projected connection and its curvature. Exterior pullback commutes "+
			"with finite matrix products, traces and the characteristic recurrence; "+
			"connection independence removes the selected Grassmann representatives."),
})}

var ToddNaturality = toddNaturalityThm{family.Add(registry.ProofEntry{
	Name: "ToddNaturality",
	Key:  "prop_31e7f9ab5d17df77",
	Deps: []registry.EntryLike{ToddConnectionIndependent},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀d:num. " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀P:prod(num, B → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, d⟩(T, 𝒜, S, ℬ, f)",
			"smooth_projection_bundle(d, fst(P), S, ℬ, snd(P))",
		},
		Conclusion: "todd_class(n, T, 𝒜, projection_pullback(T, f, P), k) = " +
			"de_rham_pullback⟨n, d⟩(T, 𝒜, S, ℬ, 2 * k, f, todd_class(d, S, ℬ, P, k))",
	},
		"Pull back a projected connection and its curvature. Exterior pullback commutes "+
			"with finite matrix products, traces and the characteristic recurrence; "+
			"connection independence removes the selected Grassmann representatives."),
})}

var ToddIsomorphism = toddIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ToddIsomorphism",
	Key:  "prop_d6218f6af097d93",
	Deps: []registry.EntryLike{
		ToddConnectionIndependent,
		ToddRecurrence,
		MatrixProductForm,
		smooth_projection_bundle.SmoothNormalizedInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:prod(num, A → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"smooth_projection_bundle(n, fst(Q), T, 𝒜, snd(Q))",
			"projection_isomorphic(T, P, Q)",
		},
		Conclusion: "todd_class(n, T, 𝒜, P, k) = todd_class(n, T, 𝒜, Q, k)",
	},
		"Smooth the continuous isomorphism u from P to Q into a smooth invertible one; "+
			"its normalized inverse v is smooth by SmoothNormalizedInverse in each chart. The "+
			"Grassmann connection of P carried through u and v is a projected connection on Q "+
			"(MatrixProductForm) with P's Chern forms, so the recurrence (ToddRecurrence) "+
			"gives it P's Todd forms, and ToddConnectionIndependent identifies the classes."),
})}

var ToddTrivial = toddTrivialThm{family.Add(registry.ProofEntry{
	Name: "ToddTrivial",
	Key:  "prop_d62eefc371b5ef45",
	Deps: []registry.EntryLike{ToddRecurrence},
	Build: family.Card(Statement{
		Binders:    "∀n r k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "todd_class(n, T, 𝒜, projection_trivial(T, r), k) = " +
			"COND(k = 0, " +
			"    de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)), " +
			"    (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * k)).zero)",
	},
		"The trivial projection is constant on the carrier, so the Grassmann curvature "+
			"vanishes and every positive-degree Chern form is zero. The recurrence then "+
			"makes every positive Todd form zero, and the degree-zero Todd form is the unit."),
})}

var ChernTensor = chernTensorThm{family.Add(registry.ProofEntry{
	Name: "ChernTensor",
	Reading: "The identity is in cohomology. For arbitrary complex connections the real parts of " +
		"their Chern forms need not multiply pointwise; unitary representatives give the class identity.",
	Key:  "prop_c85f2f3fb825a8e7",
	Deps: []registry.EntryLike{ChernConnectionIndependent},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:prod(num, A → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"smooth_projection_bundle(n, fst(Q), T, 𝒜, snd(Q))",
		},
		Conclusion: "chern_class(n, T, 𝒜, projection_tensor(P, Q), k) = " +
			"module_sum((de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * k)).add, " +
			"    (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * k)).zero, " +
			"    {j:num | j ≤ k}, " +
			"    λj:num. " +
			"        de_rham_wedge⟨n⟩(T, " +
			"            𝒜, " +
			"            2 * j, " +
			"            2 * (k - j), " +
			"            chern_class(n, T, 𝒜, P, j), " +
			"            chern_class(n, T, 𝒜, Q, k - j)))",
	},
		"Use unitary tensor-product connections, whose commuting curvature factors "+
			"exponentiate separately. Their real characteristic classes multiply; "+
			"connection independence permits the displayed Grassmann choices."),
})}
