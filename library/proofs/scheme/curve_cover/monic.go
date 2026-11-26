// monic.go — the chapter's monic statements.

package curve_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/trace_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/kaehler"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	"github.com/euc-ai/xugo/library/registry"
)

// MonicCoverFree — The short powers of each monic chart generator form its chart basis.
var MonicCoverFree = monicCoverFreeThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverFree",
	Key:  "prop_3405395220661ee",
	Deps: []registry.EntryLike{
		MonicCoverDef,
		polynomial_division.MonicDivisionAlgorithm,
		linear_independence.ModuleBasisDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
		},
		Conclusion: "module_basis(restrict_ring(field_ring(L), A₀), " +
			"    restrict_module(regular_module(field_ring(L)), B₀), " +
			"    {monoid_pow(L.mul, L.one, y₀, j) | j:num | j < polynomial_degree(F₀)}) ∧ " +
			"module_basis(restrict_ring(field_ring(L), A₁), " +
			"    restrict_module(regular_module(field_ring(L)), B₁), " +
			"    {monoid_pow(L.mul, L.one, y₁, j) | j:num | j < polynomial_degree(F₁)}) ∧ " +
			"has_size({monoid_pow(L.mul, L.one, y₀, j) | j:num | j < polynomial_degree(F₀)}, " +
			"    polynomial_degree(F₀)) ∧ " +
			"has_size({monoid_pow(L.mul, L.one, y₁, j) | j:num | j < polynomial_degree(F₁)}, " +
			"    polynomial_degree(F₁))",
	},
		"Use MonicDivisionAlgorithm and the exact evaluation kernels: "+
			"short remainders span, and a vanishing short remainder is zero. "+
			"Distinct power vectors follow from the same independence argument."),
})}

// MonicCoverPrimitive — Each chart generator generates the function field and its chart equation is the separable minimal polynomial.
var MonicCoverPrimitive = monicCoverPrimitiveThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverPrimitive",
	Key:  "prop_7796c335216c089b",
	Deps: []registry.EntryLike{
		MonicCoverFree,
		MonicCoverDef,
		algebraic_curve.FractionFieldBothCharts,
		algebraic_element.MinimalPolynomialSpec,
		separable_polynomial.SeparableIffDerivative,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
		},
		Conclusion: "field_adjoin(L, K, {y₀}) = L.carrier ∧ " +
			"field_adjoin(L, K, {y₁}) = L.carrier ∧ " +
			"minimal_polynomial(L, K, y₀) = F₀ ∧ " +
			"minimal_polynomial(L, K, y₁) = F₁ ∧ " +
			"polynomial_separable(restrict_ring(field_ring(L), K), F₀) ∧ " +
			"polynomial_separable(restrict_ring(field_ring(L), K), F₁)",
	},
		"The fraction fields of A_i and B_i show L=K(y_i). Clear an A_i-denominator "+
			"in a polynomial over K to extend the evaluation kernel; monic uniqueness "+
			"gives F_i=μ_i. Nonzero derivative and irreducibility give separability."),
})}

// MonicCoverIsCover — Exact monic presentations supply a covering whose degree is each chart polynomial degree.
var MonicCoverIsCover = monicCoverIsCoverThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverIsCover",
	Key:  "prop_f38dd598b0086356",
	Deps: []registry.EntryLike{
		MonicCoverFree,
		MonicCoverPrimitive,
		CurveCoverDef,
		module_dimension.DimBasis,
		algebraic_element.AdjoinPowerBasis,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
		},
		Conclusion: "curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁) ∧ " +
			"cover_degree(field_ring(L), K) = polynomial_degree(F₀) ∧ " +
			"cover_degree(field_ring(L), K) = polynomial_degree(F₁)",
	},
		"MonicCoverPrimitive identifies each F_i with μ_i and gives K(y_i)=L. "+
			"AdjoinPowerBasis then supplies the K-power bases; MonicCoverFree supplies the "+
			"chart bases, so CurveCoverDef applies and DimBasis gives both degree formulas."),
})}

// MonicCoverTraceDual — The inverse different on a monic chart is the chart ring divided by the derivative value.
var MonicCoverTraceDual = monicCoverTraceDualThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverTraceDual",
	Key:  "prop_7063b6a6bae39ee8",
	Reading: "Each chart is the monogenic case of the codifferent, B_i = " +
		"A_i[y_i] with the separable minimal polynomial F_i over A_i; the derivative " +
		"formula is the general one, read at the two charts with their own generators.",
	Deps: []registry.EntryLike{
		MonicCoverPrimitive,
		MonicCoverDef,
		InverseDifferentDef,
		trace_dual.MonogenicCodifferent,
		algebraic_curve.CurveOverLineDef,
		lattice_pair.BiaffineDef,
		algebraic_element.AlgebraicOverDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
		},
		Conclusion: "fst(inverse_different(L, K, A₀, A₁, B₀, B₁)) = " +
			"image(L.mul(L.inv(polynomial_eval(polynomial_derivative(F₀), y₀))), B₀) ∧ " +
			"snd(inverse_different(L, K, A₀, A₁, B₀, B₁)) = " +
			"image(L.mul(L.inv(polynomial_eval(polynomial_derivative(F₁), y₁))), B₁)",
	},
		"trace_dual.MonogenicCodifferent at S = A₀ and y = y₀: MonicCoverPrimitive makes y₀ a primitive "+
			"element of L over K with separable minimal polynomial F₀, a polynomial over the subring A₀ of "+
			"K (A₀ ⊆ A₀₁ ⊆ K by BiaffineDef and CurveOverLineDef) with B₀ = A₀[y₀] (MonicCoverDef), and y₀ "+
			"is algebraic over K, F₀ being a nonzero polynomial over K vanishing at it (AlgebraicOverDef); "+
			"its first clause is fst of the inverse different (InverseDifferentDef); chart 1 at A₁ and y₁."),
})}

// MonicCoverDifferent — The different on each monic chart is generated by the derivative value.
var MonicCoverDifferent = monicCoverDifferentThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverDifferent",
	Key:  "prop_2a6db2531d0f71e2",
	Deps: []registry.EntryLike{
		MonicCoverPrimitive,
		MonicCoverDef,
		trace_dual.MonogenicCodifferent,
		DifferentDef,
		InverseDifferentDef,
		invertible_lattice_pair.LatticePairInverseDef,
		lattice_pair.BiaffineDef,
		algebraic_element.AlgebraicOverDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
		},
		Conclusion: "fst(cover_different(L, K, A₀, A₁, B₀, B₁)) = " +
			"image(L.mul(polynomial_eval(polynomial_derivative(F₀), y₀)), B₀) ∧ " +
			"snd(cover_different(L, K, A₀, A₁, B₀, B₁)) = " +
			"image(L.mul(polynomial_eval(polynomial_derivative(F₁), y₁)), B₁)",
	},
		"The different is the chartwise fractional inverse of the inverse different (DifferentDef, "+
			"LatticePairInverseDef), and the second clause of trace_dual.MonogenicCodifferent, at A₀ and y₀ "+
			"as in MonicCoverTraceDual (y₀ algebraic over K by AlgebraicOverDef, A₀ ⊆ K by BiaffineDef), is "+
			"that inverse: F₀′(y₀) · B₀; chart 1 at A₁ and y₁. The generators may differ between the charts."),
})}

// MonicCoverInvertible — The inverse different of a monic cover is invertible.
var MonicCoverInvertible = monicCoverInvertibleThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverInvertible",
	Key:  "prop_ad431e66681303a8",
	Deps: []registry.EntryLike{
		MonicCoverIsCover,
		InverseDifferentLattice,
		MonicCoverTraceDual,
		fractional_ideal.InvertibleFractionalDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
		},
		Conclusion: "invertible_lattice_pair(field_ring(L), " +
			"    B₀, " +
			"    B₁, " +
			"    B₀₁, " +
			"    inverse_different(L, K, A₀, A₁, B₀, B₁))",
	},
		"The inverse different is a lattice pair by MonicCoverIsCover and "+
			"InverseDifferentLattice, and both chart modules are nonzero principal fractional ideals."),
})}

// MonicCoverDualizingInvertible — A monic cover carries a base dualizing model to a source dualizing model.
var MonicCoverDualizingInvertible = monicCoverDualizingInvertibleThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverDualizingInvertible",
	Key:  "prop_fe0750e330940dc7",
	Deps: []registry.EntryLike{
		MonicCoverIsCover,
		MonicCoverInvertible,
		DualizingBridge,
		CoverPullbackInvertible,
		invertible_lattice_pair.InvertibleLatticeProduct,
		serre_duality.DualizingInvertibleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
			"dualizing_invertible(restrict_field(L, K), k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "dualizing_invertible(L, k, t, B₀, B₁, B₀₁)",
	},
		"DualizingBridge gives the field-valued model f*N·C; it is invertible "+
			"because both factors are. No invertibility of ω_X is assumed."),
})}

// MonicCoverOverlapDifferent — The two derivative ideals agree after extension to the overlap.
var MonicCoverOverlapDifferent = monicCoverOverlapDifferentThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverOverlapDifferent",
	Key:  "prop_dd975239a3dce30b",
	Deps: []registry.EntryLike{
		MonicCoverTraceDual,
		TraceDualLocalizes,
		fractional_ideal.FractionalInverseDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
		},
		Conclusion: "image(L.mul(polynomial_eval(polynomial_derivative(F₀), y₀)), B₀₁) = " +
			"image(L.mul(polynomial_eval(polynomial_derivative(F₁), y₁)), B₀₁)",
	},
		"Localize the two descriptions of the inverse different and invert "+
			"them on B₀₁. Their derivative generators need only be unit associates."),
})}

// MonicCoverRamificationDegree — Derivative quotient dimensions give the monic-cover ramification degree with the overlap subtracted.
var MonicCoverRamificationDegree = monicCoverRamificationDegreeThm{family.Add(registry.ProofEntry{
	Name: "MonicCoverRamificationDegree",
	Key:  "prop_637d092308f99f16",
	Deps: []registry.EntryLike{
		MonicCoverDualizingInvertible,
		MonicCoverIsCover,
		MonicCoverTraceDual,
		MonicCoverOverlapDifferent,
		RamificationDegreeFormula,
		module_dimension.IsomorphicDim,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
			"dualizing_invertible(restrict_field(L, K), k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "ramification_degree(L, K, k, A₀, A₁, A₀₁, B₀, B₁, B₀₁) = " +
			"int_of_num(module_dim(restrict_ring(field_ring(L), k), " +
			"        quotient_module(restrict_module(regular_module(field_ring(L)), B₀), " +
			"            image(L.mul(polynomial_eval(polynomial_derivative(F₀), y₀)), B₀)))) + " +
			"int_of_num(module_dim(restrict_ring(field_ring(L), k), " +
			"        quotient_module(restrict_module(regular_module(field_ring(L)), B₁), " +
			"            image(L.mul(polynomial_eval(polynomial_derivative(F₁), y₁)), B₁)))) - " +
			"int_of_num(module_dim(restrict_ring(field_ring(L), k), " +
			"        quotient_module(restrict_module(regular_module(field_ring(L)), B₀₁), " +
			"            image(L.mul(polynomial_eval(polynomial_derivative(F₀), y₀)), B₀₁))))",
	},
		"Multiplication by F_i′(y_i) identifies C_i/B_i with B_i/F_i′(y_i)B_i; "+
			"use the same identification on the overlap and RamificationDegreeFormula."),
})}

// DifferentIsKaehlerAnnihilator — The chart different is the annihilator of relative Kähler differentials.
var DifferentIsKaehlerAnnihilator = differentIsKaehlerAnnihilatorThm{family.Add(registry.ProofEntry{
	Name: "DifferentIsKaehlerAnnihilator",
	Key:  "prop_bf71a93cc14e05f9",
	Reading: "The two chart annihilators agree on the overlap, but the local generators dy_i and " +
		"1/F_i′(y_i) have different transition laws. No global torsion-pair isomorphism is asserted.",
	Deps: []registry.EntryLike{
		MonicCoverDifferent,
		MonicCoverDef,
		kaehler.MonicEvaluationPresentation,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀y₀ y₁:A. " +
			"∀F₀ F₁:(num → A).",
		Hypotheses: []string{
			"monic_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁)",
		},
		Conclusion: "{a:A | " +
			"    a ∈ B₀ ∧ " +
			"    (∀v:set(A → A). " +
			"        v ∈ " +
			"        kaehler_module(restrict_ring(field_ring(L), A₀), " +
			"            restrict_ring(field_ring(L), B₀), " +
			"            λa:A. a).carrier ⇒ " +
			"        kaehler_module(restrict_ring(field_ring(L), A₀), " +
			"            restrict_ring(field_ring(L), B₀), " +
			"            λa:A. a).smul(a, v) = " +
			"        kaehler_module(restrict_ring(field_ring(L), A₀), " +
			"            restrict_ring(field_ring(L), B₀), " +
			"            λa:A. a).zero)} = " +
			"fst(cover_different(L, K, A₀, A₁, B₀, B₁)) ∧ " +
			"{a:A | " +
			"    a ∈ B₁ ∧ " +
			"    (∀v:set(A → A). " +
			"        v ∈ " +
			"        kaehler_module(restrict_ring(field_ring(L), A₁), " +
			"            restrict_ring(field_ring(L), B₁), " +
			"            λa:A. a).carrier ⇒ " +
			"        kaehler_module(restrict_ring(field_ring(L), A₁), " +
			"            restrict_ring(field_ring(L), B₁), " +
			"            λa:A. a).smul(a, v) = " +
			"        kaehler_module(restrict_ring(field_ring(L), A₁), " +
			"            restrict_ring(field_ring(L), B₁), " +
			"            λa:A. a).zero)} = " +
			"snd(cover_different(L, K, A₀, A₁, B₀, B₁))",
	},
		"MonicEvaluationPresentation identifies each chart differential module with "+
			"B_i/F_i′(y_i)B_i, by [b]↦b·dy_i. Its annihilator is the derivative ideal, as "+
			"tested at [1]; MonicCoverDifferent identifies it with the different. This is "+
			"chart-local and asserts no gluing of the local C_i/B_i≅Ω identifications."),
})}
