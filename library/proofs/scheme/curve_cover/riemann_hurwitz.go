// riemann_hurwitz.go — the chapter's riemann hurwitz statements.

package curve_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_sequence"
	"github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	"github.com/euc-ai/xugo/library/registry"
)

// RamificationDegreeFormula — The ramification degree is the two chart colengths minus the overlap colength.
var RamificationDegreeFormula = ramificationDegreeFormulaThm{family.Add(registry.ProofEntry{
	Name: "RamificationDegreeFormula",
	Key:  "prop_e011708073bdf3cf",
	Deps: []registry.EntryLike{
		InverseDifferentQuotientFinite,
		InverseDifferentLattice,
		TraceDualContainsStructure,
		algebraic_curve.StructureFinite,
		lattice_pair_sequence.EulerAdditive,
		RamificationDegreeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"riemann_hurwitz_data(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
		},
		Conclusion: "ramification_degree(L, K, k, A₀, A₁, A₀₁, B₀, B₁, B₀₁) = " +
			"int_of_num(module_dim(restrict_ring(field_ring(L), k), " +
			"        quotient_module(restrict_module(regular_module(field_ring(L)), " +
			"                fst(inverse_different(L, K, A₀, A₁, B₀, B₁))), " +
			"            B₀))) + " +
			"int_of_num(module_dim(restrict_ring(field_ring(L), k), " +
			"        quotient_module(restrict_module(regular_module(field_ring(L)), " +
			"                snd(inverse_different(L, K, A₀, A₁, B₀, B₁))), " +
			"            B₁))) - " +
			"int_of_num(module_dim(restrict_ring(field_ring(L), k), " +
			"        quotient_module( " +
			"            restrict_module(regular_module(field_ring(L)), trace_dual(L, K, B₀₁, A₀₁)), B₀₁)))",
	},
		"EulerAdditive applied to O_X⊆C expresses deg C as "+
			"the two chart dimensions minus the overlap dimension."),
})}

// RamificationDegreeNonneg — The ramification degree is nonnegative.
var RamificationDegreeNonneg = ramificationDegreeNonnegThm{family.Add(registry.ProofEntry{
	Name: "RamificationDegreeNonneg",
	Key:  "prop_d83361f84a3e297c",
	Deps: []registry.EntryLike{
		InverseDifferentInvertible,
		TraceDualContainsStructure,
		curve_degree.SectionDegreeNonneg,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"«ccData»",
		},
		Conclusion: "&0 ≤ «ccRamification»",
	},
		"One is a nonzero global section of C since O_X⊆C. "+
			"Apply SectionDegreeNonneg to the invertible pair C."),
})}

// UnramifiedIff — Ramification degree zero is equivalent to a trivial inverse different.
var UnramifiedIff = unramifiedIffThm{family.Add(registry.ProofEntry{
	Name: "UnramifiedIff",
	Key:  "prop_558f64bf4147bcda",
	Deps: []registry.EntryLike{
		InverseDifferentInvertible,
		TraceDualContainsStructure,
		curve_degree.DegreeZeroSectionTrivial,
		curve_degree.DegreeStructure,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"«ccData»",
		},
		Conclusion: "«ccRamification» = &0 ⇔ «ccInverseDifferent» = (B₀, B₁)",
	},
		"At degree zero the global section one trivializes C by "+
			"DegreeZeroSectionTrivial; the reverse follows from DegreeStructure."),
})}

// PullbackDualizingDegree — The pulled-back dualizing degree is the cover degree times twice the base genus minus two.
var PullbackDualizingDegree = pullbackDualizingDegreeThm{family.Add(registry.ProofEntry{
	Name: "PullbackDualizingDegree",
	Key:  "prop_d3941d2d7562ef7b",
	Deps: []registry.EntryLike{
		CoverDegreeMultiplicative,
		serre_duality.DualizingDegree,
		serre_duality.DualizingModelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"riemann_hurwitz_data(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"dualizing_model(restrict_field(L, K), k, t, A₀, A₁, A₀₁, N)",
		},
		Conclusion: "curve_degree(field_ring(L), " +
			"    k, " +
			"    B₀, " +
			"    B₁, " +
			"    B₀₁, " +
			"    cover_pullback(field_ring(L), B₀, B₁, N)) = " +
			"int_of_num(cover_degree(field_ring(L), K)) * " +
			"(&2 * int_of_num(curve_genus(restrict_ring(field_ring(L), K), k, A₀, A₁, A₀₁)) - &2)",
	},
		"Use CoverDegreeMultiplicative on the base model and DualizingDegree on Y."),
})}

// RiemannHurwitz — The canonical degree of the source is the pulled-back canonical degree plus ramification.
var RiemannHurwitz = riemannHurwitzThm{family.Add(registry.ProofEntry{
	Name: "RiemannHurwitz",
	Key:  "prop_1e7d8dd3377732f8",
	Deps: []registry.EntryLike{
		DualizingBridge,
		InverseDifferentInvertible,
		serre_duality.DualizingDegree,
		PullbackDualizingDegree,
		curve_degree.DegreeAdditive,
		curve_degree.DegreeIso,
		lattice_pair_map.IsomorphismCompose,
		lattice_pair_map.IsomorphismInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"riemann_hurwitz_data(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
		},
		Conclusion: "&2 * int_of_num(curve_genus(field_ring(L), k, B₀, B₁, B₀₁)) - &2 = " +
			"int_of_num(cover_degree(field_ring(L), K)) * " +
			"(&2 * int_of_num(curve_genus(restrict_ring(field_ring(L), K), k, A₀, A₁, A₀₁)) - &2) + " +
			"ramification_degree(L, K, k, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
	},
		"DualizingBridge identifies an invertible model of ω_X with f*N·C. DegreeIso and "+
			"DegreeAdditive give deg ω_X=deg(f*N)+deg C; insert the two dualizing degree formulas."),
})}

// RiemannHurwitzInequality — The canonical degree inequality and genus monotonicity follow from nonnegative ramification.
var RiemannHurwitzInequality = riemannHurwitzInequalityThm{family.Add(registry.ProofEntry{
	Name: "RiemannHurwitzInequality",
	Key:  "prop_b0ef68ac1c61fd34",
	Deps: []registry.EntryLike{RiemannHurwitz, RamificationDegreeNonneg, CoverDegreeCharts},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"riemann_hurwitz_data(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
		},
		Conclusion: "int_of_num(cover_degree(field_ring(L), K)) * " +
			"(&2 * int_of_num(curve_genus(restrict_ring(field_ring(L), K), k, A₀, A₁, A₀₁)) - &2) ≤ " +
			"&2 * int_of_num(curve_genus(field_ring(L), k, B₀, B₁, B₀₁)) - &2 ∧ " +
			"(&1 ≤ int_of_num(curve_genus(restrict_ring(field_ring(L), K), k, A₀, A₁, A₀₁)) ⇒ " +
			"    int_of_num(curve_genus(restrict_ring(field_ring(L), K), k, A₀, A₁, A₀₁)) ≤ " +
			"    int_of_num(curve_genus(field_ring(L), k, B₀, B₁, B₀₁)))",
	},
		"RamificationDegreeNonneg gives the first inequality. CoverDegreeCharts "+
			"gives n≥1; if g_Y≥1, integer arithmetic then gives g_X≥g_Y."),
})}

// CoverOfLineUnramifiedTrivial — An unramified cover of a genus-zero base has degree one and genus zero.
var CoverOfLineUnramifiedTrivial = coverOfLineUnramifiedTrivialThm{family.Add(registry.ProofEntry{
	Name: "CoverOfLineUnramifiedTrivial",
	Key:  "prop_153190b943fe5e19",
	Deps: []registry.EntryLike{RiemannHurwitz, CoverDegreeCharts},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"riemann_hurwitz_data(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"int_of_num(curve_genus(restrict_ring(field_ring(L), K), k, A₀, A₁, A₀₁)) = &0",
			"ramification_degree(L, K, k, A₀, A₁, A₀₁, B₀, B₁, B₀₁) = &0",
		},
		Conclusion: "cover_degree(field_ring(L), K) = 1 ∧ " +
			"int_of_num(curve_genus(field_ring(L), k, B₀, B₁, B₀₁)) = &0",
	},
		"RiemannHurwitz gives g_X=1−n. Nonnegative genus and positive cover degree force n=1 and g_X=0."),
})}
