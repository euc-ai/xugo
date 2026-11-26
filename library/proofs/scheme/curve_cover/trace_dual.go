// trace_dual.go — the chapter's trace dual statements: the inverse
// different of a cover, read as instances of algebra/field/trace_dual at
// the cover's chart rings.

package curve_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/trace_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// TraceDualSubmodule — The trace dual is a module under the source chart ring.
var TraceDualSubmodule = traceDualSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "TraceDualSubmodule",
	Key:  "prop_175ad6bcebba7f40",
	Reading: "The cover supplies what the general statement asks beyond this one's " +
		"hypotheses: K is a subfield of L and L is finite over K, by the cover's field basis.",
	Deps: []registry.EntryLike{
		trace_dual.TraceDualSubmodule,
		CurveCoverDef,
		field_extension.FiniteExtensionDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁ S B N:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"S ⊆ K",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"submodule(restrict_ring(field_ring(L), S), restrict_module(regular_module(field_ring(L)), K), N)",
		},
		Conclusion: "submodule(restrict_ring(field_ring(L), B), " +
			"    regular_module(field_ring(L)), " +
			"    trace_dual(L, K, B, N))",
	},
		"trace_dual.TraceDualSubmodule at the cover: subfield(L, K) and the finite "+
			"basis of L over K are clauses of CurveCoverDef, so L is a finite extension "+
			"of K (FiniteExtensionDef); the remaining hypotheses are this statement's."),
})}

// TraceDualContainsStructure — The inverse different contains the structure rings on both charts and their overlap.
var TraceDualContainsStructure = traceDualContainsStructureThm{family.Add(registry.ProofEntry{
	Name: "TraceDualContainsStructure",
	Key:  "prop_181025f2f2492290",
	Deps: []registry.EntryLike{field_trace.FieldTraceInSubring, CurveCoverDef, CoverOverlapBasis},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"«ccCover»",
		},
		Conclusion: "B₀ ⊆ fst(«ccInverseDifferent») ∧ " +
			"B₁ ⊆ snd(«ccInverseDifferent») ∧ " +
			"B₀₁ ⊆ trace_dual(L, K, B₀₁, A₀₁)",
		Abbrev: Abbrev{
			{Name: "ccCover", Text: "curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)"},
		},
	},
		"For z,b in B_i their product is in B_i, and its trace belongs to A_i by the "+
			"common chart and field basis. Use CoverOverlapBasis on the intersection."),
})}

// TraceDualHomIso — Trace pairing identifies a chart trace dual with its coextension Hom module.
var TraceDualHomIso = traceDualHomIsoThm{family.Add(registry.ProofEntry{
	Name: "TraceDualHomIso",
	Key:  "prop_4b2908f32e956c7a",
	Reading: "The isomorphism is B-linear for the precomposition action, not the " +
		"pointwise A-action of hom_module. Its function value is zero off B; without that " +
		"guard it is not in hom_set. The general statement asks the trace pairing of L " +
		"over K to be nondegenerate, which the cover's separable primitive element supplies.",
	Deps: []registry.EntryLike{
		trace_dual.TraceDualHomIso,
		CurveCoverDef,
		field_extension.FiniteExtensionDef,
		field_trace.TraceNondegenerate,
		hom_module.CoextendScalarsDef,
		TraceDualSubmodule,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁ S B E N:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"S ⊆ K",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"finite(E)",
			"module_basis(restrict_ring(field_ring(L), S), " +
				"    restrict_module(regular_module(field_ring(L)), B), " +
				"    E)",
			"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
			"submodule(restrict_ring(field_ring(L), S), restrict_module(regular_module(field_ring(L)), K), N)",
		},
		Conclusion: "module_isomorphism(restrict_ring(field_ring(L), B), " +
			"    restrict_module(regular_module(field_ring(L)), trace_dual(L, K, B, N)), " +
			"    coextend_scalars(restrict_ring(field_ring(L), S), " +
			"        restrict_ring(field_ring(L), B), " +
			"        λa:A. a, " +
			"        restrict_module(regular_module(field_ring(L)), N)), " +
			"    λz:A. " +
			"        COND(z ∈ trace_dual(L, K, B, N), " +
			"            λb:A. COND(b ∈ B, field_trace(L, K, z * b), L.zero), " +
			"            λb:A. L.zero))",
	},
		"trace_dual.TraceDualHomIso at the cover: L is a finite extension of K (CurveCoverDef, "+
			"FiniteExtensionDef), and the trace pairing is nondegenerate — L = K(y) for a "+
			"separable y by the cover's last clause, so a nonzero x has Tr(x · yʲ) ≠ zero for some "+
			"j (TraceNondegenerate); its map agrees with the displayed one on the trace dual, "+
			"where module_isomorphism reads it, the outer guard supplying the values off it."),
})}

// TraceDualLocalizes — Both chart trace duals extend to the same overlap trace dual.
var TraceDualLocalizes = traceDualLocalizesThm{family.Add(registry.ProofEntry{
	Name: "TraceDualLocalizes",
	Key:  "prop_9391f8791a0629ff",
	Reading: "Localizing the test module and the value module at t, or at " +
		"1/t, localizes the trace dual: the overlap trace dual is the chart trace " +
		"dual with denominators allowed. No nondegeneracy and no dual basis enter.",
	Deps: []registry.EntryLike{
		trace_dual.TraceDualLocalizes,
		CurveCoverDef,
		field_extension.FiniteExtensionDef,
		algebraic_curve.CurveOverLineDef,
		lattice_pair.BiaffineDef,
		ring_away.RingAwayDef,
		principal_ideal_domain.FinitelyGeneratedDef,
		TraceDualSubmodule,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
		},
		Conclusion: "trace_dual(L, K, B₀₁, A₀₁) = " +
			"module_span(restrict_ring(field_ring(L), B₀₁), " +
			"    regular_module(field_ring(L)), " +
			"    fst(inverse_different(L, K, A₀, A₁, B₀, B₁))) ∧ " +
			"trace_dual(L, K, B₀₁, A₀₁) = " +
			"module_span(restrict_ring(field_ring(L), B₀₁), " +
			"    regular_module(field_ring(L)), " +
			"    snd(inverse_different(L, K, A₀, A₁, B₀, B₁)))",
	},
		"trace_dual.TraceDualLocalizes at S = A₀, X = B₀, N = A₀ and s = t: L is a finite extension "+
			"of K by the cover's field basis (CurveCoverDef, FiniteExtensionDef), B₀ is finitely "+
			"generated over A₀ by the cover's basis E₀ (FinitelyGeneratedDef), and both curves' "+
			"overlaps are their charts localized at t (CurveOverLineDef, BiaffineDef, RingAwayDef) — "+
			"ring_away(…, A₀, t) computed in L is A₀₁, as a member r of L with tⁿ · r ∈ A₀ is inv(t)ⁿ · "+
			"(tⁿ · r) ∈ A₀₁ — so the spans of B₀ and of A₀ over ring_away(…, A₀, t) are B₀₁ and A₀₁; "+
			"the same span of the B₀-module trace_dual(L, K, B₀, A₀) (TraceDualSubmodule) is its "+
			"B₀₁-span, B₀₁ being B₀ · A₀₁; chart 1 at S = A₁, X = B₁, N = A₁ and s = inv(t)."),
})}

// InverseDifferentLattice — The inverse different is a lattice pair with the overlap trace dual as ambient.
var InverseDifferentLattice = inverseDifferentLatticeThm{family.Add(registry.ProofEntry{
	Name: "InverseDifferentLattice",
	Key:  "prop_10a6d7ffac552139",
	Deps: []registry.EntryLike{TraceDualSubmodule, TraceDualLocalizes, lattice_pair.LatticePairDef},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
		},
		Conclusion: "lattice_pair(restrict_ring(field_ring(L), B₀₁), " +
			"    B₀, " +
			"    B₁, " +
			"    regular_module(field_ring(L)), " +
			"    inverse_different(L, K, A₀, A₁, B₀, B₁)) ∧ " +
			"lattice_pair_ambient(restrict_ring(field_ring(L), B₀₁), " +
			"    regular_module(field_ring(L)), " +
			"    inverse_different(L, K, A₀, A₁, B₀, B₁)) = " +
			"trace_dual(L, K, B₀₁, A₀₁)",
	},
		"TraceDualSubmodule supplies the chart modules, and "+
			"TraceDualLocalizes gives their common overlap span."),
})}

// TraceDualOfInvertible — The trace dual of an invertible base module is its product with the inverse different.
var TraceDualOfInvertible = traceDualOfInvertibleThm{family.Add(registry.ProofEntry{
	Name: "TraceDualOfInvertible",
	Key:  "prop_c9eead56dfb2e722",
	Deps: []registry.EntryLike{
		trace_dual.TraceDualValueInvertible,
		CurveCoverDef,
		field_extension.FiniteExtensionDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁ S B N:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"S ⊆ K",
			"S ⊆ B",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"invertible_fractional(restrict_ring(field_ring(L), K), S, N)",
		},
		Conclusion: "trace_dual(L, K, B, N) = fractional_mul(field_ring(L), B, N, trace_dual(L, K, B, S))",
	},
		"trace_dual.TraceDualValueInvertible at the cover, L a finite extension "+
			"of K by the cover's field basis (CurveCoverDef, FiniteExtensionDef)."),
})}
