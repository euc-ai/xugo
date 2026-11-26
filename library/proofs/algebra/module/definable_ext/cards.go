package definable_ext

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

// CanonicalResolutionCountable — Induct on the canonical resolution: the initial generators are the module carrier, and each later kernel is a subset of a countable finitely supported free module.
var CanonicalResolutionCountable = canonicalResolutionCountableThm{family.Add(registry.ProofEntry{
	Name: "CanonicalResolutionCountable",
	Key:  "prop_c5336f101b4a1e0f",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"module_on(R, M)",
			"countable(R.carrier)",
			"countable(M.carrier)",
		},
		Conclusion: "countable(canonical_resolution_terms(R, M, n))",
	},
		"Induct on the canonical resolution: the initial generators are the module carrier, "+
			"and each later kernel is a subset of a countable finitely supported free module."),
	Deps: []registry.EntryLike{resolution.CanonicalResolution},
})}

// ExtPolishModel — The coordinate carrier consists of generator functions normalized to zero off each generator set. Countability and finite generator expansions supply the Polish topology and continuity.
var ExtPolishModel = extPolishModelThm{family.Add(registry.ProofEntry{
	Name: "ExtPolishModel",
	Key:  "prop_e63b9fc3f3afe98f",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"comm_ring(R)",
			"module_on(R, M)",
			"module_on(R, N)",
			"countable(R.carrier)",
			"countable(M.carrier)",
			"countable(N.carrier)",
		},
		Conclusion: "polish_cochain_complex(R, canonical_hom_complex(R, M, N), ext_topologies(R, M, N))",
	},
		"Apply the countable based-dual construction to the canonical "+
			"free resolution, identifying its dual with canonical_hom_complex."),
	Deps: []registry.EntryLike{
		CanonicalResolutionCountable,
		polish_cohomology.CountableBasedDualPolish,
	},
	Reading: "The coordinate carrier consists of generator functions " +
		"normalized to zero off each generator set. Countability and finite " +
		"generator expansions supply the Polish topology and continuity.",
})}

// ExtHasPolishCover — CohomologyHasPolishCover supplies the structure and the definition of ext identifies the existing quotient carrier.
var ExtHasPolishCover = extHasPolishCoverThm{family.Add(registry.ProofEntry{
	Name: "ExtHasPolishCover",
	Key:  "prop_4ec0aad514eb2aff",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"module_on(R, M)",
			"module_on(R, N)",
			"countable(R.carrier)",
			"countable(M.carrier)",
			"countable(N.carrier)",
		},
		Conclusion: "cohomology_cover(canonical_hom_complex(R, M, N), ext_topologies(R, M, N), n) ∧ " +
			"ext(R, M, N, n) = cohomology(canonical_hom_complex(R, M, N), n)",
	},
		"CohomologyHasPolishCover supplies the structure and the "+
			"definition of ext identifies the existing quotient carrier."),
	Deps: []registry.EntryLike{ExtPolishModel, polish_cohomology.CohomologyHasPolishCover},
})}

// ExtResolutionComparison — Lift the identity of M in both directions between the free resolutions
var ExtResolutionComparison = extResolutionComparisonThm{family.Add(registry.ProofEntry{
	Name: "ExtResolutionComparison",
	Key:  "prop_224e4477d2ea6301",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀eps:((I → A) → B). " +
			"∀S₂:(num → set(D)). " +
			"∀d₂:(num → (D → A) → D → A). " +
			"∀eps₂:((D → A) → B).",
		Hypotheses: []string{
			"comm_ring(R)",
			"free_resolution(R, M, S, d, eps)",
			"free_resolution(R, M, S₂, d₂, eps₂)",
			"module_on(R, N)",
			"countable(N.carrier)",
			"∀n:num. countable(S(n)) ∧ countable(S₂(n))",
		},
		Conclusion: "∃f:(num → (D → C) → I → C). ∃g:(num → (I → C) → D → C). " +
			"    polish_cochain_map(R, " +
			"        hom_complex(R, S₂, d₂, N), " +
			"        dual_pointwise_topologies(N, S₂), " +
			"        hom_complex(R, S, d, N), " +
			"        dual_pointwise_topologies(N, S), " +
			"        f) ∧ " +
			"    polish_cochain_map(R, " +
			"        hom_complex(R, S, d, N), " +
			"        dual_pointwise_topologies(N, S), " +
			"        hom_complex(R, S₂, d₂, N), " +
			"        dual_pointwise_topologies(N, S₂), " +
			"        g) ∧ " +
			"    cochain_homotopy_equivalence(R, hom_complex(R, S₂, d₂, N), hom_complex(R, S, d, N), f, g)",
	},
		"Lift the identity of M in both directions between the free resolutions. "+
			"Their composites are chain homotopic to the identities; transpose the "+
			"maps and homotopies, with continuity supplied by BasedDualMapContinuous."),
	Deps: []registry.EntryLike{
		free_complex_duality.FreeDualCochainMap,
		polish_cohomology.BasedDualMapContinuous,
	},
})}

// ExtResolutionDefinableIso — Any two countable free resolutions give Borel-isomorphic Ext covers through one continuous comparison.
var ExtResolutionDefinableIso = extResolutionDefinableIsoThm{family.Add(registry.ProofEntry{
	Name: "ExtResolutionDefinableIso",
	Key:  "prop_d6f90ba718ab663d",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀eps:((I → A) → B). " +
			"∀S₂:(num → set(D)). " +
			"∀d₂:(num → (D → A) → D → A). " +
			"∀eps₂:((D → A) → B).",
		Hypotheses: []string{
			"comm_ring(R)",
			"free_resolution(R, M, S, d, eps)",
			"free_resolution(R, M, S₂, d₂, eps₂)",
			"module_on(R, N)",
			"countable(N.carrier)",
			"∀k:num. countable(S(k)) ∧ countable(S₂(k))",
		},
		Conclusion: "∃f:(num → (D → C) → I → C). " +
			"    polish_cochain_map(R, " +
			"        hom_complex(R, S₂, d₂, N), " +
			"        dual_pointwise_topologies(N, S₂), " +
			"        hom_complex(R, S, d, N), " +
			"        dual_pointwise_topologies(N, S), " +
			"        f) ∧ " +
			"    (∀n:num. " +
			"        cohomology_borel_iso(hom_complex(R, S₂, d₂, N), " +
			"            dual_pointwise_topologies(N, S₂), " +
			"            n, " +
			"            hom_complex(R, S, d, N), " +
			"            dual_pointwise_topologies(N, S), " +
			"            n, " +
			"            cohomology_map(hom_complex(R, S, d, N), f, n)))",
	},
		"ExtResolutionComparison supplies a continuous comparison, a continuous map back "+
			"and a cochain homotopy equivalence between them; HomotopyEquivalenceDefinableIso "+
			"inverts the induced cohomology map with a Borel lift in every degree."),
	Deps: []registry.EntryLike{
		ExtResolutionComparison,
		polish_cohomology.HomotopyEquivalenceDefinableIso,
	},
	Reading: "The two resolutions may have different generator types. The comparison " +
		"transposes a lift of the identity of M, so by HomotopicSameCohomologyMap every " +
		"such lift induces the same isomorphism of covers.",
})}

// ExtCoefficientMapDefinable — The coefficient map of Ext uses singleton-coordinate continuity and the common cohomology functor.
var ExtCoefficientMapDefinable = extCoefficientMapDefinableThm{family.Add(registry.ProofEntry{
	Name: "ExtCoefficientMapDefinable",
	Key:  "prop_4b2d62b73060238",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀f:(C → D). " +
			"∀n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"module_on(R, M)",
			"module_homomorphism(R, N, L, f)",
			"countable(R.carrier)",
			"countable(M.carrier)",
			"countable(N.carrier)",
			"countable(L.carrier)",
		},
		Conclusion: "cohomology_borel_map(canonical_hom_complex(R, M, N), " +
			"    ext_topologies(R, M, N), " +
			"    n, " +
			"    canonical_hom_complex(R, M, L), " +
			"    ext_topologies(R, M, L), " +
			"    n, " +
			"    ext_map(R, M, L, f, n))",
	},
		"Coefficient postcomposition preserves the canonical Hom carriers and is a cochain "+
			"map. Every output reads one input coordinate, so FiniteCoordinateContinuous "+
			"supplies continuity; apply CohomologyDefinableFunctor to the existing ext_map."),
	Deps: []registry.EntryLike{
		ExtPolishModel,
		polish_space.FiniteCoordinateContinuous,
		polish_cohomology.CohomologyDefinableFunctor,
	},
	Reading: "Coefficient postcomposition preserves the inactive " +
		"coordinates because a module homomorphism preserves zero.",
})}

// ExtFirstVariableMapDefinable — The canonical chain comparison transposes to a continuous map of the Hom complexes, contravariantly in the first module
var ExtFirstVariableMapDefinable = extFirstVariableMapDefinableThm{family.Add(registry.ProofEntry{
	Name: "ExtFirstVariableMapDefinable",
	Key:  "prop_42871db910474420",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀L:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀N:module_ops(A, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"module_homomorphism(R, M, L, f)",
			"module_on(R, N)",
			"countable(R.carrier)",
			"countable(M.carrier)",
			"countable(L.carrier)",
			"countable(N.carrier)",
		},
		Conclusion: "cohomology_borel_map(canonical_hom_complex(R, L, N), " +
			"    ext_topologies(R, L, N), " +
			"    n, " +
			"    canonical_hom_complex(R, M, N), " +
			"    ext_topologies(R, M, N), " +
			"    n, " +
			"    ext_map_left(R, M, L, f, N, n))",
	},
		"The canonical chain comparison transposes to a continuous map "+
			"of the Hom complexes, contravariantly in the first module. "+
			"Apply CohomologyDefinableFunctor to the existing ext_map_left."),
	Deps: []registry.EntryLike{
		CanonicalResolutionCountable,
		polish_cohomology.BasedDualMapContinuous,
		polish_cohomology.CohomologyDefinableFunctor,
	},
})}

// ExtCountableOrContinuum — Ext of countable modules over a countable ring is countable or has at least continuum many elements.
var ExtCountableOrContinuum = extCountableOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "ExtCountableOrContinuum",
	Key:  "prop_c45eb7a3e21907d1",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"module_on(R, M)",
			"module_on(R, N)",
			"countable(R.carrier)",
			"countable(M.carrier)",
			"countable(N.carrier)",
		},
		Conclusion: "countable(ext(R, M, N, n)) ∨ card_le(𝕌⟨A:set(num)⟩, ext(R, M, N, n))",
	},
		"ExtHasPolishCover identifies ext with the cohomology of the canonical "+
			"Polish model of ExtPolishModel; CohomologyCountableOrContinuum decides."),
	Deps: []registry.EntryLike{
		ExtPolishModel,
		ExtHasPolishCover,
		polish_cohomology.CohomologyCountableOrContinuum,
	},
	Reading: "A countable Ext is finitely or countably generated as a " +
		"module over the countable ring; an uncountable one has the size " +
		"of the continuum at least, and its coboundaries are not closed.",
})}
