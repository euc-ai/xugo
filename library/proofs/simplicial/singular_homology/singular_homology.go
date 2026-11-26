// singular_homology.go — singular homology: the singular chains form a
// chain complex and a continuous map a chain map; homotopic maps are chain
// homotopic, by the prism, so a homotopy equivalence induces isomorphisms
// in homology and a contractible space is acyclic; a path-connected space
// has the ring for its homology in degree 0; chains of simplices small
// with respect to an open cover compute the same homology; and the
// Mayer–Vietoris sequence of two open sets, in the range where the two sets
// are acyclic, identifies the homology of the union one degree up with
// that of the intersection.

package singular_homology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_chain"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_set"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	"github.com/euc-ai/xugo/library/proofs/topology/path_connected"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_simplex"
	"github.com/euc-ai/xugo/library/registry"
)

// SingularChainComplex — the singular chains form a chain complex.
var SingularChainComplex = singularChainComplexThm{family.Add(registry.ProofEntry{
	Name: "SingularChainComplex",
	Key:  "prop_20d4d7d1c300c330",
	Reading: "Needs comm_ring_on(R) — the zero ring makes " +
		"every term {0} — and SingularSimplicialSet; T is arbitrary.",
	Deps: []registry.EntryLike{
		SingularComplexDef,
		simplicial_module.SimplicialChainsFreeComplex,
		singular_set.SingularSimplicialSet,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(set(D)).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "chain_complex(R, singular_complex(R, T))",
	},
		"SimplicialChainsFreeComplex at the singular simplicial "+
			"set, a simplicial set by SingularSimplicialSet"),
})}

// SingularChainMap — a continuous map induces a chain map of singular
// chains.
var SingularChainMap = singularChainMapThm{family.Add(registry.ProofEntry{
	Name: "SingularChainMap",
	Key:  "prop_1c43505c022538c4",
	Reading: "Continuity of f makes singular_map(f, n) carry singular " +
		"simplices to singular simplices, so the pushforward lands in the terms; " +
		"commuting with the boundary is SingularMapSimplicial's face clause.",
	Deps: []registry.EntryLike{
		SingularComplexDef,
		singular_set.SingularMapSimplicial,
		simplicial_chain.ChainMapOfSimplicialMap,
		free_module.FreePushforwardDef,
		free_module.FreePushforwardHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(set(D)). ∀S:set(set(E)). ∀f:(D → E).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"continuous_map(T, S, f)",
		},
		Conclusion: "chain_map(R, " +
			"    singular_complex(R, T), " +
			"    singular_complex(R, S), " +
			"    λn:num. free_pushforward(R, singular_map(f, n)))",
	},
		"the pushforward of a simplicial map is a chain map of the free chains (ChainMapOfSimplicialMap, "+
			"read through FreePushforwardDef), here at the simplicial map f induces (SingularMapSimplicial)"),
})}

// SingularHomotopyChainHomotopy — homotopic maps induce chain homotopic
// chain maps.
var SingularHomotopyChainHomotopy = singularHomotopyChainHomotopyThm{family.Add(registry.ProofEntry{
	Name: "SingularHomotopyChainHomotopy",
	Key:  "prop_e80fcd2296b678db",
	Reading: "homotopic_rel alone is enough, f and g need not be continuous " +
		"on a family that is not a topology: f ∘ σ is the homotopy after σ " +
		"paired with 0, continuous on Δⁿ. The sign of h is free under the ∃.",
	Deps: []registry.EntryLike{
		SingularComplexDef,
		homotopy.HomotopicRelDef,
		chain_complex.ChainHomotopyDef,
		free_module.FreePushforwardHom,
		euclidean_simplex.CofaceContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(set(D)). ∀S:set(set(E)). ∀f g:(D → E).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homotopic_rel(T, S, ∅, f, g)",
		},
		Conclusion: "∃h:(num → (((num → real) → D) → A) → ((num → real) → E) → A). " +
			"    chain_homotopy(R, " +
			"        singular_complex(R, T), " +
			"        singular_complex(R, S), " +
			"        λn:num. free_pushforward(R, singular_map(f, n)), " +
			"        λn:num. free_pushforward(R, singular_map(g, n)), " +
			"        h)",
	},
		"the prism: Δⁿ × ⟦0, 1⟧ is cut into the n + 1 simplices [v₀ … vᵢ wᵢ … wₙ], and h sends a "+
			"singular simplex σ to the alternating sum of the homotopy after σ × identity after each "+
			"of their affine parametrizations; ∂h + h∂ is the difference of the two ends, the interior "+
			"faces cancelling in pairs. Equivalently, the homotopy gives a simplicial homotopy of the "+
			"singular simplicial sets, and simplicial_module.SimplicialHomotopyChainHomotopy applies"),
})}

// HomotopyEquivalenceHomology — a homotopy equivalence induces an
// isomorphism of singular homology in every degree.
var HomotopyEquivalenceHomology = homotopyEquivalenceHomologyThm{family.Add(registry.ProofEntry{
	Name: "HomotopyEquivalenceHomology",
	Key:  "prop_9359f7158400d469",
	Reading: "The continuity of f and g inside homotopy_equivalence " +
		"supplies the two chain maps. Every degree, 0 included.",
	Deps: []registry.EntryLike{
		SingularHomotopyChainHomotopy,
		SingularChainMap,
		homotopy.HomotopyEquivalenceDef,
		singular_set.SingularMapCompose,
		singular_set.SingularMapIdentity,
		free_module.FreePushforwardCompose,
		free_module.FreePushforwardIdentity,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.QuasiIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(set(D)). ∀S:set(set(E)). ∀f:(D → E). ∀g:(E → D). ∀n:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"homotopy_equivalence(T, S, f, g)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    homology_module(singular_complex(R, T), n), " +
			"    homology_module(singular_complex(R, S), n), " +
			"    homology_map(singular_complex(R, S), λk:num. free_pushforward(R, singular_map(f, k)), n))",
	},
		"the chain maps of f and g compose to the chain maps of the composites (SingularMapCompose, "+
			"FreePushforwardCompose), and the identity's is the identity on chains "+
			"(SingularMapIdentity, FreePushforwardIdentity); the two homotopies to the identities are "+
			"chain homotopies (SingularHomotopyChainHomotopy), so f's chain map is a chain homotopy "+
			"equivalence and a quasi-isomorphism (ChainHomotopyEquivalenceQuasiIsomorphism)"),
})}

// ContractibleAcyclic — a contractible space has no homology above degree
// 0.
var ContractibleAcyclic = contractibleAcyclicThm{family.Add(registry.ProofEntry{
	Name: "ContractibleAcyclic",
	Key:  "prop_23463ec8958de774",
	Reading: "Only the degrees n + 1 ≥ 1 are claimed, H₀ being R. The empty " +
		"space is not contractible. T need not be a topology, which is why the " +
		"route does not pass through a homotopy equivalence with a point.",
	Deps: []registry.EntryLike{
		SingularHomotopyChainHomotopy,
		singular_set.SingularMapIdentity,
		homotopy.ContractibleSpaceDef,
		chain_complex.ChainHomotopyDef,
		simplicial_chain.BoundaryDelta,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(set(D)). ∀n:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"contractible_space(T)",
		},
		Conclusion: "cycles(singular_complex(R, T), n + 1) = boundaries(singular_complex(R, T), n + 1)",
	},
		"the contraction itself gives a chain homotopy from the identity's chain map, the identity on "+
			"chains (SingularMapIdentity), to the constant map's (SingularHomotopyChainHomotopy, which "+
			"reads no continuity of the two ends; the space need not be a topology, so no homotopy "+
			"equivalence with a point is available). For a cycle z of degree m = n + 1, z differs by a "+
			"boundary from its image, ε(z) κₘ, ε the sum of coefficients and κₘ the constant m-simplex at "+
			"the point. ∂κₘ is κₘ₋₁ for m even and 0 for m odd (BoundaryDelta, AlternatingSignDef): for m "+
			"even ε(z) κₘ is a cycle only when ε(z) = 0, and for m odd it is the boundary of ε(z) κₘ₊₁"),
})}

// PathConnectedZerothHomology — a nonempty path-connected space has the
// ring for its homology in degree 0.
var PathConnectedZerothHomology = pathConnectedZerothHomologyThm{family.Add(registry.ProofEntry{
	Name: "PathConnectedZerothHomology",
	Key:  "prop_8ef4e28ccbae9bea",
	Reading: "x ∈ ⋃T is load-bearing: the empty space is path-connected and " +
		"its H₀ is 0, not R for a nonzero ring. For the zero ring both sides are 0.",
	Deps: []registry.EntryLike{
		SingularChainComplex,
		singular_set.SingularVertex,
		path_connected.PathConnectedInDef,
		chain_complex.HomologyModuleDef,
		module_record.RegularModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(set(D)). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"path_connected_in(T, ⋃T)",
			"x ∈ ⋃T",
		},
		Conclusion: "module_isomorphic(R, homology_module(singular_complex(R, T), 0), regular_module(R))",
	},
		"the augmentation, the sum of a 0-chain's coefficients, is onto R and kills "+
			"the boundaries, the boundary of an edge being the difference of its two "+
			"ends; a 0-chain with coefficient sum 0 is a boundary, each vertex being "+
			"joined to the vertex of x by a path, a singular 1-simplex (SingularVertex)"),
})}

// SmallChainsQuasiIsomorphism — the chains of simplices each inside a
// member of an open cover compute the singular homology.
var SmallChainsQuasiIsomorphism = smallChainsQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SmallChainsQuasiIsomorphism",
	Key:  "prop_3efd857e94fb25f8",
	Reading: "c ⊆ T makes the members open, so they pull back to an open cover " +
		"of Δⁿ with a Lebesgue number; ⋃T ⊆ ⋃c makes every vertex small, so the " +
		"0-chains agree. c = ∅ forces the empty space, where both complexes are 0.",
	Deps: []registry.EntryLike{
		SingularChainComplex,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.ChainHomotopyDef,
		complete_metric.LebesgueNumber,
		euclidean_simplex.SimplexCompact,
		euclidean_simplex.SimplexConvex,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(set(D)). ∀c:set(set(D)).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"c ⊆ T",
			"⋃T ⊆ ⋃c",
		},
		Conclusion: "quasi_isomorphism(R, " +
			"    free_complex(R, " +
			"        λn:num. " +
			"            {σ:((num → real) → D) | " +
			"                σ ∈ singular_simplices(T, n) ∧ " +
			"                ∃u:set(D). u ∈ c ∧ image(σ, euclidean_simplex(n)) ⊆ u}, " +
			"        simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, singular_set(T).d)), " +
			"    singular_complex(R, T), " +
			"    λn:num. λz:(((num → real) → D) → A). z)",
	},
		"barycentric subdivision S, a chain map on singular chains chain homotopic to the identity by "+
			"a homotopy T with ∂T + T∂ = 1 − S, both natural and keeping small chains small; the simplices "+
			"of the m-th subdivision of a singular simplex σ have diameter in Δⁿ at most (n/(n + 1))^m, so "+
			"for m beyond a Lebesgue number of the cover of Δⁿ by the preimages of c (LebesgueNumber, "+
			"SimplexCompact) each lies in one member. A cycle is then homologous to a small cycle, and a "+
			"small cycle bounding a chain bounds a small chain, so inclusion is bijective in homology"),
})}

// MayerVietorisDiagonal — for two open sets that cover the space and have
// no homology in degrees n + 1 and n + 2, the homology of the space in
// degree n + 2 is that of the intersection in degree n + 1.
var MayerVietorisDiagonal = mayerVietorisDiagonalThm{family.Add(registry.ProofEntry{
	Name: "MayerVietorisDiagonal",
	Key:  "prop_5741fba913999f0b",
	Reading: "u, v ∈ T let the small-chains theorem apply with c = {u, v}; the vanishing " +
		"in degrees n + 1 and n + 2 sits on both sides of the connecting map. If u ∩ v = ∅ " +
		"it says H_(n+2) of the space is 0, as for any disjoint union of acyclic pieces.",
	Deps: []registry.EntryLike{
		SmallChainsQuasiIsomorphism,
		singular_set.SubspaceSingularSimplices,
		chain_complex.ShortExactComplexes,
		chain_complex.LongExactMiddle,
		chain_complex.LongExactQuotient,
		chain_complex.LongExactSub,
		chain_complex.ConnectingHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(set(D)). ∀u v:set(D). ∀n:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"u ∈ T",
			"v ∈ T",
			"⋃T ⊆ u ∪ v",
			"cycles(singular_complex(R, subtopology(T, u)), n + 1) = " +
				"boundaries(singular_complex(R, subtopology(T, u)), n + 1)",
			"cycles(singular_complex(R, subtopology(T, u)), n + 2) = " +
				"boundaries(singular_complex(R, subtopology(T, u)), n + 2)",
			"cycles(singular_complex(R, subtopology(T, v)), n + 1) = " +
				"boundaries(singular_complex(R, subtopology(T, v)), n + 1)",
			"cycles(singular_complex(R, subtopology(T, v)), n + 2) = " +
				"boundaries(singular_complex(R, subtopology(T, v)), n + 2)",
		},
		Conclusion: "module_isomorphic(R, " +
			"    homology_module(singular_complex(R, T), n + 2), " +
			"    homology_module(singular_complex(R, subtopology(T, u ∩ v)), n + 1))",
	},
		"the chains of u ∩ v go into the chains of u and of v by z ↦ (z, −z), and the pair to "+
			"the chains of simplices small for the cover {u, v} by the sum: a short exact sequence "+
			"of complexes, the singular simplices of a subspace being those of the space with "+
			"image in it (SubspaceSingularSimplices). Its long exact sequence (LongExactMiddle, "+
			"LongExactQuotient, LongExactSub), with the small chains' homology the space's "+
			"(SmallChainsQuasiIsomorphism), makes the connecting map from degree n + 2 to degree n "+
			"+ 1 an isomorphism, the terms on either side being the vanishing homology of u and v"),
})}
