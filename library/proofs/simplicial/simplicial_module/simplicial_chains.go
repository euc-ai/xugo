// simplicial_chains.go — the free chains on a simplicial set as a
// simplicial module: the chains over a commutative ring on a set, with
// the pushforwards of the faces and degeneracies, form a simplicial
// module whose face complex is the alternating face map complex of
// simplicial_chain; so a simplicial homotopy gives a chain homotopy of
// the chains, a simplicial homotopy equivalence a chain homotopy
// equivalence, and the chains on a constant simplicial set have their
// homology in degree 0.
//
// The chains over the ring R are `free_complex(R, X.simplices,
// simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d))`, the free
// complex of the resolution chapter on the simplices; a map F of
// simplices acts on them by its pushforward `free_pushforward(R, F(n))`.

package simplicial_module

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_chain"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The free chains as a simplicial module
// ---------------------------------------------------------------------------

// FreeChainsSimplicialModule — the chains on a simplicial set, a
// submodule of the free module on the whole type in each dimension, with
// the pushforwards of the faces and degeneracies, are a simplicial
// module.
var FreeChainsSimplicialModule = freeChainsSimplicialModuleThm{family.Add(registry.ProofEntry{
	Name: "FreeChainsSimplicialModule",
	Key:  "prop_f3d43bfecd7bb7e3",
	Deps: []registry.EntryLike{
		SimplicialModule,
		simplicial_chain.SimplicialChainsDef,
		free_module.FreeModuleOn,
		free_module.FreeModuleRecordDef,
		free_module.FreePushforwardDef,
		free_module.FreePushforwardHom,
		free_module.FreePushforwardCompose,
		free_module.FreePushforwardIdentity,
		free_module.FreeLiftUnique,
		simplicial_set.SimplicialSet,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀X:simplicial_ops(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"simplicial_set(X)",
		},
		Conclusion: "simplicial_module(R, free_module_record(R, 𝕌), free_simplicial_module(R, X))",
	},
		"the free module on X(n) is a submodule of the free module on the whole type "+
			"(FreeModuleOn, FreeModuleRecordDef); the pushforward of a map carrying X(n) into X(m) is "+
			"a homomorphism of the chains (FreePushforwardHom), functorial (FreePushforwardCompose, "+
			"FreePushforwardIdentity) and determined by the map on X(n) (FreeLiftUnique), so each "+
			"simplicial identity of X is the same identity of the pushforwards on the chains"),
})}

// SimplicialChainsFaceComplex — on every chain, the boundary of the
// alternating face map complex is the face boundary of the free
// simplicial module: Σ_{i ≤ n} (−1)^i times the pushforward of d_i.
var SimplicialChainsFaceComplex = simplicialChainsFaceComplexThm{family.Add(registry.ProofEntry{
	Name: "SimplicialChainsFaceComplex",
	Key:  "prop_ee53a548fe4668ad",
	Reading: "No simplicial identity is used: for any face maps the boundary of a chain " +
		"is the alternating sum of the pushforwards of its faces. The two complexes have " +
		"the same operations and terms, so with this they agree wherever a complex is read.",
	Deps: []registry.EntryLike{
		FaceBoundaryDef,
		simplicial_chain.SimplicialBoundaryDef,
		simplicial_chain.FaceSumDef,
		simplicial_chain.SimplicialChainsDef,
		free_module.FreeLiftDef,
		free_module.FreePushforwardDef,
		free_module.FreeModuleRecordDef,
		free_module.FreeModuleOn,
		free_module.DeltaAtIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀X:simplicial_ops(D). ∀n:num. ∀u:(D → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"u ∈ simplicial_chains(R.zero, X, R.carrier, n)",
		},
		Conclusion: "simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d, n, u) = " +
			"face_boundary(R, free_module_record(R, 𝕌), λm:num. λi:num. free_pushforward(R, X.d(m, i)), n, u)",
	},
		"both sides are the finite double sum of u(x) (−1)^i δ(d(n, i, x)) over the support of u and i ≤ "+
			"n: the left through SimplicialBoundaryDef, FreeLiftDef and FaceSumDef, the right through "+
			"FaceBoundaryDef and FreePushforwardDef; the two orders of summation agree (the module chapter's "+
			"ModuleSumSwap) in the free module on the whole type, which holds every term (DeltaAtIn)"),
})}

// SimplicialHomologyFaceComplex — the simplicial homology over R is the
// homology of the face complex of the free simplicial module.
var SimplicialHomologyFaceComplex = simplicialHomologyFaceComplexThm{family.Add(registry.ProofEntry{
	Name: "SimplicialHomologyFaceComplex",
	Key:  "prop_2408ed4b9e7fc49e",
	Deps: []registry.EntryLike{
		SimplicialChainsFaceComplex,
		FaceComplexDef,
		simplicial_chain.SimplicialHomologyDef,
		free_module.FreeModuleRecordDef,
		chain_complex.HomologyDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀X:simplicial_ops(D). ∀n:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "simplicial_homology(R.add, R.zero, R.one, R.neg, R.mul, X, R.carrier, n) = " +
			"homology(face_complex(R, free_module_record(R, 𝕌), free_simplicial_module(R, X)), n)",
	},
		"the two complexes have the same operations (FreeModuleRecordDef) and the same terms, and "+
			"their boundaries agree on the terms (SimplicialChainsFaceComplex); cycles, boundaries "+
			"and homology read the boundary on the terms only (CyclesDef, BoundariesDef, HomologyDef)"),
})}

// SimplicialChainsFreeComplex — the chains on a simplicial set over a
// commutative ring are a chain complex in the free complex's spelling.
var SimplicialChainsFreeComplex = simplicialChainsFreeComplexThm{family.Add(registry.ProofEntry{
	Name: "SimplicialChainsFreeComplex",
	Key:  "prop_6a6a9718e030f7df",
	Deps: []registry.EntryLike{
		simplicial_chain.ChainComplex,
		simplicial_chain.SimplicialChainsDef,
		resolution.FreeComplexOf,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀X:simplicial_ops(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"simplicial_set(X)",
		},
		Conclusion: "chain_complex(R, free_complex(R, X.simplices, simplicial_boundary))",
	},
		"simplicial_chain's ChainComplex at the ring mk_ring of R's parts, which is R (the "+
			"record's extensionality); the free complex's terms λn. finite_supp(R.zero, R.carrier, "+
			"X(n)) are simplicial_chains(R.zero, X, R.carrier) (SimplicialChainsDef, FreeComplexOf)"),
})}

// ---------------------------------------------------------------------------
// Homotopy invariance of the chains
// ---------------------------------------------------------------------------

// SimplicialHomotopyChainHomotopy — a simplicial homotopy H from F to G
// gives the chain homotopy Σ_{j ≤ n} (−1)^j (pushforward of H(n, j))
// between the pushforwards of F and G.
var SimplicialHomotopyChainHomotopy = simplicialHomotopyChainHomotopyThm{family.Add(registry.ProofEntry{
	Name: "SimplicialHomotopyChainHomotopy",
	Key:  "prop_342b97bcb5316220",
	Deps: []registry.EntryLike{
		FreeChainsSimplicialModule,
		SimplicialModuleHomotopyChainHomotopy,
		SimplicialModuleHomotopy,
		SimplicialModuleMap,
		SimplicialChainsFaceComplex,
		simplicial_homotopy.SimplicialHomotopy,
		free_module.FreePushforwardHom,
		free_module.FreePushforwardCompose,
		resolution.FreeComplexOf,
		chain_complex.ChainHomotopyDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:simplicial_ops(D). " +
			"∀Y:simplicial_ops(E). " +
			"∀F G:(num → D → E). " +
			"∀H:(num → num → D → E).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"simplicial_homotopy(X, Y, F, G, H)",
		},
		Conclusion: "chain_homotopy(R, " +
			"    free_complex(R, X.simplices, simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d)), " +
			"    free_complex(R, Y.simplices, simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, Y.d)), " +
			"    λn:num. free_pushforward(R, F(n)), " +
			"    λn:num. free_pushforward(R, G(n)), " +
			"    λn:num. λu:(D → A). " +
			"        module_sum(fun_add, " +
			"            fun_zero, " +
			"            0 .. n, " +
			"            λj:num. fun_smul(alternating_sign(j), free_pushforward(R, H(n, j), u))))",
	},
		"the chains of X and Y are simplicial modules (FreeChainsSimplicialModule), and the "+
			"pushforwards of F, G and H a linear simplicial homotopy, each identity of H being one of "+
			"its pushforwards on the chains (FreePushforwardHom, FreePushforwardCompose); "+
			"SimplicialModuleHomotopyChainHomotopy gives the chain homotopy of the face complexes, which "+
			"are the two chain complexes with the same boundary on chains (SimplicialChainsFaceComplex)"),
})}

// SimplicialMapsHomotopicChainHomotopic — homotopic simplicial maps have
// chain homotopic pushforwards.
var SimplicialMapsHomotopicChainHomotopic = simplicialMapsHomotopicChainHomotopicThm{family.Add(registry.ProofEntry{
	Name: "SimplicialMapsHomotopicChainHomotopic",
	Key:  "prop_6cf345575253a5ce",
	Deps: []registry.EntryLike{
		simplicial_homotopy.SimplicialMapsHomotopicDef,
		SimplicialHomotopyChainHomotopy,
		chain_complex.ChainHomotopyDef,
		free_module.FreePushforwardHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀X:simplicial_ops(D). ∀Y:simplicial_ops(E). ∀F G:(num → D → E).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"simplicial_maps_homotopic(X, Y, F, G)",
		},
		Conclusion: "∃h:(num → (D → A) → E → A). " +
			"    chain_homotopy(R, " +
			"        free_complex(R, " +
			"            X.simplices, " +
			"            simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d)), " +
			"        free_complex(R, " +
			"            Y.simplices, " +
			"            simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, Y.d)), " +
			"        λn:num. free_pushforward(R, F(n)), " +
			"        λn:num. free_pushforward(R, G(n)), " +
			"        h)",
	},
		"induction along the zigzag: a zigzag of length 0 has F = G and the zero homotopy; "+
			"each step is a chain homotopy by SimplicialHomotopyChainHomotopy, a step taken "+
			"backwards its negative, and the chain homotopies of two consecutive steps add"),
})}

// HomotopyEquivalenceChainHomotopyEquivalence — a simplicial homotopy
// equivalence F gives a chain homotopy equivalence of the chains: the
// pushforward of F, with the pushforward of an inverse of F as its
// inverse.
var HomotopyEquivalenceChainHomotopyEquivalence = homotopyEquivalenceChainHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "HomotopyEquivalenceChainHomotopyEquivalence",
	Key:  "prop_65b96361c33cfccd",
	Deps: []registry.EntryLike{
		chain_complex.ChainHomotopyEquivalenceDef,
		simplicial_homotopy.SimplicialHomotopyEquivalenceDef,
		SimplicialMapsHomotopicChainHomotopic,
		simplicial_chain.ChainMapOfSimplicialMap,
		simplicial_chain.SimplicialChainMapDef,
		free_module.FreePushforwardDef,
		free_module.FreePushforwardCompose,
		free_module.FreePushforwardIdentity,
		SimplicialChainsFreeComplex,
		chain_complex.ChainHomotopyDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀X:simplicial_ops(D). ∀Y:simplicial_ops(E). ∀F:(num → D → E).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"simplicial_homotopy_equivalence(X, Y, F)",
		},
		Conclusion: "∃G:(num → E → D). " +
			"    chain_homotopy_equivalence(R, " +
			"        free_complex(R, " +
			"            X.simplices, " +
			"            simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d)), " +
			"        free_complex(R, " +
			"            Y.simplices, " +
			"            simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, Y.d)), " +
			"        λn:num. free_pushforward(R, F(n)), " +
			"        λn:num. free_pushforward(R, G(n)))",
	},
		"G is the inverse of the definition. The pushforward of a simplicial map is its induced "+
			"chain map (ChainMapOfSimplicialMap, SimplicialChainMapDef and FreePushforwardDef "+
			"unfold to one term); on chains the pushforward of G ∘ F is the composite of the "+
			"pushforwards and that of the identity the identity (FreePushforwardCompose, "+
			"FreePushforwardIdentity), and SimplicialMapsHomotopicChainHomotopic turns the two "+
			"zigzags of the definition into the two chain homotopies of ChainHomotopyEquivalenceDef"),
})}

// ConstantSimplicialChainsHomology — the chains on the constant
// simplicial set on S have no boundaries in degree 0 and are exact above
// it: their homology is the free module on S in degree 0 and zero in
// every positive degree.
var ConstantSimplicialChainsHomology = constantSimplicialChainsHomologyThm{family.Add(registry.ProofEntry{
	Name: "ConstantSimplicialChainsHomology",
	Key:  "prop_b4f366cbccc9fea9",
	Reading: "Every face being the identity, the boundary out of degree m ≥ 1 " +
		"is the identity on the chains for m even and zero for m odd. The cycles in " +
		"degree 0 are all the chains on S, so the first conjunct says H_0 is the " +
		"free module on S. S may be empty: the chains are then {0} in every degree.",
	Deps: []registry.EntryLike{
		simplicial_chain.SimplicialBoundaryDef,
		simplicial_chain.FaceSumDef,
		comm_ring.AlternatingSignDef,
		simplicial_chain.BoundaryDelta,
		simplicial_set.ConstantSimplicialSet,
		resolution.FreeComplexOf,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		free_module.FreeLiftDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "boundaries(free_complex(R, " +
			"        λn:num. S, " +
			"        simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, λn:num. λi:num. λx:D. x)), " +
			"    0) = " +
			"{fun_zero} ∧ " +
			"(∀n:num. " +
			"    cycles(free_complex(R, " +
			"            λn:num. S, " +
			"            simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, λn:num. λi:num. λx:D. x)), " +
			"        n + 1) = " +
			"    boundaries(free_complex(R, " +
			"            λn:num. S, " +
			"            simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, λn:num. λi:num. λx:D. x)), " +
			"        n + 1))",
	},
		"every face is the identity, so the boundary of the generator at x out of dimension m is (Σ_{i "+
			"≤ m} (−1)^i) δ(x): δ(x) for m even, zero for m odd (AlternatingSignDef, BoundaryDelta); by "+
			"linearity the boundary out of m is the identity or zero on the chains, so the boundaries in "+
			"degree 0 are {0}, and above it the cycles and the boundaries are both all chains or both {0}"),
})}
