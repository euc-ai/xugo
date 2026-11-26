package polish_cohomology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/borel_subgroup"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

// CohomologyHasPolishCover — Cocycles are the closed kernel of a continuous differential
var CohomologyHasPolishCover = cohomologyHasPolishCoverThm{family.Add(registry.ProofEntry{
	Name: "CohomologyHasPolishCover",
	Key:  "prop_865715f5526ff1b4",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:complex_ops(A, B). ∀T:(num → set(set(B))). ∀n:num.",
		Hypotheses: []string{
			"polish_cochain_complex(R, Q, T)",
		},
		Conclusion: "cohomology_cover(Q, T, n)",
	},
		"Cocycles are the closed kernel of a continuous differential. In positive degree "+
			"apply ContinuousHomImagePolishable to the incoming differential with target the "+
			"cocycle group; in degree zero the denominator is the closed zero subgroup."),
	Deps: []registry.EntryLike{
		polish_group.ClosedSubgroupPolish,
		polish_group.ContinuousHomImagePolishable,
	},
})}

// CohomologyDefinableFunctor — Restrict f(n) to cocycles; it is a continuous lift of the existing cohomology_map
var CohomologyDefinableFunctor = cohomologyDefinableFunctorThm{family.Add(registry.ProofEntry{
	Name: "CohomologyDefinableFunctor",
	Key:  "prop_79c21a57fdf2e28c",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:complex_ops(A, B). " +
			"∀T:(num → set(set(B))). " +
			"∀P:complex_ops(A, C). " +
			"∀U:(num → set(set(C))). " +
			"∀f:(num → B → C). " +
			"∀n:num.",
		Hypotheses: []string{
			"polish_cochain_map(R, Q, T, P, U, f)",
		},
		Conclusion: "cohomology_borel_map(Q, T, n, P, U, n, cohomology_map(P, f, n))",
	},
		"Restrict f(n) to cocycles: it is continuous into the target cocycles by FromSubtopology "+
			"and IntoSubtopology, hence Borel, and CohomologyMapCoset makes it a lift of the existing "+
			"cohomology_map, which CohomologyMapHom makes a homomorphism of the quotients. The "+
			"identity and composition laws are those of CohomologyMapIdentity and CohomologyMapCompose."),
	Deps: []registry.EntryLike{
		CohomologyHasPolishCover,
		borel_space.ContinuousMapBorel,
		chain_complex.CohomologyMapCompose,
		chain_complex.CohomologyMapCoset,
		chain_complex.CohomologyMapHom,
		chain_complex.CohomologyMapIdentity,
		continuous.FromSubtopology,
		continuous.IntoSubtopology,
	},
})}

// ContinuousQuasiIsoDefinableIso — A continuous comparison inducing the ordinary isomorphism is inverted with a Borel lift.
var ContinuousQuasiIsoDefinableIso = continuousQuasiIsoDefinableIsoThm{family.Add(registry.ProofEntry{
	Name: "ContinuousQuasiIsoDefinableIso",
	Key:  "prop_da5edb7104079a20",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:complex_ops(A, B). " +
			"∀T:(num → set(set(B))). " +
			"∀P:complex_ops(A, C). " +
			"∀U:(num → set(set(C))). " +
			"∀f:(num → B → C). " +
			"∀n:num.",
		Hypotheses: []string{
			"polish_cochain_map(R, Q, T, P, U, f)",
			"module_isomorphism(R, cohomology_module(Q, n), cohomology_module(P, n), cohomology_map(P, f, n))",
		},
		Conclusion: "cohomology_borel_iso(Q, T, n, P, U, n, cohomology_map(P, f, n))",
	},
		"The lift of cohomology_map(P, f, n) is f(n) restricted to cocycles, a continuous "+
			"homomorphism; CohomologyHasPolishCover supplies both covers. Present the target coboundaries "+
			"as the image of the preceding differential on the preceding term, or of the constant zero "+
			"map in degree zero. The module isomorphism supplies injectivity and surjectivity on the "+
			"quotient carriers, and ContinuousLiftBijectiveIso supplies the inverse with a Borel lift."),
	Deps: []registry.EntryLike{
		CohomologyDefinableFunctor,
		CohomologyHasPolishCover,
		polish_group.ContinuousLiftBijectiveIso,
		continuous.IntoSubtopology,
	},
	Reading: "The specified comparison map must induce the ordinary isomorphism; " +
		"an unrelated abstract isomorphism between the groups would not suffice. The " +
		"inverse lift is Borel and is inverse only modulo coboundaries.",
})}

// HomotopyEquivalenceDefinableIso — Two Polish models compared by a continuous cochain homotopy equivalence have Borel-isomorphic covers in every degree.
var HomotopyEquivalenceDefinableIso = homotopyEquivalenceDefinableIsoThm{family.Add(registry.ProofEntry{
	Name: "HomotopyEquivalenceDefinableIso",
	Key:  "prop_8f67650c277ea617",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:complex_ops(A, B). " +
			"∀T:(num → set(set(B))). " +
			"∀P:complex_ops(A, C). " +
			"∀U:(num → set(set(C))). " +
			"∀f:(num → B → C). " +
			"∀g:(num → C → B). " +
			"∀n:num.",
		Hypotheses: []string{
			"polish_cochain_map(R, Q, T, P, U, f)",
			"polish_cochain_map(R, P, U, Q, T, g)",
			"cochain_homotopy_equivalence(R, Q, P, f, g)",
		},
		Conclusion: "cohomology_borel_iso(Q, T, n, P, U, n, cohomology_map(P, f, n)) ∧ " +
			"cohomology_borel_iso(P, U, n, Q, T, n, cohomology_map(Q, g, n))",
	},
		"CochainHomotopyEquivalenceIsomorphism makes each induced map a module isomorphism of "+
			"cohomology, and ContinuousQuasiIsoDefinableIso inverts each with a Borel lift. "+
			"HomotopicSameCohomologyMap makes any homotopic replacement of f or g induce the same comparison."),
	Deps: []registry.EntryLike{
		ContinuousQuasiIsoDefinableIso,
		chain_complex.CochainHomotopyEquivalenceIsomorphism,
		chain_complex.HomotopicSameCohomologyMap,
	},
	Reading: "The homotopies are algebraic data and need not be continuous: the coherence equations " +
		"live on the cohomology carriers. Each direction is read with its own degree-wise cover.",
})}

// ConnectingMapDefinable — Two Borel sections give the connecting lift on cocycle carriers.
var ConnectingMapDefinable = connectingMapDefinableThm{family.Add(registry.ProofEntry{
	Name: "ConnectingMapDefinable",
	Key:  "prop_5de426b177a150f8",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:complex_ops(A, B). " +
			"∀T:(num → set(set(B))). " +
			"∀P:complex_ops(A, C). " +
			"∀U:(num → set(set(C))). " +
			"∀W:complex_ops(A, D). " +
			"∀V:(num → set(set(D))). " +
			"∀i:(num → B → C). " +
			"∀p:(num → C → D). " +
			"∀n:num.",
		Hypotheses: []string{
			"short_exact_cochain_complexes(R, Q, P, W, i, p)",
			"polish_cochain_map(R, Q, T, P, U, i)",
			"polish_cochain_map(R, P, U, W, V, p)",
		},
		Conclusion: "cohomology_borel_map(W, V, n, Q, T, n + 1, coconnecting_hom(Q, P, i, p, n))",
	},
		"Apply ContinuousSurjectionBorelSection to p(n) onto the quotient term and to i(n+1) "+
			"corestricted to its image, which exactness identifies with the closed kernel of p(n+1), "+
			"a Polish group by ClosedSubgroupPolish; this gives Borel sections s_p and s_i. On a "+
			"target cocycle z the lift is s_i(P.d(n, s_p(z))): exactness places the middle value in "+
			"that image and injectivity in the following degree makes the output a cocycle. "+
			"CoconnectingHomCoset identifies its quotient class with the existing connecting map."),
	Deps: []registry.EntryLike{
		CohomologyHasPolishCover,
		polish_group.ContinuousSurjectionBorelSection,
		polish_group.ClosedSubgroupPolish,
		chain_complex.CoconnectingHom,
		chain_complex.CoconnectingHomCoset,
		borel_space.ContinuousMapBorel,
		borel_space.BorelMapCompose,
	},
	Reading: "Both sections come from the same surjection theorem, the second after " +
		"corestricting i(n+1) to its closed image. Neither section is a homomorphism, " +
		"and no continuous inverse is asserted. Sections are chosen after fixing the " +
		"degree and data, so no parameterwise measurability is asserted.",
})}

// CountableBasedDualPolish — A countable based dual is a Polish complex: its terms by the product-group theorem, its differential by finite-coordinate continuity.
var CountableBasedDualPolish = countableBasedDualPolishThm{family.Add(registry.ProofEntry{
	Name: "CountableBasedDualPolish",
	Key:  "prop_899b6276d40692a5",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀P:complex_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r:(num → B → I → A).",
		Hypotheses: []string{
			"based_chain_complex(R, P, S, e, r)",
			"module_on(R, N)",
			"countable(N.carrier)",
			"∀n:num. countable(S(n))",
		},
		Conclusion: "polish_cochain_complex(R, " +
			"    free_dual_complex(R, N, P, S, e, r), " +
			"    dual_pointwise_topologies(N, S))",
	},
		"The existing free-dual theorem supplies the cochain-complex laws. Each degree term is the "+
			"normalized product of copies of N on the generators with pointwise operations, a Polish "+
			"abelian group by DiscreteProductGroupPolish. Each coordinate of the transpose differential "+
			"reads the finite support of the boundary of one basis vector; apply FiniteCoordinateContinuous."),
	Deps: []registry.EntryLike{
		polish_group.DiscreteProductGroupPolish,
		polish_space.FiniteCoordinateContinuous,
		free_complex_duality.FreeDualCochainComplex,
	},
	Reading: "Countability concerns the basis generators and coefficients, not " +
		"the full chain-module carrier or the scalar ring. Finite basis expansions " +
		"and normalization supply the coordinate-dependence and image hypotheses.",
})}

// BasedDualMapContinuous — Transposed chain maps use the common finite-coordinate continuity theorem.
var BasedDualMapContinuous = basedDualMapContinuousThm{family.Add(registry.ProofEntry{
	Name: "BasedDualMapContinuous",
	Key:  "prop_909496d902e235cc",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀P:complex_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r:(num → B → I → A). " +
			"∀Q:complex_ops(A, D). " +
			"∀S₂:(num → set(E)). " +
			"∀e₂:(num → (E → A) → D). " +
			"∀r₂:(num → D → E → A). " +
			"∀f:(num → B → D).",
		Hypotheses: []string{
			"based_chain_complex(R, P, S, e, r)",
			"based_chain_complex(R, Q, S₂, e₂, r₂)",
			"chain_map(R, P, Q, f)",
			"module_on(R, N)",
			"countable(N.carrier)",
			"∀n:num. countable(S(n)) ∧ countable(S₂(n))",
		},
		Conclusion: "polish_cochain_map(R, " +
			"    free_dual_complex(R, N, Q, S₂, e₂, r₂), " +
			"    dual_pointwise_topologies(N, S₂), " +
			"    free_dual_complex(R, N, P, S, e, r), " +
			"    dual_pointwise_topologies(N, S), " +
			"    free_dual_map(R, N, S, e, r₂, f))",
	},
		"FreeDualCochainMap supplies the algebraic cochain map. For each source basis "+
			"vector its image has a finite target-basis expansion, so each dual output reads "+
			"finitely many coordinates; apply FiniteCoordinateContinuous with the dual carriers."),
	Deps: []registry.EntryLike{
		CountableBasedDualPolish,
		polish_space.FiniteCoordinateContinuous,
		free_complex_duality.FreeDualCochainMap,
	},
	Reading: "The finite support may vary with the output basis vector but is independent of " +
		"the input cochain. Inactive coordinates must still be normalized to the coefficient zero.",
})}

// CountableCohomologyClosedCoboundaries — Countable cohomology forces the coboundaries to be open and closed in the cocycles.
var CountableCohomologyClosedCoboundaries = countableCohomologyClosedCoboundariesThm{family.Add(registry.ProofEntry{
	Name: "CountableCohomologyClosedCoboundaries",
	Key:  "prop_da85140aca1f5dae",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:complex_ops(A, B). ∀T:(num → set(set(B))). ∀n:num.",
		Hypotheses: []string{
			"polish_cochain_complex(R, Q, T)",
			"countable(cohomology(Q, n))",
		},
		Conclusion: "coboundaries(Q, n) ∈ cocycle_topology(Q, T, n) ∧ " +
			"closed_in(cocycle_topology(Q, T, n), coboundaries(Q, n))",
	},
		"The coboundaries are a Borel subgroup of the Polish cocycle group: in positive degree "+
			"the image of the preceding differential, corestricted to the cocycles, Borel by "+
			"ContinuousHomImagePolishable; in degree zero the closed zero subgroup. cohomology(Q, "+
			"n) is the set of its cosets, so CountableIndexBorelSubgroupClopen applies."),
	Deps: []registry.EntryLike{
		CohomologyHasPolishCover,
		polish_group.ContinuousHomImagePolishable,
		borel_subgroup.CountableIndexBorelSubgroupClopen,
		continuous.IntoSubtopology,
	},
	Reading: "Closed in the cocycle topology is closed in the degree topology, the cocycles " +
		"being closed. The converse fails: closed coboundaries allow uncountable cohomology.",
})}

// NonclosedCoboundariesContinuumCohomology — Coboundaries that are not closed give at least continuum many classes.
var NonclosedCoboundariesContinuumCohomology = nonclosedCoboundariesContinuumCohomologyThm{family.Add(registry.ProofEntry{
	Name: "NonclosedCoboundariesContinuumCohomology",
	Key:  "prop_6036409b40525d1",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:complex_ops(A, B). ∀T:(num → set(set(B))). ∀n:num.",
		Hypotheses: []string{
			"polish_cochain_complex(R, Q, T)",
			"¬closed_in(cocycle_topology(Q, T, n), coboundaries(Q, n))",
		},
		Conclusion: "card_le(𝕌⟨A:set(num)⟩, cohomology(Q, n))",
	},
		"The coboundaries are a Borel subgroup of the Polish cocycle group as in "+
			"CountableCohomologyClosedCoboundaries; NonclosedBorelSubgroupContinuumIndex "+
			"gives continuum many cosets, which are the classes."),
	Deps: []registry.EntryLike{
		CohomologyHasPolishCover,
		polish_group.ContinuousHomImagePolishable,
		borel_subgroup.NonclosedBorelSubgroupContinuumIndex,
	},
	Reading: "The continuum is the subsets of ℕ. In degree zero the " +
		"coboundaries are closed, so the hypothesis never holds there.",
})}

// CohomologyCountableOrContinuum — The cohomology of a Polish cochain model is countable or has at least continuum many classes.
var CohomologyCountableOrContinuum = cohomologyCountableOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "CohomologyCountableOrContinuum",
	Key:  "prop_c71e41a554afd429",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:complex_ops(A, B). ∀T:(num → set(set(B))). ∀n:num.",
		Hypotheses: []string{
			"polish_cochain_complex(R, Q, T)",
		},
		Conclusion: "countable(cohomology(Q, n)) ∨ card_le(𝕌⟨A:set(num)⟩, cohomology(Q, n))",
	},
		"BorelSubgroupIndexDichotomy for the coboundaries inside the Polish "+
			"cocycle group, Borel as in CountableCohomologyClosedCoboundaries."),
	Deps: []registry.EntryLike{
		CohomologyHasPolishCover,
		polish_group.ContinuousHomImagePolishable,
		borel_subgroup.BorelSubgroupIndexDichotomy,
	},
	Reading: "The alternative is decided by whether the coboundaries " +
		"are meager in the cocycles, not by whether they are closed.",
})}
