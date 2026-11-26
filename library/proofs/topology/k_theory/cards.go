package k_theory

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/registry"
)

var StableEquivalence = stableEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "StableEquivalence",
	Key:  "prop_77b18694cbf3832f",
	Deps: []registry.EntryLike{
		projection_bundle.IsomorphismEquivalence,
		projection_bundle.SumIsomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)).",
		Conclusion: "equivalence_on({v:prod(prod(num, A → num → num → complex), " +
			"            prod(num, A → num → num → complex)) | " +
			"        k_virtual_bundle(T, v)}, " +
			"    k_stable_equivalent(T))",
	},
		"Adding the two stabilizing bundles and the middle negative bundle proves "+
			"transitivity; block permutations establish symmetry and reflexivity."),
})}

var ClassEquality = classEqualityThm{family.Add(registry.ProofEntry{
	Name: "ClassEquality",
	Key:  "prop_c4359d7efbd2584c",
	Deps: []registry.EntryLike{StableEquivalence},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀u v:prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)).",
		Hypotheses: []string{"is_topology(T)", "k_virtual_bundle(T, u)", "k_virtual_bundle(T, v)"},
		Conclusion: "k_class(T, u) = k_class(T, v) ⇔ k_stable_equivalent(T, u, v)",
	}, "The equivalence classes agree exactly for stably equivalent virtual bundles."),
})}

var OperationsDescend = operationsDescendThm{family.Add(registry.ProofEntry{
	Name: "OperationsDescend",
	Key:  "prop_3ff62e94bf5696a3",
	Deps: []registry.EntryLike{StableEquivalence},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀u v:prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)).",
		Hypotheses: []string{"is_topology(T)", "k_virtual_bundle(T, u)", "k_virtual_bundle(T, v)"},
		Conclusion: "k_add(T, k_class(T, u), k_class(T, v)) = k_class(T, k_virtual_add(u, v)) ∧ " +
			"k_multiply(T, k_class(T, u), k_class(T, v)) = k_class(T, k_virtual_multiply(u, v)) ∧ " +
			"k_negate(T, k_class(T, u)) = k_class(T, (snd(u), fst(u)))",
	},
		"Block sum and tensor product preserve stable equivalence, "+
			"so each chosen representative has the same output class."),
})}

var CommutativeRing = commutativeRingThm{family.Add(registry.ProofEntry{
	Name: "CommutativeRing",
	Key:  "prop_2c51e1dc18117eb6",
	Deps: []registry.EntryLike{
		OperationsDescend,
		projection_bundle.SumBundle,
		projection_bundle.TensorBundle,
		projection_bundle.TensorIsomorphism,
		projection_bundle.TrivialBundle,
		ClassEquality,
		projection_bundle.IsomorphismEquivalence,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Hypotheses: []string{"is_topology(T)"},
		Conclusion: "comm_ring_on(k_ring(T))",
	},
		"The virtual bundle classes form a commutative ring; canonical "+
			"block permutations and distributivity give its laws."),
})}

var PullbackHomomorphism = pullbackHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "PullbackHomomorphism",
	Key:  "prop_4a5dc19b9a588a0c",
	Deps: []registry.EntryLike{
		CommutativeRing,
		projection_bundle.PullbackBundle,
		continuous.MapsInto,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{"is_topology(T)", "is_topology(S)", "continuous_map(T, S, f)"},
		Conclusion: "ring_homomorphism(k_ring(S), k_ring(T), k_pullback(T, f))",
	},
		"Pullback preserves projection isomorphisms, block sums "+
			"and tensor products, hence induces the ring homomorphism."),
})}

var PullbackComposition = pullbackCompositionThm{family.Add(registry.ProofEntry{
	Name: "PullbackComposition",
	Key:  "prop_905cf2dcc6a7a865",
	Deps: []registry.EntryLike{PullbackHomomorphism},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀U:set(set(C)). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀a:set(prod(prod(num, C → num → num → complex), prod(num, C → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"is_topology(U)",
			"continuous_map(T, S, f)",
			"continuous_map(S, U, g)",
			"a ∈ (k_ring(U)).carrier",
		},
		Conclusion: "k_pullback(T, g ∘ f, a) = k_pullback(T, f, k_pullback(S, g, a))",
	},
		"Normalize on the source carrier after composition; "+
			"the two pullback representatives coincide there."),
})}

var HomotopyInvariance = homotopyInvarianceThm{family.Add(registry.ProofEntry{
	Name: "HomotopyInvariance",
	Key:  "prop_c648d7d2f3649dae",
	Deps: []registry.EntryLike{projection_bundle.HomotopicPullbacks},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀f g:(A → B). " +
			"∀a:set(prod(prod(num, B → num → num → complex), prod(num, B → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"is_topology(S)",
			"homotopic_rel(T, S, ∅, f, g)",
			"a ∈ (k_ring(S)).carrier",
		},
		Conclusion: "k_pullback(T, f, a) = k_pullback(T, g, a)",
	},
		"Apply the isomorphism of homotopic projection "+
			"pullbacks to both terms of a virtual representative."),
})}

var PointNormalization = pointNormalizationThm{family.Add(registry.ProofEntry{
	Name: "PointNormalization",
	Key:  "prop_9cf46ed53550e904",
	Deps: []registry.EntryLike{
		CommutativeRing,
		projection_bundle.RankTrace,
		ClassEquality,
		projection_bundle.TrivialBundle,
		module.ModuleSumSwap,
		projection_bundle.PointIsomorphicIffRank,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀x:A.",
		Hypotheses: []string{"is_topology(T)", "⋃T = {x}"},
		Conclusion: "ring_isomorphism(k_ring(T), " +
			"    int_ring, " +
			"    λa:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"        k_rank(a, x))",
	},
		"At a point Hermitian projections are classified by their finite rank, their "+
			"trace (RankTrace); differences of ranks give every integer and detect stable "+
			"equivalence. Over the point, rank detects isomorphism (PointIsomorphicIffRank)."),
})}
