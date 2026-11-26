package k_compact_support

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/k_theory"
	"github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var TripleSum = tripleSumThm{family.Add(registry.ProofEntry{
	Name: "TripleSum",
	Key:  "prop_ca0b4793e20cc6da",
	Deps: []registry.EntryLike{projection_bundle.SumBundle},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀a b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{"kc_triple(T, a)", "kc_triple(T, b)"},
		Conclusion: "kc_triple(T, kc_triple_sum(a, b))",
	}, "Take the union of the two compact supports and form the block diagonal map and its inverse."),
})}

var TripleInverse = tripleInverseThm{family.Add(registry.ProofEntry{
	Name: "TripleInverse",
	Key:  "prop_57353dfe1db21fd2",
	Deps: []registry.EntryLike{
		complex_topology.ContinuousAtConj,
		complex_topology.ContinuousOnIffMap,
		continuous.Compose,
		module.ModuleSumMonoidHomomorphism,
		complex_field.ConjMul,
		complex_field.ConjConj,
		complex_field.ConjAdd,
		complex_field.ConjOfReal,
		complex_topology.ContinuousAtOn,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{"kc_triple(T, a)"},
		Conclusion: "kc_triple(T, kc_inverse_triple(a))",
	},
		"The adjoint is invertible wherever the original map is invertible; it has the same "+
			"compact singular support. Conjugation is continuous on the plane "+
			"(ContinuousAtConj, ContinuousOnIffMap), so the adjoint's entries are "+
			"(continuous.Compose); conjugation passes through the finite sums and reverses "+
			"products (ModuleSumMonoidHomomorphism, ConjMul, ConjConj), and P, Q are Hermitian, "+
			"so the adjoint is a map from Q to P whose inverse at x is the adjoint of U's."),
})}

var Equivalence = equivalenceThm{family.Add(registry.ProofEntry{
	Name: "Equivalence",
	Key:  "prop_ec3e14b91daa9b1f",
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)).",
		Conclusion: "equivalence_on({a:prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex)) | " +
			"        kc_triple(T, a)}, " +
			"    kc_equivalent(T))",
	},
		"Each law passes through the quantifier over R: kc_equivalent(a, b) "+
			"gives R(a, b) for every admissible R, and R's own reflexivity, symmetry "+
			"and transitivity on triples give the same for b and a, or for a and c."),
})}

var OperationsDescend = operationsDescendThm{family.Add(registry.ProofEntry{
	Name: "OperationsDescend",
	Key:  "prop_d05dd67dd73fc72",
	Deps: []registry.EntryLike{Equivalence, TripleSum, TripleInverse},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀a b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{
			"is_topology(T)",
			"kc_triple(T, a)",
			"kc_triple(T, b)",
		},
		Conclusion: "kc_add(T, kc_class(T, a), kc_class(T, b)) = kc_class(T, kc_triple_sum(a, b)) ∧ " +
			"kc_negate(T, kc_class(T, a)) = kc_class(T, kc_inverse_triple(a))",
	},
		"The defining congruence handles addition; adjoints preserve "+
			"each generating relation and commute with block sum."),
})}

var AbelianGroup = abelianGroupThm{family.Add(registry.ProofEntry{
	Name: "AbelianGroup",
	Key:  "prop_c229a7b97ad9c866",
	Deps: []registry.EntryLike{
		OperationsDescend,
		projection_bundle.TrivialBundle,
		TripleSum,
		TripleInverse,
		Equivalence,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Hypotheses: []string{"is_topology(T)"},
		Conclusion: "abelian_group_on(kc_group(T))",
	},
		"Block rotations identify a triple plus its adjoint inverse with a degenerate "+
			"triple; block permutations and homotopies prove the abelian group laws."),
})}

var ProperPullback = properPullbackThm{family.Add(registry.ProofEntry{
	Name: "ProperPullback",
	Key:  "prop_788f93f990726f3c",
	Deps: []registry.EntryLike{
		AbelianGroup,
		projection_bundle.PullbackBundle,
		PullbackDescends,
		OperationsDescend,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"kc_proper_map(T, S, f)",
		},
		Conclusion: "group_homomorphism(kc_group(S), kc_group(T), kc_pullback(T, f))",
	},
		"Properness pulls compact singular support back to compact "+
			"support, including the uniform support of each homotopy."),
})}

// PullbackDescends — pulling a compactly supported class back along a proper map pulls back
// any of its triples.
var PullbackDescends = pullbackDescendsThm{family.Add(registry.ProofEntry{
	Name: "PullbackDescends",
	Key:  "prop_d4144e2cd9e44524",
	Deps: []registry.EntryLike{
		Equivalence,
		equivalence.InducedMapClass,
		PullbackDef,
		ClassDef,
		RelationDef,
		PullbackTripleDef,
		TripleDef,
		ProperDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀f:(A → B). " +
			"∀a:prod(prod(num, B → num → num → complex), " +
			"        prod(prod(num, B → num → num → complex), B → num → num → complex)).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"kc_proper_map(T, S, f)",
			"kc_triple(S, a)",
		},
		Conclusion: "kc_pullback(T, f, kc_class(S, a)) = kc_class(T, kc_triple_pullback(T, f, a))",
	},
		"kc_pullback evaluates at the chosen representative of the class (PullbackDef), so the formula "+
			"holds once pulling back carries kc_equivalent triples of S to kc_equivalent triples of T "+
			"(relations/equivalence.InducedMapClass with Equivalence). The pullback of a triple is a "+
			"triple: f is continuous, and a compact singular support K pulls back to the compact {x ∈ ⋃T | "+
			"f(x) ∈ K} (ProperDef). The generating relation (RelationDef) is carried along: the zero triple "+
			"and sums pull back exactly, a degenerate triple to a degenerate one, and the singular support "+
			"K of a homotopy over S × ⟦0, 1⟧ pulls back into f⁻¹(π_S K) × ⟦0, 1⟧, compact since π_S K is."),
	Reading: "Properness is the hypothesis the proof stands on; f × id need " +
		"not be proper when S is not Hausdorff, which is why the homotopy's " +
		"support is bounded through its projection to S. An empty ⋃T is harmless.",
})}

// CompactToKDescends — on a compact Hausdorff space the comparison map reads a class's
// virtual difference off any of its triples.
var CompactToKDescends = compactToKDescendsThm{family.Add(registry.ProofEntry{
	Name: "CompactToKDescends",
	Key:  "prop_39555f8430895513",
	Deps: []registry.EntryLike{
		Equivalence,
		equivalence.InducedMapClass,
		CompactComparisonDef,
		ClassDef,
		RelationDef,
		degenerateDef,
		HomotopyDef,
		k_theory.ClassEquality,
		projection_bundle.HomotopicPullbacks,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, ⋃T)",
			"kc_triple(T, a)",
		},
		Conclusion: "kc_to_k(T, kc_class(T, a)) = k_class(T, (fst(a), fst(snd(a))))",
	},
		"kc_to_k evaluates at the chosen representative of the class (CompactComparisonDef), so the "+
			"formula holds once kc_equivalent triples have the same virtual difference "+
			"(relations/equivalence.InducedMapClass with Equivalence). The generating relation "+
			"(RelationDef) keeps it (k_theory.ClassEquality): the zero triple is exact, sums need stable "+
			"equivalence to be a congruence for projection_sum, a degenerate triple's map is an "+
			"isomorphism of its two bundles (degenerateDef) once its pointwise inverse is made continuous, "+
			"as (σ*σ + 1 − P)⁻¹σ* (both the filler's), and a homotopy over T × ⟦0, 1⟧ (HomotopyDef) has "+
			"isomorphic end bundles on the compact base (projection_bundle.HomotopicPullbacks)."),
	Reading: "Compactness of the base is what HomotopicPullbacks needs; no separation axiom enters.",
})}

// HomeomorphismPullbackIsomorphism — a homeomorphism pulls compactly
// supported classes back isomorphically.
var HomeomorphismPullbackIsomorphism = homeomorphismPullbackIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphismPullbackIsomorphism",
	Key:  "prop_53eddb90d8e75b74",
	Deps: []registry.EntryLike{
		ProperPullback,
		PullbackDescends,
		ProperDef,
		PullbackDef,
		PullbackTripleDef,
		TripleDef,
		continuous.HomeomorphismInverse,
		continuous.ImageCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"homeomorphic_map(T, S, f)",
		},
		Conclusion: "group_isomorphism(kc_group(S), kc_group(T), kc_pullback(T, f))",
	},
		"f and its inverse g = inverse_on(⋃T, f) are proper: the points of T that f sends into a "+
			"compact K of S are g(K), compact by continuous.ImageCompact (continuous.HomeomorphismInverse), "+
			"and symmetrically; so both pullbacks are homomorphisms (ProperPullback). A triple's bundles "+
			"and map vanish off its space (TripleDef), so pulling it back along f and then g returns it "+
			"exactly (PullbackTripleDef). PullbackDescends computes each induced map on a class through a "+
			"triple of it, so the two induced maps on classes are mutually inverse."),
	Reading: "Pulling back along f and then along its inverse returns a triple " +
		"exactly only because the triple's bundles and map vanish off its space. " +
		"With an empty carrier every triple is degenerate and both groups are trivial.",
})}

var CompactComparison = compactComparisonThm{family.Add(registry.ProofEntry{
	Name: "CompactComparison",
	Key:  "prop_ad91dbb6a4f96210",
	Deps: []registry.EntryLike{AbelianGroup, k_theory.ClassEquality, CompactToKDescends},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Hypotheses: []string{"is_topology(T)", "hausdorff(T)", "compact_in(T, ⋃T)"},
		Conclusion: "group_isomorphism(kc_group(T), additive_group(k_ring(T)), kc_to_k(T))",
	},
		"On a compact base every bundle map is admissible and can be homotoped to zero; "+
			"the remaining relation is exactly stable equivalence of virtual differences."),
})}

var OpenExtensionExists = openExtensionExistsThm{family.Add(registry.ProofEntry{
	Name: "OpenExtensionExists",
	Key:  "prop_fd899fbd4e86281a",
	Deps: []registry.EntryLike{
		real_valued.LocallyCompactUrysohn,
		compact.LocallyCompactHausdorffNeighbourhood,
		projection_bundle.TrivialBundle,
		projection_bundle.SumBundle,
		projection_bundle.PullbackBundle,
		Equivalence,
		complex_topology.ContinuousComplexSum,
		complex_topology.ContinuousComplexMul,
		complex_topology.ContinuousComplexInv,
		complex_topology.ContinuousComplexProduct,
		determinant.AdjugateIdentity,
		TripleSum,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀U:set(A). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"U ∈ T",
			"a ∈ (kc_group(subtopology(T, U))).carrier",
		},
		Conclusion: "∃b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∃K:set(A). " +
			"    K ⊆ U ∧ " +
			"    kc_supported_in(T, K, b) ∧ " +
			"    kc_class(T, b) = kc_open_extension(T, U, a) ∧ " +
			"    kc_class(subtopology(T, U), kc_triple_pullback(subtopology(T, U), λx:A. x, b)) = a",
	},
		"Choose a compact neighborhood of the singular support inside U, add a complementary "+
			"projection there, and glue to a trivial bundle using the given invertible map on the "+
			"collar. A finite partition realizes the glued bundle by a Hermitian projection. The "+
			"neighbourhood and the cut-off functions of the partition come from "+
			"LocallyCompactHausdorffNeighbourhood and LocallyCompactUrysohn; the complement and the "+
			"trivial bundle are bundles by SumBundle and TrivialBundle. The glued bundle is the image "+
			"of an embedding into a trivial bundle built from the cut-offs and the clutching map, and "+
			"its orthogonal projection needs an inverse, such as that of φ₁²P + φ₂²σ*σ; the clutching "+
			"map's inverse off the support, which projection_invertible_at gives only point by point, "+
			"is needed as a continuous map too. Both are adjugates over nowhere-zero determinants "+
			"(AdjugateIdentity, ContinuousComplexProduct, ContinuousComplexInv), the other entries "+
			"sums of products (ContinuousComplexSum, ContinuousComplexMul). The restriction to U is "+
			"equivalent to a by the generators themselves: adding the degenerate complement "+
			"(TripleSum) and an isomorphism of the glued bundle with P on U, read as a homotopy; "+
			"PullbackBundle makes the restrictions bundles and Equivalence composes the steps."),
})}

var Excision = excisionThm{family.Add(registry.ProofEntry{
	Name: "Excision",
	Key:  "prop_8d18c444f48aa395",
	Deps: []registry.EntryLike{OpenExtensionExists},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀U K:set(A). " +
			"∀b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{
			"is_topology(T)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"U ∈ T",
			"K ⊆ U",
			"kc_supported_in(T, K, b)",
		},
		Conclusion: "kc_open_extension(T, " +
			"    U, " +
			"    kc_class(subtopology(T, U), kc_triple_pullback(subtopology(T, U), λx:A. x, b))) = " +
			"kc_class(T, b)",
	},
		"Extend each compactly supported homotopy and stabilization through a collar; two "+
			"global triples restricting to the same local class differ only by degenerate data."),
})}

var OpenExtensionHomomorphism = openExtensionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "OpenExtensionHomomorphism",
	Key:  "prop_4e423229e41ef6d2",
	Deps: []registry.EntryLike{Excision, AbelianGroup},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀U:set(A).",
		Hypotheses: []string{"is_topology(T)", "locally_compact_space(T)", "hausdorff(T)", "U ∈ T"},
		Conclusion: "group_homomorphism(kc_group(subtopology(T, U)), kc_group(T), kc_open_extension(T, U))",
	},
		"Direct sum of global representatives extends the "+
			"local sum, and excision identifies its class uniquely."),
})}

var OpenExtensionComposition = openExtensionCompositionThm{family.Add(registry.ProofEntry{
	Name: "OpenExtensionComposition",
	Key:  "prop_6af8600035cfa868",
	Deps: []registry.EntryLike{Excision},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀U V:set(A). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"U ∈ T",
			"V ∈ T",
			"V ⊆ U",
			"a ∈ (kc_group(subtopology(T, V))).carrier",
		},
		Conclusion: "kc_open_extension(T, U, kc_open_extension(subtopology(T, U), V, a)) = " +
			"kc_open_extension(T, V, a)",
	}, "Use a representative supported in a compact subset of V for both successive extensions."),
})}

var ExternalTripleSupport = externalTripleSupportThm{family.Add(registry.ProofEntry{
	Name: "ExternalTripleSupport",
	Key:  "prop_e0328ed3418c697f",
	Deps: []registry.EntryLike{projection_bundle.TensorBundle},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀b:prod(prod(num, B → num → num → complex), " +
			"        prod(prod(num, B → num → num → complex), B → num → num → complex)). " +
			"∀K:set(A). " +
			"∀L:set(B).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"kc_supported_in(T, K, a)",
			"kc_supported_in(S, L, b)",
		},
		Conclusion: "kc_supported_in(product_topology(T, S), " +
			"    set_cross(K, L), " +
			"    kc_triple_external(T, S, a, b))",
	},
		"Both adjoint products of the graded tensor map are sums of positive squares, so it is "+
			"invertible whenever either factor is; the singular locus is contained in the compact product."),
})}

var ExternalDescends = externalDescendsThm{family.Add(registry.ProofEntry{
	Name: "ExternalDescends",
	Key:  "prop_255f11887be4666f",
	Deps: []registry.EntryLike{ExternalTripleSupport},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀b:prod(prod(num, B → num → num → complex), " +
			"        prod(prod(num, B → num → num → complex), B → num → num → complex)).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"kc_triple(T, a)",
			"kc_triple(S, b)",
		},
		Conclusion: "kc_external(T, S, kc_class(T, a), kc_class(S, b)) = " +
			"kc_class(product_topology(T, S), kc_triple_external(T, S, a, b))",
	},
		"The graded tensor construction preserves homotopies, degenerate "+
			"triples and direct sums in each factor; compact supports multiply."),
})}

var ExternalAdditive = externalAdditiveThm{family.Add(registry.ProofEntry{
	Name: "ExternalAdditive",
	Key:  "prop_f801d220b6dd77e3",
	Deps: []registry.EntryLike{ExternalDescends},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀a b:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"∀d:set(prod(prod(num, B → num → num → complex), " +
			"            prod(prod(num, B → num → num → complex), B → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"a ∈ (kc_group(T)).carrier",
			"b ∈ (kc_group(T)).carrier",
			"d ∈ (kc_group(S)).carrier",
		},
		Conclusion: "kc_external(T, S, kc_add(T, a, b), d) = " +
			"kc_add(product_topology(T, S), kc_external(T, S, a, d), kc_external(T, S, b, d))",
	},
		"A graded block permutation identifies the external "+
			"product of a sum with the sum of external products."),
})}
