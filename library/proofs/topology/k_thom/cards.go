package k_thom

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/exterior_basis"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/topology/bott_periodicity"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

var ExteriorProjection = exteriorProjectionThm{family.Add(registry.ProofEntry{
	Name: "ExteriorProjection",
	Key:  "prop_a19fe9f80ae3f024",
	Deps: []registry.EntryLike{
		exterior_basis.ExteriorPowerProduct,
		exterior_basis.ExteriorPowerTranspose,
		exterior_basis.ExteriorPowerIdentity,
		module.ModuleSumMonoidHomomorphism,
		complex_field.ConjAdd,
		complex_field.ConjMul,
		complex_topology.ContinuousComplexSum,
		complex_topology.ContinuousComplexProduct,
		complex_topology.ContinuousComplexMul,
		continuous.Constant,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). ∀e:num.",
		Hypotheses: []string{"continuous_projection_bundle(T, P)"},
		Conclusion: "continuous_projection_bundle(T, projection_exterior(T, P, e))",
	},
		"Cauchy–Binet identifies the matrix of exterior powers with minors and preserves "+
			"adjoints and composition; parity selects an orthogonal block. The square of the minor "+
			"matrix is the exterior power of P(x)·P(x) = P(x) (ExteriorPowerProduct); conjugating "+
			"a minor of a Hermitian matrix gives the transposed minor "+
			"(ModuleSumMonoidHomomorphism, ConjAdd, ConjMul, ExteriorPowerTranspose); determinants "+
			"of continuous entries are continuous (ContinuousComplexSum, ContinuousComplexProduct, "+
			"ContinuousComplexMul and continuous.Constant for the signs)."),
})}

// TrivialExterior — the exterior bundle of a trivial bundle is the diagonal
// projection onto the masks of one parity.
var TrivialExterior = trivialExteriorThm{family.Add(registry.ProofEntry{
	Name: "TrivialExterior",
	Key:  "prop_35fac67feb07863c",
	Deps: []registry.EntryLike{
		exteriorDef,
		projection_bundle.TrivialDef,
		exterior_basis.ExteriorPowerIdentity,
		complex_field.CommRingOn,
	},
	Build: family.Card(
		"∀T:set(set(A)). ∀r e:num. "+
			"    projection_exterior(T, projection_trivial(T, r), e) = "+
			"    (nat_pow(2, r), "+
			"        λx:A. λa:num. λb:num. "+
			"            COND( "+
			"                x ∈ ⋃T ∧ a < nat_pow(2, r) ∧ a = b ∧ nat_mod(card(exterior_mask(r, a)), 2) = e, "+
			"                complex_of_real(&1), "+
			"                complex_of_real(&0)))",
		"At x ∈ ⋃T the matrix of the trivial bundle is matrix_identity(complex_ring, r) "+
			"(projection_bundle.TrivialDef), and exterior_basis.ExteriorPowerIdentity, read at the "+
			"commutative ring ℂ (complex_field.CommRingOn), makes its exterior power the identity of "+
			"size 2ʳ. exteriorDef keeps the entries whose row mask has parity e and is zero off ⋃T."),
	Reading: "It holds for every T, r and e with no hypothesis: for e " +
		"≥ 2 both sides are the zero matrix, and off ⋃T both sides vanish.",
})}

var KoszulMap = koszulMapThm{family.Add(registry.ProofEntry{
	Name: "KoszulMap",
	Key:  "prop_bf51cc9ff22e7eec",
	Deps: []registry.EntryLike{
		ExteriorProjection,
		projection_bundle.PullbackBundle,
		topological_space.SubtopologyTopology,
		product_topology.ProductTopology,
		product_topology.FstContinuous,
		continuous.FromSubtopology,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
		},
		Conclusion: "continuous_projection_map(projection_total_topology(T, P), " +
			"    fst(koszul_triple(T, P)), " +
			"    fst(snd(koszul_triple(T, P))), " +
			"    koszul_projection_map(T, P))",
	},
		"Wedge and contraction preserve the exterior algebra of the "+
			"image when the fibre vector lies in it; both reverse parity."),
})}

var KoszulInvertible = koszulInvertibleThm{family.Add(registry.ProofEntry{
	Name: "KoszulInvertible",
	Key:  "prop_6a87e4998e93664c",
	Deps: []registry.EntryLike{KoszulMap},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). ∀p:prod(A, num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"p ∈ projection_total_space(T, P)",
			"snd(p) ≠ (λi:num. complex_of_real(&0))",
		},
		Conclusion: "projection_invertible_at(fst(koszul_triple(T, P)), " +
			"    fst(snd(koszul_triple(T, P))), " +
			"    koszul_projection_map(T, P), " +
			"    p)",
	},
		"The anticommutator of wedge by v and contraction by v is the squared norm "+
			"times the identity. Divide the adjoint by that positive squared norm."),
})}

var KoszulCompactSupport = koszulCompactSupportThm{family.Add(registry.ProofEntry{
	Name: "KoszulCompactSupport",
	Key:  "prop_216a29442ee99f47",
	Deps: []registry.EntryLike{KoszulInvertible},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "kc_supported_in(projection_total_topology(T, P), " +
			"    {p:prod(A, num → complex) | fst(p) ∈ ⋃T ∧ snd(p) = (λi:num. complex_of_real(&0))}, " +
			"    koszul_triple(T, P))",
	}, "The only possible singularities are on the zero section, which is a compact copy of the base."),
})}

var ThomCompactSupport = thomCompactSupportThm{family.Add(registry.ProofEntry{
	Name: "ThomCompactSupport",
	Key:  "prop_9855866109298775",
	Deps: []registry.EntryLike{KoszulInvertible},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"kc_triple(T, a)",
		},
		Conclusion: "kc_triple(projection_total_topology(T, P), " +
			"    kc_triple_product(kc_triple_pullback(projection_total_topology(T, P), " +
			"            λp:prod(A, num → complex). fst(p), " +
			"            a), " +
			"        koszul_triple(T, P)))",
	},
		"The product is invertible away from the zero section over "+
			"the original compact singular support; this set is compact."),
})}

// ThomMapDescends — the Thom map sends a compactly supported class to the class of the Thom
// product of any of its triples.
var ThomMapDescends = thomMapDescendsThm{family.Add(registry.ProofEntry{
	Name: "ThomMapDescends",
	Key:  "prop_1084087cd33cdaa6",
	Deps: []registry.EntryLike{
		ThomMapDef,
		ThomCompactSupport,
		k_compact_support.Equivalence,
		k_compact_support.RelationDef,
		KoszulInvertible,
		equivalence.InducedMapClass,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"kc_triple(T, b)",
		},
		Conclusion: "kc_thom_map(T, P, kc_class(T, b)) = " +
			"kc_class(projection_total_topology(T, P), " +
			"    kc_triple_product(kc_triple_pullback(projection_total_topology(T, P), " +
			"            λp:prod(A, num → complex). fst(p), " +
			"            b), " +
			"        koszul_triple(T, P)))",
	},
		"kc_thom_map evaluates at the chosen representative of the class (ThomMapDef), so the formula "+
			"holds once kc_equivalent triples have kc_equivalent Thom products "+
			"(relations/equivalence.InducedMapClass with k_compact_support.Equivalence). The product with "+
			"the Koszul triple is a triple with compact singular support (ThomCompactSupport). It carries "+
			"the generating relation (k_compact_support.RelationDef) along: the zero triple goes to the "+
			"zero triple; the product of a sum is a constant block permutation of the sum of the products, "+
			"homotopic to it along a unitary path from the identity; a degenerate triple gives a degenerate "+
			"product; and a homotopy's product is invertible off the zero section (KoszulInvertible), so "+
			"its singular support lies in the image of the homotopy's under (x, t) ↦ ((x, 0), t), compact — "+
			"fst × id is not proper, and the Koszul factor, not the pullback, bounds it."),
	Reading: "No local compactness or separation of T is used: " +
		"the Koszul factor alone makes the product's support compact.",
})}

var ThomHomomorphism = thomHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "ThomHomomorphism",
	Key:  "prop_22144283d47d73bd",
	Deps: []registry.EntryLike{ThomCompactSupport, ThomMapDescends, k_compact_support.ExternalDescends},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"locally_compact_space(T)",
			"hausdorff(T)",
		},
		Conclusion: "group_homomorphism(kc_group(T), " +
			"    kc_group(projection_total_topology(T, P)), " +
			"    kc_thom_map(T, P))",
	},
		"The product preserves the relative generating relations "+
			"with compact support, hence descends to the group."),
})}

var ThomIsomorphism = thomIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ThomIsomorphism",
	Key:  "prop_5ce2e579b71c2f64",
	Deps: []registry.EntryLike{
		ThomHomomorphism,
		TrivialBundleThom,
		TwoOpenThomGluing,
		CompactRelationLocalization,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"locally_compact_space(T)",
			"hausdorff(T)",
		},
		Conclusion: "group_isomorphism(kc_group(T), " +
			"    kc_group(projection_total_topology(T, P)), " +
			"    kc_thom_map(T, P))",
	},
		"Cover the compact supports of a class or an equality by finitely many bundle "+
			"trivializations. The trivial-bundle result uses locally compact Bott; two-open "+
			"gluing applies also to suspensions. Compact localization of the relative relations "+
			"passes the resulting isomorphism from that neighborhood to the full base."),
})}

var CompactThomIsomorphism = compactThomIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "CompactThomIsomorphism",
	Key:  "prop_217c38f23c54e3bc",
	Deps: []registry.EntryLike{ThomIsomorphism, bott_periodicity.CompactInverse},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "group_isomorphism(additive_group(k_ring(T)), " +
			"    kc_group(projection_total_topology(T, P)), " +
			"    k_thom_map(T, P))",
	}, "Compose the compact relative comparison with the compact-support Thom isomorphism."),
})}

var TrivialBundleThom = trivialBundleThomThm{family.Add(registry.ProofEntry{
	Name: "TrivialBundleThom",
	Key:  "prop_8c8b7eed1c40cbef",
	Deps: []registry.EntryLike{
		bott_periodicity.CompactSupportBott,
		TrivialExterior,
		k_compact_support.HomeomorphismPullbackIsomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). ∀r:num.",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"projection_isomorphic(T, P, projection_trivial(T, r))",
		},
		Conclusion: "kc_thom_isomorphism(T, P)",
	},
		"A bundle isomorphism has a fibrewise polar unitary representative. Koszul naturality "+
			"transports the map to the trivial rank-r bundle, whose exterior bundles are the parity "+
			"diagonals (TrivialExterior) and whose Thom class is the r-fold product of the compact-support "+
			"Bott class. Iterate the locally compact Bott isomorphism, including rank zero, carrying "+
			"classes between the total space and T × ℂʳ by HomeomorphismPullbackIsomorphism."),
})}

var TwoOpenThomGluing = twoOpenThomGluingThm{family.Add(registry.ProofEntry{
	Name: "TwoOpenThomGluing",
	Key:  "prop_4063ef96f3cf1672",
	Deps: []registry.EntryLike{
		k_compact_support.Excision,
		k_compact_support.OpenExtensionHomomorphism,
		bott_periodicity.CompactSupportBott,
		projection_bundle.TotalSpaceLocallyCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). ∀U V:set(A).",
		Hypotheses: []string{
			"continuous_projection_bundle(T, P)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"kc_thom_isomorphism(subtopology(T, U), projection_pullback(subtopology(T, U), λx:A. x, P)) ∧ " +
				"kc_thom_isomorphism(product_topology(subtopology(T, U), real_topology), " +
				"    projection_pullback(product_topology(subtopology(T, U), real_topology), " +
				"        λp:prod(A, real). fst(p), " +
				"        P))",
			"kc_thom_isomorphism(subtopology(T, V), projection_pullback(subtopology(T, V), λx:A. x, P)) ∧ " +
				"kc_thom_isomorphism(product_topology(subtopology(T, V), real_topology), " +
				"    projection_pullback(product_topology(subtopology(T, V), real_topology), " +
				"        λp:prod(A, real). fst(p), " +
				"        P))",
			"kc_thom_isomorphism(subtopology(T, U ∩ V), " +
				"    projection_pullback(subtopology(T, U ∩ V), λx:A. x, P)) ∧ " +
				"kc_thom_isomorphism(product_topology(subtopology(T, U ∩ V), real_topology), " +
				"    projection_pullback(product_topology(subtopology(T, U ∩ V), real_topology), " +
				"        λp:prod(A, real). fst(p), " +
				"        P))",
		},
		Conclusion: "kc_thom_isomorphism(T, P)",
	},
		"Relative triple pasting gives the Mayer–Vietoris comparison, with the "+
			"suspended overlap supplied explicitly. Compact-support Bott identifies "+
			"double suspension. The exact-sequence diagram then gives both injectivity "+
			"and surjectivity, with open-extension naturality of the Koszul product."),
})}

var CompactRelationLocalization = compactRelationLocalizationThm{family.Add(registry.ProofEntry{
	Name: "CompactRelationLocalization",
	Key:  "prop_35fcfb89ad4ab7c8",
	Deps: []registry.EntryLike{
		k_compact_support.Equivalence,
		compact.CompactUnion,
		continuous.ImageCompact,
		product_topology.FstContinuous,
		projection_bundle.PullbackBundle,
		k_compact_support.TripleSum,
		projection_bundle.TrivialBundle,
		compact.CompactInSubtopology,
		product_topology.PairedContinuousIff,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀a b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)).",
		Hypotheses: []string{
			"is_topology(T)",
			"kc_triple(T, a)",
			"kc_triple(T, b)",
			"kc_equivalent(T, a, b)",
		},
		Conclusion: "∃K:set(A). " +
			"    compact_in(T, K) ∧ " +
			"    kc_supported_in(T, K, a) ∧ " +
			"    kc_supported_in(T, K, b) ∧ " +
			"    (∀U:set(A). " +
			"        U ∈ T ∧ K ⊆ U ⇒ " +
			"        kc_equivalent(subtopology(T, U), " +
			"            kc_triple_pullback(subtopology(T, U), λx:A. x, a), " +
			"            kc_triple_pullback(subtopology(T, U), λx:A. x, b)))",
	},
		"A derivation in the generated equivalence uses only finitely many generators. Their "+
			"singular supports and the projected supports of their compact homotopies have a "+
			"compact union; restriction to an open neighborhood preserves each step. Read by "+
			"induction over the generating relation: the pairs with such a K form an equivalence on "+
			"triples (k_compact_support.Equivalence on each U, CompactUnion for the union of two "+
			"supports) holding the generators, a homotopy's support projected along fst being "+
			"compact (FstContinuous, ImageCompact), and restriction keeps bundles (PullbackBundle). "+
			"The sum clause takes the union with the added triple's support, restriction commuting "+
			"with kc_triple_sum (TripleSum); the zero triple is a triple (TrivialBundle), and the "+
			"ends of a homotopy are its pullbacks along x ↦ (x, 0) and (x, 1) (PairedContinuousIff)."),
})}
