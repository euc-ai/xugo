package definable_andre_quillen

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/milnor_sequence"
	"github.com/euc-ai/xugo/library/registry"
)

var AQUnionTowerDef = aQUnionTowerDefThm{family.Define(registry.DefEntry{
	Name:  "AQUnionTowerDef",
	Key:   "prop_ba599baf8ad92770",
	Const: "aq_union_tower",
	Type: "ring_ops(A) → " +
		"(num → ring_ops(B)) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"num → " +
		"complex_ops(B, U → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀V:(num → ring_ops(B)). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀k:num. " +
			"    aq_union_tower(R, V, S, f, N)(k) = cotangent_cochain⟨U:U⟩(R, V(k), f, S, λy:B. y, N)",
	},
	Deps: []registry.EntryLike{},
	Reading: "Each stage uses the final coefficient ring S " +
		"and its module N; the scalar ring is common to the tower."})}

var AQUnionTransitionDef = aQUnionTransitionDefThm{family.Define(registry.DefEntry{
	Name:  "AQUnionTransitionDef",
	Key:   "prop_ec2eb1b6ad2b3f3",
	Const: "aq_union_transition",
	Type:  "ring_ops(A) → (num → ring_ops(B)) → module_ops(B, D) → num → num → (U → D) → U → D",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:(num → ring_ops(B)). ∀N:module_ops(B, D). ∀k n:num. ∀w:(U → D). ∀u:U. " +
			"    aq_union_transition(R, V, N, k, n, w, u) = " +
			"    COND(u ∈ standard_names(R, V(k), n), " +
			"        w(standard_name_map(R, V(k), V(k + 1), λy:B. y, n, u)), " +
			"        N.zero)",
	},
	Deps:    []registry.EntryLike{},
	Reading: "Restriction along the injective name map, normalized off the source names."})}

var aqUnionComparisonDef = aqUnionComparisonDefThm{family.Define(registry.DefEntry{
	Name:  "aqUnionComparisonDef",
	Key:   "prop_64c266e50ea88580",
	Const: "aq_union_comparison",
	Type: "ring_ops(A) → " +
		"(num → ring_ops(B)) → " +
		"ring_ops(B) → " +
		"module_ops(B, D) → " +
		"num → " +
		"(U → D) → " +
		"num → " +
		"U → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀V:(num → ring_ops(B)). " +
			"∀S:ring_ops(B). " +
			"∀N:module_ops(B, D). " +
			"∀n:num. " +
			"∀w:(U → D). " +
			"∀k:num. " +
			"∀u:U. " +
			"    aq_union_comparison(R, V, S, N, n, w, k, u) = " +
			"    COND(u ∈ standard_names(R, V(k), n), w(standard_name_map(R, V(k), S, λy:B. y, n, u)), N.zero)",
	},
	Deps: []registry.EntryLike{},
	Reading: "The canonical comparison sends a cochain " +
		"on the union to its compatible stage restrictions."})}

var AQUnionComplexLimit = aQUnionComplexLimitThm{family.Add(registry.ProofEntry{
	Name: "AQUnionComplexLimit",
	Key:  "prop_d34163d7b5316a97",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀V:(num → ring_ops(B)). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D).",
			Hypotheses: []string{
				"increasing_algebra_union(R, V, S, f)",
				"module_on(S, N)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
				"∀k:num. cotangent_universe(V(k), 𝕌⟨A:U⟩)",
			},
			Conclusion: "complex_tower(S, " +
				"    aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"    aq_union_transition⟨U:U⟩(R, V, N)) ∧ " +
				"complex_tower_onto(aq_union_tower⟨U:U⟩(R, V, S, f, N), aq_union_transition⟨U:U⟩(R, V, N)) ∧ " +
				"cochain_map(S, " +
				"    cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
				"    limit_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N), aq_union_transition⟨U:U⟩(R, V, N)), " +
				"    aq_union_comparison⟨U:U⟩(R, V, S, N)) ∧ " +
				"(∀n:num. " +
				"    homeomorphic_map(aq_topologies(R, S, N)(n), " +
				"        polish_limit_topologies(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"            aq_union_transition⟨U:U⟩(R, V, N), " +
				"            λk:num. dual_pointwise_topologies(N, standard_names⟨U:U⟩(R, V(k))), " +
				"            n), " +
				"        aq_union_comparison⟨U:U⟩(R, V, S, N)(n)))",
		},
		"StandardResolutionUnion gives compatible injective name maps and the union of their "+
			"images. Extend a stage function by zero to prove transition surjectivity. Compatible "+
			"functions glue uniquely and each inverse coordinate reads one sufficiently large "+
			"stage; naturality of the standard resolution gives the differential equation."),
	Deps: []registry.EntryLike{
		AQUnionTowerDef,
		AQUnionTransitionDef,
		aqUnionComparisonDef,
		standard_resolution.StandardResolutionUnion,
		AQAlgebraMapContinuous,
		cotangent_complex.CotangentMapsDualAgreement,
	},
	Reading: "StandardResolutionUnion gives compatible injective name maps and the union " +
		"of their images. Extend a stage function by zero to prove transition surjectivity. " +
		"Compatible functions glue uniquely and each inverse coordinate reads one sufficiently " +
		"large stage; naturality of the standard resolution gives the differential equation.",
})}

var AQTowerPolishModel = aQTowerPolishModelThm{family.Add(registry.ProofEntry{
	Name: "AQTowerPolishModel",
	Key:  "prop_9467a53eefa27a23",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀V:(num → ring_ops(B)). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D).",
			Hypotheses: []string{
				"increasing_algebra_union(R, V, S, f)",
				"module_on(S, N)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
				"∀k:num. cotangent_universe(V(k), 𝕌⟨A:U⟩)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
			},
			Conclusion: "polish_complex_tower(S, " +
				"    aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"    aq_union_transition⟨U:U⟩(R, V, N), " +
				"    λk:num. dual_pointwise_topologies(N, standard_names⟨U:U⟩(R, V(k)))) ∧ " +
				"polish_cochain_map(S, " +
				"    cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
				"    aq_topologies(R, S, N), " +
				"    limit_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N), aq_union_transition⟨U:U⟩(R, V, N)), " +
				"    polish_limit_topologies(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"        aq_union_transition⟨U:U⟩(R, V, N), " +
				"        λk:num. dual_pointwise_topologies(N, standard_names⟨U:U⟩(R, V(k)))), " +
				"    aq_union_comparison⟨U:U⟩(R, V, S, N))",
		},
		"Each stage is countable as a subset of S. AQScalarPolishModel and AQUnionComplexLimit "+
			"give the tower and its continuous comparison; PolishComplexTowerModel supplies the limit."),
	Deps: []registry.EntryLike{
		AQUnionComplexLimit,
		AQScalarPolishModel,
		milnor_sequence.PolishComplexTowerModel,
	},
	Reading: "Each stage is countable as a subset of S. AQScalarPolishModel and AQUnionComplexLimit " +
		"give the tower and its continuous comparison; PolishComplexTowerModel supplies the limit.",
})}

var AQMilnorSequence = aQMilnorSequenceThm{family.Add(registry.ProofEntry{
	Name: "AQMilnorSequence",
	Key:  "prop_ad382dc7007aa8df",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀V:(num → ring_ops(B)). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D). " +
				"∀n:num.",
			Hypotheses: []string{
				"increasing_algebra_union(R, V, S, f)",
				"module_on(S, N)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
				"∀k:num. cotangent_universe(V(k), 𝕌⟨A:U⟩)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
			},
			Conclusion: "image(product_class_map(aq_union_tower⟨U:U⟩(R, V, S, f, N), n + 1), " +
				"    image(cohomology_map(product_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"            λj:num. λs:(num → U → D). s, " +
				"            n + 1), " +
				"        cohomology(limit_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                aq_union_transition⟨U:U⟩(R, V, N)), " +
				"            n + 1))) = " +
				"inverse_limit(cohomology_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N), n + 1), " +
				"    cohomology_tower_maps(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"        aq_union_transition⟨U:U⟩(R, V, N), " +
				"        n + 1)) ∧ " +
				"(∀c:set(num → U → D). " +
				"    c ∈ cohomology(product_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N)), n) ⇒ " +
				"    (coconnecting_hom(limit_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                aq_union_transition⟨U:U⟩(R, V, N)), " +
				"            product_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"            λj:num. λs:(num → U → D). s, " +
				"            product_shift(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                aq_union_transition⟨U:U⟩(R, V, N)), " +
				"            n)(c) = " +
				"        coboundaries(limit_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                aq_union_transition⟨U:U⟩(R, V, N)), " +
				"            n + 1) ⇔ " +
				"        product_class_map(aq_union_tower⟨U:U⟩(R, V, S, f, N), n, c) ∈ " +
				"        image(tower_shift(cohomology_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N), n), " +
				"                cohomology_tower_maps(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                    aq_union_transition⟨U:U⟩(R, V, N), " +
				"                    n)), " +
				"            tower_terms(cohomology_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N), n), 0)))) ∧ " +
				"cohomology_borel_map(product_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"    polish_product_topologies(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"        λk:num. dual_pointwise_topologies(N, standard_names⟨U:U⟩(R, V(k)))), " +
				"    n, " +
				"    limit_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N), aq_union_transition⟨U:U⟩(R, V, N)), " +
				"    polish_limit_topologies(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"        aq_union_transition⟨U:U⟩(R, V, N), " +
				"        λk:num. dual_pointwise_topologies(N, standard_names⟨U:U⟩(R, V(k)))), " +
				"    n + 1, " +
				"    coconnecting_hom( " +
				"        limit_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N), aq_union_transition⟨U:U⟩(R, V, N)), " +
				"        product_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"        λj:num. λs:(num → U → D). s, " +
				"        product_shift(aq_union_tower⟨U:U⟩(R, V, S, f, N), aq_union_transition⟨U:U⟩(R, V, N)), " +
				"        n))",
		},
		"Apply MilnorLimitImage, MilnorDerivedLimitKernel and "+
			"PolishMilnorConnectingDefinable. AQUnionComplexLimit identifies the middle term "+
			"with D^(n+1)(S/R,N); exactness is the long exact sequence of ComplexTowerShortExact."),
	Deps: []registry.EntryLike{
		AQTowerPolishModel,
		AQUnionComplexLimit,
		milnor_sequence.MilnorLimitImage,
		milnor_sequence.MilnorDerivedLimitKernel,
		milnor_sequence.PolishMilnorConnectingDefinable,
	},
	Reading: "Positive degrees use n+1 so no negative natural-number " +
		"degree is hidden. The lim-one term has the presentation induced by " +
		"the connecting map, not an assumed Polish topology on stage cohomology.",
})}

var AQMilnorDegreeZero = aQMilnorDegreeZeroThm{family.Add(registry.ProofEntry{
	Name: "AQMilnorDegreeZero",
	Key:  "prop_e161f48f7131724b",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀V:(num → ring_ops(B)). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D).",
			Hypotheses: []string{
				"increasing_algebra_union(R, V, S, f)",
				"module_on(S, N)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
				"∀k:num. cotangent_universe(V(k), 𝕌⟨A:U⟩)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
			},
			Conclusion: "module_isomorphism(S, " +
				"    cohomology_module(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 0), " +
				"    mk_module(sequence_module(cohomology_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N), 0)).add, " +
				"        sequence_module(cohomology_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N), 0)).zero, " +
				"        sequence_module(cohomology_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N), 0)).neg, " +
				"        sequence_module(cohomology_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N), 0)).smul, " +
				"        inverse_limit(cohomology_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N), 0), " +
				"            cohomology_tower_maps(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                aq_union_transition⟨U:U⟩(R, V, N), " +
				"                0))), " +
				"    λc:set(U → D). " +
				"        product_class_map(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"            0, " +
				"            cohomology_map(product_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"                λj:num. λs:(num → U → D). s, " +
				"                0, " +
				"                cohomology_map(limit_complex(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                        aq_union_transition⟨U:U⟩(R, V, N)), " +
				"                    aq_union_comparison⟨U:U⟩(R, V, S, N), " +
				"                    0, " +
				"                    c))))",
		},
		"There are no incoming degree-zero boundaries. Compatible zero cocycles are precisely "+
			"zero cocycles of the limit, and AQUnionComplexLimit supplies the comparison."),
	Deps: []registry.EntryLike{AQUnionComplexLimit, milnor_sequence.ProductCohomologyClasses},
	Reading: "There are no incoming degree-zero boundaries. Compatible zero cocycles are " +
		"precisely zero cocycles of the limit, and AQUnionComplexLimit supplies the comparison.",
})}
