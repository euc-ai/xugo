package definable_andre_quillen

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/derived_limit"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/milnor_sequence"
	"github.com/euc-ai/xugo/library/registry"
)

var aqUnionInverseDef = aqUnionInverseDefThm{family.Define(registry.DefEntry{
	Name:  "aqUnionInverseDef",
	Key:   "prop_eff4c5bd903f1b60",
	Const: "aq_union_inverse",
	Type: "ring_ops(A) → " +
		"(num → ring_ops(B)) → " +
		"ring_ops(B) → " +
		"module_ops(B, D) → " +
		"num → " +
		"(num → U → D) → " +
		"U → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:(num → ring_ops(B)). ∀S:ring_ops(B). ∀N:module_ops(B, D). ∀n:num. " +
			"    aq_union_inverse(R, V, S, N, n) = " +
			"    inverse_on(indexed_functions(standard_names(R, S, n), λu:U. N.zero, λu:U. N.carrier), " +
			"        aq_union_comparison(R, V, S, N, n))",
	},
	Deps: []registry.EntryLike{aqUnionComparisonDef},
	Reading: "Glue a compatible sequence of stage " +
		"cochains to the unique normalized global cochain."})}

var AQPhantomRepresentativesDef = aQPhantomRepresentativesDefThm{family.Define(registry.DefEntry{
	Name:  "AQPhantomRepresentativesDef",
	Key:   "prop_2c457ff1d36832ef",
	Const: "aq_phantom_representatives",
	Type: "ring_ops(A) → " +
		"(num → ring_ops(B)) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:(num → ring_ops(B)). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). " +
			"    aq_phantom_representatives(R, V, S, f, N) = " +
			"    {z:(U → D) | " +
			"        z ∈ cocycles(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1) ∧ " +
			"        (∀k:num. " +
			"            aq_union_comparison⟨U:U⟩(R, V, S, N)(1, z, k) ∈ " +
			"            coboundaries(aq_union_tower⟨U:U⟩(R, V, S, f, N)(k), 1))}",
	},
	Deps:    []registry.EntryLike{aqUnionComparisonDef, AQUnionTowerDef},
	Reading: "Global degree-one AQ cocycles whose class restricts to zero at every stage."})}

var PhantomExtensionsDerivedLimit = phantomExtensionsDerivedLimitThm{family.Add(registry.ProofEntry{
	Name: "PhantomExtensionsDerivedLimit",
	Key:  "prop_743e92a4e937fcf4",
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
			Conclusion: "borel_cover_map(cocycle_group(tower_complex( " +
				"            zero_cocycle_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"            λk:num. aq_union_transition⟨U:U⟩(R, V, N)(k, 0)), " +
				"        1), " +
				"    cocycle_topology(tower_complex(zero_cocycle_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"            λk:num. aq_union_transition⟨U:U⟩(R, V, N)(k, 0)), " +
				"        polish_tower_topologies(zero_cocycle_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"            λk:num. " +
				"                cocycle_topology(aq_union_tower⟨U:U⟩(R, V, S, f, N)(k), " +
				"                    (λk:num. dual_pointwise_topologies(N, standard_names(R, V(k))))(k), " +
				"                    0)), " +
				"        1), " +
				"    coboundaries(tower_complex(zero_cocycle_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"            λk:num. aq_union_transition⟨U:U⟩(R, V, N)(k, 0)), " +
				"        1), " +
				"    cocycle_group(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1), " +
				"    cocycle_topology(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
				"        aq_topologies(R, S, N), " +
				"        1), " +
				"    coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1), " +
				"    λc:set(num → U → D). " +
				"        cohomology_map(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
				"            aq_union_inverse(R, V, S, N), " +
				"            1, " +
				"            milnor_zero_connecting(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                aq_union_transition⟨U:U⟩(R, V, N))(c))) ∧ " +
				"injective_on(cohomology(tower_complex(zero_cocycle_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"            λk:num. aq_union_transition⟨U:U⟩(R, V, N)(k, 0)), " +
				"        1), " +
				"    λc:set(num → U → D). " +
				"        cohomology_map(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
				"            aq_union_inverse(R, V, S, N), " +
				"            1, " +
				"            milnor_zero_connecting(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                aq_union_transition⟨U:U⟩(R, V, N))(c))) ∧ " +
				"image(λc:set(num → U → D). " +
				"        cohomology_map(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
				"            aq_union_inverse(R, V, S, N), " +
				"            1, " +
				"            milnor_zero_connecting(aq_union_tower⟨U:U⟩(R, V, S, f, N), " +
				"                aq_union_transition⟨U:U⟩(R, V, N))(c)), " +
				"    cohomology(tower_complex(zero_cocycle_tower(aq_union_tower⟨U:U⟩(R, V, S, f, N)), " +
				"            λk:num. aq_union_transition⟨U:U⟩(R, V, N)(k, 0)), " +
				"        1)) = " +
				"image(λz:(U → D). " +
				"        left_coset(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N).add, " +
				"            z, " +
				"            coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1)), " +
				"    aq_phantom_representatives⟨U:U⟩(R, V, S, f, N))",
		},
		"Apply PolishMilnorPhantom and its inverse representative lift, then transport "+
			"through AQUnionComplexLimit. DerivationModelHomeomorphism identifies stage "+
			"zero cocycles with normalized Der_R(V_k,N), compatibly with restriction."),
	Deps: []registry.EntryLike{
		aqUnionInverseDef,
		AQPhantomRepresentativesDef,
		AQTowerPolishModel,
		AQUnionComplexLimit,
		DerivationModelHomeomorphism,
		milnor_sequence.PolishMilnorPhantom,
		milnor_sequence.PolishMilnorPhantomInverse,
	},
	Reading: "The lim-one cover is the genuine Polish tower of derivations, " +
		"not a tower of discrete cochain terms. Under FactorSetAQDefinableIso " +
		"these classes are actual marked extensions split at every stage.",
})}

var PhantomZeroOrContinuum = phantomZeroOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "PhantomZeroOrContinuum",
	Key:  "prop_f81811e9af072737",
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
			Conclusion: "image(λz:(U → D). " +
				"        left_coset(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N).add, " +
				"            z, " +
				"            coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1)), " +
				"    aq_phantom_representatives⟨U:U⟩(R, V, S, f, N)) = " +
				"{coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1)} ∨ " +
				"card_le(𝕌⟨A:set(num)⟩, " +
				"    image(λz:(U → D). " +
				"            left_coset(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N).add, " +
				"                z, " +
				"                coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1)), " +
				"        aq_phantom_representatives⟨U:U⟩(R, V, S, f, N)))",
		},
		"Apply PolishDerivedLimitZeroOrContinuum to the zero-cocycle tower and "+
			"transfer its two alternatives through the injective phantom comparison."),
	Deps: []registry.EntryLike{
		PhantomExtensionsDerivedLimit,
		milnor_sequence.ZeroCocyclePolishTower,
		derived_limit.PolishDerivedLimitZeroOrContinuum,
	},
	Reading: "Apply PolishDerivedLimitZeroOrContinuum to the zero-cocycle tower " +
		"and transfer its two alternatives through the injective phantom comparison.",
})}
