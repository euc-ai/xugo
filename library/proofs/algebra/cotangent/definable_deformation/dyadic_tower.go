package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_andre_quillen"
	"github.com/euc-ai/xugo/library/registry"
)

var DyadicDerivationTower = dyadicDerivationTowerThm{family.Add(registry.ProofEntry{
	Name: "DyadicDerivationTower",
	Key:  "prop_6cbb5017dbd711e2",
	Build: family.Card(
		Statement{
			Binders: "∀V:(num → ring_ops(num)). " +
				"∀S:ring_ops(num). " +
				"∀f:(int → num). " +
				"∀a:(num → int). " +
				"∀φ:(num → num → num).",
			Hypotheses: []string{
				"dyadic_polynomial_union(V, S, f, a, φ)",
				"cotangent_universe(int_ring, 𝕌⟨A:num⟩)",
				"cotangent_universe(S, 𝕌⟨A:num⟩)",
				"∀k:num. cotangent_universe(V(k), 𝕌⟨A:num⟩)",
			},
			Conclusion: "(∀k:num. " +
				"    group_isomorphism(cocycle_group(aq_union_tower⟨U:num⟩(int_ring, " +
				"                V, " +
				"                S, " +
				"                f, " +
				"                scalar_restriction(a, regular_module(int_ring)))(k), " +
				"            0), " +
				"        module_additive_group(regular_module(int_ring)), " +
				"        λc:(num → int). " +
				"            c(carrier_tag⟨B:num, U:num⟩(V(k).carrier, " +
				"                    φ(k, universe_algebra_var⟨A:int, U:num⟩(int_ring, 0))))) ∧ " +
				"    homeomorphic_map(cocycle_topology(aq_union_tower⟨U:num⟩(int_ring, " +
				"                V, " +
				"                S, " +
				"                f, " +
				"                scalar_restriction(a, regular_module(int_ring)))(k), " +
				"            (λk:num. " +
				"                dual_pointwise_topologies(scalar_restriction(a, regular_module(int_ring)), " +
				"                    standard_names⟨U:num⟩(int_ring, V(k))))(k), " +
				"            0), " +
				"        {s:set(int) | s ⊆ int_ring.carrier}, " +
				"        λc:(num → int). " +
				"            c(carrier_tag⟨B:num, U:num⟩(V(k).carrier, " +
				"                    φ(k, universe_algebra_var⟨A:int, U:num⟩(int_ring, 0)))))) ∧ " +
				"(∀k:num. ∀c:(num → int). " +
				"    c ∈ " +
				"    cocycles(aq_union_tower⟨U:num⟩(int_ring, " +
				"            V, " +
				"            S, " +
				"            f, " +
				"            scalar_restriction(a, regular_module(int_ring)))(k + 1), " +
				"        0) ⇒ " +
				"    (λc:(num → int). " +
				"        c(carrier_tag⟨B:num, U:num⟩(V(k).carrier, " +
				"                φ(k, universe_algebra_var⟨A:int, U:num⟩(int_ring, 0)))))(aq_union_transition⟨ " +
				"            U:num⟩(int_ring, V, scalar_restriction(a, regular_module(int_ring)))(k, 0, c)) = " +
				"    2 * " +
				"    (λc:(num → int). " +
				"        c(carrier_tag⟨B:num, U:num⟩(V(k + 1).carrier, " +
				"                φ(k + 1, universe_algebra_var⟨A:int, U:num⟩(int_ring, 0)))))(c))",
		},
		"The degree-zero AQ cocycle is the normalized derivation, and a derivation "+
			"of Z[x_k] with zero-augmentation coefficients is uniquely determined by "+
			"its value on x_k. Evaluation and reconstruction read finitely many "+
			"coordinates. The transition x_k=2x_(k+1) multiplies this value by two."),
	Deps: []registry.EntryLike{
		dyadicPolynomialUnionDef,
		definable_andre_quillen.DerivationModelHomeomorphism,
		definable_andre_quillen.AQUnionComplexLimit,
	},
	Reading: "The degree-zero AQ cocycle is the normalized derivation, and a " +
		"derivation of Z[x_k] with zero-augmentation coefficients is uniquely " +
		"determined by its value on x_k. Evaluation and reconstruction read finitely " +
		"many coordinates. The transition x_k=2x_(k+1) multiplies this value by two.",
})}
