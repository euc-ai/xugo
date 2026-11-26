package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_andre_quillen"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/dyadic_integers"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/registry"
)

var dyadicPolynomialUnionDef = dyadicPolynomialUnionDefThm{family.Define(registry.DefEntry{
	Name:  "dyadicPolynomialUnionDef",
	Key:   "prop_4b6a0e8fe9e2b4d3",
	Const: "dyadic_polynomial_union",
	Type: "(num → ring_ops(num)) → " +
		"ring_ops(num) → " +
		"(int → num) → " +
		"(num → int) → " +
		"(num → num → num) → " +
		"bool",
	Equations: []string{
		"∀V:(num → ring_ops(num)). " +
			"∀S:ring_ops(num). " +
			"∀f:(int → num). " +
			"∀a:(num → int). " +
			"∀φ:(num → num → num). " +
			"    dyadic_polynomial_union(V, S, f, a, φ) ⇔ " +
			"    increasing_algebra_union(int_ring, V, S, f) ∧ " +
			"    ring_homomorphism(S, int_ring, a) ∧ " +
			"    (∀r:int. a(f(r)) = r) ∧ " +
			"    (∀k:num. " +
			"        ring_isomorphism(universe_algebra_ring⟨A:int, U:num⟩(int_ring, {0}), V(k), φ(k)) ∧ " +
			"        (∀r:int. φ(k, universe_algebra_const⟨A:int, U:num⟩(int_ring, r)) = f(r)) ∧ " +
			"        a(φ(k, universe_algebra_var⟨A:int, U:num⟩(int_ring, 0))) = 0 ∧ " +
			"        φ(k, universe_algebra_var⟨A:int, U:num⟩(int_ring, 0)) = " +
			"        S.mul(f(2), φ(k + 1, universe_algebra_var⟨A:int, U:num⟩(int_ring, 0))))",
	},
	Deps: []registry.EntryLike{},
	Reading: "An increasing union of polynomial integer rings whose variable " +
		"at stage k is twice the next variable, with the zero augmentation."})}

var DyadicPolynomialUnionExists = dyadicPolynomialUnionExistsThm{family.Add(registry.ProofEntry{
	Name: "DyadicPolynomialUnionExists",
	Key:  "prop_253d161583d71c1",
	Build: family.Card(
		Statement{
			Binders:    "",
			Hypotheses: []string{},
			Conclusion: "∃V:(num → ring_ops(num)). " +
				"∃S:ring_ops(num). " +
				"∃f:(int → num). " +
				"∃a:(num → int). " +
				"∃φ:(num → num → num). " +
				"    dyadic_polynomial_union(V, S, f, a, φ)",
		},
		"Construct the injective direct limit of Z[x] under x↦2x, or the "+
			"subring Z+x Z[1/2][x] in Q[x], and enumerate its countable carrier. "+
			"Its stages are Z[x/2^k], and evaluation at zero is the augmentation."),
	Deps: []registry.EntryLike{dyadicPolynomialUnionDef},
	Reading: "Construct the injective direct limit of Z[x] under x↦2x, or " +
		"the subring Z+x Z[1/2][x] in Q[x], and enumerate its countable carrier. " +
		"Its stages are Z[x/2^k], and evaluation at zero is the augmentation.",
})}

var DyadicPhantomExtensions = dyadicPhantomExtensionsThm{family.Add(registry.ProofEntry{
	Name: "DyadicPhantomExtensions",
	Key:  "prop_273f2e9837cee27e",
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
			Conclusion: "card_le(𝕌⟨A:set(num)⟩, " +
				"    image(λz:(num → int). " +
				"            left_coset(cotangent_cochain⟨U:num⟩(int_ring, " +
				"                    S, " +
				"                    f, " +
				"                    S, " +
				"                    λy:num. y, " +
				"                    scalar_restriction(a, regular_module(int_ring))).add, " +
				"                z, " +
				"                coboundaries(cotangent_cochain⟨U:num⟩(int_ring, " +
				"                        S, " +
				"                        f, " +
				"                        S, " +
				"                        λy:num. y, " +
				"                        scalar_restriction(a, regular_module(int_ring))), " +
				"                    1)), " +
				"        aq_phantom_representatives⟨U:num⟩(int_ring, " +
				"            V, " +
				"            S, " +
				"            f, " +
				"            scalar_restriction(a, regular_module(int_ring))))) ∧ " +
				"(∀c:set(num → int). " +
				"    c ∈ " +
				"    image(λz:(num → int). " +
				"            left_coset(cotangent_cochain⟨U:num⟩(int_ring, " +
				"                    S, " +
				"                    f, " +
				"                    S, " +
				"                    λy:num. y, " +
				"                    scalar_restriction(a, regular_module(int_ring))).add, " +
				"                z, " +
				"                coboundaries(cotangent_cochain⟨U:num⟩(int_ring, " +
				"                        S, " +
				"                        f, " +
				"                        S, " +
				"                        λy:num. y, " +
				"                        scalar_restriction(a, regular_module(int_ring))), " +
				"                    1)), " +
				"        aq_phantom_representatives⟨U:num⟩(int_ring, " +
				"            V, " +
				"            S, " +
				"            f, " +
				"            scalar_restriction(a, regular_module(int_ring)))) ⇒ " +
				"    ∃z:prod(prod(num, num) → int, prod(prod(num, num) → int, int → int)). " +
				"        z ∈ factor_set_codes(int_ring, S, f, scalar_restriction(a, regular_module(int_ring))) ∧ " +
				"        square_zero_class⟨U:num⟩(int_ring, " +
				"            S, " +
				"            f, " +
				"            scalar_restriction(a, regular_module(int_ring)), " +
				"            factor_set_extension(S, f, scalar_restriction(a, regular_module(int_ring)), z)) = " +
				"        c)",
		},
		"Evaluate a derivation on x_k to identify its normalized Polish group "+
			"with discrete Z. Restriction evaluates at 2x_(k+1), so the tower map is "+
			"multiplication by two. DyadicDerivedLimit identifies lim-one with Z_2/Z "+
			"and gives continuum many classes; PhantomExtensionsDerivedLimit and "+
			"FactorSetAQDefinableIso realize all of them as actual coded extensions."),
	Deps: []registry.EntryLike{
		dyadicPolynomialUnionDef,
		DyadicDerivationTower,
		dyadic_integers.DyadicDerivedLimit,
		definable_andre_quillen.PhantomExtensionsDerivedLimit,
		FactorSetAQDefinableIso,
	},
	Reading: "Every displayed class splits at every polynomial stage. " +
		"Its nonsplitting is global; the cardinal conclusion is about " +
		"distinct marked extension classes, not only cocycle representatives.",
})}
