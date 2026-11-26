package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_andre_quillen"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var reducedConormalCodesDef = reducedConormalCodesDefThm{family.Define(registry.DefEntry{
	Name:  "reducedConormalCodesDef",
	Key:   "prop_23c0a5b856c365ea",
	Const: "reduced_conormal_codes",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → module_ops(B, D) → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). " +
			"    reduced_conormal_codes(R, S, f, N) = " +
			"    {h:(U → D) | " +
			"        conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"            S, " +
			"            standard_eps(R, S, f), " +
			"            N, " +
			"            h) ∧ " +
			"        h(universe_algebra_var(R, carrier_tag(S.carrier, S.zero))) = N.zero}",
	},
	Deps: []registry.EntryLike{},
	Reading: "Conormal maps that vanish at the zero generator. This removes " +
		"the contractible coefficient summand forced by a zero-preserving section."})}

var conormalFactorSetDef = conormalFactorSetDefThm{family.Define(registry.DefEntry{
	Name:  "conormalFactorSetDef",
	Key:   "prop_b7bbdac46fe9fc34",
	Const: "conormal_factor_set",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(B, D) → " +
		"(U → D) → " +
		"prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D). ∀h:(U → D). " +
			"    conormal_factor_set(R, S, f, N, h) = " +
			"    (λp:prod(B, B). " +
			"        COND(p ∈ set_cross(S.carrier, S.carrier), " +
			"            h(universe_algebra_ring(R, standard_names(R, S, 0)).sub(universe_algebra_ring(R, " +
			"                        standard_names(R, S, 0)).add( " +
			"                        universe_algebra_var(R, carrier_tag(S.carrier, fst(p))), " +
			"                        universe_algebra_var(R, carrier_tag(S.carrier, snd(p)))), " +
			"                    universe_algebra_var(R, carrier_tag(S.carrier, S.add(fst(p), snd(p)))))), " +
			"            N.zero), " +
			"    (λp:prod(B, B). " +
			"        COND(p ∈ set_cross(S.carrier, S.carrier), " +
			"            h(universe_algebra_ring(R, standard_names(R, S, 0)).sub(universe_algebra_ring(R, " +
			"                        standard_names(R, S, 0)).mul( " +
			"                        universe_algebra_var(R, carrier_tag(S.carrier, fst(p))), " +
			"                        universe_algebra_var(R, carrier_tag(S.carrier, snd(p)))), " +
			"                    universe_algebra_var(R, carrier_tag(S.carrier, S.mul(fst(p), snd(p)))))), " +
			"            N.zero), " +
			"    λr:A. " +
			"        COND(r ∈ R.carrier, " +
			"            h(universe_algebra_ring(R, standard_names(R, S, 0)).sub( " +
			"                    universe_algebra_const(R, r), " +
			"                    universe_algebra_var(R, carrier_tag(S.carrier, f(r))))), " +
			"            N.zero)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Evaluate a conormal map on the additive, multiplicative " +
		"and base-ring relations, with zero off their carriers."})}

var FactorSetConormalAgreement = factorSetConormalAgreementThm{family.Add(registry.ProofEntry{
	Name: "FactorSetConormalAgreement",
	Key:  "prop_c74821d28b69b7fb",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
			},
			Conclusion: "homeomorphic_map(subtopology(indexed_discrete_topology( " +
				"            ring_kernel(S.zero, standard_terms(R, S, 0), standard_eps(R, S, f)), " +
				"            λx:U. N.zero, " +
				"            λx:U. N.carrier), " +
				"        reduced_conormal_codes(R, S, f, N)), " +
				"    subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    conormal_factor_set(R, S, f, N)) ∧ " +
				"image(conormal_factor_set(R, S, f, N), " +
				"    {h:(U → D) | " +
				"        h ∈ reduced_conormal_codes(R, S, f, N) ∧ " +
				"        conormal_class(R, S, f, N, h) = " +
				"        coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1)}) = " +
				"factor_set_boundaries(R, S, f, N)",
		},
		"The three relation families generate the standard presentation kernel. The "+
			"explicit code ring and its canonical polynomial lift construct the inverse "+
			"evaluation. Evaluation and inverse evaluation read finitely many coordinates; "+
			"vanishing at x_0 identifies precisely normalized derivation restrictions."),
	Deps: []registry.EntryLike{
		conormalFactorSetDef,
		reducedConormalCodesDef,
		FactorSetRealization,
		FactorSetShear,
		definable_andre_quillen.ConormalCoboundariesCorrespond,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "The three relation families generate the standard presentation kernel. " +
		"The explicit code ring and its canonical polynomial lift construct the inverse " +
		"evaluation. Evaluation and inverse evaluation read finitely many coordinates; " +
		"vanishing at x_0 identifies precisely normalized derivation restrictions.",
})}
