package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/topology/cech_cohomology"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var localizedDerivationDef = localizedDerivationDefThm{family.Define(registry.DefEntry{
	Name:  "localizedDerivationDef",
	Key:   "prop_c67db5226083fddd",
	Const: "localized_derivation",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"(B → C) → " +
		"module_ops(C, D) → " +
		"(B → D) → " +
		"C → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀d:(B → D). " +
			"    localized_derivation(R, S, f, T, g, N, d) = " +
			"    (λy:C. COND(y ∈ T.carrier, derivation_localization(S, T, g, N, d, y), N.zero))",
	},
	Deps: []registry.EntryLike{},
	Reading: "The existing quotient-rule derivation, " +
		"normalized to zero off the localization carrier."})}

var coverDerivationModuleDef = coverDerivationModuleDefThm{family.Define(registry.DefEntry{
	Name:  "coverDerivationModuleDef",
	Key:   "prop_6fed75e74bff009a",
	Const: "cover_derivation_module",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"set(num) → " +
		"module_ops(A, B → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀σ:set(num). " +
			"    cover_derivation_module(R, S, f, N)(σ) = " +
			"    mk_module(fun_add(N(σ).add), " +
			"        λs:B. N(σ).zero, " +
			"        λd:(B → D). λs:B. N(σ).neg(d(s)), " +
			"        λa:A. λd:(B → D). λs:B. N(σ).smul(f(σ, a), d(s)), " +
			"        {d:(B → D) | " +
			"            d ∈ indexed_functions(S(σ).carrier, λs:B. N(σ).zero, λs:B. N(σ).carrier) ∧ " +
			"            derivation_on(R, S(σ), f(σ), N(σ), d)})",
	},
	Deps:    []registry.EntryLike{},
	Reading: "Normalized derivations form an R-module by the chart structure map."})}

var coverDerivationRestrictionDef = coverDerivationRestrictionDefThm{family.Define(registry.DefEntry{
	Name:  "coverDerivationRestrictionDef",
	Key:   "prop_590d37b1f3f67713",
	Const: "cover_derivation_restriction",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"set(num) → " +
		"set(num) → " +
		"(B → D) → " +
		"B → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀σ τ:set(num). " +
			"∀d:(B → D). " +
			"    cover_derivation_restriction(R, S, f, N, g, v)(σ, τ, d) = " +
			"    localized_derivation(R, S(σ), f(σ), S(τ), g(σ, τ), N(τ), λs:B. v(σ, τ, d(s)))",
	},
	Deps:    []registry.EntryLike{localizedDerivationDef},
	Reading: "Postcompose coefficients and uniquely extend across the localization."})}

var coverDerivationTopologyDef = coverDerivationTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "coverDerivationTopologyDef",
	Key:   "prop_175afcae676f4fc2",
	Const: "cover_derivation_topology",
	Type:  "(set(num) → ring_ops(B)) → (set(num) → module_ops(B, D)) → set(num) → set(set(B → D))",
	Equations: []string{
		"∀S:(set(num) → ring_ops(B)). ∀N:(set(num) → module_ops(B, D)). ∀σ:set(num). " +
			"    cover_derivation_topology(S, N, σ) = " +
			"    indexed_discrete_topology(S(σ).carrier, λs:B. N(σ).zero, λs:B. N(σ).carrier)",
	},
	Deps: []registry.EntryLike{},
	Reading: "Ambient pointwise topologies; intersect with " +
		"the derivation carrier when making a Polish group."})}

var DerivationLocalizationUnique = derivationLocalizationUniqueThm{family.Add(registry.ProofEntry{
	Name: "DerivationLocalizationUnique",
	Key:  "prop_c2fd43024c8b02dc",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀T:ring_ops(C). " +
				"∀g:(B → C). " +
				"∀N:module_ops(C, D). " +
				"∀a:B. " +
				"∀d:(B → D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"a ∈ S.carrier",
				"is_localization_on(S, monoid_powers(S.mul, S.one, a), T, g)",
				"module_on(T, N)",
				"derivation_on(R, S, f, scalar_restriction(g, N), d)",
			},
			Conclusion: "localized_derivation(R, S, f, T, g, N, d) ∈ " +
				"indexed_functions(T.carrier, λx:C. N.zero, λx:C. N.carrier) ∧ " +
				"derivation_on(R, T, λr:A. g(f(r)), N, localized_derivation(R, S, f, T, g, N, d)) ∧ " +
				"(∀s:B. s ∈ S.carrier ⇒ localized_derivation(R, S, f, T, g, N, d, g(s)) = d(s)) ∧ " +
				"(∀e:(C → D). " +
				"    e ∈ indexed_functions(T.carrier, λx:C. N.zero, λx:C. N.carrier) ∧ " +
				"    derivation_on(R, T, λr:A. g(f(r)), N, e) ∧ " +
				"    (∀s:B. s ∈ S.carrier ⇒ e(g(s)) = d(s)) ⇒ " +
				"    e = localized_derivation(R, S, f, T, g, N, d))",
		},
		"The quotient rule determines d(s/a^k), proves independence of representatives and "+
			"supplies the unique extension. Off-carrier normalization is part of uniqueness."),
	Deps: []registry.EntryLike{localizedDerivationDef, partial_derivative.DerivationExtendsUniquely},
	Reading: "The quotient rule determines d(s/a^k), proves independence of representatives " +
		"and supplies the unique extension. Off-carrier normalization is part of uniqueness.",
})}

var DerivationPresheaf = derivationPresheafThm{family.Add(registry.ProofEntry{
	Name: "DerivationPresheaf",
	Key:  "prop_60867da720653741",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{"cover_datum(R, S, f, N, g, v, t)"},
			Conclusion: "intersection_module_datum(R, " +
				"    cover_derivation_module(R, S, f, N), " +
				"    cover_derivation_restriction(R, S, f, N, g, v))",
		},
		"Uniqueness of derivation localization proves identity, composition and linearity of restriction."),
	Deps: []registry.EntryLike{
		coverDatumDef,
		coverDerivationModuleDef,
		coverDerivationRestrictionDef,
		DerivationLocalizationUnique,
	},
	Reading: "Uniqueness of derivation localization proves " +
		"identity, composition and linearity of restriction.",
})}

var DerivationPresheafPolish = derivationPresheafPolishThm{family.Add(registry.ProofEntry{
	Name: "DerivationPresheafPolish",
	Key:  "prop_a4f430b9c34c020b",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"countable(R.carrier)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ countable(S(σ).carrier) ∧ countable(N(σ).carrier)",
			},
			Conclusion: "(∀σ:set(num). " +
				"    σ ∈ intersection_indices ⇒ " +
				"    closed_in(cover_derivation_topology(S, N, σ), " +
				"        cover_derivation_module(R, S, f, N)(σ).carrier) ∧ " +
				"    polish_abelian_group(module_additive_group(cover_derivation_module(R, S, f, N)(σ)), " +
				"        (λσ:set(num). " +
				"            subtopology(cover_derivation_topology(S, N, σ), " +
				"                cover_derivation_module(R, S, f, N, σ).carrier))(σ))) ∧ " +
				"(∀σ τ:set(num). " +
				"    σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
				"    continuous_map((λσ:set(num). " +
				"            subtopology(cover_derivation_topology(S, N, σ), " +
				"                cover_derivation_module(R, S, f, N, σ).carrier))(σ), " +
				"        (λσ:set(num). " +
				"            subtopology(cover_derivation_topology(S, N, σ), " +
				"                cover_derivation_module(R, S, f, N, σ).carrier))(τ), " +
				"        cover_derivation_restriction(R, S, f, N, g, v)(σ, τ))) ∧ " +
				"polish_cochain_complex(R, " +
				"    intersection_cech_complex(R, " +
				"        cover_derivation_module(R, S, f, N), " +
				"        cover_derivation_restriction(R, S, f, N, g, v)), " +
				"    intersection_cech_topologies(cover_derivation_module(R, S, f, N), " +
				"        λσ:set(num). " +
				"            subtopology(cover_derivation_topology(S, N, σ), " +
				"                cover_derivation_module(R, S, f, N, σ).carrier)))",
		},
		"Derivation equations are closed finite-coordinate conditions. A fixed "+
			"representation of each localized scalar makes the quotient rule read "+
			"finitely many source values. Apply IntersectionCechPolishModel."),
	Deps: []registry.EntryLike{
		DerivationPresheaf,
		coverDerivationTopologyDef,
		cech_cohomology.IntersectionCechPolishModel,
		polish_space.FiniteCoordinateContinuous,
		polish_group.ClosedSubgroupPolish,
	},
	Reading: "Derivation equations are closed finite-coordinate conditions. " +
		"A fixed representation of each localized scalar makes the quotient rule " +
		"read finitely many source values. Apply IntersectionCechPolishModel.",
})}

var coverAQModuleDef = coverAQModuleDefThm{family.Define(registry.DefEntry{
	Name:  "coverAQModuleDef",
	Key:   "prop_a5d8fa4f6a4b8f8e",
	Const: "cover_aq_module",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"num → " +
		"set(num) → " +
		"module_ops(A, set(U → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀n:num. " +
			"∀σ:set(num). " +
			"    cover_aq_module(R, S, f, N, n, σ) = " +
			"    scalar_restriction(f(σ), cotangent_cohomology⟨U:U⟩(R, S(σ), f(σ), S(σ), λy:B. y, N(σ), n))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "AQ cohomology read as an R-module; no Polish quotient topology is imposed."})}

var coverAQRestrictionDef = coverAQRestrictionDefThm{family.Define(registry.DefEntry{
	Name:  "coverAQRestrictionDef",
	Key:   "prop_23f69ac952c96984",
	Const: "cover_aq_restriction",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"num → " +
		"set(num) → " +
		"set(num) → " +
		"set(U → D) → " +
		"set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀n:num. " +
			"∀σ τ:set(num). " +
			"    cover_aq_restriction(R, S, f, N, g, v, n, σ, τ) = " +
			"    cotangent_cohomology_restriction(R, S(σ), f(σ), S(τ), g(σ, τ), N(τ), v(σ, τ), n)",
	},
	Deps:    []registry.EntryLike{},
	Reading: "The named localization restriction on AQ classes."})}

var AQPresheaf = aQPresheafThm{family.Add(registry.ProofEntry{
	Name: "AQPresheaf",
	Key:  "prop_7437768f93b7910a",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀n:num.",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
			},
			Conclusion: "intersection_module_datum(R, " +
				"    cover_aq_module⟨U:U⟩(R, S, f, N, n), " +
				"    cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, n))",
		},
		"StandardMapCompose and CotangentFunctorialCompose give strict composition on "+
			"carriers. Coefficient naturality and the unique inverse of the localization "+
			"right map on cohomology give identity and composition of restrictions on classes."),
	Deps: []registry.EntryLike{
		coverAQModuleDef,
		coverAQRestrictionDef,
		standard_resolution.StandardMapCompose,
		cotangent_complex.CotangentFunctorialCompose,
		cotangent_examples.CotangentCohomologyRestrictionHom,
		transitivity.CotangentCohomologyTransitivityCoefficientNatural,
	},
	Reading: "This is an algebraic diagram. Its section groups need not themselves be Polish; " +
		"the compatible degree-one classes get the witness cover in CoverSequenceDefinable.",
})}
