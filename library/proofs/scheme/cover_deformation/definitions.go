package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	_ "github.com/euc-ai/xugo/library/proofs/topology/cech_cohomology"
	"github.com/euc-ai/xugo/library/registry"
)

var coverDatumDef = coverDatumDefThm{family.Define(registry.DefEntry{
	Name:  "coverDatumDef",
	Key:   "prop_43897fb4560dd5b8",
	Const: "cover_datum",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → set(num) → B) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀t:(set(num) → set(num) → B). " +
			"    cover_datum(R, S, f, N, g, v, t) ⇔ " +
			"    (∀σ:set(num). " +
			"        σ ∈ intersection_indices ⇒ " +
			"        ring_homomorphism(R, S(σ), f(σ)) ∧ " +
			"        module_on(S(σ), N(σ)) ∧ " +
			"        (∀x:B. x ∈ S(σ).carrier ⇒ g(σ, σ, x) = x) ∧ " +
			"        (∀n:D. n ∈ N(σ).carrier ⇒ v(σ, σ, n) = n)) ∧ " +
			"    (∀σ τ:set(num). " +
			"        σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
			"        t(σ, τ) ∈ S(σ).carrier ∧ " +
			"        is_localization_on(S(σ), monoid_powers(S(σ).mul, S(σ).one, t(σ, τ)), S(τ), g(σ, τ)) ∧ " +
			"        is_module_localization_on(S(σ), " +
			"            monoid_powers(S(σ).mul, S(σ).one, t(σ, τ)), " +
			"            S(τ), " +
			"            g(σ, τ), " +
			"            N(σ), " +
			"            N(τ), " +
			"            v(σ, τ)) ∧ " +
			"        (∀a:A. a ∈ R.carrier ⇒ g(σ, τ, f(σ, a)) = f(τ, a))) ∧ " +
			"    (∀σ τ υ:set(num). " +
			"        σ ∈ intersection_indices ∧ " +
			"        τ ∈ intersection_indices ∧ " +
			"        υ ∈ intersection_indices ∧ " +
			"        σ ⊆ τ ∧ " +
			"        τ ⊆ υ ⇒ " +
			"        (∀x:B. x ∈ S(σ).carrier ⇒ g(τ, υ, g(σ, τ, x)) = g(σ, υ, x)) ∧ " +
			"        (∀n:D. n ∈ N(σ).carrier ⇒ v(τ, υ, v(σ, τ, n)) = v(σ, υ, n)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Countably indexed affine intersection data with principal localization arrows and " +
		"strictly compatible ring and module maps. Countability of carriers is a separate hypothesis."})}

var coverExtensionDef = coverExtensionDefThm{family.Define(registry.DefEntry{
	Name:  "coverExtensionDef",
	Key:   "prop_7d18bdd07bdf2a58",
	Const: "cover_extension",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → square_zero_ops(A, B, I, D)) → " +
		"(set(num) → set(num) → I → I) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D).∀E:(set(num) → square_zero_ops(A, B, I, D)). " +
			"∀F:(set(num) → set(num) → I → I). " +
			"    cover_extension(R, S, f, N, g, v, E, F) ⇔ " +
			"    (∀σ:set(num). " +
			"        σ ∈ intersection_indices ⇒ " +
			"        square_zero_extension(R, S(σ), f(σ), N(σ), E(σ)) ∧ " +
			"        (∀x:I. x ∈ E(σ).ring.carrier ⇒ F(σ, σ, x) = x)) ∧ " +
			"    (∀σ τ:set(num). " +
			"        σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
			"        ring_homomorphism(E(σ).ring, E(τ).ring, F(σ, τ)) ∧ " +
			"        (∀a:A. a ∈ R.carrier ⇒ F(σ, τ, E(σ).structure(a)) = E(τ).structure(a)) ∧ " +
			"        (∀n:D. n ∈ N(σ).carrier ⇒ F(σ, τ, E(σ).inclusion(n)) = E(τ).inclusion(v(σ, τ, n))) ∧ " +
			"        (∀x:I. " +
			"            x ∈ E(σ).ring.carrier ⇒ " +
			"            E(τ).projection(F(σ, τ, x)) = g(σ, τ, E(σ).projection(x)))) ∧ " +
			"    (∀σ τ υ:set(num). " +
			"        σ ∈ intersection_indices ∧ " +
			"        τ ∈ intersection_indices ∧ " +
			"        υ ∈ intersection_indices ∧ " +
			"        σ ⊆ τ ∧ " +
			"        τ ⊆ υ ⇒ " +
			"        (∀x:I. x ∈ E(σ).ring.carrier ⇒ F(τ, υ, F(σ, τ, x)) = F(σ, υ, x)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "An actual extension at every finite intersection, with marked maps and " +
		"strict composition. Localization of these maps follows from CoverExtensionMapsLocalize."})}

var coverExtensionIsoDef = coverExtensionIsoDefThm{family.Define(registry.DefEntry{
	Name:  "coverExtensionIsoDef",
	Key:   "prop_3fbe6c45bfdfb528",
	Const: "cover_extension_iso",
	Type: "ring_ops(A) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → square_zero_ops(A, B, I, D)) → " +
		"(set(num) → set(num) → I → I) → " +
		"(set(num) → square_zero_ops(A, B, H, D)) → " +
		"(set(num) → set(num) → H → H) → " +
		"(set(num) → I → H) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀E:(set(num) → square_zero_ops(A, B, I, D)). " +
			"∀F:(set(num) → set(num) → I → I). " +
			"∀E₁:(set(num) → square_zero_ops(A, B, H, D)). " +
			"∀F₁:(set(num) → set(num) → H → H). " +
			"∀h:(set(num) → I → H). " +
			"    cover_extension_iso(R, N, E, F, E₁, F₁, h) ⇔ " +
			"    (∀σ:set(num). " +
			"        σ ∈ intersection_indices ⇒ square_zero_isomorphism(R, N(σ), E(σ), E₁(σ), h(σ))) ∧ " +
			"    (∀σ τ:set(num). " +
			"        σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
			"        (∀x:I. x ∈ E(σ).ring.carrier ⇒ h(τ, F(σ, τ, x)) = F₁(σ, τ, h(σ, x))))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "Objectwise marked isomorphisms commuting with every intersection map."})}

var CoverExtensionMapsLocalize = coverExtensionMapsLocalizeThm{family.Add(registry.ProofEntry{
	Name: "CoverExtensionMapsLocalize",
	Key:  "prop_f471c95bd584cf51",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).∀E:(set(num) → square_zero_ops(A, B, I, D)). " +
				"∀F:(set(num) → set(num) → I → I). " +
				"∀σ τ:set(num). " +
				"∀a:I.",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"cover_extension(R, S, f, N, g, v, E, F)",
				"σ ∈ intersection_indices",
				"τ ∈ intersection_indices",
				"σ ⊆ τ",
				"a ∈ E(σ).ring.carrier",
				"E(σ).projection(a) = t(σ, τ)",
			},
			Conclusion: "is_localization_on(E(σ).ring, " +
				"    monoid_powers(E(σ).ring.mul, E(σ).ring.one, a), " +
				"    E(τ).ring, " +
				"    F(σ, τ))",
		},
		"The image of a is a unit because it is a unit modulo a square-zero "+
			"ideal. The induced map from the localized source is an isomorphism "+
			"on both kernel and quotient, hence an isomorphism of extensions."),
	Deps: []registry.EntryLike{
		coverDatumDef,
		coverExtensionDef,
		square_zero_extension.SquareZeroLocalizationIsExtension,
	},
	Reading: "Thus actual intersection diagrams recover the usual localized " +
		"gluing data without imposing artificial strictness on section choices.",
})}
