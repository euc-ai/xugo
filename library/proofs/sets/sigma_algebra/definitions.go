package sigma_algebra

import (
	"github.com/euc-ai/xugo/library/registry"
)

// SigmaAlgebraOnDef — Complements and countable unions are taken inside X.
var SigmaAlgebraOnDef = sigmaAlgebraOnDefThm{family.Define(registry.DefEntry{
	Name:  "SigmaAlgebraOnDef",
	Key:   "prop_abc7d41934ec5c5d",
	Const: "sigma_algebra_on",
	Type:  "set(A) → set(set(A)) → bool",
	Equations: []string{
		"∀X:set(A). ∀S:set(set(A)). " +
			"    sigma_algebra_on(X, S) ⇔ " +
			"    S ⊆ {u:set(A) | u ⊆ X} ∧ " +
			"    X ∈ S ∧ " +
			"    (∀u:set(A). u ∈ S ⇒ X ∖ u ∈ S) ∧ " +
			"    (∀a:(num → set(A)). (∀n:num. a(n) ∈ S) ⇒ ⋃image(a, 𝕌) ∈ S)",
	},
	Reading: "Complements and countable unions are taken inside X.",
})}

var GeneratedSigmaDef = generatedSigmaDefThm{family.Define(registry.DefEntry{
	Name:  "GeneratedSigmaDef",
	Key:   "prop_609c7d2bba60c896",
	Const: "generated_sigma",
	Type:  "set(A) → set(set(A)) → set(set(A))",
	Deps:  []registry.EntryLike{SigmaAlgebraOnDef},
	Reading: "The generating sets must lie in the carrier for the generated family to be a " +
		"sigma algebra. If they do not, the intersection is empty-indexed and is the universal family.",
	Equations: []string{
		"∀Ω:set(A). ∀C:set(set(A)). " +
			"    generated_sigma(Ω, C) = ⋂{S:set(set(A)) | sigma_algebra_on(Ω, S) ∧ C ⊆ S}",
	},
})}

var PiSystemDef = piSystemDefThm{family.Define(registry.DefEntry{
	Name:  "PiSystemDef",
	Key:   "prop_33030c427f2db193",
	Const: "pi_system_on",
	Type:  "set(A) → set(set(A)) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀C:set(set(A)). " +
			"    pi_system_on(Ω, C) ⇔ C ⊆ {s:set(A) | s ⊆ Ω} ∧ (∀s t:set(A). s ∈ C ∧ t ∈ C ⇒ s ∩ t ∈ C)",
	},
})}

var LambdaSystemDef = lambdaSystemDefThm{family.Define(registry.DefEntry{
	Name:  "LambdaSystemDef",
	Key:   "prop_73c665e713179e73",
	Const: "lambda_system_on",
	Type:  "set(A) → set(set(A)) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀D:set(set(A)). " +
			"    lambda_system_on(Ω, D) ⇔ " +
			"    D ⊆ {s:set(A) | s ⊆ Ω} ∧ " +
			"    Ω ∈ D ∧ " +
			"    (∀s:set(A). s ∈ D ⇒ Ω ∖ s ∈ D) ∧ " +
			"    (∀a:(num → set(A)). " +
			"        (∀n:num. a(n) ∈ D) ∧ (∀i j:num. i ≠ j ⇒ a(i) ∩ a(j) = ∅) ⇒ ⋃image(a, 𝕌) ∈ D)",
	},
})}

// SigmaJoinDef — `sigma_join(Ω, F, K)` is the σ-algebra on Ω generated
// by the members F(i), i ∈ K, of a family of σ-algebras: σ_K. An empty
// K generates the trivial σ-algebra {∅, Ω}.
var SigmaJoinDef = sigmaJoinDefThm{family.Define(registry.DefEntry{
	Name:  "SigmaJoinDef",
	Key:   "prop_6217dcb8afe96795",
	Const: "sigma_join",
	Type:  "set(A) → (I → set(set(A))) → set(I) → set(set(A))",
	Equations: []string{
		"∀Ω:set(A). ∀F:(I → set(set(A))). ∀K:set(I). " +
			"    sigma_join(Ω, F, K) = generated_sigma(Ω, ⋃image(F, K))",
	},
	Deps: []registry.EntryLike{GeneratedSigmaDef},
})}
