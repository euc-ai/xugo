// definitions.go — the positive model class over a fixed graph and set
// of observed nodes, and identifiability of a query over a model class.

package identifiability

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PositiveScmDef — `positive_scm(V, E, O, D, M)`: M is a legal model with
// independent noise on the graph (V, E); the observed nodes O lie in V,
// each with the finite state carrier D(i) and all its subsets
// measurable; and every observed configuration has positive probability.
// The latent nodes' carriers are free.
var PositiveScmDef = positiveScmDefThm{family.Define(registry.DefEntry{
	Name:  "PositiveScmDef",
	Key:   "prop_c4672fd65b0410bc",
	Const: "positive_scm",
	Type:  "set(I) → (I → I → bool) → set(I) → (I → set(B)) → scm_model(A, B, I) → bool",
	Equations: []string{
		"∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀D:(I → set(B)). ∀M:scm_model(A, B, I). " +
			"    positive_scm(V, E, O, D, M) ⇔ " +
			"    scm_on(M) ∧ " +
			"    scm_noise_independent(M) ∧ " +
			"    M.nodes = V ∧ " +
			"    M.edges = E ∧ " +
			"    O ⊆ V ∧ " +
			"    (∀i:I. " +
			"        i ∈ O ⇒ M.states(i) = D(i) ∧ finite(D(i)) ∧ M.state_sigma(i) = {s:set(B) | s ⊆ D(i)}) ∧ " +
			"    (∀v:(I → B). (∀i:I. i ∈ O ⇒ v(i) ∈ D(i)) ⇒ scm_distribution(M, agree_on(O, v)) ≠ &0)",
	},
})}

// IdentifiableDef — `scm_identifiable(C, O, Q)`: any two models of the
// class C that give every configuration of the observed nodes O the same
// probability give the query Q the same value. The sample type is fixed
// by the statement; identifiability is relative to it.
var IdentifiableDef = identifiableDefThm{family.Define(registry.DefEntry{
	Name:  "IdentifiableDef",
	Key:   "prop_baf6b46e6ebcfef6",
	Const: "scm_identifiable",
	Type:  "(scm_model(A, B, I) → bool) → set(I) → (scm_model(A, B, I) → real) → bool",
	Equations: []string{
		"∀C:(scm_model(A, B, I) → bool). ∀O:set(I). ∀Q:(scm_model(A, B, I) → real). " +
			"    scm_identifiable(C, O, Q) ⇔ " +
			"    ∀M₁ M₂:scm_model(A, B, I). " +
			"        C(M₁) ∧ " +
			"        C(M₂) ∧ " +
			"        (∀v:(I → B). " +
			"            scm_distribution(M₁, agree_on(O, v)) = scm_distribution(M₂, agree_on(O, v))) ⇒ " +
			"        Q(M₁) = Q(M₂)",
	},
})}
