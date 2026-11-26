// definitions.go — the sign programs on a latent projection and their class laws: the
// vocabulary the completeness construction is stated in.

package hedge_criterion

import (
	"github.com/euc-ai/xugo/library/registry"
)

// signProgramDef — `latent_sign_program(E, O, Λ, N, g)`: g is a sign program on the
// latent projection of E onto O. A class set z holds the observed nodes that are off
// their reference point, and σ the labels of Λ whose fair bit is set; g(v, z, σ) is the
// mean of the sign of v, +1 at the reference point. The program reads z only at the
// parents of v in the projection and σ only at the labels e with v ∈ N(e); the nodes
// reading one label share a latent ancestor that reaches each through latent nodes;
// and the probabilities (1 + g)/2 are dyadic with one exponent.
var signProgramDef = signProgramDefThm{family.Define(registry.DefEntry{
	Name:  "signProgramDef",
	Key:   "prop_aa3870c1120d1de5",
	Const: "latent_sign_program",
	Type:  "(I → I → bool) → set(I) → set(C) → (C → set(I)) → (I → set(I) → set(C) → real) → bool",
	Equations: []string{
		"∀E:(I → I → bool). ∀O:set(I). ∀Λ:set(C). ∀N:(C → set(I)). ∀g:(I → set(I) → set(C) → real). " +
			"    latent_sign_program(E, O, Λ, N, g) ⇔ " +
			"    finite(Λ) ∧ " +
			"    (∀e:C. e ∈ Λ ⇒ (∃l:I. l ∉ O ∧ (∀v:I. v ∈ N(e) ⇒ latent_reach(E, O, l, v)))) ∧ " +
			"    (∀v:I. ∀z z':set(I). ∀σ:set(C). " +
			"        v ∈ O ∧ (∀u:I. latent_proj_directed(E, O, u, v) ⇒ (u ∈ z ⇔ u ∈ z')) ⇒ " +
			"        g(v, z, σ) = g(v, z', σ)) ∧ " +
			"    (∀v:I. ∀z:set(I). ∀σ σ':set(C). " +
			"        v ∈ O ∧ (∀e:C. e ∈ Λ ∧ v ∈ N(e) ⇒ (e ∈ σ ⇔ e ∈ σ')) ⇒ g(v, z, σ) = g(v, z, σ')) ∧ " +
			"    (∃m:num. ∀v:I. ∀z:set(I). ∀σ:set(C). " +
			"        v ∈ O ⇒ (∃n:num. n ≤ 2 ^ m ∧ (&1 + g(v, z, σ)) / &2 = &n / &(2 ^ m)))",
	},
})}

// signLawDef — `latent_sign_law(O, Λ, g, X, z)`: the probability, under the sign
// program g with the nodes of X held, that the observed nodes off X fall in the classes
// of z — the average over the fair bits of the product of the factors (1 ± g)/2.
var signLawDef = signLawDefThm{family.Define(registry.DefEntry{
	Name:  "signLawDef",
	Key:   "prop_7308706a5861be8a",
	Const: "latent_sign_law",
	Type:  "set(I) → set(C) → (I → set(I) → set(C) → real) → set(I) → set(I) → real",
	Equations: []string{
		"∀O:set(I). ∀Λ:set(C). ∀g:(I → set(I) → set(C) → real). ∀X z:set(I). " +
			"    latent_sign_law(O, Λ, g, X, z) = " +
			"    (Σ_{σ∈{σ:set(C) | σ ⊆ Λ}} Π_{v∈O ∖ X} (&1 + COND(v ∈ z, -&1, &1) * g(v, z, σ)) / &2) / " +
			"    &(2 ^ card(Λ))",
	},
})}

// forestSignMeanDef — `c_forest_sign_mean(W, κ, α, F, R, U, Ed, τ)` is the sign program of
// a forest F with roots R. Off F the mean of v is the route term W(v, z). On F it adds α(v)
// times the sum over the tracks A ⊆ U of three factors: the spins on the track A of the
// edges of Ed at v; the signs of the vertices off A that τ sends to v; and W(v, z) where v
// is in A, κ(v, z) where v is a root, 1 otherwise. A label is an edge of Ed with a track,
// and U holds the vertices where a route re-enters the forest.
var forestSignMeanDef = forestSignMeanDefThm{family.Define(registry.DefEntry{
	Name:  "forestSignMeanDef",
	Key:   "prop_b69adda58770b5b4",
	Const: "c_forest_sign_mean",
	Type: "(I → set(I) → real) → " +
		"(I → set(I) → real) → " +
		"(I → real) → " +
		"set(I) → " +
		"set(I) → " +
		"set(I) → " +
		"set(prod(I, I)) → " +
		"(I → I) → " +
		"I → " +
		"set(I) → " +
		"set(prod(prod(I, I), set(I))) → " +
		"real",
	Equations: []string{
		"∀W κ:(I → set(I) → real). " +
			"∀α:(I → real). " +
			"∀F R U:set(I). " +
			"∀Ed:set(prod(I, I)). " +
			"∀τ:(I → I). " +
			"∀v:I. " +
			"∀z:set(I). " +
			"∀σ:set(prod(prod(I, I), set(I))). " +
			"    c_forest_sign_mean(W, κ, α, F, R, U, Ed, τ, v, z, σ) = " +
			"    W(v, z) + " +
			"    COND(v ∈ F, " +
			"        α(v) * " +
			"        Σ_{A∈{A:set(I) | A ⊆ U}} (Π_{e∈{e:prod(I, I) | e ∈ Ed ∧ (fst(e) = v ∨ snd(e) = v)}} COND((e, A) ∈ σ, -&1, &1)) * " +
			"        (Π_{w∈{w:I | w ∈ F ∧ w ∉ R ∧ w ∉ A ∧ τ(w) = v}} COND(w ∈ z, -&1, &1)) * " +
			"        COND(v ∈ A, W(v, z), COND(v ∈ R, κ(v, z), &1)), " +
			"        &0)",
	},
})}
