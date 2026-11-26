package k_pushforward

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/proofs/topology/k_thom"
	"github.com/euc-ai/xugo/library/registry"
)

var PushforwardHomomorphism = pushforwardHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "PushforwardHomomorphism",
	Key:  "prop_af158ed5466121e7",
	Deps: []registry.EntryLike{
		k_thom.ThomHomomorphism,
		k_compact_support.OpenExtensionHomomorphism,
		k_compact_support.ProperPullback,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀j:(A → B). " +
			"∀h:(prod(A, num → complex) → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"is_topology(S)",
			"locally_compact_space(S)",
			"hausdorff(S)",
			"k_tubular_presentation(T, S, P, j, h)",
		},
		Conclusion: "group_homomorphism(kc_group(T), kc_group(S), kc_tubular_pushforward(T, S, P, h))",
	},
		"The tubular inverse is a proper homeomorphism; compose its "+
			"pullback with the Thom homomorphism and open extension."),
})}

var TubeRestrictionIndependent = tubeRestrictionIndependentThm{family.Add(registry.ProofEntry{
	Name: "TubeRestrictionIndependent",
	Key:  "prop_45de71d659d7ac10",
	Deps: []registry.EntryLike{k_compact_support.OpenExtensionComposition, k_compact_support.Excision},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀j:(A → B). " +
			"∀h k:(prod(A, num → complex) → B). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))).",
		Hypotheses: []string{
			"is_topology(T)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"is_topology(S)",
			"locally_compact_space(S)",
			"hausdorff(S)",
			"k_tubular_presentation(T, S, P, j, h)",
			"k_tubular_presentation(T, S, P, j, k)",
			"∃W:set(prod(A, num → complex)). " +
				"    W ∈ projection_total_topology(T, P) ∧ " +
				"    (∀x:A. x ∈ ⋃T ⇒ (x, λi:num. complex_of_real(&0)) ∈ W) ∧ " +
				"    (∀p:prod(A, num → complex). p ∈ W ⇒ h(p) = k(p))",
			"a ∈ (kc_group(T)).carrier",
		},
		Conclusion: "kc_tubular_pushforward(T, S, P, h, a) = kc_tubular_pushforward(T, S, P, k, a)",
	},
		"A Thom product can be represented with support in any prescribed "+
			"neighborhood of the zero section over the compact support of a. "+
			"Excision then compares the identical restricted tubular maps."),
})}
