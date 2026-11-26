package k_pushforward

import (
	"github.com/euc-ai/xugo/library/registry"
)

var TubularDef = tubularDefThm{family.Define(registry.DefEntry{
	Name:  "TubularDef",
	Key:   "prop_1153d0390fc4bb32",
	Const: "k_tubular_presentation",
	Type: "set(set(A)) → " +
		"set(set(B)) → " +
		"prod(num, A → num → num → complex) → " +
		"(A → B) → " +
		"(prod(A, num → complex) → B) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀j:(A → B). " +
			"∀h:(prod(A, num → complex) → B). " +
			"    k_tubular_presentation(T, S, P, j, h) ⇔ " +
			"    continuous_projection_bundle(T, P) ∧ " +
			"    image(h, projection_total_space(T, P)) ∈ S ∧ " +
			"    homeomorphic_map(projection_total_topology(T, P), " +
			"        subtopology(S, image(h, projection_total_space(T, P))), " +
			"        h) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ h((x, λi:num. complex_of_real(&0))) = j(x))",
	},
})}

var PushforwardDef = pushforwardDefThm{family.Define(registry.DefEntry{
	Name:  "PushforwardDef",
	Key:   "prop_24fb7800d4f9086b",
	Const: "kc_tubular_pushforward",
	Type: "set(set(A)) → " +
		"set(set(B)) → " +
		"prod(num, A → num → num → complex) → " +
		"(prod(A, num → complex) → B) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, B → num → num → complex), " +
		"        prod(prod(num, B → num → num → complex), B → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀h:(prod(A, num → complex) → B). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"    kc_tubular_pushforward(T, S, P, h, a) = " +
			"    kc_open_extension(S, " +
			"        image(h, projection_total_space(T, P)), " +
			"        kc_pullback(subtopology(S, image(h, projection_total_space(T, P))), " +
			"            inverse_on(projection_total_space(T, P), h), " +
			"            kc_thom_map(T, P, a)))",
	},
})}
