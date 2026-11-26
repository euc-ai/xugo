// Cohomology multiplication uses closed representatives, and the external product pulls each factor to the product manifold.

package de_rham_product

import (
	"github.com/euc-ai/xugo/library/registry"
)

var WedgeDef = wedgeDefThm{family.Define(registry.DefEntry{
	Name:  "WedgeDef",
	Key:   "prop_8e1b7164a04b2bbc",
	Const: "de_rham_wedge",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Dim:  "n",
	Deps: []registry.EntryLike{},
	Reading: "The chosen representatives are required to be normalized closed forms representing " +
		"the given classes. ClassRepresentative supplies them on genuine cohomology carriers; no value " +
		"or law is prescribed outside those carriers. WedgeClass proves independence of these choices.",
	Equations: []string{
		"∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_wedge⟨n⟩(T, 𝒜, p, q, s, t) = " +
			"    de_rham_class⟨n⟩(T, " +
			"        𝒜, " +
			"        p + q, " +
			"        manifold_form_wedge⟨n⟩(T, " +
			"            𝒜, " +
			"            p, " +
			"            q, " +
			"            «closed representative»(p, s), " +
			"            «closed representative»(q, t)))",
	},
})}

var ExternalProductDef = externalProductDefThm{family.Define(registry.DefEntry{
	Name:       "ExternalProductDef",
	Key:        "prop_a8fb9685f55f17bb",
	Const:      "de_rham_external_product",
	Dimensions: []string{"n", "m"},
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"num → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real)",
	Deps: []registry.EntryLike{WedgeDef},
	Reading: "The order is first-factor pullback followed by second-factor " +
		"pullback in the wedge. Its result is a class of whole forms on the product " +
		"point type. Both dimensions are written in the suffix, as for de_rham_pullback.",
	Equations: []string{
		"∀n m p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀t:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_external_product⟨n, m⟩(T, 𝒜, S, ℬ, p, q, s, t) = " +
			"    de_rham_wedge⟨n + m⟩(product_topology(T, S), " +
			"        «product atlas», " +
			"        p, " +
			"        q, " +
			"        de_rham_pullback⟨n + m, n⟩(product_topology(T, S), «product atlas», T, 𝒜, p, fst)(s), " +
			"        de_rham_pullback⟨n + m, m⟩(product_topology(T, S), «product atlas», S, ℬ, q, snd)(t))",
	},
})}
