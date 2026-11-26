// definitions.go — a character of a group: a homomorphism into the
// nonzero complex numbers.

package group_character

import (
	"github.com/euc-ai/xugo/library/registry"
)

// GroupCharacterDef — `group_character(G, χ)`: χ carries G's product to
// the product of nonzero complex numbers, and is 0 off G's carrier.
var GroupCharacterDef = groupCharacterDefThm{family.Define(registry.DefEntry{
	Name:  "GroupCharacterDef",
	Key:   "prop_3a2c0f591bb7a4cc",
	Const: "group_character",
	Type:  "group_ops(A) → (A → complex) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀χ:(A → complex). " +
			"    group_character(G, χ) ⇔ " +
			"    group_homomorphism(G, field_units(complex_field_ops), χ) ∧ (∀x:A. x ∉ G.carrier ⇒ χ(x) = &0)",
	},
	Reading: "A homomorphism is constrained only on the carrier, so two homomorphisms " +
		"that agree there are the same character only once their values off it are fixed: a " +
		"character is 0 off the carrier, which makes the characters of a finite group a finite " +
		"set of functions. The definition holds group_on(G) through group_homomorphism; it does " +
		"not ask G to be abelian or finite, which the theorems on extension and counting do.",
})}
