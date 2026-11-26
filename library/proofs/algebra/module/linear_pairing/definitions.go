package linear_pairing

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// BilinearPairingDef — `bilinear_pairing(R, M, b)`: b is linear in each
// argument, every slice b(x, -) and b(-, y) at a vector of M being a
// homomorphism of M into the scalars.
var BilinearPairingDef = bilinearPairingDefThm{family.Define(registry.DefEntry{
	Name:  "BilinearPairingDef",
	Key:   "prop_ad2df6b570b501a6",
	Deps:  []registry.EntryLike{},
	Const: "bilinear_pairing",
	Type:  "ring_ops(A) → module_ops(A, B) → (B → B → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀b:(B → B → A). " +
			"    bilinear_pairing(R, M, b) ⇔ " +
			"    (∀x:B. x ∈ M.carrier ⇒ module_homomorphism(R, M, regular_module(R), b(x))) ∧ " +
			"    (∀y:B. y ∈ M.carrier ⇒ module_homomorphism(R, M, regular_module(R), λx:B. b(x, y)))",
	},
})}

// PairingNondegenerateDef — `pairing_nondegenerate(R, M, b)`: b is
// left-nondegenerate, every nonzero vector x of M pairing to a nonzero
// scalar b(x, y) with some vector y of M.
var PairingNondegenerateDef = pairingNondegenerateDefThm{family.Define(registry.DefEntry{
	Name:  "PairingNondegenerateDef",
	Key:   "prop_c8b6063ee1c236b5",
	Deps:  []registry.EntryLike{BilinearPairingDef},
	Const: "pairing_nondegenerate",
	Type:  "ring_ops(A) → module_ops(A, B) → (B → B → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀b:(B → B → A). " +
			"    pairing_nondegenerate(R, M, b) ⇔ " +
			"    (∀x:B. x ∈ M.carrier ∧ x ≠ M.zero ⇒ ∃y:B. y ∈ M.carrier ∧ b(x, y) ≠ R.zero)",
	},
})}
