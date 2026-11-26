// definitions.go — the chapter's definitional layer: primality,
// defined in ℕ.
//
// The constant goes through the define door (family.Define): the
// equation is read in the chapter's own vocabulary, the kernel mints
// `nat_prime = λp. ¬(p = 1) ∧ ∀x. x ∣ p ⇒ x = 1 ∨ x = p`, and the
// entry below is the characterizing statement a proof cites to unfold
// it. Constant identity is process-global: `ctx.Const("nat_prime", …)`
// in any package hands back the minted meta with the definition
// attached.

package nat_prime

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PrimeDef — a number whose only divisors are 1 and itself, with 1
// legislated out. Divisibility is nat_num/nat_divides's relation, so
// the whole definition stands on ℕ's own construction; the imported
// `prime` says the same thing over a divisibility that is routed
// through ℤ, and nat_prime.go is where the two are shown to agree.
var PrimeDef = primeDefThm{family.Define(registry.DefEntry{
	Name:      "PrimeDef",
	Key:       "prop_79b80a75d0c5776d",
	Const:     "nat_prime",
	Type:      "num → bool",
	Equations: []string{"∀p:num. nat_prime(p) ⇔ ¬(p = 1) ∧ ∀x:num. x ∣ p ⇒ x = 1 ∨ x = p"},
})}
