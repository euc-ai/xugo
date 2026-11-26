// definitions.go — the chapter's definitional layer: divisibility,
// defined in ℕ.
//
// The constant goes through the define door like every chapter's
// (family.Define): the equation is read in the chapter's own
// vocabulary, the kernel mints `nat_divides = λd n. ∃x. n = d · x`, and
// the entry below is the characterizing statement a proof cites to
// unfold it. Constant identity is process-global: the mint registers
// the meta in the shared ConstMetaManager, so `ctx.Const("nat_divides", …)`
// in any package hands back THIS meta with the definition attached.

package nat_divides

import (
	"github.com/euc-ai/xugo/library/registry"
)

// DividesFactor — d divides n when n is a multiple of d: a divisibility
// IS the existence of the cofactor. Defined in ℕ and nowhere else, so
// a theorem stated in it has ℕ's own construction under it and nothing
// above. The entry is what lets a member name that cofactor, and what
// lets a member that has built one conclude the divisibility back.
var DividesFactor = dividesFactorThm{family.Define(registry.DefEntry{
	Name:      "DividesFactor",
	Key:       "prop_ad34b971103f541a",
	Const:     "nat_divides",
	Type:      "num → num → bool",
	Equations: []string{"∀d n:num. nat_divides(d, n) ⇔ ∃x:num. n = d * x"},
})}
