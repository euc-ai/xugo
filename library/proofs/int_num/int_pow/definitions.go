// definitions.go — the chapter's definitional layer: the integer
// power.
//
// Like every other integer operation, it is the real one read at the
// representative and brought back up. The exponent stays a natural:
// ℤ is not closed under negative powers, and the real power at an
// integer exponent is real_zpow's business, not this chapter's.

package int_pow

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IntPowDef — the real power at the representative.
var IntPowDef = intPowDefThm{family.Define(registry.DefEntry{
	Name:      "IntPowDef",
	Key:       "prop_3a629946c3a24bb5",
	Const:     "int_pow",
	Type:      "int → num → int",
	Equations: []string{"∀x:int. ∀n:num. int_pow(x, n) = int_of_real(real_pow(real_of_int(x), n))"},
})}
