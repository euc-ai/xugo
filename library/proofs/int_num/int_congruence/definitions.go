// definitions.go — the chapter's definitional layer: congruence.
//
// `int_cong(x, y, m)` is the chapter's subject written as a relation:
// x and y agree modulo m exactly when m divides their difference. It
// is the surface `x ≡ y (mod m)` lowers to at int — the same three
// places, in the same order, as ℕ's `nat_cong(x, y, m)` at num — and
// nothing here needs m to be positive or nonzero: at m = 0 the
// relation is equality, which is the right answer rather than a gap.

package int_congruence

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IntCongDef — agreement modulo m: m divides the difference.
var IntCongDef = intCongDefThm{family.Define(registry.DefEntry{
	Name:      "IntCongDef",
	Key:       "prop_e58808fc645f51d9",
	Const:     "int_cong",
	Type:      "int → int → int → bool",
	Equations: []string{"∀x y m:int. int_cong(x, y, m) ⇔ m ∣ (x - y)"},
})}
