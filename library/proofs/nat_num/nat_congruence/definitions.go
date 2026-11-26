// definitions.go — the chapter's definitional layer: congruence,
// defined in ℕ.
//
// The constant goes through the define door (family.Define): the
// equation is read in the chapter's own vocabulary, the kernel mints
// `nat_cong = λx y n. nat_mod(x, n) = nat_mod(y, n)`, and the entry
// below is the characterizing statement a proof cites to unfold it.
// Constant identity is process-global: `ctx.Const("nat_cong", …)` in
// any package hands back the minted meta with the definition attached.

package nat_congruence

import (
	"github.com/euc-ai/xugo/library/registry"
)

// CongDef — x and y are congruent modulo n when they leave the same
// remainder. On ℕ that computation IS the relation, so it is the
// definition, and a theorem stated in it has ℕ's own division
// underneath and nothing above.
var CongDef = congDefThm{family.Define(registry.DefEntry{
	Name:      "CongDef",
	Key:       "prop_89cfdb7eeb29981d",
	Const:     "nat_cong",
	Type:      "num → num → num → bool",
	Equations: []string{"∀x y n:num. nat_cong(x, y, n) ⇔ rem(x, n) = rem(y, n)"},
})}
