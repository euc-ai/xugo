// definitions.go — the chapter's definitional layer: the least common
// multiple.
//
// The lcm is the product divided by the gcd, in magnitude, with zero
// handled outright: when either argument is zero the product is, and
// the quotient would be a division by the gcd of a pair whose gcd is
// the other argument — so the definition returns zero rather than
// leaving the value to the division's own convention.

package int_div_rem

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IntLcmDef — the product over the gcd, in magnitude; zero at zero.
// Written through fst and snd; a definition matching a pair pattern
// mints the same constant.
var IntLcmDef = intLcmDefThm{family.Define(registry.DefEntry{
	Name:  "IntLcmDef",
	Key:   "prop_fc330dcb4f49dc37",
	Const: "int_lcm",
	Type:  "prod(int, int) → int",
	Equations: []string{"∀p:prod(int, int). " +
		"    int_lcm(p) = " +
		"    COND(fst(p) * snd(p) = int_of_num(0), " +
		"        int_of_num(0), " +
		"        div(|fst(p) * snd(p)|, int_gcd((fst(p), snd(p)))))"},
	// divRemSpec is a dep so its mint runs before this equation is
	// read: the equation names `int_div`, and only the mint answers for a
	// name — read first, the equation fails to parse.
	Deps: []registry.EntryLike{divRemSpec},
})}
