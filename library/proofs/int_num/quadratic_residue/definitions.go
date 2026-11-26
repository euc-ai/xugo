// definitions.go — the Legendre symbol (a/p): 0 when p divides a, 1 when a
// is a nonzero square mod p, and −1 otherwise.

package quadratic_residue

import (
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/registry"
)

// LegendreSymbolDef — (a/p): 0 when p divides a, 1 when a is a nonzero
// square mod p, −1 otherwise.
var LegendreSymbolDef = legendreSymbolDefThm{family.Define(registry.DefEntry{
	Name:  "LegendreSymbolDef",
	Key:   "prop_922ccc81a4d57dbc",
	Const: "legendre_symbol",
	Type:  "int → num → int",
	Equations: []string{"∀a:int. ∀p:num. " +
		"    legendre_symbol(a, p) = " +
		"    COND(int_of_num(p) ∣ a, int_of_num(0), COND(∃x:int. x * x ≡ a (mod p), int_of_num(1), -1))"},
})}
