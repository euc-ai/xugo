// squares.go — the square of an integer, read through the ± form of the
// carving predicate: it is the square of a natural number.

package int_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerSquareNatural — the square of an integer is the square of a
// natural number: an integer is n or −n for a natural n.
var IntegerSquareNatural = integerSquareNaturalThm{family.Add(registry.ProofEntry{
	Name: "IntegerSquareNatural",
	Key:  "prop_ec8ccfade79140b9",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real.",
		Hypotheses: []string{"integer(x)"},
		Conclusion: "∃n:num. x * x = &n * &n",
	}, func(a *Argument, x *Expr[Real], integral Fact) {
		a.Show(
			"x is n or −n for a natural n, and either way its square is n n",
			By(integral, IntegerIffPlusMinusNat.At(x), real_ring.MulNegNeg))
	}),
})}
