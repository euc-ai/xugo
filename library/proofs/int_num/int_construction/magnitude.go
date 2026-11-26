// magnitude.go — an integer read through its magnitude, the natural the
// carving predicate names: one smaller than 1 is 0.

package int_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerAbsLessOne — an integer of absolute value below 1 is 0: its
// absolute value is a natural number n, and n < 1.
var IntegerAbsLessOne = integerAbsLessOneThm{family.Add(registry.ProofEntry{
	Name: "IntegerAbsLessOne",
	Key:  "prop_a5e1118587ef0067",
	Build: family.Theorem(Statement{
		Binders:    "∀k:real.",
		Hypotheses: []string{"integer(k)", "|k| < &1"},
		Conclusion: "k = &0",
	}, func(a *Argument, k *Expr[Real], integral, small Fact) {
		n, magnitude := a.UnpackAs[Nat](a.Unfolded(integral, IntegerDef), "n")
		below := a.Have(
			"the natural number n = |k| is below 1",
			"n < 1",
			By(Normalized, magnitude, small, real_order_ring.OfNumLessThan.At(n, a.TermAs[Nat]("1"))))
		a.Show(
			"so n = 0, and |k| = 0",
			ByArith(below, magnitude))
	}),
})}
