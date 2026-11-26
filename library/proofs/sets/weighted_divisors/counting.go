// counting.go — the chapter's theorem: in degree n the effective divisors
// are finitely many, their number is the n-th coefficient of the
// Euler product, and it satisfies the logarithmic recurrence.

package weighted_divisors

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// WeightedEulerProduct — when only finitely many points of S weigh at most
// n, the effective divisors of degree n are finitely many, their number is
// the n-th coefficient of the Euler product over those points of the
// geometric series Σ_k z^{k·w(x)}, and n times it is the sum over
// 0 < m ≤ n of weighted_multiples(S, w, m) times the count at n − m: the
// three statements WeightedDivisorsFinite, WeightedCountProduct and
// WeightedCountRecurrence, read at one n.
var WeightedEulerProduct = weightedEulerProductThm{family.Add(registry.ProofEntry{
	Name: "WeightedEulerProduct",
	Key:  "prop_a08b956e22a2c3ff",
	Reading: "Only the points of weight at most n are asked to be finitely many: no " +
		"other level is read, and no positivity of w on S, since an effective divisor " +
		"already vanishes at points of weight 0 and the geometric series of such a point is 1.",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀w:(A → num). ∀n:num.",
		Hypotheses: []string{
			"finite(«lowWeight»)",
		},
		Conclusion: "finite(«divisors») ∧ " +
			"weighted_count(S, w, n) = set_fold(«step», «lowWeight», «unit», n) ∧ " +
			"n * weighted_count(S, w, n) = " +
			"nat_sum(«oneToN», λm:num. weighted_multiples(S, w, m) * weighted_count(S, w, n - m))",
	},
		func(a *Argument, S *Expr[Set[A]], w *Arrow[A, Nat], n *Expr[Nat], lowWeight Fact) {
			a.Show(
				"finitely many, counted by the Euler product, and bound by the logarithmic recurrence",
				By(
					lowWeight,
					WeightedDivisorsFinite.At(S, w, n),
					WeightedCountProduct.At(S, w, n),
					WeightedCountRecurrence.At(S, w, n)))
		}),
})}
