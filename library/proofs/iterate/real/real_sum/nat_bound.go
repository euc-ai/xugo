// nat_bound.go — a finite sum of natural numbers bounded in ℝ.

package real_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// NatSumBound — a finite sum of natural numbers, each at most the real number c,
// is at most card(s) · c: transport the sum to ℝ and apply the real sum bound.
var NatSumBound = natSumBoundThm{family.Add(registry.ProofEntry{
	Name: "NatSumBound",
	Key:  "prop_1ff42e559f32fe2",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f:(A → num). ∀c:real.",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ real_of_num(f(x)) ≤ c",
		},
		Conclusion: "real_of_num(nat_sum(s, f)) ≤ real_of_num(card(s)) * c",
	},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Nat], c *Expr[Real], finiteS, bounded Fact) {
			a.Show(
				"transport the sum to ℝ and apply the bound to its summands",
				Simp(Fwd(RealOfNatSum)),
				By(finiteS, bounded, Bound.At(s, a.TermAs[Fun[A, Real]]("λx:A. real_of_num(f(x))"), c)))
		}),
})}
