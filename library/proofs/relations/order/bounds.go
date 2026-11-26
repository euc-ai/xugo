// bounds.go — the greatest and the maximal points of a set under a
// relation. What is here holds of any relation, or of the structure its
// statement names.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Greatest, least and maximal points
// ---------------------------------------------------------------------------

// MaximalGreatest — under a total order a maximal point is the
// greatest: each point is below it, or maximality reverses their comparison.
var MaximalGreatest = maximalGreatestThm{family.Add(registry.ProofEntry{
	Name: "MaximalGreatest",
	Key:  "prop_5cb7372e32e6f170",
	Reading: "Of the total order only comparability is spent. Under equality on a two-point type, " +
		"each point of the whole type is maximal and neither is greatest. At a one-point set it is the " +
		"comparison of the point with itself that puts it below itself, which maximality does not give.",
	Build: TotalOrder.Law(Statement{
		Binders: "∀s:set(A). ∀m:A.",
		Hypotheses: []string{
			"maximal(R, s, m)",
		},
		Conclusion: "greatest(R, s, m)",
	},
		func(a *Argument, R *Arrow2[A, A, Bool], total Fact, s *Expr[Set[A]], m *Expr[A], maximal Fact) {
			a.Show(
				"each point of s is below m by comparability and maximality, so m is greatest",
				By(
					maximal,
					MaximalDef.At(R, s, m),
					GreatestDef.At(R, s, m),
					UpperBoundDef.At(R, s, m),
					Total.Read(total)))
		}),
})}

// FiniteMaximal — a finite set that is not empty has a maximal point
// under a preorder. On inserting x, retain the old maximal point m if
// m is not below x; otherwise x is maximal by transitivity.
var FiniteMaximal = finiteMaximalThm{family.Add(registry.ProofEntry{
	Name: "FiniteMaximal",
	Key:  "prop_d11d6b2f66575b70",
	Reading: "Of the preorder only transitivity is spent: a reflexive cycle on " +
		"three points has no maximal point. s ≠ ∅ is needed because a maximal point " +
		"is a point of the set, and finiteness because ℕ under its order has none.",
	Build: Preorder.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
		},
		Conclusion: "∃m:A. maximal(R, s, m)",
	},
		func(a *Argument, R *Arrow2[A, A, Bool], pre Fact, s *Expr[Set[A]], finite, nonempty Fact) {
			a.Show(
				"finite induction gives a maximal point whenever the set is nonempty",
				ByInduction(finite_set.FiniteInduct, finite, Generalizing(nonempty),
					Case(
						"the empty set cannot satisfy the nonempty premise",
						Derive(func(b *Argument) {
							impossible := b.Assume()
							b.Show(
								"the premise contradicts itself",
								By(impossible))
						})),
					Case(
						"inserting a point preserves existence of a maximal point",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							t := b.FixAs[Set[A]]("t")
							carried := b.Assume()
							b.Assume()
							enlarged := b.TermAs[Set[A]]("insert(x, t)")
							nonempty := b.Unless(
								b.TermAs[Bool]("t = ∅"),
								"if t is empty, x is the only point of the enlarged set",
								Given(func(c *Argument, empty Fact) {
									c.Take(x)
									c.Show(
										"the sole point is maximal",
										BySets(empty, MaximalDef.At(R, enlarged, x)))
								}))
							m, maximal := b.ObtainAs[A](
								"the nonempty old set has a maximal point m",
								"∃m:A. maximal(R, t, m)",
								By(nonempty, carried))
							b.Cases(R.Apply(m, x))
							b.When(
								"if m is below x, x is maximal in the enlarged set",
								func(c *Argument, below Fact) {
									c.Take(x)
									c.Show(
										"an old point above x lies above m, hence below m and then below x",
										BySets(below, maximal, MaximalDef.At(R, t, m), MaximalDef.At(R, enlarged, x), Transitive.Read(pre)))
								})
							b.Otherwise(
								"if m is not below x, m stays maximal",
								func(c *Argument, notBelow Fact) {
									c.Take(m)
									c.Show(
										"x cannot violate maximality, and the old points already satisfy it",
										BySets(notBelow, maximal, MaximalDef.At(R, t, m), MaximalDef.At(R, enlarged, m)))
								})
						}))))
		}),
})}
