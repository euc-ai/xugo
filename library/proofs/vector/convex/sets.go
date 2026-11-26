// sets.go — what the definition says directly: the condition restated
// with one parameter, and the sets that satisfy it for no reason of
// their own.
//
// Nothing here is constructed. Each member is the definition read back
// — at a different pair of weights, or at a set whose membership
// settles the question before the weights are looked at — and in none
// of them does the module enter: the weighted average is carried from
// hypothesis to conclusion as it stands and is never expanded. So none
// of them names a dimension either.
//
// `Segment` is the definition at a parameter and its complement instead
// of at two independent weights. The chapter defines convexity the other
// way round because that is what a fold's recursion step produces, but
// the one-parameter test is the form convexity is usually stated in, and
// the form a consumer holding a single parameter has to hand — so the
// two are proved equivalent here. Each direction is the other form with
// its weights renamed, and the whole content is that `c` and `&1 - d`
// are the same number.

package convex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// Segment — convexity tested one parameter at a time.
//
// A pair of weights totalling one is a parameter and its complement,
// and that translation is the whole proof. Going to the test, the pair
// is (&1 - t, t): the first weight is nonnegative because t is at most
// one, and taking t away from one and adding it back returns one.
// Coming from it, the pair (c, d) is read at the parameter d, which is
// at most one because the weight beside it is nonnegative, and whose
// complement &1 - d is c.
var Segment = segmentThm{family.Add(registry.ProofEntry{
	Name: "Segment",
	Key:  "prop_567dc1f53db2a60a",
	Build: family.Theorem(
		"∀s:set(num → real). "+
			"    convex(s) ⇔ "+
			"    (∀x y:(num → real). ∀t:real. x ∈ s ∧ y ∈ s ∧ &0 ≤ t ∧ t ≤ &1 ⇒ (&1 - t) • x + t • y ∈ s)",
		func(a *Argument, s *Expr[Set[Fun[Nat, Real]]]) {
			a.Iff()
			a.Forward(
				"the test's parameter makes the pair (&1 - t, t): nonnegative weights totalling one",
				func(a *Argument, convexity Fact) {
					// The test's own binders: the two points, then
					// the parameter.
					a.Fix("x")
					a.Fix("y")
					a.Fix("t")
					bounds := a.Assume()

					complementNonneg := a.Have(
						"the complement of a parameter at most one is nonnegative",
						"&0 ≤ &1 - t",
						ByArith(bounds))
					sumOne := a.Have(
						"and taking t from one and adding it back returns one",
						"(&1 - t) + t = &1",
						Cite(real_ring.SubAddRight))

					a.Show(
						"so convexity at that pair holds the point the test names",
						By(convexity, bounds, complementNonneg, sumOne, ConvexDef))
				})
			a.Backward(
				"convexity asks about a pair (c, d), and that pair is the test read at d, whose complement is c",
				Simp(Fwd(ConvexDef)),
				Given(func(a *Argument, segment Fact) {
					// The definition's own binders: the two points,
					// then the two weights.
					a.Fix("x")
					a.Fix("y")
					a.Fix("c")
					a.Fix("d")
					weights := a.Assume()

					atMostOne := a.Have(
						"d is at most one, the weight beside it being nonnegative",
						"d ≤ &1",
						ByArith(weights))
					complement := a.Have(
						"and c is what one leaves after d",
						"c = &1 - d",
						ByArith(weights))

					a.Show(
						"so the test read at d is the pair's own average of x and y",
						By(segment, weights, atMostOne, complement))
				}))
		}),
})}

// Empty — the convexity condition has no pair of points to be read at.
//
// The condition is an implication whose hypothesis asks for two points
// of the set; nothing is a point of ∅, so the hypothesis fails at every
// pair of candidates and every choice of weights, and the average it
// would have been read at is never formed.
var Empty = emptyThm{family.Add(registry.ProofEntry{
	Name: "Empty",
	Key:  "prop_d076a78fdc941991",
	Build: family.Theorem(
		"convex(∅)",
		BySets(ConvexDef)),
})}

// Univ — convexity is unconditional on 𝕌: the condition's conclusion
// is a membership every vector satisfies.
//
// Whatever average the two points and the two weights determine is a
// point of 𝕌, so the conclusion holds before anything asked of the
// weights is read, and the average is never expanded to see what it
// is.
var Univ = univThm{family.Add(registry.ProofEntry{
	Name:  "Univ",
	Key:   "prop_1cf7718a8381b9c0",
	Build: family.Theorem("convex(𝕌)", BySets(ConvexDef)),
})}

// Inter — an intersection of two convex sets is convex.
//
// A weighted average of two points of the intersection is a weighted
// average of two points of s and equally of two points of t, so each
// hypothesis lands it in its own set, and a point of both sets is a
// point of the intersection. The two conditions are read at the same
// two points and the same two weights throughout: the condition on the
// intersection is their conjunction and nothing more.
var Inter = interThm{family.Add(registry.ProofEntry{
	Name: "Inter",
	Key:  "prop_72ca43c09c0b228a",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(num → real).",
			Hypotheses: []string{
				"convex(s)",
				"convex(t)",
			},
			Conclusion: "convex(s ∩ t)",
		},
		BySets(ConvexDef)),
})}
