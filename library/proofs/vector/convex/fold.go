// fold.go — the cone over a convex set is closed under finite sums,
// and the chapter's theorem is that closure read at total weight one.
//
// The cone is closed under addition: two of its points, at heights
// whose total is positive, sum to a point of it at the summed height.
// Adding one point at a time carries that law along a whole finite
// family. A family of points of s, each scaled by a height of its own,
// sums to the total height above a single point of s — provided only
// that the total is positive. No individual height need be positive,
// and nothing is rescaled between steps.
//
// The induction carries the height beside the point because neither
// determines the other. What a fold accumulates is a vector, and the
// only thing about it that survives one more term is that it is SOME
// height above SOME point of s: the height is the weight totalled so
// far, which the fold over ℝ tracks in step with the fold over the
// module, and the point is what convexity supplies when the two are
// combined. Carrying the point alone would leave the next step nothing
// to scale it by; carrying the height alone would say nothing about s.
//
// The pair fails in exactly one place — a total height of zero, where
// there is no point to carry. There every term of the fold is
// weightless and the fold is the zero vector, which stands at height
// zero above any point of s whatever; the point just laid in is one.
//
// The chapter's headline is that theorem read at total weight one.
// Weights totalling one total more than nothing, so the cone applies
// and the family stands at weight one above a point of s; and a weight
// of one scales nothing. The height that carried the whole induction
// then disappears, leaving the combination equal to the point it
// stands above — a point of s.

package convex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ConeIterate — the closure under addition, applied once per point of
// the index set as it grows.
//
// The induction runs over the index set in the strong form, because
// each step asks for exactly what that form grants: the index laid in
// is new and the set it enlarges is finite, which is what the two
// folds' recursion clauses need before they will give up a term. The
// step then reaches the two-point law holding the new point at its own
// height beside the point the rest already stands above, at the height
// the rest has accumulated. Their total is the enlarged total, which
// the step assumes positive, so neither height is asked to be positive
// on its own and no weight is rescaled.
var ConeIterate = coneIterateThm{family.Add(registry.ProofEntry{
	Name: "ConeIterate",
	Key:  "prop_3c8e8b4a6ccb6a48",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(num → real). ∀k:set(num). ∀u:(num → real). ∀x:(num → num → real).",
			Hypotheses: []string{
				"convex(s)",
				"finite(k)",
				"∀i:num. i ∈ k ⇒ &0 ≤ u(i) ∧ x(i) ∈ s",
				"&0 < Σ_{i∈k} u(i)",
			},
			Conclusion: "∃w:(num → real). w ∈ s ∧ Σ_{i∈k} u(i) • x(i) = (Σ_{i∈k} u(i)) • w",
		},
		func(
			a *Argument,
			s *Expr[Set[Fun[Nat, Real]]],
			k *Expr[Set[Nat]],
			u *Arrow[Nat, Real],
			x *Arrow[Nat, Fun[Nat, Real]],
			convexity, finite, admissible, totalPositive Fact,
		) {

			// The property the induction is run on: over an index set, a
			// family admissible there and weighing more than nothing stands
			// at its total weight above a point of s. The set and the family
			// are fixed outside it; the two hypotheses sit inside, because
			// the empty index set meets neither and the property must still
			// hold of it.
			standsAbove := a.TermAs[Set[Set[Nat]]](
				"λt:set(num). " +
					"    (∀i:num. i ∈ t ⇒ &0 ≤ u(i) ∧ x(i) ∈ s) ⇒ " +
					"    &0 < Σ_{i∈t} u(i) ⇒ " +
					"    (∃w:(num → real). w ∈ s ∧ Σ_{i∈t} u(i) • x(i) = (Σ_{i∈t} u(i)) • w)")

			a.Show(
				"so the combination stands above a point of s over every finite index set, k among them",
				ByInduction(finite_set.FiniteInductFresh.At(standsAbove, k), finite, admissible, totalPositive,

					Case(
						"∅: nothing is indexed, so the total weight is zero "+
							"and the hypothesis of positive weight is never met",
						By(Normalized, real_sum.Clauses, real_order_ring.LessThanIrrefl)),

					Case(
						"insert: the new point enters at its own weight, beside the point the rest already stands above",
						Derive(func(b *Argument) {
							b.Fix("y")                       // the index laid in
							b.Fix("t")                       // the set it enlarges
							carried := b.Assume()            // the property at t, with y ∉ t and t finite
							admissibleEnlarged := b.Assume() // the family over insert(y, t)
							weighsEnlarged := b.Assume()     // and its total weight there

							// The one thing the fold mechanism asks of the vectors,
							// read at the real ring.
							vectors := vec_space.MonoidalVecAdd.Read(real_ring.CommRing)

							// One turn of each recursion. The index is new and the
							// set it enlarges is finite, so both clauses give up
							// exactly the new term.
							enlargedWeight := b.Have(
								"the total weight grows by exactly the new point's weight",
								"Σ_{i∈insert(y, t)} u(i) = u(y) + Σ_{i∈t} u(i)",
								By(carried, real_sum.Clauses))
							enlargedFold := b.Have(
								"and the combination by exactly the new point at that weight",
								"Σ_{i∈insert(y, t)} u(i) • x(i) = u(y) • x(y) + Σ_{i∈t} u(i) • x(i)",
								By(vectors, carried, monoidal.OneTurn))

							// What the enlarged index set assumes, read at its two
							// parts: the smaller set, and the point laid in.
							admissibleRest := b.Have(
								"the family is admissible over the smaller index set too",
								"∀i:num. i ∈ t ⇒ &0 ≤ u(i) ∧ x(i) ∈ s",
								By(admissibleEnlarged, set_basic.InInsert))
							weightsRest := b.Have(
								"in particular its weights there are nonnegative",
								"∀i:num. i ∈ t ⇒ &0 ≤ u(i)",
								By(admissibleRest))
							restNonneg := b.Have(
								"so the weight accumulated so far is at least zero",
								"&0 ≤ Σ_{i∈t} u(i)",
								By(weightsRest, real_sum.Nonneg))
							newPoint := b.Have(
								"and the new index carries a nonnegative weight at a point of s",
								"&0 ≤ u(y) ∧ x(y) ∈ s",
								By(admissibleEnlarged, set_basic.InInsert))

							// The point the rest stands above — call it w₀. The
							// height it stands at is nonnegative and nothing makes it
							// positive; where that height vanishes the property
							// carried says nothing, so a point must be named
							// outright, and the one just laid in serves, every point
							// of s standing at height zero from the zero vector.
							_, stands := b.Obtain(
								"the combination over the smaller set stands at its own weight above a point of s",
								"∃w:(num → real). w ∈ s ∧ Σ_{i∈t} u(i) • x(i) = (Σ_{i∈t} u(i)) • w",
								ByCaseStep(b.Term("&0 < Σ_{i∈t} u(i)"),
									Case(
										"positive: the smaller set meets both of the property's "+
											"hypotheses, and the property carried over it is the claim",
										Given(func(c *Argument, carriesWeight Fact) {
											c.Show(
												"so the property at t applies",
												By(admissibleRest, carriesWeight, carried))
										})),
									Case(
										"vanishing: every weight is then zero and the combination is "+
											"the zero vector, which stands at height zero above the new point",
										Given(func(c *Argument, weightless Fact) {
											vanishes := c.Have(
												"a nonnegative total that is not positive is zero",
												"Σ_{i∈t} u(i) = &0",
												By(weightless, restNonneg, real_order_ring.LessEqSplit))
											silent := c.Have(
												"so the combination over t contributes nothing",
												"Σ_{i∈t} u(i) • x(i) = vec_zero",
												By(weightsRest, vanishes, carried, VanishingWeights))

											c.Take(c.TermAs[Fun[Nat, Real]]("x(y)"))
											atZeroHeight := c.Have(
												"and zero height above the new point is that same zero vector",
												"(Σ_{i∈t} u(i)) • x(y) = vec_zero",
												By(vanishes, vec_space.ZeroSmul.Read(real_ring.CommRing)))
											c.Show(
												"both sides are the zero vector, and the new point is a point of s",
												By(silent, atZeroHeight, newPoint))
										}))))

							// The two-point law, at the new point's weight and the
							// weight carried. Their total is the enlarged total, which
							// the step assumes positive — neither weight is asked to be.
							totalPositive := b.Have(
								"the two weights total the enlarged weight, which is positive",
								"&0 < u(y) + Σ_{i∈t} u(i)",
								By(enlargedWeight, weighsEnlarged))
							combined := b.Have(
								"so the cone is closed on the new point and the point carried",
								"∃w:(num → real). w ∈ s ∧ u(y) • x(y) + (Σ_{i∈t} u(i)) • w₀ = (u(y) + Σ_{i∈t} u(i)) • w",
								By(convexity, restNonneg, totalPositive, stands, newPoint, PositiveCombination))

							b.Show(
								"which, read back through the two recursion clauses, "+
									"is the enlarged combination at the enlarged weight",
								By(combined, enlargedFold, enlargedWeight, stands))
						}))))
		}),
})}

// Combination — a convex set holds every convex combination of finitely
// many of its points.
//
// Nothing is proved here that the cone did not already carry: the
// weights total one, which is more than nothing, so the cone reaches a
// point of s and puts the combination at total weight above it. At
// weight one that scaling is the identity, so the combination is the
// point itself.
var Combination = combinationThm{family.Add(registry.ProofEntry{
	Name: "Combination",
	Key:  "prop_9bb2437951dcfafc",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(num → real). ∀k:set(num). ∀u:(num → real). ∀x:(num → num → real).",
			Hypotheses: []string{
				"convex(s)",
				"finite(k)",
				"∀i:num. i ∈ k ⇒ &0 ≤ u(i) ∧ x(i) ∈ s",
				"Σ_{i∈k} u(i) = &1",
			},
			Conclusion: "Σ_{i∈k} u(i) • x(i) ∈ s",
		},
		func(
			a *Argument,
			s *Expr[Set[Fun[Nat, Real]]],
			k *Expr[Set[Nat]],
			u *Arrow[Nat, Real],
			x *Arrow[Nat, Fun[Nat, Real]],
			convexity, finite, admissible, totalOne Fact,
		) {

			// The cone asks for a positive total, which a total of one is:
			// the unit stands above zero.
			_, stands := a.Obtain(
				"the combination stands at its total weight above a point of s — call it w₀",
				"∃w:(num → real). w ∈ s ∧ Σ_{i∈k} u(i) • x(i) = (Σ_{i∈k} u(i)) • w",
				By(convexity, finite, admissible, totalOne, real_order_ring.ZeroLessThanOne, ConeIterate))

			atUnitHeight := a.Have(
				"and a total weight of one leaves that point where it stands",
				"(Σ_{i∈k} u(i)) • w₀ = w₀",
				By(totalOne, vec_space.SmulOne.Read(real_ring.CommRing)))

			a.Show(
				"so the combination is that point, and the point is a point of s",
				By(Normalized, stands, atUnitHeight))
		}),
})}
