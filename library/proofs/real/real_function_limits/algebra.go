// algebra.go — the elementary limits and the algebra of limits (README,
// "The elementary limits", "The algebra of limits"): the constant and the
// identity, then the negative, the sum, the difference, the product, the
// scalar multiple and the reciprocal of functions with limits.
//
// The two engine facts every ε-δ body here obeys are stated once, in
// definitions.go's header.

package real_function_limits

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// LimitAtConst — a constant function tends to its value.
//
// Any radius answers any ε: the value at every point of the ball is k
// itself, at distance |k − k| = 0 from k, which is below ε. The radius
// is taken to be 1, whose positivity is a law of the order.
var LimitAtConst = limitAtConstThm{family.Add(registry.ProofEntry{
	Name: "LimitAtConst",
	Key:  "prop_9324d6174d7961f3",
	Build: family.Theorem("∀k c:real. (λx:real. k) ⟶ k (at c)",
		func(a *Argument, k, c *Expr[Real]) {
			a.Do(Unfold(RealLimitAtDef))
			a.FixAs[Real]()
			pos := a.Assume()
			a.Take(a.TermAs[Real]("&1"))
			a.Do(SplitConj(
				Case(
					"the radius 1 is positive",
					Cite(real_order_ring.ZeroLessThanOne)),
				Case(
					"and at every point of the ball the value is k, at distance 0 from k, which is below ε",
					Derive(func(b *Argument) {
						b.FixAs[Real]()
						b.Assume()
						b.Show(
							"|k − k| = 0 < ε",
							ByArith(pos))
					})),
			))
		}),
})}

// LimitAtId — the identity tends to the point.
//
// The radius is ε itself: the identity's value at a point of the ball
// of radius ε around c is that point, and the ball's own condition puts
// it within ε of c.
var LimitAtId = limitAtIdThm{family.Add(registry.ProofEntry{
	Name: "LimitAtId",
	Key:  "prop_51ef314f7f1b3992",
	Build: family.Theorem("∀c:real. (λx:real. x) ⟶ c (at c)",
		func(a *Argument, c *Expr[Real]) {
			a.Do(Unfold(RealLimitAtDef))
			eps := a.FixAs[Real]()
			pos := a.Assume()
			a.Take(eps)
			a.Do(SplitConj(
				Case(
					"the radius is ε itself, which is positive",
					By(pos)),
				Case(
					"and at every point of the ball the value is the "+
						"point itself, within ε of c by the ball's condition",
					Derive(func(b *Argument) {
						b.FixAs[Real]()
						ball := b.Assume()
						b.Show(
							"|x − c| < ε is the ball's second condition",
							By(ball))
					})),
			))
		}),
})}

// LimitAtNeg — the negative of a function tends to the negative of its
// limit.
//
// The same radius answers the same ε: |−f(x) − (−l)| = |f(x) − l|, so on
// the punctured ball where the values of f lie within ε of l, the values
// of −f lie within ε of −l.
var LimitAtNeg = limitAtNegThm{family.Add(registry.ProofEntry{
	Name: "LimitAtNeg",
	Key:  "prop_40fe31c3b209ddb6",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
		},
		Conclusion: "(λx:real. -f(x)) ⟶ -l (at c)",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l *Expr[Real], limit Fact) {
			near := a.Unfolded(limit, RealLimitAtDef)
			a.Do(Unfold(RealLimitAtDef))
			eps := a.FixAs[Real]()
			pos := a.Assume()
			d0, radius := a.Obtain(
				"f ⟶ l (at c) at ε hands over a radius δ₀ inside which the values of f are within ε of l",
				"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε",
				By(near.At(eps), pos))
			within := a.Have(
				"on the punctured ball of radius δ₀ the values of f are within ε of l",
				"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - l| < ε",
				By(radius))
			a.Take(d0)
			a.Do(SplitConj(
				Case(
					"the radius δ₀ is positive, as it was obtained",
					By(radius)),
				Case(
					"and at every point of the ball the value of −f is within ε of −l",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						ball := b.Assume()
						estimate := b.Have(
							"x lies in the ball, so f(x) is within ε of l",
							"|f(x) - l| < ε",
							By(within.At(x), ball))
						b.Show(
							"|−f(x) − (−l)| = |f(x) − l| < ε",
							ByArith(estimate))
					})),
			))
		}),
})}

// LimitAtAdd — the sum of two functions tends to the sum of their
// limits.
//
// Each limit is given half of ε: on the punctured ball the two limits
// share at ε/2, f is within ε/2 of l and g within ε/2 of m, and the
// triangle inequality puts f + g within ε/2 + ε/2 = ε of l + m.
var LimitAtAdd = limitAtAddThm{family.Add(registry.ProofEntry{
	Name: "LimitAtAdd",
	Key:  "prop_d100ed9373525596",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
		},
		Conclusion: "(λx:real. f(x) + g(x)) ⟶ l + m (at c)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], limits Fact) {
			shared := a.Have(
				"the two limits share, for every positive ε, one punctured "+
					"ball on which f is within ε of l and g within ε of m",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ (∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε ∧ |g(x) - m| < ε)",
				},
				By(LimitAtCommonRadius, limits))
			a.Do(Unfold(RealLimitAtDef))
			a.FixAs[Real]()
			pos := a.Assume()
			half := a.TermAs[Real]("ε / &2")
			halfPos := a.Have(
				"half of ε is positive",
				"&0 < ε / &2",
				ByArith(pos))
			d0, radius := a.Obtain(
				"the shared ball at ε/2 has some radius δ₀, inside "+
					"which f is within ε/2 of l and g within ε/2 of m",
				"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε / &2 ∧ |g(x) - m| < ε / &2",
				By(shared.At(half), halfPos))
			within := a.Have(
				"on the punctured ball of radius δ₀, f is within ε/2 of l and g within ε/2 of m",
				"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - l| < ε / &2 ∧ |g(x) - m| < ε / &2",
				By(radius))
			a.Take(d0)
			a.Do(SplitConj(
				Case(
					"the radius δ₀ is positive, as it was obtained",
					By(radius)),
				Case(
					"and at every point of the ball the value of f + g is within ε of l + m",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						ball := b.Assume()
						near := b.Have(
							"x lies in the ball, so f(x) is within ε/2 of l and g(x) within ε/2 of m",
							"|f(x) - l| < ε / &2 ∧ |g(x) - m| < ε / &2",
							By(within.At(x), ball))
						b.Show(
							"|(f(x) + g(x)) − (l + m)| ≤ |f(x) − l| + |g(x) − m| < ε/2 + ε/2 = ε",
							ByArith(near))
					})),
			))
		}),
})}

// LimitAtSub — the difference of two functions tends to the difference
// of their limits.
//
// f − g is f + (−g): the negative of g tends to −m, so the sum of f and
// −g tends to l + (−m), which is l − m.
var LimitAtSub = limitAtSubThm{family.Add(registry.ProofEntry{
	Name: "LimitAtSub",
	Key:  "prop_b0a3f94ef8de919e",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
		},
		Conclusion: "(λx:real. f(x) - g(x)) ⟶ l - m (at c)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], limits Fact) {
			negG := a.Have(
				"g tends to m, so its negative tends to −m",
				"(λx:real. -g(x)) ⟶ -m (at c)",
				By(LimitAtNeg, limits))
			// Subtraction is addition of the negation, in the function and
			// in the limit alike.
			a.Do(Simp(Fwd(real_ring.RealSubDef)))
			a.Show(
				"f tends to l and −g to −m, so f + (−g) tends to l + (−m)",
				By(LimitAtAdd, limits, negG))
		}),
})}

// LimitAtMul — the product of two functions tends to the product of
// their limits. Along every sequence approaching c without touching it,
// the two functions give convergent sequences. Their product converges
// by real_sequences.LimitMul, and the sequential criterion gives the
// function limit.
var LimitAtMul = limitAtMulThm{family.Add(registry.ProofEntry{
	Name: "LimitAtMul",
	Key:  "prop_b22a223f61b3b1e2",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
		},
		Conclusion: "(λx:real. f(x) * g(x)) ⟶ l * m (at c)",
	},
		func(arg *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], toL, toM Fact) {
			sequential := arg.Have(
				"along every sequence approaching c without touching it, the product tends to l·m",
				"∀a:(num → real). (∀n:num. a(n) ≠ c) ∧ a ⟶ c ⇒ (λx:real. f(x) * g(x)) ∘ a ⟶ l * m",
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, Real]]()
					approach := b.Assume()
					fSequence := b.Have(
						"f carries the sequence to a sequence tending to l",
						"f ∘ a ⟶ l",
						By(approach, toL, LimitAtImpSequential))
					gSequence := b.Have(
						"g carries the sequence to a sequence tending to m",
						"g ∘ a ⟶ m",
						By(approach, toM, LimitAtImpSequential))
					b.Do(Unfold(functions.ComposeApply))
					b.Show(
						"the product of these two sequences tends to l·m",
						By(fSequence, gSequence, real_sequences.LimitMul))
				}))
			arg.Show(
				"the sequential criterion gives the product's limit at c",
				By(sequential, SequentialImpLimitAt))
		}),
})}

// LimitAtScale — a scalar multiple of a function tends to the scalar
// multiple of its limit.
//
// k·f is the product of the constant function k and f: the constant
// tends to k and f to l, so the product tends to k·l.
var LimitAtScale = limitAtScaleThm{family.Add(registry.ProofEntry{
	Name: "LimitAtScale",
	Key:  "prop_cd6f25d3d1349b45",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l k:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
		},
		Conclusion: "(λx:real. k * f(x)) ⟶ k * l (at c)",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l, k *Expr[Real], limit Fact) {
			a.Show(
				"the constant function k tends to k and f to l, so their product k·f tends to k·l",
				By(LimitAtMul, LimitAtConst.At(k, c), limit))
		}),
})}

// LimitAtInv — the reciprocal of a function with a nonzero limit tends to
// the reciprocal of the limit.
//
// Two balls are met. On the first, the values of f stay away from zero:
// within |l|/2 of l, |f(x)| exceeds |l|/2. On the second, f is within the
// tolerance η = ε·|l|·|l|/2 of l. On the smaller of the two the distance
// between the reciprocals is the distance between the values divided by
// their sizes, |1/f(x) − 1/l| = |f(x) − l| / (|f(x)|·|l|), and the two
// bounds make it less than η / ((|l|/2)·|l|) = ε.
var LimitAtInv = limitAtInvThm{family.Add(registry.ProofEntry{
	Name: "LimitAtInv",
	Key:  "prop_be4d933b1d3cadd8",
	Build: family.Sections(Statement{
		Binders: "∀f:(real → real). ∀c l:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"l ≠ &0",
		},
		Conclusion: "(λx:real. real_inv(f(x))) ⟶ real_inv(l) (at c)",
		Abbrev: Abbrev{
			{Name: "tolerance", Text: "ε * |l| * |l| / &2"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The estimate at one value: a number u larger than |l|/2 in size
			// and within ε·|l|·|l|/2 of l has its reciprocal within ε of l's.
			estimate := ctx.Lemma(Statement{
				Binders: "∀u l ε:real.",
				Hypotheses: []string{
					"&0 < ε",
					"l ≠ &0",
					"|l| / &2 < |u|",
					"|u - l| < ε * |l| * |l| / &2",
				},
				Conclusion: "|real_inv(u) - real_inv(l)| < ε",
			},
				func(s *Argument, u, l, ε *Expr[Real], bounds Fact) {
					difference, product := s.TermAs[Real]("real_inv(u) - real_inv(l)"), s.TermAs[Real]("u * l")
					sizes := s.TermAs[Real]("|u| * |l|")

					lPos := s.Have(
						"l is not zero, so |l| is positive",
						"&0 < |l|",
						By(real_sgn_abs.AbsPosIffNonzero.At(l), bounds))
					uPos := s.Have(
						"|u| exceeds |l|/2, so it is positive too",
						"&0 < |u|",
						ByArith(lPos, bounds))
					identity := s.Have(
						"neither u nor l is zero, so the difference of the reciprocals, multiplied by u·l, is l − u",
						"(real_inv(u) - real_inv(l)) * (u * l) = l - u",
						ByArith(uPos, bounds))
					distance := s.Have(
						"taking absolute values: |1/u − 1/l|·(|u|·|l|) = |u − l|",
						"|real_inv(u) - real_inv(l)| * (|u| * |l|) = |u - l|",
						ByArith(identity, real_sgn_abs.AbsMul.At(difference, product), real_sgn_abs.AbsMul.At(u, l)))
					scaled := s.Have(
						"|u − l| < ε·|l|·|l|/2 < ε·(|u|·|l|), since |l| < 2|u|",
						"|u - l| < ε * (|u| * |l|)",
						ByArith(
							real_order_ring.LessThanMulLeft.At(
								s.TermAs[Real]("ε * |l|"), s.TermAs[Real]("|l|"), s.TermAs[Real]("&2 * |u|")),
							lPos,
							bounds))
					s.Show(
						"so |1/u − 1/l|·(|u|·|l|) < ε·(|u|·|l|), and the positive factor |u|·|l| cancels",
						ByArith(
							real_order_ring.LessThanCancelMulRight.At(s.TermAs[Real]("|real_inv(u) - real_inv(l)|"), ε, sizes),
							distance,
							scaled,
							lPos,
							uPos))
				})

			// A nonzero limit keeps the function away from zero: on a punctured
			// ball where f is within |l|/2 of l, |f(x)| exceeds |l|/2.
			awayFromZero := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀c l:real.",
				Hypotheses: []string{
					"f ⟶ l (at c)",
					"l ≠ &0",
				},
				Conclusion: "∃δ:real. &0 < δ ∧ (∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |l| / &2 < |f(x)|)",
			},
				func(s *Argument, f *Arrow[Real, Real], c, l *Expr[Real], given Fact) {
					parts := s.Conjuncts(
						given,
						"f tends to l at c",
						"and l is not zero")
					limit, nonzero := parts[0], parts[1]
					near := s.Unfolded(limit, RealLimitAtDef)
					half := s.TermAs[Real]("|l| / &2")
					halfPos := s.Have(
						"l is not zero, so half of |l| is positive",
						"&0 < |l| / &2",
						ByArith(real_sgn_abs.AbsPosIffNonzero.At(l), nonzero))
					d0, radius := s.ObtainAs[Real](
						"f ⟶ l (at c) at |l|/2 hands over a radius δ₀ inside which the values of f are within |l|/2 of l",
						"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < |l| / &2",
						By(near.At(half), halfPos))
					within := s.Have(
						"on the punctured ball of radius δ₀ the values of f are within |l|/2 of l",
						"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - l| < |l| / &2",
						By(radius))
					s.Take(d0)
					s.Do(SplitConj(
						Case(
							"the radius δ₀ is positive, as it was obtained",
							By(radius)),
						Case(
							"and at every point of the ball |f(x)| exceeds |l|/2",
							Derive(func(b *Argument) {
								x := b.FixAs[Real]()
								ball := b.Assume()
								deviation := b.Have(
									"x lies in the ball, so f(x) is within |l|/2 of l",
									"|f(x) - l| < |l| / &2",
									By(within.At(x), ball))
								b.Show(
									"|l| ≤ |f(x)| + |f(x) − l| < |f(x)| + |l|/2",
									ByArith(deviation))
							})),
					))
				})

			return ctx.Theorem(headline,
				func(a *Argument, f *Arrow[Real, Real], c, l *Expr[Real], given Fact) {
					parts := a.Conjuncts(
						given,
						"f tends to l at c",
						"and l is not zero")
					limit, nonzero := parts[0], parts[1]
					near := a.Unfolded(limit, RealLimitAtDef)
					d0, awayBall := a.ObtainAs[Real](
						"a nonzero limit keeps f away from zero: on a punctured ball of radius δ₀, |f(x)| exceeds |l|/2",
						"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |l| / &2 < |f(x)|",
						By(At(awayFromZero, f, c, l), given))
					awayParts := a.Conjuncts(
						awayBall,
						"δ₀ is positive",
						"and on the punctured ball of radius δ₀, |f(x)| exceeds |l|/2")
					d0Pos, away := awayParts[0], awayParts[1]
					a.Do(Unfold(RealLimitAtDef))
					eps := a.FixAs[Real]()
					pos := a.Assume()
					lPos := a.Have(
						"l is not zero, so |l| is positive",
						"&0 < |l|",
						By(real_sgn_abs.AbsPosIffNonzero.At(l), nonzero))

					// Every statement writes the tolerance out; the one Go constant
					// keeps the spellings one.
					const tolerance = "ε * |l| * |l| / &2"
					η := a.TermAs[Real]("«tolerance»")
					ηPos := a.Have(
						"so the tolerance η = ε·|l|·|l|/2 is positive",
						"&0 < «tolerance»",
						ByArith(pos, lPos))
					d1, radius := a.ObtainAs[Real](
						"f ⟶ l (at c) at η hands over a radius δ₁ inside which the values of f are within η of l",
						"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < «tolerance»",
						By(near.At(η), ηPos))
					within := a.Have(
						"on the punctured ball of radius δ₁ the values of f are within η of l",
						"∀x:real. &0 < |x - c| ∧ |x - c| < δ₁ ⇒ |f(x) - l| < «tolerance»",
						By(radius))

					a.Take(a.TermAs[Real]("min(δ₀, δ₁)"))
					a.Do(SplitConj(
						Case(
							"the smaller radius is positive, both radii being positive",
							By(real_sup_inf.LessThanMin.At(d0, d1, a.TermAs[Real]("&0")), d0Pos, radius)),
						Case(
							"and at every point of its punctured ball the reciprocal of f is within ε of the reciprocal of l",
							Derive(func(b *Argument) {
								x := b.FixAs[Real]()
								ball := b.Assume()
								inBoth := b.Have(
									"a distance below the smaller radius is below δ₀ and below δ₁",
									"|x - c| < δ₀ ∧ |x - c| < δ₁",
									By(real_sup_inf.LessThanMin.At(d0, d1, b.TermAs[Real]("|x - c|")), ball))
								bounds := b.Have(
									"so x lies in both balls: |f(x)| exceeds |l|/2, and f(x) is within η of l",
									"|l| / &2 < |f(x)| ∧ |f(x) - l| < «tolerance»",
									By(away.At(x), within.At(x), ball, inBoth))
								b.Show(
									"the estimate at the value f(x): |1/f(x) − 1/l| < ε",
									By(At(estimate, b.TermAs[Real]("f(x)"), l, eps), pos, nonzero, bounds))
							})),
					))
				})
		}),
})}
