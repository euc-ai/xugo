// uniform.go — uniform continuity: one radius for every centre. It
// implies continuity on the set, and on a compact set — a closed bounded
// interval above all — continuity implies it (Heine–Cantor).

package real_continuous

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// UniformlyContinuousContinuous — a function uniformly continuous on s is
// continuous on s. At a point c of s, the one radius uniform continuity
// gives for ε serves c: a point x of s within it, paired with c, has its
// value within ε of f(c).
var UniformlyContinuousContinuous = uniformlyContinuousContinuousThm{family.Add(registry.ProofEntry{
	Name: "UniformlyContinuousContinuous",
	Key:  "prop_2e7121a1e0d9a64c",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_uniformly_continuous_on(s, f)",
		},
		Conclusion: "real_continuous_on(s, f)",
	},
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], uniform Fact) {
			near := a.Unfolded(uniform, RealUniformlyContinuousOnDef)
			a.Do(Unfold(RealContinuousOnDef))
			c := a.FixAs[Real]()
			inS := a.Assume()
			eps := a.FixAs[Real]()
			pos := a.Assume()
			d0, radius := a.ObtainAs[Real](
				"uniform continuity answers ε with one radius δ₀ for every pair of points of s",
				"∃δ:real. &0 < δ ∧ ∀x y:real. x ∈ s ∧ y ∈ s ∧ |x - y| < δ ⇒ |f(x) - f(y)| < ε",
				By(near.At(eps), pos))
			held := a.Conjuncts(
				radius,
				"δ₀ is positive",
				"inside δ₀ any two points of s have values within ε of each other")
			a.Take(d0)
			a.Do(SplitConj(
				Case(
					"the radius δ₀ is positive",
					By(held[0])),
				Case(
					"and a point of s inside it has its value within ε of f(c)",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						inside := b.Assume()
						b.Show(
							"x and c are two points of s within δ₀ of each other",
							By(held[1].At(x, c), inS, inside))
					})),
			))
		}),
})}

// ContinuousCompactUniformlyContinuous — Heine–Cantor: a function
// continuous on a compact set of reals is uniformly continuous there.
//
// Suppose some ε > 0 has no radius. Then for every n the radius
// 1/(n + 1) is beaten by a pair of points of s within it of each other
// whose values are not within ε, and choosing one pair for each n gives
// two sequences x and y in s. Compactness gives a subsequence x ∘ σ
// tending to a point l of s; since σ(k) ≥ k, the differences
// y(σ(k)) − x(σ(k)) lie within 1/(k + 1) of 0 and so tend to 0.
// Continuity at l answers ε/2 with a radius δ₀, and from some index N on,
// x(σ(n)) lies within δ₀/2 of l and y(σ(n)) within δ₀/2 of x(σ(n)). At
// n = N both points then lie within δ₀ of l, their values within ε/2 of
// f(l) and so within ε of each other — against the choice of the pair.
var ContinuousCompactUniformlyContinuous = continuousCompactUniformlyContinuousThm{family.Add(registry.ProofEntry{
	Name: "ContinuousCompactUniformlyContinuous",
	Key:  "prop_feb62068178618ee",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"compact_in(s)",
			"real_continuous_on(s, f)",
		},
		Conclusion: "real_uniformly_continuous_on(s, f)",
	},
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], compact, continuous Fact) {
			near := a.Unfolded(continuous, RealContinuousOnDef)
			a.Do(Unfold(RealUniformlyContinuousOnDef))
			a.FixAs[Real]()
			pos := a.Assume()
			noRadius := a.SupposeNot()
			beaten := a.Have(
				"so every positive radius is beaten by a pair of points of s whose values are not within ε",
				"∀δ:real. &0 < δ ⇒ ∃x y:real. x ∈ s ∧ y ∈ s ∧ |x - y| < δ ∧ ¬(|f(x) - f(y)| < ε)",
				By(Normalized, noRadius))
			pairs := a.Have(
				"the radius 1/(n + 1) among them, for every n",
				"∀n:num. ∃u v:real. u ∈ s ∧ v ∈ s ∧ |u - v| < real_inv(&n + &1) ∧ ¬(|f(u) - f(v)| < ε)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					b.Show(
						"1/(n + 1) is a positive radius, so it is beaten too",
						ByArith(
							beaten.At(b.TermAs[Real]("real_inv(&n + &1)")),
							real_order_field.InvPos.At(b.TermAs[Real]("&n + &1"))))
				}))
			x, _, chosen := a.Obtain2As[Fun[Nat, Real], Fun[Nat, Real]](
				"choosing one such pair for every n gives two sequences in s",
				"∃x y:(num → real). ∀n:num. "+
					"    x(n) ∈ s ∧ y(n) ∈ s ∧ |x(n) - y(n)| < real_inv(&n + &1) ∧ ¬(|f(x(n)) - f(y(n))| < ε)",
				By(pairs))
			sigma, l, sub := a.Obtain2As[Fun[Nat, Nat], Real](
				"s is compact, so a subsequence x ∘ σ tends to a point l of s",
				"∃σ:(num → num). ∃l:real. (∀j:num. σ(j) < σ(j + 1)) ∧ x ∘ σ ⟶ l ∧ l ∈ s",
				By(real_topology.CompactSubsequence.At(s, x), chosen, compact))
			held := a.Conjuncts(
				sub,
				"σ is strictly increasing",
				"x ∘ σ ⟶ l",
				"l lies in s")
			// x ∘ σ read pointwise, λk. x(σ(k)), as the limit lemma below takes it.
			toL := a.Unfolded(held[1], functions.ComposeApply)
			bound := a.Have(
				"σ(k) ≥ k, so the differences y(σ(k)) − x(σ(k)) lie within 1/(σ(k) + 1) ≤ 1/(k + 1) of 0",
				"∀k:num. |y(σ(k)) - x(σ(k)) - &0| < real_inv(&k + &1)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Show(
						"the σ(k)-th pair lies within 1/(σ(k) + 1) of each other, and k ≤ σ(k)",
						ByArith(
							chosen.At(b.TermAs[Nat]("σ(k)")),
							held[0],
							nat_order.LessEqStrictlyIncreasing.At(sigma, k),
							real_order_field.InvAntitoneWeak.At(
								b.TermAs[Real]("&k + &1"),
								b.TermAs[Real]("&(σ(k)) + &1"))))
				}))
			_, radius := a.ObtainAs[Real](
				"f is continuous at the point l of s, which answers ε/2 with a radius δ₀",
				"∃δ:real. &0 < δ ∧ ∀z:real. z ∈ s ∧ |z - l| < δ ⇒ |f(z) - f(l)| < ε / &2",
				ByArith(near.At(l, a.TermAs[Real]("ε / &2")), held[2], pos),
				Named("δ₀"))
			ball := a.Conjuncts(
				radius,
				"δ₀ is positive",
				"inside δ₀ about l the values at points of s are within ε/2 of f(l)")
			halfPos := a.Have(
				"half of δ₀ is positive",
				"&0 < δ₀ / &2",
				ByArith(ball[0]))
			zero := a.TermAs[Real]("&0")
			differences := a.TermAs[Fun[Nat, Real]]("λk:num. y(σ(k)) - x(σ(k))")
			N, tail := a.ObtainAs[Nat](
				"x ∘ σ ⟶ l and the differences tend to 0: from some N on, "+
					"x(σ(n)) is within δ₀/2 of l and y(σ(n)) within δ₀/2 of x(σ(n))",
				"∃N:num. ∀n:num. N ≤ n ⇒ |x(σ(n)) - l| < δ₀ / &2 ∧ |y(σ(n)) - x(σ(n)) - &0| < δ₀ / &2",
				By(
					real_sequences.WithinReciprocalConverges.At(differences, zero),
					real_sequences.LimitCommonIndex.At(
						a.TermAs[Fun[Nat, Real]]("λk:num. x(σ(k))"),
						differences,
						l,
						zero,
						a.TermAs[Real]("δ₀ / &2")),
					bound,
					toL,
					halfPos))
			atN := a.Have(
				"at n = N itself",
				"|x(σ(N)) - l| < δ₀ / &2 ∧ |y(σ(N)) - x(σ(N)) - &0| < δ₀ / &2",
				By(tail.At(N), nat_order.LessEqRefl.At(N)))
			both := a.Have(
				"so x(σ(N)) and y(σ(N)) both lie within δ₀ of l",
				"|x(σ(N)) - l| < δ₀ ∧ |y(σ(N)) - l| < δ₀",
				ByArith(atN))
			pair := a.Conjuncts(
				chosen.At(a.TermAs[Nat]("σ(N)")),
				"x(σ(N)) lies in s",
				"y(σ(N)) lies in s",
				"the two lie within 1/(σ(N) + 1) of each other",
				"and their values are not within ε of each other")
			values := a.Have(
				"so f(x(σ(N))) and f(y(σ(N))) both lie within ε/2 of f(l)",
				"|f(x(σ(N))) - f(l)| < ε / &2 ∧ |f(y(σ(N))) - f(l)| < ε / &2",
				By(
					ball[1].At(a.TermAs[Real]("x(σ(N))")),
					ball[1].At(a.TermAs[Real]("y(σ(N))")),
					pair[0],
					pair[1],
					both))
			a.Show(
				"and so within ε of each other, against the choice of the pair",
				ByArith(pair[3], values))
		}),
})}

// ContinuousClosedIntervalUniformlyContinuous — a function continuous on
// a closed bounded interval ⟦a, b⟧ is uniformly continuous there: ⟦a, b⟧
// is compact, and Heine–Cantor applies.
var ContinuousClosedIntervalUniformlyContinuous = continuousClosedIntervalUniformlyContinuousThm{family.Add(registry.ProofEntry{
	Name: "ContinuousClosedIntervalUniformlyContinuous",
	Key:  "prop_798711fc60bb759b",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
		},
		Conclusion: "real_uniformly_continuous_on(⟦a, b⟧, f)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			arg.Show(
				"⟦a, b⟧ is compact, so Heine–Cantor applies",
				By(
					ContinuousCompactUniformlyContinuous.At(f, arg.TermAs[Set[Real]]("⟦a, b⟧")),
					real_topology.ClosedIntervalCompact.At(a, b),
					given))
		}),
})}

// NonexpansiveUniformlyContinuous — a function that moves no two points
// of the line further apart is uniformly continuous there: ε itself is a
// radius for ε.
var NonexpansiveUniformlyContinuous = nonexpansiveUniformlyContinuousThm{family.Add(registry.ProofEntry{
	Name: "NonexpansiveUniformlyContinuous",
	Key:  "prop_203d7844e2986a86",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real).",
		Hypotheses: []string{
			"∀x y:real. |f(x) - f(y)| ≤ |x - y|",
		},
		Conclusion: "real_uniformly_continuous_on(𝕌, f)",
	},
		func(a *Argument, f *Arrow[Real, Real], nonexpansive Fact) {
			a.Do(Unfold(RealUniformlyContinuousOnDef))
			eps := a.FixAs[Real]()
			pos := a.Assume()
			a.Take(eps)
			a.Do(SplitConj(
				Case(
					"the radius ε is positive",
					By(pos)),
				Case(
					"points within ε of each other have values within ε of each other",
					Derive(func(b *Argument) {
						u := b.FixAs[Real]()
						v := b.FixAs[Real]()
						near := b.Assume()
						b.Show(
							"|f(x) − f(y)| ≤ |x − y| < ε",
							ByArith(nonexpansive.At(u, v), near))
					})),
			))
		}),
})}

// ClampedUniformlyContinuous — a function continuous on ⟦a, b⟧, read
// through the clamp to ⟦a, b⟧, is uniformly continuous on the whole line:
// f is uniformly continuous on ⟦a, b⟧, a closed bounded interval
// (Heine–Cantor), and the clamp lands in ⟦a, b⟧ and moves no two points
// further apart, so the radius that serves f on ⟦a, b⟧ serves it on the line.
var ClampedUniformlyContinuous = clampedUniformlyContinuousThm{family.Add(registry.ProofEntry{
	Name: "ClampedUniformlyContinuous",
	Key:  "prop_36dfef61dea6bea9",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
		},
		Conclusion: "real_uniformly_continuous_on(𝕌, λx:real. f(max(a, min(b, x))))",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], ordered, continuous Fact) {
			onInterval := arg.Have(
				"f is uniformly continuous on ⟦a, b⟧, a closed bounded interval",
				"real_uniformly_continuous_on(⟦a, b⟧, f)",
				By(ordered, continuous, ContinuousClosedIntervalUniformlyContinuous.At(f, a, b)),
			)
			arg.Do(Unfold(RealUniformlyContinuousOnDef))
			arg.FixAs[Real]()
			pos := arg.Assume()
			r, radius := arg.ObtainAs[Real](
				"uniform continuity on ⟦a, b⟧ answers ε with a radius r",
				"∃r:real. &0 < r ∧ (∀u v:real. u ∈ ⟦a, b⟧ ∧ v ∈ ⟦a, b⟧ ∧ |u - v| < r ⇒ |f(u) - f(v)| < ε)",
				By(pos, onInterval, RealUniformlyContinuousOnDef.At(arg.TermAs[Set[Real]]("⟦a, b⟧"), f)),
			)
			arg.Take(r)
			arg.Do(SplitConj(
				Case(
					"r is positive",
					By(radius),
				),
				Case(
					"two points within r have their clamps in ⟦a, b⟧ and within r",
					Derive(func(c *Argument) {
						x := c.FixAs[Real]()
						y := c.FixAs[Real]()
						near := c.Assume()
						xRange := c.Have(
							"the clamp of x lies between a and b",
							"a ≤ max(a, min(b, x)) ∧ max(a, min(b, x)) ≤ b",
							By(ordered, real_sup_inf.ClampRange.At(a, b, x)),
						)
						xIn := c.Have(
							"so it is a point of ⟦a, b⟧",
							"max(a, min(b, x)) ∈ ⟦a, b⟧",
							By(xRange, real_topology.ClosedIntervalMembership.At(c.TermAs[Real]("max(a, min(b, x))"), a, b)),
						)
						yRange := c.Have(
							"the clamp of y lies between a and b",
							"a ≤ max(a, min(b, y)) ∧ max(a, min(b, y)) ≤ b",
							By(ordered, real_sup_inf.ClampRange.At(a, b, y)),
						)
						yIn := c.Have(
							"so it is a point of ⟦a, b⟧",
							"max(a, min(b, y)) ∈ ⟦a, b⟧",
							By(yRange, real_topology.ClosedIntervalMembership.At(c.TermAs[Real]("max(a, min(b, y))"), a, b)),
						)
						contracted := c.Have(
							"the clamp moves x and y no further apart",
							"|max(a, min(b, x)) - max(a, min(b, y))| ≤ |x - y|",
							By(real_sup_inf.ClampNonexpansive.At(a, b, x, y)),
						)
						clampsNear := c.Have(
							"so their clamps are within r",
							"|max(a, min(b, x)) - max(a, min(b, y))| < r",
							By(
								contracted,
								near,
								real_order_ring.LessEqLessThanTrans.At(
									c.TermAs[Real]("|max(a, min(b, x)) - max(a, min(b, y))|"),
									c.TermAs[Real]("|x - y|"),
									r)),
						)
						c.Show(
							"so f at them is within ε",
							By(radius, xIn, yIn, clampsNear),
						)
					}),
				),
			))
		}),
})}
