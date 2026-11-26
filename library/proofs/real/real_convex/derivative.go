// derivative.go — the derivative tests for convexity: on an interval, a
// function whose derivative increases is convex, and so is one whose
// second derivative is nonnegative; and the two convex functions the
// classical inequalities are read from, the exponential and the negative
// of the logarithm, convex by those tests.

package real_convex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// DerivativeIncreasingConvex — on an interval where f has a derivative
// at every point and the derivative increases, f is convex. For x < y < z
// in the interval the mean value theorem writes the slope of the chord
// from x to y as f'(u) with x < u < y, and that from y to z as f'(v) with
// y < v < z; u and v lie in the interval and u < v, so f'(u) ≤ f'(v) —
// the slopes of chords increase, which is convexity.
var DerivativeIncreasingConvex = derivativeIncreasingConvexThm{family.Add(registry.ProofEntry{
	Name: "DerivativeIncreasingConvex",
	Key:  "prop_670192caf775f259",
	Build: family.Theorem(Statement{
		Binders: "∀f f':real → real. ∀s:set(real).",
		Hypotheses: []string{
			"real_interval(s)",
			"∀x:real. x ∈ s ⇒ real_derivative_at(f, x, f'(x))",
			"real_increasing_on(s, f')",
		},
		Conclusion: "real_convex_on(s, f)",
	}, func(
		a *Argument,
		f, fPrime *Arrow[Real, Real],
		s *Expr[Set[Real]],
		interval, derivative, increasingOn Fact,
	) {
		between := a.Unfolded(interval, real_topology.RealIntervalDef)
		increasing := a.Unfolded(increasingOn, real_continuous.RealIncreasingOnDef)
		slopes := a.Have(
			"the slopes of chords increase",
			"∀x y z:real. x ∈ s ∧ z ∈ s ∧ x < y ∧ y < z ⇒ (f(y) - f(x)) / (y - x) ≤ (f(z) - f(y)) / (z - y)",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]()
				y := b.FixAs[Real]()
				z := b.FixAs[Real]()
				given := b.Conjuncts(
					b.Assume(),
					"x lies in s",
					"z lies in s",
					"x < y",
					"y < z")
				yIn := b.Have(
					"y lies in s, between x and z",
					"y ∈ s",
					By(between.At(x, y, z), given[0], given[1], given[2], given[3], real_order_ring.LessEqOfLessThan),
				)
				u, left := b.UnpackAs[Real](
					GroupPremises(
						interval,
						derivative,
						given[0],
						yIn,
						given[2],
						real_derivative.MeanValueOnInterval.At(f, fPrime, s, x, y)),
					"u")
				v, right := b.UnpackAs[Real](
					GroupPremises(
						interval,
						derivative,
						yIn,
						given[1],
						given[3],
						real_derivative.MeanValueOnInterval.At(f, fPrime, s, y, z)),
					"v")
				onLeft := b.Conjuncts(
					left,
					"x < u",
					"u < y",
					"the chord from x to y has slope f'(u)")
				onRight := b.Conjuncts(
					right,
					"y < v",
					"v < z",
					"the chord from y to z has slope f'(v)")
				inS := b.Have(
					"u and v lie in s, between points of s",
					"u ∈ s ∧ v ∈ s",
					By(
						between.At(x, u, y),
						between.At(y, v, z),
						given[0],
						yIn,
						given[1],
						onLeft[0],
						onLeft[1],
						onRight[0],
						onRight[1],
						real_order_ring.LessEqOfLessThan),
				)
				b.Show(
					"each slope is f' at its mean value point, and f' increases from u to v",
					onLeft[2].Rw(),
					onRight[2].Rw(),
					ByArith(increasing.At(u, v), inS, onLeft[1], onRight[0], given[2], given[3]),
				)
			}),
		)
		a.Show(
			"so f is convex on s",
			By(ConvexIffChordSlopes.At(f, s), slopes))
	}),
})}

// SecondDerivativeNonnegConvex — on an interval where f has a derivative
// f' and f' a derivative f″ at every point, f″ ≥ 0 makes f convex. The
// mean value theorem for f' writes f'(y) − f'(x) as f″(z)·(y − x) for
// some z between x < y, a product of two nonnegative numbers; so f'
// increases, and the first-derivative test applies.
var SecondDerivativeNonnegConvex = secondDerivativeNonnegConvexThm{family.Add(registry.ProofEntry{
	Name: "SecondDerivativeNonnegConvex",
	Key:  "prop_413ae0af2f4448d1",
	Build: family.Theorem(Statement{
		Binders: "∀f f' f'':real → real. ∀s:set(real).",
		Hypotheses: []string{
			"real_interval(s)",
			"∀x:real. " +
				"    x ∈ s ⇒ real_derivative_at(f, x, f'(x)) ∧ real_derivative_at(f', x, f''(x)) ∧ &0 ≤ f''(x)",
		},
		Conclusion: "real_convex_on(s, f)",
	}, func(
		a *Argument,
		f, fPrime, fSecond *Arrow[Real, Real],
		s *Expr[Set[Real]],
		interval, derivatives Fact,
	) {
		between := a.Unfolded(interval, real_topology.RealIntervalDef)
		second := a.Have(
			"f' has derivative f''(x) at every point x of s",
			"∀x:real. x ∈ s ⇒ real_derivative_at(f', x, f''(x))",
			By(derivatives),
		)
		increasing := a.Have(
			"f' increases on s",
			"real_increasing_on(s, f')",
			Unfold(real_continuous.RealIncreasingOnDef),
			Derive(func(b *Argument) {
				x := b.FixAs[Real]()
				y := b.FixAs[Real]()
				given := b.Conjuncts(
					b.Assume(),
					"x lies in s",
					"y lies in s",
					"x ≤ y")
				xy := b.Assuming(
					b.Term("x < y"),
					"at y = x there is nothing to compare",
					Given(func(c *Argument, notLess Fact) {
						same := c.Have(
							"y is x",
							"x = y",
							ByArith(notLess, given[2]))
						c.Show(
							"f'(y) ≤ f'(y)",
							same.Rw(),
							ByArith())
					}))
				z, mvt := b.UnpackAs[Real](
					GroupPremises(
						interval,
						second,
						given[0],
						given[1],
						xy,
						real_derivative.MeanValueOnInterval.At(fPrime, fSecond, s, x, y)),
					"z")
				parts := b.Conjuncts(
					mvt,
					"x < z",
					"z < y",
					"f'(y) − f'(x) is f''(z)·(y − x)")
				zIn := b.Have(
					"z lies in s, between x and y",
					"z ∈ s",
					By(between.At(x, z, y), given[0], given[1], parts[0], parts[1], real_order_ring.LessEqOfLessThan),
				)
				b.Show(
					"f'(y) − f'(x) is f''(z)·(y − x), a product of two nonnegative numbers",
					ByArith(parts[2], derivatives.At(z), zIn, given[2]),
				)
			}),
		)
		a.Show(
			"f' increases on s, so f is convex there",
			By(DerivativeIncreasingConvex.At(f, fPrime, s), interval, derivatives, increasing),
		)
	}),
})}

// ExpConvex — the exponential is convex on the whole line: it is its own
// first and second derivative, and it is positive.
var ExpConvex = expConvexThm{family.Add(registry.ProofEntry{
	Name: "ExpConvex",
	Key:  "prop_4d4bea7cd5ecd5c1",
	Build: family.Theorem("real_convex_on(𝕌, real_exp)", func(a *Argument) {
		line := a.Have(
			"the real line is an interval",
			"real_interval(𝕌)",
			Unfold(real_topology.RealIntervalDef),
			By(set_basic.InUniv),
		)
		exp := a.TermAs[Fun[Real, Real]]("real_exp")
		a.Show(
			"exp has derivative exp, whose derivative exp is positive",
			By(
				SecondDerivativeNonnegConvex.At(exp, exp, exp, a.TermAs[Set[Real]]("𝕌")),
				line,
				real_exp_log.ExpDerivative,
				real_exp_log.ExpPositive,
				real_order_ring.LessEqOfLessThan),
		)
	}),
})}

// NegLogConvex — x ↦ −log(x) is convex on the positive reals: its
// derivative −1/x increases there, the reciprocal decreasing.
var NegLogConvex = negLogConvexThm{family.Add(registry.ProofEntry{
	Name: "NegLogConvex",
	Key:  "prop_9192517563fa3af2",
	Build: family.Theorem("real_convex_on({x:real | &0 < x}, λx:real. -log(x))", func(a *Argument) {
		positive := a.Have(
			"the positive reals form an interval",
			"real_interval({x:real | &0 < x})",
			Unfold(real_topology.RealIntervalDef),
			ByArith(),
		)
		derivative := a.Have(
			"−log has derivative −1/x at every x > 0",
			"∀x:real. &0 < x ⇒ real_derivative_at(λx:real. -log(x), x, -real_inv(x))",
			By(real_derivative.DerivativeNeg, real_exp_log.LogDerivative),
		)
		increasing := a.Have(
			"−1/x increases on the positive reals",
			"real_increasing_on({x:real | &0 < x}, λx:real. -real_inv(x))",
			Unfold(real_continuous.RealIncreasingOnDef),
			ByArith(real_order_field.InvAntitoneWeak),
		)
		a.Show(
			"−log has an increasing derivative on the positive reals",
			By(
				DerivativeIncreasingConvex.At(
					a.TermAs[Fun[Real, Real]]("λx:real. -log(x)"),
					a.TermAs[Fun[Real, Real]]("λx:real. -real_inv(x)"),
					a.TermAs[Set[Real]]("{x:real | &0 < x}")),
				positive,
				derivative,
				increasing),
		)
	}),
})}
