// sequences.go — convergence in ℝⁿ is convergence of each coordinate, so
// ℝⁿ is complete, each coordinate of a Cauchy sequence being a Cauchy
// sequence of reals; and so is a closed ball of ℝⁿ, a closed subset of it.

package euclidean_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ConvergesIffCoordinates — a sequence of n-vectors converges to an
// n-vector exactly when each of its first n coordinates does. Forward, a
// coordinate of x(k) - l is at most its norm (euclidean.ComponentLeNorm), the
// distance from x(k) to l, so the index past which x is within ε of l serves
// every coordinate. Backward, each coordinate below n lies within ε/(n + 1)
// of its limit from some index N(i) on; past the sum of the n indices every
// coordinate of x(k) - l is at most ε/(n + 1) in size, so its norm is at most
// n·ε/(n + 1) < ε (euclidean.CoordinateNormBound).
var ConvergesIffCoordinates = convergesIffCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "ConvergesIffCoordinates",
	Key:  "prop_493ba5d00f56f1b3",
	Reading: "Both vec hypotheses are load-bearing for the backward direction: " +
		"metric convergence asks every term and the limit to be n-vectors, which the " +
		"coordinates below n do not see. At n = 0 every distance is 0 and both sides hold.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x:(num → num → real). ∀l:(num → real).",
		Hypotheses: []string{
			"∀k:num. vec⟨n⟩(x(k))",
			"vec⟨n⟩(l)",
		},
		Conclusion: "metric_converges_to({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, x, l) ⇔ " +
			"∀i:num. i < n ⇒ (λk:num. x(k)(i)) ⟶ l(i)",
	}, func(
		a *Argument,
		n *Expr[Nat],
		x *Arrow2[Nat, Nat, Real],
		l *Vec[Real, DimN],
		terms, limit Fact,
	) {
		// The arithmetic closes read only ground facts, so VecSubDef is cited at
		// its points and its implicit subtraction is spelled.
		sub := a.TermAs[Op[Real]]("real_sub")
		a.Iff()
		a.Forward(
			"a coordinate of x(k) - l is at most the distance from x(k) to l, so each coordinate converges",
			func(b *Argument, converges Fact) {
				near := b.Conjuncts(
					b.Unfolded(converges, complete_metric.MetricConvergesToDef),
					"l is an n-vector",
					"so is every term of x",
					"every positive ε has a tail of x within ε of l")
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				b.Do(Unfold(real_sequences.RealConvergesToDef))
				eps := b.FixAs[Real]("ε")
				pos := b.Assume()
				N, tail := b.ObtainAs[Nat](
					"from some index N on, x is within ε of l",
					"∃N:num. ∀k:num. N ≤ k ⇒ dist⟨n⟩(x(k), l) < ε",
					By(near[2].At(eps), pos))
				b.Take(N)
				k := b.FixAs[Nat]("k")
				past := b.Assume()
				xk := b.VecAs[Real, DimN]("x(k)")
				b.Show(
					"the coordinate i of x(k) - l is at most its norm, the distance, below ε past N",
					ByArith(
						tail.At(k),
						past,
						below,
						euclidean.ComponentLeNorm.At(i, b.VecAs[Real, DimN]("x(k) - l")),
						vec_space.VecSubDef.At(sub, xk, l, i),
						euclidean.VecDistDef.At(xk, l)))
			})
		a.Backward(
			"past a common index for ε/(n + 1) in every coordinate, x(k) - l has norm at most n·ε/(n + 1) < ε",
			func(b *Argument, coordinatewise Fact) {
				tails := b.Have(
					"every positive ε has a tail of x within ε of l",
					"∀ε:real. &0 < ε ⇒ ∃N:num. ∀k:num. N ≤ k ⇒ dist⟨n⟩(x(k), l) < ε",
					Derive(func(c *Argument) {
						c.FixAs[Real]("ε")
						pos := c.Assume()
						radius := c.TermAs[Real]("ε / (&n + &1)")
						small := c.Have(
							"ε/(n + 1) is positive",
							"&0 < ε / (&n + &1)",
							ByArith(pos))
						thresholds := c.Have(
							"each coordinate below n lies within ε/(n + 1) of its limit from some index on",
							"∀i:num. i < n ⇒ ∃N:num. ∀k:num. N ≤ k ⇒ |x(k)(i) - l(i)| < ε / (&n + &1)",
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								below := d.Assume()
								d.Show(
									"the coordinate i converges to l(i)",
									By(coordinatewise.At(i), below, small, real_sequences.RealConvergesToDef))
							}))
						N, chosen := c.ObtainAs[Fun[Nat, Nat]](
							"choose such an index N(i) for each coordinate i below n",
							"∃N:(num → num). ∀i:num. i < n ⇒ ∀k:num. N(i) ≤ k ⇒ |x(k)(i) - l(i)| < ε / (&n + &1)",
							By(thresholds))
						indices := c.TermAs[Set[Nat]]("{j:num | j < n}")
						common := c.Have(
							"past the sum of the n indices every coordinate of x(k) - l is at most ε/(n + 1) in size",
							"∀k:num. nat_sum({j:num | j < n}, N) ≤ k ⇒ ∀i:num. i < n ⇒ |(x(k) - l)(i)| ≤ ε / (&n + &1)",
							Derive(func(d *Argument) {
								k := d.FixAs[Nat]("k")
								past := d.Assume()
								i := d.FixAs[Nat]("i")
								below := d.Assume()
								d.Show(
									"N(i) is a term of the sum, so at most k, and the coordinate i of x(k) - l is x(k)(i) - l(i)",
									ByArith(
										chosen.At(i, k),
										below,
										past,
										nat_sum.TermLeSum.At(N, indices, i),
										num_segment.FiniteBelowStrict.At(n),
										vec_space.VecSubDef.At(sub, d.VecAs[Real, DimN]("x(k)"), l, i)))
							}))
						c.Take(c.TermAs[Nat]("nat_sum({j:num | j < n}, N)"))
						k := c.FixAs[Nat]("k")
						past := c.Assume()
						bound := c.Have(
							"so x(k) - l has norm at most n·ε/(n + 1)",
							"‖x(k) - l‖_n ≤ &n * (ε / (&n + &1))",
							By(common.At(k), past, euclidean.CoordinateNormBound.At(c.VecAs[Real, DimN]("x(k) - l"), radius)))
						c.Show(
							"which is below ε",
							ByArith(
								bound,
								pos,
								real_order_ring.NumNonneg.At(n),
								euclidean.VecDistDef.At(c.VecAs[Real, DimN]("x(k)"), l)))
					}))
				b.Show(
					"the limit and every term are n-vectors, and every positive ε has a tail of x within ε of l",
					Unfold(complete_metric.MetricConvergesToDef),
					By(tails, terms, limit))
			})
	}),
})}

// EuclideanComplete — ℝⁿ is complete: a Cauchy sequence of n-vectors
// converges. A coordinate of a difference is at most its norm, the
// distance, so each coordinate below n of a Cauchy sequence is a Cauchy
// sequence of reals, which converges; the n limits, extended by 0 from n
// on, are an n-vector, and the sequence converges to it because each of
// its coordinates does.
var EuclideanComplete = euclideanCompleteThm{family.Add(registry.ProofEntry{
	Name: "EuclideanComplete",
	Key:  "prop_f629ad9320ad82f0",
	Build: family.Theorem(
		"∀n:num. metric_complete({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩)",
		func(a *Argument, n *Expr[Nat]) {
			// The arithmetic close reads only ground facts, so VecSubDef is cited at
			// its points and its implicit subtraction is spelled.
			sub := a.TermAs[Op[Real]]("real_sub")
			a.Do(Unfold(complete_metric.MetricCompleteDef))
			x := a.FixAs[Fun2[Nat, Nat, Real]]("x")
			cauchy := a.Conjuncts(
				a.Unfolded(a.Assume(), complete_metric.MetricCauchyDef),
				"every term of x is an n-vector",
				"every positive ε has a tail of x whose terms are within ε of each other")
			coordinates := a.Have(
				"each coordinate of x below n is a Cauchy sequence of reals",
				"∀i:num. i < n ⇒ real_cauchy(λk:num. x(k)(i))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					below := b.Assume()
					b.Do(Simp(Fwd(real_sequences.RealCauchyDef)))
					eps := b.FixAs[Real]("ε")
					pos := b.Assume()
					N, tail := b.ObtainAs[Nat](
						"from some index N on, any two terms of x are within ε",
						"∃N:num. ∀m p:num. N ≤ m ∧ N ≤ p ⇒ dist⟨n⟩(x(m), x(p)) < ε",
						By(cauchy[1].At(eps), pos))
					b.Take(N)
					m := b.FixAs[Nat]("m")
					p := b.FixAs[Nat]("p")
					past := b.Assume()
					xm := b.VecAs[Real, DimN]("x(m)")
					xp := b.VecAs[Real, DimN]("x(p)")
					b.Show(
						"the coordinate i of x(m) - x(p) is at most its norm, the distance, below ε past N",
						ByArith(
							tail.At(m, p),
							past,
							below,
							euclidean.ComponentLeNorm.At(i, b.VecAs[Real, DimN]("x(m) - x(p)")),
							vec_space.VecSubDef.At(sub, xm, xp, i),
							euclidean.VecDistDef.At(xm, xp)))
				}))
			l, limitVector := a.ObtainAs[Fun[Nat, Real]](
				"the n limits, extended by 0 from n on, are an n-vector l",
				"∃l:(num → real). vec⟨n⟩(l) ∧ ∀i:num. i < n ⇒ (λk:num. x(k)(i)) ⟶ l(i)",
				Derive(func(b *Argument) {
					_, limits := b.ObtainAs[Fun[Nat, Real]](
						"a Cauchy sequence of reals converges, so choosing "+
							"a limit for each coordinate below n is a function L",
						"∃L:(num → real). ∀i:num. i < n ⇒ (λk:num. x(k)(i)) ⟶ L(i)",
						By(coordinates, real_sequences.CauchyIffConvergent))
					b.Take(b.TermAs[Fun[Nat, Real]]("λi:num. COND(i < n, L(i), &0)"))
					b.Show(
						"it is 0 from n on and L below n",
						ByArith(limits, vec_space.VecDef))
				}))
			ofL := a.Conjuncts(
				limitVector,
				"l is an n-vector",
				"each coordinate of x below n converges to that of l")
			a.Take(l)
			a.Show(
				"x converges to l, each of its n coordinates converging",
				By(
					cauchy[0],
					ofL[0],
					ofL[1],
					ConvergesIffCoordinates.At(x, proof.Inhabit(a.VecAs[Real, DimN]("l"), ofL[0]))))
		}),
})}

// ClosedBallComplete — a closed ball of ℝⁿ is complete. The n-vectors
// within r of c are the closed ball of ℝⁿ about c, the distance being
// symmetric; a closed ball of a metric space is closed
// (metric_space.ClosedBallClosed), and a closed subset of the complete
// space ℝⁿ (EuclideanComplete) is complete
// (complete_metric.ClosedComplete).
var ClosedBallComplete = closedBallCompleteThm{family.Add(registry.ProofEntry{
	Name: "ClosedBallComplete",
	Key:  "prop_edbcfe8176733e7c",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀c:(num → real). ∀r:real.",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
		},
		Conclusion: "metric_complete({u:(num → real) | vec⟨n⟩(u) ∧ ‖u - c‖_n ≤ r}, vec_dist⟨n⟩)",
	},
		func(a *Argument, n *Expr[Nat], c *Vec[Real, DimN], r *Expr[Real], centre Fact) {
			space := a.TermAs[Set[Fun[Nat, Real]]]("{u:(num → real) | vec⟨n⟩(u)}")
			distance := a.TermAs[Fun2[Fun[Nat, Real], Fun[Nat, Real], Real]]("vec_dist⟨n⟩")
			ball := a.TermAs[Set[Fun[Nat, Real]]](
				"closed_ball({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, c, r)")
			symmetric := a.Have(
				"the distance from c to u is the norm of u − c",
				"∀u:(num → real). dist⟨n⟩(c, u) = ‖u - c‖_n",
				By(Normalized, euclidean.DistSym, euclidean.VecDistDef))
			isBall := a.Have(
				"so the set is the closed ball of ℝⁿ about c",
				"{u:(num → real) | vec⟨n⟩(u) ∧ ‖u - c‖_n ≤ r} = "+
					"closed_ball({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, c, r)",
				Unfold(metric_space.ClosedBallDef),
				BySets(symmetric))
			a.Show(
				"a closed ball is closed, and a closed subset of the complete ℝⁿ is complete",
				isBall.Rw(),
				By(
					centre,
					euclidean.EuclideanMetric.At(n),
					EuclideanComplete.At(n),
					metric_space.ClosedBallClosed.At(space, distance, c, r),
					complete_metric.ClosedComplete.At(space, distance, ball)))
		}),
})}
