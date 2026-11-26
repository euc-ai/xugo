// metric.go — the line as a metric space: its open sets are the open sets
// of the distance |x − y|, and it is complete, a Cauchy sequence of the
// distance being a Cauchy sequence of reals.

package real_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/registry"
)

// RealMetric — the reals with their distance form a metric space, on
// the whole line. Each axiom, the distance unfolded to the magnitude of
// the difference, is a fact of the order and |·| the arithmetic closer
// decides, splitting the absolute values itself: a difference vanishes
// only between equal reals, x − y and y − x are negatives of each
// other, and x − z is the sum of x − y and y − z. The carrier is every
// real, so each case's membership assumption says nothing.
var RealMetric = realMetricThm{family.Add(registry.ProofEntry{
	Name: "RealMetric",
	Key:  "prop_33d53e0b4df2b7c3",
	Build: family.Instance(metric_space.MetricSpace, "metric_space(𝕌, real_dist)",
		Case(
			"reals at distance zero are equal",
			Derive(func(a *Argument) {
				a.FixAs[Real]("x")
				a.FixAs[Real]("y")
				a.Assume()
				a.Show(
					"|x − y| vanishes exactly when x − y does",
					Simp(Fwd(real_sgn_abs.RealDistDef)),
					ByArith())
			})),
		Case(
			"the distance reads the same both ways",
			Derive(func(a *Argument) {
				a.FixAs[Real]("x")
				a.FixAs[Real]("y")
				a.Assume()
				a.Show(
					"x − y and y − x are negatives of each other",
					Simp(Fwd(real_sgn_abs.RealDistDef)),
					ByArith())
			})),
		Case(
			"the triangle inequality",
			Derive(func(a *Argument) {
				a.FixAs[Real]("x")
				a.FixAs[Real]("y")
				a.FixAs[Real]("z")
				a.Assume()
				a.Show(
					"x − z is the sum of x − y and y − z",
					Simp(Fwd(real_sgn_abs.RealDistDef)),
					ByArith())
			})),
	),
})}

// RealBall — a ball of the distance is the set of reals within its
// radius of its centre: the distance is |c − y|, and |c − y| = |y − c|.
// Every later reading of the line as a metric space goes through it.
var RealBall = realBallThm{family.Add(registry.ProofEntry{
	Name: "RealBall",
	Key:  "prop_b511a5510ed8556",
	Build: family.Theorem("∀c r y:real. y ∈ ball(𝕌, real_dist, c, r) ⇔ |y - c| < r",
		func(a *Argument, c, r, y *Expr[Real]) {
			symmetric := a.Have(
				"the distance is symmetric: c − y is the negative of y − c, and |·| forgets the sign",
				"|c - y| = |y - c|",
				By(Normalized, real_sgn_abs.AbsEven.At(a.TermAs[Real]("c - y")), real_ring.NegSub.At(c, y)))
			a.Show(
				"the ball holds the reals y with |c − y| < r, that is |y − c| < r",
				Simp(Fwd(metric_space.BallDef.Inst[Real]()), Fwd(real_sgn_abs.RealDistDef)),
				symmetric.RwRev(),
				BySets())
		}),
})}

// RealTopologyMetric — the line's open sets are the open sets of the
// distance: two families of sets are equal when they have the same
// members, every set of reals lies in the carrier 𝕌, and a ball of the
// distance about c is the set of reals within its radius of c, so the
// two tests of openness are one test.
var RealTopologyMetric = realTopologyMetricThm{family.Add(registry.ProofEntry{
	Name: "RealTopologyMetric",
	Key:  "prop_7a30accbb1d94f49",
	Build: family.Theorem("real_topology = metric_topology(𝕌, real_dist)",
		func(a *Argument) {
			a.Show(
				"a set of reals is open on the line exactly when it is open for the distance",
				// Same members; membership in each family is its openness
				// test, and every set of reals lies in the carrier 𝕌.
				Simp(
					Fwd(set_basic.Extension.Inst[Set[Real]]()),
					Fwd(OpenIff),
					Fwd(metric_space.OpenIff.Inst[Real]()),
					Fwd(set_order.SubsetUniv.Inst[Real]())),
				// A ball lies in u when each of its points does, and its
				// points are the reals within its radius of its centre: the
				// tests now agree.
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(RealBall)),
				TrivialNormalized())
		}),
})}

// RealComplete — the line with its distance is complete. Read with the
// distance |x(m) − x(n)|, a Cauchy sequence of the metric space is a
// Cauchy sequence of reals, which converges by Cauchy's criterion; its
// limit is a real, and the terms come within ε of it in the distance as
// they do in |·|.
var RealComplete = realCompleteThm{family.Add(registry.ProofEntry{
	Name: "RealComplete",
	Key:  "prop_d25b9d38cd8edafa",
	Build: family.Theorem("metric_complete(𝕌, real_dist)",
		func(a *Argument) {
			a.Do(Unfold(complete_metric.MetricCompleteDef))
			x := a.FixAs[Fun[Nat, Real]]("x")
			cauchy := a.Assume() // x is Cauchy in the metric space
			parts := a.Conjuncts(
				a.Unfolded(cauchy, complete_metric.MetricCauchyDef),
				"every term is a point of the line",
				"the terms draw together in the distance")
			terms, together := parts[0], parts[1]
			realCauchy := a.Have(
				"x is a Cauchy sequence of reals, the distance of two terms being |x(m) − x(n)|",
				"real_cauchy(x)",
				Unfold(real_sequences.RealCauchyDef),
				Simp(Rev(real_sgn_abs.RealDistDef)),
				By(together))
			l, limit := a.ObtainAs[Real](
				"so it converges, by Cauchy's criterion",
				"∃l:real. x ⟶ l",
				By(realCauchy, real_sequences.CauchyIffConvergent.At(x)))
			near := a.Unfolded(limit, real_sequences.RealConvergesToDef)
			a.Take(l)
			a.Show(
				"l is a real, and the terms come within ε of it in the distance as they do in |·|",
				Unfold(complete_metric.MetricConvergesToDef),
				Simp(Fwd(real_sgn_abs.RealDistDef)),
				By(terms, near, set_basic.InUniv.At(l)))
		}),
})}
