// complete.go — what completeness gives: nested closed sets shrinking to
// nothing have a common point (Cantor), countably many dense open sets
// meet in a dense set (Baire), and a contraction has exactly one fixed
// point (Banach); and the product of two complete spaces, and a countable
// product of complete spaces, are complete.

package complete_metric

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Nested closed sets
// ---------------------------------------------------------------------------

// CantorIntersection — in a complete space, a decreasing sequence of
// non-empty closed sets whose diameters shrink to nothing has a common
// point.
//
// The sequence decreases all the way, c(n) lying in c(m) whenever m ≤ n
// (order.DecreasingFromSteps). A point x(n) chosen in each c(n) is then a
// sequence whose terms from n on lie in c(n). Past an index K at which
// any two points of c(K) are within ε of each other, any two terms are,
// so x is Cauchy and converges to some l. For each n the tail j ↦ x(j + n) is a
// subsequence converging to l (LimitSubsequence) whose terms lie in the
// closed c(n), which therefore holds l (ClosedIffSequential).
var CantorIntersection = cantorIntersectionThm{family.Add(registry.ProofEntry{
	Name: "CantorIntersection",
	Key:  "prop_852268809a0b1ed4",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀c:(num → set(A)).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_complete(M, d)",
			"∀n:num. closed_in(metric_topology(M, d), c(n)) ∧ ¬(c(n) = ∅) ∧ c(n + 1) ⊆ c(n)",
			"∀ε:real. &0 < ε ⇒ ∃n:num. ∀x y:A. x ∈ c(n) ∧ y ∈ c(n) ⇒ d(x, y) < ε",
		},
		Conclusion: "∃l:A. ∀n:num. l ∈ c(n)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			complete Fact,
			c *Arrow[Nat, Set[A]],
			nested, shrinking Fact,
		) {
			inM := a.Have(
				"each c(n) lies in M, being closed",
				"∀n:num. c(n) ⊆ M",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(nested.At(n), metric, ClosedIffSequential.At(M, d, c.Apply(n)))
				}))
			somePoint := a.Have(
				"each c(n) has a point, being non-empty",
				"∀n:num. ∃y:A. y ∈ c(n)",
				By(nested, set_basic.MemberNotEmpty))
			x, chosen := a.ObtainAs[Fun[Nat, A]](
				"choosing one for each n is a sequence x with x(n) in c(n)",
				"∃x:(num → A). ∀n:num. x(n) ∈ c(n)",
				By(somePoint))
			tail := a.Have(
				"so the terms of x from n on lie in c(n), the sequence decreasing all the way",
				"∀n m:num. n ≤ m ⇒ x(m) ∈ c(n)",
				BySets(nested, chosen, At(order.DecreasingFromSteps, c)))
			cauchy := a.Have(
				"x is Cauchy: past an index K at which c(K) holds no two points ε apart, any two terms lie in c(K)",
				"metric_cauchy(M, d, x)",
				Unfold(MetricCauchyDef),
				SplitConj(
					Case(
						"every term is a point of M",
						a.ForEach(func(n *Expr[Nat]) Action {
							return BySets(chosen.At(n), inM.At(n))
						})),
					Case(
						"past some index any two terms are within ε of each other",
						Derive(func(b *Argument) {
							eps := b.FixAs[Real]()
							pos := b.Assume()
							K, narrow := b.ObtainAs[Nat](
								"the diameters shrinking to nothing, some c(K) holds no two points ε apart",
								"∃K:num. ∀u v:A. u ∈ c(K) ∧ v ∈ c(K) ⇒ d(u, v) < ε",
								By(shrinking.At(eps), pos))
							b.Take(K)
							m := b.FixAs[Nat]()
							n := b.FixAs[Nat]()
							past := b.Assume()
							b.Show(
								"x(m) and x(n), terms past K, lie in c(K)",
								By(narrow.At(b.TermAs[A]("x(m)"), b.TermAs[A]("x(n)")), tail.At(K, m), tail.At(K, n), past))
						})),
				))
			l, limit := a.ObtainAs[A](
				"M being complete, x converges to some l",
				"∃l:A. metric_converges_to(M, d, x, l)",
				By(complete, cauchy, MetricCompleteDef))
			a.Take(l)
			n := a.FixAs[Nat]()
			// `o` is the constant behind `∘`: unfolded, the j-th term of the
			// tail x ∘ (λj. j + n) is x(j + n).
			tailInC := a.Have(
				"the terms of the tail from n lie in c(n)",
				"∀j:num. (x ∘ (λj:num. j + n))(j) ∈ c(n)",
				Unfold(functions.ComposeApply),
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]()
					b.Show(
						"x(j + n) is a term of x from n on",
						By(tail.At(n, b.TermAs[Nat]("j + n")), nat_order.LessEqAddLeft.At(j, n)))
				}))
			tailToL := a.Have(
				"the tail is a subsequence of x, the shift by n rising, so it converges to l as well",
				"metric_converges_to(M, d, x ∘ (λj:num. j + n), l)",
				ByArith(limit, LimitSubsequence.At(M, d, x, a.TermAs[Fun[Nat, Nat]]("λj:num. j + n"), l)))
			a.Show(
				"c(n) is closed and holds the terms of the tail, so it holds their limit l",
				By(tailInC, tailToL, nested.At(n), metric, ClosedIffSequential.At(M, d, c.Apply(n))))
		}),
})}

// NestedClosedBallsMeet — in a complete space, closed balls about points
// of M, each inside the one before and with radii tending to zero, have
// a common point.
//
// Each closed ball is closed and holds its centre, its radius being at
// least zero. Two points of the n-th lie within twice its radius of each
// other, so within ε once that radius is below ε/2: the closed balls
// shrink to nothing, and CantorIntersection gives the common point.
var NestedClosedBallsMeet = nestedClosedBallsMeetThm{family.Add(registry.ProofEntry{
	Name: "NestedClosedBallsMeet",
	Key:  "prop_3af442d2b05d2607",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:(num → A). ∀r:(num → real).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_complete(M, d)",
			"∀n:num. x(n) ∈ M ∧ &0 ≤ r(n)",
			"∀n:num. «closedBall»(n + 1) ⊆ «closedBall»(n)",
			"∀ε:real. &0 < ε ⇒ ∃n:num. r(n) < ε",
		},
		Conclusion: "∃l:A. ∀n:num. l ∈ «closedBall»(n)",
		Abbrev: Abbrev{
			{Name: "closedBall", Text: "λn:num. closed_ball(M, d, x(n), r(n))"},
		},
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			complete Fact,
			x *Arrow[Nat, A],
			r *Arrow[Nat, Real],
			balls, nested, vanishing Fact,
		) {
			chain := a.Have(
				"the closed balls are closed, non-empty and nested",
				"∀n:num. "+
					"    closed_in(metric_topology(M, d), «closedBall»(n)) ∧ "+
					"    «closedBall»(n) ≠ ∅ ∧ "+
					"    «closedBall»(n + 1) ⊆ «closedBall»(n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					here := b.Conjuncts(
						balls.At(n),
						"the centre is a point of M",
						"the radius is at least zero")
					centre := b.MemberOf[on.M](x.Apply(n), here[0])
					b.Do(SplitConjAll(
						Case(
							"a closed ball about a point of M is closed",
							By(metric_space.ClosedBallClosed.Read(metric).At(centre, r.Apply(n)))),
						Case(
							"it holds its centre, its radius being at least zero",
							BySets(here[1], metric_space.CentreInClosedBall.Read(metric).At(centre, r.Apply(n)))),
						Case(
							"and it holds the next closed ball",
							By(nested.At(n))),
					))
				}))
			shrinking := a.Have(
				"their diameters shrink to nothing: two points of "+
					"the N-th closed ball lie within 2·r(N) of each other",
				"∀ε:real. &0 < ε ⇒ ∃n:num. ∀y z:A. y ∈ «closedBall»(n) ∧ z ∈ «closedBall»(n) ⇒ d(y, z) < ε",
				Derive(func(b *Argument) {
					b.FixAs[Real]()
					positive := b.Assume()
					N, small := b.ObtainAs[Nat](
						"the radii tending to zero, some r(N) is below ε/2",
						"∃N:num. r(N) < ε / &2",
						ByArith(positive, vanishing.At(b.TermAs[Real]("ε / &2"))))
					b.Take(N)
					y := b.FixAs[A]()
					z := b.FixAs[A]()
					both := b.Conjuncts(
						b.Assume(),
						"y lies in the N-th closed ball",
						"z lies in the N-th closed ball")
					nearY := b.Conjuncts(
						b.Unfolded(both[0], metric_space.ClosedBallDef),
						"y is a point of M",
						"y lies within r(N) of the centre")
					nearZ := b.Conjuncts(
						b.Unfolded(both[1], metric_space.ClosedBallDef),
						"z is a point of M",
						"z lies within r(N) of the centre")
					here := b.Conjuncts(
						balls.At(N),
						"the centre is a point of M",
						"the radius is at least zero")
					centre := b.MemberOf[on.M](x.Apply(N), here[0])
					ym := b.MemberOf[on.M](y, nearY[0])
					zm := b.MemberOf[on.M](z, nearZ[0])
					b.Show(
						"y and z lie within r(N) < ε/2 of the centre, so within ε of each other",
						ByArith(
							nearY[1],
							nearZ[1],
							small,
							metric_space.DistTriangle.Read(metric).At(ym, centre, zm),
							metric_space.DistSym.Read(metric).At(centre, ym)))
				}))
			a.Show(
				"the space being complete, the nested closed balls have a common point",
				By(
					metric,
					complete,
					chain,
					shrinking,
					CantorIntersection.At(M, d, a.TermAs[Fun[Nat, Set[A]]]("«closedBall»"))))
		}),
})}

// ClosedBallInDenseMeet — a non-empty open set and a dense open set meet in
// a set holding a closed ball of every small radius.
//
// The dense v meets the non-empty open u (topological_space.DenseMeetsOpen),
// at a point x. The two meet in an open set, so a ball about x of some
// radius r₀ lies in it; the closed ball about x of radius min(r₀, ε)/2,
// below both r₀ and ε, lies in that ball.
var ClosedBallInDenseMeet = closedBallInDenseMeetThm{family.Add(registry.ProofEntry{
	Name: "ClosedBallInDenseMeet",
	Key:  "prop_cbdb989dd659d3b3",
	Build: metric_space.MetricSpace.Law(Statement{
		Binders: "∀u v:set(A). ∀ε:real.",
		Hypotheses: []string{
			"u ∈ metric_topology",
			"u ≠ ∅",
			"v ∈ metric_topology",
			"closure(metric_topology, v) = M",
			"&0 < ε",
		},
		Conclusion: "∃c:A. ∃r:real. c ∈ M ∧ &0 < r ∧ r < ε ∧ closed_ball(c, r) ⊆ u ∩ v",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			u, v *Expr[Set[A]],
			ε *Expr[Real],
			uOpen, nonempty, vOpen, dense, positive Fact,
		) {
			topology := a.Have(
				"the open sets of the distance form a topology",
				"is_topology(metric_topology(M, d))",
				By(metric_space.MetricTopology.At(M, d)))
			meets := a.Have(
				"v being dense, it meets the non-empty open set u",
				"u ∩ v ≠ ∅",
				By(
					uOpen,
					nonempty,
					vOpen,
					dense,
					topological_space.DenseMeetsOpen.Read(topology).At(v),
					metric_space.MetricTopologySpace.At(M, d),
					metric_space.OpenIff.At(M, d, v)))
			x, both := a.ObtainAs[A](
				"so some point x lies in both",
				"∃x:A. x ∈ u ∩ v",
				By(meets, set_basic.MemberNotEmpty))
			r0, around := a.ObtainAs[Real](
				"u ∩ v is open, so a ball about x of some radius r₀ lies in it",
				"∃r:real. &0 < r ∧ ball(x, r) ⊆ u ∩ v",
				By(
					both,
					uOpen,
					vOpen,
					topological_space.InterOpen.Read(topology).AsFact().At(u, v),
					metric_space.OpenIff.At(M, d, a.TermAs[Set[A]]("u ∩ v"))),
				Named("r₀"))
			ball := a.Conjuncts(
				around,
				"r₀ is positive",
				"the ball of radius r₀ about x lies in u ∩ v")
			zero := a.TermAs[Real]("&0")
			half := a.TermAs[Real]("min(r₀, ε) / &2")
			radius := a.Have(
				"half of min(r₀, ε) is positive and below both r₀ and ε, which are positive",
				"&0 < min(r₀, ε) / &2 ∧ min(r₀, ε) / &2 < r₀ ∧ min(r₀, ε) / &2 < ε",
				ByArith(
					ball[0],
					positive,
					real_sup_inf.LessThanMin.At(r0, ε, zero),
					real_sup_inf.MinLowerBound.At(r0, ε)))
			a.Take(x)
			a.Take(half)
			a.Do(SplitConjAll(
				Case(
					"x is a point of M, u lying in M",
					BySets(both, uOpen, metric_space.OpenIff.At(M, d, u))),
				Case(
					"half of min(r₀, ε) is positive",
					By(radius)),
				Case(
					"and below ε",
					By(radius)),
				Case(
					"its closed ball about x lies in the ball of radius r₀, which lies in u ∩ v",
					BySets(radius, metric_space.ClosedBallSubsetBall.At(M, d, x, half, r0), ball[1])),
			))
		}),
})}

// BaireCategory — in a complete space, countably many dense open sets
// meet in a dense set.
//
// Read pointwise (topological_space.DenseMeetsOpen), the intersection is
// dense when it meets every non-empty open set u. Inside u and the dense
// open g(0) lies a closed ball of radius below 1 (ClosedBallInDenseMeet).
// Inside the open ball of a (centre, radius) pair p and the dense open
// g(n + 1) lies again a closed ball, of radius below 1/(n + 2); next(p, n)
// chooses one, and recursion threads the choices into a sequence B of
// pairs whose n-th closed ball lies in g(n) and has radius below
// 1/(n + 1). Each closed ball lies in the open ball before it, so in the
// closed ball before it, and in the complete space the nested closed balls
// have a common point (NestedClosedBallsMeet), which lies in the first,
// inside u, and in every g(n).
var BaireCategory = baireCategoryThm{family.Add(registry.ProofEntry{
	Name: "BaireCategory",
	Key:  "prop_d8a7eb2248f3dad",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀g:(num → set(A)).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_complete(M, d)",
			"∀n:num. g(n) ∈ metric_topology(M, d) ∧ closure(metric_topology(M, d), g(n)) = M",
		},
		Conclusion: "closure(metric_topology(M, d), ⋂image(g, 𝕌)) = M",
		Abbrev: Abbrev{
			{Name: "closedBall", Text: "λn:num. closed_ball(M, d, fst(B(n)), snd(B(n)))"},
		},
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			complete Fact,
			g *Arrow[Nat, Set[A]],
			dense Fact,
		) {
			topology := a.Have(
				"the open sets of the distance form a topology",
				"is_topology(metric_topology(M, d))",
				By(metric_space.MetricTopology.At(M, d)))
			zero := a.TermAs[Nat]("0")
			within := a.Have(
				"the intersection lies in g(0), which lies in its closure M",
				"⋂image(g, 𝕌) ⊆ M",
				BySets(
					dense.At(zero),
					topological_space.SubsetClosure.At(a.TermAs[Set[Set[A]]]("metric_topology(M, d)"), g.Apply(zero))))
			pointwise := a.Have(
				"read pointwise, the intersection is dense when it meets every non-empty open set",
				"closure(metric_topology(M, d), ⋂image(g, 𝕌)) = M ⇔ "+
					"∀u:set(A). u ∈ metric_topology(M, d) ∧ u ≠ ∅ ⇒ u ∩ ⋂image(g, 𝕌) ≠ ∅",
				By(
					within,
					topological_space.DenseMeetsOpen.Read(topology).At(a.TermAs[Set[A]]("⋂image(g, 𝕌)")),
					metric_space.MetricTopologySpace.At(M, d)))
			a.Do(pointwise.Rw())
			u := a.FixAs[Set[A]]("u")
			open := a.Conjuncts(
				a.Assume(),
				"u is open",
				"u is non-empty")

			_, _, first := a.Obtain2As[A, Real](
				"inside u and the dense open g(0) lies a closed ball of radius below 1",
				"∃c:A. ∃r:real. c ∈ M ∧ &0 < r ∧ r < real_inv(&0 + &1) ∧ closed_ball(M, d, c, r) ⊆ u ∩ g(0)",
				By(
					open[0],
					open[1],
					dense.At(zero),
					real_order_field.InvPos.At(a.TermAs[Real]("&0 + &1")),
					ClosedBallInDenseMeet.Read(metric).At(u, g.Apply(zero), a.TermAs[Real]("real_inv(&0 + &1)"))),
				Named("c₀", "r₀"))

			// A (centre, radius) pair p names the ball of that centre and radius;
			// next(p, n) chooses a centre in M and a radius below 1/(n + 2) whose
			// closed ball lies inside the ball p and inside g(n + 1).
			ballInside := a.Have(
				"inside a ball p of M and the dense open g(n + 1) lies a closed ball of radius below 1/(n + 2)",
				Statement{
					Binders: "∀p:prod(A, real). ∀n:num.",
					Hypotheses: []string{
						"fst(p) ∈ M",
						"&0 < snd(p)",
					},
					Conclusion: "∃q:prod(A, real). " +
						"    fst(q) ∈ M ∧ " +
						"    &0 < snd(q) ∧ " +
						"    snd(q) < real_inv(&(n + 1) + &1) ∧ " +
						"    closed_ball(M, d, fst(q), snd(q)) ⊆ ball(M, d, fst(p), snd(p)) ∩ g(n + 1)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Prod[A, Real]]()
					b.FixAs[Nat]()
					pair := b.Conjuncts(
						b.Assume(),
						"the centre is a point of M",
						"the radius is positive")
					centre := b.MemberOf[on.M](b.TermAs[A]("fst(p)"), pair[0])
					radius := b.TermAs[Real]("snd(p)")
					later := b.TermAs[Nat]("n + 1")
					nonempty := b.Have(
						"the ball p holds its centre, so it is non-empty",
						"ball(M, d, fst(p), snd(p)) ≠ ∅",
						By(
							Normalized,
							pair[1],
							metric_space.CentreInBall.Read(metric).At(centre, radius),
							set_basic.MemberNotEmpty))
					c, r, inside := b.Obtain2As[A, Real](
						"inside the open ball p and the dense open g(n + 1) lies a closed ball of radius below 1/(n + 2)",
						"∃c:A. ∃r:real. "+
							"    c ∈ M ∧ "+
							"    &0 < r ∧ "+
							"    r < real_inv(&(n + 1) + &1) ∧ "+
							"    closed_ball(M, d, c, r) ⊆ ball(M, d, fst(p), snd(p)) ∩ g(n + 1)",
						ByArith(
							nonempty,
							dense.At(later),
							metric_space.BallOpen.Read(metric).At(centre, radius),
							real_order_field.InvPos.At(b.TermAs[Real]("&(n + 1) + &1")),
							ClosedBallInDenseMeet.Read(metric).At(
								b.TermAs[Set[A]]("ball(M, d, fst(p), snd(p))"),
								g.Apply(later),
								b.TermAs[Real]("real_inv(&(n + 1) + &1)"))))
					b.Show(
						"the pair (c, r) is such a ball",
						By(inside, pairs.Fst.At(c, r), pairs.Snd.At(c, r)))
				}))
			next, chosen := a.ObtainAs[Fun2[Prod[A, Real], Nat, Prod[A, Real]]](
				"one such pair chosen for every ball p of M and every n",
				"∃next:(prod(A, real) → num → prod(A, real)). ∀p:prod(A, real). ∀n:num. "+
					"    fst(p) ∈ M ∧ &0 < snd(p) ⇒ "+
					"    fst(next(p, n)) ∈ M ∧ "+
					"    &0 < snd(next(p, n)) ∧ "+
					"    snd(next(p, n)) < real_inv(&(n + 1) + &1) ∧ "+
					"    closed_ball(M, d, fst(next(p, n)), snd(next(p, n))) ⊆ ball(M, d, fst(p), snd(p)) ∩ g(n + 1)",
				By(ballInside))

			_, recursion := a.ObtainAs[Fun[Nat, Prod[A, Real]]](
				"recursion threads the choices: B(0) = (c₀, r₀) and B(n + 1) = next(B(n), n)",
				"∃B:(num → prod(A, real)). B(0) = (c₀, r₀) ∧ ∀n:num. B(n + 1) = next(B(n), n)",
				By(peano.Recursion.At(next, a.TermAs[Prod[A, Real]]("(c₀, r₀)")), nat_arith.Add1))
			threads := a.Conjuncts(
				recursion,
				"the first pair is (c₀, r₀)",
				"each pair after it is the choice inside the one before")
			invariant := a.Have(
				"each B(n) is a ball of M of radius below 1/(n + 1) whose closed ball lies in g(n)",
				"∀n:num. fst(B(n)) ∈ M ∧ &0 < snd(B(n)) ∧ snd(B(n)) < real_inv(&n + &1) ∧ «closedBall»(n) ⊆ g(n)",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"B(0) is (c₀, r₀), whose closed ball lies in u ∩ g(0)",
						threads[0].Rw(),
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						BySets(first))
					b.Step(
						"B(n + 1) is next(B(n), n), chosen inside g(n + 1)",
						func(e *Argument, ih Fact) {
							n := e.TermAs[Nat]("n")
							e.Do(Simp(Fwd(nat_arith.Add1)), threads[1].At(n).Rw())
							e.Show(
								"next(B(n), n) is a closed ball inside g(n + 1), B(n) being a ball of M",
								BySets(chosen.At(e.TermAs[Prod[A, Real]]("B(n)"), n), ih))
						})
				}))

			nested := a.Have(
				"each closed ball lies in the open ball before it, so in its closed ball",
				"∀n:num. «closedBall»(n + 1) ⊆ «closedBall»(n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					b.Do(threads[1].At(n).Rw())
					b.Show(
						"next(B(n), n) is a closed ball inside the open ball B(n), B(n) being a ball of M",
						BySets(
							chosen.At(b.TermAs[Prod[A, Real]]("B(n)"), n),
							invariant.At(n),
							metric_space.BallSubsetClosedBall.At(M, d, b.TermAs[A]("fst(B(n))"), b.TermAs[Real]("snd(B(n))"))))
				}))
			vanishing := a.Have(
				"the radii tend to zero, the n-th being below 1/(n + 1)",
				"∀ε:real. &0 < ε ⇒ ∃n:num. snd(B(n)) < ε",
				Derive(func(b *Argument) {
					ε := b.FixAs[Real]()
					positive := b.Assume()
					N, small := b.ObtainAs[Nat](
						"some 1/(N + 1) is below ε",
						"∃N:num. real_inv(&N + &1) < ε",
						By(positive, real_archimedean.ExistsReciprocalBelow.At(ε)))
					b.Take(N)
					b.Show(
						"the N-th radius is below 1/(N + 1)",
						ByArith(small, invariant.At(N)))
				}))
			balls := a.Have(
				"each B(n) is a ball about a point of M of radius at least zero",
				"∀n:num. fst(B(n)) ∈ M ∧ &0 ≤ snd(B(n))",
				a.ForEach(func(n *Expr[Nat]) Action { return ByArith(invariant.At(n)) }))
			_, common := a.ObtainAs[A](
				"the space being complete, the nested closed balls, "+
					"whose radii tend to zero, have a common point l",
				"∃l:A. ∀n:num. l ∈ «closedBall»(n)",
				By(
					metric,
					complete,
					balls,
					nested,
					vanishing,
					NestedClosedBallsMeet.At(
						M,
						d,
						a.TermAs[Fun[Nat, A]]("λn:num. fst(B(n))"),
						a.TermAs[Fun[Nat, Real]]("λn:num. snd(B(n))"))))
			inU := a.Have(
				"l lies in the first closed ball, inside u",
				"l ∈ u",
				BySets(common.At(zero), threads[0], first, pairs.Fst, pairs.Snd))
			inEvery := a.Have(
				"and in every g(n), which holds the n-th closed ball",
				"∀n:num. l ∈ g(n)",
				BySets(common, invariant))
			a.Show(
				"so l lies in u and in the intersection of the g(n)",
				BySets(inU, inEvery))
		}),
})}

// ---------------------------------------------------------------------------
// Contractions
// ---------------------------------------------------------------------------

// GeometricStepsCauchy — a sequence of points of M whose successive
// distances shrink geometrically is Cauchy.
//
// Say d(x(n + 1), x(n)) ≤ c·qⁿ with 0 ≤ q < 1. By induction on j, adding
// one step at a time by the triangle inequality, the j steps from x(n)
// on cover at most c·(qⁿ − qⁿ⁺ʲ)/(1 − q), so (1 − q)·d(x(n + j), x(n)) ≤
// c·qⁿ. The bounds c·qⁿ tend to zero with the powers of q; past an index
// K at which they are below ε·(1 − q), a term is within ε of every later
// one, and so any two terms are within ε of each other.
var GeometricStepsCauchy = geometricStepsCauchyThm{family.Add(registry.ProofEntry{
	Name: "GeometricStepsCauchy",
	Key:  "prop_38132622e05c3730",
	Build: metric_space.MetricSpace.Law(Statement{
		Binders: "∀x:(num → A). ∀q c:real.",
		Hypotheses: []string{
			"∀n:num. x(n) ∈ M",
			"&0 ≤ q",
			"q < &1",
			"∀n:num. d(x(n + 1), x(n)) ≤ c * q ^ n",
		},
		Conclusion: "metric_cauchy(x)",
	},
		func(
			a *Argument,
			metric metric_space.MetricSpaceFact[on.M],
			x *Arrow[Nat, A],
			q, c *Expr[Real],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"every term is a point of M",
				"q is non-negative",
				"q is below 1",
				"the n-th step is at most c·qⁿ")
			zero := a.TermAs[Nat]("0")
			one := a.TermAs[Nat]("0 + 1")
			x0 := a.MemberOf[on.M](x.Apply(zero), parts[0].At(zero))
			x1 := a.MemberOf[on.M](x.Apply(one), parts[0].At(one))
			scale := a.Have(
				"c is non-negative, bounding the first step",
				"&0 ≤ c",
				ByArith(
					parts[3].At(zero),
					metric_space.DistNonneg.Read(metric).At(x1, x0),
					real_pow.PowExpZeroClause.At(q)))
			telescoping := a.Have(
				"the j steps from x(n) on cover at most c·(qⁿ − qⁿ⁺ʲ)/(1 − q)",
				"∀n j:num. (&1 - q) * d(x(n + j), x(n)) ≤ c * (q ^ n - q ^ (n + j))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					xn := b.MemberOf[on.M](x.Apply(n), parts[0].At(n))
					b.Induct("j")
					b.Base(
						"no step covers no distance",
						ByArith(metric_space.DistSelf.Read(metric).At(xn)))
					b.Step(
						"one more step adds at most c·qⁿ⁺ʲ to the distance, by the triangle inequality",
						func(e *Argument, ih Fact) {
							e.Do(Simp(Fwd(nat_arith.AddSuc), Fwd(real_pow.PowExpSucClause)))
							k := e.TermAs[Nat]("n + j")
							xk := e.MemberOf[on.M](x.Apply(k), parts[0].At(k))
							xNext := e.MemberOf[on.M](e.TermAs[A]("x(suc(n + j))"), parts[0].At(e.TermAs[Nat]("suc(n + j)")))
							shrink := e.TermAs[Real]("&1 - q")
							e.Show(
								"(1 − q)·d(x(n + j + 1), x(n)) is at most (1 − q)·c·qⁿ⁺ʲ + c·(qⁿ − qⁿ⁺ʲ) = c·(qⁿ − qⁿ⁺ʲ⁺¹)",
								ByArith(
									ih,
									parts[2],
									parts[3].At(k),
									nat_arith.Add1.At(k),
									metric_space.DistTriangle.Read(metric).At(xNext, xk, xn),
									real_order_ring.LessEqMulLeft.At(
										shrink,
										e.TermAs[Real]("d(x(suc(n + j)), x(n))"),
										e.TermAs[Real]("d(x(suc(n + j)), x(n + j)) + d(x(n + j), x(n))")),
									real_order_ring.LessEqMulLeft.At(
										shrink,
										e.TermAs[Real]("d(x(suc(n + j)), x(n + j))"),
										e.TermAs[Real]("c * q ^ (n + j)"))))
						})
				}))
			toZero := a.Have(
				"the bounds c·qⁿ tend to zero with the powers of q, |q| being below 1",
				"(λn:num. c * q ^ n) ⟶ c * &0",
				ByArith(
					parts[1],
					parts[2],
					real_sequences.PowerTendsToZero.At(q),
					real_sequences.LimitScale.At(a.TermAs[Fun[Nat, Real]]("λn:num. q ^ n"), a.TermAs[Real]("&0"), c)))

			a.Do(Unfold(MetricCauchyDef))
			a.Do(SplitConj(
				Case(
					"every term is a point of M",
					By(parts[0])),
				Case(
					"past the index at which c·qⁿ is below ε·(1 − q) any two terms are within ε of each other",
					Derive(func(b *Argument) {
						eps := b.FixAs[Real]()
						pos := b.Assume()
						K, small := b.ObtainAs[Nat](
							"past some index K the bounds c·qⁿ are below ε·(1 − q)",
							"∃K:num. ∀n:num. K ≤ n ⇒ |c * q ^ n - &0| < ε * (&1 - q)",
							ByArith(
								b.Unfolded(toZero, real_sequences.RealConvergesToDef).At(b.TermAs[Real]("ε * (&1 - q)")),
								pos,
								parts[2]))
						later := b.Have(
							"past K a term is within ε of every later one: (1 − q)·d(x(n + j), x(n)) ≤ c·qⁿ < ε·(1 − q)",
							"∀n j:num. K ≤ n ⇒ d(x(n + j), x(n)) < ε",
							Derive(func(e *Argument) {
								n := e.FixAs[Nat]()
								j := e.FixAs[Nat]()
								past := e.Assume()
								e.Show(
									"cancel the positive factor 1 − q",
									ByArith(
										telescoping.At(n, j),
										small.At(n),
										past,
										scale,
										parts[1],
										parts[2],
										real_pow.PowNonneg.At(q, e.TermAs[Nat]("n + j")),
										real_order_ring.LessThanCancelMulLeft.At(
											e.TermAs[Real]("&1 - q"),
											e.TermAs[Real]("d(x(n + j), x(n))"),
											eps)))
							}))
						b.Take(K)
						m := b.FixAs[Nat]()
						n := b.FixAs[Nat]()
						past := b.Assume()
						b.Cases(b.Term("n ≤ m"))
						b.When(
							"x(m) is x(n) some steps on",
							func(e *Argument, order Fact) {
								j, gap := e.ObtainAs[Nat](
									"m is n plus a gap j",
									"∃j:num. m = n + j",
									By(order, nat_order.LessEqExists.At(m, n)))
								e.Do(gap.Rw())
								e.Show(
									"x(n + j) is within ε of x(n), n being past K",
									By(later.At(n, j), past))
							})
						b.Otherwise(
							"x(n) is x(m) some steps on, and the distance is symmetric",
							func(e *Argument, order Fact) {
								j, gap := e.ObtainAs[Nat](
									"n is m plus a gap j",
									"∃j:num. n = m + j",
									ByArith(order, nat_order.LessEqExists.At(n, m)))
								e.Do(gap.Rw())
								xm := e.MemberOf[on.M](x.Apply(m), parts[0].At(m))
								xmj := e.MemberOf[on.M](e.TermAs[A]("x(m + j)"), parts[0].At(e.TermAs[Nat]("m + j")))
								e.Show(
									"x(m + j) is within ε of x(m), m being past K",
									ByArith(later.At(m, j), past, metric_space.DistSym.Read(metric).At(xm, xmj)))
							})
					})),
			))
		}),
})}

// BanachFixedPoint — a contraction of a non-empty complete space has
// exactly one fixed point.
//
// The factor may be taken non-negative, q = max(k, 0), since a distance
// is never negative. The iterates x(n) of f from a point p of M take
// steps d(x(n + 1), x(n)) ≤ d(x(1), x(0))·qⁿ, each the image under f of
// the one before; so they form a Cauchy sequence (GeometricStepsCauchy)
// and converge to some l. A Lipschitz map is continuous, so the images
// f(x(n)) converge to f(l); they are the iterates x(n + 1), which
// converge to l; a limit being unique, f(l) = l. A second fixed point y
// would have d(y, l) = d(f(y), f(l)) ≤ k·d(y, l), which with k < 1 forces
// d(y, l) = 0.
var BanachFixedPoint = banachFixedPointThm{family.Add(registry.ProofEntry{
	Name: "BanachFixedPoint",
	Key:  "prop_e57b7728aa5b9082",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀f:(A → A). ∀k:real.",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_complete(M, d)",
			"¬(M = ∅)",
			"∀x:A. x ∈ M ⇒ f(x) ∈ M",
			"k < &1",
			"∀x y:A. x ∈ M ∧ y ∈ M ⇒ d(f(x), f(y)) ≤ k * d(x, y)",
		},
		Conclusion: "∃x:A. x ∈ M ∧ f(x) = x ∧ (∀y:A. y ∈ M ∧ f(y) = y ⇒ y = x)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			complete, nonempty Fact,
			f *Arrow[A, A],
			mapsInto Fact,
			k *Expr[Real],
			below, contraction Fact,
		) {
			zero := a.TermAs[Real]("&0")
			q, factor := a.ObtainAs[Real](
				"the factor may be taken non-negative: max(k, 0) serves as well, a distance being non-negative",
				"∃q:real. &0 ≤ q ∧ q < &1 ∧ ∀x y:A. x ∈ M ∧ y ∈ M ⇒ d(f(x), f(y)) ≤ q * d(x, y)",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Real]("max(k, &0)"))
					b.Do(SplitConjAll(
						Case(
							"max(k, 0) is at least 0",
							ByArith(real_sup_inf.MaxUpperBound.At(k, zero))),
						Case(
							"max(k, 0) is k or 0, both below 1",
							ByArith(below, real_sup_inf.MaxIsArgument.At(k, zero))),
						Case(
							"k·d(x, y) ≤ max(k, 0)·d(x, y), d(x, y) being non-negative",
							Derive(func(e *Argument) {
								x := e.FixAs[A]()
								y := e.FixAs[A]()
								both := e.Conjuncts(
									e.Assume(),
									"x is a point of M",
									"y is a point of M")
								xm := e.MemberOf[on.M](x, both[0])
								ym := e.MemberOf[on.M](y, both[1])
								e.Show(
									"d(f(x), f(y)) ≤ k·d(x, y) ≤ max(k, 0)·d(x, y)",
									ByArith(
										contraction.At(xm, ym),
										xm,
										ym,
										real_sup_inf.MaxUpperBound.At(k, zero),
										metric_space.DistNonneg.Read(metric).At(xm, ym),
										real_order_ring.LessEqMulRight.At(k, e.TermAs[Real]("max(k, &0)"), e.TermAs[Real]("d(x, y)"))))
							})),
					))
				}))
			bounds := a.Conjuncts(
				factor,
				"q is non-negative",
				"q is below 1",
				"f shrinks every distance between points of M by the factor q")
			p, start := a.ObtainAs[A](
				"M being non-empty, it has a point p",
				"∃p:A. p ∈ M",
				By(nonempty, set_basic.MemberNotEmpty))
			x, iterates := a.ObtainAs[Fun[Nat, A]](
				"the iterates of f from p: x(0) = p and x(n + 1) = f(x(n))",
				"∃x:(num → A). x(0) = p ∧ ∀n:num. x(n + 1) = f(x(n))",
				By(peano.Recursion.At(a.TermAs[Fun2[A, Nat, A]]("λb:A. λn:num. f(b)"), p), nat_arith.Add1))
			iterate := a.Conjuncts(
				iterates,
				"the iteration starts at p",
				"each iterate is the image under f of the one before")
			inM := a.Have(
				"the iterates are points of M, f carrying M into itself",
				"∀n:num. x(n) ∈ M",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"x(0) is p",
						By(Normalized, iterate[0], start))
					b.Step(
						"x(n + 1) is f(x(n))",
						func(e *Argument, ih Fact) {
							n := e.TermAs[Nat]("n")
							e.Show(
								"f carries the point x(n) of M into M",
								By(Normalized, ih, iterate[1].At(n), mapsInto.At(e.TermAs[A]("x(n)")), nat_arith.Add1.At(n)))
						})
				}))
			steps := a.Have(
				"the n-th step is at most qⁿ times the first, f shrinking each step by q",
				"∀n:num. d(x(n + 1), x(n)) ≤ d(x(1), x(0)) * q ^ n",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"q⁰ is 1",
						ByArith(real_pow.PowExpZeroClause.At(q)))
					b.Step(
						"the step from x(n + 1) is the image under f of the step from x(n)",
						func(e *Argument, ih Fact) {
							n := e.TermAs[Nat]("n")
							next := e.TermAs[Nat]("n + 1")
							images := e.Have(
								"both ends of the step are images under f",
								"d(x(suc(n) + 1), x(suc(n))) = d(f(x(n + 1)), f(x(n)))",
								By(Normalized, iterate[1].At(e.TermAs[Nat]("suc(n)")), iterate[1].At(n), nat_arith.Add1.At(n)))
							xn := e.MemberOf[on.M](e.TermAs[A]("x(n)"), inM.At(n))
							xNext := e.MemberOf[on.M](e.TermAs[A]("x(n + 1)"), inM.At(next))
							e.Do(Simp(Fwd(real_pow.PowExpSucClause)))
							e.Show(
								"f shrinks the step by q, and q times qⁿ is qⁿ⁺¹",
								ByArith(
									images,
									bounds[2].At(xNext, xn),
									xNext,
									xn,
									ih,
									bounds[0],
									real_order_ring.LessEqMulLeft.At(
										q,
										e.TermAs[Real]("d(x(n + 1), x(n))"),
										e.TermAs[Real]("d(x(1), x(0)) * q ^ n"))))
						})
				}))
			cauchy := a.Have(
				"the steps shrinking geometrically, the iterates form a Cauchy sequence",
				"metric_cauchy(M, d, x)",
				By(
					inM,
					bounds[0],
					bounds[1],
					steps,
					GeometricStepsCauchy.Read(metric).At(x, q, a.TermAs[Real]("d(x(1), x(0))"))))
			l, limit := a.ObtainAs[A](
				"M being complete, the iterates converge to some l",
				"∃l:A. metric_converges_to(M, d, x, l)",
				By(complete, cauchy, MetricCompleteDef))
			lm := a.MemberOf[on.M](l, a.Have(
				"l is a point of M",
				"l ∈ M",
				By(limit, MetricConvergesToDef)))

			successors := a.Have(
				"the images f(x(n)) are the iterates x(n + 1)",
				"f ∘ x = x ∘ (λj:num. j + 1)",
				Unfold(functions.ComposeApply),
				By(Normalized, iterate[1]))
			lipschitz := a.Have(
				"f is Lipschitz on M, stretching no distance by more than k",
				"lipschitz_map(M, d, M, d, f)",
				LipschitzMap.Intro(
					Case(
						"f carries M into M",
						By(mapsInto)),
					Case(
						"k bounds every stretch",
						Derive(func(b *Argument) {
							b.Take(k)
							b.Show(
								"the contraction inequality",
								By(contraction))
						})),
				))
			uniform := a.Have(
				"so f is uniformly continuous",
				"uniformly_continuous_map(M, d, M, d, f)",
				By(metric, LipschitzImpUniformlyContinuous.Read(lipschitz)))
			images := a.Have(
				"f being continuous, the images f(x(n)) converge to f(l)",
				"metric_converges_to(M, d, f ∘ x, f(l))",
				By(
					metric,
					limit,
					UniformlyContinuousImpContinuous.Read(uniform),
					ContinuousIffSequential.At(M, d, M, d, f)))
			shifted := a.Have(
				"the iterates from the second on are a subsequence, so they converge to l",
				"metric_converges_to(M, d, x ∘ (λj:num. j + 1), l)",
				ByArith(limit, LimitSubsequence.At(M, d, x, a.TermAs[Fun[Nat, Nat]]("λj:num. j + 1"), l)))
			fixed := a.Have(
				"they are the images f(x(n)), and a limit is unique, so f(l) = l",
				"f(l) = l",
				By(
					successors,
					images,
					shifted,
					metric,
					LimitUnique.At(M, d, a.TermAs[Fun[Nat, A]]("x ∘ (λj:num. j + 1)"), l, f.Apply(l))))
			a.Take(l)
			a.Do(SplitConjAll(
				Case(
					"l is a point of M",
					By(lm)),
				Case(
					"f fixes l",
					By(fixed)),
				Case(
					"a fixed point y of f is l: d(y, l) ≤ k·d(y, l) with k < 1 forces d(y, l) = 0",
					Derive(func(b *Argument) {
						y := b.FixAs[A]()
						given := b.Conjuncts(
							b.Assume(),
							"y is a point of M",
							"f fixes y")
						ym := b.MemberOf[on.M](y, given[0])
						shrunk := b.Have(
							"f fixes both, so the contraction inequality at y and l reads d(y, l) ≤ k·d(y, l)",
							"d(y, l) ≤ k * d(y, l)",
							By(Normalized, contraction.At(ym, lm), ym, lm, given[1], fixed))
						b.Show(
							"a non-negative distance at most k < 1 times itself is zero, and y is l",
							ByArith(
								shrunk,
								below,
								metric_space.DistNonneg.Read(metric).At(ym, lm),
								metric_space.DistZeroIff.Read(metric).At(ym, lm)))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Products
// ---------------------------------------------------------------------------

// ProductComplete — the product of two complete metric spaces is
// complete.
//
// Each coordinate distance is at most the product distance, the larger
// of the two. So the coordinates of a Cauchy sequence of pairs form
// Cauchy sequences of M and of N, which converge, to u and to v. Past the
// sum of the indices at which the first coordinates come within ε of u
// and the second within ε of v, both coordinate distances are below ε,
// and so is the larger of them: the pairs converge to (u, v). No axiom of
// either distance enters.
var ProductComplete = productCompleteThm{family.Add(registry.ProofEntry{
	Name: "ProductComplete",
	Key:  "prop_d468225607b24c6c",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real).",
		Hypotheses: []string{
			"metric_complete(M, d)",
			"metric_complete(N, e)",
		},
		Conclusion: "metric_complete(set_cross(M, N), product_metric(d, e))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			completeM Fact,
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			completeN Fact,
		) {
			// The two completenesses read as their sentences: every Cauchy
			// sequence converges.
			convergeM := a.Unfolded(completeM, MetricCompleteDef)
			convergeN := a.Unfolded(completeN, MetricCompleteDef)
			dominated := a.Have(
				"each coordinate distance is at most the product distance, the larger of the two",
				"∀p q:prod(A, B). "+
					"    d(fst(p), fst(q)) ≤ product_metric(d, e, p, q) ∧ "+
					"    e(snd(p), snd(q)) ≤ product_metric(d, e, p, q)",
				Derive(func(b *Argument) {
					b.FixAs[Prod[A, B]]("p")
					b.FixAs[Prod[A, B]]("q")
					b.Show(
						"the larger of two numbers is at least each",
						ByArith(
							real_sup_inf.MaxUpperBound.At(
								b.TermAs[Real]("d(fst(p), fst(q))"), b.TermAs[Real]("e(snd(p), snd(q))")),
							metric_space.ProductMetricDef))
				}))

			// The goal read as its sentence: every Cauchy sequence of pairs
			// converges to a pair of M × N.
			a.Do(Unfold(MetricCompleteDef))
			a.FixAs[Fun[Nat, Prod[A, B]]]()
			cauchy := a.Conjuncts(
				a.Unfolded(a.Assume(), MetricCauchyDef),
				"every term is a pair of M × N",
				"every positive distance holds any two terms past some index")
			coordinates := a.Have(
				"the coordinates of the terms are points of M and of N",
				"∀n:num. fst(x(n)) ∈ M ∧ snd(x(n)) ∈ N",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					b.Show(
						"x(n) is a pair of M × N",
						By(cauchy[0].At(n), set_product.InCrossProjections.At(M, N, b.TermAs[Prod[A, B]]("x(n)"))))
				}))
			firsts := a.Have(
				"the first coordinates form a Cauchy sequence of M, "+
					"their distances being at most the product distances",
				"metric_cauchy(M, d, λn:num. fst(x(n)))",
				Unfold(MetricCauchyDef),
				SplitConj(
					Case(
						"every first coordinate is a point of M",
						By(coordinates)),
					Case(
						"past the index at which any two pairs are within ε, any two first coordinates are",
						Derive(func(b *Argument) {
							eps := b.FixAs[Real]()
							pos := b.Assume()
							K, together := b.ObtainAs[Nat](
								"x being Cauchy, past some index K any two terms are within ε of each other",
								"∃K:num. ∀m n:num. K ≤ m ∧ K ≤ n ⇒ product_metric(d, e, x(m), x(n)) < ε",
								By(cauchy[1].At(eps), pos))
							b.Take(K)
							m := b.FixAs[Nat]()
							n := b.FixAs[Nat]()
							past := b.Assume()
							b.Show(
								"the first coordinates of x(m) and x(n) are no further apart than the pairs",
								ByArith(
									together.At(m, n),
									past,
									dominated.At(b.TermAs[Prod[A, B]]("x(m)"), b.TermAs[Prod[A, B]]("x(n)"))))
						})),
				))
			seconds := a.Have(
				"so do the second coordinates, in N",
				"metric_cauchy(N, e, λn:num. snd(x(n)))",
				Unfold(MetricCauchyDef),
				SplitConj(
					Case(
						"every second coordinate is a point of N",
						By(coordinates)),
					Case(
						"past the index at which any two pairs are within ε, any two second coordinates are",
						Derive(func(b *Argument) {
							eps := b.FixAs[Real]()
							pos := b.Assume()
							K, together := b.ObtainAs[Nat](
								"x being Cauchy, past some index K any two terms are within ε of each other",
								"∃K:num. ∀m n:num. K ≤ m ∧ K ≤ n ⇒ product_metric(d, e, x(m), x(n)) < ε",
								By(cauchy[1].At(eps), pos))
							b.Take(K)
							m := b.FixAs[Nat]()
							n := b.FixAs[Nat]()
							past := b.Assume()
							b.Show(
								"the second coordinates of x(m) and x(n) are no further apart than the pairs",
								ByArith(
									together.At(m, n),
									past,
									dominated.At(b.TermAs[Prod[A, B]]("x(m)"), b.TermAs[Prod[A, B]]("x(n)"))))
						})),
				))
			u, toFirst := a.ObtainAs[A](
				"M being complete, the first coordinates converge to some u",
				"∃u:A. metric_converges_to(M, d, λn:num. fst(x(n)), u)",
				By(convergeM.At(a.TermAs[Fun[Nat, A]]("λn:num. fst(x(n))")), firsts))
			v, toSecond := a.ObtainAs[B](
				"N being complete, the second coordinates converge to some v",
				"∃v:B. metric_converges_to(N, e, λn:num. snd(x(n)), v)",
				By(convergeN.At(a.TermAs[Fun[Nat, B]]("λn:num. snd(x(n))")), seconds))
			nearFirst := a.Conjuncts(
				a.Unfolded(toFirst, MetricConvergesToDef),
				"u is a point of M",
				"every first coordinate is a point of M",
				"every positive distance about u holds a tail of the first coordinates")
			nearSecond := a.Conjuncts(
				a.Unfolded(toSecond, MetricConvergesToDef),
				"v is a point of N",
				"every second coordinate is a point of N",
				"every positive distance about v holds a tail of the second coordinates")

			// The pairs converge to (u, v), read as the ε-N sentence.
			a.Take(a.TermAs[Prod[A, B]]("(u, v)"))
			a.Do(Unfold(MetricConvergesToDef))
			a.Do(SplitConjAll(
				Case(
					"(u, v) is a pair of M × N",
					By(nearFirst[0], nearSecond[0], set_product.InCross.At(M, N, u, v))),
				Case(
					"every term is a pair of M × N",
					By(cauchy[0])),
				Case(
					"past the sum of the two coordinates' indices for ε, the larger coordinate distance is below ε",
					Derive(func(b *Argument) {
						eps := b.FixAs[Real]()
						pos := b.Assume()
						_, tailFirst := b.ObtainAs[Nat](
							"past some index K₁ the first coordinates are within ε of u",
							"∃K₁:num. ∀n:num. K₁ ≤ n ⇒ d(fst(x(n)), u) < ε",
							By(nearFirst[2].At(eps), pos))
						_, tailSecond := b.ObtainAs[Nat](
							"and past some index K₂ the second coordinates within ε of v",
							"∃K₂:num. ∀n:num. K₂ ≤ n ⇒ e(snd(x(n)), v) < ε",
							By(nearSecond[2].At(eps), pos))
						b.Take(b.TermAs[Nat]("K₁ + K₂"))
						n := b.FixAs[Nat]()
						past := b.Assume()
						b.Show(
							"both coordinate distances of x(n) from (u, v) are below ε, so the larger is",
							ByArith(
								tailFirst.At(n),
								tailSecond.At(n),
								past,
								metric_space.ProductMetricDef.At(
									d, e, b.TermAs[Prod[A, B]]("x(n)"), b.TermAs[Prod[A, B]]("(u, v)")),
								pairs.Fst.At(u, v),
								pairs.Snd.At(u, v),
								real_sup_inf.MaxIsArgument.At(
									b.TermAs[Real]("d(fst(x(n)), u)"), b.TermAs[Real]("e(snd(x(n)), v)"))))
					})),
			))
		}),
})}

// CountableProductComplete — a countable product of complete factors is
// complete under the countable product distance along a sequence h that
// runs through the indices of J; no metric axiom of the factors is asked.
//
// The product distance controls each active coordinate uniformly
// (metric_space.CountableProductProjectionUniform), so the coordinates of
// a Cauchy sequence of the product are Cauchy sequences of their factors,
// which converge; their limits, with the prescribed values at the inactive
// indices, make a point l of the product. For ε > 0, the coordinates h
// takes up to some place N control the product distance to within ε/2
// (metric_space.CountableProductHeadBound), and past the largest of the
// finitely many indices at which those coordinates come within ε/2 of
// their limits the sequence is within ε/2 of l.
var CountableProductComplete = countableProductCompleteThm{family.Add(registry.ProofEntry{
	Name: "CountableProductComplete",
	Key:  "prop_ffd8bcace86e507b",
	Build: family.Sections(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)). ∀d:(I → A → A → real). ∀h:(num → I).",
		Hypotheses: []string{
			"J ⊆ image(h, 𝕌)",
			"∀i:I. i ∈ J ⇒ metric_complete(X(i), d(i))",
		},
		Conclusion: "metric_complete(indexed_functions(J, z, X), countable_product_metric(J, d, h))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			finiteHeadBound := ctx.Lemma("∀f:(num → num). ∀N:num. ∃K:num. ∀i:num. i ≤ N ⇒ f(i) ≤ K", func(
				a *Argument,
				f *Arrow[Nat, Nat],
				N *Expr[Nat],
			) {
				finiteImage := a.Have(
					"the image of the finite initial segment is finite",
					"finite(image(f, 0 .. N))",
					By(
						num_segment.Finite.At(a.TermAs[Nat]("0"), N),
						finite_set.FiniteImage.At(f, a.TermAs[Set[Nat]]("0 .. N"))))
				a.Show(
					"a finite set of natural indices has an upper bound",
					BySets(
						finiteImage,
						num_segment.FiniteIffBounded.At(a.TermAs[Set[Nat]]("image(f, 0 .. N)")),
						num_segment.MembershipFromZero))
			})
			return ctx.Theorem(headline, func(
				a *Argument,
				J *Expr[Set[I]],
				z *Arrow[I, A],
				X *Arrow[I, Set[A]],
				d *Expr[Fun3[I, A, A, Real]],
				h *Arrow[Nat, I],
				cover, factors Fact,
			) {
				C := a.TermAs[Set[Fun[I, A]]]("indexed_functions(J, z, X)")
				D := a.TermAs[Fun2[Fun[I, A], Fun[I, A], Real]]("countable_product_metric(J, d, h)")
				projections := a.Have(
					"each active coordinate projection is uniformly continuous",
					Statement{
						Binders: "∀i:I.",
						Hypotheses: []string{
							"i ∈ J",
						},
						Conclusion: "uniformly_continuous_map(indexed_functions(J, z, X), " +
							"    countable_product_metric(J, d, h), " +
							"    X(i), " +
							"    d(i), " +
							"    λf:(I → A). f(i))",
					},
					Derive(func(b *Argument) {
						i := b.FixAs[I]()
						active := b.Assume()
						b.Do(Unfold(UniformlyContinuousMap), SplitConj(
							Case(
								"the projection maps the product into its factor",
								By(active, At(indexed_functions.IndexedFunctionsCoordinate, J, z, X, i))),
							Case(
								"the product distance controls the coordinate uniformly",
								Derive(func(c *Argument) {
									eps := c.FixAs[Real]()
									positive := c.Assume()
									taken := c.Have(
										"h takes the index i",
										"i ∈ image(h, 𝕌)",
										BySets(cover, active))
									c.Show(
										"the δ that serves ε for all functions serves it for the points of the product",
										By(taken, active, positive, metric_space.CountableProductProjectionUniform.At(J, d, h, i, eps)))
								})),
						))
					}))
				a.Do(Simp(Fwd(MetricCompleteDef)))
				x := a.FixAs[Fun[Nat, Fun[I, A]]]()
				cauchy := a.Assume()
				activeLimits := a.Have(
					"each active coordinate sequence is Cauchy and has a limit",
					"∀i:I. i ∈ J ⇒ ∃l:A. metric_converges_to(X(i), d(i), λk:num. x(k, i), l)",
					Derive(func(b *Argument) {
						i := b.FixAs[I]()
						active := b.Assume()
						projection := b.TermAs[Fun[Fun[I, A], A]]("λf:(I → A). f(i)")
						completeFactor := b.Unfolded(GroupPremises(active, factors.At(i)), MetricCompleteDef)
						b.Show(
							"uniformly continuous projections carry a Cauchy sequence into a complete factor",
							By(
								completeFactor,
								projections.At(i),
								active,
								cauchy,
								UniformlyContinuousCauchy.At(
									C, D, b.TermAs[Set[A]]("X(i)"), b.TermAs[Fun2[A, A, Real]]("d(i)"), projection, x),
								functions.ComposeApply.At(projection, x)))
					}))
				pointChoices := a.Have(
					"limits are chosen on active coordinates and prescribed values on inactive ones",
					"∀i:I. ∃y:A. (i ∈ J ⇒ metric_converges_to(X(i), d(i), λk:num. x(k, i), y)) ∧ (i ∉ J ⇒ y = z(i))",
					Derive(func(b *Argument) {
						i := b.FixAs[I]()
						b.Cases(b.TermAs[Bool]("i ∈ J"))
						b.When(
							"an active coordinate has a complete-factor limit",
							func(c *Argument, active Fact) {
								c.Show(
									"the active limit supplies the choice",
									By(activeLimits.At(i), active))
							})
						b.Otherwise(
							"an inactive coordinate uses its prescribed value",
							func(c *Argument, inactive Fact) {
								c.Take(z.Apply(i))
								c.Show(
									"the inactive normalization is satisfied",
									By(inactive))
							})
					}))
				l, chosen := a.ObtainAs[Fun[I, A]](
					"choose the coordinate limit function",
					"∃l:(I → A). ∀i:I. "+
						"    (i ∈ J ⇒ metric_converges_to(X(i), d(i), λk:num. x(k, i), l(i))) ∧ (i ∉ J ⇒ l(i) = z(i))",
					By(pointChoices))
				limits := a.Unfolded(chosen, MetricConvergesToDef)
				members := a.Have(
					"the limit and every term are normalized product points",
					"l ∈ indexed_functions(J, z, X) ∧ (∀k:num. x(k) ∈ indexed_functions(J, z, X))",
					BySets(
						limits,
						cauchy,
						indexed_functions.IndexedFunctionsDef.At(J, z, X),
						MetricCauchyDef.Inst[Fun[I, A]]().At(C, D, x)))
				convergence := a.Have(
					"finitely many coordinates converge together, and they control the product distance",
					"∀ε:real. &0 < ε ⇒ ∃K:num. ∀k:num. K ≤ k ⇒ countable_product_metric(J, d, h, x(k), l) < ε",
					Derive(func(b *Argument) {
						b.FixAs[Real]()
						positive := b.Assume()
						halfPositive := b.Have(
							"half the radius is positive",
							"&0 < ε / &2",
							ByArith(positive))
						N, head := b.ObtainAs[Nat](
							"the coordinates h takes up to some place N control the product distance to within ε / 2",
							"∃N:num. ∀u v:(I → A). "+
								"    (∀n:num. n ≤ N ∧ h(n) ∈ J ⇒ d(h(n), u(h(n)), v(h(n))) < ε / &2) ⇒ "+
								"    countable_product_metric(J, d, h, u, v) ≤ ε / &2",
							By(halfPositive, metric_space.CountableProductHeadBound.At(J, d, h, b.TermAs[Real]("ε / &2"))))
						thresholds := b.Have(
							"the coordinate at each index of J that h takes comes within ε / 2 of its limit from some index on",
							"∀n:num. h(n) ∈ J ⇒ ∃K:num. ∀k:num. K ≤ k ⇒ d(h(n), x(k, h(n)), l(h(n))) < ε / &2",
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]()
								active := c.Assume()
								c.Show(
									"its convergence in the factor at ε / 2 gives the index",
									By(limits.At(h.Apply(n)), active, halfPositive))
							}))
						t, past := b.ObtainAs[Fun[Nat, Nat]](
							"choose such an index for each place",
							"∃t:(num → num). ∀n k:num. h(n) ∈ J ∧ t(n) ≤ k ⇒ d(h(n), x(k, h(n)), l(h(n))) < ε / &2",
							By(thresholds))
						K, bounded := b.ObtainAs[Nat](
							"one index lies past the chosen indices of the places up to N",
							"∃K:num. ∀i:num. i ≤ N ⇒ t(i) ≤ K",
							By(At(finiteHeadBound, t, N)))
						b.Take(K)
						k := b.FixAs[Nat]()
						late := b.Assume()
						near := b.Have(
							"from K on, the active coordinates taken up to N are within ε / 2 of their limits",
							"∀n:num. n ≤ N ∧ h(n) ∈ J ⇒ d(h(n), x(k, h(n)), l(h(n))) < ε / &2",
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]()
								data := c.Assume()
								c.Show(
									"the chosen index at n is at most K",
									ByArith(past.At(n, k), bounded.At(n), late, data))
							}))
						within := b.Have(
							"so the term is within ε / 2 of the limit",
							"countable_product_metric(J, d, h, x(k), l) ≤ ε / &2",
							By(head.At(b.TermAs[Fun[I, A]]("x(k)"), l), near))
						b.Show(
							"half the radius is below the radius",
							ByArith(within, positive))
					}))
				a.Take(l)
				a.Show(
					"the chosen limit satisfies metric convergence",
					By(convergence, members, MetricConvergesToDef.Inst[Fun[I, A]]().At(C, D, x, l)))
			})
		}),
})}
