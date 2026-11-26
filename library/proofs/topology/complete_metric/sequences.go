// sequences.go — sequences in a metric space: a limit is unique, a
// convergent sequence is Cauchy, a subsequence converges where the
// sequence does, a Cauchy sequence converges where a subsequence does,
// and a point of M every ball about which meets a set is the limit of a
// sequence of its points. So the closed sets are the sets that keep the
// limits of their sequences, a closed subset of a complete space is
// complete and a complete subset closed, the closure of a set is the set
// of limits of its sequences, and the continuous maps are those carrying
// convergent sequences to convergent sequences; and the terms of a
// Cauchy sequence form a bounded set.

package complete_metric

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Limits and Cauchy sequences
// ---------------------------------------------------------------------------

// LimitUnique — a sequence converges to at most one point.
//
// Were the two limits l and m distinct, they would lie a positive
// distance d(l, m) apart. Asked for half of it, each limit hands over an
// index past which the terms are within d(l, m)/2 of it; at an index past
// both, the detour from l to m through that term is shorter than d(l, m).
var LimitUnique = limitUniqueThm{family.Add(registry.ProofEntry{
	Name: "LimitUnique",
	Key:  "prop_978f82af07a4f9b",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:(num → A). ∀l m:A.",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_converges_to(M, d, x, l)",
			"metric_converges_to(M, d, x, m)",
		},
		Conclusion: "l = m",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			x *Arrow[Nat, A],
			l, m *Expr[A],
			toL, toM Fact,
		) {
			nearL := a.Conjuncts(
				a.Unfolded(toL, MetricConvergesToDef),
				"l is a point of M",
				"every term is a point of M",
				"every positive distance about l holds a tail of x")
			nearM := a.Conjuncts(
				a.Unfolded(toM, MetricConvergesToDef),
				"m is a point of M",
				"every term is a point of M",
				"every positive distance about m holds a tail of x")
			lM := a.MemberOf[on.M](l, nearL[0])
			mM := a.MemberOf[on.M](m, nearM[0])

			distinct := a.SupposeNot()
			apart := a.Have(
				"two distinct points of M lie a positive distance apart",
				"&0 < d(l, m)",
				ByArith(
					distinct,
					metric_space.DistZeroIff.Read(metric).At(lM, mM),
					metric_space.DistNonneg.Read(metric).At(lM, mM)))
			half := a.TermAs[Real]("d(l, m) / &2")
			_, tailL := a.ObtainAs[Nat](
				"asked for half that distance, the limit l hands over "+
					"an index N₀ past which the terms are within it of l",
				"∃N:num. ∀n:num. N ≤ n ⇒ d(x(n), l) < d(l, m) / &2",
				ByArith(nearL[2].At(half), apart),
				Named("N₀"))
			_, tailM := a.ObtainAs[Nat](
				"and the limit m an index N₁ past which they are within it of m",
				"∃N:num. ∀n:num. N ≤ n ⇒ d(x(n), m) < d(l, m) / &2",
				ByArith(nearM[2].At(half), apart),
				Named("N₁"))
			n := a.TermAs[Nat]("N₀ + N₁")
			xn := a.MemberOf[on.M](x.Apply(n), nearL[1].At(n))
			a.Show(
				"x(N₀ + N₁) lies within d(l, m)/2 of both, so the "+
					"detour from l to m through it is shorter than d(l, m)",
				ByArith(
					tailL.At(n),
					tailM.At(n),
					metric_space.DistTriangle.Read(metric).At(lM, xn, mM),
					metric_space.DistSym.Read(metric).At(lM, xn)))
		}),
})}

// ConvergentImpCauchy — a convergent sequence is Cauchy.
//
// Given ε > 0, the limit is asked for half of it: it hands over an index
// N past which every term is within ε/2 of l. Two terms past N are then
// within ε of each other, by the detour through l.
var ConvergentImpCauchy = convergentImpCauchyThm{family.Add(registry.ProofEntry{
	Name: "ConvergentImpCauchy",
	Key:  "prop_6b794cb2819b0e2b",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:(num → A). ∀l:A.",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_converges_to(M, d, x, l)",
		},
		Conclusion: "metric_cauchy(M, d, x)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			x *Arrow[Nat, A],
			l *Expr[A],
			converges Fact,
		) {
			near := a.Conjuncts(
				a.Unfolded(converges, MetricConvergesToDef),
				"l is a point of M",
				"every term is a point of M",
				"every positive distance about l holds a tail of x")
			lM := a.MemberOf[on.M](l, near[0])

			// The goal read as its ε-N statement: pairs of terms, and no
			// limit named.
			a.Do(Unfold(MetricCauchyDef))
			a.Do(SplitConj(
				Case(
					"every term is a point of M",
					By(near[1])),
				Case(
					"past some index any two terms are within ε of each other",
					Derive(func(b *Argument) {
						b.FixAs[Real]()
						pos := b.Assume()
						half := b.TermAs[Real]("ε / &2")
						N, tail := b.ObtainAs[Nat](
							"asked for ε/2, the limit hands over an index N past which every term is within ε/2 of l",
							"∃N:num. ∀n:num. N ≤ n ⇒ d(x(n), l) < ε / &2",
							ByArith(near[2].At(half), pos))
						b.Take(N)
						m := b.FixAs[Nat]()
						n := b.FixAs[Nat]()
						past := b.Assume()
						xm := b.MemberOf[on.M](x.Apply(m), near[1].At(m))
						xn := b.MemberOf[on.M](x.Apply(n), near[1].At(n))
						b.Show(
							"two terms past N, each within ε/2 of l, are within ε of each other by the detour through l",
							ByArith(
								tail.At(m),
								tail.At(n),
								past,
								metric_space.DistTriangle.Read(metric).At(xm, lM, xn),
								metric_space.DistSym.Read(metric).At(lM, xn)))
					})),
			))
		}),
})}

// LimitSubsequence — a subsequence of a convergent sequence converges to
// the same point.
//
// A strictly increasing σ never falls below the identity. So the index
// N₀ that the limit hands over at ε serves x ∘ σ as well: past it,
// N₀ ≤ k ≤ σ(k), and the k-th term of the subsequence, x(σ(k)), is a
// term of x past N₀, within ε of l. Being terms of x, the terms of the
// subsequence lie in M.
var LimitSubsequence = limitSubsequenceThm{family.Add(registry.ProofEntry{
	Name: "LimitSubsequence",
	Key:  "prop_f014da682e2e4af7",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:(num → A). ∀σ:(num → num). ∀l:A.",
		Hypotheses: []string{
			"∀j:num. σ(j) < σ(j + 1)",
			"metric_converges_to(M, d, x, l)",
		},
		Conclusion: "metric_converges_to(M, d, x ∘ σ, l)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			x *Arrow[Nat, A],
			σ *Arrow[Nat, Nat],
			l *Expr[A],
			rises, converges Fact,
		) {
			near := a.Conjuncts(
				a.Unfolded(converges, MetricConvergesToDef),
				"l is a point of M",
				"every term is a point of M",
				"every positive distance about l holds a tail of x")

			// The goal read as its ε-N statement; `o` is the constant behind
			// `∘`: unfolded, the k-th term of x ∘ σ is x(σ(k)).
			a.Do(Unfold(MetricConvergesToDef), Unfold(functions.ComposeApply))
			a.Do(SplitConjAll(
				Case(
					"l is a point of M",
					By(near[0])),
				Case(
					"every term x(σ(k)) of the subsequence is a term of x, so a point of M",
					By(near[1])),
				Case(
					"the index x hands over at ε serves the subsequence too",
					Derive(func(b *Argument) {
						eps := b.FixAs[Real]()
						pos := b.Assume()
						N0, tail := b.ObtainAs[Nat](
							"at ε the limit hands over an index N₀ past which every term of x is within ε of l",
							"∃N:num. ∀n:num. N ≤ n ⇒ d(x(n), l) < ε",
							By(near[2].At(eps), pos),
							Named("N₀"))
						b.Take(N0)
						k := b.FixAs[Nat]("k")
						past := b.Assume()
						σk := σ.Apply(k)
						b.Show(
							"σ never falls below the identity, so N₀ ≤ k ≤ σ(k) and x(σ(k)) is a term of x past N₀",
							By(
								tail.At(σk),
								past,
								rises,
								nat_order.LessEqStrictlyIncreasing.At(σ, k),
								nat_order.LessEqTrans.At(N0, k, σk)))
					})),
			))
		}),
})}

// CauchySubsequenceConverges — a Cauchy sequence with a convergent
// subsequence converges, to the subsequence's limit.
//
// Given ε > 0, past some index N₀ any two terms are within ε/2 of each
// other, and past some index N₁ the terms of the subsequence are within
// ε/2 of l. At j = N₀ + N₁ the index σ(j) lies past N₀, σ never falling
// below the identity, so a term x(n) past N₀ is within ε/2 of x(σ(j)),
// which is within ε/2 of l.
var CauchySubsequenceConverges = cauchySubsequenceConvergesThm{family.Add(registry.ProofEntry{
	Name: "CauchySubsequenceConverges",
	Key:  "prop_8259e8a6ecf1d5cc",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:(num → A). ∀σ:(num → num). ∀l:A.",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_cauchy(M, d, x)",
			"∀j:num. σ(j) < σ(j + 1)",
			"metric_converges_to(M, d, x ∘ σ, l)",
		},
		Conclusion: "metric_converges_to(M, d, x, l)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			x *Arrow[Nat, A],
			cauchy Fact,
			σ *Arrow[Nat, Nat],
			rises Fact,
			l *Expr[A],
			converges Fact,
		) {
			together := a.Conjuncts(
				a.Unfolded(cauchy, MetricCauchyDef),
				"every term is a point of M",
				"every positive distance holds any two terms past some index")
			near := a.Conjuncts(
				a.Unfolded(a.Unfolded(converges, MetricConvergesToDef), functions.ComposeApply),
				"l is a point of M",
				"every term of the subsequence is a point of M",
				"every positive distance about l holds a tail of the subsequence")
			lM := a.MemberOf[on.M](l, near[0])

			a.Do(Unfold(MetricConvergesToDef))
			a.Do(SplitConjAll(
				Case(
					"l is a point of M",
					By(near[0])),
				Case(
					"every term is a point of M",
					By(together[0])),
				Case(
					"past the Cauchy index for ε/2 every term is within ε of l",
					Derive(func(b *Argument) {
						b.FixAs[Real]()
						pos := b.Assume()
						half := b.TermAs[Real]("ε / &2")
						N0, pairs := b.ObtainAs[Nat](
							"x being Cauchy, past some index N₀ any two terms are within ε/2 of each other",
							"∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ d(x(m), x(n)) < ε / &2",
							ByArith(together[1].At(half), pos),
							Named("N₀"))
						_, tail := b.ObtainAs[Nat](
							"and past some index N₁ the terms of the subsequence are within ε/2 of l",
							"∃N:num. ∀n:num. N ≤ n ⇒ d(x(σ(n)), l) < ε / &2",
							ByArith(near[2].At(half), pos),
							Named("N₁"))
						b.Take(N0)
						n := b.FixAs[Nat]()
						past := b.Assume()
						j := b.TermAs[Nat]("N₀ + N₁")
						σj := σ.Apply(j)
						xn := b.MemberOf[on.M](x.Apply(n), together[0].At(n))
						xσj := b.MemberOf[on.M](x.Apply(σj), together[0].At(σj))
						b.Show(
							"σ(N₀ + N₁) ≥ N₀ + N₁ lies past N₀, so x(n) is "+
								"within ε/2 of x(σ(N₀ + N₁)), which is within ε/2 of l",
							ByArith(
								pairs.At(n, σj),
								tail.At(j),
								past,
								rises,
								nat_order.LessEqStrictlyIncreasing.At(σ, j),
								metric_space.DistTriangle.Read(metric).At(xn, xσj, lM)))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Closed sets by sequences
// ---------------------------------------------------------------------------

// ApproachingSequence — a point of M every ball about which meets s is
// the limit of a sequence of points of s.
//
// The ball of radius 1/(n + 1) about l holds a point of s for each n, and
// choosing one for each n is a sequence x of points of s whose n-th term
// lies within 1/(n + 1) of l. Those distances tend to zero
// (real_sequences.WithinReciprocalConverges), which is what convergence
// to l asks.
var ApproachingSequence = approachingSequenceThm{family.Add(registry.ProofEntry{
	Name: "ApproachingSequence",
	Key:  "prop_aaf23a9080a63856",
	Build: metric_space.MetricSpace.Law(Statement{
		Binders: "∀s:set(A). ∀l:A.",
		Hypotheses: []string{
			"l ∈ M",
			"∀r:real. &0 < r ⇒ ball(l, r) ∩ s ≠ ∅",
		},
		Conclusion: "∃x:(num → A). (∀n:num. x(n) ∈ s) ∧ metric_converges_to(x, l)",
	},
		func(
			a *Argument,
			metric metric_space.MetricSpaceFact[on.M],
			s *Expr[Set[A]],
			l *Expr[A],
			given Fact,
		) {
			about := a.Conjuncts(
				given,
				"l is a point of M",
				"every ball about l meets s")
			lM := a.MemberOf[on.M](l, about[0])
			pointPerIndex := a.Have(
				"for each n the ball of radius 1/(n + 1) about l holds a point of s",
				"∀n:num. ∃y:A. y ∈ s ∧ y ∈ M ∧ d(l, y) < real_inv(&n + &1)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					positive := b.Have(
						"1/(n + 1) is a positive radius, n + 1 being positive",
						"&0 < real_inv(&n + &1)",
						ByArith(real_order_field.InvPos.At(b.TermAs[Real]("&n + &1"))))
					meets := about[1].At(b.TermAs[Real]("real_inv(&n + &1)"))
					b.Show(
						"so the ball of that radius meets s, at a point of M within 1/(n + 1) of l",
						BySets(b.Unfolded(GroupPremises(positive, meets), metric_space.BallDef)))
				}))
			x, chosen := a.ObtainAs[Fun[Nat, A]](
				"choosing one such point for each n is a sequence x",
				"∃x:(num → A). (∀n:num. x(n) ∈ s) ∧ (∀n:num. x(n) ∈ M) ∧ ∀n:num. d(l, x(n)) < real_inv(&n + &1)",
				By(pointPerIndex))
			terms := a.Conjuncts(
				chosen,
				"every term is a point of s",
				"every term is a point of M",
				"the n-th term lies within 1/(n + 1) of l")
			near := a.Have(
				"so the n-th distance d(x(n), l) lies within 1/(n + 1) of zero",
				"∀n:num. |d(x(n), l) - &0| < real_inv(&n + &1)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					xn := b.MemberOf[on.M](b.TermAs[A]("x(n)"), terms[1].At(n))
					b.Show(
						"d(x(n), l) is d(l, x(n)), at least zero and below 1/(n + 1)",
						ByArith(
							terms[2].At(n),
							metric_space.DistSym.Read(metric).At(lM, xn),
							metric_space.DistNonneg.Read(metric).At(xn, lM)))
				}))
			distances := a.TermAs[Fun[Nat, Real]]("λn:num. d(x(n), l)")
			toZero := a.Unfolded(
				GroupPremises(near, real_sequences.WithinReciprocalConverges.At(distances, a.TermAs[Real]("&0"))),
				real_sequences.RealConvergesToDef)
			converges := a.Have(
				"x converges to l, the distances of its terms from l tending to zero",
				"metric_converges_to(x, l)",
				Unfold(MetricConvergesToDef),
				SplitConjAll(
					Case(
						"l is a point of M",
						By(about[0])),
					Case(
						"every term is a point of M",
						By(terms[1])),
					Case(
						"past some index every term is within ε of l",
						Derive(func(b *Argument) {
							eps := b.FixAs[Real]()
							pos := b.Assume()
							N, tail := b.ObtainAs[Nat](
								"the distances tending to zero, past some index N they are below ε",
								"∃N:num. ∀n:num. N ≤ n ⇒ |d(x(n), l) - &0| < ε",
								By(toZero.At(eps), pos))
							b.Take(N)
							n := b.FixAs[Nat]()
							past := b.Assume()
							b.Show(
								"so d(x(n), l) < ε",
								ByArith(tail.At(n), past))
						})),
				))
			a.Take(x)
			a.Show(
				"x is a sequence of points of s converging to l",
				By(terms[0], converges))
		}),
})}

// ClosedIffSequential — a subset of M is closed exactly when it lies in
// M and holds the limit of every convergent sequence of its points.
//
// A closed set gives each point of M outside it a ball missing it
// (metric_space.ClosedIff). Were a sequence of points of c to converge to
// a limit l outside c, a ball about l would miss c, and the tail of the
// sequence, which enters every ball about l, would put a point of c in
// it. Conversely, a point of M outside c all of whose balls met c would be
// the limit of a sequence of points of c (ApproachingSequence), and c
// would hold it; so each point of M outside c has a ball missing c.
var ClosedIffSequential = closedIffSequentialThm{family.Add(registry.ProofEntry{
	Name: "ClosedIffSequential",
	Key:  "prop_a7f2ac65e5194861",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀c:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
		},
		Conclusion: "closed_in(metric_topology(M, d), c) ⇔ " +
			"c ⊆ M ∧ (∀x:(num → A). ∀l:A. (∀n:num. x(n) ∈ c) ∧ metric_converges_to(M, d, x, l) ⇒ l ∈ c)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			c *Expr[Set[A]],
		) {
			a.Iff()

			a.Forward(
				"a limit outside c has a ball about it missing c, and the tail of the sequence enters that ball",
				func(b *Argument, closed Fact) {
					missing := b.Conjuncts(
						b.Have(
							"c is closed: it lies in M, and a point of M outside it has a ball missing it",
							"c ⊆ M ∧ ∀p:A. p ∈ M ∧ p ∉ c ⇒ ∃r:real. &0 < r ∧ ball(M, d, p, r) ∩ c = ∅",
							By(closed, metric_space.ClosedIff)),
						"c lies in M",
						"a point of M outside c has a ball missing c")
					b.Do(SplitConj(
						Case(
							"c lies in M",
							By(missing[0])),
						Case(
							"c holds the limit of every convergent sequence of its points",
							Derive(func(e *Argument) {
								e.FixAs[Fun[Nat, A]]() // the sequence x, spelled by the statement in the claims
								l := e.FixAs[A]()
								given := e.Conjuncts(
									e.Assume(),
									"every term is a point of c",
									"x converges to l")
								near := e.Conjuncts(
									e.Unfolded(given[1], MetricConvergesToDef),
									"l is a point of M",
									"every term is a point of M",
									"every positive distance about l holds a tail of x")
								lM := e.MemberOf[on.M](l, near[0])
								outside := e.SupposeNot()
								r, radius := e.ObtainAs[Real](
									"then some ball about l, of radius r, misses c",
									"∃r:real. &0 < r ∧ ball(M, d, l, r) ∩ c = ∅",
									By(missing[1].At(l), near[0], outside))
								ball := e.Conjuncts(
									radius,
									"r is positive",
									"the ball of radius r about l misses c")
								N, tail := e.ObtainAs[Nat](
									"x converges to l: past some index N its terms are within r of l",
									"∃N:num. ∀n:num. N ≤ n ⇒ d(x(n), l) < r",
									By(near[2].At(r), ball[0]))
								xN := e.MemberOf[on.M](e.TermAs[A]("x(N)"), near[1].At(N))
								inBall := e.Have(
									"x(N) itself lies within r of l",
									"d(l, x(N)) < r",
									ByArith(tail.At(N), metric_space.DistSym.Read(metric).At(lM, xN)))
								e.Show(
									"so x(N), a point of M and of c, lies in the ball that misses c",
									BySets(e.Unfolded(ball[1], metric_space.BallDef), inBall, near[1].At(N), given[0].At(N)))
							})),
					))
				})

			a.Backward(
				"a point of M outside c all of whose balls met c would be the limit of a sequence of points of c",
				func(b *Argument, sequential Fact) {
					keeps := b.Conjuncts(
						sequential,
						"c lies in M",
						"c holds the limit of every convergent sequence of its points")
					// Closedness read by balls: each point of M outside c has
					// one missing c.
					b.Do(Simp(Fwd(metric_space.ClosedIff)))
					b.Do(SplitConj(
						Case(
							"c lies in M",
							By(keeps[0])),
						Case(
							"a point of M outside c has a ball missing c",
							Derive(func(e *Argument) {
								p := e.FixAs[A]("p")
								point := e.Conjuncts(
									e.Assume(),
									"p is a point of M",
									"p lies outside c")
								pm := e.MemberOf[on.M](p, point[0])
								noBall := e.SupposeNot()
								everyBall := e.Have(
									"then every ball about p meets c",
									"∀r:real. &0 < r ⇒ ball(M, d, p, r) ∩ c ≠ ∅",
									By(Normalized, noBall))
								y, sequence := e.ObtainAs[Fun[Nat, A]](
									"so some sequence y of points of c converges to p",
									"∃y:(num → A). (∀n:num. y(n) ∈ c) ∧ metric_converges_to(M, d, y, p)",
									By(everyBall, ApproachingSequence.Read(metric).At(c, pm)))
								e.Show(
									"c holds the limit p of y, though p lies outside c",
									By(Normalized, point[1], sequence, keeps[1].At(y, p)))
							})),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Complete subspaces
// ---------------------------------------------------------------------------

// ClosedComplete — a closed subset of a complete space is complete.
//
// A Cauchy sequence of points of s is a Cauchy sequence of points of M,
// s lying in M and the distance being the same; M being complete, it
// converges to a point l of M. The closed s keeps the limits of its
// sequences (ClosedIffSequential), so l lies in s, and the sequence
// converges to l in s.
var ClosedComplete = closedCompleteThm{family.Add(registry.ProofEntry{
	Name: "ClosedComplete",
	Key:  "prop_7eeb116eb7aa6671",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀s:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_complete(M, d)",
			"closed_in(metric_topology(M, d), s)",
		},
		Conclusion: "metric_complete(s, d)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			complete Fact,
			s *Expr[Set[A]],
			closed Fact,
		) {
			keeps := a.Conjuncts(
				a.Have(
					"s is closed: it lies in M and keeps the limits of its sequences",
					"s ⊆ M ∧ ∀x:(num → A). ∀l:A. (∀n:num. x(n) ∈ s) ∧ metric_converges_to(M, d, x, l) ⇒ l ∈ s",
					By(closed, metric, ClosedIffSequential.At(M, d, s))),
				"s lies in M",
				"s keeps the limits of its sequences")
			// M's completeness read as its sentence, a Cauchy sequence spelled
			// out: its terms in M, and its pairs of late terms close.
			converge := a.Unfolded(a.Unfolded(complete, MetricCompleteDef), MetricCauchyDef)

			// The goal read as its sentence: every Cauchy sequence of points of
			// s converges to a point of s.
			a.Do(Unfold(MetricCompleteDef))
			x := a.FixAs[Fun[Nat, A]]()
			cauchy := a.Conjuncts(
				a.Unfolded(a.Assume(), MetricCauchyDef),
				"every term is a point of s",
				"every positive distance holds any two terms past some index")
			inM := a.Have(
				"its terms are points of M, s lying in M",
				"∀n:num. x(n) ∈ M",
				BySets(cauchy[0], keeps[0]))
			l, limit := a.ObtainAs[A](
				"so x is a Cauchy sequence of M, and M being complete it converges to some l",
				"∃l:A. metric_converges_to(M, d, x, l)",
				By(converge.At(x), inM, cauchy[1]))
			inS := a.Have(
				"s keeps the limit of x, so l lies in s",
				"l ∈ s",
				By(keeps[1].At(x, l), cauchy[0], limit))
			near := a.Conjuncts(
				a.Unfolded(limit, MetricConvergesToDef),
				"l is a point of M",
				"every term is a point of M",
				"every positive distance about l holds a tail of x")
			a.Take(l)
			a.Show(
				"so x converges to l in s, its terms and l being points of s",
				Unfold(MetricConvergesToDef),
				By(inS, cauchy[0], near[2]))
		}),
})}

// CompleteClosed — a complete subset of a metric space is closed in it.
//
// Let a sequence of points of s converge in M to l. Being convergent it is
// Cauchy (ConvergentImpCauchy), and the Cauchy condition asks nothing of
// the carrier beyond its terms, so it is a Cauchy sequence of s; s being
// complete, it converges in s to some m, and so in M as well. Limits are
// unique (LimitUnique), so l is m, a point of s; s keeps the limits of its
// sequences, which is closedness (ClosedIffSequential).
var CompleteClosed = completeClosedThm{family.Add(registry.ProofEntry{
	Name: "CompleteClosed",
	Key:  "prop_ae1854e8a4879582",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀s:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"s ⊆ M",
			"metric_complete(s, d)",
		},
		Conclusion: "closed_in(metric_topology(M, d), s)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			s *Expr[Set[A]],
			within, complete Fact,
		) {
			// s's completeness read as its sentence, a Cauchy sequence spelled
			// out: its terms in s, and its pairs of late terms close.
			converge := a.Unfolded(a.Unfolded(complete, MetricCompleteDef), MetricCauchyDef)

			// Closedness read by sequences.
			a.Do(Simp(Fwd(ClosedIffSequential)))
			a.Do(SplitConj(
				Case(
					"s lies in M",
					By(within)),
				Case(
					"s holds the limit in M of every sequence of its points",
					Derive(func(b *Argument) {
						x := b.FixAs[Fun[Nat, A]]()
						l := b.FixAs[A]()
						given := b.Conjuncts(
							b.Assume(),
							"every term is a point of s",
							"x converges to l in M")
						cauchy := b.Conjuncts(
							b.Unfolded(GroupPremises(metric, given[1], ConvergentImpCauchy.At(M, d, x, l)), MetricCauchyDef),
							"every term is a point of M",
							"every positive distance holds any two terms past some index")
						m, limit := b.ObtainAs[A](
							"so x is a Cauchy sequence of s as well, and s being complete it converges in s to some m",
							"∃m:A. metric_converges_to(s, d, x, m)",
							By(converge.At(x), given[0], cauchy[1]))
						near := b.Conjuncts(
							b.Unfolded(limit, MetricConvergesToDef),
							"m is a point of s",
							"every term is a point of s",
							"every positive distance about m holds a tail of x")
						inM := b.Have(
							"m is a point of M, s lying in M",
							"m ∈ M",
							BySets(near[0], within))
						limitM := b.Have(
							"so x converges to m in M too",
							"metric_converges_to(M, d, x, m)",
							By(inM, cauchy[0], near[2], MetricConvergesToDef))
						b.Show(
							"limits are unique, so l is m, a point of s",
							By(Normalized, metric, given[1], limitM, near[0], LimitUnique.At(M, d, x, l, m)))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Closure and continuity by sequences, and bounded sequences
// ---------------------------------------------------------------------------

// ClosureIffSequential — the closure of a set is the set of limits of
// its sequences.
//
// Read pointwise (topological_space.ClosurePointwise at the metric
// topology), the closure holds the points of M every open set about which
// meets s. Every ball about such a point is open and holds it, so every
// ball meets s, and ApproachingSequence gives a sequence of points of s
// converging to it. Conversely, an open set about the limit of a sequence
// of points of s holds a ball about it, and the tail of the sequence
// enters that ball, so the open set meets s.
var ClosureIffSequential = closureIffSequentialThm{family.Add(registry.ProofEntry{
	Name: "ClosureIffSequential",
	Key:  "prop_13a16dc435c2e5d2",
	Build: metric_space.MetricSpace.Law(Statement{
		Binders: "∀s:set(A). ∀l:A.",
		Hypotheses: []string{
			"s ⊆ M",
		},
		Conclusion: "l ∈ closure(metric_topology(M, d), s) ⇔ " +
			"∃x:(num → A). (∀n:num. x(n) ∈ s) ∧ metric_converges_to(x, l)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			s *Expr[Set[A]],
			l *Expr[A],
			within Fact,
		) {
			topology := a.Have(
				"the open sets of the distance form a topology",
				"is_topology(metric_topology(M, d))",
				By(metric_space.MetricTopology.At(M, d)))
			pointwise := a.Have(
				"read pointwise, the closure holds the points of M every open set about which meets s",
				"l ∈ closure(metric_topology(M, d), s) ⇔ "+
					"l ∈ M ∧ ∀u:set(A). u ∈ metric_topology(M, d) ∧ l ∈ u ⇒ u ∩ s ≠ ∅",
				By(
					within,
					topological_space.ClosurePointwise.Read(topology).At(s, l),
					metric_space.MetricTopologySpace.At(M, d)))
			a.Do(pointwise.Rw())
			a.Iff()

			a.Forward(
				"every ball about a point of the closure is open and "+
					"holds it, so it meets s, and points of s close in on it",
				func(b *Argument, near Fact) {
					about := b.Conjuncts(
						near,
						"l is a point of M",
						"every open set about l meets s")
					lM := b.MemberOf[on.M](l, about[0])
					everyBall := b.Have(
						"every ball about l meets s",
						"∀r:real. &0 < r ⇒ ball(l, r) ∩ s ≠ ∅",
						Derive(func(c *Argument) {
							r := c.FixAs[Real]()
							positive := c.Assume()
							c.Show(
								"the ball of radius r about l is open and holds l",
								By(
									about[1].At(c.TermAs[Set[A]]("ball(l, r)")),
									positive,
									metric_space.BallOpen.Read(metric).At(lM, r),
									metric_space.CentreInBall.Read(metric).At(lM, r)))
						}))
					b.Show(
						"so a sequence of points of s converges to l",
						By(everyBall, ApproachingSequence.Read(metric).At(s, lM)))
				})

			a.Backward(
				"an open set about the limit holds a ball about it, which the tail of the sequence enters",
				func(b *Argument, limit Fact) {
					_, sequence := b.UnpackAs[Fun[Nat, A]](limit)
					given := b.Conjuncts(
						sequence,
						"every term is a point of s",
						"x converges to l")
					near := b.Conjuncts(
						b.Unfolded(given[1], MetricConvergesToDef),
						"l is a point of M",
						"every term is a point of M",
						"every positive distance about l holds a tail of x")
					lM := b.MemberOf[on.M](l, near[0])
					b.Do(SplitConj(
						Case(
							"l is a point of M",
							By(near[0])),
						Case(
							"every open set about l meets s",
							Derive(func(c *Argument) {
								u := c.FixAs[Set[A]]("u")
								about := c.Conjuncts(
									c.Assume(),
									"u is open",
									"l lies in u")
								r, radius := c.ObtainAs[Real](
									"u being open, a ball about l, of radius r, lies in u",
									"∃r:real. &0 < r ∧ ball(l, r) ⊆ u",
									By(about[0], about[1], metric_space.OpenIff.At(M, d, u)))
								ball := c.Conjuncts(
									radius,
									"r is positive",
									"the ball of radius r about l lies in u")
								N, tail := c.ObtainAs[Nat](
									"x converges to l: past some index N its terms are within r of l",
									"∃N:num. ∀n:num. N ≤ n ⇒ d(x(n), l) < r",
									By(near[2].At(r), ball[0]))
								xN := c.MemberOf[on.M](c.TermAs[A]("x(N)"), near[1].At(N))
								inBall := c.Have(
									"x(N) itself lies within r of l",
									"d(l, x(N)) < r",
									ByArith(tail.At(N), metric_space.DistSym.Read(metric).At(lM, xN)))
								c.Show(
									"so x(N), a point of s, lies in the ball inside u",
									BySets(c.Unfolded(ball[1], metric_space.BallDef), inBall, near[1].At(N), given[0].At(N)))
							})),
					))
				})
		}),
})}

// ContinuousIffSequential — a map between metric spaces is continuous
// exactly when it carries convergent sequences to convergent sequences.
//
// Continuity for the metric topologies is continuity in the ε-δ sense
// (metric_space.ContinuousMapIff). Forward: the δ that ε hands over at
// the limit l is met by the terms past some index, and their values are
// then within ε of f(l). Backward: were the ε-δ condition to fail at a
// point p for some ε, every ball about p would hold a point whose value
// is not within ε of f(p); a sequence of such points converges to p
// (ApproachingSequence), so their values converge to f(p), and a value
// past some index lies within ε of f(p) after all.
var ContinuousIffSequential = continuousIffSequentialThm{family.Add(registry.ProofEntry{
	Name: "ContinuousIffSequential",
	Key:  "prop_55644b74dce7a06f",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real). ∀f:(A → B).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_space(N, e)",
		},
		Conclusion: "continuous_map(metric_topology(M, d), metric_topology(N, e), f) ⇔ " +
			"(∀x:A. x ∈ M ⇒ f(x) ∈ N) ∧ " +
			"(∀x:(num → A). ∀l:A. metric_converges_to(M, d, x, l) ⇒ metric_converges_to(N, e, f ∘ x, f(l)))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			target metric_space.MetricSpaceFact[on.N],
			f *Arrow[A, B],
		) {
			// Continuity read in the ε-δ sense.
			a.Do(Simp(Fwd(metric_space.ContinuousMapIff)))
			a.Iff()

			a.Forward(
				"past the index at which the terms are within δ of "+
					"the limit, their values are within ε of its value",
				func(b *Argument, continuous Fact) {
					parts := b.Conjuncts(
						continuous,
						"f carries M into N",
						"f is continuous at every point of M")
					b.Do(SplitConj(
						Case(
							"f carries M into N",
							By(parts[0])),
						Case(
							"f carries a sequence converging to l to one converging to f(l)",
							Derive(func(c *Argument) {
								c.FixAs[Fun[Nat, A]]() // the sequence x, spelled by the statement in the claims
								l := c.FixAs[A]()
								near := c.Conjuncts(
									c.Unfolded(c.Assume(), MetricConvergesToDef),
									"l is a point of M",
									"every term is a point of M",
									"every positive distance about l holds a tail of x")
								lM := c.MemberOf[on.M](l, near[0])
								fl := c.MemberOf[on.N](f.Apply(l), GroupPremises(near[0], parts[0].At(l)))

								c.Do(Unfold(MetricConvergesToDef), Unfold(functions.ComposeApply))
								c.Do(SplitConjAll(
									Case(
										"f(l) is a point of N",
										By(fl)),
									Case(
										"every value f(x(n)) is a point of N",
										By(parts[0], near[1])),
									Case(
										"past some index every value is within ε of f(l)",
										Derive(func(h *Argument) {
											eps := h.FixAs[Real]()
											pos := h.Assume()
											δ, ball := h.ObtainAs[Real](
												"f is continuous at l: some δ sends the points of M within δ of l within ε of f(l)",
												"∃δ:real. &0 < δ ∧ ∀y:A. y ∈ M ∧ d(l, y) < δ ⇒ e(f(l), f(y)) < ε",
												By(parts[1].At(l, eps), near[0], pos))
											within := h.Conjuncts(
												ball,
												"δ is positive",
												"f sends the points of M within δ of l within ε of f(l)")
											K, tail := h.ObtainAs[Nat](
												"x converges to l: past some index K its terms are within δ of l",
												"∃K:num. ∀n:num. K ≤ n ⇒ d(x(n), l) < δ",
												By(near[2].At(δ), within[0]))
											h.Take(K)
											n := h.FixAs[Nat]()
											past := h.Assume()
											term := h.TermAs[A]("x(n)")
											xn := h.MemberOf[on.M](term, near[1].At(n))
											fxn := h.MemberOf[on.N](f.Apply(term), GroupPremises(near[1].At(n), parts[0].At(term)))
											closeBy := h.Have(
												"x(n) lies within δ of l",
												"d(l, x(n)) < δ",
												ByArith(tail.At(n), past, metric_space.DistSym.Read(metric).At(lM, xn)))
											h.Show(
												"so f(x(n)) lies within ε of f(l)",
												ByArith(within[1].At(term), xn, closeBy, metric_space.DistSym.Read(target).At(fxn, fl)))
										})),
								))
							})),
					))
				})

			a.Backward(
				"a point where the ε-δ condition failed would be the "+
					"limit of points whose values stay ε away from its value",
				func(b *Argument, sequential Fact) {
					parts := b.Conjuncts(
						sequential,
						"f carries M into N",
						"f carries convergent sequences to convergent sequences")
					b.Do(SplitConj(
						Case(
							"f carries M into N",
							By(parts[0])),
						Case(
							"f is continuous at every point of M",
							Derive(func(c *Argument) {
								p := c.FixAs[A]("p")
								eps := c.FixAs[Real]()
								point := c.Conjuncts(
									c.Assume(),
									"p is a point of M",
									"ε is positive")
								pm := c.MemberOf[on.M](p, point[0])
								noDelta := c.SupposeNot()
								everyBall := c.Have(
									"then every ball about p holds a point whose value is not within ε of f(p)",
									"∀r:real. &0 < r ⇒ ball(M, d, p, r) ∩ {y:A | ¬(e(f(p), f(y)) < ε)} ≠ ∅",
									BySets(noDelta, metric_space.BallDef))
								y, sequence := c.ObtainAs[Fun[Nat, A]](
									"so a sequence y of such points converges to p",
									"∃y:(num → A). (∀n:num. y(n) ∈ {z:A | ¬(e(f(p), f(z)) < ε)}) ∧ metric_converges_to(M, d, y, p)",
									By(
										everyBall,
										ApproachingSequence.Read(metric).At(c.TermAs[Set[A]]("{z:A | ¬(e(f(p), f(z)) < ε)}"), pm)))
								given := c.Conjuncts(
									sequence,
									"no value f(y(n)) is within ε of f(p)",
									"y converges to p")
								images := c.Conjuncts(
									c.Unfolded(
										c.Unfolded(GroupPremises(given[1], parts[1].At(y, p)), MetricConvergesToDef),
										functions.ComposeApply),
									"f(p) is a point of N",
									"every value f(y(n)) is a point of N",
									"every positive distance about f(p) holds a tail of the values")
								K, tail := c.ObtainAs[Nat](
									"so the values converge to f(p): past some index K they are within ε of it",
									"∃K:num. ∀n:num. K ≤ n ⇒ e(f(y(n)), f(p)) < ε",
									By(images[2].At(eps), point[1]))
								fyK := c.MemberOf[on.N](c.TermAs[B]("f(y(K))"), images[1].At(K))
								fp := c.MemberOf[on.N](f.Apply(p), images[0])
								c.Show(
									"yet f(y(K)) is not within ε of f(p)",
									ByArith(
										tail.At(K),
										given[0].At(K),
										nat_order.LessEqRefl.At(K),
										metric_space.DistSym.Read(target).At(fyK, fp)))
							})),
					))
				})
		}),
})}

// CauchyBounded — the terms of a Cauchy sequence form a bounded set.
//
// The distances of the terms from x(0) form a Cauchy sequence of reals:
// two of them differ by at most the distance between their terms, by the
// triangle inequality taken both ways. A Cauchy sequence of reals is
// bounded, so some B bounds every d(x(n), x(0)), and any two terms are
// within 2B of each other, through x(0).
var CauchyBounded = cauchyBoundedThm{family.Add(registry.ProofEntry{
	Name: "CauchyBounded",
	Key:  "prop_a4a7af1d88eaa413",
	Build: metric_space.MetricSpace.Law(Statement{
		Binders: "∀x:(num → A).",
		Hypotheses: []string{
			"metric_cauchy(x)",
		},
		Conclusion: "metric_bounded(image(x, 𝕌))",
	},
		func(a *Argument, metric metric_space.MetricSpaceFact[on.M], x *Arrow[Nat, A], cauchy Fact) {
			together := a.Conjuncts(
				a.Unfolded(cauchy, MetricCauchyDef),
				"every term is a point of M",
				"every positive distance holds any two terms past some index")
			zero := a.TermAs[Nat]("0")
			x0 := a.MemberOf[on.M](x.Apply(zero), together[0].At(zero))

			distances := a.Have(
				"the distances of the terms from x(0) form a Cauchy sequence of reals",
				"real_cauchy(λn:num. d(x(n), x(0)))",
				Unfold(real_sequences.RealCauchyDef),
				Derive(func(b *Argument) {
					eps := b.FixAs[Real]()
					pos := b.Assume()
					N, pairs := b.ObtainAs[Nat](
						"x being Cauchy, past some index N any two terms are within ε of each other",
						"∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ d(x(m), x(n)) < ε",
						By(together[1].At(eps), pos))
					b.Take(N)
					m := b.FixAs[Nat]()
					n := b.FixAs[Nat]()
					past := b.Assume()
					xm := b.MemberOf[on.M](x.Apply(m), together[0].At(m))
					xn := b.MemberOf[on.M](x.Apply(n), together[0].At(n))
					b.Show(
						"their distances from x(0) differ by at most d(x(m), x(n)), by the triangle inequality both ways",
						ByArith(
							pairs.At(m, n),
							past,
							metric_space.DistTriangle.Read(metric).At(xm, xn, x0),
							metric_space.DistTriangle.Read(metric).At(xn, xm, x0),
							metric_space.DistSym.Read(metric).At(xm, xn)))
				}))
			_, bound := a.ObtainAs[Real](
				"a Cauchy sequence of reals is bounded: some B bounds every distance d(x(n), x(0))",
				"∃B:real. ∀n:num. |d(x(n), x(0))| ≤ B",
				By(real_sequences.CauchyBounded.At(a.TermAs[Fun[Nat, Real]]("λn:num. d(x(n), x(0))")), distances))
			spread := a.Have(
				"so any two terms are within 2B of each other, through x(0)",
				"∀i j:num. d(x(i), x(j)) ≤ &2 * B",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					j := b.FixAs[Nat]()
					xi := b.MemberOf[on.M](x.Apply(i), together[0].At(i))
					xj := b.MemberOf[on.M](x.Apply(j), together[0].At(j))
					b.Show(
						"x(i) and x(j) are each within B of x(0)",
						ByArith(
							bound.At(i),
							bound.At(j),
							metric_space.DistTriangle.Read(metric).At(xi, x0, xj),
							metric_space.DistSym.Read(metric).At(x0, xj)))
				}))

			// The image is bounded when it lies in M and some bound holds
			// between any two of its points.
			a.Do(Unfold(metric_space.MetricBoundedDef))
			a.Do(SplitConj(
				Case(
					"the terms are points of M",
					By(together[0], set_image.ImageSubsetIff)),
				Case(
					"2B bounds the distance between any two points of the image",
					Derive(func(b *Argument) {
						b.Take(b.TermAs[Real]("&2 * B"))
						b.Show(
							"two points of the image are two terms",
							By(
								spread,
								Where(
									set_image.ForallInImagePair, "P", b.TermAs[Fun2[A, A, Bool]]("λp:A. λq:A. d(p, q) ≤ &2 * B"))))
					})),
			))
		}),
})}
