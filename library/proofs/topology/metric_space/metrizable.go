// metrizable.go — metrizable spaces: a topology that is the topology of
// some distance. A subspace of one is one, the product of two is one, and
// a discrete space is one.

package metric_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Metrizable spaces
// ---------------------------------------------------------------------------

// MetrizableSubtopology — a subspace of a metrizable space is
// metrizable. With T the topology of a distance d on M, cutting to s is
// cutting to M ∩ s, the part of s in the space of T; there the subspace
// topology is the topology of d on M ∩ s, itself a metric space.
var MetrizableSubtopology = metrizableSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "MetrizableSubtopology",
	Key:  "prop_3abcdee1914f2a09",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"metrizable_space(T)",
		},
		Conclusion: "metrizable_space(subtopology(T, s))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], metrizable Fact) {
			M, d, given := a.Unpack2As[Set[A], Fun2[A, A, Real]](
				a.Unfolded(metrizable, MetrizableSpaceDef), "M", "d")
			parts := a.Conjuncts(
				given,
				"d is a distance on M",
				"T is its topology")
			cut := a.Have(
				"cutting to s is cutting to the part of s in M, the space of T",
				"subtopology(T, s) = subtopology(T, M ∩ s)",
				By(
					Normalized,
					parts[1],
					topological_space.SubtopologySelf.At(T),
					topological_space.SubtopologySubtopology.At(T, a.TermAs[Set[A]]("⋃T"), s),
					MetricTopologySpace.At(M, d)))
			trace := a.TermAs[Set[A]]("M ∩ s")
			a.Do(Simp(Fwd(MetrizableSpaceDef)))
			a.Take(trace)
			a.Take(d)
			a.Do(SplitConj(
				Case(
					"d is a distance on M ∩ s, a part of M",
					BySets(SubMetricSpace.Read(parts[0]).At(trace))),
				Case(
					"and its topology there is the subspace topology",
					BySets(parts[1], cut, MetricTopologySubspace.Read(parts[0]).At(trace))),
			))
		}),
})}

// MetrizableProduct — the product of two metrizable spaces is
// metrizable: with T the topology of d on M and S that of e on N, the
// larger of the two distances is a distance on the product of M and N
// whose topology is the product topology.
var MetrizableProduct = metrizableProductThm{family.Add(registry.ProofEntry{
	Name: "MetrizableProduct",
	Key:  "prop_746379736352538a",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"metrizable_space(T)",
			"metrizable_space(S)",
		},
		Conclusion: "metrizable_space(product_topology(T, S))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], metrizableT, metrizableS Fact) {
			M, d, onT := a.Unpack2As[Set[A], Fun2[A, A, Real]](
				a.Unfolded(metrizableT, MetrizableSpaceDef), "M", "d")
			N, e, onS := a.Unpack2As[Set[B], Fun2[B, B, Real]](
				a.Unfolded(metrizableS, MetrizableSpaceDef), "N", "e")
			tParts := a.Conjuncts(
				onT,
				"d is a distance on M",
				"T is its topology")
			sParts := a.Conjuncts(
				onS,
				"e is a distance on N",
				"S is its topology")
			a.Do(Simp(Fwd(MetrizableSpaceDef)))
			a.Take(a.TermAs[Set[Prod[A, B]]]("set_cross(M, N)"))
			a.Take(a.TermAs[Fun2[Prod[A, B], Prod[A, B], Real]]("product_metric(d, e)"))
			a.Do(SplitConj(
				Case(
					"the larger of the two distances is a distance on the product",
					By(ProductMetric.At(M, d, N, e), tParts[0], sParts[0])),
				Case(
					"whose topology is the product of the two, which are T and S",
					By(Normalized, ProductMetricTopology.At(M, d, N, e), tParts[0], sParts[0], tParts[1], sParts[1])),
			))
		}),
})}

// DiscreteMetrizable — a discrete space is metrizable, by the distance δ
// on X that is 0 between a point and itself and 1 between two others. Its
// axioms hold case by case on which of the points coincide. A point within
// 1 of y is y itself, so the ball of radius 1 about a point of a subset t
// of X lies in t: every subset of X is open, and an open set lies in X.
var DiscreteMetrizable = discreteMetrizableThm{family.Add(registry.ProofEntry{
	Name: "DiscreteMetrizable",
	Key:  "prop_5c8124a689a5739b",
	Build: family.Theorem("∀X:set(A). metrizable_space({t:set(A) | t ⊆ X})",
		func(a *Argument, X *Expr[Set[A]]) {
			delta, isDelta := a.LetAs[Fun2[A, A, Real]]("δ", "λx:A. λy:A. COND(x = y, &0, &1)")
			pointwise := a.Have(
				"δ is 0 between a point and itself and 1 between two others",
				"∀x y:A. δ(x, y) = COND(x = y, &0, &1)",
				By(Normalized, isDelta))
			near := a.Have(
				"a point within 1 of x is x itself",
				"∀x y:A. δ(x, y) < &1 ⇒ x = y",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					within := b.Assume()
					apart := b.SupposeNot()
					b.Show(
						"two distinct points are 1 apart",
						ByArith(apart, pointwise.At(x, y), within))
				}))
			a.Do(Simp(Fwd(MetrizableSpaceDef)))
			a.Take(X)
			a.Take(delta)
			a.Do(SplitConj(
				Case(
					"δ is a distance on X, each axiom holding whichever of its points coincide",
					Simp(Fwd(MetricSpace)),
					SplitConjAll(
						Case(
							"δ vanishes exactly between a point and itself",
							Derive(func(b *Argument) {
								b.FixAs[A]("x")
								b.FixAs[A]("y")
								b.Assume()
								b.Show(
									"1 is not 0",
									Simp(Fwd(pointwise)),
									CondRewrite(),
									ByArith())
							})),
						Case(
							"δ is symmetric, x being y exactly when y is x",
							Derive(func(b *Argument) {
								b.FixAs[A]("x")
								b.FixAs[A]("y")
								b.Assume()
								b.Show(
									"both sides are 0 or both are 1",
									Simp(Fwd(pointwise)),
									CondRewrite(),
									ByArith())
							})),
						Case(
							"δ obeys the triangle inequality: when x and z differ, y differs from one of them",
							Derive(func(b *Argument) {
								b.FixAs[A]("x")
								b.FixAs[A]("y")
								b.FixAs[A]("z")
								b.Assume()
								b.Show(
									"so the detour is at least 1 whenever the direct way is",
									Simp(Fwd(pointwise)),
									CondRewrite(),
									ByArith())
							})),
					)),
				Case(
					"the open sets of δ are the subsets of X",
					Simp(Fwd(set_basic.Extension.Inst[Set[A]]()), Fwd(OpenIff)),
					Derive(func(b *Argument) {
						b.FixAs[Set[A]]("t")
						b.Iff()
						b.Forward(
							"a subset t of X holds the ball of radius 1 about each of its points, that point alone",
							func(c *Argument, subset Fact) {
								c.Do(SplitConj(
									Case(
										"t lies in X",
										By(subset)),
									Case(
										"the ball of radius 1 about a point y of t lies in t",
										Derive(func(e *Argument) {
											e.FixAs[A]("y")
											inT := e.Assume()
											e.Take(e.TermAs[Real]("&1"))
											e.Do(SplitConj(
												Case(
													"the radius is positive",
													ByArith()),
												Case(
													"and a point of the ball is y itself, a point of t",
													Unfold(BallDef),
													BySets(near, inT)),
											))
										})),
								))
							})
						b.Backward(
							"an open set of δ lies in X",
							func(c *Argument, open Fact) {
								c.Show(
									"so it is a subset of X",
									By(open))
							})
					})),
			))
		}),
})}
