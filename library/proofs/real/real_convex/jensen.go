// jensen.go — convex combinations of finitely many points: an interval
// holds them, and a convex function lies below its values averaged at
// them (Jensen's inequality).

package real_convex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ConvexCombinationInsert — for weights totalling 1 over u with a fresh
// j adjoined, nonnegative on u, the weights on u total 1 − w(j), and a
// combination of values y over the larger set is y(j) at weight w(j)
// beside the combination over u at the weights divided by 1 − w(j), at
// weight 1 − w(j). Adjoining j adds its term to each sum over u; and
// 1 − w(j) times a divided weight is the weight itself — when w(j) = 1,
// every weight on u is 0, a nonnegative weight in a zero total.
var ConvexCombinationInsert = convexCombinationInsertThm{family.Add(registry.ProofEntry{
	Name: "ConvexCombinationInsert",
	Key:  "prop_d769f3883cebc9e5",
	Build: family.Theorem(Statement{
		Binders: "∀u:set(A). ∀j:A. ∀w y:A → real.",
		Hypotheses: []string{
			"finite(u)",
			"j ∉ u",
			"∀i:A. i ∈ u ⇒ &0 ≤ w(i)",
			"Σ_{i∈insert(j, u)} w(i) = &1",
		},
		Conclusion: "Σ_{i∈u} w(i) = &1 - w(j) ∧ " +
			"Σ_{i∈insert(j, u)} w(i) * y(i) = " +
			"w(j) * y(j) + (&1 - w(j)) * Σ_{i∈u} real_inv(&1 - w(j)) * w(i) * y(i)",
	}, func(
		a *Argument,
		u *Expr[Set[A]],
		j *Expr[A],
		w, y *Arrow[A, Real],
		finiteU, fresh, nonneg, total Fact,
	) {
		peel := a.Have(
			"adjoining j adds its term to each sum over u",
			"Σ_{i∈insert(j, u)} w(i) = w(j) + Σ_{i∈u} w(i) ∧ "+
				"Σ_{i∈insert(j, u)} w(i) * y(i) = w(j) * y(j) + Σ_{i∈u} w(i) * y(i)",
			By(real_sum.Clauses, finiteU, fresh),
		)
		rest := a.Have(
			"so the weights on u total 1 − w(j)",
			"Σ_{i∈u} w(i) = &1 - w(j)",
			ByArith(peel, total))
		rescaled := a.Have(
			"1 − w(j) times a divided weight is the weight",
			"∀i:A. i ∈ u ⇒ (&1 - w(j)) * (real_inv(&1 - w(j)) * w(i) * y(i)) = w(i) * y(i)",
			Derive(func(b *Argument) {
				i := b.FixAs[A]("i")
				in := b.Assume()
				b.Cases(b.Term("w(j) = &1"))
				b.When(
					"all the weight sits at j, so w(i) is 0",
					func(c *Argument, one Fact) {
						none := c.Have(
							"the weights on u total 0",
							"Σ_{l∈u} w(l) = &0",
							ByArith(one, rest))
						zero := c.Have(
							"a nonnegative weight in a zero total is 0",
							"w(i) = &0",
							By(real_sum.NonnegEqZero.At(u, w, i), finiteU, nonneg, none, in),
						)
						c.Show(
							"both sides are 0",
							ByArith(zero))
					})
				b.Otherwise(
					"otherwise 1 − w(j) is not 0",
					func(c *Argument, notOne Fact) {
						c.Show(
							"and cancels against its reciprocal",
							ByArith(notOne))
					})
			}),
		)
		a.Show(
			"so 1 − w(j) times the divided combination over u is the combination over u",
			ByArith(
				peel,
				rest,
				rescaled,
				real_sum.ScalarLeft.At(
					a.TermAs[Real]("&1 - w(j)"),
					a.TermAs[Fun[A, Real]]("λi:A. real_inv(&1 - w(j)) * w(i) * y(i)"),
					u),
				real_sum.Congruence.At(
					u,
					a.TermAs[Fun[A, Real]]("λi:A. (&1 - w(j)) * (real_inv(&1 - w(j)) * w(i) * y(i))"),
					a.TermAs[Fun[A, Real]]("λi:A. w(i) * y(i)"))),
		)
	}),
})}

// ConvexCombinationIn — an interval holds every convex combination of
// finitely many of its points. By induction on the finite index set:
// adjoining a point j, the combination is x(j) at weight w(j) beside the
// combination m of the other points, at their weights divided by their
// total 1 − w(j), at weight 1 − w(j) (ConvexCombinationInsert). If
// w(j) = 1 that is x(j). Otherwise 1 − w(j) > 0, the divided weights form
// a convex combination over the smaller set, so the interval holds m, and
// with it every point between x(j) and m.
var ConvexCombinationIn = convexCombinationInThm{family.Add(registry.ProofEntry{
	Name: "ConvexCombinationIn",
	Key:  "prop_1bccc3ed5a3b1fe8",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀k:set(A). ∀w x:A → real.",
		Hypotheses: []string{
			"real_interval(s)",
			"finite(k)",
			"∀i:A. i ∈ k ⇒ &0 ≤ w(i) ∧ x(i) ∈ s",
			"Σ_{i∈k} w(i) = &1",
		},
		Conclusion: "Σ_{i∈k} w(i) * x(i) ∈ s",
	}, func(a *Argument, s *Expr[Set[Real]], k *Expr[Set[A]], interval, finiteK Fact) {
		a.Show(
			"by induction on the finite index set, adjoining one fresh point at a time",
			ByInduction(
				finite_set.FiniteInductFresh,
				finiteK,
				Case(
					"weights over the empty set total zero, never one",
					Simp(Fwd(real_sum.Clauses)),
					ByArith(),
				),
				Case(
					"adjoining a fresh point j to a finite set u",
					Derive(func(b *Argument) {
						j := b.FixAs[A]("j")
						u := b.FixAs[Set[A]]("u")
						step := b.Conjuncts(
							b.Assume(),
							"the claim holds over u",
							"j is not in u",
							"u is finite")
						w := b.FixAs[Fun[A, Real]]("w")
						x := b.FixAs[Fun[A, Real]]("x")
						given := b.Conjuncts(
							b.Assume(),
							"the weights are nonnegative at points of s",
							"and total one")
						weights := b.Have(
							"the weights on u are nonnegative",
							"∀i:A. i ∈ u ⇒ &0 ≤ w(i)",
							BySets(given[0]))
						points := b.Have(
							"and their points lie in s",
							"∀i:A. i ∈ u ⇒ x(i) ∈ s",
							BySets(given[0]))
						atJ := b.Have(
							"so does j, at a nonnegative weight",
							"&0 ≤ w(j) ∧ x(j) ∈ s",
							BySets(given[0]))
						split := b.Conjuncts(
							GroupPremises(step[2], step[1], weights, given[1], ConvexCombinationInsert.At(u, j, w, x)),
							"the weights on u total 1 − w(j)",
							"the combination is x(j) at weight w(j) beside m at weight 1 − w(j)")
						m, mDef := b.LetAs[Real]("m", "Σ_{i∈u} real_inv(&1 - w(j)) * w(i) * x(i)")
						notOne := b.Unless(
							b.Term("w(j) = &1"),
							"all the weight sits at j, so the combination is x(j)",
							Given(func(c *Argument, one Fact) {
								atX := c.Have(
									"the combination is 1·x(j) + 0·m",
									"Σ_{i∈insert(j, u)} w(i) * x(i) = x(j)",
									ByArith(split[1], one))
								c.Show(
									"which lies in s",
									atX.Rw(),
									By(atJ))
							}))
						positive := b.Have(
							"1 − w(j), a total of nonnegative weights, is not 0, so it is positive",
							"&0 < &1 - w(j)",
							ByArith(real_sum.Nonneg.At(u, w), weights, split[0], notOne),
						)
						scaled := b.Have(
							"the weights divided by 1 − w(j) are nonnegative at points of s",
							"∀l:A. l ∈ u ⇒ &0 ≤ real_inv(&1 - w(j)) * w(l) ∧ x(l) ∈ s",
							b.ForEach(func(l *Expr[A]) Action {
								return ByArith(weights.At(l), points.At(l), positive)
							}),
						)
						unit := b.Have(
							"and total one",
							"Σ_{l∈u} real_inv(&1 - w(j)) * w(l) = &1",
							ByArith(real_sum.ScalarLeft.At(b.TermAs[Real]("real_inv(&1 - w(j))"), w, u), split[0], positive),
						)
						inS := b.Have(
							"so s holds m, their combination, by the claim over u",
							"m ∈ s",
							By(step[0].At(b.TermAs[Fun[A, Real]]("λl:A. real_inv(&1 - w(j)) * w(l)"), x), scaled, unit, mDef),
						)
						b.Show(
							"and every point between x(j) and m",
							split[1].Rw(),
							ByArith(
								real_topology.IntervalSegment.At(s, b.TermAs[Real]("x(j)"), m, b.TermAs[Real]("w(j)")),
								interval,
								atJ,
								inS,
								positive),
						)
					}),
				),
			),
		)
	}),
})}

// Jensen — Jensen's inequality: a function convex on an interval, at a
// convex combination of finitely many points of it, is at most the same
// combination of its values. By induction on the finite index set, as
// for ConvexCombinationIn: adjoining a point j, the combination is x(j)
// at weight w(j) beside the combination m of the other points, at their
// weights divided by 1 − w(j), at weight 1 − w(j), and the combination of
// values splits the same way (ConvexCombinationInsert). If w(j) = 1 both
// sides are f(x(j)). Otherwise m lies in the interval with f(m) at most
// the divided combination of values there, and convexity between x(j)
// and m at weight w(j) finishes.
var Jensen = jensenThm{family.Add(registry.ProofEntry{
	Name: "Jensen",
	Key:  "prop_32df06cdebf92e55",
	Build: family.Theorem(Statement{
		Binders: "∀f:real → real. ∀s:set(real). ∀k:set(A). ∀w x:A → real.",
		Hypotheses: []string{
			"real_convex_on(s, f)",
			"real_interval(s)",
			"finite(k)",
			"∀i:A. i ∈ k ⇒ &0 ≤ w(i) ∧ x(i) ∈ s",
			"Σ_{i∈k} w(i) = &1",
		},
		Conclusion: "f(Σ_{i∈k} w(i) * x(i)) ≤ Σ_{i∈k} w(i) * f(x(i))",
	}, func(
		a *Argument,
		f *Arrow[Real, Real],
		s *Expr[Set[Real]],
		k *Expr[Set[A]],
		convex, interval, finiteK Fact,
	) {
		chord := a.Unfolded(convex, RealConvexOnDef)
		a.Show(
			"by induction on the finite index set, adjoining one fresh point at a time",
			ByInduction(
				finite_set.FiniteInductFresh,
				finiteK,
				Case(
					"weights over the empty set total zero, never one",
					Simp(Fwd(real_sum.Clauses)),
					ByArith(),
				),
				Case(
					"adjoining a fresh point j to a finite set u",
					Derive(func(b *Argument) {
						j := b.FixAs[A]("j")
						u := b.FixAs[Set[A]]("u")
						step := b.Conjuncts(
							b.Assume(),
							"the inequality holds over u",
							"j is not in u",
							"u is finite")
						w := b.FixAs[Fun[A, Real]]("w")
						x := b.FixAs[Fun[A, Real]]("x")
						given := b.Conjuncts(
							b.Assume(),
							"the weights are nonnegative at points of s",
							"and total one")
						weights := b.Have(
							"the weights on u are nonnegative",
							"∀i:A. i ∈ u ⇒ &0 ≤ w(i)",
							BySets(given[0]))
						points := b.Have(
							"and their points lie in s",
							"∀i:A. i ∈ u ⇒ x(i) ∈ s",
							BySets(given[0]))
						atJ := b.Have(
							"so does j, at a nonnegative weight",
							"&0 ≤ w(j) ∧ x(j) ∈ s",
							BySets(given[0]))
						split := b.Conjuncts(
							GroupPremises(step[2], step[1], weights, given[1], ConvexCombinationInsert.At(u, j, w, x)),
							"the weights on u total 1 − w(j)",
							"the combination is x(j) at weight w(j) beside m at weight 1 − w(j)")
						values := b.Conjuncts(
							GroupPremises(
								step[2],
								step[1],
								weights,
								given[1],
								ConvexCombinationInsert.At(u, j, w, b.TermAs[Fun[A, Real]]("λi:A. f(x(i))"))),
							"the weights on u total 1 − w(j)",
							"the combination of values is f(x(j)) at weight "+
								"w(j) beside the divided combination of values over u")
						m, mDef := b.LetAs[Real]("m", "Σ_{i∈u} real_inv(&1 - w(j)) * w(i) * x(i)")
						notOne := b.Unless(
							b.Term("w(j) = &1"),
							"all the weight sits at j, so both sides are f(x(j))",
							Given(func(c *Argument, one Fact) {
								collapse := c.Conjuncts(
									c.Have(
										"the combination is x(j), and the combination of values f(x(j))",
										"Σ_{i∈insert(j, u)} w(i) * x(i) = x(j) ∧ Σ_{i∈insert(j, u)} w(i) * f(x(i)) = f(x(j))",
										ByArith(split[1], values[1], one),
									),
									"the combination is x(j)",
									"the combination of values is f(x(j))")
								c.Show(
									"f(x(j)) ≤ f(x(j))",
									collapse[0].Rw(),
									collapse[1].Rw(),
									ByArith())
							}))
						positive := b.Have(
							"1 − w(j), a total of nonnegative weights, is not 0, so it is positive",
							"&0 < &1 - w(j)",
							ByArith(real_sum.Nonneg.At(u, w), weights, split[0], notOne),
						)
						scaled := b.Have(
							"the weights divided by 1 − w(j) are nonnegative at points of s",
							"∀l:A. l ∈ u ⇒ &0 ≤ real_inv(&1 - w(j)) * w(l) ∧ x(l) ∈ s",
							b.ForEach(func(l *Expr[A]) Action {
								return ByArith(weights.At(l), points.At(l), positive)
							}),
						)
						unit := b.Have(
							"and total one",
							"Σ_{l∈u} real_inv(&1 - w(j)) * w(l) = &1",
							ByArith(real_sum.ScalarLeft.At(b.TermAs[Real]("real_inv(&1 - w(j))"), w, u), split[0], positive),
						)
						divided := b.TermAs[Fun[A, Real]]("λl:A. real_inv(&1 - w(j)) * w(l)")
						averaged := b.Conjuncts(
							b.Have(
								"so m lies in s, and f(m) is at most the divided combination of values, by the inequality over u",
								"m ∈ s ∧ f(m) ≤ Σ_{i∈u} real_inv(&1 - w(j)) * w(i) * f(x(i))",
								By(
									ConvexCombinationIn.At(s, u, divided, x),
									step[0].At(divided, x),
									interval,
									step[2],
									scaled,
									unit,
									mDef),
							),
							"m lies in s",
							"f(m) is at most the divided combination of values")
						between := b.Have(
							"convexity between x(j) and m at weight w(j)",
							"f(w(j) * x(j) + (&1 - w(j)) * m) ≤ w(j) * f(x(j)) + (&1 - w(j)) * f(m)",
							ByArith(chord.At(b.TermAs[Real]("x(j)"), m, b.TermAs[Real]("w(j)")), atJ, averaged[0], positive),
						)
						b.Show(
							"and (1 − w(j))·f(m) is at most 1 − w(j) times the divided combination of values",
							split[1].Rw(),
							values[1].Rw(),
							ByArith(
								between,
								averaged[1],
								positive,
								real_order_ring.LessEqMulLeft.At(
									b.TermAs[Real]("&1 - w(j)"),
									b.TermAs[Real]("f(m)"),
									b.TermAs[Real]("Σ_{i∈u} real_inv(&1 - w(j)) * w(i) * f(x(i))"))),
						)
					}),
				),
			),
		)
	}),
})}
