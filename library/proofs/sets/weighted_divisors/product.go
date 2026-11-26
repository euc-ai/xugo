// product.go — the counting sequence of the effective divisors as an Euler
// product. Over a finite set each point contributes its geometric series
// 1 + z^{w(x)} + z^{2w(x)} + …, the coefficients multiplied by the
// convolution of sequences of naturals; in degree n only the points of weight
// at most n can occur. An effective divisor D spends i at x when its value
// there, weighted, is i: w(x)·D(x) = i.

package weighted_divisors

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// WeightedCountFibre — the effective divisors over T with a fresh point x
// added, of degree m, that spend i of their degree at x — i a multiple of
// w(x) — are as many as the effective divisors over T of degree m − i.
// Clearing the value at x and putting i / w(x) back are inverse to each
// other: the first takes such a divisor to one over T whose degree drops by
// exactly w(x)·D(x) = i, the second puts i back, and a value put at x is
// nonzero only where w(x) is, i / 0 being 0.
var WeightedCountFibre = weightedCountFibreThm{family.Add(registry.ProofEntry{
	Name: "WeightedCountFibre",
	Key:  "prop_73a1da42cee70c8b",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(A). ∀w:(A → num). ∀x:A. ∀m i:num.",
		Hypotheses: []string{
			"finite(T)",
			"x ∉ T",
			"i ≤ m",
			"w(x) ∣ i",
		},
		Conclusion: "has_size(«fibre», weighted_count(T, w, m - i))",
		Abbrev: Abbrev{
			{Name: "fibre", Text: "{D:A → num | " +
				"    weighted_effective(insert(x, T), w, D) ∧ weighted_degree(w, D) = m ∧ w(x) * D(x) = i}"},
			{Name: "lower", Text: "{E:A → num | weighted_effective(T, w, E) ∧ weighted_degree(w, E) = m - i}"},
			{Name: "extend", Text: "λE:A → num. λy:A. COND(y = x, div(i, w(x)), E(y))"},
			{Name: "restrict", Text: "λD:A → num. λy:A. COND(y = x, 0, D(y))"},
		},
	}, func(
		a *Argument,
		T *Expr[Set[A]],
		w *Arrow[A, Nat],
		x *Expr[A],
		m, i *Expr[Nat],
		finiteT, fresh, below, divides Fact,
	) {
		weight := w.Apply(x)
		quotient := a.Have(
			"w(x) divides i, so w(x) times i / w(x) is i",
			"w(x) * div(i, w(x)) = i",
			Derive(func(b *Argument) {
				nonzero := b.Unless(
					b.TermAs[Bool]("w(x) = 0"),
					"where w(x) = 0 it divides only i = 0, and both sides are 0",
					Given(func(c *Argument, weightless Fact) {
						c.Do(ByArith(weightless, divides, nat_divides.ZeroDivides.At(i)))
					}))
				b.Show(
					"where w(x) ≠ 0, i is w(x) times its quotient, the remainder being 0",
					ByArith(nonzero, divides, nat_divides.DividesMod.At(weight, i), nat_div_mod.Division.At(i, weight)))
			}))
		count := a.TermAs[Nat]("weighted_count(T, w, m - i)")
		counted := a.Have(
			"the effective divisors over the finite T of degree m − "+
				"i are finitely many, weighted_count(T, w, m − i) of them",
			"has_size(«lower», weighted_count(T, w, m - i))",
			By(
				finiteT,
				finite_set.FiniteRestrict.At(T, a.TermAs[Set[A]]("λy:A. w(y) ≤ m - i")),
				WeightedDivisorsFinite.At(T, w, a.TermAs[Nat]("m - i")),
				WeightedCountDef.At(T, w, a.TermAs[Nat]("m - i")),
				cardinality.HasSizeDef.At(a.TermAs[Set[Fun[A, Nat]]]("«lower»"), count)))
		extended := a.Have(
			"putting i / w(x) at x carries an effective divisor over T "+
				"of degree m − i into the fibre, and clearing x gives it back",
			Statement{
				Binders: "∀E:A → num.",
				Hypotheses: []string{
					"weighted_effective(T, w, E)",
					"weighted_degree(w, E) = m - i",
				},
				Conclusion: "«extend»(E) ∈ «fibre» ∧ «restrict»(«extend»(E)) = E",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[A, Nat]]("E")
				lower := b.Conjuncts(
					b.Assume(),
					"E is effective over T",
					"of degree m − i")
				effective := b.Conjuncts(
					b.Unfolded(lower[0], WeightedEffectiveDef),
					"the support of E is finite",
					"and lies in T, at points of positive weight")
				cleared := b.Have(
					"E vanishes at x, which lies outside T, so clearing x after putting i / w(x) there gives E back",
					"«restrict»(«extend»(E)) = E",
					Funext(),
					By(fresh, effective[1]))
				spread := b.Have(
					"the extension vanishes off x and the support of E",
					"fun_support(0, λy:A. COND(y = x, div(i, w(x)), E(y))) ⊆ insert(x, fun_support(0, E))",
					BySets())
				finiteSpread := b.Have(
					"so its support is finite",
					"finite(fun_support(0, λy:A. COND(y = x, div(i, w(x)), E(y))))",
					By(
						spread,
						effective[0],
						finite_set.FiniteInsert.At(x, b.TermAs[Set[A]]("fun_support(0, E)")),
						finite_set.FiniteSubset))
				extendedEffective := b.Have(
					"and it is effective over insert(x, T): i / w(x) is nonzero only where w(x) is",
					"weighted_effective(insert(x, T), w, «extend»(E))",
					Unfold(WeightedEffectiveDef),
					By(
						finiteSpread,
						effective[1],
						nat_div_mod.DivZero.At(i),
						nat_order.PosIffNonzero.At(weight),
						set_basic.InInsert))
				b.Show(
					"its degree is w(x)·(i / w(x)) = i more than the degree m − i of E, and it spends i at x",
					ByArith(
						extendedEffective,
						finiteSpread,
						cleared,
						quotient,
						below,
						lower[1],
						WeightedDegreeSplit.At(w, b.TermAs[Fun[A, Nat]]("«extend»(E)"), x)))
			}))
		restricted := a.Have(
			"clearing x carries a divisor of the fibre to an effective divisor "+
				"over T of degree m − i, and putting i / w(x) back gives it back",
			Statement{
				Binders: "∀D:A → num.",
				Hypotheses: []string{
					"weighted_effective(insert(x, T), w, D)",
					"weighted_degree(w, D) = m",
					"w(x) * D(x) = i",
				},
				Conclusion: "«restrict»(D) ∈ «lower» ∧ «extend»(«restrict»(D)) = D",
			},
			Derive(func(b *Argument) {
				D := b.FixAs[Fun[A, Nat]]("D")
				fibre := b.Conjuncts(
					b.Assume(),
					"D is effective over insert(x, T)",
					"of degree m",
					"spending i at x")
				effective := b.Conjuncts(
					b.Unfolded(fibre[0], WeightedEffectiveDef),
					"the support of D is finite",
					"and lies in insert(x, T), at points of positive weight")
				value := b.Have(
					"the value of D at x is i / w(x)",
					"D(x) = div(i, w(x))",
					Derive(func(c *Argument) {
						nonzero := c.Unless(
							c.TermAs[Bool]("w(x) = 0"),
							"where w(x) = 0 both are 0: D vanishes at the points of weight 0, and i / 0 is 0",
							Given(func(d *Argument, weightless Fact) {
								d.Do(By(
									Normalized,
									weightless,
									effective[1],
									nat_div_mod.DivZero.At(i),
									nat_order.PosIffNonzero.At(weight)))
							}))
						c.Show(
							"where w(x) ≠ 0, dividing w(x)·D(x) = i by w(x) gives back D(x)",
							By(Normalized, nonzero, fibre[2], nat_div_mod.DivMult.At(weight, c.TermAs[Nat]("D(x)"))))
					}))
				regained := b.Have(
					"so putting i / w(x) back at x gives D",
					"«extend»(«restrict»(D)) = D",
					Funext(),
					By(value))
				shrunk := b.Have(
					"clearing x shrinks the support",
					"fun_support(0, λy:A. COND(y = x, 0, D(y))) ⊆ fun_support(0, D)",
					BySets())
				restrictedEffective := b.Have(
					"so D cleared at x is effective over T, its support finite and avoiding x",
					"weighted_effective(T, w, «restrict»(D))",
					Unfold(WeightedEffectiveDef),
					By(shrunk, effective[0], finite_set.FiniteSubset, effective[1], set_basic.InInsert))
				b.Show(
					"its degree is m less the part w(x)·D(x) = i that D spends at x",
					ByArith(
						restrictedEffective,
						regained,
						effective[0],
						fibre[1],
						fibre[2],
						WeightedDegreeSplit.At(w, D, x)))
			}))
		a.Show(
			"so the fibre has as many points as the effective divisors over T of degree m − i",
			By(
				extended,
				restricted,
				counted,
				cardinality.MutualInversesHasSize.At(
					a.TermAs[Set[Fun[A, Nat]]]("«lower»"),
					a.TermAs[Set[Fun[A, Nat]]]("«fibre»"),
					a.TermAs[Fun[Fun[A, Nat], Fun[A, Nat]]]("«extend»"),
					a.TermAs[Fun[Fun[A, Nat], Fun[A, Nat]]]("«restrict»"),
					count)))
	}),
})}

// WeightedCountInsert — adjoining a fresh point x to a finite T multiplies the
// counting sequence of the effective divisors by the geometric series of x,
// whose i-th coefficient is 1 where w(x) divides i and 0 elsewhere. In degree
// m, sort the effective divisors over insert(x, T) by the part i = w(x)·D(x)
// of their degree spent at x: the part is at most m, and the divisors
// spending i are counted by weighted_count(T, w, m − i) where w(x) divides i
// (WeightedCountFibre) and are none where it does not.
var WeightedCountInsert = weightedCountInsertThm{family.Add(registry.ProofEntry{
	Name: "WeightedCountInsert",
	Key:  "prop_6106602667685402",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(A). ∀w:(A → num). ∀x:A. ∀m:num.",
		Hypotheses: []string{
			"finite(T)",
			"x ∉ T",
		},
		Conclusion: "weighted_count(insert(x, T), w, m) = " +
			"«conv»(λi:num. COND(w(x) ∣ i, 1, 0), weighted_count(T, w), m)",
		Abbrev: Abbrev{
			{Name: "insertDivisors", Text: "{D:A → num | " +
				"    weighted_effective(insert(x, T), w, D) ∧ weighted_degree(w, D) = m}"},
			{Name: "spending", Text: "λi:num. {D:A → num | D ∈ «insertDivisors» ∧ w(x) * D(x) = i}"},
		},
	}, func(
		a *Argument,
		T *Expr[Set[A]],
		w *Arrow[A, Nat],
		x *Expr[A],
		m *Expr[Nat],
		finiteT, fresh Fact,
	) {
		inserted := a.TermAs[Set[A]]("insert(x, T)")
		divisors := a.TermAs[Set[Fun[A, Nat]]]("«insertDivisors»")
		finiteDivisors := a.Have(
			"only finitely many effective divisors over the finite insert(x, T) have degree m",
			"finite(«insertDivisors»)",
			By(
				finiteT,
				finite_set.FiniteInsert.At(x, T),
				finite_set.FiniteRestrict.At(inserted, a.TermAs[Set[A]]("λy:A. w(y) ≤ m")),
				WeightedDivisorsFinite.At(inserted, w, m)))
		spent := a.Have(
			"each of them spends at x a part w(x)·D(x) of its degree, at most m",
			"∀D:A → num. D ∈ «insertDivisors» ⇒ ∃!i:num. i ∈ {j:num | j ≤ m} ∧ w(x) * D(x) = i",
			Derive(func(b *Argument) {
				D := b.FixAs[Fun[A, Nat]]("D")
				member := b.Assume()
				b.Show(
					"the degree is w(x)·D(x) plus the degree of D cleared at x",
					By(
						member,
						WeightedEffectiveDef.At(inserted, w, D),
						WeightedDegreeSplit.At(w, D, x),
						nat_order.LessEqAdd))
			}))
		sizes := a.Have(
			"over each i ≤ m, the divisors spending i at x number "+
				"weighted_count(T, w, m − i) where w(x) divides i, and none elsewhere",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i ∈ {j:num | j ≤ m}",
				},
				Conclusion: "has_size(«spending»(i), COND(w(x) ∣ i, 1, 0) * weighted_count(T, w, m - i))",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				b.Cases(b.TermAs[Bool]("w(x) ∣ i"))
				b.When(
					"where w(x) divides i, clearing x matches them with the effective divisors over T of degree m − i",
					func(c *Argument, divides Fact) {
						c.Show(
							"so they number weighted_count(T, w, m − i)",
							ByArith(finiteT, fresh, below, divides, WeightedCountFibre.At(T, w, x, m, i)))
					})
				b.Otherwise(
					"where it does not, there are none, a multiple of w(x) being divisible by w(x)",
					func(c *Argument, indivisible Fact) {
						none := c.Have(
							"no divisor spends i at x",
							"«spending»(i) = ∅",
							BySets(indivisible, nat_divides.DividesOwnMultiple))
						c.Show(
							"and the empty set has no points",
							ByArith(indivisible, none, cardinality.HasSizeZero))
					})
			}))
		a.Show(
			"so the count is the sum over i ≤ m of the fibre sizes, the m-th coefficient of the convolution",
			By(
				finiteDivisors,
				spent,
				sizes,
				WeightedCountDef.At(inserted, w, m),
				nat_sum.CardByFibres.At(
					divisors,
					a.TermAs[Set[Nat]]("{j:num | j ≤ m}"),
					a.TermAs[Fun2[Fun[A, Nat], Nat, Bool]]("λD:A → num. λi:num. w(x) * D(x) = i"),
					a.TermAs[Fun[Nat, Nat]]("λi:num. COND(w(x) ∣ i, 1, 0) * weighted_count(T, w, m - i)")),
				At(
					polynomial.NatPolynomialMulSum,
					a.TermAs[Fun[Nat, Nat]]("λi:num. COND(w(x) ∣ i, 1, 0)"),
					a.TermAs[Fun[Nat, Nat]]("weighted_count(T, w)"),
					m)))
	}),
})}

// WeightedCountFold — over a finite set T, the counting sequence of the
// effective divisors is the product, folded over T, of the geometric series
// of the points of T, the fold starting from the unit sequence. By induction
// on T: over ∅ only the zero divisor is effective, in degree 0, and a fresh
// point multiplies the counts by its own series (WeightedCountInsert), which
// is the next step of the fold, the convolution factors of two points
// commuting. The induction is on the equality of whole sequences, not of one
// coefficient: the insert step convolves, so its degree m reads the counts
// over the smaller set at every degree up to m.
var WeightedCountFold = weightedCountFoldThm{family.Add(registry.ProofEntry{
	Name: "WeightedCountFold",
	Key:  "prop_cc46c6cdbfa98136",
	Build: family.Theorem(Statement{
		Binders:    "∀T:set(A). ∀w:(A → num). ∀m:num.",
		Hypotheses: []string{"finite(T)"},
		Conclusion: "weighted_count(T, w, m) = set_fold(«step», T, «unit», m)",
	}, func(a *Argument, T *Expr[Set[A]], w *Arrow[A, Nat], finiteT Fact) {
		step := a.TermAs[Fun2[A, Fun[Nat, Nat], Fun[Nat, Nat]]]("«step»")
		unit := a.TermAs[Fun[Nat, Nat]]("«unit»")
		commute := a.Have(
			"the steps of any two points commute, convolution being "+
				"left-commutative; the fold's recursion asks it of distinct points only",
			"∀x y:A. ∀z:(num → num). x ≠ y ⇒ «step»(x, «step»(y, z)) = «step»(y, «step»(x, z))",
			By(polynomial.NatPolynomialMulLeftComm))
		empty := a.TermAs[Set[A]]("∅")
		counted := a.TermAs[Fun[Set[A], Bool]](
			"λU:set(A). weighted_count(U, w) = set_fold(«step», U, «unit»)")
		a.Show(
			"by induction on the finite set T, one point at a time",
			ByInduction(finite_set.FiniteInductFresh.At(counted, T), finiteT,
				Case(
					"over ∅ the counts are the unit sequence, which is the empty fold",
					Derive(func(b *Argument) {
						vanishing := b.Have(
							"an effective divisor over ∅ vanishes everywhere, so has degree 0",
							"∀D:(A → num). weighted_effective(∅, w, D) ⇒ weighted_degree(w, D) = 0",
							Derive(func(c *Argument) {
								c.FixAs[Fun[A, Nat]]("D")
								support := c.Unfolded(c.Assume(), WeightedEffectiveDef)
								nowhere := c.Have(
									"its support lies in ∅",
									"fun_support(0, D) = ∅",
									BySets(support))
								c.Show(
									"and the sum over ∅ is 0",
									By(nowhere, WeightedDegreeDef, nat_sum.Clauses))
							}))
						b.Do(Funext())
						m := b.FixAs[Nat]("m")
						b.Cases(b.TermAs[Bool]("m = 0"))
						b.When(
							"in degree 0 the zero divisor is the one effective divisor",
							func(c *Argument, zero Fact) {
								c.Show(
									"and the unit sequence is 1 there",
									By(zero, commute, cardinality.FiniteRecursion.At(step, unit), WeightedCountZero.At(empty, w)))
							})
						b.Otherwise(
							"in positive degree there is no effective divisor over ∅",
							func(c *Argument, positive Fact) {
								none := c.Have(
									"the effective divisors over ∅ of degree m form the empty set",
									"{D:A → num | weighted_effective(∅, w, D) ∧ weighted_degree(w, D) = m} = ∅",
									BySets(positive, vanishing))
								c.Show(
									"so the count is 0, as the unit sequence is there",
									By(
										positive,
										none,
										WeightedCountDef.At(empty, w, m),
										cardinality.CardClauses,
										commute,
										cardinality.FiniteRecursion.At(step, unit)))
							})
					})),
				Case(
					"a fresh point x multiplies the counts by its geometric series, the next step of the fold",
					Derive(func(b *Argument) {
						x, U := b.FixAs[A]("x"), b.FixAs[Set[A]]("U")
						carried := b.Conjuncts(
							b.Assume(),
							"the counts over U are the fold over U",
							"x is not in U",
							"U is finite")
						b.Show(
							"adjoining x convolves both sides with the geometric series of x",
							By(
								carried[0],
								carried[1],
								carried[2],
								commute,
								cardinality.FiniteRecursion.At(step, unit),
								At(WeightedCountInsert, U, w, x)))
					}))))
	}),
})}

// WeightedCountProduct — the number of effective divisors of degree n is the
// n-th coefficient of the Euler product of the geometric series of the points
// of weight at most n, when those points are finitely many. A divisor of
// degree n spends at most n at any point of its support, so it is effective
// over S exactly when it is over the points of weight at most n; there the
// count is the folded product (WeightedCountFold).
var WeightedCountProduct = weightedCountProductThm{family.Add(registry.ProofEntry{
	Name: "WeightedCountProduct",
	Key:  "prop_c437c78a01fd2339",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A). ∀w:(A → num). ∀n:num.",
		Hypotheses: []string{"finite(«lowWeight»)"},
		Conclusion: "weighted_count(S, w, n) = set_fold(«step», «lowWeight», «unit», n)",
	}, func(a *Argument, S *Expr[Set[A]], w *Arrow[A, Nat], n *Expr[Nat], finiteLowWeight Fact) {
		lowWeight := a.TermAs[Set[A]]("«lowWeight»")
		agree := a.Have(
			"a divisor of degree n is effective over S exactly when "+
				"it is effective over the points of weight at most n",
			Statement{
				Binders:    "∀D:A → num.",
				Hypotheses: []string{"weighted_degree(w, D) = n"},
				Conclusion: "weighted_effective(S, w, D) ⇔ weighted_effective(«lowWeight», w, D)",
			},
			Derive(func(b *Argument) {
				D := b.FixAs[Fun[A, Nat]]("D")
				degree := b.Assume()
				b.Iff()
				b.Forward(
					"its support lies in S at weights at most its degree n",
					func(c *Argument, effective Fact) {
						bounded := c.Have(
							"where D does not vanish, the weight is at most the degree",
							"∀x:A. D(x) ≠ 0 ⇒ w(x) ≤ n",
							By(Normalized, effective, degree, At(WeightedSupportBound, S, w, D)))
						onS := c.Conjuncts(
							c.Unfolded(effective, WeightedEffectiveDef),
							"the support of D is finite",
							"and lies in S, at points of positive weight")
						c.Show(
							"so it lies among the points of weight at most n",
							Unfold(WeightedEffectiveDef),
							By(onS[0], onS[1], bounded))
					})
				b.Backward(
					"the points of weight at most n lie in S",
					func(c *Argument, effective Fact) {
						c.Show(
							"so a support among them lies in S",
							By(effective, WeightedEffectiveDef))
					})
			}))
		a.Show(
			"the two carry the same effective divisors of degree n, and over "+
				"the finitely many low-weight points the count is the folded product",
			By(
				finiteLowWeight,
				agree,
				set_basic.Extension.At(
					a.TermAs[Set[Fun[A, Nat]]]("{D:A → num | weighted_effective(S, w, D) ∧ weighted_degree(w, D) = n}"),
					a.TermAs[Set[Fun[A, Nat]]](
						"{D:A → num | weighted_effective(«lowWeight», w, D) ∧ weighted_degree(w, D) = n}")),
				WeightedCountDef.At(S, w, n),
				WeightedCountDef.At(lowWeight, w, n),
				WeightedCountFold.At(lowWeight, w, n)))
	}),
})}
