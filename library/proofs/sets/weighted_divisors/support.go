// support.go — the support and the degree of an effective divisor: a
// finitely supported D : A → num that vanishes off S and at the points of
// weight 0 (weighted_effective), of degree Σ_x w(x)·D(x). A point of its
// support is a point of S of positive weight, the weight and the value there
// at most the degree; the effective divisors of one degree are finitely many
// when the points weighing at most it are, and in degree zero there is one;
// and the degree splits at a point, may be summed over any set holding the
// support, and grows by k·w(x) when k is added at x.

package weighted_divisors

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// WeightedSupportBound — a point where an effective divisor does not vanish
// is a point of S of positive weight, and both its weight and the divisor's
// value there are at most the degree. The product w(x)·D(x) is one term of
// the finite sum the degree is, and a product of two nonzero naturals bounds
// each of its factors.
var WeightedSupportBound = weightedSupportBoundThm{family.Add(registry.ProofEntry{
	Name: "WeightedSupportBound",
	Key:  "prop_dbb4c79564696f1c",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀w D:(A → num). ∀x:A.",
		Hypotheses: []string{
			"weighted_effective(S, w, D)",
			"D(x) ≠ 0",
		},
		Conclusion: "x ∈ S ∧ 0 < w(x) ∧ w(x) ≤ weighted_degree(w, D) ∧ D(x) ≤ weighted_degree(w, D)",
	},
		func(a *Argument, S *Expr[Set[A]], w, D *Arrow[A, Nat], x *Expr[A], effective, nonzero Fact) {
			support := a.Conjuncts(
				a.Unfolded(effective, WeightedEffectiveDef),
				"the support of D is finite",
				"and lies in S, at points of positive weight")
			term := a.Have(
				"w(x)·D(x) is a term of the finite sum that is the degree",
				"w(x) * D(x) ≤ weighted_degree(w, D)",
				By(
					Normalized,
					support[0],
					nonzero,
					WeightedDegreeDef,
					nat_sum.TermLeSum.At(
						a.TermAs[Fun[A, Nat]]("λy:A. w(y) * D(y)"),
						a.TermAs[Set[A]]("fun_support(0, D)"),
						x)))
			weight, value := w.Apply(x), D.Apply(x)
			a.Show(
				"x has positive weight, and a product of two nonzero naturals bounds each factor",
				ByArith(
					nonzero,
					support[1].At(x),
					term,
					nat_order.LessEqMulNonzero.At(weight, value),
					nat_order.LessEqMulNonzero.At(value, weight)))
		}),
})}

// WeightedDivisorsFinite — when only finitely many points of S weigh at
// most n, only finitely many effective divisors have degree n. Such a
// divisor takes values at most n and vanishes off those points, so it is one
// of the maps from them into {0, …, n} that vanish elsewhere; those maps are
// finitely many, and a subset of a finite set is finite.
var WeightedDivisorsFinite = weightedDivisorsFiniteThm{family.Add(registry.ProofEntry{
	Name: "WeightedDivisorsFinite",
	Key:  "prop_2392c9f126261353",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀w:(A → num). ∀n:num.",
		Hypotheses: []string{
			"finite(«lowWeight»)",
		},
		Conclusion: "finite(«divisors»)",
		Abbrev: Abbrev{
			{Name: "upToN", Text: "{i:num | i ≤ n}"},
			{Name: "maps", Text: "{h:A → num | " +
				"    (∀x:A. x ∈ «lowWeight» ⇒ h(x) ∈ «upToN») ∧ (∀x:A. x ∉ «lowWeight» ⇒ h(x) = 0)}"},
		},
	},
		func(a *Argument, S *Expr[Set[A]], w *Arrow[A, Nat], n *Expr[Nat], finiteLowWeight Fact) {
			bounded := a.Have(
				"an effective divisor of degree n takes values at "+
					"most n and vanishes off the points of weight at most n",
				Statement{
					Binders: "∀D:A → num. ∀x:A.",
					Hypotheses: []string{
						"weighted_effective(S, w, D)",
						"weighted_degree(w, D) = n",
					},
					Conclusion: "D(x) ≤ n ∧ (D(x) ≠ 0 ⇒ x ∈ «lowWeight»)",
				},
				Derive(func(b *Argument) {
					D := b.FixAs[Fun[A, Nat]]()
					x := b.FixAs[A]()
					ofDegreeN := b.Assume()
					b.Show(
						"where D does not vanish, the weight there and D(x) are at most the degree, which is n",
						ByArith(ofDegreeN, WeightedSupportBound.At(S, w, D, x)))
				}))
			within := a.Have(
				"so every effective divisor of degree n is one of those maps",
				"«divisors» ⊆ «maps»",
				BySets(bounded))
			a.Show(
				"and those maps are finitely many, their domain and the values up to n being finite",
				By(
					finiteLowWeight,
					within,
					num_segment.FiniteBelow.At(n),
					cardinality.FiniteFunspace.At(
						a.TermAs[Set[A]]("«lowWeight»"),
						a.TermAs[Set[Nat]]("«upToN»"),
						a.TermAs[Nat]("0")),
					finite_set.FiniteSubset))
		}),
})}

// WeightedCountZero — the zero divisor is the one effective divisor of degree
// zero. It is effective, of degree the empty sum; and a value that did not
// vanish would be at most the degree (WeightedSupportBound), which is 0.
var WeightedCountZero = weightedCountZeroThm{family.Add(registry.ProofEntry{
	Name: "WeightedCountZero",
	Key:  "prop_fc9aa2b883264baf",
	Build: family.Theorem(
		"∀S:set(A). ∀w:(A → num). weighted_count(S, w, 0) = 1",
		func(a *Argument, S *Expr[Set[A]], w *Arrow[A, Nat]) {
			noSupport := a.Have(
				"the zero divisor has empty support",
				"fun_support(0, λx:A. 0) = ∅",
				BySets())
			zero := a.Have(
				"so it is effective, of degree the empty sum",
				"weighted_effective(S, w, λx:A. 0) ∧ weighted_degree(w, λx:A. 0) = 0",
				Simp(
					Fwd(WeightedEffectiveDef),
					Fwd(WeightedDegreeDef),
					Fwd(noSupport),
					Fwd(nat_sum.Clauses),
					Fwd(finite_set.FiniteRules)),
				Basic())
			only := a.Have(
				"and an effective divisor of degree zero is the zero divisor",
				"∀D:(A → num). weighted_effective(S, w, D) ∧ weighted_degree(w, D) = 0 ⇒ D = λx:A. 0",
				Derive(func(b *Argument) {
					D := b.FixAs[Fun[A, Nat]]("D")
					ofDegreeZero := b.Assume()
					b.Do(Funext())
					x := b.FixAs[A]("x")
					nonzero := b.SupposeNot()
					b.Show(
						"but where D does not vanish its value is at most the degree, 0",
						ByArith(ofDegreeZero, nonzero, WeightedSupportBound.At(S, w, D, x)))
				}))
			degreeZero := a.Have(
				"so the effective divisors of degree zero are the zero divisor alone",
				"{D:A → num | weighted_effective(S, w, D) ∧ weighted_degree(w, D) = 0} = {λx:A. 0}",
				BySets(only, zero))
			a.Show(
				"and their number is one",
				By(degreeZero, WeightedCountDef, cardinality.CardSing))
		}),
})}

// WeightedDegreeSplit — the degree of a finitely supported D is what its
// value at one point x contributes, w(x)·D(x), plus the degree of D with that
// value cleared. Where D(x) = 0 nothing is cleared; where it is not, the
// support of D is x laid into the support of D cleared at x, and the sum over
// it takes the one new term.
var WeightedDegreeSplit = weightedDegreeSplitThm{family.Add(registry.ProofEntry{
	Name: "WeightedDegreeSplit",
	Key:  "prop_8eddc5b3d6da5b10",
	Build: family.Theorem(Statement{
		Binders:    "∀w D:(A → num). ∀x:A.",
		Hypotheses: []string{"finite(fun_support(0, D))"},
		Conclusion: "weighted_degree(w, D) = w(x) * D(x) + weighted_degree(w, «cleared»)",
		Abbrev: Abbrev{
			{Name: "cleared", Text: "λy:A. COND(y = x, 0, D(y))"},
		},
	}, func(a *Argument, w, D *Arrow[A, Nat], x *Expr[A], finiteSupport Fact) {
		a.Cases(a.TermAs[Bool]("D(x) = 0"))
		a.When(
			"where D vanishes at x, clearing x changes nothing and x contributes w(x)·0",
			func(b *Argument, vanishes Fact) {
				unchanged := b.Have(
					"D cleared at x is D itself",
					"«cleared» = D",
					Funext(),
					By(vanishes))
				b.Show(
					"so both degrees are the degree of D",
					ByArith(unchanged, vanishes))
			})
		a.Otherwise(
			"where D(x) ≠ 0, the support is the cleared support with x laid in",
			func(b *Argument, nonzero Fact) {
				rest := b.TermAs[Set[A]]("fun_support(0, λy:A. COND(y = x, 0, D(y)))")
				support := b.Have(
					"the support of D is x laid into the support of D cleared at x",
					"fun_support(0, D) = insert(x, fun_support(0, λy:A. COND(y = x, 0, D(y))))",
					BySets(nonzero))
				restSum := b.Have(
					"off x, D and D cleared at x agree, so the sum of "+
						"w·D over the cleared support is the cleared degree",
					"nat_sum(fun_support(0, λy:A. COND(y = x, 0, D(y))), λy:A. w(y) * D(y)) = "+
						"weighted_degree(w, «cleared»)",
					By(
						WeightedDegreeDef.At(w, b.TermAs[Fun[A, Nat]]("«cleared»")),
						nat_sum.Congruence.At(
							rest,
							b.TermAs[Fun[A, Nat]]("λy:A. w(y) * D(y)"),
							b.TermAs[Fun[A, Nat]]("λy:A. w(y) * COND(y = x, 0, D(y))"))))
				b.Show(
					"and the sum over the support takes the one new term w(x)·D(x)",
					By(
						finiteSupport,
						support,
						finite_set.FiniteInsert,
						restSum,
						WeightedDegreeDef.At(w, D),
						nat_sum.Clauses))
			})
	}),
})}

// WeightedDegreeOver — the degree of D may be summed over any set that holds
// its support: off the support every term w(x)·D(x) is zero, and enlarging an
// index set by zero terms leaves a sum where it was. The sum reads only the
// points where its terms are nonzero, so T need not be finite.
var WeightedDegreeOver = weightedDegreeOverThm{family.Add(registry.ProofEntry{
	Name: "WeightedDegreeOver",
	Key:  "prop_872837db66522bc9",
	Build: family.Theorem(Statement{
		Binders:    "∀w D:(A → num). ∀T:set(A).",
		Hypotheses: []string{"fun_support(0, D) ⊆ T"},
		Conclusion: "weighted_degree(w, D) = nat_sum(T, λx:A. w(x) * D(x))",
	},
		func(a *Argument, w, D *Arrow[A, Nat], T *Expr[Set[A]], within Fact) {
			a.Show(
				"the terms T adds to the support vanish, and vanishing terms do not move the sum",
				Unfold(WeightedDegreeDef),
				By(within, nat_sum.Superset, nat_arith.MulZero))
		}),
})}

// WeightedRaise — adding k to an effective divisor D at a point x of S of
// positive weight leaves it effective and raises its degree by k·w(x). The
// raised divisor vanishes off x and the support of D, so it is finitely
// supported, and where it does not vanish it is at x or at a point of D's
// support. Cleared at x it is D cleared at x, so both degrees split at x over
// D cleared at x (WeightedDegreeSplit), and only the terms at x differ, by
// w(x)·k.
var WeightedRaise = weightedRaiseThm{family.Add(registry.ProofEntry{
	Name: "WeightedRaise",
	Key:  "prop_3e288265b3baf85c",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀w D:(A → num). ∀x:A. ∀k:num.",
		Hypotheses: []string{
			"weighted_effective(S, w, D)",
			"x ∈ S",
			"0 < w(x)",
		},
		Conclusion: "weighted_effective(S, w, «raised») ∧ " +
			"weighted_degree(w, «raised») = weighted_degree(w, D) + k * w(x)",
		Abbrev: Abbrev{
			{Name: "raised", Text: "λy:A. D(y) + COND(y = x, k, 0)"},
		},
	},
		func(
			a *Argument,
			S *Expr[Set[A]],
			w, D *Arrow[A, Nat],
			x *Expr[A],
			k *Expr[Nat],
			effective, xInS, positive Fact,
		) {
			support := a.Conjuncts(
				a.Unfolded(effective, WeightedEffectiveDef),
				"the support of D is finite",
				"and lies in S, at points of positive weight")
			within := a.Have(
				"the raised divisor vanishes off x and the support of D",
				"fun_support(0, λy:A. «raised»(y)) ⊆ insert(x, fun_support(0, D))",
				BySets(nat_arith.AddZero))
			raisedFinite := a.Have(
				"so it is finitely supported",
				"finite(fun_support(0, λy:A. «raised»(y)))",
				By(
					within,
					support[0],
					finite_set.FiniteInsert.At(x, a.TermAs[Set[A]]("fun_support(0, D)")),
					finite_set.FiniteSubset))
			raisedEffective := a.Have(
				"and effective: where it does not vanish is x or a point "+
					"of D's support, both points of S of positive weight",
				"weighted_effective(S, w, «raised»)",
				Unfold(WeightedEffectiveDef),
				By(raisedFinite, support[1], xInS, positive, nat_arith.AddZero))
			sameCleared := a.Have(
				"cleared at x, the raised divisor is D cleared at x",
				"(λy:A. COND(y = x, 0, «raised»(y))) = (λy:A. COND(y = x, 0, D(y)))",
				Funext(),
				By(nat_arith.AddZero))
			a.Show(
				"both degrees split at x over D cleared at x, and the terms at x differ by w(x)·k",
				ByArith(
					support[0],
					raisedFinite,
					raisedEffective,
					sameCleared,
					WeightedDegreeSplit.At(w, D, x),
					WeightedDegreeSplit.At(w, a.TermAs[Fun[A, Nat]]("«raised»"), x)))
		}),
})}
