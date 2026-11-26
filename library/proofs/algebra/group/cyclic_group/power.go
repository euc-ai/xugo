// power.go — the order of an element of a group on a set, and the
// powers of the element it governs.

package cyclic_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// OrderLeast — when x has a positive period n, its order is a positive
// period too, and at most n: the positive periods have a least one by
// well-ordering, so the choice the order is defined by is a positive
// period at most every other, and the definition's condition holds.
var OrderLeast = orderLeastThm{family.Add(registry.ProofEntry{
	Name: "OrderLeast",
	Key:  "prop_5c57802c051722a0",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀x:A. ∀n:num.",
		Hypotheses: []string{
			"0 < n",
			"monoid_pow(G.mul, G.one, x, n) = G.one",
		},
		Conclusion: "0 < group_element_order(G, x) ∧ " +
			"monoid_pow(G.mul, G.one, x, group_element_order(G, x)) = G.one ∧ " +
			"group_element_order(G, x) ≤ n",
	},
		func(a *Argument, G *Expr[GroupOps[A]], x *Expr[A], n *Expr[Nat], positive, period Fact) {
			some := a.Have(
				"x has a positive period",
				"∃k:num. 0 < k ∧ monoid_pow(G.mul, G.one, x, k) = G.one",
				By(positive, period))
			e, least := a.ObtainAs[Nat](
				"so its positive periods have a least one, e",
				"∃e:num. "+
					"    0 < e ∧ "+
					"    monoid_pow(G.mul, G.one, x, e) = G.one ∧ "+
					"    (∀m:num. m < e ⇒ ¬(0 < m ∧ monoid_pow(G.mul, G.one, x, m) = G.one))",
				By(
					some,
					nat_order.WellOrdering.At(
						a.TermAs[Set[Nat]]("λk:num. 0 < k ∧ monoid_pow(G.mul, G.one, x, k) = G.one"))))
			leastExists := a.Have(
				"so some positive period is at most every positive period — e is one",
				"∃k:num. "+
					"    0 < k ∧ "+
					"    monoid_pow(G.mul, G.one, x, k) = G.one ∧ "+
					"    (∀d:num. 0 < d ∧ monoid_pow(G.mul, G.one, x, d) = G.one ⇒ k ≤ d)",
				Witness(e),
				By(least, nat_order.NotLessThan))
			a.Show(
				"the order is the choice among such periods, x having a positive period",
				Simp(Fwd(GroupElementOrderDef)),
				By(leastExists, positive, period))
		}),
})}

// PowOrderIsOne — x to the power of its order is the identity: when x
// has a positive period, the order is one (OrderLeast); when it has
// none, the order is 0, and x ^ 0 is the identity.
var PowOrderIsOne = powOrderIsOneThm{family.Add(registry.ProofEntry{
	Name: "PowOrderIsOne",
	Key:  "prop_f5ba2e0ae3c13f51",
	Build: family.Theorem("∀G:group_ops(A). ∀x:A. "+
		"    monoid_pow(G.mul, G.one, x, group_element_order(G, x)) = G.one",
		func(a *Argument, G *Expr[GroupOps[A]], x *Expr[A]) {
			a.Cases(a.Term("∃n:num. 0 < n ∧ monoid_pow(G.mul, G.one, x, n) = G.one"))
			a.When(
				"x has a positive period n, so its order is a period",
				func(b *Argument, some Fact) {
					_, period := b.UnpackAs[Nat](some)
					b.Show(
						"the order is a positive period at most n",
						By(period, OrderLeast))
				})
			a.Otherwise(
				"x has no positive period, so its order is 0, and x ^ 0 is the identity",
				Simp(Fwd(GroupElementOrderDef), Fwd(comm_monoid.MonoidPowDef)),
				Refl())
		}),
})}

// PowOrderMulIsOne — every multiple of the order is a period:
// x ^ (ord · k) is (x ^ ord) ^ k, a power of the identity.
var PowOrderMulIsOne = powOrderMulIsOneThm{family.Add(registry.ProofEntry{
	Name: "PowOrderMulIsOne",
	Key:  "prop_c413f2dfcdb8b3e9",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A. ∀k:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "monoid_pow(G.mul, G.one, x, group_element_order(G, x) * k) = G.one",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], k *Expr[Nat]) {
			a.Show(
				"x ^ (ord · k) is a power of x ^ ord, which is the identity",
				CalcEq(
					Leg(
						a.TermAs[A]("monoid_pow(G.mul, G.one, monoid_pow(G.mul, G.one, x, group_element_order(G, x)), k)"),
						"a power of a power",
						By(group.PowPow, grp, x)),
					Leg(
						a.TermAs[A]("monoid_pow(G.mul, G.one, G.one, k)"),
						"x to its order is the identity",
						Simp(Fwd(PowOrderIsOne)),
						Basic()),
					FinalLeg(
						"and so are the identity's powers",
						By(group.OnePow, grp)),
				))
		}),
})}

// PowRemOrder — a power of a member depends only on the exponent's
// remainder by the order: n is a multiple ord · q of the order plus that
// remainder, and the multiple is a period (PowOrderMulIsOne). By 0 the
// remainder is n itself.
var PowRemOrder = powRemOrderThm{family.Add(registry.ProofEntry{
	Name: "PowRemOrder",
	Key:  "prop_42524e551566ca0a",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "monoid_pow(G.mul, G.one, x, n) = " +
			"monoid_pow(G.mul, G.one, x, rem(n, group_element_order(G, x)))",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], n *Expr[Nat]) {
			order := a.TermAs[Nat]("group_element_order(G, x)")
			nonzero := a.Unless(
				a.TermAs[Bool]("group_element_order(G, x) = 0"),
				"the remainder by 0 is n itself",
				Given(func(b *Argument, zero Fact) {
					b.Do(By(zero, nat_div_mod.ModZero))
				}))
			division := a.Have(
				"n is a multiple of the order plus its remainder",
				"n = "+
					"group_element_order(G, x) * div(n, group_element_order(G, x)) + rem(n, group_element_order(G, x))",
				ByArith(nonzero, nat_div_mod.Division.At(n, order)))
			a.LetAs[Nat]("q", "div(n, group_element_order(G, x))")
			a.LetAs[Nat]("r", "rem(n, group_element_order(G, x))")
			a.Show(
				"x ^ n is x ^ (ord · q) * x ^ r, and the first factor is the identity",
				CalcEq(
					Leg(
						a.TermAs[A]("monoid_pow(G.mul, G.one, x, group_element_order(G, x) * q + r)"),
						"n is ord · q + r",
						division.Rw(),
						Basic()),
					Leg(
						a.TermAs[A](
							"monoid_pow(G.mul, G.one, x, group_element_order(G, x) * q) * monoid_pow(G.mul, G.one, x, r)"),
						"exponents add",
						By(group.PowAdd, grp, x)),
					Leg(
						a.TermAs[A]("G.one * monoid_pow(G.mul, G.one, x, r)"),
						"ord · q, a multiple of the order, is a period",
						Simp(Fwd(PowOrderMulIsOne)),
						Basic()),
					FinalLeg(
						"and the identity drops off",
						By(group.LeftIdentityOn, grp, x, group.PowIn)),
				))
		}),
})}

// OrderDividesIff — a power of a member is the identity exactly when the
// exponent is a multiple of the order. The power depends only on the
// exponent's remainder by the order (PowRemOrder), which is 0 for a
// multiple; and the remainder of a period is a period too, which the
// order's minimality forces to be 0, being below the order.
var OrderDividesIff = orderDividesIffThm{family.Add(registry.ProofEntry{
	Name: "OrderDividesIff",
	Key:  "prop_27d7e0680bbd9a34",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "monoid_pow(G.mul, G.one, x, n) = G.one ⇔ group_element_order(G, x) ∣ n",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], n *Expr[Nat]) {
			G := a.TermAs[GroupOps[A]]("G")
			order := a.TermAs[Nat]("group_element_order(G, x)")
			remainder := a.TermAs[Nat]("rem(n, group_element_order(G, x))")
			a.Iff()
			a.Backward(
				"a multiple of the order leaves remainder 0, and x ^ 0 is the identity",
				func(b *Argument, divides Fact) {
					b.Show(
						"x ^ n is x to its remainder by the order",
						By(divides, nat_divides.DividesMod, PowRemOrder.Read(grp).At(x, n), comm_monoid.MonoidPowDef))
				})
			a.Forward(
				"a period is a multiple of the order",
				func(b *Argument, period Fact) {
					remainderPeriod := b.Have(
						"the remainder of n by the order is a period too",
						"monoid_pow(G.mul, G.one, x, rem(n, group_element_order(G, x))) = G.one",
						By(period, PowRemOrder.Read(grp).At(x, n)))
					b.Cases(b.Term("rem(n, group_element_order(G, x)) = 0"))
					b.When(
						"no remainder: the order divides n",
						func(c *Argument, zero Fact) {
							c.Show(
								"a zero remainder is divisibility",
								By(zero, nat_divides.DividesMod))
						})
					b.Otherwise(
						"a positive remainder would be a period below the order",
						func(c *Argument, nonzero Fact) {
							c.Show(
								"the order is positive and at most the remainder, which is below it",
								ByArith(
									nonzero,
									remainderPeriod,
									OrderLeast.At(G, x, remainder),
									nat_div_mod.Division.At(n, order)))
						})
				})
		}),
})}

// OrderAtMostGap — two equal powers x ^ i = x ^ j at distinct exponents
// make the gap between them a positive period, so the order of x is
// positive and at most that gap: for m < n, writing n = m + suc(d),
// x ^ m * x ^ suc(d) is x ^ n = x ^ m, and x ^ m cancels.
var OrderAtMostGap = orderAtMostGapThm{family.Add(registry.ProofEntry{
	Name: "OrderAtMostGap",
	Key:  "prop_af438afd99c2cb8f",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A. ∀i j:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"i ≠ j",
			"monoid_pow(G.mul, G.one, x, i) = monoid_pow(G.mul, G.one, x, j)",
		},
		Conclusion: "0 < group_element_order(G, x) ∧ " +
			"(group_element_order(G, x) ≤ j - i ∨ group_element_order(G, x) ≤ i - j)",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			x *Member[A, on.G],
			i, j *Expr[Nat],
			distinct, equal Fact,
		) {
			G := a.TermAs[GroupOps[A]]("G")
			ordered := a.Have(
				"for exponents m < n with equal powers, the gap n − m is a positive period",
				Statement{
					Binders: "∀m n:num.",
					Hypotheses: []string{
						"m < n",
						"monoid_pow(G.mul, G.one, x, m) = monoid_pow(G.mul, G.one, x, n)",
					},
					Conclusion: "0 < group_element_order(G, x) ∧ group_element_order(G, x) ≤ n - m",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					b.FixAs[Nat]("n")
					given := b.Conjuncts(
						b.Assume(),
						"m is below n",
						"x ^ m = x ^ n")
					_, gap := b.ObtainAs[Nat](
						"write n as m + suc(d)",
						"∃d:num. n = m + suc(d)",
						By(given[0], nat_order.LessThanExists))
					cancellable := b.Have(
						"x ^ m * x ^ suc(d) is x ^ n, which is x ^ m",
						"monoid_pow(G.mul, G.one, x, m) * monoid_pow(G.mul, G.one, x, suc(d)) = "+
							"monoid_pow(G.mul, G.one, x, m) * G.one",
						CalcEq(
							Leg(
								b.TermAs[A]("monoid_pow(G.mul, G.one, x, m + suc(d))"),
								"exponents add",
								By(group.PowAdd, grp, x)),
							Leg(
								b.TermAs[A]("monoid_pow(G.mul, G.one, x, n)"),
								"m + suc(d) is n",
								gap.Rw(),
								Basic()),
							Leg(
								b.TermAs[A]("monoid_pow(G.mul, G.one, x, m)"),
								"the two powers agree",
								By(given[1])),
							FinalLeg(
								"the identity on the right changes nothing",
								By(group.RightIdentityOn, grp, x, group.PowIn)),
						))
					period := b.Have(
						"so x ^ m cancels, and the gap suc(d) is a period",
						"monoid_pow(G.mul, G.one, x, suc(d)) = G.one",
						By(cancellable, group.LeftCancelOn, grp, x, group.PowIn, group.OneIn))
					b.Show(
						"the order is positive and at most suc(d), which is n − m",
						ByArith(gap, period, OrderLeast.At(G, x, b.TermAs[Nat]("suc(d)"))))
				}))
			a.Show(
				"whichever of i and j is smaller, the gap between them is a positive period",
				ByArith(distinct, equal, ordered.At(i, j), ordered.At(j, i)))
		}),
})}

// PowersBelowOrderInjective — the powers of a member at exponents below its
// order are distinct: two of them that agree would leave a positive period
// below the order (OrderAtMostGap).
var PowersBelowOrderInjective = powersBelowOrderInjectiveThm{family.Add(registry.ProofEntry{
	Name: "PowersBelowOrderInjective",
	Key:  "prop_626108f4248f464a",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "injective_on({k:num | k < group_element_order(G, x)}, " +
			"    λk:num. monoid_pow(G.mul, G.one, x, k))",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G]) {
			a.Do(Unfold(functions.InjectiveOnDef))
			i := a.FixAs[Nat]("i")
			j := a.FixAs[Nat]("j")
			parts := a.Conjuncts(
				a.Assume(),
				"i is below the order",
				"so is j",
				"x ^ i = x ^ j")
			a.Show(
				"were i and j distinct, the gap between them would be a positive period below the order",
				ByArith(parts[0], parts[1], parts[2], OrderAtMostGap.Read(grp).At(x, i, j)))
		}),
})}

// FiniteOrderPositive — in a finite group every element has positive
// order: the card(G.carrier) + 1 powers x ^ 0, …, x ^ card(G.carrier) lie
// in the carrier, so two of them coincide (pigeonhole), and the gap
// between their exponents is a positive period (OrderAtMostGap).
var FiniteOrderPositive = finiteOrderPositiveThm{family.Add(registry.ProofEntry{
	Name: "FiniteOrderPositive",
	Key:  "prop_3fec37fd814f6cf9",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"finite(G.carrier)",
		},
		Conclusion: "0 < group_element_order(G, x)",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], finite Fact) {
			i, j, collision := a.Obtain2As[Nat, Nat](
				"two of the powers x ^ 0, …, x ^ card(G.carrier) coincide, all lying in the carrier",
				"∃i j:num. "+
					"    i ≤ card(G.carrier) ∧ "+
					"    j ≤ card(G.carrier) ∧ "+
					"    i ≠ j ∧ "+
					"    monoid_pow(G.mul, G.one, x, i) = monoid_pow(G.mul, G.one, x, j)",
				By(
					grp,
					x,
					finite,
					num_segment.FiniteRangeRepeats.At(
						a.TermAs[Set[A]]("G.carrier"),
						a.TermAs[Fun[Nat, A]]("λk:num. monoid_pow(G.mul, G.one, x, k)"),
						a.TermAs[Nat]("card(G.carrier)")),
					group.PowIn,
					nat_order.LessEqRefl))
			a.Show(
				"the gap between i and j is a positive period",
				ByArith(collision, OrderAtMostGap.Read(grp).At(x, i, j)))
		}),
})}
