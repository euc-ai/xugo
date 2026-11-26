// cyclic_subgroup.go — the subgroup an element generates, and its size.

package cyclic_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// CyclicSubgroupSubgroup — the powers of a member and their inverses form
// a subgroup. The identity is x ^ 0 and the inverse of an inverse is the
// power itself. Of the four kinds of product, two powers make a power and
// two inverses the inverse of a power; in a mixed product the larger
// exponent is the smaller one plus a gap d, and what is left is x ^ d or
// its inverse.
var CyclicSubgroupSubgroup = cyclicSubgroupSubgroupThm{family.Add(registry.ProofEntry{
	Name: "CyclicSubgroupSubgroup",
	Key:  "prop_e0d24e7a0af889ca",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "subgroup(G, cyclic_subgroup(G, x))",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G]) {
			powers := a.Have(
				"it holds every power of x",
				"∀n:num. monoid_pow(G.mul, G.one, x, n) ∈ cyclic_subgroup(G, x)",
				Unfold(CyclicSubgroupDef),
				BySets())
			inverses := a.Have(
				"and the inverse of every power",
				"∀n:num. G.inv(monoid_pow(G.mul, G.one, x, n)) ∈ cyclic_subgroup(G, x)",
				Unfold(CyclicSubgroupDef),
				BySets())
			powerProducts := a.Have(
				"a product of two powers is a power",
				"∀m n:num. monoid_pow(G.mul, G.one, x, m) * monoid_pow(G.mul, G.one, x, n) ∈ cyclic_subgroup(G, x)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					b.FixAs[Nat]("n")
					b.Show(
						"x ^ m * x ^ n is x ^ (m + n)",
						Simp(Rev(group.PowAdd)),
						By(powers))
				}))
			inverseProducts := a.Have(
				"a product of two inverse powers is the inverse of a power",
				"∀m n:num. "+
					"    G.inv(monoid_pow(G.mul, G.one, x, m)) * G.inv(monoid_pow(G.mul, G.one, x, n)) ∈ "+
					"    cyclic_subgroup(G, x)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					b.FixAs[Nat]("n")
					b.Show(
						"G.inv(x ^ m) * G.inv(x ^ n) is G.inv(x ^ n * x ^ m), the inverse of x ^ (n + m)",
						Simp(Rev(group.InvMulOn), Fwd(group.PowIn), Rev(group.PowAdd)),
						By(inverses))
				}))
			powerTimesInverse := a.Have(
				"a power times an inverse power is one or the other",
				"∀m n:num. "+
					"    monoid_pow(G.mul, G.one, x, m) * G.inv(monoid_pow(G.mul, G.one, x, n)) ∈ "+
					"    cyclic_subgroup(G, x)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					b.FixAs[Nat]("n")
					b.Cases(b.Term("n ≤ m"))
					b.When(
						"m = d + n: x ^ n cancels, leaving x ^ d",
						func(c *Argument, smaller Fact) {
							_, split := c.ObtainAs[Nat](
								"write m as d + n",
								"∃d:num. m = d + n",
								Witness(c.Term("m - n")),
								ByArith(smaller))
							c.Show(
								"x ^ d * x ^ n * G.inv(x ^ n) is x ^ d",
								split.Rw(),
								Simp(Fwd(group.PowAdd), Fwd(group.MulInvCancelRightOn), Fwd(group.PowIn), Fwd(group.InvIn)),
								By(powers))
						})
					b.Otherwise(
						"n = d + m: x ^ m cancels, leaving the inverse of x ^ d",
						func(c *Argument, larger Fact) {
							_, split := c.ObtainAs[Nat](
								"write n as d + m",
								"∃d:num. n = d + m",
								Witness(c.Term("n - m")),
								ByArith(larger))
							c.Show(
								"x ^ m * (G.inv(x ^ m) * G.inv(x ^ d)) is G.inv(x ^ d)",
								split.Rw(),
								Simp(
									Fwd(group.PowAdd),
									Fwd(group.InvMulOn),
									Fwd(group.MulInvCancelLeftOn),
									Fwd(group.PowIn),
									Fwd(group.InvIn)),
								By(inverses))
						})
				}))
			inverseTimesPower := a.Have(
				"an inverse power times a power is one or the other",
				"∀m n:num. "+
					"    G.inv(monoid_pow(G.mul, G.one, x, m)) * monoid_pow(G.mul, G.one, x, n) ∈ "+
					"    cyclic_subgroup(G, x)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					b.FixAs[Nat]("n")
					b.Cases(b.Term("m ≤ n"))
					b.When(
						"n = m + d: x ^ m cancels, leaving x ^ d",
						func(c *Argument, smaller Fact) {
							_, split := c.ObtainAs[Nat](
								"write n as m + d",
								"∃d:num. n = m + d",
								Witness(c.Term("n - m")),
								ByArith(smaller))
							c.Show(
								"G.inv(x ^ m) * (x ^ m * x ^ d) is x ^ d",
								split.Rw(),
								Simp(Fwd(group.PowAdd), Fwd(group.InvMulCancelLeftOn), Fwd(group.PowIn)),
								By(powers))
						})
					b.Otherwise(
						"m = n + d: x ^ n cancels, leaving the inverse of x ^ d",
						func(c *Argument, larger Fact) {
							_, split := c.ObtainAs[Nat](
								"write m as n + d",
								"∃d:num. m = n + d",
								Witness(c.Term("m - n")),
								ByArith(larger))
							c.Show(
								"G.inv(x ^ d) * G.inv(x ^ n) * x ^ n is G.inv(x ^ d)",
								split.Rw(),
								Simp(
									Fwd(group.PowAdd),
									Fwd(group.InvMulOn),
									Fwd(group.InvMulCancelRightOn),
									Fwd(group.PowIn),
									Fwd(group.InvIn)),
								By(inverses))
						})
				}))
			a.Show(
				"so it is a subgroup",
				Unfold(group.SubgroupDef),
				Unfold(set_basic.SubsetDef),
				SplitConjAll(
					Case(
						"it lies in the carrier: so do the powers of x and their inverses",
						Derive(func(b *Argument) {
							b.FixAs[A]("y")
							member := b.Assume()
							_, form := b.UnpackAs[Nat](b.Unfolded(member, CyclicSubgroupDef), "n")
							b.Show(
								"y is x ^ n or its inverse",
								By(form, grp, x, group.PowIn, group.InvIn))
						})),
					Case(
						"it holds G.one, which is x ^ 0",
						By(powers, comm_monoid.MonoidPowDef)),
					Case(
						"it is closed under the product: each of the four kinds of product is in it",
						Derive(func(b *Argument) {
							b.FixAs[A]("y")
							b.FixAs[A]("z")
							both := b.Assume()
							members := b.Conjuncts(
								both,
								"y lies in it",
								"so does z")
							m, yForm := b.UnpackAs[Nat](b.Unfolded(members[0], CyclicSubgroupDef), "m")
							n, zForm := b.UnpackAs[Nat](b.Unfolded(members[1], CyclicSubgroupDef), "n")
							b.Show(
								"y is x ^ m or its inverse, and z is x ^ n or its inverse",
								By(
									yForm,
									zForm,
									powerProducts.At(m, n),
									powerTimesInverse.At(m, n),
									inverseTimesPower.At(m, n),
									inverseProducts.At(m, n)))
						})),
					Case(
						"and under the inverse: the inverse of an inverse power is the power",
						Derive(func(b *Argument) {
							b.FixAs[A]("y")
							member := b.Assume()
							n, form := b.UnpackAs[Nat](b.Unfolded(member, CyclicSubgroupDef), "n")
							b.Show(
								"y is x ^ n or its inverse",
								By(form, grp, x, powers.At(n), inverses.At(n), group.InvInvOn, group.PowIn))
						}))))
		}),
})}

// CyclicSubgroupPowersBelowOrder — when x has positive order, the subgroup
// it generates is its powers below the order: a power depends only on the
// exponent's remainder by the order (PowRemOrder), and the inverse of x ^ n
// is the power x ^ (ord · n − n), the two multiplying to x ^ (ord · n),
// a period.
var CyclicSubgroupPowersBelowOrder = cyclicSubgroupPowersBelowOrderThm{family.Add(registry.ProofEntry{
	Name: "CyclicSubgroupPowersBelowOrder",
	Key:  "prop_236a1cc4f066ec51",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"0 < group_element_order(G, x)",
		},
		Conclusion: "cyclic_subgroup(G, x) = " +
			"image(λk:num. monoid_pow(G.mul, G.one, x, k), {k:num | k < group_element_order(G, x)})",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], positive Fact) {
			order := a.TermAs[Nat]("group_element_order(G, x)")
			below := a.Have(
				"every power of x is a power below the order",
				"∀n:num. ∃k:num. "+
					"    k < group_element_order(G, x) ∧ "+
					"    monoid_pow(G.mul, G.one, x, n) = monoid_pow(G.mul, G.one, x, k)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Take(b.TermAs[Nat]("rem(n, group_element_order(G, x))"))
					b.Show(
						"x ^ n is x to its remainder by the order, which is below the order",
						By(
							positive,
							PowRemOrder.Read(grp).At(x, n),
							nat_div_mod.Division.At(n, order),
							nat_order.PosIffNonzero))
				}))
			inverse := a.Have(
				"the inverse of a power is a power",
				"∀n:num. "+
					"    G.inv(monoid_pow(G.mul, G.one, x, n)) = "+
					"    monoid_pow(G.mul, G.one, x, group_element_order(G, x) * n - n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					exponent := b.Have(
						"n is at most ord · n, the order being positive",
						"group_element_order(G, x) * n - n + n = group_element_order(G, x) * n",
						ByArith(positive, nat_order.LessEqSelfMul.At(n, order)))
					product := b.Have(
						"x ^ (ord · n − n) times x ^ n is x ^ (ord · n), a period",
						"monoid_pow(G.mul, G.one, x, group_element_order(G, x) * n - n) * "+
							"monoid_pow(G.mul, G.one, x, n) = "+
							"G.one",
						CalcEq(
							Leg(
								b.TermAs[A]("monoid_pow(G.mul, G.one, x, group_element_order(G, x) * n - n + n)"),
								"exponents add",
								By(group.PowAdd, grp, x)),
							Leg(
								b.TermAs[A]("monoid_pow(G.mul, G.one, x, group_element_order(G, x) * n)"),
								"the exponent is ord · n",
								exponent.Rw(),
								Basic()),
							FinalLeg(
								"a multiple of the order is a period",
								By(PowOrderMulIsOne, grp, x)),
						))
					b.Show(
						"so x ^ (ord · n − n) is the inverse of x ^ n",
						By(product, group.InvUniqueOn, grp, x, group.PowIn))
				}))
			a.Show(
				"so both sides hold exactly the powers of x below the order",
				Unfold(CyclicSubgroupDef),
				BySets(below, inverse))
		}),
})}

// CardCyclicSubgroup — when x has positive order, the subgroup it
// generates has as many elements as the order: it is the image of the
// exponents below the order (CyclicSubgroupPowersBelowOrder), at which the
// powers are distinct (PowersBelowOrderInjective).
var CardCyclicSubgroup = cardCyclicSubgroupThm{family.Add(registry.ProofEntry{
	Name: "CardCyclicSubgroup",
	Key:  "prop_2f69f0540807aeaf",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"0 < group_element_order(G, x)",
		},
		Conclusion: "has_size(cyclic_subgroup(G, x), group_element_order(G, x))",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], positive Fact) {
			a.Show(
				"the subgroup is the image of the order's many exponents, taken one to one",
				Simp(Fwd(CyclicSubgroupPowersBelowOrder)),
				By(
					PowersBelowOrderInjective.Read(grp).At(x),
					cardinality.HasSizeImageInj,
					num_segment.HasSizeBelowStrict))
		}),
})}

// OrderDividesCard — in a finite group every element has a positive order
// dividing the group's size: the order is positive (FiniteOrderPositive),
// the element generates a subgroup with as many elements as the order
// (CardCyclicSubgroup), and the size of a subgroup divides the size of the
// group (finite_group.LagrangeDividesOn).
var OrderDividesCard = orderDividesCardThm{family.Add(registry.ProofEntry{
	Name: "OrderDividesCard",
	Key:  "prop_3dced9132db7c81f",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"finite(G.carrier)",
		},
		Conclusion: "0 < group_element_order(G, x) ∧ group_element_order(G, x) ∣ card(G.carrier)",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], finite Fact) {
			positive := a.Have(
				"x has positive order, the group being finite",
				"0 < group_element_order(G, x)",
				By(FiniteOrderPositive, grp, x, finite))
			size := a.Have(
				"x generates a subgroup with as many elements as the order",
				"card(cyclic_subgroup(G, x)) = group_element_order(G, x)",
				By(CardCyclicSubgroup, grp, x, positive, cardinality.CardOfSized))
			a.Show(
				"by Lagrange, the size of that subgroup divides the size of the group",
				By(
					Normalized,
					positive,
					size,
					finite_group.LagrangeDividesOn.Read(grp).At(a.TermAs[Set[A]]("cyclic_subgroup(G, x)")),
					CyclicSubgroupSubgroup.Read(grp).At(x),
					finite))
		}),
})}

// PowCardIsOne — in a finite group a member raised to the group's size is
// the identity: the order divides the size (OrderDividesCard), and the
// multiples of the order are periods (OrderDividesIff).
var PowCardIsOne = powCardIsOneThm{family.Add(registry.ProofEntry{
	Name: "PowCardIsOne",
	Key:  "prop_5c3becd36a4317cd",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"finite(G.carrier)",
		},
		Conclusion: "monoid_pow(G.mul, G.one, x, card(G.carrier)) = G.one",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], finite Fact) {
			a.Show(
				"the order divides the size of the group, and its multiples are periods",
				By(grp, x, finite, OrderDividesCard, OrderDividesIff))
		}),
})}
