// criterion.go — the elements of each order, and two criteria for a
// finite group to be cyclic: an element whose order is the group's size,
// and the count of the solutions of x ^ d = 1.

package cyclic_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// OrderOfPowerCoprime — for x of positive order d, the power x ^ k has order
// d exactly when k is coprime to d. Its periods m are those with d ∣ k · m.
// When k is coprime to d, the order e of x ^ k divides d, d dividing k · d,
// and d divides e, dividing k · e; so e = d. When e = d, write k = g · c and
// d = g · q for g = gcd(k, d): then d divides k · q = d · c, so d divides q,
// which divides d; so q = d, and g · d = d forces g = 1.
var OrderOfPowerCoprime = orderOfPowerCoprimeThm{family.Add(registry.ProofEntry{
	Name: "OrderOfPowerCoprime",
	Key:  "prop_74363f58f9cdc6aa",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A. ∀k:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"0 < group_element_order(G, x)",
		},
		Conclusion: "group_element_order(G, monoid_pow(G.mul, G.one, x, k)) = " +
			"group_element_order(G, x) ⇔ " +
			"nat_coprime(k, group_element_order(G, x))",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], k *Expr[Nat], positive Fact) {
			divides := a.Have(
				"(x ^ k) ^ m is x ^ (k · m): the order of x ^ k "+
					"divides m exactly when the order of x divides k · m",
				"∀m:num. "+
					"    group_element_order(G, monoid_pow(G.mul, G.one, x, k)) ∣ m ⇔ "+
					"    group_element_order(G, x) ∣ k * m",
				a.ForEach(func(m *Expr[Nat]) Action {
					return By(
						grp,
						x,
						group.PowPow,
						OrderDividesIff,
						OrderDividesIff.Read(grp).At(group.PowIn.Read(grp).At(x, k), m))
				}))
			d, _ := a.LetAs[Nat]("d", "group_element_order(G, x)")
			e, _ := a.LetAs[Nat]("e", "group_element_order(G, monoid_pow(G.mul, G.one, x, k))")
			a.Iff()
			a.Backward(
				"k coprime to d: e and d divide each other",
				func(b *Argument, coprime Fact) {
					eDividesD := b.Have(
						"d divides k · d, so e divides d",
						"e ∣ d",
						By(divides.At(d), nat_divides.DividesOwnMultiple.At(d, k)))
					dDividesE := b.Have(
						"d divides k · e and is coprime to k, so d divides e",
						"d ∣ e",
						By(
							divides.At(e),
							coprime,
							nat_divides.DividesRefl.At(e),
							nat_gcd.CoprimeSym.At(k, d),
							nat_arith.MulSym.At(k, e),
							nat_gcd.CoprimeCancel.At(d, e, k)))
					b.Show(
						"so e = d",
						By(eDividesD, dDividesE, nat_divides.DividesAntisym))
				})
			a.Forward(
				"e = d: the gcd of k and d is 1",
				func(b *Argument, same Fact) {
					g, gDef := b.LetAs[Nat]("g", "nat_gcd(k, d)")
					c, kFactor := b.ObtainAs[Nat](
						"k is a multiple of g, the gcd of k and d",
						"∃c:num. k = g * c",
						By(gDef, nat_gcd.Gcd.At(k, d), nat_divides.DividesFactor))
					q, dFactor := b.ObtainAs[Nat](
						"and so is d",
						"∃q:num. d = g * q",
						By(gDef, nat_gcd.Gcd.At(k, d), nat_divides.DividesFactor))
					product := b.Have(
						"k · q and d · c are both g · c · q",
						"k * q = d * c",
						ByArith(Scaled(q, kFactor), Scaled(c, dFactor)))
					cofactor := b.Have(
						"so d divides k · q, and e = d divides q, which divides d: q = d",
						"q = d",
						By(
							divides.At(q),
							same,
							product,
							nat_divides.DividesOwnMultiple.At(d, c),
							dFactor,
							nat_divides.DividesOwnMultiple.At(q, g),
							nat_divides.DividesAntisym.At(q, d)))
					b.Show(
						"g · d = d with d positive leaves g = 1",
						By(
							positive,
							cofactor,
							dFactor,
							gDef,
							nat_gcd.CoprimeDef.At(k, d),
							nat_arith.MulEqLCancel.At(d, g, b.TermAs[Nat]("1")),
							nat_arith.MulSym.At(d, g),
							nat_arith.MulOne.At(d),
							nat_order.PosIffNonzero.At(d)))
				})
		}),
})}

// ElementsOfOrderInCyclic — for x of positive order d, the subgroup x
// generates holds φ(d) elements of order d: they are the powers x ^ k with k
// below d and coprime to d (CyclicSubgroupPowersBelowOrder,
// OrderOfPowerCoprime), which are distinct, as all the powers below d are
// (PowersBelowOrderInjective).
var ElementsOfOrderInCyclic = elementsOfOrderInCyclicThm{family.Add(registry.ProofEntry{
	Name: "ElementsOfOrderInCyclic",
	Key:  "prop_a31ad160f4424ccb",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"0 < group_element_order(G, x)",
		},
		Conclusion: "has_size(«generators», totient(group_element_order(G, x)))",
		Abbrev: Abbrev{
			{Name: "generators", Text: "{y:A | " +
				"    y ∈ cyclic_subgroup(G, x) ∧ group_element_order(G, y) = group_element_order(G, x)}"},
			{Name: "coprimeExponents", Text: "{k:num | " +
				"    k < group_element_order(G, x) ∧ nat_coprime(k, group_element_order(G, x))}"},
		},
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], positive Fact) {
			order := a.TermAs[Nat]("group_element_order(G, x)")
			ofFullOrder := a.Have(
				"the elements of the subgroup with the order of x are "+
					"the powers x ^ k, k below the order and coprime to it",
				"«generators» = image(λk:num. monoid_pow(G.mul, G.one, x, k), «coprimeExponents»)",
				Simp(Fwd(CyclicSubgroupPowersBelowOrder)),
				BySets(OrderOfPowerCoprime.Read(grp), x, positive))
			below := a.Have(
				"those exponents are below the order",
				"«coprimeExponents» ⊆ {k:num | k < group_element_order(G, x)}",
				BySets())
			distinct := a.Have(
				"so the powers there are distinct, as all the powers below the order are",
				"injective_on(«coprimeExponents», λk:num. monoid_pow(G.mul, G.one, x, k))",
				By(
					below,
					PowersBelowOrderInjective.Read(grp).At(x),
					functions.InjectiveOnSubset.At(
						a.TermAs[Fun[Nat, A]]("λk:num. monoid_pow(G.mul, G.one, x, k)"),
						a.TermAs[Set[Nat]]("«coprimeExponents»"),
						a.TermAs[Set[Nat]]("{k:num | k < group_element_order(G, x)}"))))
			a.Show(
				"so they are as many as the residues below the order coprime to it: φ of the order",
				ofFullOrder.Rw(),
				By(distinct, cardinality.HasSizeImageInj, totient.TotientHasSize.At(order)))
		}),
})}

// ElementsOfOrderUnderRootBound — for x of order d in a finite group where
// y ^ d = 1 has at most d solutions, the group has φ(d) elements of order d.
// The d elements of the subgroup x generates are powers of x, so all of
// them solve y ^ d = 1; being as many as the solutions can be, they are all
// of them. An element of order d solves it, so it lies in that subgroup, which
// holds φ(d) of them (ElementsOfOrderInCyclic).
var ElementsOfOrderUnderRootBound = elementsOfOrderUnderRootBoundThm{family.Add(registry.ProofEntry{
	Name: "ElementsOfOrderUnderRootBound",
	Key:  "prop_8b88f45628ca2a04",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"finite(G.carrier)",
			"card(«roots») ≤ group_element_order(G, x)",
		},
		Conclusion: "has_size(«ofOrder»(group_element_order(G, x)), totient(group_element_order(G, x)))",
		Abbrev: Abbrev{
			{Name: "ofOrder", Text: "λd:num. {y:A | y ∈ G.carrier ∧ group_element_order(G, y) = d}"},
			{Name: "generators", Text: "{y:A | " +
				"    y ∈ cyclic_subgroup(G, x) ∧ group_element_order(G, y) = group_element_order(G, x)}"},
			{Name: "roots", Text: "{y:A | " +
				"    y ∈ G.carrier ∧ monoid_pow(G.mul, G.one, y, group_element_order(G, x)) = G.one}"},
		},
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], finite, bound Fact) {
			order := a.TermAs[Nat]("group_element_order(G, x)")
			generated := a.TermAs[Set[A]]("cyclic_subgroup(G, x)")
			roots := a.TermAs[Set[A]]("«roots»")
			positive := a.Have(
				"x has positive order, the group being finite",
				"0 < group_element_order(G, x)",
				By(FiniteOrderPositive, grp, x, finite))
			powersAreRoots := a.Have(
				"every power x ^ k solves y ^ d = 1, d the order of x: (x ^ k) ^ d is x ^ (k · d)",
				"∀k:num. "+
					"    monoid_pow(G.mul, G.one, monoid_pow(G.mul, G.one, x, k), group_element_order(G, x)) = G.one",
				a.ForEach(func(k *Expr[Nat]) Action {
					return By(grp, x, group.PowPow, OrderDividesIff, nat_divides.DividesOwnMultiple.At(order, k))
				}))
			inside := a.Have(
				"so the subgroup x generates, the powers of x below its order, lies among the solutions",
				"cyclic_subgroup(G, x) ⊆ «roots»",
				Simp(Fwd(CyclicSubgroupPowersBelowOrder)),
				BySets(grp, x, powersAreRoots, group.PowIn))
			fewer := a.Have(
				"the subgroup has d elements, as many as the solutions can be",
				"card(«roots») ≤ card(cyclic_subgroup(G, x))",
				By(
					bound,
					CardCyclicSubgroup.Read(grp).At(x),
					positive,
					cardinality.CardOfSized.At(generated, order)))
			allRoots := a.Have(
				"so the subgroup, lying among the finitely many solutions, is all of them",
				"cyclic_subgroup(G, x) = «roots»",
				By(
					inside,
					finite,
					finite_set.FiniteRestrict.At(
						a.TermAs[Set[A]]("G.carrier"),
						a.TermAs[Set[A]]("λy:A. monoid_pow(G.mul, G.one, y, group_element_order(G, x)) = G.one")),
					fewer,
					cardinality.CardSubsetLe.At(generated, roots)))
			ofOrder := a.Have(
				"an element of order d solves y ^ d = 1, so it lies in the subgroup",
				"«ofOrder»(group_element_order(G, x)) = «generators»",
				BySets(allRoots, PowOrderIsOne))
			a.Show(
				"and the subgroup holds φ(d) elements of order d",
				ofOrder.Rw(),
				By(ElementsOfOrderInCyclic.Read(grp).At(x), positive))
		}),
})}

// ElementOfFullOrderGenerates — in a finite group an element whose order is
// the group's size generates the group: the subgroup it generates has as
// many elements as its order, so as many as the finite carrier it lies in,
// and is the whole carrier.
var ElementOfFullOrderGenerates = elementOfFullOrderGeneratesThm{family.Add(registry.ProofEntry{
	Name: "ElementOfFullOrderGenerates",
	Key:  "prop_19a7152cad2e6330",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"finite(G.carrier)",
			"group_element_order(G, x) = card(G.carrier)",
		},
		Conclusion: "cyclic_group(G)",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Member[A, on.G], finite, full Fact) {
			generated := a.TermAs[Set[A]]("cyclic_subgroup(G, x)")
			whole := a.Have(
				"the subgroup x generates lies in G and has as many elements as G, which is finite, so it is G",
				"G.carrier = cyclic_subgroup(G, x)",
				By(
					finite,
					full,
					CyclicSubgroupSubgroup.Read(grp).At(x),
					CardCyclicSubgroup.Read(grp).At(x),
					FiniteOrderPositive.Read(grp).At(x),
					group.SubgroupSubset.At(a.TermAs[group.GroupOps[A]]("G"), generated),
					cardinality.HasSizeDef.At(generated, a.TermAs[Nat]("group_element_order(G, x)")),
					cardinality.CardSubsetEq.At(generated, a.TermAs[Set[A]]("G.carrier"))))
			a.Show(
				"so x generates G",
				By(grp, x, whole, CyclicGroupDef))
		}),
})}

// CyclicCriterion — a finite group in which, for every positive d, the
// equation x ^ d = 1 has at most d solutions is cyclic. Sorting the n
// elements by their orders, which divide n, gives n as the sum over the
// divisors d of n of the number of elements of order d; that number is at
// most φ(d) (ElementsOfOrderUnderRootBound, and 0 when no element has order
// d), while the φ(d) themselves also add up to n by Gauss's identity. So the
// number is φ(d) at every divisor (nat_sum.SumLeEqTermwise), at n too:
// φ(n) > 0 elements have order n, and such an element generates the group
// (ElementOfFullOrderGenerates).
var CyclicCriterion = cyclicCriterionThm{family.Add(registry.ProofEntry{
	Name: "CyclicCriterion",
	Key:  "prop_c515b9d8d69b762e",
	Build: group.GroupOn.Law(Statement{
		Hypotheses: []string{
			"finite(G.carrier)",
			"∀d:num. 0 < d ⇒ card({x:A | x ∈ G.carrier ∧ monoid_pow(G.mul, G.one, x, d) = G.one}) ≤ d",
		},
		Conclusion: "cyclic_group(G)",
		Abbrev: Abbrev{
			{Name: "ofOrder", Text: "λd:num. {x:A | x ∈ G.carrier ∧ group_element_order(G, x) = d}"},
			{Name: "divisors", Text: "{d:num | d ∣ card(G.carrier)}"},
		},
	},
		func(a *Argument, grp group.GroupFact[on.G], finite, bound Fact) {
			carrier := a.TermAs[Set[A]]("G.carrier")
			size := a.TermAs[Nat]("card(G.carrier)")
			divisors := a.TermAs[Set[Nat]]("«divisors»")
			count := a.TermAs[Fun[Nat, Nat]]("λd:num. card(«ofOrder»(d))")
			nonempty := a.Have(
				"the group is not empty, holding its identity",
				"0 < card(G.carrier)",
				ByArith(finite, group.OneIn.Read(grp), cardinality.CountsOneMore.At(carrier, a.TermAs[A]("G.one"))))
			termwise := a.Have(
				"for every d, the elements of order d number at most φ(d)",
				"∀d:num. card(«ofOrder»(d)) ≤ totient(d)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					b.Cases(b.Term("∃y:A. y ∈ G.carrier ∧ group_element_order(G, y) = d"))
					b.When(
						"some y has order d: then the elements of order d number φ(d)",
						func(c *Argument, some Fact) {
							y, of := c.UnpackAs[A](some)
							parts := c.Conjuncts(
								of,
								"y lies in the group",
								"with order d")
							ym := c.MemberOf[on.G](y, parts[0])
							yPositive := c.Have(
								"y has positive order, the group being finite",
								"0 < group_element_order(G, y)",
								By(FiniteOrderPositive, grp, ym, finite))
							c.Show(
								"z ^ d = 1 has at most d solutions, d being the order of y, so φ(d) elements have order d",
								parts[1].RwRev(),
								By(
									ElementsOfOrderUnderRootBound.Read(grp).At(ym),
									finite,
									yPositive,
									bound.At(c.TermAs[Nat]("group_element_order(G, y)")),
									cardinality.CardOfSized,
									nat_order.LessEqRefl))
						})
					b.Otherwise(
						"no element has order d: there are none",
						func(c *Argument, none Fact) {
							empty := c.Have(
								"the elements of order d form the empty set",
								"«ofOrder»(d) = ∅",
								BySets(none))
							c.Show(
								"which has no elements",
								ByArith(empty, cardinality.CardClauses))
						})
				}))
			sorted := a.Have(
				"each element has exactly one order, and it divides the size of the group",
				"∀x:A. x ∈ G.carrier ⇒ ∃!d:num. d ∣ card(G.carrier) ∧ group_element_order(G, x) = d",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					xm := b.MemberOf[on.G](x, b.Assume())
					b.Show(
						"by Lagrange's theorem, the order of x divides the size of the group",
						By(grp, xm, finite, OrderDividesCard))
				}))
			sized := a.Have(
				"each class of elements of one order has a size, the carrier being finite",
				"∀d:num. has_size(«ofOrder»(d), card(«ofOrder»(d)))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					b.Show(
						"a part of a finite set is finite",
						By(
							finite,
							finite_set.FiniteRestrict.At(carrier, b.TermAs[Set[A]]("λx:A. group_element_order(G, x) = d")),
							cardinality.FiniteHasSize))
				}))
			partition := a.Have(
				"sorting the elements by their orders: the size of the group "+
					"is the sum, over its divisors d, of the number of order d",
				"card(G.carrier) = sum(«divisors», λd:num. card(«ofOrder»(d)))",
				By(
					finite,
					sorted,
					sized,
					nat_sum.CardByFibres.At(
						carrier,
						divisors,
						a.TermAs[Fun2[A, Nat, Bool]]("λx:A. λd:num. group_element_order(G, x) = d"),
						count)))
			sameSum := a.Have(
				"by Gauss's identity, the totients of the divisors add up to the size of the group as well",
				"sum(«divisors», λd:num. card(«ofOrder»(d))) = sum(«divisors», totient)",
				By(nonempty, partition, totient.DivisorSum.At(size)))
			forced := a.Have(
				"at most φ(d) at every divisor with the same total, "+
					"the count is φ(d) at each, at the size of the group too",
				"card(«ofOrder»(card(G.carrier))) = totient(card(G.carrier))",
				By(
					nonempty,
					nat_divides.DivisorsFinite.At(size),
					termwise,
					sameSum,
					nat_sum.SumLeEqTermwise.At(divisors, count, a.TermAs[Fun[Nat, Nat]]("totient"), size),
					nat_divides.DividesRefl.At(size)))
			fullOrder := a.Have(
				"φ of the size of the group is positive, so some element has the size of the group as its order",
				"«ofOrder»(card(G.carrier)) ≠ ∅",
				By(
					nonempty,
					forced,
					totient.TotientPositive.At(size),
					cardinality.CardClauses,
					nat_order.LessThanIrrefl))
			g, generator := a.ObtainAs[A](
				"take such an element g",
				"∃g:A. g ∈ G.carrier ∧ group_element_order(G, g) = card(G.carrier)",
				BySets(fullOrder))
			parts := a.Conjuncts(
				generator,
				"g lies in the group",
				"and has the size of the group as its order")
			gm := a.MemberOf[on.G](g, parts[0])
			a.Show(
				"an element whose order is the size of the finite group generates it",
				By(ElementOfFullOrderGenerates.Read(grp).At(gm), finite, parts[1]))
		}),
})}
