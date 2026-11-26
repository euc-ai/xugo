// existence.go — subgroups of every prime-power order dividing a finite
// group (Sylow I): a p-subgroup of index divisible by p lies, as a normal
// subgroup, in one p times as large, so a finite group has a subgroup of
// every order p ^ n dividing its own; the Sylow p-subgroups are the
// subgroups of order the full power of p in the order of the group, and
// one exists; a finite group whose order divides a power of a prime is a
// p-group; and a nontrivial p-group has a subgroup of index p.

package sylow

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_action"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// PSubgroupGrowth — a p-subgroup H whose index p divides is a normal
// subgroup of a subgroup p times as large. H acts on its cosets by left
// translation and, being a p-group, fixes as many of them as there are,
// mod p; the cosets it fixes are those of H in its normalizer N, so p divides
// the order of the group N/H. Cauchy's theorem gives a subgroup of order p
// in N/H, and its preimage in N is the subgroup sought.
var PSubgroupGrowth = pSubgroupGrowthThm{family.Add(registry.ProofEntry{
	Name: "PSubgroupGrowth",
	Key:  "prop_208a6c5d0c163c39",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀H:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
			"p_subgroup(G, p, H)",
			"p ∣ card(left_cosets(G.carrier, H))",
		},
		Conclusion: "∃K:set(A). " +
			"    subgroup(G, K) ∧ normal_subgroup(restrict_group(G, K), H) ∧ card(K) = p * card(H)",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], H *Expr[Set[A]],
			finiteG, prime, pSub, index Fact) {
			sub, pGroup := finite_group.PSubgroupSubgroup.Read(pSub), finite_group.PSubgroupPGroup.Read(pSub)
			G := a.TermAs[GroupOps[A]]("G")
			N, nDef := a.LetAs[Set[A]]("N", "group_normalizer(G, H)")
			normal := a.Have(
				"the normalizer N of H is a subgroup of G holding H, and H is normal in N",
				"subgroup(G, N) ∧ H ⊆ N ∧ normal_subgroup(restrict_group(G, N), H)",
				By(Normalized, nDef, sub, group_action.NormalizerSubgroup.Read(grp).At(H)))
			finiteness := a.Have(
				"H and N are subgroups of the finite G, so finite, and the finite G has finitely many cosets of H",
				"finite(H) ∧ finite(N) ∧ finite(left_cosets(G.carrier, H))",
				By(
					finiteG,
					sub,
					normal,
					finite_group.SubgroupFinite.At(G, H),
					finite_group.SubgroupFinite.At(G, N),
					quotient_group.LeftCosetsFinite.At(a.TermAs[Op[A]]("G.mul"), a.TermAs[Set[A]]("G.carrier"), H)))
			translation := a.Have(
				"G acts on the cosets of H by left translation",
				"group_action(G, left_cosets(G.carrier, H), λg:A. λS:set(A). image(G.mul(g), S))",
				By(sub, group_action.CosetAction.Read(grp).At(H)))
			byH := a.Have(
				"and so does its subgroup H",
				"group_action(restrict_group(G, H), "+
					"    left_cosets(G.carrier, H), "+
					"    λg:A. λS:set(A). image(G.mul(g), S))",
				By(sub, group_action.RestrictAction.Read(translation).At(H)))
			congruent := a.Have(
				"H, a p-group, fixes as many cosets as there are, "+
					"mod p, and those it fixes are the cosets of H in N",
				"card(left_cosets(G.carrier, H)) ≡ card(left_cosets(N, H)) (mod p)",
				By(
					nDef,
					finiteness,
					prime,
					pGroup,
					sub,
					group_action.PrimePowerFixedPoints.Read(byH).At(p),
					group_action.FixedCosetsNormalizer.Read(grp).At(H)))
			allCosets, cosetsInN :=
				a.TermAs[Nat]("card(left_cosets(G.carrier, H))"), a.TermAs[Nat]("card(left_cosets(N, H))")
			divisible := a.Have(
				"p divides the index of H, so it divides the number "+
					"of cosets of H in N, which has the same remainder",
				"p ∣ card(left_cosets(N, H))",
				By(
					index,
					congruent,
					nat_congruence.CongDef.At(allCosets, cosetsInN, p),
					nat_divides.DividesMod.At(p, allCosets),
					nat_divides.DividesMod.At(p, cosetsInN)))
			restricted := a.Have(
				"N is a group under the operations of G",
				"group_on(restrict_group(G, N))",
				By(normal, group.SubgroupGroupOn.Read(grp).At(N)))
			_, qDef := a.LetAs[GroupOps[Set[A]]]("Q", "quotient_group(restrict_group(G, N), H)")
			quotient := a.Have(
				"H being normal in N, the cosets of H in N form the quotient group Q",
				"group_on(Q)",
				By(Normalized, qDef, normal, quotient_group.QuotientGroupOn.Read(restricted).At(H)))
			quotientOrder := a.Have(
				"Q is finite and p divides its order: its points are "+
					"the cosets of H in N, finitely many as N is finite",
				"finite(Q.carrier) ∧ p ∣ card(Q.carrier)",
				By(
					Normalized,
					qDef,
					divisible,
					finiteness,
					quotient_group.QuotientGroupDef,
					quotient_group.LeftCosetsFinite.At(a.TermAs[Op[A]]("G.mul"), N, H)))
			C, element := a.ObtainAs[Set[A]](
				"by Cauchy's theorem Q has an element C of order p",
				"∃C:set(A). C ∈ Q.carrier ∧ group_element_order(Q, C) = p",
				By(prime, quotientOrder, group_action.Cauchy.Read(quotient).At(p)))
			generated := a.TermAs[Set[Set[A]]]("cyclic_subgroup(Q, C)")
			cyclic := a.Have(
				"C generates a subgroup of Q of order p, a prime being positive",
				"subgroup(Q, cyclic_subgroup(Q, C)) ∧ card(cyclic_subgroup(Q, C)) = p",
				ByArith(
					prime,
					element,
					nat_prime.PrimeAtLeastTwo.At(p),
					cyclic_group.CyclicSubgroupSubgroup.Read(quotient).AsFact().At(C),
					cyclic_group.CardCyclicSubgroup.Read(quotient).AsFact().At(C),
					cardinality.HasSizeDef.At(generated, a.TermAs[Nat]("group_element_order(Q, C)"))))
			K, kDef := a.LetAs[Set[A]]("K", "preimage_on(N, coset_map(G.mul, H), cyclic_subgroup(Q, C))")
			lifted := a.Have(
				"its preimage K in N is a subgroup of N holding H, with card(H) * p points",
				"subgroup(restrict_group(G, N), K) ∧ H ⊆ K ∧ card(K) = card(H) * p",
				By(
					Normalized,
					kDef,
					qDef,
					cyclic,
					finiteness,
					normal,
					quotient_group.PreimageSubgroup.Read(restricted).At(H, generated),
					quotient_group.PreimageCard.Read(restricted).At(H, generated)))
			groupN := a.TermAs[GroupOps[A]]("restrict_group(G, N)")
			inG := a.Have(
				"so K is a subgroup of G, and H, normal in N, is normal "+
					"in K, the two restrictions of G to K being one record",
				"subgroup(G, K) ∧ normal_subgroup(restrict_group(G, K), H)",
				By(
					normal,
					lifted,
					group_isomorphism.SubgroupTrans.At(G, N, K),
					group_isomorphism.NormalRestrict.At(groupN, K, H),
					group.RestrictGroupDef.At(groupN, K),
					group.RestrictGroupDef.At(G, K)))
			a.Take(K)
			a.Show(
				"K is the subgroup sought",
				ByArith(inG, lifted))
		}),
})}

// PrimePowerOrderSubgroup — a finite group has a subgroup of every order
// p ^ n, p a prime, dividing its own. By induction on n from the trivial
// subgroup: where p ^ (n + 1) divides card(G), a subgroup H of order p ^ n
// has index card(G) / p ^ n, a multiple of p by Lagrange's theorem, so
// PSubgroupGrowth enlarges H to a subgroup of order p ^ (n + 1).
var PrimePowerOrderSubgroup = primePowerOrderSubgroupThm{family.Add(registry.ProofEntry{
	Name: "PrimePowerOrderSubgroup",
	Key:  "prop_747b8c6f4bdd5810",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
			"p ^ n ∣ card(G.carrier)",
		},
		Conclusion: "∃H:set(A). subgroup(G, H) ∧ card(H) = p ^ n",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], finiteG, prime Fact) {
			a.Induct("n")
			a.Base(
				"the trivial subgroup has order 1, the zeroth power of p",
				func(b *Argument) {
					b.Assume()
					b.Take(b.TermAs[Set[A]]("{G.one}"))
					b.Show(
						"a singleton has one point",
						By(Normalized, group.TrivialSubgroupOn.Read(grp), cardinality.CardSing, nat_arith.NatPow))
				})
			a.Step(
				"a subgroup of order p ^ n has index divisible by p, so it grows to order p ^ (n + 1)",
				func(b *Argument, ih Fact) {
					divides := b.Assume()
					m, factor := b.ObtainAs[Nat](
						"write the order of G as p ^ (n + 1) times a cofactor m",
						"∃m:num. card(G.carrier) = p ^ suc(n) * m",
						By(divides, nat_divides.DividesFactor))
					power := b.Have(
						"the next power of p is p times the last",
						"p ^ suc(n) = p * p ^ n",
						By(nat_arith.NatPow))
					lastPower, cofactor := b.TermAs[Nat]("p ^ n"), b.TermAs[Nat]("p * m")
					regrouped := b.Have(
						"so the order of G is p ^ n times p * m",
						"card(G.carrier) = p ^ n * (p * m)",
						ByArith(b.Simplified(factor, Fwd(power))))
					H, found := b.ObtainAs[Set[A]](
						"p ^ n divides the order of G, so by the induction hypothesis G has a subgroup H of order p ^ n",
						"∃H:set(A). subgroup(G, H) ∧ card(H) = p ^ n",
						By(regrouped, nat_divides.DividesOwnMultiple.At(lastPower, cofactor), ih))
					parts := b.Conjuncts(
						found,
						"H is a subgroup of G",
						"H has order p ^ n")
					sub, order := parts[0], parts[1]
					index := b.Have(
						"Lagrange's theorem counts G as p ^ n times the index of H, and cancelling "+
							"p ^ n, not zero as the order of G is not, leaves the index p * m",
						"card(left_cosets(G.carrier, H)) = p * m",
						ByArith(
							finiteG,
							sub,
							order,
							regrouped,
							finite_group.CarrierCardPositive.Read(grp),
							quotient_group.LagrangeIndex.Read(grp).At(H),
							nat_arith.MulEqLCancel.At(lastPower, b.TermAs[Nat]("card(left_cosets(G.carrier, H))"), cofactor)))
					pSub := b.Have(
						"H, a subgroup of the finite G of order p ^ n, is a p-subgroup",
						"p_subgroup(G, p, H)",
						By(
							Normalized,
							finiteG,
							sub,
							order,
							finite_group.SubgroupFinite.At(b.TermAs[GroupOps[A]]("G"), H),
							finite_group.PSubgroupIff.Read(grp).At(p, H)))
					K, grown := b.ObtainAs[Set[A]](
						"p divides the index of H, so H lies in a subgroup K of G p times as large",
						"∃K:set(A). subgroup(G, K) ∧ card(K) = p * card(H)",
						By(
							index,
							pSub,
							finiteG,
							prime,
							nat_divides.DividesOwnMultiple.At(p, m),
							PSubgroupGrowth.Read(grp).At(p, H)))
					b.Take(K)
					b.Show(
						"K has order p * p ^ n, the next power of p",
						By(Normalized, power, order, grown))
				})
		}),
})}

// SylowOrder — for 2 ≤ p, the Sylow p-subgroups of a finite group are
// exactly its subgroups of order p ^ e, e the multiplicity of p in the order
// of G. Lagrange's theorem writes card(G) as card(P) times the index of P.
// For a Sylow subgroup of order p ^ k, p ^ k divides card(G) and p ^ (k + 1)
// does not, as p does not divide the index, so k is the multiplicity; for a
// subgroup of order p ^ e the index is the cofactor of p ^ e in card(G),
// which p does not divide.
var SylowOrder = sylowOrderThm{family.Add(registry.ProofEntry{
	Name: "SylowOrder",
	Key:  "prop_c006379b3e04dad3",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀P:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"2 ≤ p",
			"subgroup(G, P)",
		},
		Conclusion: "sylow_subgroup(G, p, P) ⇔ card(P) = p ^ nat_multiplicity(p, card(G.carrier))",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			p *Expr[Nat],
			P *Expr[Set[A]],
			finiteG, atLeastTwo, sub Fact,
		) {
			G, orderG := a.TermAs[GroupOps[A]]("G"), a.TermAs[Nat]("card(G.carrier)")
			index := a.TermAs[Nat]("card(left_cosets(G.carrier, P))")
			_, eDef := a.LetAs[Nat]("e", "nat_multiplicity(p, card(G.carrier))")
			nonzero := a.Have(
				"G, a finite group, has positive order",
				"card(G.carrier) ≠ 0",
				ByArith(finiteG, finite_group.CarrierCardPositive.Read(grp)))
			lagrange := a.Have(
				"Lagrange's theorem counts G as the order of P times its index",
				"card(G.carrier) = card(P) * card(left_cosets(G.carrier, P))",
				By(finiteG, sub, quotient_group.LagrangeIndex.Read(grp).At(P)))
			a.Iff()
			a.Forward(
				"a Sylow p-subgroup has order p ^ k, with p ^ k "+
					"dividing the order of G and p ^ (k + 1) not, so k is e",
				func(b *Argument, sylow Fact) {
					indivisible := SylowSubgroupIndexNotDivisible.Read(sylow)
					k, orderP := b.ObtainAs[Nat](
						"P, a p-subgroup, has order p ^ k for some k",
						"∃k:num. card(P) = p ^ k",
						By(SylowSubgroupPSubgroup.Read(sylow), finite_group.PSubgroupIff.Read(grp).At(p, P)))
					powerK := b.TermAs[Nat]("p ^ k")
					counted := b.Have(
						"so G has order p ^ k times the index of P",
						"card(G.carrier) = p ^ k * card(left_cosets(G.carrier, P))",
						By(Normalized, orderP, lagrange))
					nonzeroPower := b.Have(
						"p ^ k is not zero, as p is at least 2",
						"p ^ k ≠ 0",
						ByArith(atLeastTwo, nat_arith.PowEqZero.At(p, k)))
					notNext := b.Have(
						"p ^ (k + 1) = p ^ k * p does not divide the order of G, "+
							"since cancelling p ^ k would leave p dividing the index",
						"¬(p ^ (k + 1) ∣ card(G.carrier))",
						By(
							nonzeroPower,
							indivisible,
							counted,
							nat_arith.PowAdd.At(p, k, b.TermAs[Nat]("1")),
							nat_arith.PowOne.At(p),
							nat_divides.MulDividesLCancel.At(powerK, p, index)))
					exponent := b.Have(
						"p ^ k divides the order of G and p ^ (k + 1) does not, so k is the multiplicity e of p in it",
						"e = k",
						By(
							atLeastTwo,
							nonzero,
							eDef,
							counted,
							notNext,
							nat_divides.DividesOwnMultiple.At(powerK, index),
							nat_multiplicity.MultiplicityUnique.At(p, orderG, k)))
					b.Show(
						"so P has order p ^ e",
						By(Normalized, exponent, orderP))
				})
			a.Backward(
				"a subgroup of order p ^ e has the cofactor of p ^ e "+
					"in the order of G as its index, which p does not divide",
				func(b *Argument, orderP Fact) {
					c, factored := b.ObtainAs[Nat](
						"the order of G is p ^ e times a cofactor c that p does not divide",
						"∃c:num. card(G.carrier) = p ^ e * c ∧ ¬(p ∣ c)",
						By(Normalized, atLeastTwo, nonzero, eDef, nat_multiplicity.MultiplicityCofactor.At(p, orderG)))
					factors := b.Conjuncts(
						factored,
						"G has order p ^ e * c",
						"p does not divide c")
					factor, indivisible := factors[0], factors[1]
					cofactor := b.Have(
						"the two counts of G share the factor p ^ e, not zero as "+
							"the order of G is not, and cancelling it leaves the index c",
						"card(left_cosets(G.carrier, P)) = c",
						ByArith(
							nonzero,
							orderP,
							lagrange,
							factor,
							nat_arith.MulEqLCancel.At(b.TermAs[Nat]("p ^ e"), index, c)))
					pSub := b.Have(
						"P, a subgroup of the finite G of order p ^ e, is a p-subgroup",
						"p_subgroup(G, p, P)",
						By(
							Normalized,
							finiteG,
							sub,
							orderP,
							finite_group.SubgroupFinite.At(G, P),
							finite_group.PSubgroupIff.Read(grp).At(p, P)))
					b.Show(
						"so P is a p-subgroup whose index c is not divisible by p",
						By(Normalized, pSub, cofactor, indivisible, SylowSubgroupDef.At(G, p, P)))
				})
		}),
})}

// SylowExists — a finite group has a Sylow p-subgroup for every prime p:
// Sylow I at the full power of p, read through SylowOrder. With e the
// multiplicity of p in the order of G, p ^ e divides that order, so G has a
// subgroup P of order p ^ e (PrimePowerOrderSubgroup), and a subgroup of
// that order is a Sylow p-subgroup (SylowOrder).
var SylowExists = sylowExistsThm{family.Add(registry.ProofEntry{
	Name: "SylowExists",
	Key:  "prop_83729e18f67ceb18",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
		},
		Conclusion: "∃P:set(A). sylow_subgroup(G, p, P)",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], finiteG, prime Fact) {
			e, eDef := a.LetAs[Nat]("e", "nat_multiplicity(p, card(G.carrier))")
			atLeastTwo := a.Have(
				"the prime p is at least 2",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			nonzero := a.Have(
				"G, a finite group, has positive order",
				"card(G.carrier) ≠ 0",
				ByArith(finiteG, finite_group.CarrierCardPositive.Read(grp)))
			divides := a.Have(
				"p ^ e divides the order of G, e being the multiplicity of p in it",
				"p ^ e ∣ card(G.carrier)",
				By(
					Normalized,
					atLeastTwo,
					nonzero,
					eDef,
					nat_multiplicity.MultiplicitySpec.At(p, a.TermAs[Nat]("card(G.carrier)"))))
			P, found := a.ObtainAs[Set[A]](
				"so G has a subgroup P of order p ^ e",
				"∃P:set(A). subgroup(G, P) ∧ card(P) = p ^ e",
				By(finiteG, prime, divides, PrimePowerOrderSubgroup.Read(grp).At(p, e)))
			a.Take(P)
			a.Show(
				"a subgroup of order p ^ e is a Sylow p-subgroup",
				By(Normalized, finiteG, atLeastTwo, eDef, found, SylowOrder.Read(grp).At(p, P)))
		}),
})}

// PGroupOfOrderDividing — a finite group whose order divides a power of a
// prime p is a p-group: a divisor of p ^ n is a power of p
// (nat_prime.PrimePowerDivisor).
var PGroupOfOrderDividing = pGroupOfOrderDividingThm{family.Add(registry.ProofEntry{
	Name: "PGroupOfOrderDividing",
	Key:  "prop_6359a40f6725c114",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
			"card(G.carrier) ∣ p ^ n",
		},
		Conclusion: "p_group(G, p)",
	},
		func(a *Argument, grp group.GroupFact[on.G], p, n *Expr[Nat], finite, prime, divides Fact) {
			a.Show(
				"the order of G, dividing a power of the prime p, is itself a power of p",
				Simp(Fwd(finite_group.PGroupDef)),
				By(
					grp,
					finite,
					prime,
					divides,
					nat_prime.PrimePowerDivisor.At(p, n, a.TermAs[Nat]("card(G.carrier)"))))
		}),
})}

// PGroupIndexPrime — a nontrivial p-group, p a prime, has a subgroup of
// index p. Its order is a power p ^ k, and k is not zero since the group
// has more than one element; so card(G) is p * p ^ j, and a subgroup of
// order p ^ j (PrimePowerOrderSubgroup) has index p.
var PGroupIndexPrime = pGroupIndexPrimeThm{family.Add(registry.ProofEntry{
	Name: "PGroupIndexPrime",
	Key:  "prop_34e326959909b8b0",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p_group(G, p)",
			"1 < card(G.carrier)",
		},
		Conclusion: "∃H:set(A). subgroup(G, H) ∧ card(G.carrier) = p * card(H)",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], prime, pGroup, nontrivial Fact) {
			finiteG := finite_group.PGroupFinite.Read(pGroup)
			k, power := a.UnpackAs[Nat](finite_group.PGroupPowerOrder.Read(pGroup).AsFact(), "k")
			j, successor := a.ObtainAs[Nat](
				"the exponent k is positive, so it is j + 1 for some j",
				"∃j:num. k = suc(j)",
				Derive(func(b *Argument) {
					nonzero := b.Unless(
						b.TermAs[Bool]("k = 0"),
						"at k = 0 the group would have exactly one element",
						Given(func(c *Argument, zero Fact) {
							one := c.Simplified(power, Fwd(zero), Fwd(nat_arith.NatPow))
							c.Show(
								"which contradicts its having more than one",
								ByArith(one, nontrivial))
						}))
					b.Show(
						"a nonzero natural number is a successor",
						By(Normalized, nonzero, peano.Cases.At(k)))
				}))
			order := a.Simplified(power, Fwd(successor), Fwd(nat_arith.NatPow))
			H, found := a.ObtainAs[Set[A]](
				"p ^ j divides the order p * p ^ j of G, so G has a subgroup H of order p ^ j",
				"∃H:set(A). subgroup(G, H) ∧ card(H) = p ^ j",
				By(
					finiteG,
					prime,
					order,
					nat_divides.DividesOwnMultiple.At(a.TermAs[Nat]("p ^ j"), p),
					PrimePowerOrderSubgroup.Read(grp).At(p, j)))
			a.Take(H)
			a.Show(
				"H has index p",
				By(Normalized, order, found))
		}),
})}
