// counting.go — the number of Sylow p-subgroups: the index of a
// normalizer, a divisor of the index of a Sylow subgroup, and 1 mod p
// (Sylow III).

package sylow

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_action"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// sylowSubgroupsAreSubsets — the Sylow p-subgroups are subsets of the
// carrier: each is a subgroup (SylowSubgroupSubgroup). The conjugation
// action on them and their count both read them among the subsets of the
// carrier.
var sylowSubgroupsAreSubsets = sylowSubgroupsAreSubsetsThm{family.Add(registry.ProofEntry{
	Name: "sylowSubgroupsAreSubsets",
	Key:  "prop_6f62cdcf6b6be5f0",
	Build: family.Theorem("∀G:group_ops(A). ∀p:num. sylow_subgroups(G, p) ⊆ {S:set(A) | S ⊆ G.carrier}",
		func(a *Argument, G *Expr[GroupOps[A]], p *Expr[Nat]) {
			a.Show(
				"a Sylow p-subgroup is a subgroup, so a subset of the carrier",
				BySets(SylowSubgroupSubgroup, group.SubgroupSubset))
		}),
})}

// SylowConjugationAction — a finite group acts by conjugation on its Sylow
// p-subgroups. G acts by conjugation on the subsets of its carrier
// (ConjugationAction); a Sylow subgroup is a subgroup, so one of those
// subsets, and a conjugate of a Sylow subgroup is again one
// (ConjugateIsSylow), so the action restricts to them (SubsetAction).
var SylowConjugationAction = sylowConjugationActionThm{family.Add(registry.ProofEntry{
	Name: "SylowConjugationAction",
	Key:  "prop_4fdf5c42c38a4c29",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"finite(G.carrier)",
		},
		Conclusion: "group_action(G, sylow_subgroups(G, p), group_conjugate(G))",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], finiteG Fact) {
			a.Show(
				"a Sylow p-subgroup is a subset of the carrier, and a conjugate of one "+
					"is one, so conjugation on the subsets of the carrier restricts to them",
				By(
					sylowSubgroupsAreSubsets.At(a.TermAs[GroupOps[A]]("G"), p),
					finiteG,
					ConjugateIsSylow.Read(grp),
					group_action.SubsetAction.Read(group_action.ConjugationAction.Read(grp))))
		}),
})}

// SylowCountIndex — the number of Sylow p-subgroups of a finite group is
// the index of the normalizer of any one of them. G acts on them by
// conjugation (SylowConjugationAction), and the orbit of P is all of them,
// every Sylow subgroup being a conjugate of P (SylowConjugacy); its
// stabilizer is the normalizer N of P (NormalizerIsStabilizer).
// Orbit–stabilizer counts G as their number times card(N), Lagrange's
// theorem as card(N) times the index of N, and card(N), not zero as the
// order of G is not, cancels.
var SylowCountIndex = sylowCountIndexThm{family.Add(registry.ProofEntry{
	Name: "SylowCountIndex",
	Key:  "prop_d3d0caa6ea9760f",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀P:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
			"sylow_subgroup(G, p, P)",
		},
		Conclusion: "card(sylow_subgroups(G, p)) = card(left_cosets(G.carrier, group_normalizer(G, P)))",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			p *Expr[Nat],
			P *Expr[Set[A]],
			finiteG, prime, sylow Fact,
		) {
			G, carrier := a.TermAs[GroupOps[A]]("G"), a.TermAs[Set[A]]("G.carrier")
			N, nDef := a.LetAs[Set[A]]("N", "group_normalizer(G, P)")
			subP := SylowSubgroupSubgroup.Read(sylow)
			action := a.Have(
				"G acts by conjugation on its Sylow p-subgroups",
				"group_action(G, sylow_subgroups(G, p), group_conjugate(G))",
				By(finiteG, SylowConjugationAction.Read(grp).At(p)))
			pm := a.MemberOf[on.Any](P, a.Have(
				"P is one of the Sylow p-subgroups",
				"P ∈ sylow_subgroups(G, p)",
				By(sylow)))
			orbit := a.Have(
				"the orbit of P is all the Sylow p-subgroups",
				"group_orbit(G, group_conjugate(G), P) = sylow_subgroups(G, p)",
				Derive(func(b *Argument) {
					conjugates := b.Have(
						"each Sylow p-subgroup is a conjugate of P, so lies in its orbit",
						"sylow_subgroups(G, p) ⊆ group_orbit(G, group_conjugate(G), P)",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(c *Argument) {
							Q := c.FixAs[Set[A]]("Q")
							sylowQ := c.Assume()
							g, conjugate := c.ObtainAs[A](
								"Q is a conjugate gPg⁻¹ of P",
								"∃g:A. g ∈ G.carrier ∧ Q = group_conjugate(G, g, P)",
								By(finiteG, prime, sylow, sylowQ, SylowConjugacy.Read(grp).At(p, P, Q)))
							parts := c.Conjuncts(
								conjugate,
								"g lies in the carrier",
								"Q is gPg⁻¹")
							conjugation := c.TermAs[Fun[A, Set[A]]]("λg:A. group_conjugate(G, g, P)")
							c.Show(
								"and the orbit of P is its image under g ↦ gPg⁻¹",
								parts[1].Rw(),
								By(parts[0], group_action.GroupOrbitDef, set_image.FunInImage.At(conjugation, carrier, g)))
						}))
					b.Show(
						"the orbit lies among the Sylow p-subgroups, which lie in it",
						By(conjugates, group_action.OrbitSubset.Read(action).At(pm), set_order.SubsetAntisym))
				}))
			byOrbit := a.Have(
				"orbit–stabilizer counts G as the number of Sylow p-subgroups "+
					"times the order of the stabilizer of P, its normalizer N",
				"card(G.carrier) = card(sylow_subgroups(G, p)) * card(N)",
				By(
					Normalized,
					nDef,
					finiteG,
					orbit,
					group_action.NormalizerIsStabilizer.At(G, P),
					group_action.OrbitStabilizer.Read(action).At(pm)))
			byCosets := a.Have(
				"Lagrange's theorem counts G as the order of N, a subgroup, times its index",
				"card(G.carrier) = card(N) * card(left_cosets(G.carrier, N))",
				By(
					nDef,
					finiteG,
					subP,
					group_action.NormalizerSubgroup.Read(grp).At(P),
					quotient_group.LagrangeIndex.Read(grp).At(N)))
			a.Show(
				"G, a finite group, has positive order, so the order "+
					"of N is not zero and cancels between the two counts",
				ByArith(
					finiteG,
					byOrbit,
					byCosets,
					finite_group.CarrierCardPositive.Read(grp),
					nat_arith.MulEqLCancel.At(
						a.TermAs[Nat]("card(N)"),
						a.TermAs[Nat]("card(sylow_subgroups(G, p))"),
						a.TermAs[Nat]("card(left_cosets(G.carrier, N))"))))
		}),
})}

// SylowCountDivides — the number of Sylow p-subgroups of a finite group
// divides the index of each of them. The number is the index of the
// normalizer N of P (SylowCountIndex), and N is a subgroup holding P, so
// the index of P is the index of N times the index of P in N
// (quotient_group.IndexMultiplicative).
var SylowCountDivides = sylowCountDividesThm{family.Add(registry.ProofEntry{
	Name: "SylowCountDivides",
	Key:  "prop_327530f67e5a7f82",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀P:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
			"sylow_subgroup(G, p, P)",
		},
		Conclusion: "card(sylow_subgroups(G, p)) ∣ card(left_cosets(G.carrier, P))",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			p *Expr[Nat],
			P *Expr[Set[A]],
			finiteG, prime, sylow Fact,
		) {
			N, nDef := a.LetAs[Set[A]]("N", "group_normalizer(G, P)")
			subP := SylowSubgroupSubgroup.Read(sylow)
			tower := a.Have(
				"the normalizer N of P is a subgroup holding P, so "+
					"the index of P is the index of N times that of P in N",
				"card(left_cosets(G.carrier, P)) = card(left_cosets(G.carrier, N)) * card(left_cosets(N, P))",
				By(
					nDef,
					finiteG,
					subP,
					group.SubgroupOne.Read(subP),
					group_action.NormalizerSubgroup.Read(grp).At(P),
					quotient_group.LeftCosetsFinite.At(a.TermAs[Op[A]]("G.mul"), a.TermAs[Set[A]]("G.carrier"), P),
					quotient_group.IndexMultiplicative.Read(grp).At(P, N)))
			a.Show(
				"the number of Sylow p-subgroups is the index of N, a factor of the index of P",
				By(
					nDef,
					finiteG,
					prime,
					sylow,
					tower,
					SylowCountIndex.Read(grp).At(p, P),
					nat_divides.DividesOwnMultiple.At(
						a.TermAs[Nat]("card(left_cosets(G.carrier, N))"),
						a.TermAs[Nat]("card(left_cosets(N, P))"))))
		}),
})}

// SylowInSubgroup — a Sylow p-subgroup of G inside a subgroup K is a Sylow
// p-subgroup of K. P is a p-subgroup of K
// (group_isomorphism.PSubgroupRestrict), and its index in G is the index of
// K in G times its index in K (quotient_group.IndexMultiplicative), so p,
// which does not divide the index in G, does not divide the index in K.
var SylowInSubgroup = sylowInSubgroupThm{family.Add(registry.ProofEntry{
	Name: "SylowInSubgroup",
	Key:  "prop_7cc4602e386f3e70",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀P K:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"sylow_subgroup(G, p, P)",
			"subgroup(G, K)",
			"P ⊆ K",
		},
		Conclusion: "sylow_subgroup(restrict_group(G, K), p, P)",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			p *Expr[Nat],
			P, K *Expr[Set[A]],
			finiteG, sylow, subK, inK Fact,
		) {
			G := a.TermAs[GroupOps[A]]("G")
			indexInK := a.TermAs[Nat]("card(left_cosets(K, P))")
			indexOfK := a.TermAs[Nat]("card(left_cosets(G.carrier, K))")
			pSub, indivisible := SylowSubgroupPSubgroup.Read(sylow), SylowSubgroupIndexNotDivisible.Read(sylow)
			sub := SylowSubgroupSubgroup.Read(sylow)
			indivisibleInK := a.Have(
				"the index of P in G is the index of K times the index of P in K, so p does not divide the latter",
				"¬(p ∣ card(left_cosets(K, P)))",
				By(
					finiteG,
					group.SubgroupOne.Read(sub),
					subK,
					inK,
					indivisible,
					quotient_group.LeftCosetsFinite.At(a.TermAs[Op[A]]("G.mul"), a.TermAs[Set[A]]("G.carrier"), P),
					quotient_group.IndexMultiplicative.Read(grp).At(P, K),
					nat_divides.DividesMul.At(p, indexInK, indexOfK),
					nat_arith.MulSym.At(indexInK, indexOfK)))
			a.Show(
				"so P, a p-subgroup of K, has an index in K that p does not divide",
				By(
					pSub,
					inK,
					indivisibleInK,
					group_isomorphism.PSubgroupRestrict.At(G, p, P, K),
					SylowSubgroupDef.At(a.TermAs[GroupOps[A]]("restrict_group(G, K)"), p, P)))
		}),
})}

// SylowInNormalizer — a Sylow p-subgroup inside the normalizer of another
// is that other one. The normalizer N of Q is a subgroup holding Q
// (NormalizerSubgroup), in which Q is a Sylow subgroup (SylowInSubgroup)
// and P a p-subgroup (group_isomorphism.PSubgroupRestrict), so P lies in a
// conjugate gQg⁻¹ with g in N (PSubgroupInConjugate in the group N). As g
// normalizes Q, P lies in Q; and P, conjugate to Q in G (SylowConjugacy),
// has the order of Q (ConjugateCard), so P is Q.
var SylowInNormalizer = sylowInNormalizerThm{family.Add(registry.ProofEntry{
	Name: "SylowInNormalizer",
	Key:  "prop_61ac5149380722e4",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀P Q:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
			"sylow_subgroup(G, p, P)",
			"sylow_subgroup(G, p, Q)",
			"P ⊆ group_normalizer(G, Q)",
		},
		Conclusion: "P = Q",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], P, Q *Expr[Set[A]],
			finiteG, prime, sylowP, sylowQ, inN Fact) {
			G := a.TermAs[GroupOps[A]]("G")
			N, nDef := a.LetAs[Set[A]]("N", "group_normalizer(G, Q)")
			pSubP := SylowSubgroupPSubgroup.Read(sylowP)
			subQ := SylowSubgroupSubgroup.Read(sylowQ)
			normalizer := a.Have(
				"the normalizer N of Q is a subgroup of G holding Q",
				"subgroup(G, N) ∧ Q ⊆ N",
				By(Normalized, nDef, subQ, group_action.NormalizerSubgroup.Read(grp).At(Q)))
			restricted := a.Have(
				"N is a group under the operations of G",
				"group_on(restrict_group(G, N))",
				By(normalizer, group.SubgroupGroupOn.Read(grp).At(N)))
			finiteN := a.Have(
				"N, a subgroup of the finite G, is finite",
				"finite(N)",
				By(finiteG, normalizer, finite_group.SubgroupFinite.At(G, N)))
			sylowQInN := a.Have(
				"Q is a Sylow p-subgroup of N",
				"sylow_subgroup(restrict_group(G, N), p, Q)",
				By(finiteG, sylowQ, normalizer, SylowInSubgroup.Read(grp).At(p, Q, N)))
			pSubPInN := a.Have(
				"and P a p-subgroup of N",
				"p_subgroup(restrict_group(G, N), p, P)",
				By(pSubP, inN, group_isomorphism.PSubgroupRestrict.At(G, p, P, N)))
			subQInN := SylowSubgroupSubgroup.Read(sylowQInN)
			indivisibleInN := SylowSubgroupIndexNotDivisible.Read(sylowQInN)
			_, conjugate := a.ObtainAs[A](
				"so P lies in a conjugate gQg⁻¹ of Q in N, by an element g of N",
				"∃g:A. g ∈ N ∧ P ⊆ group_conjugate(restrict_group(G, N), g, Q)",
				By(
					prime,
					subQInN,
					finiteN,
					indivisibleInN,
					pSubPInN,
					quotient_group.LeftCosetsFinite.At(a.TermAs[Op[A]]("G.mul"), N, Q),
					PSubgroupInConjugate.Read(restricted).At(p, Q, P)))
			gParts := a.Conjuncts(
				conjugate,
				"g lies in N",
				"P lies in gQg⁻¹")
			sameConjugate := a.Have(
				"N carries the operations of G, so gQg⁻¹ in N is gQg⁻¹ in G",
				"group_conjugate(restrict_group(G, N), g, Q) = group_conjugate(G, g, Q)",
				Unfold(group_action.GroupConjugateDef))
			normalizes := a.Unfolded(a.Simplified(gParts[0], Fwd(nDef)), group_action.GroupNormalizerDef)
			finiteQ := a.Have(
				"Q, a subgroup of the finite G, is finite",
				"finite(Q)",
				By(finiteG, subQ, finite_group.SubgroupFinite.At(G, Q)))
			k, conjugateOfQ := a.ObtainAs[A](
				"P, a Sylow p-subgroup as Q is, is a conjugate kQk⁻¹ of Q",
				"∃k:A. k ∈ G.carrier ∧ P = group_conjugate(G, k, Q)",
				By(finiteG, prime, sylowQ, sylowP, SylowConjugacy.Read(grp).At(p, Q, P)))
			kParts := a.Conjuncts(
				conjugateOfQ,
				"k lies in the carrier",
				"P is kQk⁻¹")
			sameOrder := a.Have(
				"so P has the order of Q",
				"card(P) = card(Q)",
				By(
					Normalized,
					kParts[1],
					finiteQ,
					group.SubgroupSubset.Read(subQ),
					group_action.ConjugateCard.Read(grp).At(Q, a.MemberOf[on.G](k, kParts[0]))))
			a.Show(
				"g normalizes Q, so P lies in gQg⁻¹, which is Q, and "+
					"a subset of the finite Q with as many points is Q",
				ByArith(
					finiteQ,
					normalizes,
					gParts[1],
					sameConjugate,
					sameOrder,
					cardinality.CardSubsetLe.At(P, Q)))
		}),
})}

// SylowCountMod — the number of Sylow p-subgroups of a finite group is 1
// mod p. A Sylow p-subgroup P (SylowExists) acts on them by conjugation,
// the action of G restricted to P, so, P having p-power order, their
// number is congruent mod p to the number of them P fixes
// (PrimePowerFixedPoints). P fixes itself, lying in its own normalizer;
// and a Sylow subgroup Q that P fixes has P in its normalizer, so Q is P
// (SylowInNormalizer). P fixes exactly one, and the count is 1 mod p.
var SylowCountMod = sylowCountModThm{family.Add(registry.ProofEntry{
	Name: "SylowCountMod",
	Key:  "prop_4c6747320654f257",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
		},
		Conclusion: "card(sylow_subgroups(G, p)) ≡ 1 (mod p)",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], finiteG, prime Fact) {
			carrier := a.TermAs[Set[A]]("G.carrier")
			P, sylow := a.ObtainAs[Set[A]](
				"G has a Sylow p-subgroup P",
				"∃P:set(A). sylow_subgroup(G, p, P)",
				By(finiteG, prime, SylowExists.Read(grp).At(p)))
			pSub := SylowSubgroupPSubgroup.Read(sylow)
			subP, pGroup := SylowSubgroupSubgroup.Read(sylow), finite_group.PSubgroupPGroup.Read(pSub)
			action := a.Have(
				"G acts by conjugation on its Sylow p-subgroups",
				"group_action(G, sylow_subgroups(G, p), group_conjugate(G))",
				By(finiteG, SylowConjugationAction.Read(grp).At(p)))
			byP := a.Have(
				"and so does its subgroup P",
				"group_action(restrict_group(G, P), sylow_subgroups(G, p), group_conjugate(G))",
				By(subP, group_action.RestrictAction.Read(action).At(P)))
			finiteness := a.Have(
				"the Sylow p-subgroups are among the finitely many subsets of the finite carrier",
				"finite(sylow_subgroups(G, p))",
				By(
					finiteG,
					sylowSubgroupsAreSubsets.At(a.TermAs[GroupOps[A]]("G"), p),
					finite_set.FinitePowerset.At(carrier),
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Set[A]]]("sylow_subgroups(G, p)"),
						a.TermAs[Set[Set[A]]]("{S:set(A) | S ⊆ G.carrier}"))))
			_, fDef := a.LetAs[Set[Set[A]]](
				"F",
				"{Q:set(A) | Q ∈ sylow_subgroups(G, p) ∧ ∀g:A. g ∈ P ⇒ group_conjugate(G, g, Q) = Q}")
			congruent := a.Have(
				"P, a p-group, fixes as many Sylow p-subgroups as there are, mod p",
				"card(sylow_subgroups(G, p)) ≡ card(F) (mod p)",
				By(fDef, finiteness, prime, pGroup, group_action.PrimePowerFixedPoints.Read(byP).At(p)))
			selfNormal := a.Have(
				"each element of P conjugates P onto P, P lying in its own normalizer",
				"∀g:A. g ∈ P ⇒ group_conjugate(G, g, P) = P",
				Derive(func(b *Argument) {
					b.FixAs[A]("g")
					inP := b.Assume()
					inN := b.Have(
						"g lies in the normalizer of P",
						"g ∈ group_normalizer(G, P)",
						By(inP, subP, group_action.NormalizerSubgroup.Read(grp).At(P), set_basic.SubsetDef))
					b.Show(
						"which is to say that conjugation by g carries P onto P",
						By(b.Unfolded(inN, group_action.GroupNormalizerDef)))
				}))
			fixed := a.Have(
				"P fixes itself and no other Sylow p-subgroup",
				"F = {P}",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					Q := b.FixAs[Set[A]]("Q")
					b.Iff()
					b.Forward(
						"a Sylow p-subgroup Q that P fixes has P in its normalizer, so is P",
						func(c *Argument, inF Fact) {
							fixedParts := c.Conjuncts(
								c.Simplified(inF, Fwd(fDef)),
								"Q is a Sylow p-subgroup",
								"which every element of P conjugates onto itself")
							normalizes := c.Have(
								"P, inside the carrier, lies in the normalizer of Q",
								"P ⊆ group_normalizer(G, Q)",
								Simp(Fwd(group_action.GroupNormalizerDef)),
								BySets(fixedParts[1], group.SubgroupSubset.Read(subP)))
							c.Show(
								"so Q, a Sylow p-subgroup whose normalizer holds P, is P",
								By(
									finiteG,
									prime,
									sylow,
									fixedParts[0],
									normalizes,
									set_basic.InSing,
									SylowInNormalizer.Read(grp).At(p, P, Q)))
						})
					b.Backward(
						"P is a Sylow p-subgroup that each of its elements conjugates onto itself",
						func(c *Argument, single Fact) {
							isP := c.Simplified(single, Fwd(set_basic.InSing))
							c.Show(
								"so P lies in F",
								isP.Rw(),
								fDef.Rw(),
								By(selfNormal, sylow))
						})
				}))
			a.Show(
				"so P fixes exactly one Sylow p-subgroup, and their number is 1 mod p",
				By(Normalized, congruent, fixed, cardinality.CardSing.At(P)))
		}),
})}
