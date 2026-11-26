// conjugacy.go — a p-subgroup lies in a conjugate of every subgroup whose
// index p does not divide, and any two Sylow p-subgroups are conjugate
// (Sylow II).

package sylow

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_action"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// PSubgroupInConjugate — a p-subgroup lies in a conjugate of every subgroup
// of finite index that p does not divide. Q acts on the cosets of P by left
// translation and, being a p-group, fixes, mod p, as many of them as there
// are (PrimePowerFixedPoints), a number p does not divide, so it fixes some
// coset gP. Then g⁻¹hg lies in P for each h in Q (CosetFixedIff), and
// h = g(g⁻¹hg)g⁻¹ lies in gPg⁻¹.
var PSubgroupInConjugate = pSubgroupInConjugateThm{family.Add(registry.ProofEntry{
	Name: "PSubgroupInConjugate",
	Key:  "prop_ae436363170e1910",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀P Q:set(A).",
		Hypotheses: []string{
			"nat_prime(p)",
			"subgroup(G, P)",
			"finite(left_cosets(G.carrier, P))",
			"¬(p ∣ card(left_cosets(G.carrier, P)))",
			"p_subgroup(G, p, Q)",
		},
		Conclusion: "∃g:A. g ∈ G.carrier ∧ Q ⊆ group_conjugate(G, g, P)",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], P, Q *Expr[Set[A]],
			prime, subP, finiteIndex, indivisible, pSubQ Fact) {
			subQ, pGroupQ :=
				finite_group.PSubgroupSubgroup.Read(pSubQ), finite_group.PSubgroupPGroup.Read(pSubQ)
			translation := a.Have(
				"G acts on the cosets of P by left translation",
				"group_action(G, left_cosets(G.carrier, P), λg:A. λS:set(A). image(G.mul(g), S))",
				By(subP, group_action.CosetAction.Read(grp).At(P)))
			byQ := a.Have(
				"and so does its subgroup Q",
				"group_action(restrict_group(G, Q), "+
					"    left_cosets(G.carrier, P), "+
					"    λg:A. λS:set(A). image(G.mul(g), S))",
				By(subQ, group_action.RestrictAction.Read(translation).At(Q)))
			F, fDef := a.LetAs[Set[Set[A]]](
				"F",
				"{S:set(A) | S ∈ left_cosets(G.carrier, P) ∧ ∀h:A. h ∈ Q ⇒ image(G.mul(h), S) = S}")
			congruent := a.Have(
				"the cosets of P are finitely many, and Q, a p-group, fixes as many of them as there are, mod p",
				"card(left_cosets(G.carrier, P)) ≡ card(F) (mod p)",
				By(fDef, finiteIndex, prime, pGroupQ, group_action.PrimePowerFixedPoints.Read(byQ).At(p)))
			index := a.TermAs[Nat]("card(left_cosets(G.carrier, P))")
			nonzero := a.Have(
				"p does not divide the index of P, so neither does it "+
					"divide the number of cosets Q fixes, which is not 0",
				"card(F) ≠ 0",
				ByArith(
					indivisible,
					congruent,
					nat_congruence.CongDef.At(index, a.TermAs[Nat]("card(F)"), p),
					nat_divides.DividesMod.At(p, index)))
			S, inF := a.ObtainAs[Set[A]](
				"so Q fixes some coset S",
				"∃S:set(A). S ∈ F",
				By(Normalized, nonzero, cardinality.CardClauses, set_basic.MemberNotEmpty.At(F)))
			fixed := a.Conjuncts(
				a.Simplified(inF, Fwd(fDef)),
				"S is a coset of P",
				"and every element of Q fixes it")
			g, represented := a.ObtainAs[A](
				"S is the coset gP of a point g of the carrier",
				"∃g:A. S = left_coset(g, P) ∧ g ∈ G.carrier",
				By(fixed[0], group.SubgroupSubset.Read(subP), quotient_group.InLeftCosets.Read(grp).At(P, S)))
			coset := a.Conjuncts(
				represented,
				"S is the coset of g",
				"g lies in the carrier")
			gm := a.MemberOf[on.G](g, coset[1])
			inConjugate := a.Have(
				"Q lies in the conjugate gPg⁻¹",
				"Q ⊆ group_conjugate(G, g, P)",
				Unfold(group_action.GroupConjugateDef),
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					h := b.FixAs[A]("h")
					inQ := b.Assume()
					inCarrier := b.Have(
						"h lies in the carrier, as Q does",
						"h ∈ G.carrier",
						By(inQ, group.SubgroupSubset.Read(subQ), set_basic.SubsetDef))
					hm := b.MemberOf[on.G](h, inCarrier)
					conjugate := b.Have(
						"h fixes the coset gP, so G.inv(g) * h * g lies in P",
						"G.inv(g) * h * g ∈ P",
						By(fixed[1].At(h), inQ, coset[0], subP, group_action.CosetFixedIff.Read(grp).At(P, gm, hm)))
					inverseTimesH := group.MulIn.Read(grp).At(group.InvIn.Read(grp).At(gm), hm)
					conjugation := b.TermAs[Fun[A, A]]("λx:A. g * x * G.inv(g)")
					b.Show(
						"and h = g(g⁻¹hg)g⁻¹ is the image of G.inv(g) * h * g under conjugation by g",
						By(
							Normalized,
							conjugate,
							set_image.FunInImage.At(conjugation, P, b.TermAs[A]("G.inv(g) * h * g")),
							group.AssocOn.Read(grp).At(gm, inverseTimesH, gm),
							group.MulInvCancelRightOn.Read(grp).At(gm, group.MulIn.Read(grp).At(gm, inverseTimesH)),
							group.MulInvCancelLeftOn.Read(grp).At(gm, hm)))
				}))
			a.Take(g)
			a.Show(
				"so g is the point sought",
				By(coset[1], inConjugate))
		}),
})}

// SylowConjugacy — any two Sylow p-subgroups of a finite group are
// conjugate. Each is a p-subgroup with an index p does not divide, so
// PSubgroupInConjugate puts Q in a conjugate gPg⁻¹ and P in a conjugate
// kQk⁻¹. Conjugates have the size of what they conjugate (ConjugateCard),
// so card(gPg⁻¹) = card(P) ≤ card(Q), and Q, a subset of the finite gPg⁻¹
// at least as large, is gPg⁻¹.
var SylowConjugacy = sylowConjugacyThm{family.Add(registry.ProofEntry{
	Name: "SylowConjugacy",
	Key:  "prop_a4cfa9c58e86d7f1",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀P Q:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(p)",
			"sylow_subgroup(G, p, P)",
			"sylow_subgroup(G, p, Q)",
		},
		Conclusion: "∃g:A. g ∈ G.carrier ∧ Q = group_conjugate(G, g, P)",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], P, Q *Expr[Set[A]],
			finiteG, prime, sylowP, sylowQ Fact) {
			G := a.TermAs[GroupOps[A]]("G")
			pSubP := SylowSubgroupPSubgroup.Read(sylowP)
			subP := SylowSubgroupSubgroup.Read(sylowP)
			indivisibleP := SylowSubgroupIndexNotDivisible.Read(sylowP)
			pSubQ := SylowSubgroupPSubgroup.Read(sylowQ)
			subQ := SylowSubgroupSubgroup.Read(sylowQ)
			indivisibleQ := SylowSubgroupIndexNotDivisible.Read(sylowQ)
			g, inConjugateOfP := a.ObtainAs[A](
				"Q, a p-subgroup, lies in a conjugate gPg⁻¹ of P",
				"∃g:A. g ∈ G.carrier ∧ Q ⊆ group_conjugate(G, g, P)",
				By(
					finiteG,
					prime,
					subP,
					indivisibleP,
					pSubQ,
					quotient_group.LeftCosetsFinite.At(a.TermAs[Op[A]]("G.mul"), a.TermAs[Set[A]]("G.carrier"), P),
					PSubgroupInConjugate.Read(grp).At(p, P, Q)))
			k, inConjugateOfQ := a.ObtainAs[A](
				"and P in a conjugate kQk⁻¹ of Q",
				"∃k:A. k ∈ G.carrier ∧ P ⊆ group_conjugate(G, k, Q)",
				By(
					finiteG,
					prime,
					subQ,
					indivisibleQ,
					pSubP,
					quotient_group.LeftCosetsFinite.At(a.TermAs[Op[A]]("G.mul"), a.TermAs[Set[A]]("G.carrier"), Q),
					PSubgroupInConjugate.Read(grp).At(p, Q, P)))
			gParts := a.Conjuncts(
				inConjugateOfP,
				"g lies in the carrier",
				"Q lies in gPg⁻¹")
			kParts := a.Conjuncts(
				inConjugateOfQ,
				"k lies in the carrier",
				"P lies in kQk⁻¹")
			gm, km := a.MemberOf[on.G](g, gParts[0]), a.MemberOf[on.G](k, kParts[0])
			finite := a.Have(
				"P and Q, subgroups of the finite G, are finite",
				"finite(P) ∧ finite(Q)",
				By(finiteG, subP, subQ, finite_group.SubgroupFinite.At(G, P), finite_group.SubgroupFinite.At(G, Q)))
			sizes := a.Have(
				"a conjugate has the size of what it conjugates",
				"card(group_conjugate(G, g, P)) = card(P) ∧ card(group_conjugate(G, k, Q)) = card(Q)",
				By(
					finite,
					group.SubgroupSubset.Read(subP),
					group.SubgroupSubset.Read(subQ),
					group_action.ConjugateCard.Read(grp).At(P, gm),
					group_action.ConjugateCard.Read(grp).At(Q, km)))
			atMostQ := a.Have(
				"P lies in the finite kQk⁻¹, of the size of Q, so gPg⁻¹, of the size of P, is no larger than Q",
				"card(group_conjugate(G, g, P)) ≤ card(Q)",
				By(
					Normalized,
					finite,
					sizes,
					kParts[1],
					group_action.ConjugateFinite.At(G, k, Q),
					cardinality.CardSubset.At(P, a.TermAs[Set[A]]("group_conjugate(G, k, Q)"))))
			a.Take(g)
			a.Show(
				"Q, a subset of the finite gPg⁻¹ at least as large as it, is gPg⁻¹",
				By(
					gParts[0],
					finite,
					gParts[1],
					atMostQ,
					group_action.ConjugateFinite.At(G, g, P),
					cardinality.CardSubsetLe.At(Q, a.TermAs[Set[A]]("group_conjugate(G, g, P)"))))
		}),
})}

// ConjugateIsSylow — a conjugate of a Sylow p-subgroup is a Sylow
// p-subgroup. gPg⁻¹ is a subgroup of G with as many points as P, so a
// p-subgroup, and Lagrange's theorem counts G both as card(P) times the
// index of P and as card(gPg⁻¹) times the index of gPg⁻¹. The order of G is
// not zero, so neither is card(P), and the two indices agree: p does not
// divide the new one either.
var ConjugateIsSylow = conjugateIsSylowThm{family.Add(registry.ProofEntry{
	Name: "ConjugateIsSylow",
	Key:  "prop_aac7878d908b583f",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀p:num. ∀P:set(A). ∀g:A.",
		Hypotheses: []string{
			"finite(G.carrier)",
			"g ∈ G.carrier",
			"sylow_subgroup(G, p, P)",
		},
		Conclusion: "sylow_subgroup(G, p, group_conjugate(G, g, P))",
	},
		func(a *Argument, grp group.GroupFact[on.G], p *Expr[Nat], P *Expr[Set[A]], finiteG, sylow Fact,
			g *Member[A, on.G]) {
			G := a.TermAs[GroupOps[A]]("G")
			conjugate := a.TermAs[Set[A]]("group_conjugate(G, g, P)")
			pSub, indivisible := SylowSubgroupPSubgroup.Read(sylow), SylowSubgroupIndexNotDivisible.Read(sylow)
			sub := SylowSubgroupSubgroup.Read(sylow)
			_, power := a.ObtainAs[Nat](
				"P, a p-subgroup, has order p ^ n for some n",
				"∃n:num. card(P) = p ^ n",
				By(pSub, finite_group.PSubgroupIff.Read(grp).At(p, P)))
			conjugateSub := a.Have(
				"the conjugate gPg⁻¹ is a subgroup of G",
				"subgroup(G, group_conjugate(G, g, P))",
				By(sub, group_action.ConjugateSubgroup.Read(grp).At(P, g)))
			conjugateOrder := a.Have(
				"gPg⁻¹ has the order of P, a subgroup of the finite G",
				"card(group_conjugate(G, g, P)) = card(P)",
				By(
					finiteG,
					sub,
					group.SubgroupSubset.Read(sub),
					finite_group.SubgroupFinite.At(G, P),
					group_action.ConjugateCard.Read(grp).At(P, g)))
			index := a.Have(
				"card(P) times the index of P and card(gPg⁻¹) times its "+
					"index both count G, and the two orders agree and are not zero",
				"card(left_cosets(G.carrier, group_conjugate(G, g, P))) = card(left_cosets(G.carrier, P))",
				ByArith(
					finiteG,
					sub,
					conjugateSub,
					conjugateOrder,
					quotient_group.LagrangeIndex.Read(grp).At(P),
					quotient_group.LagrangeIndex.Read(grp).At(conjugate),
					finite_group.CarrierCardPositive.Read(grp),
					nat_arith.MulEqLCancel.At(
						a.TermAs[Nat]("card(P)"),
						a.TermAs[Nat]("card(left_cosets(G.carrier, group_conjugate(G, g, P)))"),
						a.TermAs[Nat]("card(left_cosets(G.carrier, P))"))))
			conjugatePSub := a.Have(
				"gPg⁻¹ is a p-subgroup: a subgroup of the finite G of the order p ^ n of P",
				"p_subgroup(G, p, group_conjugate(G, g, P))",
				By(
					Normalized,
					finiteG,
					conjugateSub,
					conjugateOrder,
					power,
					finite_group.SubgroupFinite.At(G, conjugate),
					finite_group.PSubgroupIff.Read(grp).At(p, conjugate)))
			a.Show(
				"so gPg⁻¹ is a p-subgroup whose index p does not divide",
				By(conjugatePSub, index, indivisible, SylowSubgroupDef.At(G, p, conjugate)))
		}),
})}
