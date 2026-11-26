// correspondence.go — the subgroups of a quotient G/N read back in G, one
// direction of the correspondence theorem: the preimage of a subgroup S of
// the quotient under the coset map is a subgroup of G holding N, with
// card(N) * card(S) points.

package quotient_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// PreimageSubgroup — the preimage of a subgroup of G/N under the coset
// map is a subgroup of G holding N. The preimage is the set of points of
// the carrier whose coset lies in S, and S, read at the quotient's
// record, holds the quotient's identity N and is closed under the product
// and the inverse of sets. The coset map carries G.one to N
// (group.LeftCosetOneOn), a product to the product of the cosets
// (LeftCosetMulOn) and an inverse to the inverse of the coset
// (LeftCosetInvOn), so the preimage holds G.one and is closed under both;
// and a point of N has N itself as its coset (LeftCosetIsSubgroupIffIn).
var PreimageSubgroup = preimageSubgroupThm{family.Add(registry.ProofEntry{
	Name: "PreimageSubgroup",
	Key:  "prop_d8b7262e9ef2e904",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀N:set(A). ∀S:set(set(A)).",
		Hypotheses: []string{
			"normal_subgroup(G, N)",
			"subgroup(quotient_group(G, N), S)",
		},
		Conclusion: "subgroup(G, preimage_on(G.carrier, coset_map(G.mul, N), S)) ∧ " +
			"N ⊆ preimage_on(G.carrier, coset_map(G.mul, N), S)",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			N *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			normal, quotientSub Fact,
		) {
			nSub := a.Have(
				"a normal subgroup is a subgroup",
				"subgroup(G, N)",
				By(group.NormalSubgroupSubgroup, normal))
			nInC := a.Have(
				"which lies in G.carrier",
				"N ⊆ G.carrier",
				By(group.SubgroupSubset, nSub))
			inS := a.Conjuncts(
				a.Unfolded(quotientSub, group.SubgroupDef),
				"S is a set of cosets of N",
				"S holds N, the identity of the quotient",
				"S is closed under the product of cosets",
				"and under the inverse of a coset")
			nInS, mulInS, invInS := inS[1], inS[2], inS[3]
			preimage := a.Have(
				"the preimage is the set of points of G.carrier whose coset lies in S",
				"preimage_on(G.carrier, coset_map(G.mul, N), S) = {x:A | x ∈ G.carrier ∧ left_coset(x, N) ∈ S}",
				By(functions.PreimageOnDef, group.CosetMapDef))
			a.Show(
				"the points of G.carrier whose coset lies in S form a subgroup holding N",
				preimage.Rw(),
				SplitConj(
					Case(
						"they form a subgroup of G: the four conditions",
						Simp(Fwd(group.SubgroupDef)),
						SplitConjAll(
							Case(
								"they lie in G.carrier",
								BySets()),
							Case(
								"G.one is one of them: its coset is N, which S holds",
								By(Normalized, nInC, nInS, group.OneIn.Read(grp), group.LeftCosetOneOn.Read(grp).At(N))),
							Case(
								"they are closed under the product: the coset of x * y is the product of the cosets of x and y",
								Derive(func(b *Argument) {
									x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
									both := b.Conjuncts(
										b.Assume(),
										"x is one of them",
										"so is y")
									xParts := b.Conjuncts(
										both[0],
										"x lies in G.carrier",
										"and its coset lies in S")
									yParts := b.Conjuncts(
										both[1],
										"y lies in G.carrier",
										"and its coset lies in S")
									xm, ym := b.MemberOf[on.G](x, xParts[0]), b.MemberOf[on.G](y, yParts[0])
									b.Show(
										"x * y lies in G.carrier, and its coset, the product of two cosets in S, lies in S",
										By(
											normal,
											xParts[1],
											yParts[1],
											mulInS.At(b.TermAs[Set[A]]("left_coset(x, N)"), b.TermAs[Set[A]]("left_coset(y, N)")),
											group.MulIn.Read(grp).At(xm, ym),
											LeftCosetMulOn.Read(grp).At(N, xm, ym)))
								})),
							Case(
								"they are closed under the inverse: the coset of G.inv(x) is the inverse of the coset of x",
								Derive(func(b *Argument) {
									x := b.FixAs[A]("x")
									parts := b.Conjuncts(
										b.Assume(),
										"x lies in G.carrier",
										"and its coset lies in S")
									xm := b.MemberOf[on.G](x, parts[0])
									b.Show(
										"G.inv(x) lies in G.carrier, and its coset, the inverse of a coset in S, lies in S",
										By(
											normal,
											parts[1],
											invInS.At(b.TermAs[Set[A]]("left_coset(x, N)")),
											group.InvIn.Read(grp).At(xm),
											LeftCosetInvOn.Read(grp).At(N, xm)))
								})),
						)),
					Case(
						"they hold N: a point of N lies in G.carrier and has N itself as its coset",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							xIn := b.Assume()
							xm := b.MemberOf[on.G](x, b.Have(
								"x lies in G.carrier",
								"x ∈ G.carrier",
								By(xIn, nInC, set_basic.SubsetDef)))
							b.Show(
								"x lies in G.carrier, and its coset is N, which S holds",
								By(Normalized, xIn, nSub, nInS, LeftCosetIsSubgroupIffIn.Read(grp).At(xm, N)))
						})),
				))
		}),
})}

// PreimageCard — for a finite group, the preimage of a subgroup S of G/N
// has card(N) * card(S) points. The preimage P is a subgroup of G holding
// N (PreimageSubgroup), finite as a subgroup of a finite group, so Lagrange's
// theorem at N inside P (finite_group.LagrangeOn) counts it as card(N) times the
// number of cosets of N by points of P. Those cosets are S: each member of
// S is a coset of N, the coset of a point of G.carrier (LeftCosetsImage),
// and that point lies in P.
var PreimageCard = preimageCardThm{family.Add(registry.ProofEntry{
	Name: "PreimageCard",
	Key:  "prop_c4b1d34b32638875",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀N:set(A). ∀S:set(set(A)).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"normal_subgroup(G, N)",
			"subgroup(quotient_group(G, N), S)",
		},
		Conclusion: "card(preimage_on(G.carrier, coset_map(G.mul, N), S)) = card(N) * card(S)",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			N *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			finite, normal, quotientSub Fact,
		) {
			preimage := a.Conjuncts(
				GroupPremises(normal, quotientSub, PreimageSubgroup.Read(grp).At(N, S)),
				"the preimage of S is a subgroup of G",
				"holding N")
			P, pDef := a.LetAs[Set[A]]("P", "preimage_on(G.carrier, coset_map(G.mul, N), S)")
			nSub := a.Have(
				"a normal subgroup is a subgroup",
				"subgroup(G, N)",
				By(group.NormalSubgroupSubgroup, normal))
			nInC := a.Have(
				"which lies in G.carrier",
				"N ⊆ G.carrier",
				By(group.SubgroupSubset, nSub))
			inImage := a.Have(
				"every member of S is the coset of a point of G.carrier: S lies among "+
					"the cosets of N, which are the image of G.carrier under the coset map",
				"S ⊆ image(coset_map(G.mul, N), G.carrier)",
				By(Normalized, nInC, group.SubgroupSubset.Read(quotientSub), LeftCosetsImage.Read(grp).At(N)))
			onto := a.Have(
				"so the coset map carries P onto S",
				"image(coset_map(G.mul, N), P) = S",
				BySets(pDef, inImage))
			finiteP := a.Have(
				"P is finite, a subgroup of the finite G",
				"finite(P)",
				By(finite, preimage[0], finite_group.SubgroupFinite.At(a.TermAs[GroupOps[A]]("G"), P)))
			a.Show(
				"Lagrange's theorem at N inside P counts P as card(N) "+
					"times the number of its cosets of N, which are S",
				By(
					Normalized,
					nSub,
					preimage[0],
					preimage[1],
					finiteP,
					onto,
					finite_group.LagrangeOn.Read(grp).At(N, P)))
		}),
})}
