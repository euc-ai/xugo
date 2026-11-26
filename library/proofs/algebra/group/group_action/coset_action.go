// coset_action.go — a group acting on the left cosets of a subgroup by left
// translation, and the cosets a subgroup fixes.

package group_action

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// CosetAction — a group acts on the left cosets of a subgroup by left
// translation, g · xH = gxH: the translate of a coset is again a coset
// (group.TranslateCoset), and the identity and product axioms are the
// group's own at each point of a coset, a subset of the carrier.
var CosetAction = cosetActionThm{family.Add(registry.ProofEntry{
	Name: "CosetAction",
	Key:  "prop_73ef0984c27f3366",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H:set(A).",
		Hypotheses: []string{
			"subgroup(G, H)",
		},
		Conclusion: "group_action(G, left_cosets(G.carrier, H), λg:A. λS:set(A). image(G.mul(g), S))",
	},
		func(a *Argument, grp group.GroupFact[on.G], H *Expr[Set[A]], sub Fact) {
			inside := group.SubgroupSubset.Read(sub)
			inCarrier := a.Have(
				"each coset of H lies in the carrier",
				"∀S:set(A). S ∈ left_cosets(G.carrier, H) ⇒ S ⊆ G.carrier",
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					coset := b.Assume()
					b.Show(
						"it is the coset of a point of the carrier",
						BySets(coset, inside, quotient_group.InLeftCosets.Read(grp).At(H, S), group.LeftCosetIn.Read(grp)))
				}))
			a.Do(GroupAction.Intro(
				Case(
					"G is a group",
					By(grp)),
				Case(
					"a translate of a coset of H is a coset of H",
					Derive(func(b *Argument) {
						g := b.FixAs[A]("g")
						S := b.FixAs[Set[A]]("S")
						point := b.Assume()
						parts := b.Conjuncts(
							point,
							"g lies in the carrier",
							"S is a coset of H")
						z, represented := b.ObtainAs[A](
							"S is the coset of a point z of the carrier",
							"∃z:A. S = left_coset(z, H) ∧ z ∈ G.carrier",
							By(parts[1], inside, quotient_group.InLeftCosets.Read(grp).At(H, S)))
						coset := b.Conjuncts(
							represented,
							"S is the coset of z",
							"z lies in the carrier")
						gm, zm := b.MemberOf[on.G](g, parts[0]), b.MemberOf[on.G](z, coset[1])
						b.Show(
							"and its translate by g, the coset g(zH), is the coset of g * z",
							coset[0].Rw(),
							Simp(Rev(group.LeftCosetDef)),
							By(
								inside,
								group.TranslateCoset.Read(grp).At(gm, zm, H),
								quotient_group.LeftCosetInLeftCosets.Read(grp).At(H, group.MulIn.Read(grp).At(gm, zm))))
					})),
				Case(
					"the identity fixes every coset of H",
					Derive(func(b *Argument) {
						S := b.FixAs[Set[A]]("S")
						coset := b.Assume()
						b.Show(
							"it fixes each point of S, a subset of the carrier",
							BySets(coset, inCarrier.At(S), grp, group.LeftIdentityOn))
					})),
				Case(
					"translating by g * h is translating by h and then by g",
					Derive(func(b *Argument) {
						g := b.FixAs[A]("g")
						h := b.FixAs[A]("h")
						S := b.FixAs[Set[A]]("S")
						points := b.Assume()
						b.Show(
							"at each point x of S, (g * h) * x is g * (h * x)",
							BySets(points, inCarrier.At(S), grp, group.AssocOn.Read(grp).AsFact().At(g, h)))
					})),
			))
		}),
})}

// CosetFixedIff — h fixes the coset gH exactly when g⁻¹hg lies in H. The
// translate of gH by h is the coset of hg (group.TranslateCoset), and the
// cosets of g and hg are equal exactly when g⁻¹(hg) lies in H.
var CosetFixedIff = cosetFixedIffThm{family.Add(registry.ProofEntry{
	Name: "CosetFixedIff",
	Key:  "prop_1ea45a3294d2da67",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H:set(A). ∀g h:A.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"h ∈ G.carrier",
			"subgroup(G, H)",
		},
		Conclusion: "image(G.mul(h), left_coset(g, H)) = left_coset(g, H) ⇔ G.inv(g) * h * g ∈ H",
	},
		func(a *Argument, grp group.GroupFact[on.G], H *Expr[Set[A]], sub Fact, g, h *Member[A, on.G]) {
			a.Show(
				"the translate of gH by h is the coset of h * g, which is gH "+
					"exactly when G.inv(g) * (h * g), that is G.inv(g) * h * g, lies in H",
				Simp(Rev(group.LeftCosetDef)),
				By(
					sub,
					group.SubgroupSubset.Read(sub),
					group.TranslateCoset.Read(grp).At(h, g, H),
					group.LeftCosetEqOn.Read(grp).At(g, group.MulIn.Read(grp).At(h, g), H),
					group.AssocOn.Read(grp).At(group.InvIn.Read(grp).At(g), h, g)))
		}),
})}

// FixedCosetsNormalizer — the cosets of a finite subgroup H that every
// element of H fixes are the cosets of H in its normalizer. By
// CosetFixedIff, H fixes gH exactly when g⁻¹Hg ⊆ H; H being finite and
// g⁻¹Hg of its size (ConjugateCard), that is g⁻¹Hg = H, so g⁻¹ and with it
// g lies in the normalizer. Conversely, H being normal in the normalizer,
// a point g there has g⁻¹hg in H for each h in H. The cosets of H in the
// normalizer are the cosets of its points (LeftCosetsImage at the
// normalizer, a group under the operations of G).
var FixedCosetsNormalizer = fixedCosetsNormalizerThm{family.Add(registry.ProofEntry{
	Name: "FixedCosetsNormalizer",
	Key:  "prop_e8bc28233b81b68b",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H:set(A).",
		Hypotheses: []string{
			"subgroup(G, H)",
			"finite(H)",
		},
		Conclusion: "{S:set(A) | S ∈ left_cosets(G.carrier, H) ∧ ∀h:A. h ∈ H ⇒ image(G.mul(h), S) = S} = " +
			"left_cosets(group_normalizer(G, H), H)",
	},
		func(a *Argument, grp group.GroupFact[on.G], H *Expr[Set[A]], sub, finite Fact) {
			G := a.TermAs[GroupOps[A]]("G")
			N := a.TermAs[Set[A]]("group_normalizer(G, H)")
			inside := group.SubgroupSubset.Read(sub)
			normalizer := a.Conjuncts(
				GroupPremises(sub, NormalizerSubgroup.Read(grp).At(H)),
				"the normalizer of H is a subgroup",
				"it holds H",
				"and H is normal in it")
			fixesIff := a.Have(
				"H fixes the coset of a point g of the carrier exactly when g lies in the normalizer",
				Statement{
					Binders: "∀g:A.",
					Hypotheses: []string{
						"g ∈ G.carrier",
					},
					Conclusion: "(∀h:A. h ∈ H ⇒ image(G.mul(h), left_coset(g, H)) = left_coset(g, H)) ⇔ " +
						"g ∈ group_normalizer(G, H)",
				},
				Derive(func(b *Argument) {
					g := b.FixAs[A]("g")
					gIn := b.Assume()
					gm := b.MemberOf[on.G](g, gIn)
					inverse := group.InvIn.Read(grp).At(gm)
					b.Iff()
					b.Forward(
						"if H fixes gH, g lies in the normalizer",
						func(c *Argument, fixed Fact) {
							into := c.Have(
								"conjugation by G.inv(g) maps H into H, the inverse of G.inv(g) being g",
								"group_conjugate(G, G.inv(g), H) ⊆ H",
								Unfold(GroupConjugateDef),
								BySets(
									Normalized,
									fixed,
									sub,
									inside,
									gIn,
									group.InvInvOn.Read(grp).At(gm),
									CosetFixedIff.Read(grp).AsFact().At(H, g)))
							onto := c.Have(
								"and onto H, its image of the finite H having the size of H",
								"group_conjugate(G, G.inv(g), H) = H",
								By(
									into,
									finite,
									inside,
									ConjugateCard.Read(grp).At(H, inverse),
									cardinality.CardSubsetEq.At(c.TermAs[Set[A]]("group_conjugate(G, G.inv(g), H)"), H)))
							c.Show(
								"so G.inv(g) lies in the normalizer, and with it g",
								BySets(
									onto,
									inverse,
									normalizer[0],
									GroupNormalizerDef.At(G, H),
									group.SubgroupInvIffOn.Read(grp).At(N, gm)))
						})
					b.Backward(
						"if g lies in the normalizer, H fixes gH",
						func(c *Argument, inN Fact) {
							inverseN := c.Have(
								"G.inv(g) lies in the normalizer too",
								"G.inv(g) ∈ group_normalizer(G, H)",
								By(inN, normalizer[0], group.SubgroupInv))
							h := c.FixAs[A]("h")
							inH := c.Assume()
							conjugate := c.Have(
								"H being normal in the normalizer, G.inv(g) * h * g lies in H",
								"G.inv(g) * h * g ∈ H",
								By(
									Normalized,
									inH,
									inverseN,
									group.NormalSubgroupConjugate.Read(normalizer[2]).AsFact().At(c.TermAs[A]("G.inv(g)"), h),
									group.RestrictGroupDef.At(G, N),
									group.InvInvOn.Read(grp).At(gm)))
							c.Show(
								"so h fixes gH",
								BySets(inH, conjugate, gIn, inside, sub, CosetFixedIff.Read(grp).AsFact().At(H, g, h)))
						})
				}))
			groupOnN := a.Have(
				"the normalizer is a group under the operations of G",
				"group_on(restrict_group(G, group_normalizer(G, H)))",
				By(normalizer[0], group.SubgroupGroupOn.Read(grp).At(N)))
			cosetsOfN := a.Have(
				"the cosets of H in the normalizer are the cosets of its points",
				"left_cosets(group_normalizer(G, H), H) = image(coset_map(G.mul, H), group_normalizer(G, H))",
				By(
					normalizer[1],
					quotient_group.LeftCosetsImage.Read(groupOnN).At(H),
					group.RestrictGroupDef.At(G, N)))
			a.Show(
				"so the cosets H fixes are the cosets of the points of the normalizer",
				cosetsOfN.Rw(),
				// Extension is pinned at sets of cosets: the bare rule would
				// also read each equation image(G.mul(h), S) = S inside the
				// set-builder point by point, where fixesIff states it whole.
				Simp(Fwd(set_basic.Extension.Inst[Set[A]]())),
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					b.Iff()
					b.Forward(
						"a coset H fixes is the coset of a point of the normalizer",
						func(c *Argument, fixed Fact) {
							parts := c.Conjuncts(
								fixed,
								"S is a coset of H",
								"every element of H fixes S")
							g, represented := c.ObtainAs[A](
								"S is the coset of a point g of the carrier",
								"∃g:A. S = left_coset(g, H) ∧ g ∈ G.carrier",
								By(parts[0], inside, quotient_group.InLeftCosets.Read(grp).At(H, S)))
							normalizes := c.Have(
								"H fixing its coset, g lies in the normalizer",
								"g ∈ group_normalizer(G, H)",
								By(Normalized, parts[1], represented, fixesIff.At(g)))
							c.Show(
								"so S is the coset of a point of the normalizer",
								BySets(normalizes, represented, group.CosetMapDef.At(c.TermAs[Op[A]]("G.mul"), H)))
						})
					b.Backward(
						"the coset of a point of the normalizer is a coset H fixes",
						func(c *Argument, inImage Fact) {
							g, represented := c.ObtainAs[A](
								"S is the coset of a point g of the normalizer",
								"∃g:A. g ∈ group_normalizer(G, H) ∧ S = coset_map(G.mul, H, g)",
								By(inImage, set_basic.InImage.At(c.TermAs[Fun[A, Set[A]]]("coset_map(G.mul, H)"), N, S)))
							parts := c.Conjuncts(
								c.Simplified(represented, Fwd(group.CosetMapDef)),
								"g lies in the normalizer",
								"S is its coset")
							inCarrier := c.Have(
								"g lies in the carrier, as the normalizer does",
								"g ∈ G.carrier",
								By(parts[0], group.SubgroupSubset.Read(normalizer[0]), set_basic.SubsetDef))
							c.Show(
								"which is a coset of H that H fixes",
								parts[1].Rw(),
								By(
									parts[0],
									inside,
									quotient_group.LeftCosetInLeftCosets.Read(grp).At(H, c.MemberOf[on.G](g, inCarrier)),
									fixesIff.At(g),
									inCarrier))
						})
				}))
		}),
})}
