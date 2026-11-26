// counting.go — counting the left cosets of a subgroup: a transversal
// counts them, Lagrange's theorem counts a finite group as a subgroup's
// order times its index, a group is finite exactly when a subgroup and its
// cosets are, the index is multiplicative along a tower of subgroups of any
// group, and a strictly larger subgroup has a strictly smaller finite
// index. None of it needs a normal subgroup or the quotient group.
//
// The group hypothesis is named `grp` throughout: this package imports
// the group chapter as `group`, and the group chapter's usual name for its
// hypothesis would shadow it.

package quotient_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// LeftCosetsTransversalSize — a set T of k points of the carrier meeting
// every left coset of a subgroup h in exactly one point counts the cosets:
// there are k of them. The coset map v ↦ v·h is one-to-one on T, two points
// of T in one coset being equal, and onto the cosets, each coset being the
// coset of the point of T it holds.
var LeftCosetsTransversalSize = leftCosetsTransversalSizeThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetsTransversalSize",
	Key:  "prop_65cc46e5dd727bc2",
	Build: family.Sections(group.GroupOn.Statement(Statement{
		Binders: "∀h T:set(A). ∀k:num.",
		Hypotheses: []string{
			"subgroup(G, h)",
			"T ⊆ G.carrier",
			"has_size(T, k)",
			"∀X:set(A). X ∈ left_cosets(G.carrier, h) ⇒ ∃v:A. v ∈ X ∧ v ∈ T ∧ (∀w:A. w ∈ X ∧ w ∈ T ⇒ w = v)",
		},
		Conclusion: "has_size(left_cosets(G.carrier, h), k)",
	}), func(ctx *Script, headline string) *GoalStackNode {
		cosetMember := ctx.Lemma(group.GroupOn.Statement(Statement{
			Binders: "∀h X:set(A). ∀v:A.",
			Hypotheses: []string{
				"subgroup(G, h)",
				"X ∈ left_cosets(G.carrier, h)",
				"v ∈ X",
			},
			Conclusion: "v ∈ G.carrier ∧ left_coset(v, h) = X",
		}), func(a *Argument, grp group.GroupFact[on.G], h, X *Expr[Set[A]], v *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"h is a subgroup",
				"X is a quotient coset",
				"v belongs to X")
			subset := a.Have(
				"the subgroup lies in the group carrier",
				"h ⊆ G.carrier",
				By(parts[0], group.SubgroupSubset))
			x, presentation := a.ObtainAs[A](
				"choose a group point presenting X",
				"∃x:A. X = left_coset(x, h) ∧ x ∈ G.carrier",
				By(parts[1], subset, InLeftCosets.Read(grp).At(h, X)),
				Named("x"))
			present := a.Conjuncts(
				presentation,
				"X is the coset of x",
				"x lies in the group carrier")
			a.Show(
				"each coset member presents the same coset",
				present[0].Rw(),
				Derive(func(b *Argument) {
					xm := b.MemberOf[on.G](x, present[1])
					vIn := b.Have(
						"a coset member is a group point",
						"v ∈ G.carrier",
						By(parts[2], subset, group.CosetClosedOn.Read(grp).At(h, xm, v)))
					vm := b.MemberOf[on.G](v, vIn)
					difference := b.Have(
						"the group difference lies in h",
						"G.mul(G.inv(x), v) ∈ h",
						By(parts[2], subset, group.InLeftCosetOn.Read(grp).At(xm, vm, h)))
					b.Show(
						"the coset equality law identifies the two presentations",
						By(vIn, difference, parts[0], group.LeftCosetEqOn.Read(grp).At(xm, vm, h)))
				}))
		})
		ownCoset := ctx.Lemma(group.GroupOn.Statement(Statement{
			Binders: "∀h:set(A). ∀v:A.",
			Hypotheses: []string{
				"subgroup(G, h)",
				"v ∈ G.carrier",
			},
			Conclusion: "left_coset(v, h) ∈ left_cosets(G.carrier, h) ∧ v ∈ left_coset(v, h)",
		}), func(a *Argument, grp group.GroupFact[on.G], h *Expr[Set[A]], v *Expr[A], given Fact) {
			a.Show(
				"a group point belongs to its own quotient coset",
				By(
					given,
					group.SubgroupSubset,
					InLeftCosets.Read(grp).At(h, a.TermAs[Set[A]]("left_coset(v, h)")),
					group.InOwnLeftCosetOn.Read(grp).AsFact().At(v, h)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			grp group.GroupFact[on.G],
			h, T *Expr[Set[A]],
			k *Expr[Nat],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"h is a subgroup",
				"the representatives lie in the group",
				"T has size k",
				"every coset has a unique representative in T")
			groupRecord := a.TermAs[group.GroupOps[A]]("G")
			cosetMap := a.TermAs[Fun[A, Set[A]]]("λv:A. left_coset(v, h)")
			quotient := a.TermAs[Set[Set[A]]]("left_cosets(G.carrier, h)")
			into := a.Have(
				"each representative lies in its own quotient coset",
				"∀v:A. v ∈ T ⇒ left_coset(v, h) ∈ left_cosets(G.carrier, h) ∧ v ∈ left_coset(v, h)",
				BySets(grp, parts[0], parts[1], At(ownCoset, groupRecord, h)))
			injective := a.Have(
				"the coset map is injective on representatives",
				"injective_on(T, λv:A. left_coset(v, h))",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					equalImages := b.Assume()
					data := b.Conjuncts(
						equalImages,
						"x belongs to T",
						"y belongs to T",
						"their cosets agree")
					xOwn := b.Have(
						"x belongs to its quotient coset",
						"left_coset(x, h) ∈ left_cosets(G.carrier, h) ∧ x ∈ left_coset(x, h)",
						By(data[0], into.At(x)))
					yOwn := b.Have(
						"y belongs to its quotient coset",
						"left_coset(y, h) ∈ left_cosets(G.carrier, h) ∧ y ∈ left_coset(y, h)",
						By(data[1], into.At(y)))
					common := b.Have(
						"x also lies in the coset of y",
						"x ∈ left_coset(y, h)",
						data[2].RwRev(),
						By(xOwn))
					b.Show(
						"uniqueness in the common coset identifies x and y",
						By(data[0], data[1], common, yOwn, parts[3].At(b.TermAs[Set[A]]("left_coset(y, h)"))))
				}))
			onto := a.Have(
				"each quotient coset is the image of its representative",
				"∀X:set(A). X ∈ left_cosets(G.carrier, h) ⇒ ∃v:A. v ∈ T ∧ X = left_coset(v, h)",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					inQuotient := b.Assume()
					v, representative := b.ObtainAs[A](
						"choose the representative in X",
						"∃v:A. v ∈ X ∧ v ∈ T ∧ (∀w:A. w ∈ X ∧ w ∈ T ⇒ w = v)",
						By(inQuotient, parts[3].At(X)),
						Named("v"))
					b.Show(
						"this representative presents X",
						Witness(v),
						By(Normalized, grp, inQuotient, parts[0], representative, At(cosetMember, groupRecord, h, X, v)))
				}))
			imageInside := a.Have(
				"the representative image lies in the quotient",
				"image(λv:A. left_coset(v, h), T) ⊆ left_cosets(G.carrier, h)",
				By(into, set_image.ImageSubsetIff.At(cosetMap, T, quotient)))
			imageCovers := a.Have(
				"the representative image covers the quotient",
				"left_cosets(G.carrier, h) ⊆ image(λv:A. left_coset(v, h), T)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					inQuotient := b.Assume()
					b.Show(
						"the explicit preimage gives image membership",
						By(inQuotient, onto.At(X), set_basic.InImage.At(cosetMap, T, X)))
				}))
			image := a.Have(
				"the representative image equals the quotient",
				"image(λv:A. left_coset(v, h), T) = left_cosets(G.carrier, h)",
				By(
					imageInside,
					imageCovers,
					set_order.SubsetAntisym.At(a.TermAs[Set[Set[A]]]("image(λv:A. left_coset(v, h), T)"), quotient)))
			a.Show(
				"the coset bijection preserves the size",
				image.RwRev(),
				By(parts[2], injective, cardinality.HasSizeImageInj.At(cosetMap, T, k)))
		})
	}),
})}

// LagrangeIndex — Lagrange's theorem counted by the cosets: the order of a
// finite group is the order of a subgroup times its index, the number of
// its left cosets. The carrier is a subgroup of itself, so Lagrange's count
// of a subgroup inside a larger one (finite_group.LagrangeOn) applies inside the
// carrier, and there it counts the image of the carrier under the coset
// map, which is the set of cosets (LeftCosetsImage).
var LagrangeIndex = lagrangeIndexThm{family.Add(registry.ProofEntry{
	Name: "LagrangeIndex",
	Key:  "prop_5577e961e8313e8c",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"subgroup(G, H)",
		},
		Conclusion: "card(G.carrier) = card(H) * card(left_cosets(G.carrier, H))",
	},
		func(a *Argument, grp group.GroupFact[on.G], H *Expr[Set[A]], finite, subgroup Fact) {
			a.Show(
				"Lagrange's count of H inside the carrier, a subgroup of itself, "+
					"where the cosets of H are the image of the carrier under the coset map",
				By(
					Normalized,
					finite,
					subgroup,
					group.CarrierSubgroupOn.Read(grp),
					finite_group.LagrangeOn.Read(grp).At(H, a.TermAs[Set[A]]("G.carrier")),
					LeftCosetsImage.Read(grp).At(H),
					group.SubgroupSubset.Read(subgroup)))
		}),
})}

// FiniteIffSubgroupAndCosets — a group is finite exactly when a subgroup
// and its set of cosets are. A finite carrier has the subgroup as a finite
// subgroup (finite_group.SubgroupFinite) and finitely many cosets
// (LeftCosetsFinite). Conversely the cosets are the classes of an
// equivalence on the carrier, so they cover it, and each, the coset of a
// point of the carrier, has as many points as the subgroup, so finitely
// many of them have a finite union, the carrier.
var FiniteIffSubgroupAndCosets = finiteIffSubgroupAndCosetsThm{family.Add(registry.ProofEntry{
	Name: "FiniteIffSubgroupAndCosets",
	Key:  "prop_4f661d024921ccfd",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀h:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
		},
		Conclusion: "finite(G.carrier) ⇔ finite(h) ∧ finite(left_cosets(G.carrier, h))",
	},
		func(a *Argument, grp group.GroupFact[on.G], h *Expr[Set[A]], sub Fact) {
			subset := a.Have(
				"h lies in the carrier",
				"h ⊆ G.carrier",
				By(group.SubgroupSubset.Read(sub)))
			a.Iff()
			a.Forward(
				"a finite carrier has a finite subgroup and finitely many cosets",
				func(b *Argument, finiteCarrier Fact) {
					b.Show(
						"both sets are finite",
						SplitConj(
							Case(
								"the subgroup of the finite G is finite",
								By(finiteCarrier, sub, finite_group.SubgroupFinite.At(b.TermAs[GroupOps[A]]("G"), h))),
							Case(
								"the finite carrier has finitely many cosets",
								By(finiteCarrier, LeftCosetsFinite.At(b.TermAs[Op[A]]("G.mul"), b.TermAs[Set[A]]("G.carrier"), h))),
						))
				})
			a.Backward(
				"finitely many finite cosets have finite union, the carrier",
				func(b *Argument, finiteParts Fact) {
					equivalent := b.Have(
						"lying in one h-coset is an equivalence relation",
						"equivalence_on(G.carrier, λx:A. λy:A. y ∈ left_coset(x, h))",
						By(sub, group.CosetEquivalenceOn.Read(grp).At(h)))
					cover := b.Have(
						"so its classes, the cosets, cover the carrier",
						"⋃left_cosets(G.carrier, h) = G.carrier",
						Unfold(LeftCosetsDef),
						By(equivalence.QuotientOnCovers.Read(equivalent)))
					cosets := b.TermAs[Set[Set[A]]]("left_cosets(G.carrier, h)")
					cardH := b.TermAs[Nat]("card(h)")
					sizedH := b.Have(
						"h, being finite, has card(h) points",
						"has_size(h, card(h))",
						By(finiteParts, cardinality.FiniteHasSize.At(h)))
					eachFinite := b.Have(
						"every coset is finite: the coset of a point of the carrier has card(h) points",
						"∀s:set(A). s ∈ left_cosets(G.carrier, h) ⇒ finite(s)",
						Simp(Fwd(ForallInLeftCosets.Read(grp))),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							c.Show(
								"the coset of x has card(h) points, as many as h, so it is finite",
								By(
									subset,
									sizedH,
									finite_group.LeftCosetSizeOn.Read(grp).At(c.MemberOf[on.G](x, xIn), h, cardH),
									cardinality.HasSizeDef.At(c.TermAs[Set[A]]("left_coset(x, h)"), cardH)))
						}))
					finiteUnion := b.Have(
						"the union of the finite cosets is finite",
						"finite(⋃left_cosets(G.carrier, h))",
						By(eachFinite, finiteParts, finite_set.FiniteUnions.At(cosets)))
					b.Show(
						"their union, the carrier, is finite",
						By(Normalized, finiteUnion, cover))
				})
		}),
})}

// IndexMultiplicative — for a subgroup K of a group and a set H ⊆ K
// holding the identity, the index of H is finite exactly when the index of
// K and that of H in K are, and it is then their product,
// [G:H] = [G:K][K:H]. The cosets of H inside a coset xK, its block, are the
// translates by x of the cosets of H in K, as many as those, translation by
// x being one-to-one. Two cosets of K whose blocks share a coset of H are
// one, so the blocks are disjoint, one for each coset of K, and together
// they hold every coset of H.
var IndexMultiplicative = indexMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "IndexMultiplicative",
	Key:  "prop_b9bb312bfc7eca51",
	Reading: "The indices are the cardinalities of sets of left cosets, so neither G nor K " +
		"need be finite, and K need not be normal. H need not be a subgroup either: a set inside " +
		"K holding the identity is all the counting reads, the form LeftCosetSetMulAbsorb takes.",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H K:set(A).",
		Hypotheses: []string{
			"subgroup(G, K)",
			"H ⊆ K",
			"G.one ∈ H",
		},
		Conclusion: "(finite(left_cosets(G.carrier, H)) ⇔ " +
			"    finite(left_cosets(G.carrier, K)) ∧ finite(left_cosets(K, H))) ∧ " +
			"(finite(left_cosets(G.carrier, H)) ⇒ " +
			"    card(left_cosets(G.carrier, H)) = card(left_cosets(G.carrier, K)) * card(left_cosets(K, H)))",
	},
		func(a *Argument, grp group.GroupFact[on.G], H, K *Expr[Set[A]], subK, hInK, oneInH Fact) {
			G, mul := a.TermAs[GroupOps[A]]("G"), a.TermAs[Op[A]]("G.mul")
			carrier := a.TermAs[Set[A]]("G.carrier")
			cosetMapH := a.TermAs[Fun[A, Set[A]]]("coset_map(G.mul, H)")
			cosetsH := a.TermAs[Set[Set[A]]]("left_cosets(G.carrier, H)")
			cosetsK := a.TermAs[Set[Set[A]]]("left_cosets(G.carrier, K)")
			cosetsKH := a.TermAs[Set[Set[A]]]("left_cosets(K, H)")
			kInC := a.Have(
				"K lies in the carrier",
				"K ⊆ G.carrier",
				By(group.SubgroupSubset.Read(subK)))
			hInC := a.Have(
				"and so does H",
				"H ⊆ G.carrier",
				BySets(hInK, kInC))
			groupK := a.Have(
				"K is a group under the operations of G",
				"group_on(restrict_group(G, K))",
				By(subK, group.SubgroupGroupOn.Read(grp).At(K)))
			imageH := a.Have(
				"the cosets of H are the cosets of the points of the carrier",
				"left_cosets(G.carrier, H) = image(coset_map(G.mul, H), G.carrier)",
				By(hInC, LeftCosetsImage.Read(grp).At(H)))
			imageKH := a.Have(
				"and the cosets of H in K those of the points of K",
				"left_cosets(K, H) = image(coset_map(G.mul, H), K)",
				By(hInK, LeftCosetsImage.Read(groupK).At(H), group.RestrictGroupDef.At(G, K)))
			// The block of a coset T of K is the set of the cosets of H inside it,
			// image(coset_map(G.mul, H), T); blocks is the set of the blocks.
			blocks, blocksDef := a.LetAs[Set[Set[Set[A]]]](
				"blocks", "image(image(coset_map(G.mul, H)), left_cosets(G.carrier, K))")
			translates := a.Have(
				"the block of a coset xK is the set of the translates by x of the cosets of H in K",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ G.carrier",
					},
					Conclusion: "image(coset_map(G.mul, H), left_coset(x, K)) = " +
						"image(λS:set(A). left_coset(x, S), left_cosets(K, H))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xm := b.MemberOf[on.G](x, b.Assume())
					pointwise := b.Have(
						"the coset of H of x * k is the translate by x of the coset of k",
						"∀k:A. k ∈ K ⇒ left_coset(x * k, H) = left_coset(x, left_coset(k, H))",
						Derive(func(c *Argument) {
							k := c.FixAs[A]("k")
							kIn := c.Assume()
							km := c.MemberOf[on.G](k, c.Have(
								"k lies in the carrier",
								"k ∈ G.carrier",
								BySets(kIn, kInC)))
							c.Show(
								"translating the coset of k by x",
								By(hInC, group.TranslateCoset.Read(grp).At(xm, km, H)))
						}))
					translated := b.Have(
						"xK is the image of K under translation by x",
						"left_coset(x, K) = image(λy:A. x * y, K)",
						By(group.LeftCosetDef.At(mul, x, K)))
					b.Show(
						"both are images of K, under k ↦ (x * k)H and k ↦ x(kH), which agree on K",
						imageKH.Rw(),
						translated.Rw(),
						// ImageCompose at its two type instances, a map of points
						// after a translation and a map of sets after the coset map.
						Simp(
							Rev(set_image.ImageCompose.Inst(
								TypeBinder.BindA[A](), TypeBinder.BindB[A](), TypeBinder.BindC[Set[A]]())),
							Rev(set_image.ImageCompose.Inst(
								TypeBinder.BindA[A](), TypeBinder.BindB[Set[A]](), TypeBinder.BindC[Set[A]]()))),
						Unfold(functions.ComposeApply),
						Unfold(group.CosetMapDef),
						By(pointwise, set_image.ImageCongruence))
				}))
			sized := a.Have(
				"so the block of a coset of K has as many members as K "+
					"has cosets of H, translation by x being one-to-one on them",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"finite(left_cosets(K, H))",
						"x ∈ G.carrier",
					},
					Conclusion: "has_size(image(coset_map(G.mul, H), left_coset(x, K)), card(left_cosets(K, H)))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					given := b.Conjuncts(
						b.Assume(),
						"K has finitely many cosets of H",
						"x lies in the carrier")
					xm := b.MemberOf[on.G](x, given[1])
					inverse := group.InvIn.Read(grp).At(xm)
					back := b.Have(
						"translating by G.inv(x) undoes translating by x on the cosets of H in K",
						"∀S:set(A). S ∈ left_cosets(K, H) ⇒ left_coset(G.inv(x), left_coset(x, S)) = S",
						imageKH.Rw(),
						Simp(Fwd(set_image.ForallInImage)),
						Unfold(group.CosetMapDef),
						Derive(func(c *Argument) {
							k := c.FixAs[A]("k")
							kIn := c.Assume()
							km := c.MemberOf[on.G](k, c.Have(
								"k lies in the carrier",
								"k ∈ G.carrier",
								BySets(kIn, kInC)))
							c.Show(
								"x(kH) is (x * k)H, which G.inv(x) carries to (G.inv(x) * (x * k))H, that is kH",
								By(
									Normalized,
									hInC,
									group.TranslateCoset.Read(grp).At(xm, km, H),
									group.TranslateCoset.Read(grp).At(inverse, group.MulIn.Read(grp).At(xm, km), H),
									group.InvMulCancelLeftOn.Read(grp).At(xm, km)))
						}))
					translate := b.TermAs[Fun[Set[A], Set[A]]]("λS:set(A). left_coset(x, S)")
					oneToOne := b.Have(
						"so translation by x is one-to-one on the cosets of H in K",
						"injective_on(left_cosets(K, H), λS:set(A). left_coset(x, S))",
						Simp(Fwd(functions.InjectiveOnDef)),
						Derive(func(c *Argument) {
							S, T := c.FixAs[Set[A]]("S"), c.FixAs[Set[A]]("T")
							pair := c.Conjuncts(
								c.Assume(),
								"S is a coset of H in K",
								"so is T",
								"x translates them alike")
							c.Show(
								"each is the translate back of its translate by x",
								By(pair[2], pair[0], pair[1], back.At(S), back.At(T)))
						}))
					b.Show(
						"the block of xK is the set of the translates of the cosets of H in K",
						By(
							given[0],
							given[1],
							oneToOne,
							translates.At(x),
							cardinality.FiniteHasSize.At(cosetsKH),
							cardinality.HasSizeImageInj.At(translate, cosetsKH, b.TermAs[Nat]("card(left_cosets(K, H))"))))
				}))
			blockSize := a.Have(
				"each block has as many members as K has cosets of H",
				"∀X:set(set(A)). finite(left_cosets(K, H)) ∧ X ∈ blocks ⇒ has_size(X, card(left_cosets(K, H)))",
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("X")
					given := b.Conjuncts(
						b.Assume(),
						"K has finitely many cosets of H",
						"X is a block")
					T, ofT := b.ObtainAs[Set[A]](
						"X is the block of a coset T of K",
						"∃T:set(A). X = image(coset_map(G.mul, H), T) ∧ T ∈ left_cosets(G.carrier, K)",
						By(b.Simplified(given[1], Fwd(blocksDef)), set_basic.InImage))
					parts := b.Conjuncts(
						ofT,
						"X is the block of T",
						"T is a coset of K")
					x, atX := b.ObtainAs[A](
						"T is the coset of a point x of the carrier",
						"∃x:A. T = left_coset(x, K) ∧ x ∈ G.carrier",
						By(parts[1], kInC, InLeftCosets.Read(grp).At(K, T)))
					b.Show(
						"the block of xK has [K:H] members",
						By(Normalized, given[0], parts[0], atX, sized.At(x)))
				}))
			presents := a.Have(
				"a point of the coset xK lies in the carrier and its coset of K is xK",
				Statement{
					Binders: "∀x v:A.",
					Hypotheses: []string{
						"x ∈ G.carrier",
						"v ∈ left_coset(x, K)",
					},
					Conclusion: "v ∈ G.carrier ∧ left_coset(v, K) = left_coset(x, K)",
				},
				Derive(func(b *Argument) {
					x, v := b.FixAs[A]("x"), b.FixAs[A]("v")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in the carrier",
						"v lies in xK")
					xm := b.MemberOf[on.G](x, given[0])
					vIn := b.Have(
						"v lies in the carrier",
						"v ∈ G.carrier",
						By(given[1], kInC, group.CosetClosedOn.Read(grp).At(K, xm, v)))
					vm := b.MemberOf[on.G](v, vIn)
					b.Show(
						"G.inv(x) * v lies in K, which makes the two cosets one",
						By(
							vIn,
							given[1],
							subK,
							kInC,
							group.InLeftCosetOn.Read(grp).At(xm, vm, K),
							group.LeftCosetEqOn.Read(grp).At(xm, vm, K)))
				}))
			meet := a.Have(
				"two cosets of K whose blocks share a coset of H are one",
				Statement{
					Binders: "∀x y:A. ∀S:set(A).",
					Hypotheses: []string{
						"x ∈ G.carrier ∧ y ∈ G.carrier",
						"S ∈ image(coset_map(G.mul, H), left_coset(x, K))",
						"S ∈ image(coset_map(G.mul, H), left_coset(y, K))",
					},
					Conclusion: "left_coset(x, K) = left_coset(y, K)",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					b.FixAs[Set[A]]("S")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in the carrier",
						"so does y",
						"S lies in the block of xK",
						"and in that of yK")
					u, atU := b.ObtainAs[A](
						"S is the coset of H of a point u of xK",
						"∃u:A. S = left_coset(u, H) ∧ u ∈ left_coset(x, K)",
						Unfold(group.CosetMapDef),
						By(given[2], set_basic.InImage))
					v, atV := b.ObtainAs[A](
						"and of a point v of yK",
						"∃v:A. S = left_coset(v, H) ∧ v ∈ left_coset(y, K)",
						Unfold(group.CosetMapDef),
						By(given[3], set_basic.InImage))
					uParts := b.Conjuncts(
						atU,
						"S is uH",
						"u lies in xK")
					vParts := b.Conjuncts(
						atV,
						"S is vH",
						"v lies in yK")
					fromU := b.Conjuncts(
						GroupPremises(given[0], uParts[1], presents.At(x, u)),
						"u lies in the carrier",
						"uK is xK")
					fromV := b.Conjuncts(
						GroupPremises(given[1], vParts[1], presents.At(y, v)),
						"v lies in the carrier",
						"vK is yK")
					um, vm := b.MemberOf[on.G](u, fromU[0]), b.MemberOf[on.G](v, fromV[0])
					inUH := b.Have(
						"v lies in its own coset of H, G.inv(v) * v being G.one, which is that of u",
						"v ∈ left_coset(u, H)",
						By(
							Normalized,
							uParts[0],
							vParts[0],
							oneInH,
							hInC,
							group.LeftInverseOn.Read(grp).At(vm),
							group.InLeftCosetOn.Read(grp).At(vm, vm, H)))
					inH := b.Have(
						"so G.inv(u) * v lies in H",
						"G.inv(u) * v ∈ H",
						By(inUH, hInC, group.InLeftCosetOn.Read(grp).At(um, vm, H)))
					inK := b.Have(
						"and with it in K, H lying in K",
						"G.inv(u) * v ∈ K",
						BySets(inH, hInK))
					inUK := b.Have(
						"so v lies in uK",
						"v ∈ left_coset(u, K)",
						By(inK, kInC, group.InLeftCosetOn.Read(grp).At(um, vm, K)))
					b.Show(
						"so vK is uK, and xK = uK = vK = yK",
						By(fromU[1], fromV[1], fromU[0], inUK, presents.At(u, v)))
				}))
			apart := a.Have(
				"two different blocks are disjoint",
				"∀X Y:set(set(A)). X ∈ blocks ∧ Y ∈ blocks ⇒ (X ≠ Y ⇒ disjoint(X, Y))",
				blocksDef.Rw(),
				Simp(Fwd(set_image.ForallInImagePair), Fwd(ForallInLeftCosetsPair.Read(grp))),
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					points := b.Assume()
					different := b.Assume()
					b.Show(
						"a coset of H in both blocks would make the two cosets of K one, and with them their blocks",
						Simp(Fwd(set_algebra.InDisjoint)),
						Derive(func(c *Argument) {
							S, both := c.ObtainAs[Set[A]](
								"some coset S of H lies in both blocks",
								"∃S:set(A). "+
									"    S ∈ image(coset_map(G.mul, H), left_coset(x, K)) ∧ "+
									"    S ∈ image(coset_map(G.mul, H), left_coset(y, K))",
								By(c.SupposeNot()))
							same := c.Have(
								"so xK and yK are one",
								"left_coset(x, K) = left_coset(y, K)",
								By(points, both, meet.At(x, y, S)))
							c.Show(
								"and so are their blocks",
								By(Normalized, different, same))
						}))
				}))
			blockInjective := a.Have(
				"different cosets of K have different blocks",
				"injective_on(left_cosets(G.carrier, K), image(coset_map(G.mul, H)))",
				Simp(Fwd(functions.InjectiveOnAlt), Fwd(ForallInLeftCosetsPair.Read(grp))),
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					points := b.Conjuncts(
						b.Assume(),
						"x lies in the carrier",
						"so does y")
					xm := b.MemberOf[on.G](x, points[0])
					own := b.Have(
						"x lies in xK, so xH lies in the block of xK",
						"left_coset(x, H) ∈ image(coset_map(G.mul, H), left_coset(x, K))",
						Unfold(group.CosetMapDef),
						By(subK, group.InOwnLeftCosetOn.Read(grp).At(xm, K), set_image.FunInImage))
					b.Show(
						"equal blocks share xH, which makes the two cosets of K one",
						By(points[0], points[1], own, meet.At(x, y, b.TermAs[Set[A]]("left_coset(x, H)"))))
				}))
			equivalentK := a.Have(
				"lying in one coset of K is an equivalence relation on the carrier",
				"equivalence_on(G.carrier, λx:A. λy:A. y ∈ left_coset(x, K))",
				By(subK, group.CosetEquivalenceOn.Read(grp).At(K)))
			coverK := a.Have(
				"so the cosets of K, its classes, cover the carrier",
				"⋃left_cosets(G.carrier, K) = G.carrier",
				Unfold(LeftCosetsDef),
				By(equivalence.QuotientOnCovers.Read(equivalentK)))
			union := a.Have(
				"the blocks together hold every coset of H",
				"⋃blocks = left_cosets(G.carrier, H)",
				By(Normalized, blocksDef, imageH, coverK, set_image.ImageUnions.At(cosetMapH, cosetsK)))
			blockOfCoset := a.TermAs[Fun[Set[A], Set[Set[A]]]]("image(coset_map(G.mul, H))")
			finiteIff := a.Have(
				"the cosets of H are finitely many exactly when those of K and those of H in K are",
				"finite(left_cosets(G.carrier, H)) ⇔ finite(left_cosets(G.carrier, K)) ∧ finite(left_cosets(K, H))",
				Derive(func(b *Argument) {
					b.Iff()
					b.Forward(
						"finitely many cosets of H make finitely many blocks, "+
							"one to a coset of K, and include the cosets of H in K",
						func(c *Argument, finiteH Fact) {
							finiteBlocks := c.Have(
								"the blocks are finitely many",
								"finite(blocks)",
								By(Normalized, finiteH, union, finite_set.FiniteUnions.At(blocks)))
							c.Show(
								"so are the cosets of K and those of H in K",
								SplitConj(
									Case(
										"finitely many cosets of K",
										By(
											Normalized,
											finiteBlocks,
											blocksDef,
											blockInjective,
											finite_set.FiniteImageInjEq.At(blockOfCoset, cosetsK))),
									Case(
										"finitely many cosets of H in K",
										By(
											Normalized,
											finiteH,
											imageH,
											imageKH,
											kInC,
											set_image.ImageSubset.At(cosetMapH, K, carrier),
											finite_set.FiniteSubset.At(cosetsKH, cosetsH)))))
						})
					b.Backward(
						"finitely many cosets of K make finitely many blocks, each finite, whose union is the cosets of H",
						func(c *Argument, finiteParts Fact) {
							parts := c.Conjuncts(
								finiteParts,
								"finitely many cosets of K",
								"finitely many cosets of H in K")
							eachFinite := c.Have(
								"each block is finite",
								"∀X:set(set(A)). X ∈ blocks ⇒ finite(X)",
								Derive(func(d *Argument) {
									X := d.FixAs[Set[Set[A]]]("X")
									inBlocks := d.Assume()
									d.Show(
										"it has [K:H] members",
										By(
											inBlocks,
											parts[1],
											blockSize.At(X),
											cardinality.HasSizeDef.At(X, d.TermAs[Nat]("card(left_cosets(K, H))"))))
								}))
							c.Show(
								"so the cosets of H are finitely many",
								By(
									union,
									eachFinite,
									blocksDef,
									parts[0],
									finite_set.FiniteImage.At(blockOfCoset, cosetsK),
									finite_set.FiniteUnions.At(blocks)))
						})
				}))
			a.Show(
				"the two halves of the statement",
				SplitConj(
					Case(
						"the index of H is finite exactly when the other two are",
						By(finiteIff)),
					Case(
						"the index of H is then [G:K] · [K:H]",
						Derive(func(b *Argument) {
							finiteH := b.Assume()
							finites := b.Conjuncts(
								b.Have(
									"finitely many cosets of K and of H in K",
									"finite(left_cosets(G.carrier, K)) ∧ finite(left_cosets(K, H))",
									By(finiteH, finiteIff)),
								"finitely many cosets of K",
								"finitely many cosets of H in K")
							n := b.TermAs[Nat]("card(left_cosets(K, H))")
							sizedUnion := b.Have(
								"[K:H] cosets of H in each of the disjoint blocks make [K:H] · |blocks| in all",
								"has_size(⋃blocks, card(left_cosets(K, H)) * card(blocks))",
								By(
									blocksDef,
									finites[0],
									finites[1],
									blockSize,
									apart,
									finite_set.FiniteImage.At(blockOfCoset, cosetsK),
									cardinality.HasSizeUnions.At(blocks, n)))
							oneEach := b.Have(
								"there is one block for each coset of K",
								"card(blocks) = card(left_cosets(G.carrier, K))",
								By(
									Normalized,
									blocksDef,
									finites[0],
									blockInjective,
									cardinality.CardImageInj.At(blockOfCoset, cosetsK)))
							count := b.Have(
								"the union of the blocks is the cosets of H, so they number [K:H] · [G:K]",
								"card(left_cosets(G.carrier, H)) = card(left_cosets(K, H)) * card(left_cosets(G.carrier, K))",
								By(
									union,
									sizedUnion,
									oneEach,
									cardinality.HasSizeDef.At(
										b.TermAs[Set[Set[A]]]("⋃blocks"), b.TermAs[Nat]("card(left_cosets(K, H)) * card(blocks)"))))
							b.Show(
								"commute the two factors",
								Simp(Fwd(count)),
								Cite(nat_arith.MulSym))
						}))))
		}),
})}

// StrictInclusionLowersIndex — enlarging a subgroup H of finite index to
// a strictly larger subgroup K strictly lowers the index:
// [G:H] = [G:K][K:H] (IndexMultiplicative), [K:H] > 1 because H is a
// proper subgroup of K and so has a nontrivial quotient there
// (QuotientTrivialIff), and [G:K] ≠ 0, G/K holding the coset K itself.
var StrictInclusionLowersIndex = strictInclusionLowersIndexThm{family.Add(registry.ProofEntry{
	Name: "StrictInclusionLowersIndex",
	Key:  "prop_a89e236818cee2dc",
	Reading: "H ≠ K is load-bearing: at H = K the two indices " +
		"are equal. Finiteness is assumed of the index of H alone.",
	Build: family.Sections(group.GroupOn.Statement(
		Statement{
			Binders: "∀H K:set(A).",
			Hypotheses: []string{
				"subgroup(G, H)",
				"subgroup(G, K)",
				"H ⊆ K",
				"H ≠ K",
				"finite(left_cosets(G.carrier, H))",
			},
			Conclusion: "card(left_cosets(G.carrier, K)) < card(left_cosets(G.carrier, H))",
		}),
		func(ctx *Script, headline string) *GoalStackNode {
			nontrivialIndex := ctx.Lemma(group.GroupOn.Statement(
				Statement{
					Binders: "∀N:set(A).",
					Hypotheses: []string{
						"subgroup(G, N)",
						"N ≠ G.carrier",
						"finite(left_cosets(G.carrier, N))",
					},
					Conclusion: "1 < card(left_cosets(G.carrier, N))",
				}),
				func(a *Argument, grp group.GroupFact[on.G], N *Expr[Set[A]], given Fact) {
					parts := a.Conjuncts(
						given,
						"N is a subgroup",
						"N is proper",
						"the quotient is finite")
					sub, proper, finiteQuotient := parts[0], parts[1], parts[2]
					cosets := a.TermAs[Set[Set[A]]]("left_cosets(G.carrier, N)")
					singleton := a.TermAs[Set[Set[A]]]("{N}")
					identityIn := a.Have(
						"the identity coset belongs to the quotient",
						"N ∈ left_cosets(G.carrier, N)",
						By(sub, SubgroupInLeftCosets.Read(grp).At(N)))
					singletonSubset := a.Have(
						"the identity singleton lies in the quotient",
						"{N} ⊆ left_cosets(G.carrier, N)",
						By(identityIn, set_order.SingSubset.At(cosets, N)))
					notSingleton := a.Have(
						"a proper subgroup has a nontrivial quotient",
						"left_cosets(G.carrier, N) ≠ {N}",
						By(proper, sub, QuotientTrivialIff.Read(grp).At(N)))
					notLarge := a.SupposeNot()
					small := a.Have(
						"the quotient would have at most one member",
						"card(left_cosets(G.carrier, N)) ≤ 1",
						By(
							notLarge,
							nat_order.NotLessThan.At(a.TermAs[Nat]("1"), a.TermAs[Nat]("card(left_cosets(G.carrier, N))"))))
					collapsed := a.Have(
						"the quotient would equal the identity singleton",
						"{N} = left_cosets(G.carrier, N)",
						Derive(func(b *Argument) {
							singletonBound := b.Have(
								"its cardinality would be bounded by that singleton",
								"card(left_cosets(G.carrier, N)) ≤ card({N})",
								Simp(Fwd(cardinality.CardSing.Inst[Set[A]]())),
								By(small))
							b.Show(
								"a finite superset of no greater cardinality is the same set",
								By(finiteQuotient, singletonBound, singletonSubset, cardinality.CardSubsetLe.At(singleton, cosets)))
						}))
					a.Show(
						"that contradicts the nontrivial quotient",
						By(Normalized, notSingleton, collapsed))
				})

			return ctx.Theorem(headline,
				func(a *Argument, grp group.GroupFact[on.G], H, K *Expr[Set[A]], given Fact) {
					parts := a.Conjuncts(
						given,
						"H is a subgroup",
						"K is a subgroup",
						"H lies in K",
						"H is proper in K",
						"G/H is finite")
					hSub, kSub, hInK, proper, finiteTotal := parts[0], parts[1], parts[2], parts[3], parts[4]
					indices := a.Have(
						"both adjacent quotients are finite and their indices multiply",
						"finite(left_cosets(G.carrier, K)) ∧ "+
							"finite(left_cosets(K, H)) ∧ "+
							"card(left_cosets(G.carrier, H)) = card(left_cosets(G.carrier, K)) * card(left_cosets(K, H))",
						By(finiteTotal, kSub, hInK, group.SubgroupOne.Read(hSub), IndexMultiplicative.Read(grp).At(H, K)))
					indexParts := a.Conjuncts(
						indices,
						"G/K is finite",
						"K/H is finite",
						"the total index factors")
					finiteUpper, finiteLower, factorization := indexParts[0], indexParts[1], indexParts[2]
					kGroup := a.Have(
						"the restriction to K is a group",
						"group_on(restrict_group(G, K))",
						By(kSub, group.SubgroupGroupOn.Read(grp).At(K)))
					hLaws := a.Unfolded(hSub, group.SubgroupDef)
					hSubK := a.Have(
						"H is a subgroup of the restriction to K",
						"subgroup(restrict_group(G, K), H)",
						Simp(Fwd(group.SubgroupDef.Inst[A]()), Fwd(group.RestrictGroupDef.Inst[A]())),
						By(hInK, hLaws))
					lowerLarge := a.Have(
						"the proper quotient K/H has more than one coset",
						"1 < card(left_cosets(K, H))",
						By(finiteLower, proper, hSubK, Read(nontrivialIndex, kGroup).At(H)))
					identityUpper := a.Have(
						"the identity coset belongs to G/K",
						"K ∈ left_cosets(G.carrier, K)",
						By(kSub, SubgroupInLeftCosets.Read(grp).At(K)))
					upper := a.TermAs[Set[Set[A]]]("left_cosets(G.carrier, K)")
					upperCount := a.TermAs[Nat]("card(left_cosets(G.carrier, K))")
					lowerCount := a.TermAs[Nat]("card(left_cosets(K, H))")
					nonzero := a.Have(
						"the finite quotient G/K has nonzero cardinality",
						"card(left_cosets(G.carrier, K)) ≠ 0",
						By(
							finiteUpper,
							identityUpper,
							cardinality.CardEqZero.At(upper),
							set_basic.NotInEmpty.Inst[Set[A]]()))
					growth := a.Have(
						"the second factor makes the product strictly larger",
						"card(left_cosets(G.carrier, K)) * 1 < card(left_cosets(G.carrier, K)) * card(left_cosets(K, H))",
						By(nonzero, lowerLarge, nat_order.LessThanMulCancel.At(upperCount, a.TermAs[Nat]("1"), lowerCount)))
					a.Show(
						"the larger subgroup has strictly smaller index",
						Simp(Fwd(factorization)),
						By(growth, nat_arith.MulOne.At(upperCount)))
				})
		}),
})}
