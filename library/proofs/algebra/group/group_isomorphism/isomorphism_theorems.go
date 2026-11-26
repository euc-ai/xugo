// isomorphism_theorems.go — the second and third isomorphism theorems
// for groups on sets, each with the map written out: a coset is sent to
// a coset by a set operation, and nothing is chosen.

package group_isomorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// SecondIsomorphism — the second isomorphism theorem: for a subgroup h
// and a normal subgroup n of the group on c, the coset x·(h ∩ n) of h
// goes to the coset x·n of hn, a map of sets `s ↦ s·n`, and that map
// is an isomorphism of h/(h ∩ n) onto hn/n. It is a homomorphism of the
// two quotient groups (s·n)·(t·n) = (s·t)·n; one-to-one, since x·n = y·n
// with x, y in h puts inv(x) * y in h ∩ n; and onto, since a coset
// (x * y)·n of hn with x in h, y in n is x·n, the image of x·(h ∩ n).
var SecondIsomorphism = secondIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SecondIsomorphism",
	Key:  "prop_bb9060c494de4200",

	Deps: []registry.EntryLike{
		group_homomorphism.GroupIsomorphismDef,
		group_homomorphism.GroupHomomorphism,
		SetMulNormal,
		NormalInter,
		NormalInSetMul,
		SubsetSetMulLeft,
		group.SubgroupGroupOn,
		quotient_group.QuotientGroupOn,
		quotient_group.LeftCosetMulOn,
		quotient_group.InLeftCosets,
		quotient_group.InSetMul,
		group.LeftCosetEqOn,
		group.InLeftCosetOn,
		group.SubgroupMul,
		group.SubgroupInv,
		set_basic.InInter,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀h n:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"normal_subgroup(G, n)",
		},
		Conclusion: "group_isomorphism(quotient_group(restrict_group(G, h), h ∩ n), " +
			"    quotient_group(restrict_group(G, set_mul(h, n)), n), " +
			"    λs:set(A). set_mul(s, n))",
	}),
		"both quotients are groups on sets (QuotientGroupOn at h with NormalInter, at hn with "+
			"NormalInSetMul); the map carries x·(h ∩ n) to x·(h ∩ n)·n = x·n, a coset of hn by n since h ⊆ "+
			"hn; multiplicative by LeftCosetMulOn at hn; one-to-one by LeftCosetEqOn at both carriers, "+
			"G.inv(x) * y ∈ n with x, y ∈ h giving G.inv(x) * y ∈ h ∩ n; onto since (x * y)·n = x·n for y ∈ n"),
})}

// ThirdIsomorphismNormal — the cosets of n in m form a normal subgroup
// of G/n when n ⊆ m are normal subgroups of G: products, inverses and
// conjugates of cosets are represented by the corresponding elements.
var ThirdIsomorphismNormal = thirdIsomorphismNormalThm{family.Add(registry.ProofEntry{
	Name: "ThirdIsomorphismNormal",
	Key:  "prop_a5c2b74bd10a5495",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_on(A). ∀m n:set(A).",
		Hypotheses: []string{
			"normal_subgroup(G, m)",
			"normal_subgroup(G, n)",
			"n ⊆ m",
		},
		Conclusion: "normal_subgroup(quotient_group(G, n), left_cosets(m, n))",
	},
		func(a *Argument, G group.GroupFact[on.G], m, n *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"m is normal in G",
				"n is normal in G",
				"n lies in m")
			mNormal, nNormal, nInM := parts[0], parts[1], parts[2]
			mSub := a.Have(
				"m is a subgroup",
				"subgroup(G, m)",
				By(group.NormalSubgroupSubgroup.Read(mNormal)))
			nSub := a.Have(
				"n is a subgroup",
				"subgroup(G, n)",
				By(group.NormalSubgroupSubgroup.Read(nNormal)))
			mInCarrier := a.Have(
				"m lies in the carrier",
				"m ⊆ G.carrier",
				By(group.SubgroupSubset.Read(mSub)))
			nInCarrier := a.Have(
				"n lies in the carrier",
				"n ⊆ G.carrier",
				By(group.SubgroupSubset.Read(nSub)))
			mGroup := a.Have(
				"the restriction to m is a group",
				"group_on(restrict_group(G, m))",
				By(mSub, group.SubgroupGroupOn.Read(G).At(m)))
			a.Show(
				"the cosets in m/n satisfy the subgroup and conjugation conditions in G/n",
				Simp(Fwd(group.NormalSubgroupDef), Fwd(group.SubgroupDef)),
				SplitConjAll(
					Case(
						"the coset of a point of m is the coset of a point of G.carrier",
						Simp(Fwd(set_basic.SubsetDef), Fwd(quotient_group.ForallInLeftCosets.Read(mGroup))),
						Derive(func(b *Argument) {
							u := b.FixAs[A]("u")
							uC := b.MemberOf[on.G](u, b.Have(
								"u lies in G.carrier",
								"u ∈ G.carrier",
								BySets(mInCarrier, b.Assume())))
							b.Show(
								"so its coset is a coset in G/n",
								By(nInCarrier, quotient_group.LeftCosetInLeftCosets.Read(G).At(n, uC)))
						})),
					Case(
						"the identity coset n is a coset in m/n, n being a subgroup of the group on m",
						Derive(func(b *Argument) {
							nInGroupM := b.Have(
								"n, a subgroup lying in m, is a subgroup of the group on m",
								"subgroup(restrict_group(G, m), n)",
								By(nSub, nInM, SubgroupRestrict.At(b.TermAs[group.GroupOps[A]]("G"), m, n)))
							b.Show(
								"so n is one of its own cosets in m",
								By(nInGroupM, quotient_group.SubgroupInLeftCosets.Read(mGroup).At(n)))
						})),
					Case(
						"the product of the cosets of two points of m is the coset of their product",
						Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(mGroup))),
						Derive(func(b *Argument) {
							u, v := b.FixAs[A]("u"), b.FixAs[A]("v")
							points := b.Conjuncts(
								b.Assume(),
								"u lies in m",
								"v lies in m")
							uM, vM := proof.MemberOf(u, points[0]), proof.MemberOf(v, points[1])
							uC := b.MemberOf[on.G](u, b.Have(
								"u lies in G.carrier",
								"u ∈ G.carrier",
								BySets(mInCarrier, uM)))
							vC := b.MemberOf[on.G](v, b.Have(
								"v lies in G.carrier",
								"v ∈ G.carrier",
								BySets(mInCarrier, vM)))
							productInM := b.Have(
								"m holds the product of its two points",
								"u * v ∈ m",
								By(group.SubgroupMul.Read(mSub).At(uM, vM)))
							productCoset := b.Have(
								"coset multiplication multiplies the points",
								"set_mul(left_coset(u, n), left_coset(v, n)) = left_coset(u * v, n)",
								By(nNormal, quotient_group.LeftCosetMulOn.Read(G).At(n, uC, vC)))
							b.Show(
								"the coset of u * v is a coset in m/n",
								productCoset.Rw(),
								By(
									nInM,
									quotient_group.LeftCosetInLeftCosets.Read(mGroup).At(
										n, proof.MemberOf(b.TermAs[A]("u * v"), productInM))))
						})),
					Case(
						"the inverses of the coset of a point of m are the coset of its inverse",
						Simp(Fwd(quotient_group.ForallInLeftCosets.Read(mGroup))),
						Derive(func(b *Argument) {
							u := b.FixAs[A]("u")
							uM := proof.MemberOf(u, b.Assume())
							uC := b.MemberOf[on.G](u, b.Have(
								"u lies in G.carrier",
								"u ∈ G.carrier",
								BySets(mInCarrier, uM)))
							inverseInM := b.Have(
								"m holds the inverse of its point",
								"G.inv(u) ∈ m",
								By(group.SubgroupInv.Read(mSub).At(uM)))
							inverseCoset := b.Have(
								"coset inversion inverts the point",
								"set_inv(left_coset(u, n)) = left_coset(G.inv(u), n)",
								By(nNormal, quotient_group.LeftCosetInvOn.Read(G).At(n, uC)))
							b.Show(
								"the coset of G.inv(u) is a coset in m/n",
								inverseCoset.Rw(),
								By(
									nInM,
									quotient_group.LeftCosetInLeftCosets.Read(mGroup).At(
										n, proof.MemberOf(b.TermAs[A]("G.inv(u)"), inverseInM))))
						})),
					Case(
						"conjugation is represented by conjugation in G, which preserves m",
						Derive(func(b *Argument) {
							conjugates := b.Have(
								"a coset of G/n conjugates a coset of m/n into m/n",
								"∀g:set(A). "+
									"    g ∈ left_cosets(G.carrier, n) ⇒ "+
									"    ∀x:set(A). x ∈ left_cosets(m, n) ⇒ set_mul(set_mul(g, x), set_inv(g)) ∈ left_cosets(m, n)",
								Simp(Fwd(quotient_group.ForallInLeftCosets.Read(G))),
								Derive(func(c *Argument) {
									u := c.FixAs[A]("u")
									uIn := c.Assume()
									c.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(mGroup))))
									v := c.FixAs[A]("v")
									vM := proof.MemberOf(v, c.Assume())
									uC := c.MemberOf[on.G](u, uIn)
									vC := c.MemberOf[on.G](v, c.Have(
										"v lies in G.carrier",
										"v ∈ G.carrier",
										BySets(mInCarrier, vM)))
									conjugateInM := c.Have(
										"normality of m keeps the conjugate in m",
										"u * v * G.inv(u) ∈ m",
										By(uC, vM, group.NormalSubgroupConjugate.Read(mNormal).AsFact().At(u, v)))
									uv := group.MulIn.Read(G).At(uC, vC)
									inverse := group.InvIn.Read(G).At(uC)
									productCoset := c.Have(
										"the first product is the coset of u * v",
										"set_mul(left_coset(u, n), left_coset(v, n)) = left_coset(u * v, n)",
										By(nNormal, quotient_group.LeftCosetMulOn.Read(G).At(n, uC, vC)))
									inverseCoset := c.Have(
										"the inverse coset is the coset of G.inv(u)",
										"set_inv(left_coset(u, n)) = left_coset(G.inv(u), n)",
										By(nNormal, quotient_group.LeftCosetInvOn.Read(G).At(n, uC)))
									conjugateCoset := c.Have(
										"so the quotient conjugate is the coset of the conjugate",
										"set_mul(left_coset(u * v, n), left_coset(G.inv(u), n)) = left_coset(u * v * G.inv(u), n)",
										By(nNormal, quotient_group.LeftCosetMulOn.Read(G).At(n, uv, inverse)))
									c.Show(
										"the coset of the conjugate is a coset in m/n",
										productCoset.Rw(),
										inverseCoset.Rw(),
										conjugateCoset.Rw(),
										By(
											nInM,
											quotient_group.LeftCosetInLeftCosets.Read(mGroup).At(
												n, proof.MemberOf(c.TermAs[A]("u * v * G.inv(u)"), conjugateInM))))
								}))
							b.Show(
								"which is the condition, its two memberships taken together",
								By(conjugates))
						})),
				))
		}),
})}

// ThirdIsomorphism — union identifies (G/n)/(m/n) with G/m. For a point u
// of G, the union of the coset of u·n by m/n is u·m; so union preserves
// the product, tells distinct source cosets apart, and reaches every coset
// of G/m. The map is written out rather than induced through
// FirstIsomorphism, whose induced_map chooses a representative of each
// coset, where ⋃ chooses nothing.
var ThirdIsomorphism = thirdIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ThirdIsomorphism",
	Key:  "prop_1f9dec33bdff50a4",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_on(A). ∀m n:set(A).",
		Hypotheses: []string{
			"normal_subgroup(G, m)",
			"normal_subgroup(G, n)",
			"n ⊆ m",
		},
		Conclusion: "group_isomorphism(quotient_group(quotient_group(G, n), left_cosets(m, n)), " +
			"    quotient_group(G, m), " +
			"    λS:set(set(A)). ⋃S)",
		Abbrev: Abbrev{
			{Name: "(G/n)/(m/n)", Text: "left_cosets(set_mul, left_cosets(G.carrier, n), left_cosets(m, n))"},
		},
	},
		func(a *Argument, G group.GroupFact[on.G], m, n *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"m is normal",
				"n is normal",
				"n lies in m")
			mNormal, nNormal, nInM := parts[0], parts[1], parts[2]
			mSub := a.Have(
				"m is a subgroup",
				"subgroup(G, m)",
				By(group.NormalSubgroupSubgroup.Read(mNormal)))
			nSub := a.Have(
				"n is a subgroup",
				"subgroup(G, n)",
				By(group.NormalSubgroupSubgroup.Read(nNormal)))
			mInCarrier := a.Have(
				"m lies in the carrier",
				"m ⊆ G.carrier",
				By(group.SubgroupSubset.Read(mSub)))
			nInCarrier := a.Have(
				"n lies in the carrier",
				"n ⊆ G.carrier",
				By(group.SubgroupSubset.Read(nSub)))
			mGroup := a.Have(
				"the restriction to m is a group",
				"group_on(restrict_group(G, m))",
				By(mSub, group.SubgroupGroupOn.Read(G).At(m)))
			mul := a.TermAs[Op[A]]("G.mul")
			setMul := a.TermAs[Op[Set[A]]]("set_mul")
			mOverN := a.TermAs[Set[Set[A]]]("left_cosets(m, n)")
			unionOf := a.Have(
				"the union of the source coset of a point u is u·m",
				Statement{
					Binders: "∀u:A.",
					Hypotheses: []string{
						"u ∈ G.carrier",
					},
					Conclusion: "⋃left_coset(set_mul, left_coset(u, n), left_cosets(m, n)) = left_coset(u, m)",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					uC := b.MemberOf[on.G](u, b.Assume())
					un := b.TermAs[Set[A]]("left_coset(u, n)")
					outer := b.TermAs[Set[Set[A]]]("left_coset(set_mul, left_coset(u, n), left_cosets(m, n))")
					b.Do(Simp(Fwd(set_basic.Extension)))
					z := b.FixAs[A]("z")
					b.Iff()
					b.Forward(
						"absorb the n-factor into m",
						func(c *Argument, inUnion Fact) {
							_, containsZ := c.ObtainAs[Set[A]](
								"choose the coset containing z",
								"∃t:set(A). t ∈ left_coset(set_mul, left_coset(u, n), left_cosets(m, n)) ∧ z ∈ t",
								By(inUnion, set_basic.InUnions.At(outer, z)))
							s, factored := c.ObtainAs[Set[A]](
								"write that coset as u·n times a coset in m/n",
								"∃s:set(A). t = set_mul(left_coset(u, n), s) ∧ s ∈ left_cosets(m, n)",
								BySets(containsZ, group.LeftCosetDef.At(setMul, un, mOverN)))
							y, rep := c.ObtainAs[A](
								"choose the representative of s in m",
								"∃y:A. s = left_coset(y, n) ∧ y ∈ m",
								By(factored, nInM, quotient_group.InLeftCosets.Read(mGroup).At(n, s)))
							yParts := c.Conjuncts(
								rep,
								"y represents s",
								"y lies in m")
							yM := proof.MemberOf(y, yParts[1])
							yC := c.MemberOf[on.G](y, c.Have(
								"y lies in the carrier",
								"y ∈ G.carrier",
								BySets(mInCarrier, yM)))
							cosetProduct := c.Have(
								"the coset containing z is the coset of u * y",
								"t = left_coset(u * y, n)",
								By(factored, rep, nNormal, quotient_group.LeftCosetMulOn.Read(G).At(n, uC, yC)))
							v, zRep := c.ObtainAs[A](
								"write z using the remaining n-factor",
								"∃v:A. z = u * y * v ∧ v ∈ n",
								BySets(containsZ, cosetProduct, group.LeftCosetDef.At(mul, c.TermAs[A]("u * y"), n)))
							vM := proof.MemberOf(v, c.Have(
								"the n-factor lies in m",
								"v ∈ m",
								BySets(nInM, zRep)))
							vC := c.MemberOf[on.G](v, c.Have(
								"the n-factor lies in the carrier",
								"v ∈ G.carrier",
								BySets(nInCarrier, zRep)))
							factorInM := c.Have(
								"m absorbs the remaining product",
								"y * v ∈ m",
								By(group.SubgroupMul.Read(mSub).At(yM, vM)))
							reassociate := c.Have(
								"z is u times a point of m",
								"z = u * (y * v)",
								By(Normalized, zRep, group.AssocOn.Read(G).At(uC, yC, vC)))
							c.Show(
								"so z lies in u·m",
								BySets(factorInM, reassociate, group.LeftCosetDef.At(mul, u, m)))
						})
					b.Backward(
						"use the n-coset of z inside the outer coset",
						func(c *Argument, inCoset Fact) {
							y, zRep := c.ObtainAs[A](
								"write z as u times a point of m",
								"∃y:A. z = u * y ∧ y ∈ m",
								BySets(inCoset, group.LeftCosetDef.At(mul, u, m)))
							yC := c.MemberOf[on.G](y, c.Have(
								"y lies in the carrier",
								"y ∈ G.carrier",
								BySets(mInCarrier, zRep)))
							uy := group.MulIn.Read(G).At(uC, yC)
							yn := c.TermAs[Set[A]]("left_coset(y, n)")
							ynIn := c.Have(
								"y·n is a coset represented in m",
								"left_coset(y, n) ∈ left_cosets(m, n)",
								By(zRep, nInM, quotient_group.LeftCosetInLeftCosets.Read(mGroup).AsFact().At(n, y)))
							cosetProduct := c.Have(
								"u·n times y·n is the coset of u * y",
								"set_mul(left_coset(u, n), left_coset(y, n)) = left_coset(u * y, n)",
								By(nNormal, quotient_group.LeftCosetMulOn.Read(G).At(n, uC, yC)))
							inOuter := c.Have(
								"the coset of u * y belongs to the outer coset",
								"left_coset(u * y, n) ∈ left_coset(set_mul, left_coset(u, n), left_cosets(m, n))",
								Simp(
									Fwd(group.LeftCosetDef.Inst[Set[A]]()),
									Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[A]](), TypeBinder.BindB[Set[A]]()))),
								Derive(func(d *Argument) {
									d.Take(yn)
									d.Show(
										"y·n witnesses that membership",
										By(ynIn, cosetProduct))
								}))
							zIn := c.Have(
								"z lies in its own n-coset",
								"z ∈ left_coset(u * y, n)",
								By(zRep, nSub, group.InOwnLeftCosetOn.Read(G).At(uy, n)))
							c.Show(
								"hence z lies in the union",
								By(inOuter, zIn, set_basic.InUnions.At(outer, z)))
						})
				}))
			qGroup := a.Have(
				"G/n is a group",
				"group_on(quotient_group(G, n))",
				By(nNormal, quotient_group.QuotientGroupOn.Read(G).At(n)))
			mOverNNormal := a.Have(
				"m/n is normal in G/n",
				"normal_subgroup(quotient_group(G, n), left_cosets(m, n))",
				By(mNormal, nNormal, nInM, ThirdIsomorphismNormal.Read(G).At(m, n)))
			mOverNSub := a.Have(
				"m/n is a subgroup of G/n",
				"subgroup(quotient_group(G, n), left_cosets(m, n))",
				By(group.NormalSubgroupSubgroup.Read(mOverNNormal)))
			mOverNInCarrier := a.Have(
				"m/n lies in the carrier of G/n",
				"left_cosets(m, n) ⊆ left_cosets(G.carrier, n)",
				By(group.SubgroupSubset.Read(mOverNSub)))
			sourceGroup := a.Have(
				"the double quotient is a group",
				"group_on(quotient_group(quotient_group(G, n), left_cosets(m, n)))",
				By(mOverNNormal, quotient_group.QuotientGroupOn.Read(qGroup).At(mOverN)))
			targetGroup := a.Have(
				"G/m is a group",
				"group_on(quotient_group(G, m))",
				By(mNormal, quotient_group.QuotientGroupOn.Read(G).At(m)))
			nClasses := a.Have(
				"a carrier point represents an n-coset",
				"∀x:A. x ∈ G.carrier ⇒ left_coset(x, n) ∈ left_cosets(G.carrier, n)",
				By(nInCarrier, quotient_group.LeftCosetInLeftCosets.Read(G).AsFact().At(n)))
			classes := a.Have(
				"a carrier point represents a source coset",
				"∀x:A. x ∈ G.carrier ⇒ left_coset(set_mul, left_coset(x, n), left_cosets(m, n)) ∈ «(G/n)/(m/n)»",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					uIn := b.Assume()
					b.Show(
						"its n-coset, a point of G/n, represents a coset of m/n",
						By(
							nClasses.At(u),
							uIn,
							mOverNInCarrier,
							quotient_group.LeftCosetInLeftCosets.Read(qGroup).AsFact().At(
								mOverN, b.TermAs[Set[A]]("left_coset(u, n)"))))
				}))
			mapsInto := a.Have(
				"union sends source cosets to cosets in G/m",
				"∀S:set(set(A)). S ∈ «(G/n)/(m/n)» ⇒ ⋃S ∈ left_cosets(G.carrier, m)",
				Simp(
					Fwd(quotient_group.ForallInLeftCosets.Read(qGroup)),
					Fwd(quotient_group.ForallInLeftCosets.Read(G))),
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					uC := b.MemberOf[on.G](u, b.Assume())
					image := b.Have(
						"the union of the source coset of u is u·m",
						"⋃left_coset(set_mul, left_coset(u, n), left_cosets(m, n)) = left_coset(u, m)",
						By(uC, unionOf.At(u)))
					b.Show(
						"which is a coset of G/m",
						image.Rw(),
						By(mInCarrier, quotient_group.LeftCosetInLeftCosets.Read(G).At(m, uC)))
				}))
			a.Show(
				"union is a bijective homomorphism between the two quotient groups",
				Simp(
					Fwd(group_homomorphism.GroupIsomorphismDef.Inst(
						TypeBinder.BindA[Set[Set[A]]](), TypeBinder.BindB[Set[A]]())),
					Fwd(group_homomorphism.GroupHomomorphism.Inst(
						TypeBinder.BindA[Set[Set[A]]](), TypeBinder.BindB[Set[A]]()))),
				SplitConjAll(
					Case(
						"the source is the double quotient group",
						By(sourceGroup)),
					Case(
						"the target is G/m",
						By(targetGroup)),
					Case(
						"union takes source points into the target carrier",
						By(mapsInto)),
					Case(
						"union preserves multiplication of source cosets",
						Simp(
							Fwd(quotient_group.ForallInLeftCosetsPair.Read(qGroup)),
							Fwd(quotient_group.ForallInLeftCosetsPair.Read(G))),
						Derive(func(b *Argument) {
							u, v := b.FixAs[A]("u"), b.FixAs[A]("v")
							points := b.Conjuncts(
								b.Assume(),
								"u lies in the carrier",
								"v lies in the carrier")
							uC, vC := b.MemberOf[on.G](u, points[0]), b.MemberOf[on.G](v, points[1])
							un, vn := b.TermAs[Set[A]]("left_coset(u, n)"), b.TermAs[Set[A]]("left_coset(v, n)")
							unIn := b.Have(
								"u·n is a point of G/n",
								"left_coset(u, n) ∈ left_cosets(G.carrier, n)",
								By(nClasses.At(u), uC))
							vnIn := b.Have(
								"v·n is a point of G/n",
								"left_coset(v, n) ∈ left_cosets(G.carrier, n)",
								By(nClasses.At(v), vC))
							unQ, vnQ := proof.MemberOf(un, unIn), proof.MemberOf(vn, vnIn)
							uv := group.MulIn.Read(G).At(uC, vC)
							innerProduct := b.Have(
								"multiplication in G/n multiplies the representatives",
								"set_mul(left_coset(u, n), left_coset(v, n)) = left_coset(u * v, n)",
								By(uC, vC, nNormal, quotient_group.LeftCosetMulOn.Read(G).At(n, uC, vC)))
							sourceProduct := b.Have(
								"the source product is represented by u * v",
								"set_mul(set_mul, "+
									"    left_coset(set_mul, left_coset(u, n), left_cosets(m, n)), "+
									"    left_coset(set_mul, left_coset(v, n), left_cosets(m, n))) = "+
									"left_coset(set_mul, left_coset(u * v, n), left_cosets(m, n))",
								By(
									innerProduct,
									unQ,
									vnQ,
									mOverNNormal,
									quotient_group.LeftCosetMulOn.Read(qGroup).At(mOverN, unQ, vnQ)))
							unionU := b.Have(
								"the union of the source coset of u is u·m",
								"⋃left_coset(set_mul, left_coset(u, n), left_cosets(m, n)) = left_coset(u, m)",
								By(uC, unionOf.At(u)))
							unionV := b.Have(
								"the union of the source coset of v is v·m",
								"⋃left_coset(set_mul, left_coset(v, n), left_cosets(m, n)) = left_coset(v, m)",
								By(vC, unionOf.At(v)))
							unionProduct := b.Have(
								"the union of the represented product is (u * v)·m",
								"⋃left_coset(set_mul, left_coset(u * v, n), left_cosets(m, n)) = left_coset(u * v, m)",
								By(uv, unionOf.At(uv)))
							targetProduct := b.Have(
								"multiplication in G/m multiplies the same representatives",
								"set_mul(left_coset(u, m), left_coset(v, m)) = left_coset(u * v, m)",
								By(uC, vC, mNormal, quotient_group.LeftCosetMulOn.Read(G).At(m, uC, vC)))
							b.Show(
								"both sides are the m-coset of u * v",
								Simp(Fwd(sourceProduct), Fwd(unionU), Fwd(unionV), Fwd(unionProduct), Fwd(targetProduct)),
								Refl())
						})),
					Case(
						"equal unions determine equal source cosets",
						Simp(
							Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[Set[Set[A]]](), TypeBinder.BindB[Set[A]]()))),
						Derive(func(b *Argument) {
							separated := b.Have(
								"two source cosets with equal unions are equal",
								"∀x y:set(set(A)). x ∈ «(G/n)/(m/n)» ∧ y ∈ «(G/n)/(m/n)» ⇒ ⋃x = ⋃y ⇒ x = y",
								Simp(
									Fwd(quotient_group.ForallInLeftCosetsPair.Read(qGroup)),
									Fwd(quotient_group.ForallInLeftCosetsPair.Read(G))),
								Derive(func(c *Argument) {
									u, v := c.FixAs[A]("u"), c.FixAs[A]("v")
									points := c.Conjuncts(
										c.Assume(),
										"u lies in the carrier",
										"v lies in the carrier")
									uC, vC := c.MemberOf[on.G](u, points[0]), c.MemberOf[on.G](v, points[1])
									equalUnions := c.Assume()
									unionU := c.Have(
										"the union of the source coset of u is u·m",
										"⋃left_coset(set_mul, left_coset(u, n), left_cosets(m, n)) = left_coset(u, m)",
										By(uC, unionOf.At(u)))
									unionV := c.Have(
										"the union of the source coset of v is v·m",
										"⋃left_coset(set_mul, left_coset(v, n), left_cosets(m, n)) = left_coset(v, m)",
										By(vC, unionOf.At(v)))
									equalCosets := c.Simplified(equalUnions, Fwd(unionU), Fwd(unionV))
									differenceInM := c.Have(
										"the two representatives differ by a point of m",
										"G.inv(u) * v ∈ m",
										By(uC, vC, mSub, equalCosets, group.LeftCosetEqOn.Read(G).At(uC, vC, m)))
									differenceInMOverN := c.Have(
										"the n-coset of that difference belongs to m/n",
										"left_coset(G.inv(u) * v, n) ∈ left_cosets(m, n)",
										By(
											differenceInM,
											nInM,
											quotient_group.LeftCosetInLeftCosets.Read(mGroup).AsFact().At(n, c.TermAs[A]("G.inv(u) * v"))))
									un, vn := c.TermAs[Set[A]]("left_coset(u, n)"), c.TermAs[Set[A]]("left_coset(v, n)")
									unIn := c.Have(
										"u·n is a point of G/n",
										"left_coset(u, n) ∈ left_cosets(G.carrier, n)",
										By(nClasses.At(u), uC))
									vnIn := c.Have(
										"v·n is a point of G/n",
										"left_coset(v, n) ∈ left_cosets(G.carrier, n)",
										By(nClasses.At(v), vC))
									unQ, vnQ := proof.MemberOf(un, unIn), proof.MemberOf(vn, vnIn)
									inverse := group.InvIn.Read(G).At(uC)
									inverseCoset := c.Have(
										"the inverse of u·n is G.inv(u)·n",
										"set_inv(left_coset(u, n)) = left_coset(G.inv(u), n)",
										By(uC, nNormal, quotient_group.LeftCosetInvOn.Read(G).At(n, uC)))
									differenceCoset := c.Have(
										"the quotient difference is the coset of the difference",
										"set_mul(set_inv(left_coset(u, n)), left_coset(v, n)) = left_coset(G.inv(u) * v, n)",
										By(inverseCoset, inverse, vC, nNormal, quotient_group.LeftCosetMulOn.Read(G).At(n, inverse, vC)))
									c.Show(
										"the source cosets are equal because their quotient difference lies in m/n",
										By(
											differenceCoset,
											differenceInMOverN,
											unQ,
											vnQ,
											mOverNSub,
											group.LeftCosetEqOn.Read(qGroup).At(unQ, vnQ, mOverN)))
								}))
							b.Show(
								"which is one-to-one, its three hypotheses taken together",
								By(separated))
						})),
					Case(
						"every target coset is the union of a source coset",
						Simp(Fwd(set_basic.Extension.Inst[Set[A]]())),
						Derive(func(b *Argument) {
							x := b.FixAs[Set[A]]("x")
							unionMap := b.TermAs[Fun[Set[Set[A]], Set[A]]]("λS:set(set(A)). ⋃S")
							sourceCarrier := b.TermAs[Set[Set[Set[A]]]]("«(G/n)/(m/n)»")
							b.Iff()
							b.Forward(
								"the union of a source coset lies in G/m",
								func(c *Argument, inImage Fact) {
									S, imagePoint := c.ObtainAs[Set[Set[A]]](
										"choose the source coset in the image",
										"∃S:set(set(A)). x = ⋃S ∧ S ∈ «(G/n)/(m/n)»",
										By(inImage, set_basic.InImage.At(unionMap, sourceCarrier, x)))
									c.Show(
										"its union lies in the target carrier",
										By(mapsInto.At(S), imagePoint))
								})
							b.Backward(
								"lift a representative from G/m to the source",
								func(c *Argument, inTarget Fact) {
									u, rep := c.ObtainAs[A](
										"choose a representative of the target coset",
										"∃u:A. x = left_coset(u, m) ∧ u ∈ G.carrier",
										By(inTarget, mInCarrier, quotient_group.InLeftCosets.Read(G).At(m, x)))
									image := c.Have(
										"the represented source coset has the required union",
										"⋃left_coset(set_mul, left_coset(u, n), left_cosets(m, n)) = left_coset(u, m)",
										By(rep, unionOf.At(u)))
									c.Do(Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[Set[A]]](), TypeBinder.BindB[Set[A]]()))))
									c.Take(c.TermAs[Set[Set[A]]]("left_coset(set_mul, left_coset(u, n), left_cosets(m, n))"))
									c.Show(
										"that source coset witnesses image membership",
										By(rep, classes.At(u), image))
								})
						})),
				))
		}),
})}
