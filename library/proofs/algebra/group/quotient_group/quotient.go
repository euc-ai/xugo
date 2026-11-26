// quotient.go — the quotient group: the left cosets of a normal subgroup
// of a group on a set, under the product and the inverse of sets. The
// product of two cosets is the coset of the product and the inverses of
// a coset are the coset of the inverse, so the coset map carries the
// group's operations to the cosets, and the cosets are a group as the
// image of the group along it (group_homomorphism.ImageGroupOn). The
// two coset laws are read one point of the carrier at a time through
// the membership readings —
// both sides of a coset equation lie in the carrier, so extensionality
// is read inside it (set_basic.ExtensionWithin) — and the normality of N
// enters through the group chapter's conjugation law and
// NormalSubgroupSwapOn, which lets a product in N be reversed. The kernel
// of the coset map is the subgroup itself. Every group law is stated on
// its record carrier.
//
// The group hypothesis is named `grp` throughout: this package imports
// the group chapter as `group`, and the group chapter's usual name for its
// hypothesis would shadow it.

package quotient_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// LeftCosetMulOn — the product of two left cosets of a normal subgroup by
// points of the carrier is the left coset of the product. Both sides lie
// in the carrier, so one point z of the carrier at a time. A point of
// the product is a * b with a in x·N and b in y·N, which read through the
// inverse say that inv(x) * a and inv(y) * b lie in N; and inv(x * y)
// times a * b is the conjugate of inv(x) * a by inv(y), times inv(y) * b
// — a product of two members of N, which is normal and closed under
// products. Conversely a point z of (x * y)·N is x times inv(x) * z,
// where x lies in its own coset and inv(x) * z lies in y·N because
// inv(y) * (inv(x) * z) is inv(x * y) * z.
var LeftCosetMulOn = leftCosetMulOnThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetMulOn",
	Key:  "prop_fb62fc1e98a048bf",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀N:set(A). ∀x y:A.",
		Hypotheses: []string{
			"normal_subgroup(G, N)",
			"x ∈ G.carrier ∧ y ∈ G.carrier",
		},
		Conclusion: "set_mul(left_coset(x, N), left_coset(y, N)) = left_coset(x * y, N)",
	},
		func(a *Argument, grp group.GroupFact[on.G], N *Expr[Set[A]], x, y *Expr[A], normal, members Fact) {
			points := a.Conjuncts(
				members,
				"x lies in G.carrier",
				"so does y")
			xIn, yIn := points[0], points[1]
			subgroup := a.Have(
				"a normal subgroup is a subgroup",
				"subgroup(G, N)",
				By(group.NormalSubgroupSubgroup, normal))
			nInC := a.Have(
				"which lies in G.carrier",
				"N ⊆ G.carrier",
				By(group.SubgroupSubset, subgroup))
			xCosetInC := a.Have(
				"x·N lies in G.carrier",
				"left_coset(x, N) ⊆ G.carrier",
				By(group.LeftCosetIn, grp, xIn, nInC))
			yCosetInC := a.Have(
				"so does y·N",
				"left_coset(y, N) ⊆ G.carrier",
				By(group.LeftCosetIn, grp, yIn, nInC))
			productInC := a.Have(
				"and their product",
				"set_mul(left_coset(x, N), left_coset(y, N)) ⊆ G.carrier",
				By(SetMulIn, grp, xCosetInC, yCosetInC))
			xyCosetInC := a.Have(
				"and (x * y)·N",
				"left_coset(x * y, N) ⊆ G.carrier",
				By(group.LeftCosetIn, grp, members, nInC, group.MulIn))
			inX, inY := a.Unfolded(xCosetInC, set_basic.SubsetDef), a.Unfolded(yCosetInC, set_basic.SubsetDef)
			pointwise := a.Have(
				"one point z of the carrier at a time: a point of the product is a "+
					"product of members, a point of the coset reads through the inverse",
				Statement{
					Binders: "∀z:A.",
					Hypotheses: []string{
						"z ∈ G.carrier",
					},
					Conclusion: "z ∈ set_mul(left_coset(x, N), left_coset(y, N)) ⇔ z ∈ left_coset(x * y, N)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("z")
					zInC := b.Assume()
					b.Do(Simp(Fwd(InSetMul), Fwd(group.InLeftCosetOn), Fwd(group.MulIn)))
					b.Iff()
					b.Forward(
						"z is a * b with a in x·N and b in y·N, and G.inv(x * y) * "+
							"(a * b) is a conjugate of G.inv(x) * a times G.inv(y) * b",
						func(c *Argument, member Fact) {
							_, _, product := c.Unpack2As[A, A](member, "a", "b")
							parts := c.Conjuncts(
								product,
								"a lies in x·N",
								"b lies in y·N",
								"z is a * b")
							aInC := c.Have(
								"a lies in G.carrier",
								"a ∈ G.carrier",
								By(inX, parts[0]))
							bInC := c.Have(
								"so does b",
								"b ∈ G.carrier",
								By(inY, parts[1]))
							aIn := c.Have(
								"read through the inverse, G.inv(x) * a lies in N",
								"G.inv(x) * a ∈ N",
								By(group.InLeftCosetOn, grp, members, aInC, nInC, parts[0]))
							bIn := c.Have(
								"and G.inv(y) * b lies in N",
								"G.inv(y) * b ∈ N",
								By(group.InLeftCosetOn, grp, members, bInC, nInC, parts[1]))
							inverseYIn := c.Have(
								"G.inv(y) lies in G.carrier",
								"G.inv(y) ∈ G.carrier",
								By(group.InvIn, grp, yIn))
							conjugate := c.Have(
								"N is normal, so it holds the conjugate of G.inv(x) * a by G.inv(y)",
								"(G.inv(y) * (G.inv(x) * a)) * G.inv(G.inv(y)) ∈ N",
								By(group.NormalSubgroupConjugate, normal, inverseYIn, aIn))
							regroup := c.Have(
								"G.inv(x * y) * (a * b) is that conjugate times G.inv(y) * b: unfold the inverses and regroup",
								"G.inv(x * y) * (a * b) = ((G.inv(y) * (G.inv(x) * a)) * G.inv(G.inv(y))) * (G.inv(y) * b)",
								Simp(
									Fwd(group.InvMulOn),
									Fwd(group.InvInvOn),
									Fwd(group.AssocOn),
									Fwd(group.MulInvCancelRightOn),
									Fwd(group.MulIn),
									Fwd(group.InvIn)),
								Basic())
							c.Show(
								"so G.inv(x * y) * z is the product of two members of N",
								parts[2].Rw(),
								regroup.Rw(),
								By(group.SubgroupMul, subgroup, conjugate, bIn))
						})
					b.Backward(
						"z is x times G.inv(x) * z, with x in its own coset and G.inv(x) * z in y·N",
						func(c *Argument, inN Fact) {
							c.Take(x)
							c.Take(c.TermAs[A]("G.inv(x) * z"))
							xInOwn := c.Have(
								"x lies in its own coset",
								"x ∈ left_coset(x, N)",
								By(group.InOwnLeftCosetOn, grp, xIn, subgroup))
							bridge := c.Have(
								"G.inv(y) * (G.inv(x) * z) is G.inv(x * y) * z: the inverse of a product, regrouped",
								"G.inv(y) * (G.inv(x) * z) = G.inv(x * y) * z",
								Simp(Fwd(group.InvMulOn), Fwd(group.AssocOn), Fwd(group.MulIn), Fwd(group.InvIn)),
								Basic())
							zIn := c.Have(
								"so G.inv(x) * z lies in y·N, reading through the inverse as G.inv(x * y) * z",
								"G.inv(x) * z ∈ left_coset(y, N)",
								Simp(Fwd(group.InLeftCosetOn), Fwd(group.MulIn), Fwd(group.InvIn)),
								bridge.Rw(),
								By(inN))
							putBack := c.Have(
								"and x carries G.inv(x) * z back to z",
								"z = x * (G.inv(x) * z)",
								By(group.MulInvCancelLeftOn, grp, xIn, zInC))
							c.Show(
								"z is x times a member of y·N, with x in x·N",
								By(xInOwn, zIn, putBack))
						})
				}))
			a.Show(
				"two subsets of the carrier with the same points of the carrier are equal",
				By(
					set_basic.ExtensionWithin.At(
						a.TermAs[Set[A]]("G.carrier"),
						a.TermAs[Set[A]]("set_mul(left_coset(x, N), left_coset(y, N))"),
						a.TermAs[Set[A]]("left_coset(x * y, N)")),
					productInC,
					xyCosetInC,
					pointwise))
		}),
})}

// LeftCosetMul — LeftCosetMulOn on the whole type.
var LeftCosetMul = leftCosetMulThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetMul",
	Key:  "prop_a455ddc7811a5ade",
	Build: group.GroupAtUniverse.Law(Statement{
		Binders: "∀N:set(A). ∀x y:A.",
		Hypotheses: []string{
			"normal_subgroup(restrict_group(G, 𝕌), N)",
		},
		Conclusion: "set_mul(left_coset(x, N), left_coset(y, N)) = left_coset(x * y, N)",
	}, LeftCosetMulOn),
})}

// LeftCosetInvOn — the inverses of a left coset of a normal subgroup by
// a point of the carrier form the left coset of the inverse. Both sides
// lie in the carrier; one point z of it at a time: z is an inverse of a
// member of x·N exactly when inv(z) lies in x·N, that is when
// inv(x) * inv(z) = inv(z * x) lies in N; and z lies in inv(x)·N exactly
// when inv(inv(x)) * z = x * z does. A subgroup holds inv(z * x) exactly
// when it holds z * x (group.SubgroupInvIffOn), and a normal one holds
// z * x exactly when it holds x * z (group.NormalSubgroupSwapOn).
var LeftCosetInvOn = leftCosetInvOnThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetInvOn",
	Key:  "prop_be4077b52749c723",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀N:set(A). ∀x:A.",
		Hypotheses: []string{
			"normal_subgroup(G, N)",
			"x ∈ G.carrier",
		},
		Conclusion: "set_inv(left_coset(x, N)) = left_coset(G.inv(x), N)",
	},
		func(a *Argument, grp group.GroupFact[on.G], N *Expr[Set[A]], x *Expr[A], normal, member Fact) {
			subgroup := a.Have(
				"a normal subgroup is a subgroup",
				"subgroup(G, N)",
				By(group.NormalSubgroupSubgroup, normal))
			nInC := a.Have(
				"which lies in G.carrier",
				"N ⊆ G.carrier",
				By(group.SubgroupSubset, subgroup))
			cosetInC := a.Have(
				"x·N lies in G.carrier",
				"left_coset(x, N) ⊆ G.carrier",
				By(group.LeftCosetIn, grp, member, nInC))
			inversesInC := a.Have(
				"so do its inverses",
				"set_inv(left_coset(x, N)) ⊆ G.carrier",
				By(SetInvIn, grp, cosetInC))
			otherInC := a.Have(
				"and G.inv(x)·N",
				"left_coset(G.inv(x), N) ⊆ G.carrier",
				By(group.LeftCosetIn, grp, member, nInC, group.InvIn))
			pointwise := a.Have(
				"one point z of the carrier at a time, both memberships read through the inverse",
				"∀z:A. z ∈ G.carrier ⇒ (z ∈ set_inv(left_coset(x, N)) ⇔ z ∈ left_coset(G.inv(x), N))",
				Derive(func(b *Argument) {
					b.FixAs[A]("z")
					zIn := b.Assume()
					productIn := b.Have(
						"z * x lies in G.carrier",
						"z * x ∈ G.carrier",
						By(group.MulIn, grp, zIn, member))
					// z is among the inverses of x·N when inv(x) * inv(z) = inv(z * x)
					// lies in N, and z lies in inv(x)·N when inv(inv(x)) * z = x * z does.
					b.Do(Simp(
						Fwd(InSetInvOn),
						Fwd(group.InLeftCosetOn),
						Fwd(group.InvInvOn),
						Rev(group.InvMulOn),
						Fwd(group.MulIn),
						Fwd(group.InvIn)))
					invIn := b.Have(
						"a subgroup holds G.inv(z * x) exactly when it holds z * x",
						"G.inv(z * x) ∈ N ⇔ z * x ∈ N",
						By(group.SubgroupInvIffOn, subgroup, grp, productIn))
					b.Show(
						"and a normal subgroup holds z * x exactly when it holds x * z",
						invIn.Rw(),
						By(group.NormalSubgroupSwapOn, normal, grp, zIn, member))
				}))
			a.Show(
				"two subsets of the carrier with the same points of the carrier are equal",
				By(
					set_basic.ExtensionWithin.At(
						a.TermAs[Set[A]]("G.carrier"),
						a.TermAs[Set[A]]("set_inv(left_coset(x, N))"),
						a.TermAs[Set[A]]("left_coset(G.inv(x), N)")),
					inversesInC,
					otherInC,
					pointwise))
		}),
})}

// LeftCosetInv — LeftCosetInvOn on the whole type.
var LeftCosetInv = leftCosetInvThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetInv",
	Key:  "prop_2ad590f9cfc4bb03",
	Build: group.GroupAtUniverse.Law(Statement{
		Binders: "∀N:set(A). ∀x:A.",
		Hypotheses: []string{
			"normal_subgroup(restrict_group(G, 𝕌), N)",
		},
		Conclusion: "set_inv(left_coset(x, N)) = left_coset(G.inv(x), N)",
	}, LeftCosetInvOn),
})}

// QuotientGroupOn — the quotient group G/N: the left cosets of a normal
// subgroup N by the points of the carrier are a group on a set under the
// set product, with N as the identity and the set inverse as the
// inverse. The cosets are the image of the carrier under the coset map
// x ↦ x·N (LeftCosetsImage), which carries the product, the identity and
// the inverse of G to the set product (LeftCosetMulOn), N
// (group.LeftCosetOneOn) and the set inverse (LeftCosetInvOn); and the
// image of a group along a map that keeps the product, the identity and
// the inverse is a group (group_homomorphism.ImageGroupOn).
var QuotientGroupOn = quotientGroupOnThm{family.Add(registry.ProofEntry{
	Name: "QuotientGroupOn",
	Key:  "prop_30801e052b0bebc9",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀N:set(A).",
		Hypotheses: []string{
			"normal_subgroup(G, N)",
		},
		Conclusion: "group_on(quotient_group(G, N))",
	},
		func(a *Argument, grp group.GroupFact[on.G], N *Expr[Set[A]], normal Fact) {
			nInC := a.Have(
				"N lies in G.carrier",
				"N ⊆ G.carrier",
				By(group.SubgroupSubset, group.NormalSubgroupSubgroup, normal))
			mulLaw := a.Have(
				"the product of two cosets is the coset of the product",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ G.carrier",
						"y ∈ G.carrier",
					},
					Conclusion: "set_mul(left_coset(x, N), left_coset(y, N)) = left_coset(x * y, N)",
				},
				By(LeftCosetMulOn, grp, normal))
			invLaw := a.Have(
				"the inverses of a coset are the coset of the inverse",
				"∀x:A. x ∈ G.carrier ⇒ set_inv(left_coset(x, N)) = left_coset(G.inv(x), N)",
				By(LeftCosetInvOn, grp, normal))
			image := a.Unfolded(a.Have(
				"the cosets are the image of G.carrier under the coset map",
				"left_cosets(G.carrier, N) = image(coset_map(G.mul, N), G.carrier)",
				By(LeftCosetsImage, grp, nInC)), group.CosetMapDef)
			identity := a.Have(
				"the coset of G.one is N",
				"left_coset(G.one, N) = N",
				By(group.LeftCosetOneOn, grp, nInC))
			quotient := a.TermAs[group.GroupOps[Set[A]]]("quotient_group(G, N)")
			cosetMap := a.TermAs[Fun[A, Set[A]]]("λx:A. left_coset(x, N)")
			a.Show(
				"the image of a group along a map that keeps the product, the identity and the inverse is a group",
				By(
					group_homomorphism.ImageGroupOn.Read(grp).At(quotient, cosetMap),
					image,
					mulLaw,
					identity,
					invLaw))
		}),
})}

// QuotientGroup — QuotientGroupOn on the whole type.
var QuotientGroup = quotientGroupThm{family.Add(registry.ProofEntry{
	Name: "QuotientGroup",
	Key:  "prop_cecf359ed9042dd4",
	Build: group.GroupAtUniverse.Law(Statement{
		Binders: "∀N:set(A).",
		Hypotheses: []string{
			"normal_subgroup(restrict_group(G, 𝕌), N)",
		},
		Conclusion: "group_on(quotient_group(restrict_group(G, 𝕌), N))",
	}, QuotientGroupOn),
})}

// ProjectionKernelOn — the points of the carrier whose coset is N
// itself are the points of N: the kernel of the coset map x ↦ x·N on c,
// read with N as the distinguished point, is N. When N is normal this is
// the kernel of the projection onto the quotient group; the statement
// itself asks only that N be a subgroup. One point at a time: x lies in
// the kernel when it lies in c and its coset is N, which is the coset of
// one; two cosets are equal exactly when inv(x) * one — that is inv(x) —
// lies in N; and a subgroup holds inv(x) exactly when it holds x
// (group.SubgroupInvIffOn), a point of N lying in c.
var ProjectionKernelOn = projectionKernelOnThm{family.Add(registry.ProofEntry{
	Name: "ProjectionKernelOn",
	Key:  "prop_83f05c1125a6f123",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀N:set(A).",
		Hypotheses: []string{
			"subgroup(G, N)",
		},
		Conclusion: "group_kernel(N, G.carrier, coset_map(G.mul, N)) = N",
	},
		func(a *Argument, grp group.GroupFact[on.G], N *Expr[Set[A]], subgroup Fact) {
			nInC := a.Have(
				"N lies in G.carrier",
				"N ⊆ G.carrier",
				By(group.SubgroupSubset, subgroup))
			inN := a.Unfolded(nInC, set_basic.SubsetDef)
			// Two sets are equal when they hold the same points; fix one, x,
			// and read its membership in the kernel as "x lies in c and its
			// coset is N". InKernel is pinned at A, set(A): a Go Simp rule is
			// not instantiated at a type on its own.
			a.Do(Simp(Fwd(set_basic.Extension)))
			a.FixAs[A]("x")
			a.Do(Simp(
				Fwd(group_homomorphism.InKernel.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Set[A]]())),
				Fwd(group.CosetMapDef)))
			a.Iff()
			a.Forward(
				"x lies in G.carrier and its coset is N, which is the "+
					"coset of G.one; so G.inv(x) lies in N, and so does x",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"x lies in G.carrier",
						"its coset is N")
					cosetOne := b.Have(
						"N is the coset of G.one",
						"left_coset(G.one, N) = N",
						By(group.LeftCosetOneOn, grp, nInC))
					cosetEq := b.Have(
						"two cosets by points of G.carrier are equal exactly when G.inv(x) "+
							"times the other's point lies in N, and G.inv(x) * G.one is G.inv(x)",
						"left_coset(x, N) = left_coset(G.one, N) ⇔ G.inv(x) ∈ N",
						Simp(Fwd(group.LeftCosetEqOn), Fwd(group.RightIdentityOn), Fwd(group.OneIn), Fwd(group.InvIn)),
						Basic())
					invIn := b.Have(
						"so G.inv(x) lies in N: the coset of x is the coset of G.one",
						"G.inv(x) ∈ N",
						By(Normalized, parts[1], cosetOne, cosetEq))
					b.Show(
						"and a subgroup holding G.inv(x) holds x, x lying in G.carrier",
						By(group.SubgroupInvIffOn, subgroup, grp, parts[0], invIn))
				})
			a.Backward(
				"a point of N lies in G.carrier, and its coset is N",
				func(b *Argument, xIn Fact) {
					xInC := b.Have(
						"x lies in G.carrier",
						"x ∈ G.carrier",
						By(inN, xIn))
					invIn := b.Have(
						"so N holds G.inv(x)",
						"G.inv(x) ∈ N",
						By(group.SubgroupInvIffOn, subgroup, grp, xInC, xIn))
					cosetOne := b.Have(
						"N is the coset of G.one",
						"left_coset(G.one, N) = N",
						By(group.LeftCosetOneOn, grp, nInC))
					cosetEq := b.Have(
						"two cosets by points of G.carrier are equal exactly when G.inv(x) "+
							"times the other's point lies in N, and G.inv(x) * G.one is G.inv(x)",
						"left_coset(x, N) = left_coset(G.one, N) ⇔ G.inv(x) ∈ N",
						Simp(Fwd(group.LeftCosetEqOn), Fwd(group.RightIdentityOn), Fwd(group.OneIn), Fwd(group.InvIn)),
						Basic())
					b.Do(SplitConj(
						Case(
							"x lies in G.carrier",
							By(xInC)),
						Case(
							"and its coset is the coset of G.one, which is N",
							By(Normalized, cosetEq, invIn, cosetOne)),
					))
				})
		}),
})}

// ProjectionKernel — ProjectionKernelOn on the whole type.
var ProjectionKernel = projectionKernelThm{family.Add(registry.ProofEntry{
	Name: "ProjectionKernel",
	Key:  "prop_46210e693ff3354a",
	Build: group.GroupAtUniverse.Law(Statement{
		Binders: "∀N:set(A).",
		Hypotheses: []string{
			"subgroup(restrict_group(G, 𝕌), N)",
		},
		Conclusion: "group_kernel(N, 𝕌, coset_map(G.mul, N)) = N",
	}, ProjectionKernelOn),
})}

// LeftCosetIsSubgroupIffIn — the left coset of a point x of c by a subgroup h
// is h itself exactly when x lies in h: the points of c with that coset
// form the kernel of the coset map, which is h.
var LeftCosetIsSubgroupIffIn = leftCosetIsSubgroupIffInThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetIsSubgroupIffIn",
	Key:  "prop_77e6430e0b902e26",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A. ∀h:set(A).",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"subgroup(G, h)",
		},
		Conclusion: "left_coset(x, h) = h ⇔ x ∈ h",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Expr[A], h *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"x lies in c",
				"h is a subgroup of c")
			kernel := a.Unfolded(a.Have(
				"the points of c whose coset is h are the points of h",
				"group_kernel(h, G.carrier, coset_map(G.mul, h)) = h",
				By(ProjectionKernelOn.Read(grp), parts[1])), group.CosetMapDef)
			a.Show(
				"x lies in that kernel exactly when its coset is h",
				By(
					Normalized,
					kernel,
					parts[0],
					group_homomorphism.InKernel.At(
						h, a.TermAs[Set[A]]("G.carrier"), a.TermAs[Fun[A, Set[A]]]("λy:A. left_coset(y, h)"), x)))
		}),
})}

// QuotientTrivialIff — a subgroup has a single left coset exactly when
// it is the whole carrier. Both ways a point x of the carrier has the
// coset N exactly when it lies in N (LeftCosetIsSubgroupIffIn): when N
// is the only coset, the coset of x, being one, is N, so x lies in N;
// and when N is the carrier, every coset is the coset of a point of N,
// which is N, while N is itself a coset (SubgroupInLeftCosets).
var QuotientTrivialIff = quotientTrivialIffThm{family.Add(registry.ProofEntry{
	Name: "QuotientTrivialIff",
	Key:  "prop_41cb5705a646a3c0",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀N:set(A).",
		Hypotheses: []string{
			"subgroup(G, N)",
		},
		Conclusion: "left_cosets(G.carrier, N) = {N} ⇔ N = G.carrier",
	},
		func(a *Argument, grp group.GroupFact[on.G], N *Expr[Set[A]], subgroup Fact) {
			nInC := a.Have(
				"N lies in G.carrier",
				"N ⊆ G.carrier",
				By(group.SubgroupSubset.Read(subgroup)))
			a.Iff()
			a.Forward(
				"the coset of a point of G.carrier is a coset, so it is N, and then the point lies in N",
				func(b *Argument, single Fact) {
					holdsCarrier := b.Have(
						"N holds every point of G.carrier",
						"G.carrier ⊆ N",
						Simp(Fwd(set_basic.SubsetDef.Inst[A]())),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xm := c.MemberOf[on.G](x, c.Assume())
							inCosets := c.Have(
								"x·N is a coset",
								"left_coset(x, N) ∈ left_cosets(G.carrier, N)",
								By(nInC, LeftCosetInLeftCosets.Read(grp).At(N, xm)))
							isN := c.Simplified(inCosets, Fwd(single), Fwd(set_basic.InSing.Inst[Set[A]]()))
							c.Show(
								"so x lies in N",
								By(isN, subgroup, LeftCosetIsSubgroupIffIn.Read(grp).At(xm, N)))
						}))
					b.Show(
						"so N, lying in G.carrier, is G.carrier",
						By(nInC, holdsCarrier, set_order.SubsetAntisym.At(N, b.TermAs[Set[A]]("G.carrier"))))
				})
			a.Backward(
				"every coset is the coset of a point of N, which is N, and N is a coset",
				func(b *Argument, whole Fact) {
					cosets := b.TermAs[Set[Set[A]]]("left_cosets(G.carrier, N)")
					onlyN := b.Have(
						"every coset is N: the coset of a point of G.carrier",
						"left_cosets(G.carrier, N) ⊆ {N}",
						Simp(
							Fwd(set_basic.SubsetDef.Inst[Set[A]]()),
							Fwd(set_basic.InSing.Inst[Set[A]]()),
							Fwd(ForallInLeftCosets.Read(grp))),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							xm := c.MemberOf[on.G](x, xIn)
							inN := c.Have(
								"x lies in N, which is G.carrier",
								"x ∈ N",
								BySets(whole, xIn))
							c.Show(
								"so the coset of x is N",
								By(inN, subgroup, LeftCosetIsSubgroupIffIn.Read(grp).At(xm, N)))
						}))
					nIn := b.Have(
						"and N is a coset",
						"{N} ⊆ left_cosets(G.carrier, N)",
						By(subgroup, SubgroupInLeftCosets.Read(grp).At(N), set_order.SingSubset.At(cosets, N)))
					b.Show(
						"so the cosets are N alone",
						By(onlyN, nIn, set_order.SubsetAntisym.At(cosets, b.TermAs[Set[Set[A]]]("{N}"))))
				})
		}),
})}

// LeftCosetSetMulAbsorb — a left coset x·h of a set h holding one, times a
// subgroup k containing h, is the coset x·k. A point (x * u) * v with u in
// h and v in k is x * (u * v), and u * v lies in k; a point x * v of x·k is
// x, which is x * one in x·h, times v.
var LeftCosetSetMulAbsorb = leftCosetSetMulAbsorbThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetSetMulAbsorb",
	Key:  "prop_672608a6c3b50acf",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀x:A. ∀h k:set(A).",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"subgroup(G, k)",
			"h ⊆ k",
			"G.one ∈ h",
		},
		Conclusion: "set_mul(left_coset(x, h), k) = left_coset(x, k)",
	},
		func(a *Argument, grp group.GroupFact[on.G], x *Expr[A], h, k *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"x lies in c",
				"k is a subgroup of c",
				"h lies in k",
				"h holds one")
			xC := a.MemberOf[on.G](x, parts[0])
			subgroup, hInK, oneInH := parts[1], parts[2], parts[3]
			kInC := a.Have(
				"k lies in c",
				"k ⊆ G.carrier",
				By(group.SubgroupSubset, subgroup))
			intoK, intoC := a.Unfolded(hInK, set_basic.SubsetDef), a.Unfolded(kInC, set_basic.SubsetDef)
			pointwise := a.Have(
				"one point z at a time",
				"∀z:A. z ∈ set_mul(left_coset(x, h), k) ⇔ z ∈ left_coset(x, k)",
				Derive(func(b *Argument) {
					b.FixAs[A]("z")
					b.Iff()
					b.Forward(
						"z is (x * u) * v with u in h and v in k, that is x * (u * v) with u * v in k",
						func(d *Argument, member Fact) {
							u, v, point := d.Obtain2As[A, A](
								"z is (x * u) * v for some u in h and v in k",
								"∃u v:A. u ∈ h ∧ v ∈ k ∧ z = (x * u) * v",
								member.Simp(Fwd(InSetMul), Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)),
								By(member))
							pieces := d.Conjuncts(
								point,
								"u lies in h",
								"v lies in k",
								"z is (x * u) * v")
							uK := d.Have(
								"u lies in k",
								"u ∈ k",
								By(intoK, pieces[0]))
							uC := d.MemberOf[on.G](u, d.Have(
								"so u lies in c",
								"u ∈ G.carrier",
								By(intoC, uK)))
							vC := d.MemberOf[on.G](v, d.Have(
								"and so does v",
								"v ∈ G.carrier",
								By(intoC, pieces[1])))
							product := d.Have(
								"u * v lies in the subgroup k",
								"u * v ∈ k",
								By(group.SubgroupMul, subgroup, uK, pieces[1]))
							regroup := d.Have(
								"z regroups as x * (u * v)",
								"z = x * (u * v)",
								By(Normalized, pieces[2], group.AssocOn.Read(grp).At(xC, uC, vC)))
							d.Do(Simp(Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)))
							d.Take(d.TermAs[A]("u * v"))
							d.Show(
								"so z is x times a point of k",
								By(regroup, product))
						})
					b.Backward(
						"z = x * v with v in k is x, a point of x·h as x * one, times v",
						func(d *Argument, member Fact) {
							v, point := d.UnpackAs[A](d.Simplified(
								member,
								Fwd(group.LeftCosetDef),
								Fwd(set_basic.InImage)), "v")
							own := d.Have(
								"x lies in x·h, as x * one",
								"x ∈ left_coset(x, h)",
								Simp(Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)),
								Witness(d.TermAs[A]("G.one")),
								By(group.RightIdentityOn.Read(grp).At(xC), oneInH))
							d.Do(Simp(Fwd(InSetMul)))
							d.Take(x)
							d.Take(v)
							d.Show(
								"so z is x times v, with x in x·h and v in k",
								By(own, point))
						})
				}))
			a.Show(
				"two sets with the same points are equal",
				By(pointwise, set_basic.Extension))
		}),
})}
