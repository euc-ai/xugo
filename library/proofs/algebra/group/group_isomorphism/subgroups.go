// subgroups.go — what subgroups of a group on a set do to each other:
// meets, a subgroup of a subgroup, products, normality carried into a
// subgroup and into a product, and Dedekind's modular law. The
// isomorphism theorems and the butterfly lemma stand on these. A fact
// that needs no group law, only the closure of the sets, binds the
// record G:group_ops(A) and assumes none of its group laws.

package group_isomorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// SubgroupInter — two subgroups meet in a subgroup: h ∩ k lies in h and
// so in G.carrier, and each closure condition holds in h and in k, so in
// both.
var SubgroupInter = subgroupInterThm{family.Add(registry.ProofEntry{
	Name: "SubgroupInter",
	Key:  "prop_b5c0065ee8597b1d",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"subgroup(G, k)",
		},
		Conclusion: "subgroup(G, h ∩ k)",
	},
		func(a *Argument, G *Expr[group.GroupOps[A]], h, k *Expr[Set[A]], given Fact) {
			both := a.Conjuncts(
				given,
				"h is a subgroup of G",
				"so is k")
			hSub, kSub := both[0], both[1]
			a.Show(
				"h ∩ k meets the four conditions of a subgroup of G",
				Simp(Fwd(group.SubgroupDef)),
				SplitConjAll(
					Case(
						"h ∩ k lies in h, which lies in G's carrier",
						BySets(group.SubgroupSubset.Read(hSub))),
					Case(
						"G.one lies in h and in k, as each holds it",
						Simp(Fwd(set_basic.InInter)),
						By(group.SubgroupOne, hSub, kSub)),
					Case(
						"a product of two points of both lies in both, each being closed under the product",
						Simp(Fwd(set_basic.InInter)),
						By(group.SubgroupMul, hSub, kSub)),
					Case(
						"and the inverse of a point of both lies in both, each being closed under the inverse",
						Simp(Fwd(set_basic.InInter)),
						By(group.SubgroupInv, hSub, kSub)),
				))
		}),
})}

// SubgroupTrans — a subgroup of a subgroup is a subgroup: k lies in h,
// which lies in G.carrier, and unfolding restrict_group(G, h) reads its
// identity, product and inverse as G's, so k holds G.one and is closed
// under G's product and inverse.
var SubgroupTrans = subgroupTransThm{family.Add(registry.ProofEntry{
	Name: "SubgroupTrans",
	Key:  "prop_c8bb5ead3bea98ec",

	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"subgroup(restrict_group(G, h), k)",
		},
		Conclusion: "subgroup(G, k)",
	},
		func(a *Argument, G *Expr[group.GroupOps[A]], h, k *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"h is a subgroup of G.carrier",
				"k is a subgroup of G restricted to h")
			hSub, kSub := parts[0], parts[1]
			kParts := a.Conjuncts(
				a.Unfolded(kSub, group.SubgroupDef),
				"k lies in h",
				"k holds G.one",
				"k is closed under G's product",
				"k is closed under G's inverse")
			a.Show(
				"k lies in G.carrier, since k ⊆ h ⊆ G.carrier, and it "+
					"holds G.one and is closed under the product and the inverse",
				Simp(Fwd(group.SubgroupDef)),
				By(
					set_order.SubsetTrans,
					kParts[0],
					group.SubgroupSubset.Read(hSub),
					kParts[1],
					kParts[2],
					kParts[3]))
		}),
})}

// SubgroupRestrict — a subgroup of G.carrier that lies in a set h is a
// subgroup of h: the inclusion is given, the closures are its own.
var SubgroupRestrict = subgroupRestrictThm{family.Add(registry.ProofEntry{
	Name: "SubgroupRestrict",
	Key:  "prop_c4af21b000ae2bb2",

	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(G, k)",
			"k ⊆ h",
		},
		Conclusion: "subgroup(restrict_group(G, h), k)",
	},
		func(a *Argument, G *Expr[group.GroupOps[A]], h, k *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"k is a subgroup of G.carrier",
				"k lies in h")
			kParts := a.Conjuncts(
				a.Unfolded(parts[0], group.SubgroupDef),
				"k lies in G.carrier",
				"k holds G.one",
				"k is closed under the product",
				"k is closed under the inverse")
			a.Show(
				"k ⊆ h is given, and k holds G.one and is closed under "+
					"the product and the inverse as a subgroup of G.carrier",
				Simp(Fwd(group.SubgroupDef)),
				By(parts[1], kParts[1], kParts[2], kParts[3]))
		}),
})}

// PSubgroupRestrict — a p-subgroup of G inside a set K is a p-subgroup
// of G restricted to K: it is a subgroup there (SubgroupRestrict), and
// restricting G to K and then to P is restricting G to P, so the p-group is
// the same.
var PSubgroupRestrict = pSubgroupRestrictThm{family.Add(registry.ProofEntry{
	Name: "PSubgroupRestrict",
	Key:  "prop_bb04d6ccb8ffe127",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀p:num. ∀P K:set(A).",
		Hypotheses: []string{
			"p_subgroup(G, p, P)",
			"P ⊆ K",
		},
		Conclusion: "p_subgroup(restrict_group(G, K), p, P)",
	},
		func(a *Argument, G *Expr[group.GroupOps[A]], p *Expr[Nat], P, K *Expr[Set[A]], pSub, inK Fact) {
			nested := a.Have(
				"restricting to K and then to P is restricting to P",
				"restrict_group(restrict_group(G, K), P) = restrict_group(G, P)",
				Simp(
					Fwd(group.RestrictGroupDef),
					Fwd(group.GroupMulDef),
					Fwd(group.GroupOneDef),
					Fwd(group.GroupInvDef)),
				Refl())
			a.Show(
				"P is a subgroup of K, and the same p-group",
				Simp(Fwd(finite_group.PSubgroupDef)),
				nested.Rw(),
				By(
					finite_group.PSubgroupSubgroup.Read(pSub),
					finite_group.PSubgroupPGroup.Read(pSub),
					inK,
					SubgroupRestrict.At(G, K, P)))
		}),
})}

// SetMulSubgroup — the product of two subgroups is a subgroup when the
// first normalizes the second: hk is then closed under the product
// because a factor of k passes a factor of h as a conjugate, and under
// the inverse because inv(x * y) is inv(y) * inv(x), which is inv(x)
// times a conjugate of inv(y) by x.
var SetMulSubgroup = setMulSubgroupThm{family.Add(registry.ProofEntry{
	Name: "SetMulSubgroup",
	Key:  "prop_b311346796debe7a",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"subgroup(G, k)",
			"∀x y:A. x ∈ h ∧ y ∈ k ⇒ x * y * G.inv(x) ∈ k",
		},
		Conclusion: "subgroup(G, set_mul(h, k))",
	},
		func(a *Argument, grp group.GroupFact[on.G], h, k *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"h is a subgroup of G.carrier",
				"so is k",
				"and h normalizes k")
			hSub, kSub, normalizes := parts[0], parts[1], parts[2]
			hInC := a.Have(
				"h lies in G.carrier",
				"h ⊆ G.carrier",
				By(group.SubgroupSubset, hSub))
			kInC := a.Have(
				"so does k",
				"k ⊆ G.carrier",
				By(group.SubgroupSubset, kSub))
			hPoints, kPoints := a.Unfolded(hInC, set_basic.SubsetDef), a.Unfolded(kInC, set_basic.SubsetDef)
			a.Do(Simp(Fwd(group.SubgroupDef)), SplitConjAll(
				Case(
					"hk lies in G.carrier, its two factors lying in G.carrier",
					By(quotient_group.SetMulIn, grp, hInC, kInC)),
				Case(
					"hk holds G.one, which is G.one * G.one",
					Simp(Fwd(quotient_group.InSetMul)),
					Derive(func(b *Argument) {
						b.Take(b.TermAs[A]("G.one"))
						b.Take(b.TermAs[A]("G.one"))
						b.Show(
							"G.one lies in h and in k, and G.one * G.one is G.one",
							By(group.SubgroupOne, hSub, kSub, group.LeftIdentityOn, grp, group.OneIn))
					})),
				Case(
					"hk is closed under the product: y₁ passes x₂ as its conjugate by G.inv(x₂)",
					Derive(func(b *Argument) {
						b.FixAs[A]("z")
						b.FixAs[A]("w")
						both := b.Conjuncts(
							b.Assume(),
							"z lies in hk",
							"so does w")
						x1, y1, zSplit := b.Unpack2As[A, A](b.Have(
							"z is x₁ * y₁ with x₁ in h and y₁ in k",
							"∃x₁ y₁:A. x₁ ∈ h ∧ y₁ ∈ k ∧ z = x₁ * y₁",
							By(both[0], quotient_group.InSetMul)), "x₁", "y₁")
						x2, y2, wSplit := b.Unpack2As[A, A](b.Have(
							"w is x₂ * y₂ with x₂ in h and y₂ in k",
							"∃x₂ y₂:A. x₂ ∈ h ∧ y₂ ∈ k ∧ w = x₂ * y₂",
							By(both[1], quotient_group.InSetMul)), "x₂", "y₂")
						zParts := b.Conjuncts(
							zSplit,
							"x₁ lies in h",
							"y₁ lies in k",
							"z is x₁ * y₁")
						wParts := b.Conjuncts(
							wSplit,
							"x₂ lies in h",
							"y₂ lies in k",
							"w is x₂ * y₂")
						x1C := b.MemberOf[on.G](x1, b.Have(
							"x₁ lies in G.carrier",
							"x₁ ∈ G.carrier",
							By(hPoints, zParts[0])))
						y1C := b.MemberOf[on.G](y1, b.Have(
							"y₁ lies in G.carrier",
							"y₁ ∈ G.carrier",
							By(kPoints, zParts[1])))
						x2C := b.MemberOf[on.G](x2, b.Have(
							"x₂ lies in G.carrier",
							"x₂ ∈ G.carrier",
							By(hPoints, wParts[0])))
						y2C := b.MemberOf[on.G](y2, b.Have(
							"y₂ lies in G.carrier",
							"y₂ ∈ G.carrier",
							By(kPoints, wParts[1])))
						inverseInH := b.Have(
							"G.inv(x₂) lies in h",
							"G.inv(x₂) ∈ h",
							By(group.SubgroupInv, hSub, wParts[0]))
						conjugate := b.Have(
							"h normalizes k: the conjugate of y₁ by G.inv(x₂) lies in k, and G.inv(G.inv(x₂)) is x₂",
							"G.inv(x₂) * y₁ * x₂ ∈ k",
							By(
								Normalized,
								normalizes.At(b.TermAs[A]("G.inv(x₂)"), y1),
								inverseInH,
								zParts[1],
								group.InvInvOn.Read(grp).At(x2C)))
						invX2C := group.InvIn.Read(grp).At(x2C)
						regroup := b.Have(
							"the k-factor regrouped around the conjugate",
							"G.inv(x₂) * (y₁ * (x₂ * y₂)) = G.inv(x₂) * y₁ * x₂ * y₂",
							CalcEq(
								Leg(
									b.TermAs[A]("(G.inv(x₂) * y₁) * (x₂ * y₂)"),
									"regroup, so G.inv(x₂) meets y₁",
									By(group.AssocOn.Read(grp).At(invX2C, y1C, group.MulIn.Read(grp).At(x2C, y2C)))),
								FinalLeg(
									"and regroup again, so the conjugate stands before y₂",
									By(group.AssocOn.Read(grp).At(group.MulIn.Read(grp).At(invX2C, y1C), x2C, y2C))),
							))
						factorInK := b.Have(
							"so the k-factor lies in k: it is the conjugate times y₂",
							"G.inv(x₂) * (y₁ * (x₂ * y₂)) ∈ k",
							regroup.Rw(),
							By(group.SubgroupMul, kSub, conjugate, wParts[1]))
						product := b.Have(
							"z * w is x₁ * x₂ times the k-factor",
							"(x₁ * y₁) * (x₂ * y₂) = (x₁ * x₂) * (G.inv(x₂) * (y₁ * (x₂ * y₂)))",
							CalcEq(
								Leg(
									b.TermAs[A]("x₁ * (y₁ * (x₂ * y₂))"),
									"regroup, so x₁ stands alone",
									By(group.AssocOn, grp, x1C, y1C, x2C, y2C, group.MulIn)),
								Leg(
									b.TermAs[A]("x₁ * (x₂ * (G.inv(x₂) * (y₁ * (x₂ * y₂))))"),
									"x₂ undoes the G.inv(x₂) after it",
									Simp(Fwd(group.MulInvCancelLeftOn), Fwd(group.MulIn)),
									Refl()),
								FinalLeg(
									"and regroup, so x₁ * x₂ stands first",
									By(group.AssocOn, grp, x1C, x2C, y1C, y2C, group.InvIn, group.MulIn)),
							))
						b.Do(zParts[2].Rw(), wParts[2].Rw(), Simp(Fwd(quotient_group.InSetMul)))
						b.Take(b.TermAs[A]("x₁ * x₂"))
						b.Take(b.TermAs[A]("G.inv(x₂) * (y₁ * (x₂ * y₂))"))
						b.Show(
							"x₁ * x₂ lies in h, the k-factor in k, and their product is z * w",
							By(product, factorInK, zParts[0], wParts[0], hSub, group.SubgroupMul))
					})),
				Case(
					"hk is closed under the inverse: G.inv(x * y) is G.inv(x) times the conjugate of G.inv(y) by x",
					Derive(func(b *Argument) {
						b.FixAs[A]("z")
						member := b.Assume()
						x, y, split := b.Unpack2As[A, A](b.Have(
							"z is x * y with x in h and y in k",
							"∃x y:A. x ∈ h ∧ y ∈ k ∧ z = x * y",
							By(member, quotient_group.InSetMul)), "x", "y")
						factors := b.Conjuncts(
							split,
							"x lies in h",
							"y lies in k",
							"z is x * y")
						xC := b.MemberOf[on.G](x, b.Have(
							"x lies in G.carrier",
							"x ∈ G.carrier",
							By(hPoints, factors[0])))
						yC := b.MemberOf[on.G](y, b.Have(
							"y lies in G.carrier",
							"y ∈ G.carrier",
							By(kPoints, factors[1])))
						inverseInH := b.Have(
							"G.inv(x) lies in h",
							"G.inv(x) ∈ h",
							By(group.SubgroupInv, hSub, factors[0]))
						conjugate := b.Have(
							"h normalizes k: the conjugate of G.inv(y) by x lies in k",
							"x * G.inv(y) * G.inv(x) ∈ k",
							By(normalizes, factors[0], group.SubgroupInv, kSub, factors[1]))
						inverse := b.Have(
							"G.inv(x * y) is G.inv(x) times that conjugate",
							"G.inv(x * y) = G.inv(x) * (x * G.inv(y) * G.inv(x))",
							CalcEq(
								Leg(
									b.TermAs[A]("G.inv(y) * G.inv(x)"),
									"the inverse of a product reverses it",
									By(group.InvMulOn, grp, xC, yC)),
								Leg(
									b.TermAs[A]("(G.inv(x) * (x * G.inv(y))) * G.inv(x)"),
									"G.inv(x) undoes the x before G.inv(y)",
									Simp(Fwd(group.InvMulCancelLeftOn), Fwd(group.InvIn)),
									Refl()),
								FinalLeg(
									"and regroup",
									By(group.AssocOn, grp, xC, yC, group.InvIn, group.MulIn)),
							))
						b.Do(factors[2].Rw(), Simp(Fwd(quotient_group.InSetMul)))
						b.Take(b.TermAs[A]("G.inv(x)"))
						b.Take(b.TermAs[A]("x * G.inv(y) * G.inv(x)"))
						b.Show(
							"G.inv(x) lies in h, the conjugate in k, and their product is G.inv(x * y)",
							By(inverse, inverseInH, conjugate))
					})),
			))
		}),
})}

// SetMulNormal — the product of a subgroup and a normal subgroup is a
// subgroup: a normal subgroup is normalized by everything.
var SetMulNormal = setMulNormalThm{family.Add(registry.ProofEntry{
	Name: "SetMulNormal",
	Key:  "prop_25f486945db84067",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h n:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"normal_subgroup(G, n)",
		},
		Conclusion: "subgroup(G, set_mul(h, n))",
	},
		func(a *Argument, grp group.GroupFact[on.G], h, n *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"h is a subgroup of G.carrier",
				"n is normal in G.carrier")
			subgroup, normal := parts[0], parts[1]
			hPoints := a.Unfolded(group.SubgroupSubset.Read(subgroup).AsFact(), set_basic.SubsetDef)
			normalizes := a.Have(
				"h normalizes n: a conjugate by a point of h is a conjugate by a point of G.carrier",
				"∀x y:A. x ∈ h ∧ y ∈ n ⇒ x * y * G.inv(x) ∈ n",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					members := b.Conjuncts(
						b.Assume(),
						"x lies in h",
						"y lies in n")
					xInC := b.Have(
						"x lies in G.carrier, which holds all of h",
						"x ∈ G.carrier",
						By(hPoints, members[0]))
					b.Show(
						"n holds the conjugate of its member y by x",
						By(group.NormalSubgroupConjugate, normal, xInC, members[1]))
				}))
			a.Show(
				"hn is a subgroup, the product of two subgroups the first of which normalizes the second",
				By(SetMulSubgroup.Read(grp), subgroup, group.NormalSubgroupSubgroup, normal, normalizes))
		}),
})}

// SetMulNormalSwap — a normal subgroup commutes with any subset of
// G.carrier as a set: hn = nh, each product x * y being the conjugate
// x * y * inv(x) times x, and each y * x being x times the conjugate
// inv(x) * y * x.
var SetMulNormalSwap = setMulNormalSwapThm{family.Add(registry.ProofEntry{
	Name: "SetMulNormalSwap",
	Key:  "prop_11b4258656da8057",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h n:set(A).",
		Hypotheses: []string{
			"h ⊆ G.carrier",
			"normal_subgroup(G, n)",
		},
		Conclusion: "set_mul(h, n) = set_mul(n, h)",
	},
		func(a *Argument, grp group.GroupFact[on.G], h, n *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"h lies in G.carrier",
				"n is normal in G.carrier")
			hInC, normal := parts[0], parts[1]
			hPoints := a.Unfolded(hInC, set_basic.SubsetDef)
			nPoints := a.Unfolded(
				group.SubgroupSubset.Read(group.NormalSubgroupSubgroup.Read(normal)).AsFact(),
				set_basic.SubsetDef)
			a.Do(Simp(Fwd(set_basic.Extension)))
			a.FixAs[A]("z")
			a.Iff()
			a.Forward(
				"a point x * y of hn is the conjugate x * y * G.inv(x), a point of n, times x",
				func(b *Argument, member Fact) {
					x, y, split := b.Unpack2As[A, A](b.Have(
						"z is x * y with x in h and y in n",
						"∃x y:A. x ∈ h ∧ y ∈ n ∧ z = x * y",
						By(member, quotient_group.InSetMul)), "x", "y")
					factors := b.Conjuncts(
						split,
						"x lies in h",
						"y lies in n",
						"z is x * y")
					xC := b.MemberOf[on.G](x, b.Have(
						"x lies in G.carrier",
						"x ∈ G.carrier",
						By(hPoints, factors[0])))
					yC := b.MemberOf[on.G](y, b.Have(
						"y lies in G.carrier",
						"y ∈ G.carrier",
						By(nPoints, factors[1])))
					conjugate := b.Have(
						"n holds the conjugate of its point y by x",
						"x * y * G.inv(x) ∈ n",
						By(group.NormalSubgroupConjugate, normal, xC, factors[1]))
					b.Do(factors[2].Rw(), Simp(Fwd(quotient_group.InSetMul)))
					b.Take(b.TermAs[A]("x * y * G.inv(x)"))
					b.Take(x)
					b.Show(
						"the conjugate lies in n, x in h, and the conjugate times x is x * y, G.inv(x) * x cancelling",
						By(
							conjugate,
							factors[0],
							group.InvMulCancelRightOn.Read(grp).At(xC, group.MulIn.Read(grp).At(xC, yC))))
				})
			a.Backward(
				"a point y * x of nh is x times the conjugate G.inv(x) * y * x, a point of n",
				func(b *Argument, member Fact) {
					y, x, split := b.Unpack2As[A, A](b.Have(
						"z is y * x with y in n and x in h",
						"∃y x:A. y ∈ n ∧ x ∈ h ∧ z = y * x",
						By(member, quotient_group.InSetMul)), "y", "x")
					factors := b.Conjuncts(
						split,
						"y lies in n",
						"x lies in h",
						"z is y * x")
					xC := b.MemberOf[on.G](x, b.Have(
						"x lies in G.carrier",
						"x ∈ G.carrier",
						By(hPoints, factors[1])))
					yC := b.MemberOf[on.G](y, b.Have(
						"y lies in G.carrier",
						"y ∈ G.carrier",
						By(nPoints, factors[0])))
					inverse := group.InvIn.Read(grp).At(xC)
					conjugate := b.Have(
						"n holds the conjugate of its point y by G.inv(x), and G.inv(G.inv(x)) is x",
						"G.inv(x) * y * x ∈ n",
						By(
							Normalized,
							inverse,
							factors[0],
							group.NormalSubgroupConjugate.Read(normal).AsFact().At(inverse, y),
							group.InvInvOn.Read(grp).At(xC)))
					b.Do(factors[2].Rw(), Simp(Fwd(quotient_group.InSetMul)))
					b.Take(x)
					b.Take(b.TermAs[A]("G.inv(x) * y * x"))
					b.Show(
						"x lies in h, the conjugate in n, and x times the conjugate "+
							"regroups to x * (G.inv(x) * y) times x, which is y * x",
						By(
							factors[1],
							conjugate,
							group.AssocOn.Read(grp).At(xC, group.MulIn.Read(grp).At(inverse, yC), xC),
							group.MulInvCancelLeftOn.Read(grp).At(xC, yC)))
				})
		}),
})}

// SetMulAbsorb — a subgroup absorbs a subset of it holding one: hk = h.
var SetMulAbsorb = setMulAbsorbThm{family.Add(registry.ProofEntry{
	Name: "SetMulAbsorb",
	Key:  "prop_3e6d35d948eea5b8",

	Deps: []registry.EntryLike{
		quotient_group.InSetMul,
		group.SubgroupMul,
		group.SubgroupSubset,
		group.RightIdentityOn,
		set_basic.Extension,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"k ⊆ h",
			"G.one ∈ k",
		},
		Conclusion: "set_mul(h, k) = h",
	}),
		"hk ⊆ h by closure, k lying in h; x = x * G.one with G.one ∈ k"),
})}

// SubsetSetMulLeft — a subgroup lies in its product with another: a
// point x of h is x * G.one, the product of a point of h and of the
// identity, which the other subgroup holds.
var SubsetSetMulLeft = subsetSetMulLeftThm{family.Add(registry.ProofEntry{
	Name: "SubsetSetMulLeft",
	Key:  "prop_65d078e8f9820c69",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"subgroup(G, k)",
		},
		Conclusion: "h ⊆ set_mul(h, k)",
	},
		func(a *Argument, grp group.GroupFact[on.G], h, k *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"h is a subgroup of G.carrier",
				"so is k")
			hPoints := a.Unfolded(group.SubgroupSubset.Read(parts[0]).AsFact(), set_basic.SubsetDef)
			a.Do(Unfold(set_basic.SubsetDef))
			x := a.FixAs[A]("x")
			inH := a.Assume()
			xC := a.MemberOf[on.G](x, a.Have(
				"x lies in G.carrier, which holds all of h",
				"x ∈ G.carrier",
				By(hPoints, inH)))
			a.Do(Simp(Fwd(quotient_group.InSetMul)))
			a.Take(x)
			a.Take(a.TermAs[A]("G.one"))
			a.Show(
				"x lies in h, the identity in k, and x * G.one is x",
				By(inH, group.SubgroupOne.Read(parts[1]).AsFact(), group.RightIdentityOn.Read(grp).At(xC)))
		}),
})}

// SubsetSetMulRight — and so does the other.
var SubsetSetMulRight = subsetSetMulRightThm{family.Add(registry.ProofEntry{
	Name: "SubsetSetMulRight",
	Key:  "prop_c46b96e08e39707d",

	Deps: []registry.EntryLike{
		quotient_group.InSetMul,
		group.SubgroupOne,
		group.LeftIdentityOn,
		group.SubgroupSubset,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀h k:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"subgroup(G, k)",
		},
		Conclusion: "k ⊆ set_mul(h, k)",
	}),
		"y = G.one * y with G.one ∈ h, y lying in G.carrier through k"),
})}

// NormalRestrict — a normal subgroup of G.carrier that lies in a
// subgroup h is normal in h. The restricted group keeps G's product and
// inverse on the carrier h, so n is a subgroup of it as a subgroup of
// G.carrier lying in h, and a conjugate of a point of n by a point of h,
// a point of G.carrier, stays in n by normality in G.
var NormalRestrict = normalRestrictThm{family.Add(registry.ProofEntry{
	Name: "NormalRestrict",
	Key:  "prop_d964cbfc5d105b27",

	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀h n:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"normal_subgroup(G, n)",
			"n ⊆ h",
		},
		Conclusion: "normal_subgroup(restrict_group(G, h), n)",
	},
		func(a *Argument, G *Expr[group.GroupOps[A]], h, n *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"h is a subgroup of G.carrier",
				"n is normal in G.carrier",
				"n lies in h")
			hSub, normal, nInH := parts[0], parts[1], parts[2]
			a.Show(
				"n is a subgroup of h, and conjugation by a point of h keeps n",
				Simp(Fwd(group.NormalSubgroupDef)),
				SplitConj(
					Case(
						"n is a subgroup of G.carrier lying in h, hence a subgroup of h",
						By(SubgroupRestrict, group.NormalSubgroupSubgroup, normal, nInH)),
					Case(
						"a conjugate of a point of n by a point of h lies in n",
						Derive(func(b *Argument) {
							b.FixAs[A]("g")
							b.FixAs[A]("x")
							members := b.Conjuncts(
								b.Assume(),
								"g lies in h",
								"x lies in n")
							hPoints := b.Unfolded(group.SubgroupSubset.Read(hSub).AsFact(), set_basic.SubsetDef)
							b.Show(
								"g lies in G.carrier, which holds all of h, so n holds the conjugate of its member x by g",
								By(group.NormalSubgroupConjugate, normal, hPoints, members[0], members[1]))
						})),
				))
		}),
})}

// NormalInter — a normal subgroup of G.carrier meets a subgroup h in a
// normal subgroup of h: a conjugate by a point of h stays in h by
// closure and in n by normality.
var NormalInter = normalInterThm{family.Add(registry.ProofEntry{
	Name: "NormalInter",
	Key:  "prop_cecc15b46830f7f7",

	Deps: []registry.EntryLike{
		SubgroupInter,
		SubgroupRestrict,
		group.NormalSubgroupDef,
		group.NormalSubgroupSubgroup,
		group.NormalSubgroupConjugate,
		group.SubgroupMul,
		group.SubgroupInv,
		group.SubgroupSubset,
		set_basic.InInter,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀h n:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"normal_subgroup(G, n)",
		},
		Conclusion: "normal_subgroup(restrict_group(G, h), h ∩ n)",
	},
		"h ∩ n is a subgroup of G.carrier (SubgroupInter) lying in h, "+
			"hence of h (SubgroupRestrict); a conjugate by g in h of x in h ∩ "+
			"n lies in h by closure and in n by normality, g lying in G.carrier"),
})}

// NormalInSetMul — a normal subgroup is normal in its product with any
// subgroup: it lies in the product, which lies in G.carrier.
var NormalInSetMul = normalInSetMulThm{family.Add(registry.ProofEntry{
	Name: "NormalInSetMul",
	Key:  "prop_224a8920430ce0bc",

	Deps: []registry.EntryLike{
		SetMulNormal,
		SubsetSetMulRight,
		NormalRestrict,
		group.NormalSubgroupSubgroup,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀h n:set(A).",
		Hypotheses: []string{
			"subgroup(G, h)",
			"normal_subgroup(G, n)",
		},
		Conclusion: "normal_subgroup(restrict_group(G, set_mul(h, n)), n)",
	}),
		"NormalRestrict at the subgroup hn (SetMulNormal), n lying in hn (SubsetSetMulRight)"),
})}

// DedekindModular — Dedekind's modular law: for a subset h of a
// subgroup k, what k meets of hn is h times what k meets of n. Only k
// is a subgroup; h and n are subsets. A point x * y of k with x in h
// and y in n has its factor y = G.inv(x) * (x * y) in k, x lying in k;
// conversely k holds x * y for x in h and y in k.
var DedekindModular = dedekindModularThm{family.Add(registry.ProofEntry{
	Name: "DedekindModular",
	Key:  "prop_4a2c2ad3861d8b83",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h k n:set(A).",
		Hypotheses: []string{
			"subgroup(G, k)",
			"h ⊆ k",
			"n ⊆ G.carrier",
		},
		Conclusion: "k ∩ set_mul(h, n) = set_mul(h, k ∩ n)",
	},
		func(a *Argument, grp group.GroupFact[on.G], h, k, n *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"k is a subgroup of G.carrier",
				"h lies in k",
				"n lies in G.carrier")
			subgroup, hInK, nInC := parts[0], parts[1], parts[2]
			hPoints := a.Unfolded(hInK, set_basic.SubsetDef)
			a.Do(Simp(Fwd(set_basic.Extension)))
			z := a.FixAs[A]("z")
			a.Iff()
			a.Forward(
				"a point z = x * y of k with x in h and y in n has y = G.inv(x) * z in k, x lying in k",
				func(b *Argument, member Fact) {
					inBoth := b.Conjuncts(
						b.Simplified(member, Fwd(set_basic.InInter)),
						"z lies in k",
						"z lies in hn")
					x, y, split := b.Unpack2As[A, A](b.Have(
						"z is x * y with x in h and y in n",
						"∃x y:A. x ∈ h ∧ y ∈ n ∧ z = x * y",
						By(inBoth[1], quotient_group.InSetMul)), "x", "y")
					factors := b.Conjuncts(
						split,
						"x lies in h",
						"y lies in n",
						"z is x * y")
					kPoints := b.Unfolded(group.SubgroupSubset.Read(subgroup).AsFact(), set_basic.SubsetDef)
					nPoints := b.Unfolded(nInC, set_basic.SubsetDef)
					xInK := b.Have(
						"x lies in k, which holds all of h",
						"x ∈ k",
						By(hPoints, factors[0]))
					xC := b.MemberOf[on.G](x, b.Have(
						"x lies in G.carrier, which holds all of k",
						"x ∈ G.carrier",
						By(kPoints, xInK)))
					yC := b.MemberOf[on.G](y, b.Have(
						"y lies in G.carrier",
						"y ∈ G.carrier",
						By(nPoints, factors[1])))
					yInK := b.Have(
						"y is G.inv(x) * z, a product of two points of k",
						"y ∈ k",
						By(
							Normalized,
							xInK,
							group.SubgroupInv.Read(subgroup).AsFact().At(x),
							inBoth[0],
							group.SubgroupMul.Read(subgroup).AsFact().At(b.TermAs[A]("G.inv(x)"), z),
							factors[2],
							group.InvMulCancelLeftOn.Read(grp).At(xC, yC)))
					b.Do(factors[2].Rw(), Simp(Fwd(quotient_group.InSetMul)))
					b.Take(x)
					b.Take(y)
					b.Show(
						"x lies in h, and y in k and in n",
						By(factors[0], yInK, factors[1], set_basic.InInter))
				})
			a.Backward(
				"a point x * y of h(k ∩ n) lies in k, x and y lying in k, and in hn by the same factors",
				func(b *Argument, member Fact) {
					x, y, split := b.Unpack2As[A, A](b.Have(
						"z is x * y with x in h and y in k ∩ n",
						"∃x y:A. x ∈ h ∧ y ∈ k ∩ n ∧ z = x * y",
						By(member, quotient_group.InSetMul)), "x", "y")
					factors := b.Conjuncts(
						split,
						"x lies in h",
						"y lies in k ∩ n",
						"z is x * y")
					yIn := b.Conjuncts(
						b.Simplified(factors[1], Fwd(set_basic.InInter)),
						"y lies in k",
						"y lies in n")
					b.Do(factors[2].Rw(), Simp(Fwd(set_basic.InInter), Fwd(quotient_group.InSetMul)))
					b.Show(
						"x * y lies in k, and x and y factor it in hn",
						SplitConj(
							Case(
								"k holds x, a point of h, and y, so it holds x * y",
								By(group.SubgroupMul, subgroup, hPoints, factors[0], yIn[0])),
							Case(
								"x lies in h and y in n",
								Witness(x),
								Witness(y),
								By(factors[0], yIn[1]))))
				})
		}),
})}
