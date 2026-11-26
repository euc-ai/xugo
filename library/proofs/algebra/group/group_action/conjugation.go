// conjugation.go — a group acting on its subsets by conjugation, and the
// normalizer of a subgroup as the stabilizer of that action.

package group_action

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ConjugationAction — a group acts on the subsets of its carrier by
// conjugation, S ↦ gSg⁻¹. The axiom that takes work is the product's: the
// inverse of gh is h⁻¹g⁻¹, so (gh)u(gh)⁻¹ = g(huh⁻¹)g⁻¹ at each point u.
var ConjugationAction = conjugationActionThm{family.Add(registry.ProofEntry{
	Name: "ConjugationAction",
	Key:  "prop_e18711a591220315",
	Build: group.GroupOn.Law("group_action(G, {S:set(A) | S ⊆ G.carrier}, group_conjugate(G))",
		func(a *Argument, grp group.GroupFact[on.G]) {
			a.Do(GroupAction.Intro(
				Case(
					"G is a group",
					By(grp)),
				Case(
					"a conjugate of a subset of the carrier lies in the carrier",
					Unfold(GroupConjugateDef),
					BySets(grp, group.MulIn, group.InvIn)),
				Case(
					"the identity conjugates every subset of the carrier to itself",
					Unfold(GroupConjugateDef),
					BySets(grp, group.LeftIdentityOn, group.RightIdentityOn, group.InvOneOn)),
				Case(
					"conjugating by g * h is conjugating by h and then by g",
					Derive(func(b *Argument) {
						b.FixAs[A]("g")
						b.FixAs[A]("h")
						b.FixAs[Set[A]]("S")
						points := b.Assume()
						compose := b.Have(
							"at each point u of S the two conjugations agree",
							"∀u:A. u ∈ S ⇒ g * h * u * G.inv(g * h) = g * (h * u * G.inv(h)) * G.inv(g)",
							Derive(func(c *Argument) {
								c.FixAs[A]("u")
								inS := c.Assume()
								c.Have(
									"u lies in the carrier, as S does",
									"u ∈ G.carrier",
									BySets(inS, points))
								c.Show(
									"the inverse of g * h is G.inv(h) * G.inv(g), and associativity regroups the factors",
									Simp(Fwd(group.InvMulOn)),
									Simp(Rev(group.AssocOn), Fwd(group.MulIn), Fwd(group.InvIn)),
									Basic())
							}))
						b.Show(
							"so the two images of S are equal",
							Unfold(GroupConjugateDef),
							BySets(compose))
					})),
			))
		}),
})}

// ConjugateSubgroup — a conjugate gHg⁻¹ of a subgroup H is a subgroup:
// conjugation by g is an automorphism of the group
// (group_homomorphism.InnerAutomorphism), and gHg⁻¹, the image of H under
// it, is a subgroup as the image of one under a homomorphism
// (group_homomorphism.SubgroupImage).
var ConjugateSubgroup = conjugateSubgroupThm{family.Add(registry.ProofEntry{
	Name: "ConjugateSubgroup",
	Key:  "prop_acc1eb424e0e1985",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H:set(A). ∀g:A.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"subgroup(G, H)",
		},
		Conclusion: "subgroup(G, group_conjugate(G, g, H))",
	},
		func(a *Argument, grp group.GroupFact[on.G], H *Expr[Set[A]], sub Fact, g *Member[A, on.G]) {
			automorphism := a.Have(
				"conjugation by g is an automorphism of G",
				"group_isomorphism(G, G, λx:A. g * x * G.inv(g))",
				By(group_homomorphism.InnerAutomorphism.Read(grp).At(g)))
			homomorphism := group_homomorphism.IsomorphismHomomorphism.Read(automorphism)
			a.Show(
				"so the conjugate of H, its image under that automorphism, is a subgroup",
				Unfold(GroupConjugateDef),
				By(sub, group_homomorphism.SubgroupImage.Read(homomorphism).At(H)))
		}),
})}

// ConjugateCard — conjugation keeps the size of a finite subset of the
// carrier. Conjugation by g is an automorphism of the group, so one-to-one
// on the carrier and on S, and a one-to-one image of a finite set has its
// size.
var ConjugateCard = conjugateCardThm{family.Add(registry.ProofEntry{
	Name: "ConjugateCard",
	Key:  "prop_15bfbdef310c4975",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀S:set(A). ∀g:A.",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"S ⊆ G.carrier",
			"finite(S)",
		},
		Conclusion: "card(group_conjugate(G, g, S)) = card(S)",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			S *Expr[Set[A]],
			inside, finite Fact,
			g *Member[A, on.G],
		) {
			conjugation := a.TermAs[Fun[A, A]]("λx:A. g * x * G.inv(g)")
			carrier := a.TermAs[Set[A]]("G.carrier")
			automorphism := a.Have(
				"conjugation by g is an automorphism of G",
				"group_isomorphism(G, G, λx:A. g * x * G.inv(g))",
				By(group_homomorphism.InnerAutomorphism.Read(grp).At(g)))
			a.Show(
				"so it is one-to-one on the carrier and on S, whose image then has the size of the finite S",
				Unfold(GroupConjugateDef),
				By(
					group_homomorphism.IsomorphismInjective.Read(automorphism),
					inside,
					finite,
					functions.InjectiveOnSubset.At(conjugation, S, carrier),
					cardinality.CardImageInj.At(conjugation, S)))
		}),
})}

// ConjugateFinite — a conjugate of a finite set is finite: it is an image
// of the set. No group law is read, so the record need not be a group.
var ConjugateFinite = conjugateFiniteThm{family.Add(registry.ProofEntry{
	Name: "ConjugateFinite",
	Key:  "prop_1c9d85f1a5da3ae5",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀g:A. ∀S:set(A).",
		Hypotheses: []string{
			"finite(S)",
		},
		Conclusion: "finite(group_conjugate(G, g, S))",
	},
		func(a *Argument, G *Expr[GroupOps[A]], g *Expr[A], S *Expr[Set[A]], finite Fact) {
			a.Show(
				"the conjugate is the image of the finite S under conjugation by g",
				Unfold(GroupConjugateDef),
				By(finite, finite_set.FiniteImage))
		}),
})}

// NormalizerSubgroup — the normalizer of a subgroup is a subgroup holding
// it, and the subgroup is normal in it. The normalizer is the stabilizer of
// H when G acts on its subsets by conjugation (NormalizerIsStabilizer), so
// a subgroup; an element h of H conjugates H into H by closure, and onto
// it, h⁻¹xh being a point of H that h conjugates to x; and an element of
// the normalizer conjugates each point of H into H, which is normality
// inside the normalizer.
var NormalizerSubgroup = normalizerSubgroupThm{family.Add(registry.ProofEntry{
	Name: "NormalizerSubgroup",
	Key:  "prop_fef016c8a8deba1b",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H:set(A).",
		Hypotheses: []string{
			"subgroup(G, H)",
		},
		Conclusion: "subgroup(G, group_normalizer(G, H)) ∧ " +
			"H ⊆ group_normalizer(G, H) ∧ " +
			"normal_subgroup(restrict_group(G, group_normalizer(G, H)), H)",
	},
		func(a *Argument, grp group.GroupFact[on.G], H *Expr[Set[A]], sub Fact) {
			G := a.TermAs[GroupOps[A]]("G")
			N := a.TermAs[Set[A]]("group_normalizer(G, H)")
			subset := a.Have(
				"H is a subset of the carrier, so a point the conjugation action acts on",
				"H ∈ {S:set(A) | S ⊆ G.carrier}",
				BySets(group.SubgroupSubset.Read(sub)))
			isSubgroup := a.Have(
				"so the normalizer, the stabilizer of H under conjugation, is a subgroup",
				"subgroup(G, group_normalizer(G, H))",
				Simp(Rev(NormalizerIsStabilizer)),
				By(StabilizerSubgroup.Read(ConjugationAction.Read(grp)).At(a.MemberOf[on.Any](H, subset))))
			ownConjugates := a.Have(
				"an element h of H conjugates H onto H",
				"∀h:A. h ∈ H ⇒ group_conjugate(G, h, H) = H",
				Derive(func(b *Argument) {
					b.FixAs[A]("h")
					inH := b.Assume()
					into := b.Have(
						"conjugation by h maps H into H",
						"∀x:A. x ∈ H ⇒ h * x * G.inv(h) ∈ H",
						By(inH, sub, group.SubgroupMul, group.SubgroupInv))
					onto := b.Have(
						"and each point x of H is the conjugate of the point G.inv(h) * x * h of H",
						"∀x:A. x ∈ H ⇒ G.inv(h) * x * h ∈ H ∧ h * (G.inv(h) * x * h) * G.inv(h) = x",
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							xIn := c.Assume()
							c.Show(
								"G.inv(h) * x * h lies in H, and h conjugates it back to x",
								SplitConj(
									Case(
										"H is closed under products and inverses",
										By(xIn, inH, sub, group.SubgroupMul, group.SubgroupInv)),
									Case(
										"the two conjugations cancel",
										Derive(func(d *Argument) {
											d.Have(
												"h and x lie in the carrier",
												"h ∈ G.carrier ∧ x ∈ G.carrier",
												BySets(xIn, inH, group.SubgroupSubset.Read(sub)))
											d.Show(
												"h cancels G.inv(h) on the left, and h * G.inv(h) is G.one on the right",
												Simp(Rev(group.AssocOn), Fwd(group.MulInvCancelLeftOn), Fwd(group.MulIn), Fwd(group.InvIn)),
												Basic(),
												Simp(Fwd(group.RightInverseOn), Fwd(group.RightIdentityOn)),
												Basic())
										})),
								))
						}))
					b.Show(
						"so the image of H under conjugation by h is H",
						Unfold(GroupConjugateDef),
						BySets(into, onto))
				}))
			contains := a.Have(
				"every element of H lies in the normalizer",
				"H ⊆ group_normalizer(G, H)",
				Simp(Fwd(GroupNormalizerDef)),
				BySets(ownConjugates, group.SubgroupSubset.Read(sub)))
			subgroupOfN := a.Have(
				"H is a subgroup of the normalizer",
				"subgroup(restrict_group(G, group_normalizer(G, H)), H)",
				By(sub, contains, group_isomorphism.SubgroupRestrict))
			conjugates := a.Have(
				"an element of the normalizer conjugates each point of H into H",
				"∀g x:A. g ∈ group_normalizer(G, H) ∧ x ∈ H ⇒ g * x * G.inv(g) ∈ H",
				Simp(Fwd(GroupNormalizerDef)),
				Unfold(GroupConjugateDef),
				BySets())
			a.Show(
				"so H is normal in its normalizer",
				Simp(Fwd(group.NormalSubgroupDef), Fwd(group.RestrictGroupDef)),
				By(conjugates, isSubgroup, subgroupOfN, contains, group.RestrictGroupDef.At(G, N)))
		}),
})}

// NormalizerIsStabilizer — the normalizer of H is its stabilizer when G acts
// on its subsets by conjugation: both are the elements of the carrier whose
// conjugation carries H onto H. No group law is read, so the record need
// not be a group.
var NormalizerIsStabilizer = normalizerIsStabilizerThm{family.Add(registry.ProofEntry{
	Name: "NormalizerIsStabilizer",
	Key:  "prop_b88eca193fca8c71",
	Build: family.Theorem("∀G:group_ops(A). ∀H:set(A). "+
		"    group_stabilizer(G, group_conjugate(G), H) = group_normalizer(G, H)",
		func(a *Argument, G *Expr[GroupOps[A]], H *Expr[Set[A]]) {
			a.Show(
				"unfolded, both are the elements of the carrier whose conjugation carries H onto H",
				Simp(Fwd(GroupStabilizerDef), Fwd(GroupNormalizerDef)),
				Refl())
		}),
})}
