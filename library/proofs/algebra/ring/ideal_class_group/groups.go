package ideal_class_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// InvertibleIdealsAbelianGroup — invertible fractional ideals form an
// abelian group: fractional multiplication supplies the product laws,
// and invertibility supplies the inverse equation.
var InvertibleIdealsAbelianGroup = invertibleIdealsAbelianGroupThm{family.Add(registry.ProofEntry{
	Name: "InvertibleIdealsAbelianGroup",
	Key:  "prop_26253e59a5eb713c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "abelian_group_on(«Invertibles»)",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subring Fact) {
		monoid := a.Have(
			"fractional ideals form a commutative monoid",
			"comm_monoid_on( "+
				"    {M:set(A) | submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), M)}, "+
				"    fractional_mul(field_ring(L), S), "+
				"    S)",
			By(subring, fractional_ideal.FractionalIdealsCommMonoid.Read(L).At(S)))
		fractionals := a.Have(
			"every invertible fractional ideal belongs to the fractional monoid",
			Statement{
				Binders: "∀M:set(A).",
				Hypotheses: []string{
					"invertible_fractional(field_ring(L), S, M)",
				},
				Conclusion: "submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), M)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Set[A]]("M")
				invertible := b.Assume()
				opened := b.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef)
				b.Show(
					"invertibility includes the fractional ideal condition",
					By(opened))
			}))
		a.Do(Unfold(InvertibleIdealsDef), Simp(Fwd(abelian_group.AbelianGroupOn)), SplitConj(
			Case(
				"invertible fractional ideals form a group",
				Unfold(group.GroupOn),
				SplitConjAll(
					Case(
						"S is invertible",
						By(subring, fractional_ideal.SubringInvertible.Read(L).At(S))),
					Case(
						"products of invertible ideals are invertible",
						By(subring, fractional_ideal.InvertibleProduct.Read(L).AsFact().At(S))),
					Case(
						"inverses of invertible ideals are invertible",
						By(subring, fractional_ideal.InvertibleInverse.Read(L).AsFact().At(S))),
					Case(
						"fractional multiplication associates on invertible ideals",
						By(fractionals, comm_monoid.AssocOn.Read(monoid))),
					Case(
						"S is the multiplicative identity",
						Derive(func(b *Argument) {
							x := b.FixAs[Set[A]]("x")
							member := b.Assume()
							fractional := b.Unfolded(member, fractional_ideal.InvertibleFractionalDef)
							b.Show(
								"multiplying a fractional ideal by S fixes it",
								By(fractional, comm_monoid.LeftIdentityOn.Read(monoid).AsFact().At(x)))
						})),
					Case(
						"the fractional inverse is a left inverse",
						Derive(func(b *Argument) {
							x := b.FixAs[Set[A]]("x")
							member := b.Assume()
							product := b.Unfolded(member, fractional_ideal.InvertibleFractionalDef)
							inverse := b.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, x)")
							inverseIdeal := b.Have(
								"the inverse belongs to the fractional monoid",
								"submodule(restrict_ring(field_ring(L), S), "+
									"    regular_module(field_ring(L)), "+
									"    fractional_inverse(field_ring(L), S, x))",
								By(subring, member, fractional_ideal.InvertibleInverse.Read(L).At(S, x), fractionals.At(inverse)))
							b.Show(
								"commuting the defining inverse equation gives the left inverse equation",
								CalcEq(
									Leg(
										b.TermAs[Set[A]]("fractional_mul(field_ring(L), S, x, fractional_inverse(field_ring(L), S, x))"),
										"the ideal and its inverse commute in the fractional monoid",
										By(
											member,
											fractionals.At(x),
											inverseIdeal,
											comm_monoid.CommOn.Read(monoid).AsFact().At(inverse, x))),
									FinalLeg(
										"the defining product is S",
										By(product)),
								))
						})),
				)),
			Case(
				"fractional multiplication commutes on invertible ideals",
				By(fractionals, comm_monoid.CommOn.Read(monoid))),
		))
	}),
})}

// PrincipalIdealsSubgroup — principal fractional ideals form a subgroup
// of the invertible ideals: they are the image of the homomorphism
// sending a nonzero scalar to its scalar multiple of S.
var PrincipalIdealsSubgroup = principalIdealsSubgroupThm{family.Add(registry.ProofEntry{
	Name: "PrincipalIdealsSubgroup",
	Key:  "prop_c8ffb7831fe1d50f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "subgroup(«Invertibles», principal_fractional_ideals(field_ring(L), S)) ∧ " +
			"group_homomorphism(mk_group(L.mul, L.one, L.inv, {a:A | a ∈ L.carrier ∧ a ≠ L.zero}), " +
			"    «Invertibles», " +
			"    λa:A. image(L.mul(a), S))",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subring Fact) {
		inField := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subring)))
		fieldRing := field.RingOn.Read(L)
		multiplicative := comm_ring.MulMonoidOn.Read(fieldRing)
		scalarGroup := a.Have(
			"the nonzero field scalars form a group",
			"group_on(mk_group(L.mul, L.one, L.inv, {a:A | a ∈ L.carrier ∧ a ≠ L.zero}))",
			Unfold(group.GroupOn),
			SplitConjAll(
				Case(
					"one is a nonzero scalar",
					By(comm_ring.OneIn.Read(fieldRing), field.OneNotZeroOn.Read(L))),
				Case(
					"the product of nonzero scalars is nonzero",
					BySets(comm_ring.MulIn.Read(fieldRing), field.MulEqZeroOn.Read(L))),
				Case(
					"the inverse of a nonzero scalar is nonzero",
					BySets(field.InvIn.Read(L), field.InvEqZeroOn.Read(L))),
				Case(
					"the field product associates",
					By(comm_monoid.AssocOn.Read(multiplicative))),
				Case(
					"one is a left identity",
					By(comm_monoid.LeftIdentityOn.Read(multiplicative))),
				Case(
					"field inversion supplies the left inverse",
					By(field.MulLeftInverseOn.Read(L))),
			))
		abelian := a.Have(
			"invertible fractional ideals form an abelian group",
			"abelian_group_on(«Invertibles»)",
			By(subring, InvertibleIdealsAbelianGroup.Read(L).At(S)))
		hom := a.Have(
			"nonzero scalars map multiplicatively to invertible principal ideals",
			"group_homomorphism(mk_group(L.mul, L.one, L.inv, {a:A | a ∈ L.carrier ∧ a ≠ L.zero}), "+
				"    «Invertibles», "+
				"    λa:A. image(L.mul(a), S))",
			Unfold(group_homomorphism.GroupHomomorphism),
			SplitConjAll(
				Case(
					"the source is the nonzero scalar group",
					By(scalarGroup)),
				Case(
					"invertible fractional ideals form the target group",
					By(abelian_group.GroupOn.Read(abelian))),
				Case(
					"nonzero principal ideals are invertible",
					Unfold(InvertibleIdealsDef),
					By(subring, inField, fractional_ideal.InvertibleScale.Read(L).AsFact().At(S, S))),
				Case(
					"the principal ideal of a product is the product of principal ideals",
					Derive(func(b *Argument) {
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						members := b.Assume()
						b.Show(
							"principal fractional ideals multiply as their generators",
							By(subring, members, fractional_ideal.PrincipalProduct.Read(L).AsFact().At(S, x, y)))
					})),
			))
		principalImage := a.Have(
			"principal fractional ideals are exactly the image of the scalar map",
			"principal_fractional_ideals(field_ring(L), S) = "+
				"image(λa:A. image(L.mul(a), S), {a:A | a ∈ L.carrier ∧ a ≠ L.zero})",
			Unfold(PrincipalFractionalIdealsDef),
			By(set_image.SimpleImageGen))
		a.Do(principalImage.Rw(), SplitConj(
			Case(
				"the image of the scalar homomorphism is a subgroup",
				By(group_homomorphism.ImageSubgroup.Read(hom))),
			Case(
				"the scalar map is the required homomorphism",
				By(hom)),
		))
	}),
})}

// InvertibleIdealClassGroupAbelian — invertible ideal classes form an
// abelian group: the principal subgroup is normal, and coset products
// inherit commutativity from their representatives.
var InvertibleIdealClassGroupAbelian = invertibleIdealClassGroupAbelianThm{family.Add(registry.ProofEntry{
	Name: "InvertibleIdealClassGroupAbelian",
	Key:  "prop_95f10c96956f9583",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "abelian_group_on(mk_group(set_mul(fractional_mul(field_ring(L), S)), " +
			"        principal_fractional_ideals(field_ring(L), S), " +
			"        set_inv(fractional_inverse(field_ring(L), S)), " +
			"        ideal_classes(field_ring(L), S)))",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subring Fact) {
		abelian := a.Have(
			"invertible fractional ideals form an abelian group",
			"abelian_group_on(«Invertibles»)",
			By(subring, InvertibleIdealsAbelianGroup.Read(L).At(S)))
		principal := a.Have(
			"principal fractional ideals form a subgroup",
			"subgroup(«Invertibles», principal_fractional_ideals(field_ring(L), S))",
			By(subring, PrincipalIdealsSubgroup.Read(L).At(S)))
		underlying := abelian_group.GroupOn.Read(abelian)
		principalSet := a.TermAs[Set[Set[A]]]("principal_fractional_ideals(field_ring(L), S)")
		normal := a.Have(
			"commutativity makes the principal subgroup normal",
			"normal_subgroup(«Invertibles», principal_fractional_ideals(field_ring(L), S))",
			Unfold(group.NormalSubgroupDef),
			SplitConj(
				Case(
					"principal ideals form a subgroup",
					By(principal)),
				Case(
					"conjugation fixes every principal ideal",
					Derive(func(b *Argument) {
						g, x := b.FixAs[Set[A]]("g"), b.FixAs[Set[A]]("x")
						members := b.Assume()
						xIn := b.Have(
							"a principal ideal lies in the ambient group",
							"x ∈ invertible_ideals(field_ring(L), S)",
							By(members, set_basic.SubsetDef, group.SubgroupSubset.Read(principal)))
						commuted := b.Have(
							"the conjugating ideal commutes with the principal ideal",
							"fractional_mul(field_ring(L), S, g, x) = fractional_mul(field_ring(L), S, x, g)",
							By(xIn, members, abelian_group.CommOn.Read(abelian).AsFact().At(g, x)))
						cancelled := b.Have(
							"the conjugating ideal cancels with its inverse",
							"fractional_mul(field_ring(L), "+
								"    S, "+
								"    fractional_mul(field_ring(L), S, x, g), "+
								"    fractional_inverse(field_ring(L), S, g)) = "+
								"x",
							By(xIn, members, group.MulInvCancelRightOn.Read(underlying).AsFact().At(g, x)))
						b.Show(
							"after commutation and cancellation the ideal remains principal",
							commuted.Rw(),
							cancelled.Rw(),
							By(members))
					})),
			))
		a.Have(
			"principal ideals lie among the invertible ideals",
			"principal_fractional_ideals(field_ring(L), S) ⊆ invertible_ideals(field_ring(L), S)",
			By(group.SubgroupSubset.Read(principal)))
		a.Do(Unfold(IdealClassesDef), Simp(Fwd(abelian_group.AbelianGroupOn)), SplitConj(
			Case(
				"the quotient by the principal subgroup is a group",
				By(
					normal,
					quotient_group.QuotientGroupOn.Read(underlying).At(principalSet),
					quotient_group.QuotientGroupDef.At(
						a.TermAs[group.GroupOps[Set[A]]](
							"mk_group(fractional_mul(field_ring(L), S), "+
								"    S, "+
								"    fractional_inverse(field_ring(L), S), "+
								"    invertible_ideals(field_ring(L), S))"),
						principalSet))),
			Case(
				"coset multiplication inherits commutativity",
				Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(underlying))),
				Derive(func(b *Argument) {
					I, J := b.FixAs[Set[A]]("I"), b.FixAs[Set[A]]("J")
					members := b.Assume()
					b.Show(
						"the coset of the product is unchanged when its factors commute",
						Simp(Fwd(quotient_group.LeftCosetMulOn.Read(underlying))),
						Congr(),
						By(members, abelian_group.CommOn.Read(abelian).AsFact().At(I, J)))
				})),
		))
	}),
})}

// IdealClassMul — the class of a product of invertible ideals is the product
// of their classes: the principal ideals form a normal subgroup of the abelian
// group of invertible ideals, so the cosets of two ideals multiply to the coset
// of their product.
var IdealClassMul = idealClassMulThm{family.Add(registry.ProofEntry{
	Name: "IdealClassMul",
	Key:  "prop_dbbd45d82e5eb4d2",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I J:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, I)",
			"invertible_fractional(field_ring(L), S, J)",
		},
		Conclusion: "ideal_class(field_ring(L), S, fractional_mul(field_ring(L), S, I, J)) = " +
			"set_mul(fractional_mul(field_ring(L), S), " +
			"    ideal_class(field_ring(L), S, I), " +
			"    ideal_class(field_ring(L), S, J))",
	}, func(a *Argument, L field.FieldFact[on.L], S, I, J *Expr[Set[A]], hypotheses Fact) {
		parts := a.Conjuncts(
			hypotheses,
			"S is a subring of L",
			"I is invertible",
			"J is invertible")
		subring := parts[0]
		abelian := a.Have(
			"invertible fractional ideals form an abelian group",
			"abelian_group_on(«Invertibles»)",
			By(subring, InvertibleIdealsAbelianGroup.Read(L).At(S)))
		principal := a.Have(
			"principal fractional ideals form a subgroup",
			"subgroup(«Invertibles», principal_fractional_ideals(field_ring(L), S))",
			By(subring, PrincipalIdealsSubgroup.Read(L).At(S)))
		ideals := abelian_group.GroupOn.Read(abelian)
		normal := a.Have(
			"commutativity makes the principal subgroup normal",
			"normal_subgroup(«Invertibles», principal_fractional_ideals(field_ring(L), S))",
			Unfold(group.NormalSubgroupDef),
			SplitConj(
				Case(
					"principal ideals form a subgroup",
					By(principal)),
				Case(
					"conjugation fixes every principal ideal",
					Derive(func(b *Argument) {
						g, x := b.FixAs[Set[A]]("g"), b.FixAs[Set[A]]("x")
						members := b.Assume()
						b.Show(
							"g commutes past the principal ideal x and cancels against its inverse",
							By(
								members,
								principal,
								set_basic.SubsetDef,
								group.SubgroupSubset.Read(principal),
								abelian_group.CommOn.Read(abelian).AsFact().At(g, x),
								group.MulInvCancelRightOn.Read(ideals).AsFact().At(g, x)))
					})),
			))
		members := a.Have(
			"I and J belong to the invertible ideal group",
			"I ∈ invertible_ideals(field_ring(L), S) ∧ J ∈ invertible_ideals(field_ring(L), S)",
			BySets(parts[1], parts[2], InvertibleIdealsDef))
		principalSet := a.TermAs[Set[Set[A]]]("principal_fractional_ideals(field_ring(L), S)")
		a.Show(
			"the principal cosets of I and J multiply to the coset of their product",
			By(
				normal,
				members,
				quotient_group.LeftCosetMulOn.Read(ideals).AsFact().At(principalSet, I, J),
				IdealClassDef))
	}),
})}
