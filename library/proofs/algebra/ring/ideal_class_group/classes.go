package ideal_class_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// IdealClassEqIffScale — two invertible ideals have the same class
// exactly when one is a nonzero scalar multiple of the other: a
// principal coset factor is aS, and multiplying by aS scales by a.
var IdealClassEqIffScale = idealClassEqIffScaleThm{family.Add(registry.ProofEntry{
	Name: "IdealClassEqIffScale",
	Key:  "prop_9bab9171f8a5d920",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I J:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, I)",
			"invertible_fractional(field_ring(L), S, J)",
		},
		Conclusion: "ideal_class(field_ring(L), S, I) = ideal_class(field_ring(L), S, J) ⇔ " +
			"∃a:A. a ∈ L.carrier ∧ a ≠ L.zero ∧ I = image(L.mul(a), J)",
	}, func(a *Argument, L field.FieldFact[on.L], S, I, J *Expr[Set[A]], hypotheses Fact) {
		parts := a.Conjuncts(
			hypotheses,
			"S is a subring of L",
			"I is invertible",
			"J is invertible")
		subring, iInv, jInv := parts[0], parts[1], parts[2]
		inField := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subring)))
		abelian := a.Have(
			"invertible ideals form an abelian group",
			"abelian_group_on(«Invertibles»)",
			By(subring, InvertibleIdealsAbelianGroup.Read(L).At(S)))
		ideals := abelian_group.GroupOn.Read(abelian)
		principal := a.Have(
			"principal ideals form a subgroup",
			"subgroup(«Invertibles», principal_fractional_ideals(field_ring(L), S))",
			By(subring, PrincipalIdealsSubgroup.Read(L).At(S)))
		members := a.Have(
			"I and J belong to the invertible ideal group",
			"I ∈ invertible_ideals(field_ring(L), S) ∧ J ∈ invertible_ideals(field_ring(L), S)",
			Unfold(InvertibleIdealsDef),
			By(iInv, jInv))
		jParts := a.Conjuncts(
			a.Unfolded(jInv, fractional_ideal.InvertibleFractionalDef),
			"J is a fractional ideal",
			"its inverse product is S")
		fractionalJ := jParts[0]
		jSubset := a.Have(
			"J lies in the field",
			"J ⊆ L.carrier",
			By(submodule.SubmoduleSubset.Read(fractionalJ)))
		principalSet := a.TermAs[Set[Set[A]]]("principal_fractional_ideals(field_ring(L), S)")
		criterion := a.Have(
			"equal ideal classes are membership in the same principal coset",
			"ideal_class(field_ring(L), S, I) = ideal_class(field_ring(L), S, J) ⇔ "+
				"I ∈ "+
				"left_coset(fractional_mul(field_ring(L), S), J, principal_fractional_ideals(field_ring(L), S))",
			Simp(Fwd(IdealClassDef)),
			By(
				group.SubgroupSubset.Read(principal),
				members,
				principal,
				group.LeftCosetEqOn.Read(ideals).AsFact().At(J, I, principalSet),
				group.InLeftCosetOn.Read(ideals).AsFact().At(J, I, principalSet)))
		unit := a.Have(
			"multiplication by S fixes J",
			"fractional_mul(field_ring(L), S, S, J) = J",
			By(subring, fractionalJ, fractional_ideal.FractionalMulOne.Read(L).At(S, J)))
		scaledProduct := a.Have(
			"multiplying J by a principal ideal is scalar multiplication",
			Statement{
				Binders: "∀a:A.",
				Hypotheses: []string{
					"a ∈ L.carrier",
				},
				Conclusion: "fractional_mul(field_ring(L), S, J, image(L.mul(a), S)) = image(L.mul(a), J)",
			},
			Derive(func(b *Argument) {
				scalar := b.FixAs[A]("a")
				aIn := b.Assume()
				aS := b.TermAs[Set[A]]("image(L.mul(a), S)")
				fractional := b.Have(
					"aS is a fractional ideal",
					"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), image(L.mul(a), S))",
					By(
						subring,
						aIn,
						fractional_ideal.ScaleSubmodule.Read(L).AsFact().At(S, S, scalar),
						fractional_ideal.SubringSubmodule.Read(L).At(S)))
				aSIn := b.Have(
					"aS lies in the field",
					"image(L.mul(a), S) ⊆ L.carrier",
					By(submodule.SubmoduleSubset.Read(fractional)))
				b.Show(
					"commute aS past J, factor out a, and remove the unit S",
					CalcEq(
						Leg(
							b.TermAs[Set[A]]("fractional_mul(field_ring(L), S, image(L.mul(a), S), J)"),
							"the fractional product commutes",
							By(jSubset, aSIn, fractional_ideal.FractionalMulComm.Read(L).At(S, J, aS))),
						Leg(
							b.TermAs[Set[A]]("image(L.mul(a), fractional_mul(field_ring(L), S, S, J))"),
							"the scalar factors out",
							By(
								subring,
								inField,
								aIn,
								jSubset,
								fractional_ideal.FractionalMulScale.Read(L).AsFact().At(S, S, J, scalar))),
						FinalLeg(
							"S is the identity on J",
							unit.Rw(),
							Basic()),
					))
			}))
		a.Iff()
		a.Forward(
			"a principal coset factor supplies the nonzero scaling scalar",
			func(b *Argument, equal Fact) {
				inCoset := b.Have(
					"I belongs to the principal coset of J",
					"I ∈ "+
						"left_coset(fractional_mul(field_ring(L), S), J, principal_fractional_ideals(field_ring(L), S))",
					By(criterion, equal))
				imageMember := b.Unfolded(inCoset, group.LeftCosetDef)
				factorExists := b.Simplified(
					imageMember,
					Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[A]](), TypeBinder.BindB[Set[A]]())))
				_, factor := b.UnpackAs[Set[A]](factorExists, "K")
				factorParts := b.Conjuncts(
					factor,
					"I is J times K",
					"K is principal")
				principalMember := b.Unfolded(factorParts[1], PrincipalFractionalIdealsDef)
				scalarExists := b.Simplified(
					principalMember,
					Fwd(set_image.SimpleImageGen),
					Fwd(set_basic.InImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Set[A]]())))
				scalar, representation := b.UnpackAs[A](scalarExists, "a")
				b.Take(scalar)
				factorIsScaled := b.Have(
					"the principal factor K is aS",
					"K = image(L.mul(a), S)",
					By(representation))
				aIn := b.Have(
					"the chosen scalar lies in L",
					"a ∈ L.carrier",
					By(representation))
				b.Show(
					"the principal factor is aS, whose product with J is aJ",
					By(aIn, representation, factorIsScaled, factorParts[0], scaledProduct.At(scalar)))
			})
		a.Backward(
			"a nonzero scalar multiple lies in the same principal coset",
			func(b *Argument, scaled Fact) {
				scalar, scaling := b.UnpackAs[A](scaled, "a")
				scalarParts := b.Conjuncts(
					scaling,
					"a lies in L",
					"a is nonzero",
					"I is aJ")
				aIn, nonzero := scalarParts[0], scalarParts[1]
				aS := b.TermAs[Set[A]]("image(L.mul(a), S)")
				toPrincipal := b.TermAs[Fun[A, Set[A]]]("λa:A. image(L.mul(a), S)")
				nonzeroScalars := b.TermAs[Set[A]]("{a:A | a ∈ L.carrier ∧ a ≠ L.zero}")
				principalScalar := b.Have(
					"aS is a principal fractional ideal",
					"image(L.mul(a), S) ∈ principal_fractional_ideals(field_ring(L), S)",
					Unfold(PrincipalFractionalIdealsDef),
					Simp(Fwd(set_image.SimpleImageGen)),
					By(aIn, nonzero, set_image.FunInImage.At(toPrincipal, nonzeroScalars, scalar)))
				product := b.Have(
					"I is J times the principal ideal aS",
					"I = fractional_mul(field_ring(L), S, J, image(L.mul(a), S))",
					By(scaling, scaledProduct.At(scalar)))
				multiplyJ := b.TermAs[Fun[Set[A], Set[A]]]("fractional_mul(field_ring(L), S, J)")
				inCoset := b.Have(
					"the principal factor aS places I in the coset of J",
					"I ∈ "+
						"left_coset(fractional_mul(field_ring(L), S), J, principal_fractional_ideals(field_ring(L), S))",
					Unfold(group.LeftCosetDef),
					product.Rw(),
					By(principalScalar, set_image.FunInImage.At(multiplyJ, principalSet, aS)))
				b.Show(
					"membership in that coset gives equality of ideal classes",
					By(inCoset, criterion))
			})
	}),
})}

// IntegralClassRepresentative — every ideal class has a nonzero integral
// invertible representative: a common denominator clears an invertible
// fractional representative without changing its class.
var IntegralClassRepresentative = integralClassRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "IntegralClassRepresentative",
	Key:  "prop_21d1d05209aff23f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀c:set(set(A)).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"c ∈ ideal_classes(field_ring(L), S)",
		},
		Conclusion: "∃I:set(A). " +
			"    ring_ideal(restrict_ring(field_ring(L), S), I) ∧ " +
			"    I ≠ {L.zero} ∧ " +
			"    invertible_fractional(field_ring(L), S, I) ∧ " +
			"    c = ideal_class(field_ring(L), S, I)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		c *Expr[Set[Set[A]]],
		hypotheses Fact,
	) {
		parts := a.Conjuncts(
			hypotheses,
			"S is a subring of L",
			"L is its fraction field",
			"c is an ideal class")
		subring, fractionField, inClasses := parts[0], parts[1], parts[2]
		inField := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subring)))
		abelian := a.Have(
			"invertible ideals form an abelian group",
			"abelian_group_on(«Invertibles»)",
			By(subring, InvertibleIdealsAbelianGroup.Read(L).At(S)))
		ideals := abelian_group.GroupOn.Read(abelian)
		principal := a.Have(
			"principal ideals form a subgroup",
			"subgroup(«Invertibles», principal_fractional_ideals(field_ring(L), S))",
			By(subring, PrincipalIdealsSubgroup.Read(L).At(S)))
		cosets := a.Unfolded(inClasses, IdealClassesDef)
		principalSet := a.TermAs[Set[Set[A]]]("principal_fractional_ideals(field_ring(L), S)")
		representatives := a.Have(
			"c is the principal coset of an invertible ideal",
			"∃J:set(A). "+
				"    c = "+
				"    left_coset(fractional_mul(field_ring(L), S), "+
				"        J, "+
				"        principal_fractional_ideals(field_ring(L), S)) ∧ "+
				"    J ∈ invertible_ideals(field_ring(L), S)",
			By(
				group.SubgroupSubset.Read(principal),
				cosets,
				quotient_group.InLeftCosets.Read(ideals).AsFact().At(principalSet, c)))
		J, representation := a.UnpackAs[Set[A]](representatives, "J")
		jParts := a.Conjuncts(
			representation,
			"c is the coset of J",
			"J belongs to the invertible ideal group")
		jInv := a.Have(
			"J is invertible",
			"invertible_fractional(field_ring(L), S, J)",
			By(a.Unfolded(jParts[1], InvertibleIdealsDef)))
		cClassJ := a.Have(
			"J represents c",
			"c = ideal_class(field_ring(L), S, J)",
			Simp(Fwd(IdealClassDef)),
			By(jParts[0]))
		jInvParts := a.Conjuncts(
			a.Unfolded(jInv, fractional_ideal.InvertibleFractionalDef),
			"J is a fractional ideal",
			"its inverse product is S")
		fractionalJ := jInvParts[0]
		jSubset := a.Have(
			"J lies in the field",
			"J ⊆ L.carrier",
			By(submodule.SubmoduleSubset.Read(fractionalJ)))
		commonDenominator := a.Have(
			"one denominator clears J",
			"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), J) ⊆ S",
			By(
				subring,
				fractionField,
				jInv,
				invertible_fractional_ideal.InvertibleCommonDenominator.Read(L).At(S, J)))
		d, clearing := a.UnpackAs[A](commonDenominator, "d")
		dParts := a.Conjuncts(
			clearing,
			"d lies in S",
			"d is nonzero",
			"dJ lies in S")
		dInS, dNonzero, contained := dParts[0], dParts[1], dParts[2]
		dInField := a.Have(
			"d lies in the field",
			"d ∈ L.carrier",
			By(dInS, inField, set_basic.SubsetDef))
		I := a.TermAs[Set[A]]("image(L.mul(d), J)")
		iInv := a.Have(
			"dJ is invertible",
			"invertible_fractional(field_ring(L), S, image(L.mul(d), J))",
			By(
				subring,
				dInField,
				dNonzero,
				jSubset,
				jInv,
				fractional_ideal.InvertibleScale.Read(L).AsFact().At(S, J, d)))
		iParts := a.Conjuncts(
			a.Unfolded(iInv, fractional_ideal.InvertibleFractionalDef),
			"dJ is a fractional ideal",
			"its inverse product is S")
		fractionalI, inverseProduct := iParts[0], iParts[1]
		integral := a.Have(
			"dJ is an integral ideal",
			"ring_ideal(restrict_ring(field_ring(L), S), image(L.mul(d), J))",
			By(subring, fractionalI, contained, fractional_ideal.IntegralIdealFractional.Read(L).At(S, I)))
		fieldModule := a.Have(
			"L is a module over S",
			"module_on(restrict_ring(field_ring(L), S), regular_module(field_ring(L)))",
			By(subring, fractional_ideal.FieldModuleOn.Read(L).At(S)))
		zeroFractional := a.Have(
			"the zero ideal is fractional",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), {L.zero})",
			By(submodule.ZeroSubmodule.Read(fieldModule)))
		oneInS := a.Have(
			"S contains one",
			"L.one ∈ S",
			By(comm_ring.SubringOne.Read(subring)))
		nonzero := a.Have(
			"the invertible ideal dJ is nonzero",
			"image(L.mul(d), J) ≠ {L.zero}",
			Derive(func(b *Argument) {
				zero := b.Have(
					"suppose dJ is the zero ideal",
					"image(L.mul(d), J) = {L.zero}",
					By(b.SupposeNot()))
				zeroProducts := b.Have(
					"then every product with its fractional inverse is zero",
					Statement{
						Binders: "∀m n:A.",
						Hypotheses: []string{
							"m ∈ image(L.mul(d), J)",
							"n ∈ fractional_inverse(field_ring(L), S, image(L.mul(d), J))",
						},
						Conclusion: "m * n ∈ {L.zero}",
					},
					BySets(
						comm_ring.MulLeftZeroOn.Read(field.RingOn.Read(L)),
						zero,
						fractional_ideal.FractionalInverseSubset.Read(L).At(S, I)))
				inverse := b.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, image(L.mul(d), J))")
				zeroSet := b.TermAs[Set[A]]("{L.zero}")
				productZero := b.Have(
					"so the whole inverse product lies in the zero ideal",
					"fractional_mul(field_ring(L), "+
						"    S, "+
						"    image(L.mul(d), J), "+
						"    fractional_inverse(field_ring(L), S, image(L.mul(d), J))) ⊆ "+
						"{L.zero}",
					By(
						zeroFractional,
						zeroProducts,
						fractional_ideal.FractionalMulLeast.Read(L).At(S, I, inverse, zeroSet)))
				b.Show(
					"the inverse product is S, contradicting one being nonzero",
					BySets(field.OneNotZeroOn.Read(L), productZero, inverseProduct, oneInS))
			}))
		scaled := a.Have(
			"dJ is a nonzero scalar multiple of J",
			"∃a:A. a ∈ L.carrier ∧ a ≠ L.zero ∧ image(L.mul(d), J) = image(L.mul(a), J)",
			Witness(d),
			By(dInField, dNonzero))
		sameClass := a.Have(
			"scaling preserves the ideal class",
			"ideal_class(field_ring(L), S, image(L.mul(d), J)) = ideal_class(field_ring(L), S, J)",
			By(subring, iInv, jInv, scaled, IdealClassEqIffScale.Read(L).At(S, I, J)))
		cClassI := a.Have(
			"dJ also represents c",
			"c = ideal_class(field_ring(L), S, image(L.mul(d), J))",
			By(cClassJ, sameClass))
		a.Show(
			"dJ is the required integral representative",
			Witness(I),
			By(integral, nonzero, iInv, cClassI))
	}),
})}
