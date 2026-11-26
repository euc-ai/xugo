package class_number

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ideal_norm"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_ideals"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_class_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegralIdealFromElement — a nonzero element of I gives an integral
// ideal in the inverse class whose product with I is the principal ideal of a:
// multiply the principal inclusion by the inverse, and compute multiplicative norms.
var IntegralIdealFromElement = integralIdealFromElementThm{family.Add(registry.ProofEntry{
	Name: "IntegralIdealFromElement",
	Key:  "prop_cf39a1f1840d83df",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀I:set(A). ∀a:A.",
		Hypotheses: []string{
			"number_field(L)",
			"ring_ideal(«R», I)",
			"a ∈ I",
			"a ≠ L.zero",
		},
		Conclusion: "ring_ideal(«R», «J») ∧ " +
			"«J» ≠ {L.zero} ∧ " +
			"fractional_mul(field_ring(L), «O», I, «J») = image(L.mul(a), «O») ∧ " +
			"ideal_class(field_ring(L), «O», «J») = " +
			"ideal_class(field_ring(L), «O», fractional_inverse(field_ring(L), «O», I)) ∧ " +
			"real_of_num(number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), «J»)) = " +
			"real_abs(rational_value(L, field_norm(field_ring(L), rational_image(L), a)))",
		Abbrev: Abbrev{
			{Name: "J", Text: "fractional_mul(field_ring(L), " +
				"    «O», " +
				"    image(L.mul(a), «O»), " +
				"    fractional_inverse(field_ring(L), «O», I))"},
		},
	}, func(arg *Argument, L field.FieldFact[on.L], I *Expr[Set[A]], a *Expr[A], given Fact) {
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
		O := arg.TermAs[Set[A]]("«O»")
		integerRing := arg.TermAs[RingOps[A]]("«R»")
		V, inverseDef := arg.LetAs[Set[A]]("V", "fractional_inverse(field_ring(L), «O», I)")
		P, principalDef := arg.LetAs[Set[A]]("P", "image(L.mul(a), «O»)")
		J, idealDef := arg.LetAs[Set[A]]("J", "fractional_mul(field_ring(L), «O», P, V)")
		multiplicative := comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))
		structure := arg.Have(
			"the integer ring is a subring of the number field, inside its carrier",
			"subring(field_ring(L), «O») ∧ «O» ⊆ L.carrier",
			By(
				given,
				integral_closure.IntegralClosureSubring.Read(L),
				comm_ring.SubringSubset.At(fieldRing, O)))
		carriers := arg.Have(
			"I and a lie in the integer ring and the field",
			"I ⊆ «O» ∧ I ⊆ L.carrier ∧ a ∈ «O» ∧ a ∈ L.carrier",
			BySets(given, structure, ring_ideal.IdealSubset.At(integerRing, I)))
		nonzeroI := arg.Have(
			"an ideal containing a nonzero element is not the zero ideal",
			"I ≠ {L.zero}",
			BySets(given))
		invertibleI := arg.Have(
			"every nonzero integral ideal is invertible",
			"invertible_fractional(field_ring(L), «O», I)",
			By(given, nonzeroI, number_ideals.NumberRingFactorization.Read(L).At(I)))
		cancellation := arg.Have(
			"I times its inverse is the integer ring",
			"fractional_mul(field_ring(L), «O», I, V) = «O»",
			By(
				Normalized,
				inverseDef,
				invertibleI,
				fractional_ideal.InvertibleFractionalDef.At(fieldRing, O, I)))
		inverse := arg.Have(
			"the inverse is an invertible fractional ideal in the field",
			"invertible_fractional(field_ring(L), «O», V) ∧ "+
				"submodule(«R», regular_module(field_ring(L)), V) ∧ "+
				"V ⊆ L.carrier",
			By(
				Normalized,
				inverseDef,
				structure,
				invertibleI,
				fractional_ideal.InvertibleInverse.Read(L).At(O, I),
				fractional_ideal.InvertibleFractionalDef.At(fieldRing, O, V),
				fractional_ideal.FractionalInverseSubset.Read(L).At(O, I)))
		principalInI := arg.Have(
			"I absorbs every integer multiple of a",
			"P ⊆ I ∧ P ⊆ L.carrier",
			BySets(
				comm_monoid.CommOn.Read(multiplicative),
				principalDef,
				given,
				carriers,
				structure,
				ring_ideal.IdealMul.Inst[A]().At(integerRing, I)))
		contained := arg.Have(
			"multiplying the principal inclusion by the inverse puts J in the integer ring",
			"J ⊆ «O»",
			Derive(func(b *Argument) {
				monotone := b.Have(
					"fractional multiplication preserves the principal inclusion",
					"fractional_mul(field_ring(L), «O», P, V) ⊆ fractional_mul(field_ring(L), «O», I, V)",
					By(
						principalInI,
						set_order.SubsetRefl,
						fractional_ideal.FractionalMulMono.Read(L).At(O, P, I, V, V)))
				b.Show(
					"the upper product is the integer ring",
					By(idealDef, cancellation, monotone))
			}))
		submoduleJ := arg.Have(
			"the product defining J is an integer submodule of the field",
			"submodule(«R», regular_module(field_ring(L)), J)",
			By(
				Normalized,
				idealDef,
				structure,
				principalInI,
				inverse,
				fractional_ideal.FractionalMulSubmodule.Read(L).At(O, P, V)))
		integral := arg.Have(
			"the submodule J contained in the integer ring is an integral ideal",
			"ring_ideal(«R», J)",
			By(
				contained,
				submoduleJ,
				submodule.SubmoduleZero.Read(submoduleJ),
				submodule.SubmoduleAdd.Read(submoduleJ),
				submodule.SubmoduleSmul.Read(submoduleJ),
				ring_ideal.RingIdealDef.At(integerRing, J)))
		scaled := arg.Have(
			"factoring a out of the principal ideal identifies J with a times the inverse",
			"J = image(L.mul(a), V)",
			By(
				Normalized,
				idealDef,
				principalDef,
				structure,
				carriers,
				inverse,
				fractional_ideal.FractionalMulScale.Read(L).AsFact().At(O, O, V, a),
				fractional_ideal.FractionalMulOne.Read(L).At(O, V)))
		invertibleJ := arg.Have(
			"nonzero scalar multiplication preserves invertibility",
			"invertible_fractional(field_ring(L), «O», J)",
			By(
				Normalized,
				scaled,
				structure,
				carriers,
				given,
				inverse,
				fractional_ideal.InvertibleScale.Read(L).AsFact().At(O, V, a)))
		oneInInverse := arg.Have(
			"the inverse of I contains one",
			"L.one ∈ V",
			Derive(func(b *Argument) {
				preserves := b.Have(
					"one preserves every element of I",
					"∀x:A. x ∈ I ⇒ L.mul(L.one, x) ∈ «O»",
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						inI := c.Assume()
						inField := c.Have(
							"an ideal element lies in the integer ring and the field",
							"x ∈ «O» ∧ x ∈ L.carrier",
							BySets(inI, carriers))
						c.Show(
							"multiplication by one fixes this element",
							By(Normalized, inField, comm_monoid.LeftIdentityOn.Read(multiplicative).AsFact().At(x)))
					}))
				b.Show(
					"one satisfies the defining multiplier condition for the inverse",
					BySets(
						comm_ring.OneIn.Read(field.RingOn.Read(L)),
						inverseDef,
						preserves,
						fractional_ideal.FractionalInverseDef.At(fieldRing, O, I)))
			}))
		nonzero := arg.Have(
			"a lies in J, so J is not the zero ideal",
			"a ∈ J ∧ J ≠ {L.zero}",
			Derive(func(b *Argument) {
				unitProduct := b.Have(
					"a times one is a",
					"L.mul(a, L.one) = a",
					By(carriers, comm_monoid.RightIdentityOn.Read(multiplicative)))
				aInJ := b.Have(
					"one witnesses a in the scalar image of the inverse",
					"a ∈ J",
					Simp(Fwd(scaled), Fwd(set_basic.InImage)),
					Witness(b.TermAs[A]("L.one")),
					By(oneInInverse, unitProduct))
				b.Show(
					"an ideal containing a nonzero element is not the zero ideal",
					BySets(aInJ, given))
			}))
		sameClass := arg.Have(
			"scaling the inverse by a preserves its ideal class",
			"ideal_class(field_ring(L), «O», J) = ideal_class(field_ring(L), «O», V)",
			Derive(func(b *Argument) {
				witness := b.Have(
					"a is a nonzero field scalar carrying the inverse to J",
					"∃c:A. c ∈ L.carrier ∧ c ≠ L.zero ∧ J = image(L.mul(c), V)",
					Witness(a),
					By(scaled, carriers, given))
				b.Show(
					"the scalar criterion identifies the ideal classes",
					By(
						structure,
						inverse,
						invertibleJ,
						witness,
						ideal_class_group.IdealClassEqIffScale.Read(L).At(O, J, V)))
			}))
		jInField := arg.Have(
			"the integral ideal J lies in the field",
			"J ⊆ L.carrier",
			BySets(contained, structure))
		product := arg.Have(
			"multiplication by I cancels the inverse factor in J",
			"fractional_mul(field_ring(L), «O», I, J) = P",
			CalcEq(
				Leg(
					arg.TermAs[Set[A]]("fractional_mul(field_ring(L), «O», J, I)"),
					"commute I and J",
					By(carriers, jInField, fractional_ideal.FractionalMulComm.Read(L))),
				Leg(
					arg.TermAs[Set[A]]("image(L.mul(a), fractional_mul(field_ring(L), «O», V, I))"),
					"factor out a from the scalar image",
					By(
						scaled,
						structure,
						carriers,
						inverse,
						fractional_ideal.FractionalMulScale.Read(L).AsFact().At(O, V, I, a))),
				FinalLeg(
					"commute the inverse factors and cancel to obtain the principal ideal",
					By(
						principalDef,
						cancellation,
						carriers,
						inverse,
						fractional_ideal.FractionalMulComm.Read(L).At(O, I, V)))))
		multiplicativeNorm := arg.Have(
			"the principal ideal's norm is the product of the two integral ideal norms",
			"number_ideal_norm(field_ring(L), P) = "+
				"number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), J)",
			By(
				given,
				nonzeroI,
				integral,
				nonzero,
				product,
				ideal_norm.IdealNormMultiplicative.Read(L).At(I, J)))
		normIdentity := arg.Have(
			"the principal ideal index is the absolute field norm of a",
			"real_of_num(number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), J)) = "+
				"real_abs(rational_value(L, field_norm(field_ring(L), rational_image(L), a)))",
			By(
				given,
				carriers,
				multiplicativeNorm,
				principalDef,
				ideal_norm.PrincipalIdealIndexAbsNorm.Read(L).At(a)))
		arg.Show(
			"J has the required ideal, product, class, and norm properties",
			By(integral, nonzero, product, sameClass, normIdentity))
	}),
})}

// BoundedClassRepresentative — every ideal class has a nonzero integral
// representative bounded by the class-number bound: take a small element in a
// representative of the inverse class and cancel the initial positive ideal norm.
var BoundedClassRepresentative = boundedClassRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "BoundedClassRepresentative",
	Key:  "prop_617a93153ed702bc",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e:(num → A). ∀c:set(set(A)).",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
			"c ∈ ideal_classes(field_ring(L), «O»)",
		},
		Conclusion: "∃I:set(A). " +
			"    ring_ideal(«R», I) ∧ " +
			"    I ≠ {L.zero} ∧ " +
			"    ideal_class(field_ring(L), «O», I) = c ∧ " +
			"    number_ideal_norm(field_ring(L), I) ≤ class_number_bound(field_ring(L), n, e)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		n *Expr[Nat],
		e *Arrow[Nat, A],
		c *Expr[Set[Set[A]]],
		given Fact,
	) {
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
		O := arg.TermAs[Set[A]]("«O»")
		H, principalDef := arg.LetAs[Set[Set[A]]]("H", "principal_fractional_ideals(field_ring(L), «O»)")
		G, groupDef := arg.LetAs[group.GroupOps[Set[A]]](
			"G",
			"mk_group(fractional_mul(field_ring(L), «O»), "+
				"    «O», "+
				"    fractional_inverse(field_ring(L), «O»), "+
				"    invertible_ideals(field_ring(L), «O»))")
		classGroupDef := arg.Let("Q", arg.TermAs[group.GroupOps[Set[Set[A]]]]("«ClassGroup»"))
		d, inverseClassDef := arg.LetAs[Set[Set[A]]](
			"d", "set_inv(fractional_inverse(field_ring(L), «O»), c)")
		structure := arg.Have(
			"the integer ring is a subring of the number field",
			"subring(field_ring(L), «O»)",
			By(given, integral_closure.IntegralClosureSubring.Read(L)))
		abelianIdeals := arg.Have(
			"the invertible fractional ideals form an abelian group",
			"abelian_group_on(G)",
			By(Normalized, groupDef, structure, ideal_class_group.InvertibleIdealsAbelianGroup.Read(L).At(O)))
		principalSubgroup := arg.Have(
			"the principal fractional ideals form a subgroup",
			"subgroup(G, H)",
			By(groupDef, principalDef, structure, ideal_class_group.PrincipalIdealsSubgroup.Read(L).At(O)))
		abelianClasses := arg.Have(
			"the ideal classes form an abelian group",
			"abelian_group_on(Q)",
			By(
				Normalized,
				classGroupDef,
				structure,
				ideal_class_group.InvertibleIdealClassGroupAbelian.Read(L).At(O)))
		classProjections := arg.Have(
			"the class group's carrier and inverse are the stated class operations",
			"Q.carrier = ideal_classes(field_ring(L), «O») ∧ "+
				"Q.inv = set_inv(fractional_inverse(field_ring(L), «O»))",
			Simp(
				Fwd(classGroupDef),
				Fwd(group.GroupCarrierDef.Inst[Set[Set[A]]]()),
				Fwd(group.GroupInvDef.Inst[Set[Set[A]]]())),
			Basic())
		classGroup := abelian_group.GroupOn.Read(abelianClasses)
		idealGroup := abelian_group.GroupOn.Read(abelianIdeals)
		conjugation := arg.Have(
			"conjugation fixes principal fractional ideals in the abelian ideal group",
			"∀x y:set(A). x ∈ G.carrier ∧ y ∈ H ⇒ G.mul(G.mul(x, y), G.inv(x)) ∈ H",
			Derive(func(b *Argument) {
				x := b.FixAs[Set[A]]("x")
				y := b.FixAs[Set[A]]("y")
				pair := b.Assume()
				members := b.Have(
					"both ideals and the inverse of x lie in the ideal group",
					"x ∈ G.carrier ∧ y ∈ G.carrier ∧ G.inv(x) ∈ G.carrier",
					BySets(
						pair,
						principalSubgroup,
						group.SubgroupSubset.At(G, H),
						group.InvIn.Read(idealGroup).AsFact().At(x)))
				fixed := b.Have(
					"commutativity moves x next to its inverse",
					"G.mul(G.mul(x, y), G.inv(x)) = y",
					CalcEq(
						Leg(
							b.TermAs[Set[A]]("G.mul(G.mul(y, x), G.inv(x))"),
							"commute the two ideals",
							By(Normalized, members, abelian_group.CommOn.Read(abelianIdeals).AsFact().At(x, y))),
						Leg(
							b.TermAs[Set[A]]("G.mul(y, G.mul(x, G.inv(x)))"),
							"associate x with its inverse",
							By(members, group.AssocOn.Read(idealGroup))),
						FinalLeg(
							"cancel x and its inverse, then the identity",
							By(
								Normalized,
								members,
								group.RightInverseOn.Read(idealGroup).AsFact().At(x),
								group.RightIdentityOn.Read(idealGroup).AsFact().At(y)))))
				b.Show(
					"the conjugate is the same principal ideal",
					By(Normalized, fixed, pair))
			}))
		normal := arg.Have(
			"the principal subgroup is normal",
			"normal_subgroup(G, H)",
			By(principalSubgroup, conjugation, group.NormalSubgroupDef.At(G, H)))
		inverseClass := arg.Have(
			"the inverse of c is an ideal class",
			"d ∈ ideal_classes(field_ring(L), «O»)",
			By(
				Normalized,
				classProjections,
				inverseClassDef,
				given,
				group.InvIn.Read(classGroup).AsFact().At(c)))
		fractionField := arg.Have(
			"the number field is the fraction field of its integer ring",
			"fraction_field_carrier(field_ring(L), «O»)",
			By(given, ring_of_integers.RingOfIntegersFractionField.Read(L)))
		I, representative := arg.UnpackAs[Set[A]](
			GroupPremises(
				structure,
				fractionField,
				inverseClass,
				ideal_class_group.IntegralClassRepresentative.Read(L).At(O, d)),
			"I")
		a, small := arg.UnpackAs[A](
			GroupPremises(given, representative, smallNormIdealElement.Read(L).At(n, e, I)), "a")
		V, inverseDef := arg.LetAs[Set[A]]("V", "fractional_inverse(field_ring(L), «O», I)")
		J, idealDef := arg.LetAs[Set[A]]("J", "fractional_mul(field_ring(L), «O», image(L.mul(a), «O»), V)")
		constructed := arg.Have(
			"the small element constructs a nonzero integral ideal with inverse class and exact norm",
			"ring_ideal(«R», J) ∧ "+
				"J ≠ {L.zero} ∧ "+
				"ideal_class(field_ring(L), «O», J) = ideal_class(field_ring(L), «O», V) ∧ "+
				"real_of_num(number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), J)) = "+
				"real_abs(rational_value(L, field_norm(field_ring(L), rational_image(L), a)))",
			By(inverseDef, idealDef, given, representative, small, IntegralIdealFromElement.Read(L).At(I, a)))
		iInGroup := arg.Have(
			"the chosen invertible ideal belongs to G",
			"I ∈ G.carrier",
			Simp(
				Fwd(groupDef),
				Fwd(group.GroupCarrierDef.Inst[Set[A]]()),
				Fwd(ideal_class_group.InvertibleIdealsDef.Inst[A]())),
			BySets(representative))
		idealProjections := arg.Have(
			"G uses fractional multiplication and inversion",
			"G.mul = fractional_mul(field_ring(L), «O») ∧ G.inv = fractional_inverse(field_ring(L), «O»)",
			Simp(Fwd(groupDef), Fwd(group.GroupMulDef.Inst[Set[A]]()), Fwd(group.GroupInvDef.Inst[Set[A]]())),
			Basic())
		classOfInverse := arg.Have(
			"the inverse ideal represents the inverse coset",
			"set_inv(fractional_inverse(field_ring(L), «O»), ideal_class(field_ring(L), «O», I)) = "+
				"ideal_class(field_ring(L), «O», V)",
			By(
				Normalized,
				inverseDef,
				principalDef,
				idealProjections,
				iInGroup,
				normal,
				quotient_group.LeftCosetInvOn.Read(idealGroup).AsFact().At(H, I),
				ideal_class_group.IdealClassDef.At(fieldRing, O, I),
				ideal_class_group.IdealClassDef.At(fieldRing, O, V)))
		cInGroup := arg.Have(
			"the original class belongs to Q",
			"c ∈ Q.carrier",
			By(Normalized, classProjections, given))
		inverseRepresentsC := arg.Have(
			"inverting the representative of the inverse class gives c",
			"ideal_class(field_ring(L), «O», V) = c",
			By(
				Normalized,
				classProjections,
				inverseClassDef,
				representative,
				classOfInverse,
				cInGroup,
				group.InvInvOn.Read(classGroup).AsFact().At(c)))
		classJ := arg.Have(
			"the constructed integral ideal represents c",
			"ideal_class(field_ring(L), «O», J) = c",
			By(Normalized, constructed, inverseRepresentsC))
		positive := arg.Have(
			"the initial ideal has positive norm",
			"0 < number_ideal_norm(field_ring(L), I)",
			By(given, representative, ideal_norm.IdealNormPositive.Read(L).At(I)))
		m := arg.TermAs[Nat]("number_ideal_norm(field_ring(L), I)")
		j := arg.TermAs[Nat]("number_ideal_norm(field_ring(L), J)")
		C := arg.TermAs[Nat]("class_number_bound(field_ring(L), n, e)")
		productBound := arg.Have(
			"transfer the small field-norm bound to the product of ideal norms",
			"number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), J) ≤ "+
				"class_number_bound(field_ring(L), n, e) * number_ideal_norm(field_ring(L), I)",
			ByArith(
				constructed,
				small,
				real_construction.OfNumLessEq.At(
					arg.TermAs[Nat]("number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), J)"),
					arg.TermAs[Nat]("class_number_bound(field_ring(L), n, e) * number_ideal_norm(field_ring(L), I)"))))
		commonFactor := arg.Have(
			"commute the factors on the upper bound",
			"number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), J) ≤ "+
				"number_ideal_norm(field_ring(L), I) * class_number_bound(field_ring(L), n, e)",
			By(productBound, nat_arith.MulSym.At(C, m)))
		bound := arg.Have(
			"cancel the positive norm of the initial ideal",
			"number_ideal_norm(field_ring(L), J) ≤ class_number_bound(field_ring(L), n, e)",
			ByArith(commonFactor, positive, nat_order.LessEqMulCancel.At(m, j, C)))
		arg.Show(
			"J is a nonzero integral representative of c with the required norm bound",
			Witness(J),
			By(constructed, classJ, bound))
	}),
})}

// BoundedIdealsCoverClasses — at an integral basis, the bounded nonzero
// integral ideals cover the ideal classes: every class has a bounded
// representative, so the classes are the image of a finite set, finitely
// many and at most as many as the bounded ideals.
var BoundedIdealsCoverClasses = boundedIdealsCoverClassesThm{family.Add(registry.ProofEntry{
	Name: "BoundedIdealsCoverClasses",
	Key:  "prop_a55165a8a3e3228d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e:(num → A).",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
		},
		Conclusion: "finite(ideal_classes(field_ring(L), «O»)) ∧ " +
			"card(ideal_classes(field_ring(L), «O»)) ≤ card(«BoundedIdeals»)",
	}, func(a *Argument, L field.FieldFact[on.L], n *Expr[Nat], e *Arrow[Nat, A], h Fact) {
		hypotheses := a.Conjuncts(
			h,
			"L is a number field",
			"e is an integral basis")
		numberField := hypotheses[0]
		bound := a.TermAs[Nat]("class_number_bound(field_ring(L), n, e)")
		bounded := a.TermAs[Set[Set[A]]]("«BoundedIdeals»")
		classOf := a.TermAs[Fun[Set[A], Set[Set[A]]]]("ideal_class(field_ring(L), «O»)")
		classes := a.TermAs[Set[Set[Set[A]]]]("ideal_classes(field_ring(L), «O»)")
		represented := a.TermAs[Set[Set[Set[A]]]]("image(ideal_class(field_ring(L), «O»), «BoundedIdeals»)")
		finiteBounded := a.Have(
			"there are finitely many bounded integral ideals",
			"finite(«BoundedIdeals»)",
			By(numberField, ideal_norm.BoundedNormIdealsFinite.Read(L).At(bound)))
		covered := a.Have(
			"every ideal class comes from a bounded integral ideal",
			"ideal_classes(field_ring(L), «O») ⊆ image(ideal_class(field_ring(L), «O»), «BoundedIdeals»)",
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				c := b.FixAs[Set[Set[A]]]("c")
				xInClasses := b.Assume()
				_, representative := b.UnpackAs[Set[A]](
					GroupPremises(hypotheses[1], xInClasses, BoundedClassRepresentative.Read(L).At(n, e, c)), "I")
				b.Show(
					"the representative puts c in the image",
					BySets(representative))
			}))
		finiteImage := a.Have(
			"the classes represented by bounded ideals form a finite set",
			"finite(image(ideal_class(field_ring(L), «O»), «BoundedIdeals»))",
			By(finiteBounded, finite_set.FiniteImage.At(classOf, bounded)))
		finiteClasses := a.Have(
			"the ideal classes form a finite set",
			"finite(ideal_classes(field_ring(L), «O»))",
			By(finiteImage, covered, finite_set.FiniteSubset.At(classes, represented)))
		count := a.CalcOrder(nat_order.OrderCalc(
			a.Ctx()), a.TermAs[Nat]("card(ideal_classes(field_ring(L), «O»))"),
			LeLeg(
				a.TermAs[Nat]("card(image(ideal_class(field_ring(L), «O»), «BoundedIdeals»))"),
				"the number of ideal classes is at most the size of the image",
				By(finiteImage, covered, cardinality.CardSubset.At(classes, represented))),
			LeLeg(
				a.TermAs[Nat]("card(«BoundedIdeals»)"),
				"taking ideal classes cannot increase the size of the bounded set",
				By(finiteBounded, cardinality.CardImageLe.At(classOf, bounded))))
		a.Show(
			"finiteness and the cardinality bound follow from the finite cover",
			By(finiteClasses, count))
	}),
})}

// ClassNumberFinite — the class number of a number field is finite: its ring
// of integers has an integral basis, and at that basis the bounded integral
// ideals cover the ideal classes.
var ClassNumberFinite = classNumberFiniteThm{family.Add(registry.ProofEntry{
	Name: "ClassNumberFinite",
	Key:  "prop_eb30b76b6cf2fcd3",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "finite(ideal_classes(field_ring(L), «O»))",
	}, func(a *Argument, L field.FieldFact[on.L], numberField Fact) {
		basisExists := a.Have(
			"the ring of integers has an integral basis",
			"∃n:num. ∃e:(num → A). integral_basis(field_ring(L), n, e)",
			By(numberField, ring_of_integers.IntegralBasisExists.Read(L)))
		n, e, basis := a.Unpack2As[Nat, Fun[Nat, A]](basisExists, "n", "e")
		a.Show(
			"the ideal classes are finite at the chosen integral basis",
			By(numberField, basis, BoundedIdealsCoverClasses.Read(L).At(n, e)))
	}),
})}

// ExponentProductClassInSubgroup — a subgroup of the ideal class group that
// holds the class of every factor of a finite exponent product of nonzero
// integral ideals holds the class of the product. The held ideals, integral
// and invertible with class in H, include the integer ring, whose class is the
// identity, and are closed under products, since the class map is
// multiplicative; so every power of a factor is held, and by induction on the
// support every finite exponent product.
var ExponentProductClassInSubgroup = exponentProductClassInSubgroupThm{family.Add(registry.ProofEntry{
	Name: "ExponentProductClassInSubgroup",
	Key:  "prop_1102cf1b58b8e890",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀H:set(set(set(A))). ∀v:(set(A) → num).",
		Hypotheses: []string{
			"number_field(L)",
			"subgroup(«ClassGroup», H)",
			"finite(fun_support(0, v))",
			"∀p:set(A). v(p) ≠ 0 ⇒ ring_ideal(«R», p) ∧ p ≠ {L.zero} ∧ ideal_class(field_ring(L), «O», p) ∈ H",
		},
		Conclusion: "ideal_class(field_ring(L), «O», ideal_exponent_product(«R», v)) ∈ H",
		Abbrev: Abbrev{
			{Name: "Invertibles", Text: "mk_group(fractional_mul(field_ring(L), «O»), " +
				"    «O», " +
				"    fractional_inverse(field_ring(L), «O»), " +
				"    invertible_ideals(field_ring(L), «O»))"},
			{Name: "Delete", Text: "λt:(set(A) → num). λm:set(A). λq:set(A). COND(q = m, 0, t(q))"},
			{Name: "Held", Text: "λX:set(A). " +
				"    ring_ideal(«R», X) ∧ " +
				"    invertible_fractional(field_ring(L), «O», X) ∧ " +
				"    ideal_class(field_ring(L), «O», X) ∈ H"},
			{Name: "Motive", Text: "λu:(set(A) → num). " +
				"    (∀q:set(A). " +
				"        u(q) ≠ 0 ⇒ " +
				"        ring_ideal(«R», q) ∧ q ≠ {L.zero} ∧ ideal_class(field_ring(L), «O», q) ∈ H) ⇒ " +
				"    «Held»(ideal_exponent_product(«R», u))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		H *Expr[Set[Set[Set[A]]]],
		v *Arrow[Set[A], Nat],
		numberField, subgroupH, finiteSupport, factors Fact,
	) {
		O := a.TermAs[Set[A]]("«O»")
		subring := a.Have(
			"the integer ring is a subring of the number field",
			"subring(field_ring(L), «O»)",
			By(numberField, integral_closure.IntegralClosureSubring.Read(L)))
		ring := a.Have(
			"so it is a commutative ring",
			"comm_ring_on(«R»)",
			By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(O)))
		abelian := a.Have(
			"the invertible fractional ideals form an abelian group",
			"abelian_group_on(«Invertibles»)",
			By(subring, ideal_class_group.InvertibleIdealsAbelianGroup.Read(L).At(O)))
		principal := a.Have(
			"the principal fractional ideals form a subgroup",
			"subgroup(«Invertibles», principal_fractional_ideals(field_ring(L), «O»))",
			By(subring, ideal_class_group.PrincipalIdealsSubgroup.Read(L).At(O)))
		ideals := abelian_group.GroupOn.Read(abelian)
		principalSet := a.TermAs[Set[Set[A]]]("principal_fractional_ideals(field_ring(L), «O»)")
		unitClass := a.Have(
			"the integer ring, the identity ideal, lies in the "+
				"principal subgroup, so its class is that subgroup",
			"ideal_class(field_ring(L), «O», «O») = principal_fractional_ideals(field_ring(L), «O»)",
			By(
				principal,
				group.SubgroupOne.Read(principal),
				group.OneIn.Read(ideals),
				quotient_group.LeftCosetIsSubgroupIffIn.Read(ideals).AsFact().At(O, principalSet),
				ideal_class_group.IdealClassDef))
		carrier := a.Have(
			"the integer ring, read as a ring, has the ring of integers as its carrier",
			"«R».carrier = «O»",
			Simp(Fwd(module_record.RestrictRingDef), Fwd(module_record.RingCarrierDef)),
			Basic())
		unit := a.Have(
			"the integer ring is held: integral, invertible, and its class, the identity, lies in H",
			"«Held»(«O»)",
			By(
				unitClass,
				subring,
				ring_ideal.CarrierIdeal.Read(ring),
				fractional_ideal.SubringInvertible.Read(L).At(O),
				group.SubgroupOne.Read(subgroupH)))
		closed := a.Have(
			"held ideals are closed under products",
			"∀X Y:set(A). «Held»(X) ∧ «Held»(Y) ⇒ «Held»(ideal_mul(«R», X, Y))",
			Derive(func(b *Argument) {
				X, Y := b.FixAs[Set[A]]("X"), b.FixAs[Set[A]]("Y")
				both := b.Conjuncts(
					b.Assume(),
					"X is integral",
					"X is invertible",
					"the class of X lies in H",
					"Y is integral",
					"Y is invertible",
					"the class of Y lies in H")
				integralX, invertibleX, classXInH := both[0], both[1], both[2]
				integralY, invertibleY, classYInH := both[3], both[4], both[5]
				classX := b.TermAs[Set[Set[A]]]("ideal_class(field_ring(L), «O», X)")
				classY := b.TermAs[Set[Set[A]]]("ideal_class(field_ring(L), «O», Y)")
				fractional := b.Have(
					"the product of integral ideals is their fractional product",
					"ideal_mul(«R», X, Y) = fractional_mul(field_ring(L), «O», X, Y)",
					By(subring, integralX, integralY, ideal_factorization.IntegralMulAsFractional.Read(L).At(O, X, Y)))
				b.Show(
					"the product is held",
					SplitConjAll(
						Case(
							"it is integral",
							By(
								subring,
								integralX,
								integralY,
								fractional,
								ideal_factorization.IntegralFractionalProduct.Read(L).At(O, X, Y))),
						Case(
							"it is invertible",
							By(
								subring,
								invertibleX,
								invertibleY,
								fractional,
								fractional_ideal.InvertibleProduct.Read(L).At(O, X, Y))),
						Case(
							"its class is the product of the classes of X and Y, which lies in H",
							By(
								subring,
								invertibleX,
								invertibleY,
								classXInH,
								classYInH,
								fractional,
								ideal_class_group.IdealClassMul.Read(L).At(O, X, Y),
								group.SubgroupMul.Read(subgroupH).AsFact().At(classX, classY)))))
			}))
		powers := a.Have(
			"so every power of a held ideal is held",
			"∀m:set(A). «Held»(m) ⇒ ∀k:num. «Held»(ideal_pow(«R», m, k))",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				held := b.Assume()
				k := b.FixAs[Nat]("k")
				b.Induct(k)
				b.Base(
					"the zeroth power is the integer ring",
					By(unit, carrier, ring_ideal.IdealPowZero))
				b.Step(
					"the next power is m times the previous one",
					func(c *Argument, ih Fact) {
						previous := c.TermAs[Set[A]]("ideal_pow(«R», m, k)")
						c.Show(
							"a product of two held ideals is held",
							By(held, ih, closed.At(m, previous), ring_ideal.IdealPowSuc))
					})
			}))
		products := a.Have(
			"every finite exponent product of nonzero ideals with classes in H is held",
			"∀u:(set(A) → num). finite(fun_support(0, u)) ⇒ «Motive»(u)",
			ByInduction(finite_set.FiniteInductSupport,
				Case(
					"the zero vector's product is the integer ring",
					By(unit, carrier, ideal_factorization.IdealExponentProductZero)),
				Case(
					"a nonzero coordinate m of u contributes its full power beside the rest",
					Derive(func(b *Argument) {
						u := b.FixAs[Fun[Set[A], Nat]]("u")
						m := b.FixAs[Set[A]]("m")
						previous := b.Conjuncts(
							b.Assume(),
							"the rest of u has its product held once its factors qualify",
							"u has an m factor",
							"u has finite support")
						uFactors := b.Assume()
						held := b.Have(
							"m is held: a nonzero ideal, so invertible, with class in H",
							"«Held»(m)",
							By(previous[1], numberField, uFactors.At(m), number_ideals.NumberRingFactorization.Read(L).At(m)))
						restFactors := b.Have(
							"the factors of the rest are factors of u",
							Statement{
								Binders: "∀q:set(A).",
								Hypotheses: []string{
									"«Delete»(u, m, q) ≠ 0",
								},
								Conclusion: "ring_ideal(«R», q) ∧ q ≠ {L.zero} ∧ ideal_class(field_ring(L), «O», q) ∈ H",
							},
							BySets(uFactors))
						rest := b.Have(
							"so the product of the rest is held",
							"«Held»(ideal_exponent_product(«R», «Delete»(u, m)))",
							By(restFactors, previous[0]))
						split := b.Have(
							"the full power of m splits from the product of u",
							"ideal_exponent_product(«R», u) = "+
								"ideal_mul(«R», ideal_pow(«R», m, u(m)), ideal_exponent_product(«R», «Delete»(u, m)))",
							By(previous[2], uFactors, ideal_factorization.IdealExponentProductSplit.Read(ring).At(u, m)))
						exponent := b.TermAs[Nat]("u(m)")
						power := b.TermAs[Set[A]]("ideal_pow(«R», m, u(m))")
						restProduct := b.TermAs[Set[A]]("ideal_exponent_product(«R», «Delete»(u, m))")
						b.Show(
							"the power of m and the rest are held, and so is their product",
							By(split, held, rest, powers.At(m, exponent), closed.At(power, restProduct)))
					}))))
		a.Show(
			"the motive at v, whose factors qualify",
			By(finiteSupport, factors, products.At(v)))
	}),
})}

// BoundedPrimeClassesGenerate — the nonzero prime ideals whose norm is at most
// the class-number bound are finitely many, and their classes generate the
// ideal class group: a subgroup of the class group holding every one of them
// is the whole group. They are among the finitely many bounded nonzero ideals.
// Every class has a bounded integral representative; each of its prime
// factors contains it, so has no larger norm and is one of the bounded primes,
// and the class of the product of the factors lies in any subgroup holding
// theirs.
var BoundedPrimeClassesGenerate = boundedPrimeClassesGenerateThm{family.Add(registry.ProofEntry{
	Name: "BoundedPrimeClassesGenerate",
	Key:  "prop_28af40843074630c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e:(num → A).",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
		},
		Conclusion: "finite(«BoundedPrimes») ∧ " +
			"(∀H:set(set(set(A))). " +
			"    subgroup(«ClassGroup», H) ∧ image(ideal_class(field_ring(L), «O»), «BoundedPrimes») ⊆ H ⇒ " +
			"    H = ideal_classes(field_ring(L), «O»))",
		Abbrev: Abbrev{
			{Name: "BoundedPrimes", Text: "{p:set(A) | " +
				"    prime_ideal(«R», p) ∧ " +
				"    p ≠ {L.zero} ∧ " +
				"    number_ideal_norm(field_ring(L), p) ≤ class_number_bound(field_ring(L), n, e)}"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], n *Expr[Nat], e *Arrow[Nat, A], h Fact) {
		hypotheses := a.Conjuncts(
			h,
			"L is a number field",
			"e is an integral basis")
		numberField, basis := hypotheses[0], hypotheses[1]
		O := a.TermAs[Set[A]]("«O»")
		integerRing := a.TermAs[RingOps[A]]("«R»")
		bound := a.TermAs[Nat]("class_number_bound(field_ring(L), n, e)")
		primes := a.TermAs[Set[Set[A]]]("«BoundedPrimes»")
		bounded := a.TermAs[Set[Set[A]]]("«BoundedIdeals»")
		ring := a.Have(
			"the integer ring is a commutative ring",
			"comm_ring_on(«R»)",
			By(
				numberField,
				integral_closure.IntegralClosureSubring.Read(L),
				comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(O)))
		finiteBounded := a.Have(
			"there are finitely many nonzero integral ideals of bounded norm",
			"finite(«BoundedIdeals»)",
			By(numberField, ideal_norm.BoundedNormIdealsFinite.Read(L).At(bound)))
		primesBounded := a.Have(
			"a nonzero prime of bounded norm is a nonzero ideal of bounded norm",
			"«BoundedPrimes» ⊆ «BoundedIdeals»",
			BySets(ring_ideal.PrimeIdealIdeal))
		boundedFactors := a.Have(
			"a nonzero integral ideal of bounded norm is a product of bounded primes",
			Statement{
				Binders: "∀I:set(A).",
				Hypotheses: []string{
					"ring_ideal(«R», I)",
					"I ≠ {L.zero}",
					"number_ideal_norm(field_ring(L), I) ≤ class_number_bound(field_ring(L), n, e)",
				},
				Conclusion: "∃v:(set(A) → num). " +
					"    finite(fun_support(0, v)) ∧ " +
					"    (∀p:set(A). v(p) ≠ 0 ⇒ p ∈ «BoundedPrimes») ∧ " +
					"    I = ideal_exponent_product(«R», v)",
			},
			Derive(func(b *Argument) {
				I := b.FixAs[Set[A]]("I")
				given := b.Conjuncts(
					b.Assume(),
					"I is integral",
					"I is nonzero",
					"I has norm at most the bound")
				v, factorization := b.ObtainAs[Fun[Set[A], Nat]](
					"I factors into nonzero prime ideals",
					"∃v:(set(A) → num). "+
						"    finite(fun_support(0, v)) ∧ "+
						"    (∀m:set(A). v(m) ≠ 0 ⇒ prime_ideal(«R», m) ∧ m ≠ {L.zero}) ∧ "+
						"    I = ideal_exponent_product(«R», v)",
					By(numberField, given[0], given[1], number_ideals.NumberRingFactorization.Read(L).At(I)))
				parts := b.Conjuncts(
					factorization,
					"v has finite support",
					"its factors are nonzero primes",
					"I is their product")
				primeFactors := b.Have(
					"each prime factor of I contains I, so has no larger norm, and is a bounded prime",
					"∀p:set(A). v(p) ≠ 0 ⇒ p ∈ «BoundedPrimes»",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						active := c.Assume()
						prime := c.Have(
							"p is a nonzero prime, hence an ideal",
							"ring_ideal(«R», p) ∧ prime_ideal(«R», p) ∧ p ≠ {L.zero}",
							By(active, parts[1].At(p), ring_ideal.PrimeIdealIdeal.At(integerRing, p)))
						contained := c.Have(
							"p is a factor of I, so contains it",
							"I ⊆ p",
							By(
								ring,
								parts[0],
								active,
								parts[2],
								parts[1],
								ring_ideal.PrimeIdealIdeal,
								ideal_factorization.IdealExponentProductInFactor.Read(ring).At(v, p)))
						normBound := c.Have(
							"the norm reverses containment",
							"number_ideal_norm(field_ring(L), p) ≤ number_ideal_norm(field_ring(L), I)",
							By(
								numberField,
								prime,
								given[0],
								given[1],
								contained,
								ideal_norm.IdealNormAntitone.Read(L).At(p, I)))
						withinBound := c.Have(
							"so the norm of p is within the bound",
							"number_ideal_norm(field_ring(L), p) ≤ class_number_bound(field_ring(L), n, e)",
							ByArith(normBound, given[2]))
						c.Show(
							"so p is a bounded prime",
							BySets(prime, withinBound))
					}))
				b.Show(
					"v is a factorization of I into bounded primes",
					Witness(v),
					By(parts[0], primeFactors, parts[2]))
			}))
		a.Show(
			"the bounded primes are finitely many, and their classes generate the class group",
			SplitConj(
				Case(
					"they lie among the finitely many bounded nonzero ideals",
					By(finiteBounded, primesBounded, finite_set.FiniteSubset.At(primes, bounded))),
				Case(
					"a subgroup holding their classes holds every class",
					Derive(func(b *Argument) {
						H := b.FixAs[Set[Set[Set[A]]]]("H")
						given := b.Conjuncts(
							b.Assume(),
							"H is a subgroup of the class group",
							"H holds the classes of the bounded primes")
						subgroupH, generators := given[0], given[1]
						inClasses := b.Have(
							"H lies in the class group",
							"H ⊆ ideal_classes(field_ring(L), «O»)",
							By(group.SubgroupSubset.Read(subgroupH)))
						everyClass := b.Have(
							"every ideal class lies in H",
							"∀c:set(set(A)). c ∈ ideal_classes(field_ring(L), «O») ⇒ c ∈ H",
							Derive(func(c *Argument) {
								class := c.FixAs[Set[Set[A]]]("c")
								isClass := c.Assume()
								I, representative := c.UnpackAs[Set[A]](
									GroupPremises(numberField, basis, isClass, BoundedClassRepresentative.Read(L).At(n, e, class)),
									"I")
								rep := c.Conjuncts(
									representative,
									"I is integral",
									"I is nonzero",
									"I represents c",
									"I has norm at most the bound")
								v, factorization := c.UnpackAs[Fun[Set[A], Nat]](
									GroupPremises(rep[0], rep[1], rep[3], boundedFactors.At(I)),
									"v")
								parts := c.Conjuncts(
									factorization,
									"v has finite support",
									"its factors are bounded primes",
									"I is their product")
								factorsInH := c.Have(
									"each factor is a nonzero ideal whose class, a generator, lies in H",
									"∀p:set(A). v(p) ≠ 0 ⇒ ring_ideal(«R», p) ∧ p ≠ {L.zero} ∧ ideal_class(field_ring(L), «O», p) ∈ H",
									c.ForEach(func(p *Expr[Set[A]]) Action {
										return BySets(parts[1].At(p), generators, ring_ideal.PrimeIdealIdeal.At(integerRing, p))
									}))
								c.Show(
									"c is the class of I, the exponent product of v, which lies in H",
									By(
										Normalized,
										numberField,
										subgroupH,
										parts[0],
										factorsInH,
										parts[2],
										rep[2],
										ExponentProductClassInSubgroup.Read(L).At(H, v)))
							}))
						b.Show(
							"H and the class group hold each other",
							BySets(inClasses, everyClass))
					})),
			))
	}),
})}
