package ideal_norm

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/lattice_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_ideals"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// NumberIdealNormAsIdealIndex — the norm of an integral ideal is its index
// in the ring of integers read as a ring of its own: both count the cosets
// of I in ring_of_integers(R) under R's addition, which the restricted
// ring keeps.
var NumberIdealNormAsIdealIndex = numberIdealNormAsIdealIndexThm{family.Add(registry.ProofEntry{
	Name: "NumberIdealNormAsIdealIndex",
	Key:  "prop_fd6d7aa9d3ee10bd",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀I:set(A).",
		Conclusion: "number_ideal_norm(R, I) = ideal_index(restrict_ring(R, ring_of_integers(R)), I)",
	}, func(a *Argument, R *Expr[RingOps[A]], I *Expr[Set[A]]) {
		a.Show(
			"both sides count the cosets of I in the ring of integers",
			Simp(Fwd(IdealNormDef), Fwd(quotient_ring.IdealIndexDef), Fwd(module_record.RestrictRingDef)),
			Basic())
	}),
})}

// PrincipalIdealIndexAbsNorm — the index of a nonzero principal integral ideal
// is the absolute rational value of its generator's field norm. Scaling a
// ℤ-basis e of O by a gives a ℤ-basis a·e of aO, so [O : aO] is the absolute
// determinant of the change of basis from e to a·e; that matrix is the matrix
// of multiplication by a, whose determinant is the norm of a.
var PrincipalIdealIndexAbsNorm = principalIdealIndexAbsNormThm{family.Add(registry.ProofEntry{
	Name: "PrincipalIdealIndexAbsNorm",
	Key:  "prop_ff63de6ef917cabd",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀a:A.",
		Hypotheses: []string{
			"number_field(L)",
			"a ∈ «O»",
			"a ≠ L.zero",
		},
		Conclusion: "real_of_num(number_ideal_norm(field_ring(L), image(L.mul(a), «O»))) = " +
			"real_abs(rational_value(L, field_norm(field_ring(L), rational_image(L), a)))",
	}, func(arg *Argument, L field.FieldFact[on.L], a *Expr[A], given Fact) {
		fieldL := arg.TermAs[FieldOps[A]]("L")
		R := arg.TermAs[RingOps[A]]("field_ring(L)")
		O := arg.TermAs[Set[A]]("«O»")
		Z := arg.TermAs[Set[A]]("integer_image(field_ring(L))")
		Q := arg.TermAs[Set[A]]("rational_image(L)")
		fieldCarrier := arg.TermAs[Set[A]]("L.carrier")
		RZ := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		RQ := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		M := arg.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		MO := arg.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), «O»)")
		scalars := arg.Conjuncts(
			GroupPremises(L, given, number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		rationalSubfield, integersInQ, integerRing, integerAmbient :=
			scalars[1], scalars[2], scalars[3], scalars[5]
		basisExists := arg.Have(
			"the integer ring has a finite basis that is also a rational basis of the field",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), «O»), "+
				"        E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        E)",
			By(given, ring_of_integers.RingOfIntegersFreeRankN.Read(L)))
		E, basis := arg.UnpackAs[Set[A]](basisExists, "E")
		n := arg.TermAs[Nat]("card(E)")
		segment := arg.TermAs[Set[Nat]]("{k:num | k < card(E)}")
		enumerationExists := arg.Have(
			"enumerate the basis on the segment below its cardinality",
			"∃e:(num → A). "+
				"    (∀i:num. i ∈ {k:num | k < card(E)} ⇒ e(i) ∈ E) ∧ "+
				"    (∀y:A. y ∈ E ⇒ ∃i:num. i ∈ {k:num | k < card(E)} ∧ e(i) = y) ∧ "+
				"    injective_on({k:num | k < card(E)}, e)",
			By(
				basis,
				num_segment.HasSizeBelowStrict.At(n),
				cardinality.HasSizeDef.At(segment, n),
				cardinality.CardEqBijection.At(segment, E)))
		e, enumeration := arg.UnpackAs[Fun[Nat, A]](enumerationExists, "e")
		basisImage := arg.Have(
			"the enumeration has exactly the common basis as its image",
			"{e(i):A | i:num | i < card(E)} = E",
			BySets(enumeration))
		indexed := arg.Have(
			"this enumeration is an indexed integer basis of the integer ring",
			"indexed_module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    card(E), "+
				"    e)",
			By(basisImage, basis, enumeration, linear_independence.IndexedModuleBasisDef.At(RZ, MO, n, e)))
		integralBasis := arg.Have(
			"so it is an integral basis",
			"integral_basis(field_ring(L), card(E), e)",
			By(indexed, ring_of_integers.IntegralBasisDef.At(R, n, e)))
		rationalSubring := arg.Have(
			"the rational image, a subfield, is a subring of the field",
			"subring(field_ring(L), rational_image(L))",
			By(rationalSubfield, field.SubfieldSubring.Read(L).At(Q)))
		integerSubring := arg.Have(
			"the algebraic integers form a subring of the field",
			"subring(field_ring(L), «O»)",
			By(given, integral_closure.IntegralClosureSubring.Read(L)))
		integersInField := arg.Have(
			"so they lie in the field",
			"«O» ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(integerSubring)))
		basisInO := arg.Have(
			"every common basis vector is an algebraic integer",
			"E ⊆ «O»",
			By(
				basis,
				linear_independence.BasisInCarrier.At(RZ, MO, E),
				module_record.RestrictModuleDef.At(M, O)))
		inField := arg.Have(
			"a and the common basis lie in the field",
			"a ∈ L.carrier ∧ E ⊆ L.carrier",
			BySets(given, basisInO, integersInField))
		aInField := arg.Have(
			"a lies in the field",
			"a ∈ L.carrier",
			By(inField))
		am := arg.MemberOf[on.L](a, aInField)
		scale := arg.TermAs[Fun[A, A]]("L.mul(a)")
		P := arg.TermAs[Set[A]]("image(L.mul(a), «O»)")
		F := arg.TermAs[Set[A]]("image(L.mul(a), E)")
		MP := arg.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), image(L.mul(a), «O»))")
		f := arg.TermAs[Fun[Nat, A]]("λi:num. a * e(i)")
		bijective := arg.Have(
			"nonzero multiplication by a is bijective on the field",
			"injective_on(L.carrier, L.mul(a)) ∧ image(L.mul(a), L.carrier) = L.carrier",
			By(given, field.MulBijective.Read(L).At(am)))
		fullO := arg.Have(
			"the integer ring is a full integer lattice",
			"full_integer_lattice(L, «O»)",
			By(given, ring_of_integers.RingOfIntegersFreeRankN.Read(L)))
		submoduleO := arg.Conjuncts(
			GroupPremises(L, given, ring_of_integers.RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is a submodule of the field over the integer image",
			"it is a module over the integer image")[0]
		integerScalarsInField := arg.Have(
			"integer scalars lie in the field",
			"integer_image(field_ring(L)) ⊆ L.carrier",
			By(integersInQ, rationalSubfield, field.SubfieldSubset.At(fieldL, Q), set_order.SubsetTrans))
		scalarSubring := arg.Have(
			"the integer scalars, a ring inside the field, form a subring of it",
			"subring(field_ring(L), integer_image(field_ring(L)))",
			By(integerScalarsInField, integerRing, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(Z)))
		linearScaling := arg.Have(
			"multiplication by a is linear over both coefficient rings",
			"module_homomorphism(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    regular_module(field_ring(L)), "+
				"    L.mul(a)) ∧ "+
				"module_homomorphism(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    regular_module(field_ring(L)), "+
				"    L.mul(a))",
			By(
				inField,
				scalarSubring,
				rationalSubring,
				field_extension.ScaleLinear.Read(L).At(Z, am),
				field_extension.ScaleLinear.Read(L).At(Q, am)))
		principalSubmodule := arg.Have(
			"the principal ideal is an integer-image submodule",
			"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    image(L.mul(a), «O»))",
			By(inField, scalarSubring, submoduleO, fractional_ideal.ScaleSubmodule.Read(L).At(Z, O, am)))
		scaledBasis := arg.Have(
			"scaling the common integer basis gives a finite integer basis of the principal ideal",
			"module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), image(L.mul(a), «O»)), "+
				"    image(L.mul(a), E)) ∧ "+
				"finite(image(L.mul(a), E))",
			Derive(func(b *Argument) {
				ambientBasis := b.Have(
					"the original basis is independent and spans O in the ambient module",
					"module_independent(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    E) ∧ "+
						"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    E) = "+
						"«O»",
					By(basis, submoduleO, linear_independence.BasisRestrict.Read(integerAmbient).At(O, E)))
				imageBasis := b.Have(
					"injective linear scaling preserves independence and transports the span to aO",
					"module_independent(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    image(L.mul(a), E)) ∧ "+
						"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    image(L.mul(a), E)) = "+
						"image(L.mul(a), «O»)",
					By(
						ambientBasis,
						linearScaling,
						bijective,
						inField,
						linear_independence.IndependentImage.At(RZ, M, M, scale, E),
						linear_independence.HomSpan.At(RZ, M, M, scale, E),
						module_record.RegularModuleDef.At(R)))
				b.Show(
					"restrict that basis to the image carrier, whose basis image is finite",
					By(
						imageBasis,
						principalSubmodule,
						basis,
						linear_independence.BasisRestrict.Read(integerAmbient).At(P, F),
						finite_set.FiniteImage.At(scale, E)))
			}))
		fullP := arg.Have(
			"the principal ideal is a full integer lattice",
			"full_integer_lattice(L, image(L.mul(a), «O»))",
			Derive(func(b *Argument) {
				generated := b.Have(
					"the finite scaled basis generates the principal ideal",
					"module_finitely_generated(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), image(L.mul(a), «O»)))",
					Simp(Fwd(principal_ideal_domain.FinitelyGeneratedDef)),
					Witness(F),
					By(
						scaledBasis,
						linear_independence.ModuleBasisDef.At(RZ, MP, F),
						linear_independence.BasisInCarrier.At(RZ, MP, F)))
				spans := b.Have(
					"its rational span is the image of the field under bijective scaling",
					"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
						"    regular_module(field_ring(L)), "+
						"    image(L.mul(a), «O»)) = "+
						"L.carrier",
					By(
						fullO,
						linearScaling,
						integersInField,
						bijective,
						int_lattice.FullIntegerLatticeDef.At(fieldL, O),
						linear_independence.HomSpan.At(RQ, M, M, scale, O),
						module_record.RegularModuleDef.At(R)))
				b.Show(
					"finite generation and the full rational span give the full lattice",
					By(
						principalSubmodule,
						generated,
						spans,
						int_lattice.IntegerLatticeDef.At(R, P),
						int_lattice.FullIntegerLatticeDef.At(fieldL, P)))
			}))
		principalInO := arg.Have(
			"integral multiplication keeps the principal ideal inside the integer ring",
			"image(L.mul(a), «O») ⊆ «O»",
			BySets(given, integral_closure.IntegralMul.Read(L).AsFact().At(a)))
		indexedScaled := arg.Have(
			"the scaled sequence is an indexed integer basis of the principal ideal",
			"indexed_module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), image(L.mul(a), «O»)), "+
				"    card(E), "+
				"    λi:num. a * e(i))",
			Derive(func(b *Argument) {
				image := b.Have(
					"the scaled sequence enumerates the scaled basis",
					"{a * e(i):A | i:num | i < card(E)} = image(L.mul(a), E)",
					BySets(basisImage))
				injective := b.Have(
					"the scaled sequence is injective on the finite index segment",
					"injective_on({i:num | i < card(E)}, λi:num. a * e(i))",
					By(
						bijective,
						inField,
						enumeration,
						functions.InjectiveOnCompose.At(scale, e, segment, fieldCarrier),
						functions.ComposeApply.At(scale, e),
						set_basic.SubsetDef.At(E, fieldCarrier)))
				b.Show(
					"the injective sequence has the principal ideal's integer basis as its image",
					By(injective, image, scaledBasis, linear_independence.IndexedModuleBasisDef.At(RZ, MP, n, f)))
			}))
		index := arg.Have(
			"the lattice index is the absolute rational value of the basis-change determinant",
			"real_of_num(card(left_cosets(L.add, «O», image(L.mul(a), «O»)))) = "+
				"real_abs(rational_value(L, "+
				"        determinant(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"            card(E), "+
				"            basis_change_matrix(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"                restrict_module(regular_module(field_ring(L)), «O»), "+
				"                card(E), "+
				"                e, "+
				"                λi:num. a * e(i)))))",
			By(
				given,
				fullO,
				fullP,
				principalInO,
				indexed,
				indexedScaled,
				lattice_determinant.LatticeIndexEqAbsDet.Read(L).At(O, P, n, e, f)))
		matricesAgree := arg.Have(
			"the matrix of multiplication by a is the integer change of basis from e to a·e",
			"module_basis_matrix(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    card(E), "+
				"    e, "+
				"    L.mul(a)) = "+
				"basis_change_matrix(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    card(E), "+
				"    e, "+
				"    λi:num. a * e(i))",
			Funext(),
			Simp(Fwd(linear_determinant.ModuleBasisMatrixDef), Fwd(linear_determinant.BasisChangeMatrixDef)),
			Basic())
		normDeterminant := arg.Have(
			"the norm of a is the integer determinant of multiplication by a in the integral basis",
			"field_norm(field_ring(L), rational_image(L), a) = "+
				"determinant(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    card(E), "+
				"    module_basis_matrix(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), «O»), "+
				"        card(E), "+
				"        e, "+
				"        L.mul(a)))",
			By(given, integralBasis, ring_of_integers.FieldNormFromIntegralBasis.Read(L).At(n, e, a)))
		arg.Do(Simp(Fwd(IdealNormDef), Fwd(normDeterminant), Fwd(matricesAgree)))
		arg.Show(
			"the quotient index is the principal ideal norm",
			By(index))
	}),
})}

// IdealNormPositive — a nonzero integral ideal has positive norm; norm one
// characterizes the whole integer ring because its quotient has only its zero class.
var IdealNormPositive = idealNormPositiveThm{family.Add(registry.ProofEntry{
	Name: "IdealNormPositive",
	Key:  "prop_3224fb8c68ec9f36",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀I:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"ring_ideal(«R», I)",
			"I ≠ {L.zero}",
		},
		Conclusion: "0 < number_ideal_norm(field_ring(L), I) ∧ " +
			"number_ideal_norm(field_ring(L), «O») = 1 ∧ " +
			"(number_ideal_norm(field_ring(L), I) = 1 ⇔ I = «O»)",
	}, func(a *Argument, L field.FieldFact[on.L], I *Expr[Set[A]], given Fact) {
		O := a.TermAs[Set[A]]("«O»")
		cosets := a.TermAs[Set[Set[A]]]("left_cosets(L.add, «O», I)")
		count := a.TermAs[Nat]("card(left_cosets(L.add, «O», I))")
		singleI := a.TermAs[Set[Set[A]]]("{I}")

		subring := a.Have(
			"the integer ring is a subring of the field",
			"subring(field_ring(L), «O»)",
			By(given, integral_closure.IntegralClosureSubring.Read(L)))
		ring := a.Have(
			"so it is a commutative ring",
			"comm_ring_on(«R»)",
			By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(O)))
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
		subgroup := a.Have(
			"the ideal is an additive subgroup",
			"subgroup(additive_group(«R»), I)",
			By(given, quotient_ring.IdealSubgroup.Read(ring).At(I)))
		zeroClass := a.Have(
			"the ideal itself is the zero coset",
			"I ∈ left_cosets(L.add, «O», I)",
			By(subgroup, quotient_group.SubgroupInLeftCosets.Read(additive).At(I)))
		finite := a.Have(
			"the quotient by the nonzero ideal is finite",
			"finite(left_cosets(L.add, «O», I))",
			By(given, ring_of_integers.NonzeroIdealFiniteIndex.Read(L).At(I)))

		a.Do(Simp(Fwd(IdealNormDef)))
		nonempty := a.Have(
			"the zero coset makes the quotient nonempty",
			"left_cosets(L.add, «O», I) ≠ ∅",
			By(Normalized, zeroClass, set_basic.NotInEmpty.At(I)))
		positive := a.Have(
			"a finite nonempty quotient has positive cardinality",
			"0 < card(left_cosets(L.add, «O», I))",
			By(finite, nonempty, cardinality.CardEqZero.At(cosets), nat_order.PosIffNonzero.At(count)))
		wholeSubgroup := a.Have(
			"the whole integer ring is an additive subgroup",
			"subgroup(additive_group(«R»), «O»)",
			By(group.CarrierSubgroupOn.Read(additive)))
		wholeQuotient := a.Have(
			"the quotient by the whole integer ring has one coset",
			"left_cosets(L.add, «O», «O») = {«O»}",
			By(wholeSubgroup, quotient_group.QuotientTrivialIff.Read(additive).At(O)))
		wholeNorm := a.Have(
			"the whole integer ring has norm one",
			"card(left_cosets(L.add, «O», «O»)) = 1",
			Simp(Fwd(wholeQuotient), Fwd(cardinality.CardSing)),
			Basic())
		containsZero := a.Have(
			"the quotient contains the singleton of its zero coset",
			"{I} ⊆ left_cosets(L.add, «O», I)",
			By(zeroClass, set_order.SingSubset.At(cosets, I)))
		oneClass := a.Have(
			"a quotient of cardinality one consists of its zero coset",
			"card(left_cosets(L.add, «O», I)) = 1 ⇔ left_cosets(L.add, «O», I) = {I}",
			By(
				finite,
				containsZero,
				cardinality.SubsetEqIffSameCount.At(singleI, cosets),
				cardinality.CardSing.At(I)))
		a.Show(
			"positivity and the singleton quotient characterize norm one",
			By(positive, oneClass, wholeNorm, subgroup, quotient_group.QuotientTrivialIff.Read(additive).At(I)))
	}),
})}

// IdealNormMultiplicative — the norm of a product of nonzero integral ideals is
// the product of their norms: J is invertible and both quotients are finite,
// so the index of IJ in the integer ring is the product of the two indices.
var IdealNormMultiplicative = idealNormMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "IdealNormMultiplicative",
	Key:  "prop_c58212f3cd15355c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"ring_ideal(«R», I)",
			"I ≠ {L.zero}",
			"ring_ideal(«R», J)",
			"J ≠ {L.zero}",
		},
		Conclusion: "number_ideal_norm(field_ring(L), fractional_mul(field_ring(L), «O», I, J)) = " +
			"number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), J)",
	}, func(a *Argument, L field.FieldFact[on.L], I, J *Expr[Set[A]], given Fact) {
		O := a.TermAs[Set[A]]("«O»")
		subring := a.Have(
			"the integer ring is a subring of the field",
			"subring(field_ring(L), «O»)",
			By(given, integral_closure.IntegralClosureSubring.Read(L)))
		invertible := a.Have(
			"the nonzero ideal J is invertible",
			"invertible_fractional(field_ring(L), «O», J)",
			By(given, number_ideals.NumberRingFactorization.Read(L).At(J)))
		finiteQuotients := a.Have(
			"both nonzero ideals have finite quotient",
			"finite(left_cosets(L.add, «O», I)) ∧ finite(left_cosets(L.add, «O», J))",
			By(
				given,
				ring_of_integers.NonzeroIdealFiniteIndex.Read(L).At(I),
				ring_of_integers.NonzeroIdealFiniteIndex.Read(L).At(J)))
		index := a.Have(
			"the index of IJ in O is the product of the indices of I and J",
			"ideal_index(«R», fractional_mul(field_ring(L), «O», I, J)) = "+
				"ideal_index(«R», I) * ideal_index(«R», J)",
			By(
				given,
				subring,
				invertible,
				finiteQuotients,
				ideal_colength.IdealIndexMultiplicative.Read(L).At(O, I, J)))
		a.Show(
			"the norms are these indices",
			Simp(Fwd(NumberIdealNormAsIdealIndex)),
			By(index))
	}),
})}

// IdealNormAntitone — the norm reverses containment: a nonzero integral ideal
// J inside an integral ideal I has at least its norm. To contain is to divide,
// J = I·K with K the integral ideal J·I⁻¹, and the norm is multiplicative with
// N(K) positive.
var IdealNormAntitone = idealNormAntitoneThm{family.Add(registry.ProofEntry{
	Name: "IdealNormAntitone",
	Key:  "prop_152fade787fe75bb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"ring_ideal(«R», I)",
			"ring_ideal(«R», J)",
			"J ≠ {L.zero}",
			"J ⊆ I",
		},
		Conclusion: "number_ideal_norm(field_ring(L), I) ≤ number_ideal_norm(field_ring(L), J)",
		Abbrev: Abbrev{
			{Name: "K", Text: "fractional_mul(field_ring(L), " +
				"    «O», " +
				"    J, " +
				"    fractional_inverse(field_ring(L), «O», I))"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], I, J *Expr[Set[A]], given Fact) {
		parts := a.Conjuncts(
			given,
			"L is a number field",
			"I is integral",
			"J is integral",
			"J is nonzero",
			"J lies in I")
		O := a.TermAs[Set[A]]("«O»")
		K := a.TermAs[Set[A]]("«K»")
		nonzero := a.Have(
			"I holds the nonzero ideal J, so is nonzero",
			"I ≠ {L.zero}",
			BySets(parts[3], parts[2], parts[4], ring_ideal.IdealZero))
		subring := a.Have(
			"the integer ring is a subring of the field",
			"subring(field_ring(L), «O»)",
			By(parts[0], integral_closure.IntegralClosureSubring.Read(L)))
		invertible := a.Have(
			"the nonzero ideal I is invertible",
			"invertible_fractional(field_ring(L), «O», I)",
			By(parts[0], parts[1], nonzero, number_ideals.NumberRingFactorization.Read(L).At(I)))
		quotient := a.Conjuncts(
			GroupPremises(
				subring,
				parts[2],
				parts[3],
				parts[1],
				parts[4],
				invertible,
				ideal_factorization.DivideByInvertibleIdeal.Read(L).At(O, J, I)),
			"K is integral",
			"K is nonzero",
			"J is I times K",
			"J lies in K")
		normProduct := a.Have(
			"the norm of J is the norm of I times the norm of K",
			"number_ideal_norm(field_ring(L), J) = "+
				"number_ideal_norm(field_ring(L), I) * number_ideal_norm(field_ring(L), «K»)",
			By(
				parts[0],
				parts[1],
				nonzero,
				quotient[0],
				quotient[1],
				quotient[2],
				IdealNormMultiplicative.Read(L).At(I, K)))
		a.Show(
			"the positive norm of K does not shrink the product",
			ByArith(normProduct, parts[0], quotient[0], quotient[1], IdealNormPositive.Read(L).At(K)))
	}),
})}

// BoundedNormIdealsFinite — only finitely many nonzero integral ideals have
// bounded norm: they lie among the integer submodules of bounded finite index.
var BoundedNormIdealsFinite = boundedNormIdealsFiniteThm{family.Add(registry.ProofEntry{
	Name: "BoundedNormIdealsFinite",
	Key:  "prop_89bacddc09ccb76d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀B:num.",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "finite( " +
			"    {I:set(A) | ring_ideal(«R», I) ∧ I ≠ {L.zero} ∧ number_ideal_norm(field_ring(L), I) ≤ B})",
	}, func(a *Argument, L field.FieldFact[on.L], B *Expr[Nat], given Fact) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		O := a.TermAs[Set[A]]("«O»")
		regular := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		integerModule := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), «O»)")
		nativeModule := a.TermAs[module_record.ModuleOps[Int, A]](
			"scalar_restriction(integer_map(field_ring(L)), " +
				"    restrict_module(regular_module(field_ring(L)), «O»))")
		charZero := a.Have(
			"a number field has characteristic zero",
			"characteristic_zero(field_ring(L))",
			By(given, number_field.NumberFieldDef.At(fieldL)))
		basisExists := a.Have(
			"the integer ring has a finite basis over the integer image",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), «O»), "+
				"        E)",
			By(given, ring_of_integers.RingOfIntegersFreeRankN.Read(L)))
		E, basis := a.UnpackAs[Set[A]](basisExists, "E")
		imageModule := a.Conjuncts(
			GroupPremises(L, given, ring_of_integers.RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is a submodule of the field over the integer image",
			"it is a module over the integer image")[1]
		transferred := a.Have(
			"restriction to native integers preserves the module and its basis",
			"module_on(int_ring, "+
				"    scalar_restriction(integer_map(field_ring(L)), "+
				"        restrict_module(regular_module(field_ring(L)), «O»))) ∧ "+
				"module_basis(int_ring, "+
				"    scalar_restriction(integer_map(field_ring(L)), "+
				"        restrict_module(regular_module(field_ring(L)), «O»)), "+
				"    E)",
			By(
				field.RingOn.Read(L),
				charZero,
				imageModule,
				basis,
				int_lattice.IntegerScalarRestriction.At(fieldRing, integerModule)))
		bounded := a.Have(
			"the integer submodules of bounded finite index form a finite set",
			"finite({N:set(A) | "+
				"        submodule(int_ring, "+
				"            scalar_restriction(integer_map(field_ring(L)), "+
				"                restrict_module(regular_module(field_ring(L)), «O»)), "+
				"            N) ∧ "+
				"        finite(left_cosets(L.add, «O», N)) ∧ "+
				"        card(left_cosets(L.add, «O», N)) ≤ B})",
			By(
				basis,
				transferred,
				int_lattice.BoundedIndexSubmodulesFinite.At(nativeModule, E, B),
				module_record.ScalarRestrictionDef.At(
					a.TermAs[Fun[Int, A]]("integer_map(field_ring(L))"), integerModule),
				module_record.RestrictModuleDef.At(regular, O),
				module_record.RegularModuleDef.At(fieldRing)))
		idealImage := a.Have(
			"an ideal is stable under addition, negation and integer-image scalars",
			Statement{
				Binders: "∀I:set(A).",
				Hypotheses: []string{
					"ring_ideal(«R», I)",
				},
				Conclusion: "submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
					"    restrict_module(regular_module(field_ring(L)), «O»), " +
					"    I)",
			},
			Derive(func(b *Argument) {
				I := b.FixAs[Set[A]]("I")
				ideal := b.Assume()
				subring := b.Have(
					"the integer ring is a subring of the field holding the integer image",
					"subring(field_ring(L), «O») ∧ integer_image(field_ring(L)) ⊆ «O»",
					By(given, integral_closure.IntegralClosureSubring.Read(L)))
				integerRingOps := b.TermAs[RingOps[A]]("«R»")
				imageRingOps := b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
				fractional := b.Have(
					"the ideal is an integer-ring submodule of the field lying in the integer ring",
					"submodule(«R», regular_module(field_ring(L)), I) ∧ I ⊆ «O»",
					By(ideal, subring, fractional_ideal.IntegralIdealFractional.Read(L).At(O, I)))
				restricted := b.Have(
					"so it is an integer-ring submodule of the integer ring itself",
					"submodule(«R», restrict_module(regular_module(field_ring(L)), «O»), I)",
					By(fractional, submodule.SubmoduleRestrict.At(integerRingOps, regular, O, I)))
				b.Show(
					"integer-image scalars are among the integer-ring scalars",
					By(subring, submodule.SubmoduleRestrictScalars.Read(restricted).At(imageRingOps)))
			}))
		idealNative := a.Have(
			"every integral ideal is a native-integer submodule",
			Statement{
				Binders: "∀I:set(A).",
				Hypotheses: []string{
					"ring_ideal(«R», I)",
				},
				Conclusion: "submodule(int_ring, " +
					"    scalar_restriction(integer_map(field_ring(L)), " +
					"        restrict_module(regular_module(field_ring(L)), «O»)), " +
					"    I)",
			},
			By(
				field.RingOn.Read(L),
				charZero,
				idealImage,
				imageModule,
				int_lattice.IntegerScalarRestriction.At(fieldRing, integerModule)))
		contained := a.Have(
			"bounded-norm nonzero ideals lie among the bounded-index submodules",
			"{I:set(A) | ring_ideal(«R», I) ∧ I ≠ {L.zero} ∧ number_ideal_norm(field_ring(L), I) ≤ B} ⊆ "+
				"{N:set(A) | "+
				"    submodule(int_ring, "+
				"        scalar_restriction(integer_map(field_ring(L)), "+
				"            restrict_module(regular_module(field_ring(L)), «O»)), "+
				"        N) ∧ "+
				"    finite(left_cosets(L.add, «O», N)) ∧ "+
				"    card(left_cosets(L.add, «O», N)) ≤ B}",
			BySets(
				given,
				idealNative,
				ring_of_integers.NonzeroIdealFiniteIndex.Read(L),
				IdealNormDef.Inst[A]().At(fieldRing)))
		a.Show(
			"a subset of this finite family is finite",
			By(bounded, contained, finite_set.FiniteSubset))
	}),
})}
