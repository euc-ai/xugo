package ring_of_integers

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// NonzeroIdealFiniteIndex — a nonzero ideal has finite additive index and
// contains a positive integer whose multiples of the integer ring stay in it:
// clearing the denominator of the inverse of a nonzero element u gives a
// positive integer d = (d·u⁻¹)·u of the ideal; multiplication by d carries an
// integer basis of the integer ring to a basis of the same size of the
// principal ideal P = d·O ⊆ I, so P has finite index, and so does I.
var NonzeroIdealFiniteIndex = nonzeroIdealFiniteIndexThm{family.Add(registry.ProofEntry{
	Name: "NonzeroIdealFiniteIndex",
	Key:  "prop_d0833fb86bb74e8",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀I:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"ring_ideal(restrict_ring(field_ring(L), ring_of_integers(field_ring(L))), I)",
			"I ≠ {L.zero}",
		},
		Conclusion: "finite(left_cosets(L.add, ring_of_integers(field_ring(L)), I)) ∧ " +
			"(∃m:num. " +
			"    0 < m ∧ " +
			"    integer_map(field_ring(L), m) ∈ I ∧ " +
			"    image(L.mul(integer_map(field_ring(L), m)), ring_of_integers(field_ring(L))) ⊆ I)",
	}, func(a *Argument, L field.FieldFact[on.L], I *Expr[Set[A]], given Fact) {
		parts := a.Conjuncts(
			given,
			"L is a number field",
			"I is an ideal of the integer ring",
			"I is nonzero")
		numberField, idealI, nonzeroI := parts[0], parts[1], parts[2]
		fieldL, ringL := a.TermAs[FieldOps[A]]("L"), a.TermAs[RingOps[A]]("field_ring(L)")
		Z := a.TermAs[Set[A]]("integer_image(field_ring(L))")
		O := a.TermAs[Set[A]]("ring_of_integers(field_ring(L))")
		integerScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		integerModuleOps := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L)))")
		carrierL := a.TermAs[Set[A]]("L.carrier")
		integerRing := a.Have(
			"the integers of L form a subring containing the integer scalars",
			"subring(field_ring(L), ring_of_integers(field_ring(L))) ∧ "+
				"integer_image(field_ring(L)) ⊆ ring_of_integers(field_ring(L))",
			By(numberField, integral_closure.IntegralClosureSubring.Read(L)))
		integerParts := a.Conjuncts(
			integerRing,
			"the integers of L form a subring of L",
			"they contain the integer scalars")
		subringO, integersInO := integerParts[0], integerParts[1]
		oInL := a.Have(
			"so they lie in L",
			"ring_of_integers(field_ring(L)) ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subringO)))
		iInO := a.Have(
			"the ideal lies in the integer ring",
			"I ⊆ ring_of_integers(field_ring(L))",
			By(ring_ideal.IdealSubset.Read(idealI)))
		scalars := a.Conjuncts(
			GroupPremises(L, parts[0], number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		characteristicZero, scalarRing, integerAmbient := scalars[0], scalars[3], scalars[5]

		u, chosen := a.ObtainAs[A](
			"choose a nonzero ideal element",
			"∃u:A. u ∈ I ∧ u ≠ L.zero",
			Named("u"),
			BySets(nonzeroI, ring_ideal.IdealZero.Read(idealI)))
		uInL := a.Have(
			"the chosen ideal element lies in L",
			"u ∈ L.carrier",
			BySets(chosen, iInO, oInL))
		um := a.MemberOf[on.L](u, uInL)
		inverseInL := a.Have(
			"its inverse lies in L",
			"L.inv(u) ∈ L.carrier",
			By(field.InvIn.Read(L).At(um)))
		inverse := a.MemberOf[on.L](a.TermAs[A]("L.inv(u)"), inverseInL)
		m, clears := a.ObtainAs[Nat](
			"clear a positive integer denominator of the inverse",
			"∃m:num. 0 < m ∧ integer_map(field_ring(L), m) * L.inv(u) ∈ ring_of_integers(field_ring(L))",
			Named("m"),
			By(numberField, integral_closure.ClearDenominator.Read(L).At(inverse)))
		d, dDefinition := a.LetAs[A]("d", "integer_map(field_ring(L), m)")
		dInZ := a.Have(
			"the denominator image is an integer scalar",
			"d ∈ integer_image(field_ring(L))",
			BySets(dDefinition, characteristic_zero.IntegerImageDef.At(ringL)))
		dInL := a.Have(
			"the denominator image lies in L",
			"d ∈ L.carrier",
			BySets(dInZ, integersInO, oInL))
		dm := a.MemberOf[on.L](d, dInL)
		dInI := a.Have(
			"the integer denominator belongs to I",
			"d ∈ I",
			Derive(func(b *Argument) {
				product := b.Have(
					"the cleared inverse recovers the integer denominator",
					"(d * L.inv(u)) * u = d",
					ByArith(L, um, dm, inverse, chosen, Scaled(d, field.MulLeftInverseOn.Read(L).AsFact().At(um))))
				b.Show(
					"I absorbs the integral multiple d·u⁻¹ of its element u",
					By(
						Normalized,
						product,
						clears,
						chosen,
						ring_ideal.IdealMul.Read(idealI).AsFact().At(b.TermAs[A]("d * L.inv(u)"), u)))
			}))
		dNonzero := a.Have(
			"the denominator image is nonzero",
			"d ≠ L.zero",
			Derive(func(b *Argument) {
				integerEmbedding := b.Have(
					"the integer map is injective",
					"injective_on(𝕌, integer_map(field_ring(L)))",
					By(characteristicZero, field.RingOn.Read(L), characteristic_zero.IntegerMapInjective.At(ringL)))
				integerNonzero := b.Have(
					"the positive denominator is a nonzero integer",
					"int_of_num(m) ≠ 0",
					ByArith(clears, int_embed.OfNumEq.At(m, b.Ctx().Nat(0))))
				b.Show(
					"the injective integer map keeps the nonzero integer m away from zero",
					BySets(
						dDefinition,
						integerEmbedding,
						characteristic_zero.IntegerMapHom.Read(field.RingOn.Read(L)),
						integerNonzero,
						functions.InjectiveOnDef))
			}))

		P, pDefinition := a.LetAs[Set[A]]("P", "image(L.mul(d), ring_of_integers(field_ring(L)))")
		pInI := a.Have(
			"every integer-ring multiple of the denominator lies in I",
			"P ⊆ I",
			Derive(func(b *Argument) {
				commutes := b.Have(
					"the integer denominator commutes with every field element",
					"∀x:A. x ∈ L.carrier ⇒ d * x = x * d",
					Derive(func(c *Argument) {
						c.FixAs[A]("x")
						xInL := c.Assume()
						c.Show(
							"field multiplication is commutative",
							ByArith(L, dInL, xInL))
					}))
				b.Show(
					"I absorbs every integer-ring multiple of its element d",
					BySets(pDefinition, dInI, commutes, oInL, ring_ideal.IdealMul.Read(idealI)))
			}))
		pInO := a.Have(
			"the principal ideal lies in the integer ring",
			"P ⊆ ring_of_integers(field_ring(L))",
			BySets(pInI, iInO))
		principalIdeal := a.Have(
			"P is an ideal of the integer ring",
			"ring_ideal(restrict_ring(field_ring(L), ring_of_integers(field_ring(L))), P)",
			Derive(func(b *Argument) {
				principalModule := b.Have(
					"the principal ideal is closed under integer-ring scalars",
					"submodule(restrict_ring(field_ring(L), ring_of_integers(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    P)",
					By(
						Normalized,
						pDefinition,
						subringO,
						fractional_ideal.SubringSubmodule.Read(L).At(O),
						fractional_ideal.ScaleSubmodule.Read(L).At(O, O, dm)))
				b.Show(
					"an integer-ring submodule of L inside the integer ring is an ideal of it",
					By(subringO, principalModule, pInO, fractional_ideal.IntegralIdealFractional.Read(L).At(O, P)))
			}))

		integersInL := a.Have(
			"integer scalars lie in L",
			"integer_image(field_ring(L)) ⊆ L.carrier",
			BySets(integersInO, oInL))
		subringZ := a.Have(
			"so they form a subring of L",
			"subring(field_ring(L), integer_image(field_ring(L)))",
			By(integersInL, scalarRing, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(Z)))
		integerModuleParts := a.Conjuncts(
			GroupPremises(L, parts[0], RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is an integer-image submodule of L",
			"it is an integer-image module")
		submoduleO, integerModule := integerModuleParts[0], integerModuleParts[1]
		freeRank := a.Conjuncts(
			GroupPremises(L, parts[0], RingOfIntegersFreeRankN.At(fieldL)),
			"the integer ring is a full integer lattice",
			"it has a finite integer basis, a rational basis of L of the field degree")
		E, basis := a.UnpackAs[Set[A]](freeRank[1], "E")
		submoduleP := a.Have(
			"the principal ideal is an integer-image submodule of L",
			"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    P)",
			By(
				Normalized,
				pDefinition,
				subringZ,
				submoduleO,
				fractional_ideal.ScaleSubmodule.Read(L).At(Z, O, dm)))
		scale := a.TermAs[Fun[A, A]]("L.mul(d)")
		F := a.TermAs[Set[A]]("image(L.mul(d), E)")
		scaledBasis := a.Have(
			"the scaled basis d·E is a finite basis of P of the size of E",
			"finite(image(L.mul(d), E)) ∧ "+
				"module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), P), "+
				"    image(L.mul(d), E)) ∧ "+
				"card(image(L.mul(d), E)) = card(E)",
			Derive(func(b *Argument) {
				injective := b.Have(
					"scaling by the nonzero denominator is injective on L",
					"injective_on(L.carrier, L.mul(d))",
					By(dNonzero, field.MulBijective.Read(L).At(dm)))
				basisInL := b.Have(
					"the chosen basis lies in L",
					"E ⊆ L.carrier",
					BySets(basis, linear_independence.BasisInCarrier.At(integerScalars, integerModuleOps, E), oInL))
				ambientBasis := b.Have(
					"E is independent and spans the integer ring in the ambient module",
					"module_independent(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    E) ∧ "+
						"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    E) = "+
						"ring_of_integers(field_ring(L))",
					By(basis, submoduleO, linear_independence.BasisRestrict.Read(integerAmbient).At(O, E)))
				imageBasis := b.Have(
					"injective linear scaling transports independence and the span to P",
					"module_independent(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    image(L.mul(d), E)) ∧ "+
						"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    image(L.mul(d), E)) = "+
						"P",
					By(
						pDefinition,
						ambientBasis,
						subringZ,
						field_extension.ScaleLinear.Read(L).At(Z, dm),
						injective,
						basisInL,
						linear_independence.IndependentImage.At(integerScalars, vectors, vectors, scale, E),
						linear_independence.HomSpan.At(integerScalars, vectors, vectors, scale, E)))
				basisP := b.Have(
					"the scaled basis is a basis of P",
					"module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), P), "+
						"    image(L.mul(d), E))",
					By(imageBasis, submoduleP, linear_independence.BasisRestrict.Read(integerAmbient).At(P, F)))
				injectiveOnBasis := b.Have(
					"scaling is injective on the chosen basis",
					"injective_on(E, L.mul(d))",
					By(injective, basisInL, functions.InjectiveOnSubset.At(scale, E, carrierL)))
				sameSize := b.Have(
					"the scaled basis has the same cardinality",
					"card(image(L.mul(d), E)) = card(E)",
					By(injectiveOnBasis, basis, cardinality.CardImageInj.At(scale, E)))
				b.Show(
					"d·E is finite, a basis of P, and as large as E",
					By(basis, finite_set.FiniteImage.At(scale, E), basisP, sameSize))
			}))
		scaledParts := a.Conjuncts(
			scaledBasis,
			"the scaled basis is finite",
			"it is a basis of P",
			"it has the size of E")
		finiteF, basisP, sameSize := scaledParts[0], scaledParts[1], scaledParts[2]

		finiteNative := a.Have(
			"full rank makes the quotient by P finite",
			"finite(left_cosets(scalar_restriction(integer_map(field_ring(L)), "+
				"            restrict_module(regular_module(field_ring(L)), "+
				"                ring_of_integers(field_ring(L)))).add, "+
				"        scalar_restriction(integer_map(field_ring(L)), "+
				"            restrict_module(regular_module(field_ring(L)), "+
				"                ring_of_integers(field_ring(L)))).carrier, "+
				"        P))",
			Derive(func(b *Argument) {
				insideO := b.Have(
					"P is an integer-image submodule of the integer ring",
					"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))), "+
						"    P)",
					By(submoduleP, pInO, submodule.SubmoduleRestrict.At(integerScalars, vectors, O, P)))
				pModuleOps := b.TermAs[module_record.ModuleOps[A, A]](
					"restrict_module(regular_module(field_ring(L)), P)")
				nativeOps := b.TermAs[module_record.ModuleOps[Int, A]](
					"scalar_restriction(integer_map(field_ring(L)), " +
						"    restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))))")
				nativeData := b.Have(
					"the full-rank index criterion is stated over int itself, so pass to "+
						"the native integers, keeping the module, its basis and the submodule P",
					"module_on(int_ring, "+
						"    scalar_restriction(integer_map(field_ring(L)), "+
						"        restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))))) ∧ "+
						"module_basis(int_ring, "+
						"    scalar_restriction(integer_map(field_ring(L)), "+
						"        restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L)))), "+
						"    E) ∧ "+
						"submodule(int_ring, "+
						"    scalar_restriction(integer_map(field_ring(L)), "+
						"        restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L)))), "+
						"    P)",
					By(
						characteristicZero,
						integerModule,
						basis,
						insideO,
						field.RingOn.Read(L),
						int_lattice.IntegerScalarRestriction.At(ringL, integerModuleOps)))
				nativeRestriction := b.Have(
					"integer scalar restriction commutes with restriction to P",
					"scalar_restriction(integer_map(field_ring(L)), "+
						"    restrict_module(regular_module(field_ring(L)), P)) = "+
						"restrict_module(scalar_restriction(integer_map(field_ring(L)), "+
						"        restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L)))), "+
						"    P)",
					Simp(Fwd(module_record.ScalarRestrictionDef), Fwd(module_record.RestrictModuleDef)),
					Basic())
				nativeBasisP := b.Have(
					"the scaled basis is a native-integer basis of the restricted principal module",
					"module_basis(int_ring, "+
						"    restrict_module(scalar_restriction(integer_map(field_ring(L)), "+
						"            restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L)))), "+
						"        P), "+
						"    image(L.mul(d), E))",
					By(
						characteristicZero,
						submoduleP,
						submodule.SubmoduleModuleOn.Read(integerAmbient).At(P),
						basisP,
						nativeRestriction,
						field.RingOn.Read(L),
						int_lattice.IntegerScalarRestriction.At(ringL, pModuleOps)))
				fullRank := b.Have(
					"P has a finite native-integer basis of the full rank",
					"∃F:set(A). "+
						"    finite(F) ∧ "+
						"    module_basis(int_ring, "+
						"        restrict_module(scalar_restriction(integer_map(field_ring(L)), "+
						"                restrict_module(regular_module(field_ring(L)), "+
						"                    ring_of_integers(field_ring(L)))), "+
						"            P), "+
						"        F) ∧ "+
						"    card(F) = card(E)",
					Witness(F),
					By(finiteF, sameSize, nativeBasisP))
				b.Show(
					"a full-rank submodule of a free integer module has finite index",
					By(basis, fullRank, nativeData, int_lattice.FullRankIffFiniteIndex.At(nativeOps, E, P)))
			}))
		finiteP := a.Simplified(
			finiteNative,
			Fwd(module_record.ScalarRestrictionDef),
			Fwd(module_record.RestrictModuleDef),
			Fwd(module_record.RegularModuleDef))
		finiteI := a.Have(
			"the larger ideal also has finite quotient",
			"finite(left_cosets(L.add, ring_of_integers(field_ring(L)), I))",
			By(
				subringO,
				comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(O),
				principalIdeal,
				idealI,
				pInI,
				finiteP,
				quotient_ring.FiniteQuotientAboveIdeal.At(
					a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), ring_of_integers(field_ring(L)))"), P, I)))
		a.Show(
			"I has finite index and contains the required positive integer",
			SplitConj(
				Case(
					"the ideal quotient is finite",
					By(finiteI)),
				Case(
					"m is the required positive integer",
					Witness(m),
					By(Normalized, dDefinition, pDefinition, clears, dInI, pInI)),
			))
	}),
})}
