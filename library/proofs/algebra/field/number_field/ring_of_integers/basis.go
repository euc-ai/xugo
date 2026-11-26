package ring_of_integers

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/trace_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FinitelyGeneratedFieldSubmoduleFree — an integer lattice in a number
// field has a finite integer basis of size at most the field degree.
// The integer image is a principal ideal domain, field cancellation
// gives torsion-freeness, and the rational span bounds the basis size.
var FinitelyGeneratedFieldSubmoduleFree = finitelyGeneratedFieldSubmoduleFreeThm{family.Add(registry.ProofEntry{
	Name: "FinitelyGeneratedFieldSubmoduleFree",
	Key:  "prop_50310d73bcd825e4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"integer_lattice(field_ring(L), M)",
		},
		Conclusion: "∃E:set(A). " +
			"    finite(E) ∧ " +
			"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
			"        restrict_module(regular_module(field_ring(L)), M), " +
			"        E) ∧ " +
			"    card(E) ≤ extension_degree(L, rational_image(L), L.carrier)",
	}, func(a *Argument, L field.FieldFact[on.L], M *Expr[Set[A]], h Fact) {
		R := a.TermAs[RingOps[A]]("field_ring(L)")
		rationals := a.TermAs[Set[A]]("rational_image(L)")
		integerRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		latticeModule := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), M)")
		fieldL := a.TermAs[FieldOps[A]]("L")
		numberField := a.Have(
			"L is a number field",
			"number_field(L)",
			By(h))
		scalars := a.Conjuncts(
			GroupPremises(L, numberField, number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		charZero, rationalSubfield, integersInRationals, pid :=
			scalars[0], scalars[1], scalars[2], scalars[4]
		integerModule, rationalModule := scalars[5], scalars[6]
		finiteDimension := a.Have(
			"its rational dimension is finite",
			"finite_dimensional(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)))",
			By(h, number_field.NumberFieldDef.At(fieldL)))
		lattice := a.Have(
			"the lattice is a finitely generated integer submodule",
			"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    M) ∧ "+
				"module_finitely_generated(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), M))",
			By(h, int_lattice.IntegerLatticeDef.At(R, M)))
		latticeFacts := a.Conjuncts(
			lattice,
			"M is an integer submodule",
			"M is finitely generated over the integers")
		scalarsInField := a.Have(
			"both scalar images lie in the ambient field",
			"rational_image(L) ⊆ L.carrier ∧ integer_image(field_ring(L)) ⊆ L.carrier",
			BySets(rationalSubfield, integersInRationals, field.SubfieldSubset.At(fieldL, rationals)))
		scalarFacts := a.Conjuncts(
			scalarsInField,
			"the rational image lies in the field",
			"the integer image lies in the field")
		latticeInField := a.Have(
			"the lattice lies in the field",
			"M ⊆ L.carrier",
			By(submodule.SubmoduleSubset.Read(latticeFacts[0])))
		restrictedModule := a.Have(
			"the lattice inherits its integer module structure",
			"module_on(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), M))",
			By(latticeFacts[0], submodule.SubmoduleModuleOn.Read(integerModule).At(M)))
		torsionFree := a.Have(
			"a nonzero integer scalar kills no nonzero lattice vector",
			"module_torsion_free(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), M))",
			Unfold(principal_ideal_domain.TorsionFreeDef),
			Derive(func(b *Argument) {
				c := b.FixAs[A]("c")
				v := b.FixAs[A]("v")
				annihilates := b.Assume()
				inField := b.Have(
					"the scalar and vector lie in the host field",
					"c ∈ L.carrier ∧ v ∈ L.carrier",
					BySets(annihilates, latticeInField, scalarFacts[1]))
				b.Show(
					"field cancellation forces the vector to vanish",
					By(inField, annihilates, field.MulEqZeroOn.Read(L).AsFact().At(c, v)))
			}))
		E, integerBasis := a.ObtainAs[Set[A]](
			"choose a finite basis over the integer principal ideal domain",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), M), "+
				"        E)",
			By(
				pid,
				latticeFacts[1],
				restrictedModule,
				torsionFree,
				principal_ideal_domain.FiniteTorsionFreeFree.At(integerRing, latticeModule)))

		N, span := a.LetAs[Set[A]](
			"N",
			"module_span(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), M)")
		spanSubmodule := a.Have(
			"the rational span of the lattice is a rational submodule",
			"submodule(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), N)",
			By(Normalized, span, latticeInField, submodule.SpanSubmodule.Read(rationalModule).At(M)))
		rank := a.Have(
			"the integer basis size is the rational span dimension",
			"module_dim(restrict_ring(field_ring(L), rational_image(L)), "+
				"    restrict_module(regular_module(field_ring(L)), N)) = "+
				"card(E)",
			By(
				Normalized,
				span,
				charZero,
				integerBasis,
				h,
				int_lattice.IntegerBasisRationalSpan.Read(L).At(M, E)))
		inverse := a.TermAs[Fun[A, A]]("L.inv")
		rationalOperations := a.Have(
			"the rational image is a field under L's own operations, with L's inverse",
			"ring_subfield(restrict_ring(field_ring(L), rational_image(L)), L.inv, rational_image(L))",
			By(rationalSubfield, field.SubfieldRingSubfield.Read(L).At(rationals, rationals)))
		bound := a.Have(
			"a rational submodule has dimension at most the ambient number field",
			"module_dim(restrict_ring(field_ring(L), rational_image(L)), "+
				"    restrict_module(regular_module(field_ring(L)), N)) ≤ "+
				"module_dim(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)))",
			By(
				rationalOperations,
				finiteDimension,
				spanSubmodule,
				module_dimension.SubmoduleDim.Read(rationalModule).At(inverse, N)))
		degree := a.Have(
			"the full rational module dimension is the field degree",
			"extension_degree(L, rational_image(L), L.carrier) = "+
				"module_dim(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)))",
			Simp(
				Fwd(field_extension.ExtensionDegreeDef),
				Fwd(module_record.RegularModuleDef),
				Fwd(module_record.RestrictModuleDef)),
			Basic())
		a.Take(E)
		a.Show(
			"the finite integer basis has size bounded by the field degree",
			By(bound, rank, degree, integerBasis))
	}),
})}

// IntegralRationalBasisExists — clearing one common denominator of a finite
// rational basis gives a rational basis consisting of integers of the field.
var IntegralRationalBasisExists = integralRationalBasisExistsThm{family.Add(registry.ProofEntry{
	Name: "IntegralRationalBasisExists",
	Key:  "prop_97790625d423b961",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "∃E:set(A). " +
			"    finite(E) ∧ " +
			"    module_basis(restrict_ring(field_ring(L), rational_image(L)), " +
			"        regular_module(field_ring(L)), " +
			"        E) ∧ " +
			"    E ⊆ ring_of_integers(field_ring(L))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		clearFinite := ctx.Lemma(Statement{
			Binders:    "∀L:field_on(A).",
			Hypotheses: []string{"number_field(L)"},
			Conclusion: "∀S:set(A). " +
				"    finite(S) ⇒ " +
				"    S ⊆ L.carrier ⇒ " +
				"    ∃d:num. " +
				"        0 < d ∧ " +
				"        (∀x:A. x ∈ S ⇒ integer_map(field_ring(L), d) * x ∈ ring_of_integers(field_ring(L)))",
		}, func(a *Argument, L field.FieldFact[on.L], numberField Fact) {
			a.Do(ByInduction(finite_set.FiniteInduct,
				Case(
					"the empty set needs no denominator",
					Derive(func(b *Argument) {
						b.Assume()
						b.Take(ctx.Nat(1))
						b.Show(
							"one clears the empty set",
							By(set_basic.NotInEmpty))
					})),
				Case(
					"multiply the denominator by one clearing the added element",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						b.FixAs[Set[A]]("S")
						induction := b.Assume()
						inField := b.Assume()
						oldAndNewInField := b.Have(
							"the old set and the added element lie in L",
							"S ⊆ L.carrier ∧ x ∈ L.carrier",
							By(inField, set_order.InsertSubset))
						xm := b.MemberOf[on.L](x, b.Conjuncts(
							oldAndNewInField,
							"the old set lies in L",
							"the added element lies in L")[1])
						d, old := b.ObtainAs[Nat](
							"choose a denominator for the old set",
							"∃d:num. "+
								"    0 < d ∧ (∀y:A. y ∈ S ⇒ integer_map(field_ring(L), d) * y ∈ ring_of_integers(field_ring(L)))",
							By(oldAndNewInField, induction))
						e, added := b.ObtainAs[Nat](
							"choose a denominator for the added element",
							"∃e:num. 0 < e ∧ integer_map(field_ring(L), e) * x ∈ ring_of_integers(field_ring(L))",
							By(numberField, integral_closure.ClearDenominator.Read(L).At(xm)))
						oldParts := b.Conjuncts(
							old,
							"d is positive",
							"d clears the old set")
						integers := b.Have(
							"integer images are integral",
							"∀z:int. integer_map(field_ring(L), z) ∈ ring_of_integers(field_ring(L))",
							BySets(
								numberField,
								integral_closure.IntegersAreIntegral.Read(L),
								characteristic_zero.IntegerImageDef))
						mapLaws := b.Simplified(characteristic_zero.IntegerMapHom.Read(field.RingOn.Read(L)))
						product := b.Have(
							"the image of the product is the product of the images",
							"integer_map(field_ring(L), int_of_num(d * e)) = "+
								"integer_map(field_ring(L), d) * integer_map(field_ring(L), e)",
							Simp(Fwd(int_embed.OfNumMul)),
							By(mapLaws))
						scalarsInField := b.Have(
							"both denominator images lie in L",
							"integer_map(field_ring(L), d) ∈ L.carrier ∧ integer_map(field_ring(L), e) ∈ L.carrier",
							BySets(mapLaws))
						atAdded := b.Have(
							"the product denominator clears the added element",
							"integer_map(field_ring(L), int_of_num(d * e)) * x ∈ ring_of_integers(field_ring(L))",
							Derive(func(c *Argument) {
								regroup := c.Have(
									"apply d to the integral multiple supplied by e",
									"integer_map(field_ring(L), int_of_num(d * e)) * x = "+
										"integer_map(field_ring(L), d) * (integer_map(field_ring(L), e) * x)",
									Simp(Fwd(product)),
									ByArith(L, scalarsInField, oldAndNewInField))
								c.Show(
									"multiplying by the integer image of d preserves integrality",
									By(
										numberField,
										integers.At(c.TermAs[Int]("d")),
										added,
										regroup,
										integral_closure.IntegralMul.Read(L).At(
											c.TermAs[A]("integer_map(field_ring(L), d)"), c.TermAs[A]("integer_map(field_ring(L), e) * x"))))
							}))
						atOld := b.Have(
							"the product denominator still clears every old element",
							"∀y:A. y ∈ S ⇒ integer_map(field_ring(L), int_of_num(d * e)) * y ∈ ring_of_integers(field_ring(L))",
							Derive(func(c *Argument) {
								y := c.FixAs[A]()
								yInS := c.Assume()
								yInField := c.Have(
									"the old element lies in L",
									"y ∈ L.carrier",
									BySets(yInS, oldAndNewInField))
								regroup := c.Have(
									"apply e to the integral multiple supplied by d",
									"integer_map(field_ring(L), int_of_num(d * e)) * y = "+
										"integer_map(field_ring(L), e) * (integer_map(field_ring(L), d) * y)",
									Simp(Fwd(product)),
									ByArith(L, scalarsInField, yInField))
								c.Show(
									"multiplying by the integer image of e preserves integrality",
									By(
										numberField,
										yInS,
										integers.At(c.TermAs[Int]("e")),
										oldParts[1].At(y),
										regroup,
										integral_closure.IntegralMul.Read(L).At(
											c.TermAs[A]("integer_map(field_ring(L), e)"), c.TermAs[A]("integer_map(field_ring(L), d) * y"))))
							}))
						positive := b.Have(
							"the product denominator is positive",
							"0 < d * e",
							ByArith(oldParts[0], added, nat_order.LessThanMulCancel.At(d, ctx.Nat(0), e)))
						clears := b.Have(
							"the product clears the enlarged set",
							Statement{
								Binders: "∀y:A.",
								Hypotheses: []string{
									"y ∈ insert(x, S)",
								},
								Conclusion: "integer_map(field_ring(L), int_of_num(d * e)) * y ∈ ring_of_integers(field_ring(L))",
							},
							BySets(atOld, atAdded))
						b.Take(b.TermAs[Nat]("d * e"))
						b.Show(
							"the enlarged set has a common positive denominator",
							By(positive, clears))
					}))))
		})
		return ctx.Theorem(headline, func(a *Argument, L field.FieldFact[on.L], numberField Fact) {
			fieldL := a.TermAs[FieldOps[A]]("L")
			rationalScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
			fieldModule := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			fieldData := a.Unfolded(numberField, number_field.NumberFieldDef)
			E0, finiteBasis := a.ObtainAs[Set[A]](
				"choose a finite rational basis",
				"∃E₀:set(A). "+
					"    finite(E₀) ∧ "+
					"    module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
					"        regular_module(field_ring(L)), "+
					"        E₀)",
				By(fieldData, module_dimension.FiniteDimensionalDef.At(rationalScalars, fieldModule)))
			basisData := a.Conjuncts(
				finiteBasis,
				"E₀ is finite",
				"E₀ is a rational basis")
			inField := a.Have(
				"the rational basis lies in L",
				"E₀ ⊆ L.carrier",
				By(linear_independence.BasisInCarrier.Read(basisData[1])))
			d, clears := a.ObtainAs[Nat](
				"clear a common positive denominator of the basis",
				"∃d:num. "+
					"    0 < d ∧ (∀x:A. x ∈ E₀ ⇒ integer_map(field_ring(L), d) * x ∈ ring_of_integers(field_ring(L)))",
				By(L, numberField, basisData[0], inField, At(clearFinite, fieldL, E0)))
			scalars := a.Conjuncts(
				GroupPremises(L, numberField, number_field.NumberFieldScalars.At(fieldL)),
				"L has characteristic zero",
				"its rational image is a subfield",
				"the integer image lies in the rational image",
				"the integer image is a commutative ring",
				"and a principal ideal domain",
				"L is a module over the integer image",
				"and over the rational image")
			characteristicZero, rationalSubfield := scalars[0], scalars[1]
			mapLaws := a.Simplified(characteristic_zero.IntegerMapHom.Read(field.RingOn.Read(L)))
			denominator := a.TermAs[A]("integer_map(field_ring(L), d)")
			denominatorInL := a.Have(
				"the denominator image lies in L",
				"integer_map(field_ring(L), d) ∈ L.carrier",
				BySets(mapLaws))
			integerEmbedding := a.Have(
				"the integer map is injective",
				"injective_on(𝕌, integer_map(field_ring(L)))",
				By(
					characteristicZero,
					field.RingOn.Read(L),
					characteristic_zero.IntegerMapInjective.At(a.TermAs[RingOps[A]]("field_ring(L)"))))
			integerNonzero := a.Have(
				"the positive denominator is a nonzero integer",
				"int_of_num(d) ≠ 0",
				ByArith(clears, int_embed.OfNumEq.At(d, ctx.Nat(0))))
			denominatorNonzero := a.Have(
				"the denominator image is nonzero",
				"integer_map(field_ring(L), d) ≠ L.zero",
				BySets(integerNonzero, integerEmbedding, mapLaws, functions.InjectiveOnDef))
			denominatorMember := a.MemberOf[on.L](denominator, denominatorInL)
			linear := a.Have(
				"scaling by the denominator is rational linear",
				"module_homomorphism(restrict_ring(field_ring(L), rational_image(L)), "+
					"    regular_module(field_ring(L)), "+
					"    regular_module(field_ring(L)), "+
					"    L.mul(integer_map(field_ring(L), d)))",
				By(
					rationalSubfield,
					field_extension.MultiplicationLinear.Read(L).At(
						a.TermAs[Set[A]]("rational_image(L)"), denominatorMember)))
			bijective := a.Have(
				"scaling by the nonzero denominator is bijective on L",
				"injective_on(L.carrier, L.mul(integer_map(field_ring(L), d))) ∧ "+
					"image(L.mul(integer_map(field_ring(L), d)), L.carrier) = L.carrier",
				By(denominatorNonzero, field.MulBijective.Read(L).At(denominatorMember)))
			originalBasis := a.Unfolded(basisData[1], linear_independence.ModuleBasisDef)
			scale := a.TermAs[Fun[A, A]]("L.mul(integer_map(field_ring(L), d))")
			E := a.TermAs[Set[A]]("image(L.mul(integer_map(field_ring(L), d)), E₀)")
			independent := a.Have(
				"injective scaling preserves independence",
				"module_independent(restrict_ring(field_ring(L), rational_image(L)), "+
					"    regular_module(field_ring(L)), "+
					"    image(L.mul(integer_map(field_ring(L), d)), E₀))",
				By(
					originalBasis,
					linear,
					bijective,
					linear_independence.IndependentImage.At(rationalScalars, fieldModule, fieldModule, scale, E0)))
			spans := a.Have(
				"surjective scaling preserves the spanning property",
				"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
					"    regular_module(field_ring(L)), "+
					"    image(L.mul(integer_map(field_ring(L), d)), E₀)) = "+
					"L.carrier",
				By(
					linear,
					inField,
					originalBasis,
					bijective,
					linear_independence.HomSpan.At(rationalScalars, fieldModule, fieldModule, scale, E0)))
			basis := a.Have(
				"the scaled set is a rational basis",
				"module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
					"    regular_module(field_ring(L)), "+
					"    image(L.mul(integer_map(field_ring(L), d)), E₀))",
				By(independent, spans, linear_independence.ModuleBasisDef.At(rationalScalars, fieldModule, E)))
			integral := a.Have(
				"every scaled basis element is integral",
				"image(L.mul(integer_map(field_ring(L), d)), E₀) ⊆ ring_of_integers(field_ring(L))",
				BySets(clears))
			a.Take(E)
			a.Show(
				"the finite scaled basis consists of integers of L",
				By(basisData[0], finite_set.FiniteImage.At(scale, E0), basis, integral))
		})
	}),
})}

// RingOfIntegersFractionField — a number field is the fraction field of its
// ring of integers: a positive integer d clears the denominator of each
// element z, so d·z is an algebraic integer, d is one too and is nonzero in
// characteristic zero, and z is the quotient of d·z by d.
var RingOfIntegersFractionField = ringOfIntegersFractionFieldThm{family.Add(registry.ProofEntry{
	Name: "RingOfIntegersFractionField",
	Key:  "prop_9f409544bb0ebb9d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "fraction_field_carrier(field_ring(L), ring_of_integers(field_ring(L)))",
	}, func(a *Argument, L field.FieldFact[on.L], numberField Fact) {
		ringL := a.TermAs[RingOps[A]]("field_ring(L)")
		integersInL := a.Have(
			"the algebraic integers of L lie in L",
			"ring_of_integers(field_ring(L)) ⊆ L.carrier",
			BySets(integral_closure.RingOfIntegersDef))
		characteristicZero := a.Have(
			"L has characteristic zero",
			"characteristic_zero(field_ring(L))",
			By(numberField, number_field.NumberFieldDef))
		sumsOfOneNonzero := a.Unfolded(characteristicZero, comm_ring.CharacteristicZeroDef)
		a.Show(
			"L is the fraction field of its algebraic integers",
			Simp(Fwd(field.FractionFieldCarrierDef)),
			SplitConj(
				Case(
					"the algebraic integers lie in L",
					By(integersInL)),
				Case(
					"each z in L is d·z over the positive integer d clearing its denominator",
					Derive(func(a *Argument) {
						z := a.FixAs[A]("z")
						zm := a.MemberOf[on.L](z, a.Assume())
						m, clears := a.ObtainAs[Nat](
							"clear a positive integer denominator of z",
							"∃m:num. 0 < m ∧ integer_map(field_ring(L), m) * z ∈ ring_of_integers(field_ring(L))",
							Named("m"),
							By(numberField, integral_closure.ClearDenominator.Read(L).At(zm)))
						d, dDefinition := a.LetAs[A]("d", "integer_map(field_ring(L), m)")
						dInO := a.Have(
							"the integer d is an algebraic integer",
							"d ∈ ring_of_integers(field_ring(L))",
							BySets(
								dDefinition,
								characteristic_zero.IntegerImageDef.At(ringL),
								numberField,
								integral_closure.IntegersAreIntegral.Read(L)))
						dInL := a.Have(
							"so d lies in L",
							"d ∈ L.carrier",
							BySets(dInO, integersInL))
						dSum := a.Have(
							"the nonnegative integer m maps to the m-fold sum of one",
							"d = monoid_pow(L.add, L.zero, L.one, m)",
							By(
								Normalized,
								dDefinition,
								characteristic_zero.IntegerMapDef.At(ringL, a.TermAs[Int]("m")),
								int_embed.EmbedNonneg.At(m),
								int_embed.OfNumRetract.At(m)))
						dNonzero := a.Have(
							"a positive sum of ones is nonzero in characteristic zero",
							"d ≠ L.zero",
							By(Normalized, dSum, clears, sumsOfOneNonzero.At(m)))
						commutes := a.Have(
							"z and d commute",
							"z * d = d * z",
							ByArith(L, zm, dInL))
						a.Take(a.TermAs[A]("d * z"))
						a.Take(d)
						a.Show(
							"z is the quotient of the algebraic integers d·z and d",
							By(clears, dInO, dNonzero, commutes))
					})),
			))
	}),
})}

// TraceDualFull — the trace dual of a full integer lattice is a full
// integer lattice, and taking its trace dual again recovers the original one:
// an integer basis of the lattice is a rational basis of the field, and the
// trace pairing is nondegenerate in characteristic zero, so that basis has a
// trace-dual basis, an integer basis of the trace dual and a rational basis
// of the field; the trace dual is therefore finitely generated and spans the
// field.
var TraceDualFull = traceDualFullThm{family.Add(registry.ProofEntry{
	Name: "TraceDualFull",
	Key:  "prop_af62ec504505dd0c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"full_integer_lattice(L, M)",
		},
		Conclusion: "full_integer_lattice(L, «D») ∧ " +
			"trace_dual(L, rational_image(L), «D», integer_image(field_ring(L))) = M",
		Abbrev: Abbrev{
			{Name: "D", Text: "trace_dual(L, rational_image(L), M, integer_image(field_ring(L)))"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], M *Expr[Set[A]], given Fact) {
		parts := a.Conjuncts(
			given,
			"L is a number field",
			"M is a full integer lattice")
		numberField, fullM := parts[0], parts[1]
		lattice := a.Conjuncts(
			a.Unfolded(fullM, int_lattice.FullIntegerLatticeDef),
			"M is an integer lattice",
			"M spans L over the rationals")
		integerM := lattice[0]
		numberData := a.Unfolded(numberField, number_field.NumberFieldDef)
		fieldL := a.TermAs[FieldOps[A]]("L")
		ringL := a.TermAs[RingOps[A]]("field_ring(L)")
		Q := a.TermAs[Set[A]]("rational_image(L)")
		Z := a.TermAs[Set[A]]("integer_image(field_ring(L))")
		D := a.TermAs[Set[A]]("«D»")
		rationalScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		carrierL := a.TermAs[Set[A]]("L.carrier")
		scalars := a.Conjuncts(
			GroupPremises(L, parts[0], number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		characteristicZero, subQ, integersInQ := scalars[0], scalars[1], scalars[2]
		moduleZ, moduleQ := scalars[5], scalars[6]
		carrier := a.Have(
			"the regular module has the field carrier",
			"regular_module(field_ring(L)).carrier = L.carrier",
			Simp(Fwd(module_record.RegularModuleDef), Fwd(field.FieldRingDef)),
			Basic())
		restrictL := a.Have(
			"restriction to the full field carrier preserves the regular module",
			"restrict_module(regular_module(field_ring(L)), L.carrier) = regular_module(field_ring(L))",
			Simp(Rev(carrier), Fwd(module_record.RestrictModuleCarrier)),
			Basic())

		E, free := a.ObtainAs[Set[A]](
			"choose a finite integer basis of M",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), M), "+
				"        E) ∧ "+
				"    card(E) ≤ extension_degree(L, rational_image(L), L.carrier)",
			Named("E"),
			By(numberField, integerM, FinitelyGeneratedFieldSubmoduleFree.Read(L).At(M)))
		freeParts := a.Conjuncts(
			free,
			"E is finite",
			"E is an integer basis of M",
			"its size is bounded by the field degree")
		rationalBasis := a.Conjuncts(
			GroupPremises(
				scalars[0],
				parts[1],
				freeParts[0],
				freeParts[1],
				int_lattice.FullLatticeBasisRational.Read(L).At(M, E)),
			"the full integer basis is also a rational basis of L",
			"on M its rational coordinates are its integer ones")[0]
		integerData := a.Unfolded(integerM, int_lattice.IntegerLatticeDef)
		spanE := a.Have(
			"the ambient integer span of E is M",
			"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    E) = "+
				"M",
			By(free, integerData, linear_independence.BasisRestrict.Read(moduleZ).At(M, E)))
		nondegenerate := a.Have(
			"the characteristic-zero trace pairing is nondegenerate",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ L.carrier",
					"x ≠ L.zero",
				},
				Conclusion: "∃y:A. y ∈ L.carrier ∧ field_trace(L, rational_image(L), x * y) ≠ L.zero",
			},
			Derive(func(b *Argument) {
				finiteExtension := b.Have(
					"L is a finite extension of its rational image",
					"finite_extension(L, rational_image(L), L.carrier)",
					By(Normalized, numberData, restrictL, field_extension.FiniteExtensionDef.At(fieldL, Q, carrierL)))
				b.Show(
					"a finite extension in characteristic zero has a nondegenerate trace pairing",
					By(characteristicZero, subQ, finiteExtension, field_trace.CharZeroTraceNondegenerate.Read(L).At(Q)))
			}))

		d, dual := a.ObtainAs[Fun[A, A]](
			"choose the trace-dual basis and its span identity",
			"∃d:(A → A). "+
				"    (∀e:A. e ∈ E ⇒ d(e) ∈ L.carrier) ∧ "+
				"    (∀e f:A. "+
				"        e ∈ E ∧ f ∈ E ⇒ "+
				"        field_trace(L, rational_image(L), d(e) * f) = COND(e = f, L.one, L.zero)) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        image(d, E)) ∧ "+
				"    «D» = "+
				"    module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        regular_module(field_ring(L)), "+
				"        image(d, E)) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), «D»), "+
				"        image(d, E)) ∧ "+
				"    trace_dual(L, rational_image(L), «D», integer_image(field_ring(L))) = M",
			Named("d"),
			By(
				subQ,
				integersInQ,
				characteristicZero,
				int_lattice.IntegerRationalImagesStructure.Read(L),
				rationalBasis,
				spanE,
				freeParts[0],
				nondegenerate,
				trace_dual.TraceDualFreeLattice.Read(L).At(Q, Z, E)))
		dualParts := a.Conjuncts(
			dual,
			"d takes E into L",
			"d is trace dual to E",
			"d(E) is a rational basis of L",
			"the trace dual is the integer span of d(E)",
			"d(E) is an integer basis of the trace dual",
			"the trace bidual is M")
		dualRationalBasis, dualSpanIdentity, dualIntegerBasis, bidual :=
			dualParts[2], dualParts[3], dualParts[4], dualParts[5]
		dualSet := a.TermAs[Set[A]]("image(d, E)")
		dualInD := a.Have(
			"the dual basis lies in the trace dual",
			"image(d, E) ⊆ «D»",
			By(linear_independence.BasisInCarrier.Read(dualIntegerBasis)))
		submoduleD := a.Have(
			"the trace dual is an integer submodule",
			"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    «D»)",
			By(
				linear_independence.BasisInCarrier.Read(dualRationalBasis),
				dualSpanIdentity,
				submodule.SpanSubmodule.Read(moduleZ).At(dualSet)))

		integerD := a.Have(
			"the trace dual is an integer lattice",
			"integer_lattice(field_ring(L), «D»)",
			Derive(func(b *Argument) {
				integerBasisData := b.Unfolded(dualIntegerBasis, linear_independence.ModuleBasisDef)
				finiteGeneration := b.Have(
					"the finite dual basis generates the trace dual over the integers",
					"module_finitely_generated(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), «D»))",
					Simp(Fwd(principal_ideal_domain.FinitelyGeneratedDef)),
					Derive(func(c *Argument) {
						c.Take(dualSet)
						c.Show(
							"take the finite integer dual basis as generators",
							By(freeParts[0], finite_set.FiniteImage.At(d, E), dualInD, integerBasisData))
					}))
				b.Show(
					"a finitely generated integer submodule is an integer lattice",
					By(finiteGeneration, submoduleD, int_lattice.IntegerLatticeDef.At(ringL, D)))
			}))
		fullDualSpan := a.Have(
			"the rational span of the trace dual is L",
			"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    «D») = "+
				"L.carrier",
			Derive(func(b *Argument) {
				rationalBasisData := b.Unfolded(dualRationalBasis, linear_independence.ModuleBasisDef)
				rationalSpan := b.TermAs[Set[A]](
					"module_span(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), «D»)")
				spanContainsL := b.Have(
					"the dual basis spans L and lies in the trace dual, "+
						"so the rational span of the trace dual contains L",
					"L.carrier ⊆ "+
						"module_span(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), «D»)",
					By(rationalBasisData, dualInD, submodule.SpanMono.At(rationalScalars, vectors, dualSet, D)))
				spanInL := b.Have(
					"the rational span of the trace dual lies in L",
					"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
						"    regular_module(field_ring(L)), "+
						"    «D») ⊆ "+
						"L.carrier",
					By(
						submodule.SubmoduleSubset.Read(submoduleD),
						submodule.CarrierSubmodule.Read(moduleQ),
						submodule.SpanLeast.At(rationalScalars, vectors, D, carrierL)))
				b.Show(
					"the two inclusions give equality",
					By(spanContainsL, spanInL, set_order.SubsetAntisym.At(rationalSpan, carrierL)))
			}))
		fullD := a.Have(
			"the trace dual is full",
			"full_integer_lattice(L, «D»)",
			By(integerD, fullDualSpan, int_lattice.FullIntegerLatticeDef.At(fieldL, D)))
		a.Show(
			"the trace dual is full and its bidual is the original lattice",
			By(fullD, bidual))
	}),
})}

// RingOfIntegersIntegerModule — the ring of integers of a number field is a
// submodule of the field over the integer image, and so a module over the
// integer image in its own right: as a subring it is a submodule over its own
// scalars, which include the integer image, and restricting the scalars keeps
// a submodule; the field is a module over its integer image, and the submodule
// inherits that structure.
var RingOfIntegersIntegerModule = ringOfIntegersIntegerModuleThm{family.Add(registry.ProofEntry{
	Name: "RingOfIntegersIntegerModule",
	Key:  "prop_da116c8eb69c0d72",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "submodule(«ℤ», regular_module(field_ring(L)), «O») ∧ " +
			"module_on(«ℤ», restrict_module(regular_module(field_ring(L)), «O»))",
	}, func(a *Argument, L field.FieldFact[on.L], numberField Fact) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		O := a.TermAs[Set[A]]("«O»")
		integerScalars := a.TermAs[RingOps[A]]("«ℤ»")
		subring := a.Have(
			"the integers of L form a subring of L containing the integer image",
			"subring(field_ring(L), «O») ∧ integer_image(field_ring(L)) ⊆ «O»",
			By(numberField, integral_closure.IntegralClosureSubring.Read(L)))
		selfModule := a.Have(
			"as a subring, the integer ring is a submodule of L over its own scalars",
			"submodule(«R», regular_module(field_ring(L)), «O»)",
			By(subring, fractional_ideal.SubringSubmodule.Read(L).At(O)))
		fewerScalars := a.Have(
			"the integer scalars are among those scalars",
			"«ℤ».carrier ⊆ «R».carrier",
			BySets(subring))
		integerSubmodule := a.Have(
			"restricting the scalars to the integer image keeps a submodule",
			"submodule(«ℤ», regular_module(field_ring(L)), «O»)",
			By(fewerScalars, submodule.SubmoduleRestrictScalars.Read(selfModule).At(integerScalars)))
		scalars := a.Conjuncts(
			GroupPremises(L, numberField, number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		ambient := scalars[5]
		a.Show(
			"the integer submodule inherits the module structure of L",
			By(integerSubmodule, submodule.SubmoduleModuleOn.Read(ambient).At(O)))
	}),
})}

// RingOfIntegersInTraceDual — the integer span of any set of integers of a
// number field lies in the integer ring, and the integer ring lies in that
// span's trace dual: the integers form a submodule containing the set, and
// the product of two integers is an integer, whose trace is an integer.
var RingOfIntegersInTraceDual = ringOfIntegersInTraceDualThm{family.Add(registry.ProofEntry{
	Name: "RingOfIntegersInTraceDual",
	Key:  "prop_b8d1f1e032d267ea",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀E:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"E ⊆ ring_of_integers(field_ring(L))",
		},
		Conclusion: "module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
			"    regular_module(field_ring(L)), " +
			"    E) ⊆ " +
			"ring_of_integers(field_ring(L)) ∧ " +
			"ring_of_integers(field_ring(L)) ⊆ " +
			"trace_dual(L, " +
			"    rational_image(L), " +
			"    module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
			"        regular_module(field_ring(L)), " +
			"        E), " +
			"    integer_image(field_ring(L)))",
	}, func(a *Argument, L field.FieldFact[on.L], E *Expr[Set[A]], hypotheses Fact) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		O := a.TermAs[Set[A]]("ring_of_integers(field_ring(L))")
		integerScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		fieldModule := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		integerRing := a.Have(
			"the integers of L form a subring containing the integer scalars",
			"subring(field_ring(L), ring_of_integers(field_ring(L))) ∧ "+
				"integer_image(field_ring(L)) ⊆ ring_of_integers(field_ring(L))",
			By(L, hypotheses, integral_closure.IntegralClosureSubring.At(fieldL)))
		subringO := a.Conjuncts(
			integerRing,
			"the integers of L form a subring of L",
			"they contain the integer scalars")[0]
		integerModule := a.Conjuncts(
			GroupPremises(L, hypotheses, RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is an integer submodule of L",
			"it is an integer module")[0]
		spanInIntegers := a.Have(
			"the integer span of E lies in the integer ring",
			"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    E) ⊆ "+
				"ring_of_integers(field_ring(L))",
			By(integerModule, hypotheses, submodule.SpanLeast.At(integerScalars, fieldModule, E, O)))
		integralPairing := a.Have(
			"every integer pairs integrally with the integer span",
			Statement{
				Binders: "∀x b:A.",
				Hypotheses: []string{
					"x ∈ ring_of_integers(field_ring(L))",
					"b ∈ " +
						"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
						"    regular_module(field_ring(L)), " +
						"    E)",
				},
				Conclusion: "field_trace(L, rational_image(L), x * b) ∈ integer_image(field_ring(L))",
			},
			Derive(func(c *Argument) {
				x := c.FixAs[A]()
				b := c.FixAs[A]()
				inPair := c.Assume()
				bIntegral := c.Have(
					"the span element is an integer of L",
					"b ∈ ring_of_integers(field_ring(L))",
					BySets(spanInIntegers, inPair))
				productIntegral := c.Have(
					"the product of the two integers remains integral",
					"x * b ∈ ring_of_integers(field_ring(L))",
					By(bIntegral, inPair, hypotheses, integral_closure.IntegralMul.Read(L).At(x, b)))
				c.Show(
					"the integral product has integer trace",
					By(productIntegral, hypotheses, IntegralTraceInInt.Read(L).At(c.TermAs[A]("x * b"))))
			}))
		integersInDual := a.Have(
			"the integer ring lies in the trace dual of the integer span",
			"ring_of_integers(field_ring(L)) ⊆ "+
				"trace_dual(L, "+
				"    rational_image(L), "+
				"    module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        regular_module(field_ring(L)), "+
				"        E), "+
				"    integer_image(field_ring(L)))",
			Simp(Fwd(trace_dual.TraceDualDef)),
			BySets(integralPairing, comm_ring.SubringSubset.Read(subringO)))
		a.Show(
			"the integer ring lies between the integer span and its trace dual",
			By(integersInDual, spanInIntegers))
	}),
})}

// RingOfIntegersFreeRankN — the integer ring is a full integer lattice with
// a finite basis whose cardinality is the degree of the number field: the
// integer span M of a rational basis of algebraic integers is a full lattice,
// and the integer ring lies between M and its trace dual, itself a full
// lattice, so it is finitely generated over the principal ideal domain of
// integer scalars; it spans the field, and an integer basis of it is a
// rational basis of the field.
var RingOfIntegersFreeRankN = ringOfIntegersFreeRankNThm{family.Add(registry.ProofEntry{
	Name: "RingOfIntegersFreeRankN",
	Key:  "prop_b46cea8366daf5bc",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "full_integer_lattice(L, ring_of_integers(field_ring(L))) ∧ " +
			"(∃E:set(A). " +
			"    finite(E) ∧ " +
			"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
			"        restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))), " +
			"        E) ∧ " +
			"    module_basis(restrict_ring(field_ring(L), rational_image(L)), " +
			"        regular_module(field_ring(L)), " +
			"        E) ∧ " +
			"    card(E) = extension_degree(L, rational_image(L), L.carrier))",
	}, func(a *Argument, L field.FieldFact[on.L], numberField Fact) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		ringL := a.TermAs[RingOps[A]]("field_ring(L)")
		Q := a.TermAs[Set[A]]("rational_image(L)")
		O := a.TermAs[Set[A]]("ring_of_integers(field_ring(L))")
		carrierL := a.TermAs[Set[A]]("L.carrier")
		rationalScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		integerScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		E, integralBasis := a.ObtainAs[Set[A]](
			"choose a finite rational basis consisting of integers of L",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        E) ∧ "+
				"    E ⊆ ring_of_integers(field_ring(L))",
			Named("E"),
			By(numberField, IntegralRationalBasisExists.Read(L)))
		M, mDefinition := a.LetAs[Set[A]](
			"M",
			"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    E)")
		scalars := a.Conjuncts(
			GroupPremises(L, numberField, number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		characteristicZero, principal, moduleZ, moduleQ := scalars[0], scalars[4], scalars[5], scalars[6]
		integerRing := a.Have(
			"the integers of L form a subring containing the integer scalars",
			"subring(field_ring(L), ring_of_integers(field_ring(L))) ∧ "+
				"integer_image(field_ring(L)) ⊆ ring_of_integers(field_ring(L))",
			By(numberField, integral_closure.IntegralClosureSubring.Read(L)))
		subringO := a.Conjuncts(
			integerRing,
			"the integers of L form a subring of L",
			"they contain the integer scalars")[0]
		oInL := a.Have(
			"so they lie in L",
			"ring_of_integers(field_ring(L)) ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subringO)))
		fullBetween := a.Have(
			"every subset of L containing E spans L over the rationals",
			Statement{
				Binders: "∀S:set(A).",
				Hypotheses: []string{
					"E ⊆ S",
					"S ⊆ L.carrier",
				},
				Conclusion: "module_span(restrict_ring(field_ring(L), rational_image(L)), " +
					"    regular_module(field_ring(L)), " +
					"    S) = " +
					"L.carrier",
			},
			Derive(func(b *Argument) {
				S := b.FixAs[Set[A]]("S")
				between := b.Assume()
				b.Show(
					"the rational basis spans L, so span monotonicity and the ambient carrier bound give equality",
					BySets(
						integralBasis,
						linear_independence.ModuleBasisDef.At(rationalScalars, vectors, E),
						between,
						submodule.SpanMono.At(rationalScalars, vectors, E, S),
						submodule.CarrierSubmodule.Read(moduleQ),
						submodule.SpanLeast.At(rationalScalars, vectors, S, carrierL)))
			}))

		fullM := a.Have(
			"the lower lattice M is a full integer lattice",
			"full_integer_lattice(L, M)",
			Derive(func(b *Argument) {
				basisInL := b.Have(
					"the integral rational basis lies in L",
					"E ⊆ L.carrier",
					BySets(integralBasis, oInL))
				submoduleM := b.Have(
					"the lower lattice is an integer submodule",
					"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    regular_module(field_ring(L)), "+
						"    M)",
					By(Normalized, mDefinition, basisInL, submodule.SpanSubmodule.Read(moduleZ).At(E)))
				basisInM := b.Have(
					"the lower lattice contains the rational basis",
					"E ⊆ M",
					By(Normalized, mDefinition, submodule.SubsetSpan.At(integerScalars, vectors, E)))
				spanInM := b.Have(
					"E generates M with the restricted module operations",
					"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), M), "+
						"    E) = "+
						"M",
					By(mDefinition, basisInM, submoduleM, linear_independence.SpanRestrict.Read(moduleZ).At(M, E)))
				finiteM := b.Have(
					"the lower lattice is finitely generated over the integer scalars",
					"module_finitely_generated(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), M))",
					Simp(Fwd(principal_ideal_domain.FinitelyGeneratedDef)),
					Witness(E),
					By(integralBasis, basisInM, spanInM))
				spanM := b.Have(
					"the lower lattice has full rational span",
					"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
						"    regular_module(field_ring(L)), "+
						"    M) = "+
						"L.carrier",
					By(basisInM, submodule.SubmoduleSubset.Read(submoduleM), fullBetween))
				b.Show(
					"a finitely generated integer submodule with full rational span is a full lattice",
					By(
						submoduleM,
						finiteM,
						spanM,
						int_lattice.IntegerLatticeDef.At(ringL, M),
						int_lattice.FullIntegerLatticeDef.At(fieldL, M)))
			}))

		sandwich := a.Have(
			"the integer ring lies between M and its trace dual",
			"M ⊆ ring_of_integers(field_ring(L)) ∧ "+
				"ring_of_integers(field_ring(L)) ⊆ "+
				"trace_dual(L, rational_image(L), M, integer_image(field_ring(L)))",
			By(Normalized, mDefinition, numberField, integralBasis, RingOfIntegersInTraceDual.Read(L).At(E)))

		integerSubmodule := a.Conjuncts(
			GroupPremises(L, numberField, RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is an integer submodule of L",
			"it is an integer module")[0]
		finiteO := a.Have(
			"the integer ring is finitely generated over the integer scalars",
			"module_finitely_generated(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))))",
			Derive(func(b *Argument) {
				D, dDefinition := b.LetAs[Set[A]](
					"D", "trace_dual(L, rational_image(L), M, integer_image(field_ring(L)))")
				fullD := b.Have(
					"the trace dual is a full integer lattice",
					"full_integer_lattice(L, D)",
					By(Normalized, dDefinition, numberField, fullM, TraceDualFull.Read(L).At(M)))
				dualLattice := b.Unfolded(fullD, int_lattice.FullIntegerLatticeDef)
				dualData := b.Unfolded(dualLattice, int_lattice.IntegerLatticeDef)
				insideDual := b.Have(
					"the integer ring is a submodule of the trace-dual lattice",
					"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), D), "+
						"    ring_of_integers(field_ring(L)))",
					By(integerSubmodule, sandwich, submodule.SubmoduleRestrict.At(integerScalars, vectors, D, O)))
				nested := b.Have(
					"restriction through D preserves the operations on the integer ring",
					"restrict_module(restrict_module(regular_module(field_ring(L)), D), "+
						"    ring_of_integers(field_ring(L))) = "+
						"restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L)))",
					Simp(Fwd(module_record.RestrictModuleDef)),
					Basic())
				b.Show(
					"a submodule of a finitely generated module over a principal ideal domain is finitely generated",
					By(
						principal,
						dualData,
						submodule.SubmoduleModuleOn.Read(moduleZ).At(D),
						insideDual,
						nested,
						principal_ideal_domain.FinitelyGeneratedSubmodule.At(
							integerScalars,
							b.TermAs[module_record.ModuleOps[A, A]]("restrict_module(regular_module(field_ring(L)), D)"),
							O)))
			}))

		fullO := a.Have(
			"the integer ring is a full integer lattice",
			"full_integer_lattice(L, ring_of_integers(field_ring(L)))",
			Derive(func(b *Argument) {
				integerLattice := b.Have(
					"the integer ring is an integer lattice",
					"integer_lattice(field_ring(L), ring_of_integers(field_ring(L)))",
					By(integerSubmodule, finiteO, int_lattice.IntegerLatticeDef.At(ringL, O)))
				spanO := b.Have(
					"the integer ring spans L over the rationals",
					"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
						"    regular_module(field_ring(L)), "+
						"    ring_of_integers(field_ring(L))) = "+
						"L.carrier",
					By(integralBasis, oInL, fullBetween))
				b.Show(
					"an integer lattice with full rational span is full",
					By(integerLattice, spanO, int_lattice.FullIntegerLatticeDef.At(fieldL, O)))
			}))

		lattice := a.Conjuncts(
			a.Unfolded(fullO, int_lattice.FullIntegerLatticeDef),
			"the integer ring is an integer lattice",
			"it spans L over the rationals")
		integerLattice, spanO := lattice[0], lattice[1]
		rankBasis := a.Have(
			"an integer basis of the integer ring is a rational basis of L whose size is the field degree",
			"∃F:set(A). "+
				"    finite(F) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))), "+
				"        F) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        F) ∧ "+
				"    card(F) = extension_degree(L, rational_image(L), L.carrier)",
			Derive(func(b *Argument) {
				F, free := b.ObtainAs[Set[A]](
					"choose a finite integer basis of the integer ring",
					"∃F:set(A). "+
						"    finite(F) ∧ "+
						"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"        restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))), "+
						"        F) ∧ "+
						"    card(F) ≤ extension_degree(L, rational_image(L), L.carrier)",
					Named("F"),
					By(numberField, integerLattice, FinitelyGeneratedFieldSubmoduleFree.Read(L).At(O)))
				carrier := b.Have(
					"the regular module has the field carrier",
					"regular_module(field_ring(L)).carrier = L.carrier",
					Simp(Fwd(module_record.RegularModuleDef), Fwd(field.FieldRingDef)),
					Basic())
				restrictL := b.Have(
					"restriction to the full field carrier preserves the regular module",
					"restrict_module(regular_module(field_ring(L)), L.carrier) = regular_module(field_ring(L))",
					Simp(Rev(carrier), Fwd(module_record.RestrictModuleCarrier)),
					Basic())
				rationalBasis := b.Have(
					"F is a rational basis and its cardinality is the rational dimension of L",
					"module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
						"    regular_module(field_ring(L)), "+
						"    F) ∧ "+
						"module_dim(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L))) = "+
						"card(F)",
					By(
						characteristicZero,
						integerLattice,
						spanO,
						restrictL,
						free,
						int_lattice.IntegerBasisRationalSpan.Read(L).At(O, F)))
				rank := b.Have(
					"the basis cardinality is the field degree",
					"card(F) = extension_degree(L, rational_image(L), L.carrier)",
					By(
						Normalized,
						rationalBasis,
						restrictL,
						field_extension.ExtensionDegreeDef.At(fieldL, Q, carrierL)))
				b.Take(F)
				b.Show(
					"F is the required basis",
					By(free, rationalBasis, rank))
			}))
		a.Show(
			"the integer ring is a full lattice with a basis of the stated rank",
			By(fullO, rankBasis))
	}),
})}

// IntegralBasisExists — the ring of integers of a number field has an
// integral basis, an integer basis indexed by the numbers below its size:
// the integer ring has a finite integer basis E, and the segment below
// card(E) has the size of E, so a bijection from it onto E enumerates E
// one-to-one with E as its image.
var IntegralBasisExists = integralBasisExistsThm{family.Add(registry.ProofEntry{
	Name: "IntegralBasisExists",
	Key:  "prop_5f0b8f727ae8d18b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "∃n:num. ∃e:(num → A). integral_basis(field_ring(L), n, e)",
	}, func(a *Argument, L field.FieldFact[on.L], numberField Fact) {
		ringL := a.TermAs[RingOps[A]]("field_ring(L)")
		integerScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		integerModule := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L)))")
		E, basis := a.ObtainAs[Set[A]](
			"choose a finite integer basis of the integer ring",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))), "+
				"        E)",
			Named("E"),
			By(numberField, RingOfIntegersFreeRankN.Read(L)))
		n := a.TermAs[Nat]("card(E)")
		segment := a.TermAs[Set[Nat]]("{k:num | k < card(E)}")
		e, enumeration := a.ObtainAs[Fun[Nat, A]](
			"enumerate E by the numbers below its size",
			"∃e:(num → A). "+
				"    (∀i:num. i ∈ {k:num | k < card(E)} ⇒ e(i) ∈ E) ∧ "+
				"    (∀y:A. y ∈ E ⇒ ∃i:num. i ∈ {k:num | k < card(E)} ∧ e(i) = y) ∧ "+
				"    injective_on({k:num | k < card(E)}, e)",
			Named("e"),
			By(
				basis,
				num_segment.HasSizeBelowStrict.At(n),
				cardinality.HasSizeDef.At(segment, n),
				cardinality.CardEqBijection.At(segment, E)))
		image := a.Have(
			"the enumeration has exactly E as its image",
			"{e(i):A | i:num | i < card(E)} = E",
			BySets(enumeration))
		a.Take(n)
		a.Take(e)
		a.Show(
			"a one-to-one enumeration of an integer basis is an integral basis",
			By(
				image,
				basis,
				enumeration,
				linear_independence.IndexedModuleBasisDef.At(integerScalars, integerModule, n, e),
				IntegralBasisDef.At(ringL, n, e)))
	}),
})}
