package integral_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ClearDenominator — multiplying a number-field element by a positive
// integer makes it integral: clear the coefficients of its multiplication
// on a rational basis and apply the stable finite module criterion to the
// integer span of that basis together with one.
var ClearDenominator = clearDenominatorThm{family.Add(registry.ProofEntry{
	Name: "ClearDenominator",
	Key:  "prop_2c433e14525c6a33",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀x:A.",
		Hypotheses: []string{
			"number_field(L)",
			"x ∈ L.carrier",
		},
		Conclusion: "∃d:num. 0 < d ∧ integer_map(field_ring(L), d) * x ∈ ring_of_integers(field_ring(L))",
	}, func(a *Argument, L field.FieldFact[on.L], x *Expr[A], h Fact) {
		parts := a.Conjuncts(
			h,
			"L is a number field",
			"x lies in L")
		numberField, xIn := parts[0], parts[1]
		fieldRing := field.RingOn.Read(L)
		mulAssoc := comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(fieldRing))
		fieldL := a.TermAs[FieldOps[A]]("L")
		scalars := a.Conjuncts(
			GroupPremises(L, parts[0], number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		charZero, integersInRationals, integerRing := scalars[0], scalars[2], scalars[3]
		integerModule, rationalModule := scalars[5], scalars[6]
		rationalIn := a.Have(
			"rational scalars lie in L",
			"rational_image(L) ⊆ L.carrier",
			By(field.SubfieldSubset.Read(scalars[1])))
		integers := a.TermAs[Set[A]]("integer_image(field_ring(L))")
		integerScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		rationalScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		ambient := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		integersIn := a.Have(
			"the integer image lies in L",
			"integer_image(field_ring(L)) ⊆ L.carrier",
			BySets(integersInRationals, rationalIn))
		integerSubring := a.Have(
			"the integer image is a subring of L",
			"subring(field_ring(L), integer_image(field_ring(L)))",
			By(integersIn, integerRing, comm_ring.SubringRingOn.Read(fieldRing).At(integers)))
		E, basis := a.ObtainAs[Set[A]](
			"choose a finite rational basis",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        E)",
			By(
				numberField,
				number_field.NumberFieldDef,
				module_dimension.FiniteDimensionalDef.At(rationalScalars, ambient)))
		basisParts := a.Conjuncts(
			basis,
			"the basis is finite",
			"E is a rational basis")
		finiteE, basisE := basisParts[0], basisParts[1]
		basisIn := a.Have(
			"the basis lies in L",
			"E ⊆ L.carrier",
			By(linear_independence.BasisInCarrier.Read(basisE)))
		G, defG := a.LetAs[Set[A]]("G", "insert(L.one, E)")
		finiteG := a.Have(
			"adjoining one leaves finitely many generators",
			"finite(G)",
			By(Normalized, finiteE, defG, finite_set.FiniteRules))
		generatorsIn := a.Have(
			"the generators lie in L and contain one and the basis",
			"G ⊆ L.carrier ∧ L.one ∈ G ∧ E ⊆ G",
			BySets(defG, basisIn, comm_ring.OneIn.Read(fieldRing)))
		M, defM := a.LetAs[Set[A]](
			"M",
			"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    G)")
		subM := a.Have(
			"their integer span is an integer submodule",
			"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    M)",
			By(Normalized, defM, generatorsIn, submodule.SpanSubmodule.Read(integerModule).At(G)))
		generatorsInM := a.Have(
			"the span contains the generators, one and the basis",
			"G ⊆ M ∧ L.one ∈ M ∧ E ⊆ M",
			BySets(defM, generatorsIn, submodule.SubsetSpan.At(integerScalars, ambient, G)))
		c, defCoordinateMap := a.LetAs[Op[A]](
			"c",
			"λg:A. λe:A. "+
				"    module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        E, "+
				"        x * g, "+
				"        e)")
		coordinates := a.Have(
			"basis coordinates expand multiplication by x on every generator",
			Statement{
				Binders: "∀g:A.",
				Hypotheses: []string{
					"g ∈ G",
				},
				Conclusion: "(∀e:A. e ∈ E ⇒ c(g, e) ∈ rational_image(L)) ∧ " +
					"module_sum(L.add, L.zero, E, λe:A. c(g, e) * e) = x * g",
			},
			Derive(func(b *Argument) {
				b.FixAs[A]("g")
				gIn := b.Assume()
				productIn := b.Have(
					"this product lies in the field",
					"x * g ∈ L.carrier",
					BySets(xIn, gIn, generatorsIn, comm_ring.MulIn.Read(fieldRing)))
				b.Show(
					"the rational basis coordinates give this expansion",
					By(
						Normalized,
						defCoordinateMap,
						finiteE,
						basisE,
						productIn,
						module_dimension.BasisCoordinatesSpec.Read(rationalModule).AsFact().At(E, b.TermAs[A]("x * g"))))
			}))
		C, defCoefficients := a.LetAs[Set[A]]("C", "{c(g, e) | g:A, e:A | g ∈ G ∧ e ∈ E}")
		finiteC := a.Have(
			"the multiplication coefficients form a finite set",
			"finite(C)",
			By(
				finiteG,
				finiteE,
				defCoefficients,
				finite_set.FiniteProductDependent.At(c, G, a.TermAs[Fun[A, Set[A]]]("λg:A. E"))))
		coefficientsIn := a.Have(
			"these coefficients are rational",
			"C ⊆ rational_image(L)",
			BySets(defCoefficients, coordinates))
		d, clears := a.ObtainAs[Nat](
			"choose one positive integer clearing all these coefficients",
			"∃d:num. 0 < d ∧ (∀a:A. a ∈ C ⇒ integer_map(field_ring(L), d) * a ∈ integer_image(field_ring(L)))",
			By(charZero, finiteC, coefficientsIn, characteristic_zero.FiniteRationalDenominator.Read(L).At(C)))
		D, defD := a.LetAs[A]("D", "integer_map(field_ring(L), d)")
		denominatorIn := a.Have(
			"the denominator belongs to the integer image",
			"D ∈ integer_image(field_ring(L))",
			BySets(defD, characteristic_zero.IntegerImageDef))
		denominatorInField := a.Have(
			"the denominator lies in L",
			"D ∈ L.carrier",
			BySets(denominatorIn, integersIn))
		clearedCoefficients := a.Have(
			"the scaled multiplication coefficients are integers",
			"∀g e:A. g ∈ G ∧ e ∈ E ⇒ D * c(g, e) ∈ integer_image(field_ring(L))",
			BySets(defCoefficients, clears))
		restrictedSpan := a.Have(
			"the same generators span the restricted module",
			"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), M), "+
				"    G) = "+
				"M",
			By(defM, generatorsInM, subM, linear_independence.SpanRestrict.Read(integerModule).At(M, G)))
		finiteM := a.Have(
			"this integer module is finitely generated",
			"module_finitely_generated(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), M))",
			Simp(Fwd(principal_ideal_domain.FinitelyGeneratedDef)),
			Witness(G),
			By(finiteG, generatorsInM, restrictedSpan))
		generatorStable := a.Have(
			"multiplication by the scaled element preserves every generator",
			"∀g:A. g ∈ G ⇒ (D * x) * g ∈ M",
			Derive(func(b *Argument) {
				g := b.FixAs[A]("g")
				gIn := b.Assume()
				gInField := b.Have(
					"this generator lies in L",
					"g ∈ L.carrier",
					BySets(gIn, generatorsIn))
				expansion := b.Have(
					"expand the product on the rational basis",
					"(∀e:A. e ∈ E ⇒ c(g, e) ∈ rational_image(L)) ∧ "+
						"module_sum(L.add, L.zero, E, λe:A. c(g, e) * e) = x * g",
					By(Normalized, gIn, coordinates.At(g)))
				expansionParts := b.Conjuncts(
					expansion,
					"these coordinates are rational",
					"the coordinate sum is the product")
				coefficientRational, sumEquals := expansionParts[0], expansionParts[1]
				termsIn := b.Have(
					"the summands lie in L",
					"∀e:A. e ∈ E ⇒ c(g, e) * e ∈ L.carrier",
					BySets(coefficientRational, rationalIn, basisIn, comm_ring.MulIn.Read(fieldRing)))
				scaledTerms := b.Have(
					"each scaled summand belongs to M",
					"∀e:A. e ∈ E ⇒ D * (c(g, e) * e) ∈ M",
					Derive(func(f *Argument) {
						e := f.FixAs[A]("e")
						eIn := f.Assume()
						scalarData := f.Have(
							"the basis element belongs to M and its cleared coefficient is an integer",
							"c(g, e) ∈ L.carrier ∧ e ∈ L.carrier ∧ e ∈ M ∧ D * c(g, e) ∈ integer_image(field_ring(L))",
							BySets(
								eIn,
								gIn,
								basisIn,
								rationalIn,
								generatorsInM,
								coefficientRational.At(e),
								clearedCoefficients.At(g, e)))
						f.Show(
							"associativity turns the summand into an integer scalar multiple",
							By(
								denominatorInField,
								scalarData,
								mulAssoc.AsFact().At(D, f.TermAs[A]("c(g, e)"), e),
								submodule.SubmoduleSmul.Read(subM).AsFact().At(f.TermAs[A]("D * c(g, e)"), e)))
					}))
				sumIn := b.Have(
					"the finite sum of scaled summands belongs to M",
					"module_sum(L.add, L.zero, E, λe:A. D * (c(g, e) * e)) ∈ M",
					By(
						finiteE,
						subM,
						scaledTerms,
						submodule.SubmoduleModuleSum.Read(integerModule).At(
							M, E, b.TermAs[Fun[A, A]]("λe:A. D * (c(g, e) * e)"))))
				distributes := b.Have(
					"scalar multiplication distributes through the coordinate sum",
					"D * module_sum(L.add, L.zero, E, λe:A. c(g, e) * e) = "+
						"module_sum(L.add, L.zero, E, λe:A. D * (c(g, e) * e))",
					By(
						finiteE,
						denominatorIn,
						termsIn,
						module.ModuleSumSmul.Read(integerModule).AsFact().At(
							E, D, b.TermAs[Fun[A, A]]("λe:A. c(g, e) * e"))))
				b.Show(
					"the scaled product is that sum in M",
					By(denominatorInField, xIn, gInField, sumIn, distributes, sumEquals, mulAssoc.AsFact().At(D, x, g)))
			}))
		scaledElement := a.TermAs[A]("D * x")
		scaledIn := a.Have(
			"the scaled element lies in L",
			"D * x ∈ L.carrier",
			By(denominatorInField, xIn, comm_ring.MulIn.Read(fieldRing).AsFact().At(D, x)))
		linearScaling := a.Have(
			"multiplication by this element is integer-linear",
			"module_homomorphism(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    regular_module(field_ring(L)), "+
				"    L.mul(D * x))",
			By(
				integerSubring,
				scaledIn,
				field_extension.ScaleLinear.Read(L).AsFact().At(integers, scaledElement)))
		scale := a.TermAs[Fun[A, A]]("L.mul(D * x)")
		imageIn := a.Have(
			"the generator images lie in M",
			"image(L.mul(D * x), G) ⊆ M",
			BySets(generatorStable))
		stable := a.Have(
			"so multiplication by the scaled element, being linear, preserves M, the span of G",
			"image(L.mul(D * x), M) ⊆ M",
			By(
				Normalized,
				defM,
				generatorsIn,
				linearScaling,
				subM,
				imageIn,
				linear_independence.HomSpanInSubmodule.At(integerScalars, ambient, ambient, scale, G, M)))
		integral := a.Have(
			"the stable finite module makes the scaled element integral",
			"integral_over(restrict_ring(field_ring(L), integer_image(field_ring(L))), D * x)",
			By(
				integerSubring,
				scaledIn,
				subM,
				finiteM,
				generatorsInM,
				stable,
				principal_ideal_domain.StableModuleIntegral.Read(L).AsFact().At(integers, scaledElement, M)))
		algebraicInteger := a.Have(
			"the scaled element belongs to the integer ring",
			"D * x ∈ ring_of_integers(field_ring(L))",
			BySets(scaledIn, integral, RingOfIntegersDef))
		a.Take(d)
		a.Show(
			"the positive denominator has the required property",
			By(Normalized, defD, clears, algebraicInteger))
	}),
})}
