package ring_of_integers

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// StableFullIntegerLattice — the span of a finite rational basis over the
// polynomial image ℤ[x] of an algebraic integer x is a full integer lattice
// preserved by multiplication by x: the span is finite over ℤ[x], which is
// finite over the integers since x is integral; it contains the basis, so it
// spans the field over the rationals; and x is one of its scalars.
var StableFullIntegerLattice = stableFullIntegerLatticeThm{family.Add(registry.ProofEntry{
	Name: "StableFullIntegerLattice",
	Key:  "prop_ee3251d1a6227907",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀x:A. ∀E:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"x ∈ ring_of_integers(field_ring(L))",
			"finite(E)",
			"module_basis(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), E)",
		},
		Conclusion: "full_integer_lattice(L, «M») ∧ image(L.mul(x), «M») ⊆ «M»",
		Abbrev: Abbrev{
			{Name: "ℤ[x]", Text: "polynomial_image(field_ring(L), integer_image(field_ring(L)), x)"},
			{Name: "M", Text: "module_span(restrict_ring(field_ring(L), «ℤ[x]»), " +
				"    regular_module(field_ring(L)), " +
				"    E)"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], x *Expr[A], E *Expr[Set[A]], given Fact) {
		parts := a.Conjuncts(
			given,
			"L is a number field",
			"x is an algebraic integer",
			"E is finite",
			"E is a rational basis of L")
		integerX, finiteE, rationalBasis := parts[1], parts[2], parts[3]
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
		subQ, integersInQ, integerRing, moduleQ := scalars[1], scalars[2], scalars[3], scalars[6]
		integersInL := a.Have(
			"the integer scalars lie in L",
			"integer_image(field_ring(L)) ⊆ L.carrier",
			BySets(integersInQ, field.SubfieldSubset.Read(subQ)))
		integerMembership := a.Unfolded(integerX, integral_closure.RingOfIntegersDef)
		xData := a.Have(
			"x lies in L and is integral over its integer image",
			"x ∈ L.carrier ∧ integral_over(restrict_ring(field_ring(L), integer_image(field_ring(L))), x)",
			BySets(integerMembership))
		xParts := a.Conjuncts(
			xData,
			"x lies in L",
			"x is integral over the integer scalars")
		xMember := a.MemberOf[on.L](x, xParts[0])
		ringL := a.TermAs[RingOps[A]]("field_ring(L)")
		Z := a.TermAs[Set[A]]("integer_image(field_ring(L))")
		subringZ := a.Have(
			"the integer scalars, a ring inside L, form a subring of L",
			"subring(field_ring(L), integer_image(field_ring(L)))",
			By(integersInL, integerRing, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(Z)))
		algebra := a.TermAs[Set[A]]("«ℤ[x]»")
		rationalScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		algebraScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), «ℤ[x]»)")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		M := a.TermAs[Set[A]]("«M»")
		carrierL := a.TermAs[Set[A]]("L.carrier")
		polynomialStructure := a.Have(
			"the polynomial image is a subring containing the integers and x",
			"subring(field_ring(L), «ℤ[x]») ∧ integer_image(field_ring(L)) ⊆ «ℤ[x]» ∧ x ∈ «ℤ[x]»",
			By(subringZ, xData, algebraic_element.PolynomialImageSubring.Read(L).At(Z, xMember)))
		polynomialParts := a.Conjuncts(
			polynomialStructure,
			"the polynomial image is a subring of L",
			"it contains the integer scalars",
			"it contains x")
		moduleA := a.Have(
			"L is a module over the polynomial image",
			"module_on(restrict_ring(field_ring(L), «ℤ[x]»), regular_module(field_ring(L)))",
			By(polynomialParts[0], fractional_ideal.FieldModuleOn.Read(L).At(algebra)))
		submoduleA := a.Have(
			"the polynomial-image span of E is a submodule",
			"submodule(restrict_ring(field_ring(L), «ℤ[x]»), regular_module(field_ring(L)), «M»)",
			By(
				linear_independence.BasisInCarrier.Read(rationalBasis),
				submodule.SpanSubmodule.Read(moduleA).At(E)))
		EInM := a.Have(
			"E lies in its polynomial-image span",
			"E ⊆ «M»",
			By(submodule.SubsetSpan.At(algebraScalars, vectors, E)))
		spanInside := a.Have(
			"E generates the restricted span module",
			"module_span(restrict_ring(field_ring(L), «ℤ[x]»), "+
				"    restrict_module(regular_module(field_ring(L)), «M»), "+
				"    E) = "+
				"«M»",
			By(submoduleA, EInM, linear_independence.SpanRestrict.Read(moduleA).At(M, E)))
		moduleFinite := a.Have(
			"M is finitely generated over the polynomial image",
			"module_finitely_generated(restrict_ring(field_ring(L), «ℤ[x]»), "+
				"    restrict_module(regular_module(field_ring(L)), «M»))",
			Simp(Fwd(principal_ideal_domain.FinitelyGeneratedDef)),
			Derive(func(b *Argument) {
				b.Take(E)
				b.Show(
					"the finite basis E supplies generators",
					By(finiteE, EInM, spanInside))
			}))
		imageFinite := a.Have(
			"integrality makes the polynomial image finite over the integers",
			"module_finitely_generated(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «ℤ[x]»))",
			By(subringZ, xData, principal_ideal_domain.IntegralPolynomialModule.Read(L).At(Z, xMember)))
		tower := a.Conjuncts(
			GroupPremises(
				polynomialParts[1],
				subringZ,
				polynomialParts[0],
				submoduleA,
				moduleFinite,
				imageFinite,
				principal_ideal_domain.FiniteModuleTower.Read(L).At(Z, algebra, M)),
			"M is an integer submodule after restricting scalars",
			"finite generation descends through the finite polynomial algebra")
		submoduleZ, finiteOverZ := tower[0], tower[1]
		integerLattice := a.Have(
			"M is an integer lattice",
			"integer_lattice(field_ring(L), «M»)",
			By(submoduleZ, finiteOverZ, int_lattice.IntegerLatticeDef.At(ringL, M)))
		rationalBasisData := a.Unfolded(rationalBasis, linear_independence.ModuleBasisDef)
		rationalSpan := a.TermAs[Set[A]](
			"module_span(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), «M»)")
		spanContainsL := a.Have(
			"E spans L over the rationals and lies in M, so the rational span of M contains L",
			"L.carrier ⊆ "+
				"module_span(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), «M»)",
			By(rationalBasisData, EInM, submodule.SpanMono.At(rationalScalars, vectors, E, M)))
		spanInL := a.Have(
			"the rational span of M lies in L",
			"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    «M») ⊆ "+
				"L.carrier",
			By(
				submodule.SubmoduleSubset.Read(submoduleA),
				submodule.CarrierSubmodule.Read(moduleQ),
				submodule.SpanLeast.At(rationalScalars, vectors, M, carrierL)))
		fullSpan := a.Have(
			"the rational span of M is L",
			"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    «M») = "+
				"L.carrier",
			By(spanContainsL, spanInL, set_order.SubsetAntisym.At(rationalSpan, carrierL)))
		fullLattice := a.Have(
			"M is a full integer lattice",
			"full_integer_lattice(L, «M»)",
			By(integerLattice, fullSpan, int_lattice.FullIntegerLatticeDef.At(fieldL, M)))
		stable := a.Have(
			"multiplication by x preserves M",
			"image(L.mul(x), «M») ⊆ «M»",
			Simp(Fwd(set_image.ImageSubsetIff)),
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				yInM := b.Assume()
				b.Show(
					"x is a polynomial scalar, so its multiple remains in M",
					By(polynomialParts[2], yInM, submodule.SubmoduleSmul.Read(submoduleA).AsFact().At(x, y)))
			}))
		a.Show(
			"the polynomial-image span is full and stable under x",
			By(fullLattice, stable))
	}),
})}

// IntegralTraceInInt — the field trace of an algebraic integer is an integer scalar.
var IntegralTraceInInt = integralTraceInIntThm{family.Add(registry.ProofEntry{
	Name: "IntegralTraceInInt",
	Key:  "prop_5d8b5abd4112447e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀x:A.",
		Hypotheses: []string{
			"number_field(L)",
			"x ∈ ring_of_integers(field_ring(L))",
		},
		Conclusion: "field_trace(L, rational_image(L), x) ∈ integer_image(field_ring(L))",
	}, func(a *Argument, L field.FieldFact[on.L], x *Expr[A], given Fact) {
		parts := a.Conjuncts(
			given,
			"L is a number field",
			"x is an algebraic integer")
		numberField, integerX := parts[0], parts[1]
		numberData := a.Unfolded(numberField, number_field.NumberFieldDef)
		Q := a.TermAs[Set[A]]("rational_image(L)")
		rationalScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		E, rationalBasisE := a.ObtainAs[Set[A]](
			"choose a finite rational basis of L",
			"∃E:set(A). "+
				"    finite(E) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        E)",
			Named("E"),
			By(numberData, module_dimension.FiniteDimensionalDef.At(rationalScalars, vectors)))
		stableSpan := a.TermAs[Set[A]](
			"module_span(restrict_ring(field_ring(L), " +
				"        polynomial_image(field_ring(L), integer_image(field_ring(L)), x)), " +
				"    regular_module(field_ring(L)), " +
				"    E)")
		M, stable := a.ObtainAs[Set[A]](
			"choose a full integer lattice preserved by multiplication by x",
			"∃M:set(A). full_integer_lattice(L, M) ∧ image(L.mul(x), M) ⊆ M",
			Named("M"),
			Witness(stableSpan),
			By(numberField, integerX, rationalBasisE, StableFullIntegerLattice.Read(L).At(x, E)))
		stableParts := a.Conjuncts(
			stable,
			"M is a full integer lattice",
			"multiplication by x preserves M")
		lattice := a.Unfolded(stableParts[0], int_lattice.FullIntegerLatticeDef)
		F, free := a.ObtainAs[Set[A]](
			"choose a finite integer basis of M",
			"∃F:set(A). "+
				"    finite(F) ∧ "+
				"    module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"        restrict_module(regular_module(field_ring(L)), M), "+
				"        F) ∧ "+
				"    card(F) ≤ extension_degree(L, rational_image(L), L.carrier)",
			Named("F"),
			By(numberField, lattice, FinitelyGeneratedFieldSubmoduleFree.Read(L).At(M)))
		scalars := a.Conjuncts(
			GroupPremises(L, parts[0], number_field.NumberFieldScalars.At(a.TermAs[FieldOps[A]]("L"))),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		subQ, integerRing, moduleZ := scalars[1], scalars[3], scalars[5]
		rational := a.Conjuncts(
			GroupPremises(
				scalars[0], stableParts[0], free, int_lattice.FullLatticeBasisRational.Read(L).At(M, F)),
			"the full integer basis is also a rational basis of L",
			"rational and integer coordinates agree on the lattice")
		rationalBasisF, coordinateRestriction := rational[0], rational[1]
		integerData := a.Unfolded(lattice, int_lattice.IntegerLatticeDef)
		integerModule := a.Have(
			"the lattice is an integer module",
			"module_on(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), M))",
			By(integerData, submodule.SubmoduleModuleOn.Read(moduleZ).At(M)))
		freeParts := a.Conjuncts(
			free,
			"F is finite",
			"F is an integer basis of M",
			"its size is bounded by the field degree")
		stablePoints := a.Simplified(stableParts[1], Fwd(set_image.ImageSubsetIff))
		diagonal := a.Have(
			"the multiplication diagonal consists of integer scalars",
			Statement{
				Binders: "∀b:A.",
				Hypotheses: []string{
					"b ∈ F",
				},
				Conclusion: "module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
					"    regular_module(field_ring(L)), " +
					"    F, " +
					"    x * b, " +
					"    b) ∈ " +
					"integer_image(field_ring(L))",
			},
			Derive(func(b *Argument) {
				b.FixAs[A]("b")
				basisMember := b.Assume()
				bInM := b.Have(
					"the basis vector lies in M",
					"b ∈ M",
					BySets(basisMember, linear_independence.BasisInCarrier.Read(freeParts[1])))
				productInM := b.Have(
					"its product with x remains in M",
					"x * b ∈ M",
					By(bInM, stablePoints))
				product := b.TermAs[A]("x * b")
				b.Show(
					"coordinate restriction gives an integer diagonal coefficient",
					Simp(Fwd(coordinateRestriction)),
					By(
						free,
						basisMember,
						productInM,
						module_dimension.BasisCoordinatesSpec.Read(integerModule).AsFact().At(F, product)))
			}))
		integerRegular := a.Have(
			"the integer scalar ring is its own regular module",
			"module_on(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(restrict_ring(field_ring(L), integer_image(field_ring(L)))))",
			By(module.RegularModuleOn.Read(integerRing)))
		diagonalFunction := a.TermAs[Fun[A, A]](
			"λb:A. " +
				"    module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
				"        regular_module(field_ring(L)), " +
				"        F, " +
				"        x * b, " +
				"        b)")
		total := a.Have(
			"the finite sum of the diagonal coefficients is an integer scalar",
			"module_sum(L.add, "+
				"    L.zero, "+
				"    F, "+
				"    λb:A. "+
				"        module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), "+
				"            regular_module(field_ring(L)), "+
				"            F, "+
				"            x * b, "+
				"            b)) ∈ "+
				"integer_image(field_ring(L))",
			By(free, diagonal, module.ModuleSumIn.Read(integerRegular).At(F, diagonalFunction)))
		xDefinition := a.Unfolded(integerX, integral_closure.RingOfIntegersDef)
		xInL := a.Have(
			"the algebraic integer lies in L",
			"x ∈ L.carrier",
			BySets(xDefinition))
		xMember := a.MemberOf[on.L](x, xInL)
		traceFormula := a.Have(
			"this rational basis computes the field trace by its multiplication diagonal",
			"field_trace(L, rational_image(L), x) = "+
				"module_basis_trace(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    F, "+
				"    L.mul(x))",
			By(subQ, free, rationalBasisF, field_trace.FieldTraceFromBasis.Read(L).At(Q, F, xMember)))
		a.Show(
			"the field trace is the integer diagonal sum",
			Simp(Fwd(traceFormula), Fwd(module_dimension.ModuleBasisTraceDef)),
			By(total))
	}),
})}
