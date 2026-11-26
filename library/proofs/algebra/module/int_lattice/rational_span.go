package int_lattice

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerRationalIndependence — independence over the integer image is
// independence over the rational image. A positive common denominator
// converts a rational relation into an integer relation; cancellation in
// the host field then recovers the original coefficients.
var IntegerRationalIndependence = integerRationalIndependenceThm{family.Add(registry.ProofEntry{
	Name: "IntegerRationalIndependence",
	Key:  "prop_969883ed8bc7cbd4",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀E:set(A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"E ⊆ L.carrier",
		},
		Conclusion: "module_independent(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
			"    regular_module(field_ring(L)), " +
			"    E) ⇔ " +
			"module_independent(restrict_ring(field_ring(L), rational_image(L)), " +
			"    regular_module(field_ring(L)), " +
			"    E)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		clearDenominators := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀T:set(A). ∀a:(A → A).",
			Hypotheses: []string{
				"characteristic_zero(field_ring(L))",
				"finite(T)",
				"∀v:A. v ∈ T ⇒ a(v) ∈ rational_image(L)",
			},
			Conclusion: "∃D:A. " +
				"    D ∈ L.carrier ∧ D ≠ L.zero ∧ (∀v:A. v ∈ T ⇒ D * a(v) ∈ integer_image(field_ring(L)))",
		}, func(b *Argument, L field.FieldFact[on.L], T *Expr[Set[A]], a *Arrow[A, A], h Fact) {
			d, denominator := b.ObtainAs[Nat](
				"one positive integer clears the finite set of rational coefficients",
				"∃d:num. "+
					"    0 < d ∧ "+
					"    (∀c:A. c ∈ image(a, T) ⇒ integer_map(field_ring(L), d) * c ∈ integer_image(field_ring(L)))",
				BySets(
					h,
					characteristic_zero.FiniteRationalDenominator.Read(L).At(b.TermAs[Set[A]]("image(a, T)")),
					finite_set.FiniteImage.At(a, T)))
			R := b.TermAs[RingOps[A]]("field_ring(L)")
			D := b.TermAs[A]("integer_map(field_ring(L), d)")
			b.Take(D)
			b.Show(
				"the positive integer image clears every coefficient",
				SplitConj(
					Case(
						"the denominator image lies in the field and is nonzero",
						BySets(
							L,
							denominator,
							h,
							field.RingOn,
							characteristic_zero.IntegerMapHom.At(R),
							characteristic_zero.IntegerMapOfNum.At(R, d),
							comm_ring.CharacteristicZeroDef.At(R))),
					Case(
						"each coefficient is a member of the cleared image",
						BySets(denominator)),
				))
		})

		return ctx.Theorem(headline,
			func(a *Argument, L field.FieldFact[on.L], E *Expr[Set[A]], h Fact) {
				a.Iff()
				a.Forward(
					"clear rational relations by a nonzero integer scalar",
					func(b *Argument, independent Fact) {
						integerFacts := b.Conjuncts(
							b.Unfolded(independent, linear_independence.ModuleIndependentDef),
							"E lies in the field",
							"integer relations have zero coefficients")
						rationalRelations := b.Have(
							"every rational relation has zero coefficients",
							"∀T:set(A). ∀a:(A → A). "+
								"    finite(T) ∧ "+
								"    T ⊆ E ∧ "+
								"    (∀v:A. v ∈ T ⇒ a(v) ∈ rational_image(L)) ∧ "+
								"    module_sum(L.add, L.zero, T, λv:A. a(v) * v) = L.zero ⇒ "+
								"    ∀v:A. v ∈ T ⇒ a(v) = L.zero",
							Derive(func(c *Argument) {
								T := c.FixAs[Set[A]]()
								coeff := c.FixAs[Fun[A, A]]()
								relation := c.Assume()
								D, cleared := c.ObtainAs[A](
									"choose a nonzero scalar that makes the coefficients integral",
									"∃D:A. D ∈ L.carrier ∧ D ≠ L.zero ∧ (∀v:A. v ∈ T ⇒ D * a(v) ∈ integer_image(field_ring(L)))",
									By(L, h, relation, At(clearDenominators, c.TermAs[FieldOps[A]]("L"), T, coeff)))
								inField := c.Have(
									"the coefficients and the relation's vectors lie in the host field",
									"(∀v:A. v ∈ T ⇒ a(v) ∈ L.carrier) ∧ T ⊆ L.carrier",
									BySets(
										L,
										h,
										relation,
										characteristic_zero.RationalEmbedding.Read(L),
										field.SubfieldSubset.At(c.TermAs[FieldOps[A]]("L"), c.TermAs[Set[A]]("rational_image(L)"))))
								regular := module.RegularModuleOn.Read(field.RingOn.Read(L))
								scaledRelation := c.Have(
									"scaling the vanishing relation gives an integer relation",
									"module_sum(L.add, L.zero, T, λv:A. (D * a(v)) * v) = L.zero",
									By(
										inField,
										cleared,
										relation,
										At(linear_independence.CombinationScale.Read(regular), T, D, coeff),
										At(module.SmulZero.Read(regular), D)))
								scaledZero := c.Have(
									"integer independence annihilates the scaled coefficients",
									"∀v:A. v ∈ T ⇒ D * a(v) = L.zero",
									By(integerFacts[1].At(T, c.TermAs[Fun[A, A]]("λv:A. D * a(v)")), scaledRelation, cleared, relation))
								c.Show(
									"cancel the nonzero denominator image",
									By(Normalized, field.MulEqZeroOn.Read(L), scaledZero, inField, cleared))
							}))
						b.Show(
							"the finite-relation criterion gives rational independence",
							By(
								rationalRelations,
								integerFacts[0],
								linear_independence.ModuleIndependentDef.At(
									b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))"),
									b.TermAs[ModuleOps[A, A]]("regular_module(field_ring(L))"), E)))
					})
				a.Backward(
					"integer coefficients are rational coefficients",
					func(b *Argument, independent Fact) {
						rationalFacts := b.Unfolded(independent, linear_independence.ModuleIndependentDef)
						b.Show(
							"the rational criterion applies to every integer relation",
							Simp(Fwd(linear_independence.ModuleIndependentDef)),
							BySets(Normalized, L, rationalFacts, h, IntegerRationalImagesStructure.Read(L)))
					})
			})
	}),
})}

// IntegerBasisRationalSpan — a finite integer basis is a rational basis
// of the rational span, with dimension equal to its size: independence
// transfers, and leastness identifies the two rational spans.
var IntegerBasisRationalSpan = integerBasisRationalSpanThm{family.Add(registry.ProofEntry{
	Name: "IntegerBasisRationalSpan",
	Key:  "prop_2dd9dd1361a4ecf0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M E:set(A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"integer_lattice(field_ring(L), M)",
			"finite(E)",
			"module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
				"    restrict_module(regular_module(field_ring(L)), M), " +
				"    E)",
		},
		Conclusion: "module_basis(restrict_ring(field_ring(L), rational_image(L)), " +
			"    restrict_module(regular_module(field_ring(L)), " +
			"        module_span(restrict_ring(field_ring(L), rational_image(L)), " +
			"            regular_module(field_ring(L)), " +
			"            M)), " +
			"    E) ∧ " +
			"module_dim(restrict_ring(field_ring(L), rational_image(L)), " +
			"    restrict_module(regular_module(field_ring(L)), " +
			"        module_span(restrict_ring(field_ring(L), rational_image(L)), " +
			"            regular_module(field_ring(L)), " +
			"            M))) = " +
			"card(E)",
	}, func(a *Argument, L field.FieldFact[on.L], M, E *Expr[Set[A]], h Fact) {
		R := a.TermAs[RingOps[A]]("field_ring(L)")
		rationals := a.TermAs[Set[A]]("rational_image(L)")
		integerRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		rationalRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		ambient := a.TermAs[ModuleOps[A, A]]("regular_module(field_ring(L))")
		lattice := a.Have(
			"the lattice is an integer submodule of the field",
			"submodule(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    M)",
			By(h, IntegerLatticeDef.At(R, M)))
		images := a.Have(
			"the integer scalars form a ring inside the rational subfield",
			"subfield(L, rational_image(L)) ∧ "+
				"integer_image(field_ring(L)) ⊆ rational_image(L) ∧ "+
				"subring(field_ring(L), integer_image(field_ring(L)))",
			By(characteristic_zero.RationalEmbedding.Read(L), IntegerRationalImagesStructure.Read(L), h))
		modules := a.Conjuncts(
			a.Have(
				"the field is a module over its integer image and over its rational image",
				"module_on(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
					"    regular_module(field_ring(L))) ∧ "+
					"module_on(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)))",
				By(h, IntegerRationalImageModules.Read(L))),
			"the field is an integer module",
			"the field is a rational module")
		integerModule, rationalModule := modules[0], modules[1]
		integerBasis := a.Have(
			"the integer basis is independent in the field and spans the lattice",
			"module_independent(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    E) ∧ "+
				"module_span(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    regular_module(field_ring(L)), "+
				"    E) = "+
				"M",
			By(h, lattice, linear_independence.BasisRestrict.Read(integerModule).At(M, E)))
		basisParts := a.Conjuncts(
			integerBasis,
			"the basis is integer independent",
			"the integer span is the lattice")
		carriers := a.Have(
			"the basis lies in the lattice, and both lie in the field",
			"E ⊆ M ∧ M ⊆ L.carrier ∧ E ⊆ L.carrier",
			BySets(
				submodule.SubmoduleSubset.Read(lattice),
				basisParts[1],
				submodule.SubsetSpan.At(integerRing, ambient, E)))
		rationalIndependent := a.Have(
			"integer independence transfers to rational independence",
			"module_independent(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    E)",
			By(carriers, h, basisParts[0], IntegerRationalIndependence.Read(L).At(E)))

		W, spanE := a.LetAs[Set[A]](
			"W",
			"module_span(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), E)")
		N, spanM := a.LetAs[Set[A]](
			"N",
			"module_span(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), M)")
		spanOverQ := a.Have(
			"the rational span of the basis is a rational submodule",
			"submodule(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), W)",
			spanE.Rw(),
			By(carriers, submodule.SpanSubmodule.Read(rationalModule).At(E)))
		basisInSpan := a.Have(
			"the rational span contains the basis",
			"E ⊆ W",
			spanE.Rw(),
			By(submodule.SubsetSpan.At(rationalRing, ambient, E)))
		latticeInSpan := a.Have(
			"integer spanning places the whole lattice in the rational "+
				"span, an integer submodule by restriction of scalars",
			"M ⊆ W",
			basisParts[1].RwRev(),
			By(
				basisInSpan,
				images,
				submodule.SubmoduleRestrictScalars.Read(spanOverQ).At(integerRing),
				submodule.SpanLeast.At(integerRing, ambient, E, W)))
		latticeSpanInBasisSpan := a.Have(
			"leastness places the rational lattice span inside the basis span",
			"N ⊆ W",
			spanM.Rw(),
			By(latticeInSpan, spanOverQ, submodule.SpanLeast.At(rationalRing, ambient, M, W)))
		basisSpanInLatticeSpan := a.Have(
			"monotonicity gives the reverse inclusion",
			"W ⊆ N",
			spanE.Rw(),
			spanM.Rw(),
			By(carriers, submodule.SpanMono.At(rationalRing, ambient, E, M)))
		sameSpan := a.Have(
			"the basis and the lattice have the same rational span",
			"W = N",
			By(latticeSpanInBasisSpan, basisSpanInLatticeSpan, set_order.SubsetAntisym))
		spanSubmodule := a.Have(
			"the rational lattice span is a rational submodule",
			"submodule(restrict_ring(field_ring(L), rational_image(L)), regular_module(field_ring(L)), N)",
			sameSpan.RwRev(),
			By(spanOverQ))
		spans := a.Have(
			"the basis spans the rational lattice span",
			"module_span(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    E) = "+
				"N",
			CalcEq(
				Leg(
					W,
					"the basis span is W",
					By(Normalized, spanE)),
				FinalLeg(
					"the two spans agree",
					By(sameSpan)),
			))
		rationalBasis := a.Have(
			"the independent spanning set is a rational basis",
			"module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"    restrict_module(regular_module(field_ring(L)), N), "+
				"    E)",
			By(
				spans,
				rationalIndependent,
				spanSubmodule,
				linear_independence.BasisRestrict.Read(rationalModule).At(N, E)))
		restrictedModule := a.Have(
			"the rational span carries the restricted module structure",
			"module_on(restrict_ring(field_ring(L), rational_image(L)), "+
				"    restrict_module(regular_module(field_ring(L)), N))",
			By(spanSubmodule, submodule.SubmoduleModuleOn.Read(rationalModule).At(N)))
		inverse := a.TermAs[Fun[A, A]]("L.inv")
		dimension := a.Have(
			"the finite rational basis computes the dimension",
			"module_dim(restrict_ring(field_ring(L), rational_image(L)), "+
				"    restrict_module(regular_module(field_ring(L)), N)) = "+
				"card(E)",
			By(
				images,
				field.SubfieldRingSubfield.Read(L).At(rationals, rationals),
				h,
				rationalBasis,
				module_dimension.DimBasis.Read(restrictedModule).At(inverse, E)))
		a.Show(
			"the integer basis is a rational basis of the same finite dimension",
			By(dimension, rationalBasis))
	}),
})}

// FullLatticeBasisRational — an integer basis of a full integer lattice is
// a rational basis of the field, and on the lattice its rational coordinates
// are its integer ones: the basis is a rational basis of the lattice's
// rational span, which is the whole field, and since the integer scalars lie
// inside the rational ones, a lattice vector's coordinates over the smaller
// ring are its coordinates over the larger.
var FullLatticeBasisRational = fullLatticeBasisRationalThm{family.Add(registry.ProofEntry{
	Name: "FullLatticeBasisRational",
	Key:  "prop_26fd795aa0c4e6ab",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M F:set(A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"full_integer_lattice(L, M)",
			"finite(F)",
			"module_basis(«ℤ», restrict_module(regular_module(field_ring(L)), M), F)",
		},
		Conclusion: "module_basis(«ℚ», regular_module(field_ring(L)), F) ∧ " +
			"(∀v:A. " +
			"    v ∈ M ⇒ " +
			"    module_basis_coordinates(«ℚ», regular_module(field_ring(L)), F, v) = " +
			"    module_basis_coordinates(«ℤ», restrict_module(regular_module(field_ring(L)), M), F, v))",
		Abbrev: Abbrev{
			{Name: "ℤ", Text: "restrict_ring(field_ring(L), integer_image(field_ring(L)))"},
			{Name: "ℚ", Text: "restrict_ring(field_ring(L), rational_image(L))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		M, F *Expr[Set[A]],
		charZero, full, finite, integerBasis Fact,
	) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		ringL := a.TermAs[RingOps[A]]("field_ring(L)")
		Q := a.TermAs[Set[A]]("rational_image(L)")
		Z := a.TermAs[Set[A]]("integer_image(field_ring(L))")
		integersInQ := a.Conjuncts(
			GroupPremises(L, charZero, IntegerRationalImagesStructure.At(fieldL)),
			"the integer image lies in the rational image",
			"it is a commutative ring",
			"a principal ideal domain",
			"whose fractions are the rational image")[0]
		modules := a.Conjuncts(
			GroupPremises(L, charZero, IntegerRationalImageModules.At(fieldL)),
			"L is a module over its integer image",
			"and over its rational image")
		moduleZ, moduleQ := modules[0], modules[1]
		lattice := a.Unfolded(full, FullIntegerLatticeDef)
		carrier := a.Have(
			"the regular module has the field carrier",
			"regular_module(field_ring(L)).carrier = L.carrier",
			Simp(Fwd(module_record.RegularModuleDef), Fwd(field.FieldRingDef)),
			Basic())
		restrictL := a.Have(
			"restriction to the field carrier preserves the regular module",
			"restrict_module(regular_module(field_ring(L)), L.carrier) = regular_module(field_ring(L))",
			Simp(Rev(carrier), Fwd(module_record.RestrictModuleCarrier)),
			Basic())
		rationalBasis := a.Have(
			"the integer basis is a rational basis of the lattice's rational span, the field",
			"module_basis(«ℚ», regular_module(field_ring(L)), F)",
			By(charZero, lattice, finite, integerBasis, restrictL, IntegerBasisRationalSpan.Read(L).At(M, F)))
		integerData := a.Unfolded(lattice, IntegerLatticeDef)
		submoduleM := a.Have(
			"the lattice is an integer submodule of L",
			"submodule(«ℤ», regular_module(field_ring(L)), M)",
			By(integerData))
		coordinates := a.Have(
			"rational and integer coordinates agree on the lattice",
			Statement{
				Binders: "∀v:A.",
				Hypotheses: []string{
					"v ∈ M",
				},
				Conclusion: "module_basis_coordinates(«ℚ», regular_module(field_ring(L)), F, v) = " +
					"module_basis_coordinates(«ℤ», restrict_module(regular_module(field_ring(L)), M), F, v)",
			},
			By(
				module_record.RestrictRingTwice.At(ringL, Q, Z),
				integerData,
				submodule.SubmoduleModuleOn.Read(moduleZ).At(M),
				finite,
				integerBasis,
				rationalBasis,
				integersInQ,
				submodule.SubmoduleSubset.Read(submoduleM),
				module_dimension.BasisCoordinatesRestrict.Read(moduleQ).AsFact().At(Z, M, F)))
		a.Show(
			"the integer basis is a rational basis with the same coordinates on the lattice",
			By(rationalBasis, coordinates))
	}),
})}
