// finiteness.go — L as a finite extension of k(t), of degree the rank of
// either chart; a chart's finite quotients by a nonzero member and by a
// nonzero ideal; for an invertible pair, the bases of its charts over the
// polynomial rings, the sandwich between free line pairs that makes its
// cohomology finite, and the finite cohomology of its twists; and the finite
// chart quotients between pairs, of an invertible pair's meet with the
// structure pair inside both, and of an invertible pair inside a larger one.

package algebraic_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line_free_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The function field over k(t)
// ---------------------------------------------------------------------------

// ChartBasisSpansFunctionField — a finite basis of a chart over k[t]
// spans the function field over k(t): over k(t) the chart lies in the span
// of the basis, and L is the chart's fractions, so FiniteSubringSpansField
// makes that span all of L.
var ChartBasisSpansFunctionField = chartBasisSpansFunctionFieldThm{family.Add(registry.ProofEntry{
	Name: "ChartBasisSpansFunctionField",
	Key:  "prop_b1839d0ebd1685fb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀E:set(A).",
		Hypotheses: []string{
			"«wcDatum»",
			"finite(E)",
			"«wcBasisOfChart»(E)",
		},
		Conclusion: "«span» = L.carrier",
		Abbrev: Abbrev{
			{Name: "span", Text: "module_span(«wcRing»(«wcRationalFunctions»), «wcField», E)"},
		},
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		E *Expr[Set[A]],
		h Fact,
	) {
		fieldValue := arg.TermAs[field.FieldOps[A]]("L")
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
		fieldCarrier := arg.TermAs[Set[A]]("L.carrier")
		rationalFunctions := arg.TermAs[Set[A]]("«wcRationalFunctions»")
		scalars := arg.TermAs[RingOps[A]]("«wcRing»(«wcRationalFunctions»)")
		vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
		chartScalars := arg.TermAs[RingOps[A]]("«wcRing»(«wcPolynomials»)")
		chartVectors := arg.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(A₀)")
		curve := arg.Have(
			"the chart is a ring in L containing k[t]",
			"subfield(L, k) ∧ "+
				"t ∈ L.carrier ∧ "+
				"subring(field_ring(L), A₀) ∧ "+
				"A₀ ⊆ L.carrier ∧ "+
				"«wcPolynomials» ⊆ A₀",
			By(h, CurveOverItsLine.Read(L).At(k, A0, A1, A01, t), comm_ring.SubringSubset.At(fieldRing, A0)))
		generators := arg.Have(
			"k and t lie in L",
			"k ⊆ L.carrier ∧ {t} ⊆ L.carrier",
			BySets(curve, field.SubfieldSubset.At(fieldValue, k)))
		rationalField := arg.Have(
			"k(t) is a subfield of L",
			"subfield(L, «wcRationalFunctions»)",
			By(generators, algebraic_element.AdjoinSubfield.Read(L).At(k, arg.TermAs[Set[A]]("{t}"))))
		scalarData := arg.Have(
			"L is a module over k(t)",
			"subring(field_ring(L), «wcRationalFunctions») ∧ "+
				"module_on(«wcRing»(«wcRationalFunctions»), «wcField»)",
			By(rationalField, field_extension.SubfieldScalars.Read(L).At(rationalFunctions)))
		polynomialData := arg.Have(
			"the polynomial scalars lie in k(t)",
			"subring(field_ring(L), «wcPolynomials») ∧ «wcPolynomials» ⊆ «wcRationalFunctions»",
			By(curve, algebraic_element.PolynomialImageRing.Read(L).AsFact().At(k, t)))
		basis := arg.Have(
			"the given basis spans the chart",
			"module_independent(«wcRing»(«wcPolynomials»), «wcVectors»(A₀), E) ∧ "+
				"module_span(«wcRing»(«wcPolynomials»), «wcVectors»(A₀), E) = A₀",
			By(h, linear_independence.ModuleBasisDef.At(chartScalars, chartVectors, E)))
		basisInField := arg.Have(
			"basis elements lie in the chart and L",
			"E ⊆ A₀ ∧ E ⊆ L.carrier",
			By(
				basis,
				curve,
				linear_independence.IndependentInCarrier.At(chartScalars, chartVectors, E),
				set_order.SubsetTrans.At(E, A0, fieldCarrier)))
		chartSubmodule := arg.Have(
			"the chart is a k[t]-submodule of L",
			"submodule(«wcRing»(«wcPolynomials»), «wcField», A₀)",
			By(
				curve,
				fractional_ideal.SubringSubmodule.Read(L).At(A0),
				submodule.SubmoduleRestrictScalars.At(
					arg.TermAs[RingOps[A]]("«wcRing»(A₀)"), vectors, A0, chartScalars)))
		chartSpan := arg.Have(
			"the chart span is unchanged in the ambient module",
			"module_span(«wcRing»(«wcPolynomials»), «wcField», E) = A₀",
			By(
				h,
				CurveOverItsLine.Read(L).At(k, A0, A1, A01, t),
				basisInField,
				basis,
				chartSubmodule,
				linear_independence.SpanRestrict.At(chartScalars, vectors, A0, E)))
		chartInSpan := arg.Have(
			"the chart lies in its k(t)-span, which extending scalars makes the k(t)-span of E",
			"A₀ ⊆ «span»",
			By(
				scalarData,
				basisInField,
				polynomialData,
				chartSpan,
				submodule.SubsetSpan.At(scalars, vectors, A0),
				submodule.SpanOfSubringSpan.At(scalars, vectors, chartScalars, E)))
		arg.Show(
			"the chart's fractions fill L, and E, finite, spans the chart",
			By(
				rationalField,
				curve,
				h,
				CurveOverLineDef.At(fieldValue, k, t, A0, A1, A01),
				basisInField,
				chartInSpan,
				integral_element.FiniteSubringSpansField.Read(L).At(rationalFunctions, A0, E)))
	}),
})}

// FiniteOverRationalFunctions — the function field is a finite extension
// of k(t), and a basis of either chart over its polynomial ring is a
// basis of the function field over k(t): the rank of both charts is
// [L : k(t)].
var FiniteOverRationalFunctions = finiteOverRationalFunctionsThm{family.Add(registry.ProofEntry{
	Name: "FiniteOverRationalFunctions",
	Key:  "prop_4261ee6cd7a93f22",
	Reading: "The finite chart bases remain independent and span over k(t), " +
		"so their cardinalities are the extension degree. The datum supplies one " +
		"finite basis, and chart one uses the same argument after k(inv(t)) = k(t).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«wcDatum»",
		},
		Conclusion: "subfield(L, «wcRationalFunctions») ∧ " +
			"finite_extension(L, «wcRationalFunctions», L.carrier) ∧ " +
			"(∀E:set(A). finite(E) ∧ «wcBasisOfChart»(E) ⇒ «rationalBasis»(E) ∧ «fieldDegree» = card(E)) ∧ " +
			"(∀F:set(A). " +
			"    finite(F) ∧ «wcBasisOfInverseChart»(F) ⇒ «rationalBasis»(F) ∧ «fieldDegree» = card(F))",
		Abbrev: Abbrev{
			{Name: "rationalBasis", Text: "module_basis(«wcRing»(«wcRationalFunctions»), «wcField»)"},
			{Name: "fieldDegree", Text: "extension_degree(L, «wcRationalFunctions», L.carrier)"},
			{Name: "inverseRationalFunctions", Text: "field_adjoin(L, k, {L.inv(t)})"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			fieldValue := arg.TermAs[FieldOps[A]]("L")
			fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
			rationalFunctions := arg.TermAs[Set[A]]("«wcRationalFunctions»")
			inverseRationalFunctions := arg.TermAs[Set[A]]("«inverseRationalFunctions»")
			scalars := arg.TermAs[RingOps[A]]("«wcRing»(«wcRationalFunctions»)")
			inverseScalars := arg.TermAs[RingOps[A]]("«wcRing»(«inverseRationalFunctions»)")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			inv := arg.TermAs[Fun[A, A]]("L.inv")
			inverseT := arg.TermAs[A]("L.inv(t)")
			// L read as a module on its own carrier is L's regular module: the same record.
			onCarrier, regular :=
				module_record.RestrictModuleDef.At(vectors, arg.TermAs[Set[A]]("L.carrier")),
				module_record.RegularModuleDef.At(fieldRing)
			data := arg.Have(
				"the datum supplies the constant field, generator, and a finite chart basis",
				"subfield(L, k) ∧ t ∈ L.carrier ∧ (∃E:set(A). finite(E) ∧ «wcBasisOfChart»(E))",
				By(curve, CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			generators := arg.Have(
				"k and t lie in L",
				"k ⊆ L.carrier ∧ {t} ⊆ L.carrier",
				BySets(data, field.SubfieldSubset.At(fieldValue, k)))
			rationalField := arg.Have(
				"k(t) is a subfield containing k and t",
				"subfield(L, «wcRationalFunctions») ∧ k ⊆ «wcRationalFunctions» ∧ {t} ⊆ «wcRationalFunctions»",
				By(generators, algebraic_element.AdjoinSubfield.Read(L).At(k, arg.TermAs[Set[A]]("{t}"))))
			scalarData := arg.Have(
				"L is a module over the field k(t)",
				"module_on(«wcRing»(«wcRationalFunctions»), «wcField»)",
				By(rationalField, field_extension.SubfieldScalars.Read(L).At(rationalFunctions)))
			degreeOfBasis := arg.Have(
				"a finite basis of L over k(t) counts the extension degree",
				"∀S:set(A). finite(S) ∧ «rationalBasis»(S) ⇒ «fieldDegree» = card(S)",
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					basis := b.Assume()
					b.Show(
						"the extension module is the regular module, whose basis has size card(S)",
						Simp(Fwd(field_extension.ExtensionDegreeDef)),
						By(
							rationalField,
							field.SubfieldRingSubfield.Read(L).At(rationalFunctions, rationalFunctions),
							scalarData,
							basis,
							module_dimension.DimBasis.At(scalars, vectors, inv, S),
							onCarrier,
							regular))
				}))
			independentBasis := arg.Have(
				"a chart basis over the polynomials stays independent over the rational functions",
				Statement{
					Binders: "∀C D H:set(A). ∀s:A. ∀F:set(A).",
					Hypotheses: []string{
						"curve_over_line(L, k, s, C, D, H)",
						"module_basis(«wcRing»(polynomial_image(field_ring(L), k, s)), «wcVectors»(C), F)",
					},
					Conclusion: "module_independent(«wcRing»(field_adjoin(L, k, {s})), «wcField», F)",
				},
				Derive(func(b *Argument) {
					C, D, H := b.FixAs[Set[A]]("C"), b.FixAs[Set[A]]("D"), b.FixAs[Set[A]]("H")
					s := b.FixAs[A]("s")
					F := b.FixAs[Set[A]]("F")
					given := b.Assume()
					polynomials := b.TermAs[Set[A]]("polynomial_image(field_ring(L), k, s)")
					rationals := b.TermAs[Set[A]]("field_adjoin(L, k, {s})")
					polynomialScalars := b.TermAs[RingOps[A]]("«wcRing»(polynomial_image(field_ring(L), k, s))")
					chart := b.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(C)")
					line := b.Have(
						"the curve supplies its constant field, its generator, and a chart ring",
						"subfield(L, k) ∧ s ∈ L.carrier ∧ subring(field_ring(L), C)",
						By(given, CurveOverItsLine.Read(L).At(k, C, D, H, s)))
					rationalField := b.Have(
						"k(s) is a subfield of L",
						"subfield(L, field_adjoin(L, k, {s}))",
						By(
							line,
							field.SubfieldSubset.At(fieldValue, k),
							set_order.SingSubset.At(b.TermAs[Set[A]]("L.carrier"), s),
							algebraic_element.AdjoinSubfield.Read(L).At(k, b.TermAs[Set[A]]("{s}"))))
					independentInL := b.Have(
						"the chart basis stays independent over k[s] inside L",
						"module_independent(«wcRing»(polynomial_image(field_ring(L), k, s)), «wcField», F)",
						By(
							line,
							comm_ring.SubringSubset.At(fieldRing, C),
							given,
							linear_independence.ModuleBasisDef.At(polynomialScalars, chart, F),
							linear_independence.IndependentRestrict.At(polynomialScalars, vectors, C, F)))
					b.Show(
						"independence over k[s] passes to its fraction field k(s)",
						By(
							line,
							algebraic_element.PolynomialImageRing.Read(L).AsFact().At(k, s),
							rationalField,
							integral_element.RationalFunctionsFractionField.Read(L).AsFact().At(k, s),
							independentInL,
							integral_element.IndependentOverFractionField.Read(L).At(polynomials, rationals, F)))
				}))
			chartZero := arg.Have(
				"a finite basis of chart zero over k[t] is a basis of L over k(t) whose size is the degree",
				"∀E:set(A). finite(E) ∧ «wcBasisOfChart»(E) ⇒ «rationalBasis»(E) ∧ «fieldDegree» = card(E)",
				Derive(func(b *Argument) {
					E := b.FixAs[Set[A]]("E")
					given := b.Assume()
					basis := b.Have(
						"independent over k(t) and spanning L over it, E is a basis of L over k(t)",
						"«rationalBasis»(E)",
						By(
							given,
							curve,
							independentBasis.At(A0, A1, A01, t, E),
							ChartBasisSpansFunctionField.Read(L).At(k, A0, A1, A01, t, E),
							linear_independence.ModuleBasisDef.At(scalars, vectors, E),
							module_record.RegularModuleDef.At(fieldRing)))
					b.Show(
						"E is a basis and its cardinality is the degree",
						By(degreeOfBasis.At(E), given, basis))
				}))
			finiteExtension := arg.Have(
				"L is a finite extension of k(t)",
				"finite_extension(L, «wcRationalFunctions», L.carrier)",
				Derive(func(b *Argument) {
					E, given := b.ObtainAs[Set[A]](
						"choose a finite chart-zero basis from the datum",
						"∃E:set(A). finite(E) ∧ «wcBasisOfChart»(E)",
						By(data))
					b.Show(
						"that same E is a finite basis of the extension module",
						Simp(Fwd(field_extension.FiniteExtensionDef)),
						Simp(Fwd(module_dimension.FiniteDimensionalDef)),
						Witness(E),
						By(chartZero.At(E), given, onCarrier, regular))
				}))
			inverseField := arg.Have(
				"adjoining inv(t) also gives a subfield of L",
				"L.inv(t) ∈ L.carrier ∧ "+
					"subfield(L, «inverseRationalFunctions») ∧ "+
					"k ⊆ «inverseRationalFunctions» ∧ "+
					"{L.inv(t)} ⊆ «inverseRationalFunctions»",
				BySets(
					generators,
					field.InvIn.Read(L).AsFact().At(t),
					algebraic_element.AdjoinSubfield.Read(L).At(k, arg.TermAs[Set[A]]("{L.inv(t)}"))))
			otherGenerator := arg.Have(
				"each generated subfield contains the other's generator",
				"L.inv(t) ∈ «wcRationalFunctions» ∧ t ∈ «inverseRationalFunctions»",
				BySets(
					data,
					rationalField,
					inverseField,
					field.SubfieldInv.At(fieldValue, rationalFunctions, t),
					field.SubfieldInv.At(fieldValue, inverseRationalFunctions, inverseT),
					field.InvInvOn.Read(L).AsFact().At(t)))
			sameField := arg.Have(
				"k(inv(t)) is k(t)",
				"«inverseRationalFunctions» = «wcRationalFunctions»",
				Derive(func(b *Argument) {
					inclusions := b.Have(
						"leastness gives the two inclusions",
						"«inverseRationalFunctions» ⊆ «wcRationalFunctions» ∧ "+
							"«wcRationalFunctions» ⊆ «inverseRationalFunctions»",
						BySets(
							otherGenerator,
							rationalField,
							inverseField,
							algebraic_element.AdjoinLeast.Read(L).At(k, b.TermAs[Set[A]]("{L.inv(t)}"), rationalFunctions),
							algebraic_element.AdjoinLeast.Read(L).At(k, b.TermAs[Set[A]]("{t}"), inverseRationalFunctions)))
					b.Show(
						"the generated subfields coincide",
						By(inclusions, set_order.SubsetAntisym.At(inverseRationalFunctions, rationalFunctions)))
				}))
			swapped := arg.Have(
				"the inverse coordinate exchanges the charts",
				"curve_over_line(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, CurveSwap.Read(L).At(k, A0, A1, A01, t)))
			chartOne := arg.Have(
				"a finite basis of chart one over k[inv(t)] is a basis of L over k(t) whose size is the degree",
				"∀F:set(A). finite(F) ∧ «wcBasisOfInverseChart»(F) ⇒ «rationalBasis»(F) ∧ «fieldDegree» = card(F)",
				Derive(func(b *Argument) {
					F := b.FixAs[Set[A]]("F")
					given := b.Assume()
					basis := b.Have(
						"independent over k(inv(t)) and spanning L over it, F is a basis of L over k(inv(t))",
						"module_basis(«wcRing»(«inverseRationalFunctions»), «wcField», F)",
						By(
							given,
							swapped,
							independentBasis.At(A1, A0, A01, inverseT, F),
							ChartBasisSpansFunctionField.Read(L).At(k, A1, A0, A01, inverseT, F),
							linear_independence.ModuleBasisDef.At(inverseScalars, vectors, F),
							module_record.RegularModuleDef.At(fieldRing)))
					b.Show(
						"over the same subfield k(t), F is a basis and counts the degree",
						By(degreeOfBasis.At(F), sameField, given, basis))
				}))
			arg.Show(
				"the function field is finite over k(t), with either chart basis counting its degree",
				By(chartZero, chartOne, rationalField, finiteExtension))
		}),
})}

// ElementAlgebraicOverRationalFunctions — every element of the function
// field is algebraic over k(t): L is a finite extension of its subfield k(t).
var ElementAlgebraicOverRationalFunctions = elementAlgebraicOverRationalFunctionsThm{family.Add(registry.ProofEntry{
	Name: "ElementAlgebraicOverRationalFunctions",
	Key:  "prop_908e664f5c2ed0b6",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t a:A.",
		Hypotheses: []string{
			"«wcDatum»",
			"a ∈ L.carrier",
		},
		Conclusion: "algebraic_over(L, «wcRationalFunctions», a)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t, a *Expr[A],
		curve, aIn Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("L")
		rational := arg.TermAs[Set[A]]("«wcRationalFunctions»")
		arg.Show(
			"a lies in L, a finite extension of its subfield k(t)",
			By(
				curve,
				aIn,
				FiniteOverRationalFunctions.Read(L).At(k, A0, A1, A01, t),
				field.CarrierSubfield.Read(L),
				field.SubfieldSubset.At(ops, rational),
				algebraic_element.FiniteExtensionAlgebraic.Read(L).At(
					rational, arg.TermAs[Set[A]]("L.carrier"), a)))
	}),
})}

// ---------------------------------------------------------------------------
// Principal ideals of the charts
// ---------------------------------------------------------------------------

// PrincipalColengthFinite — a chart ring modulo the principal ideal of a
// nonzero member is finite-dimensional over k.
var PrincipalColengthFinite = principalColengthFiniteThm{family.Add(registry.ProofEntry{
	Name: "PrincipalColengthFinite",
	Key:  "prop_15cb21159ee619d6",
	Reading: "The argument spends a ≠ zero once: multiplication by a is then onto L, so a · " +
		"A₀ spans L over k(t) as A₀ does, and principal_ideal_domain.FullSubmoduleQuotientFinite, " +
		"given the datum's finite basis of A₀ over k[t], makes A₀/aA₀ finite-dimensional; chart 1 " +
		"likewise, through the swapped curve. The hypothesis cannot be dropped: A₀ modulo {zero} " +
		"is A₀, infinite-dimensional over k since t is transcendental.",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«wcDatum»"},
		Conclusion: "(∀a:A. " +
			"    a ∈ A₀ ∧ a ≠ L.zero ⇒ " +
			"    finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(A₀), image(L.mul(a), A₀)))) ∧ " +
			"(∀a:A. " +
			"    a ∈ A₁ ∧ a ≠ L.zero ⇒ " +
			"    finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(A₁), image(L.mul(a), A₁))))",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		curve Fact,
	) {
		oneChart := arg.Have(
			"the first chart of any curve has finite principal colength",
			Statement{
				Binders:    "∀C D H:set(A). ∀s b:A.",
				Hypotheses: []string{"curve_over_line(L, k, s, C, D, H)", "b ∈ C", "b ≠ L.zero"},
				Conclusion: "finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(C), image(L.mul(b), C)))",
			},
			Derive(func(p *Argument) {
				C, D, H := p.FixAs[Set[A]]("C"), p.FixAs[Set[A]]("D"), p.FixAs[Set[A]]("H")
				s, b := p.FixAs[A]("s"), p.FixAs[A]("b")
				principal := p.Assume()
				P, polynomialImage := p.LetAs[Set[A]]("P", "polynomial_image(field_ring(L), k, s)")
				rationalFunctions, generatedField := p.LetAs[Set[A]]("rationalFunctions", "field_adjoin(L, k, {s})")
				I, principalImage := p.LetAs[Set[A]]("I", "image(L.mul(b), C)")
				ring := p.TermAs[RingOps[A]]("field_ring(L)")
				fieldRecord := p.TermAs[FieldOps[A]]("L")
				vectors := p.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
				chart := p.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(C)")
				polynomialRing := p.TermAs[RingOps[A]]("«wcRing»(P)")
				rationalRing := p.TermAs[RingOps[A]]("«wcRing»(rationalFunctions)")
				chartRing := p.TermAs[RingOps[A]]("«wcRing»(C)")
				data := p.Have(
					"the curve supplies its polynomial scalar ring and a finite chart basis",
					"subfield(L, k) ∧ "+
						"s ∈ L.carrier ∧ "+
						"subring(field_ring(L), P) ∧ "+
						"P ⊆ C ∧ "+
						"subring(field_ring(L), C) ∧ "+
						"(∃E:set(A). finite(E) ∧ module_basis(«wcRing»(P), «wcVectors»(C), E))",
					By(principal, polynomialImage, CurveOverItsLine.Read(L).At(k, C, D, H, s)))
				E, basis := p.ObtainAs[Set[A]](
					"choose the datum's finite basis of C over P",
					"∃E:set(A). finite(E) ∧ module_basis(«wcRing»(P), «wcVectors»(C), E)",
					By(data),
					Named("E"))
				carriers := p.Have(
					"the polynomial ring, chart, and nonzero multiplier lie in L",
					"P ⊆ L.carrier ∧ C ⊆ L.carrier ∧ b ∈ L.carrier",
					BySets(Normalized, data, principal, comm_ring.SubringSubset.At(ring, C)))
				sInL := p.MemberOf[on.L](s, p.Have(
					"the curve parameter lies in L",
					"s ∈ L.carrier",
					By(data)))
				bInL := p.MemberOf[on.L](b, p.Have(
					"the principal multiplier lies in L",
					"b ∈ L.carrier",
					By(carriers)))
				fieldData := p.Have(
					"k(s) is a subfield of L",
					"subfield(L, rationalFunctions)",
					By(
						Normalized,
						data,
						sInL,
						generatedField,
						field.SubfieldSubset.At(fieldRecord, k),
						set_order.SingSubset.At(p.TermAs[Set[A]]("L.carrier"), s),
						algebraic_element.AdjoinSubfield.Read(L).At(k, p.TermAs[Set[A]]("{s}"))))
				modules := p.Have(
					"L is a module over k(s) and C",
					"module_on(«wcRing»(rationalFunctions), «wcField») ∧ module_on(«wcRing»(C), «wcField»)",
					By(
						fieldData,
						data,
						fractional_ideal.FieldModuleOn.Read(L).At(C),
						field_extension.SubfieldScalars.Read(L).At(rationalFunctions)))
				chartOverP := p.Have(
					"C is a P-submodule of L",
					"submodule(«wcRing»(P), «wcField», C)",
					By(
						data,
						fractional_ideal.SubringSubmodule.Read(L).At(C),
						submodule.SubmoduleRestrictScalars.At(chartRing, vectors, C, polynomialRing)))
				basisSpans := p.Have(
					"the chart basis spans the function field over k(s)",
					"module_span(«wcRing»(rationalFunctions), «wcField», E) = L.carrier",
					By(
						Normalized,
						principal,
						basis,
						polynomialImage,
						generatedField,
						ChartBasisSpansFunctionField.Read(L).At(k, C, D, H, s, E)))
				chartSpan := p.TermAs[Set[A]]("module_span(«wcRing»(rationalFunctions), «wcField», C)")
				chartSpans := p.Have(
					"C therefore spans L over k(s)",
					"module_span(«wcRing»(rationalFunctions), «wcField», C) = L.carrier",
					By(
						basisSpans,
						basis,
						linear_independence.BasisInCarrier.At(polynomialRing, chart, E),
						carriers,
						modules,
						submodule.SpanMono.At(rationalRing, vectors, E, C),
						submodule.SpanSubmodule.At(rationalRing, vectors, C),
						submodule.SubmoduleSubset.At(rationalRing, vectors, chartSpan),
						set_order.SubsetAntisym.At(chartSpan, p.TermAs[Set[A]]("L.carrier"))))
				linearOverRationalFunctions := p.Have(
					"multiplication by b is k(s)-linear on L",
					"module_homomorphism(«wcRing»(rationalFunctions), «wcField», «wcField», L.mul(b))",
					By(fieldData, field_extension.MultiplicationLinear.Read(L).At(rationalFunctions, bInL)))
				linearOverP := p.Have(
					"multiplication by b is also P-linear on L",
					"module_homomorphism(«wcRing»(P), «wcField», «wcField», L.mul(b))",
					By(
						modules,
						data,
						principal,
						module_homomorphism.ScalingLinearOverSubring.At(ring, C, P, vectors, b)))
				idealOverP := p.Have(
					"bC is a P-submodule of L",
					"submodule(«wcRing»(P), «wcField», I)",
					By(
						Normalized,
						linearOverP,
						chartOverP,
						principalImage,
						module_homomorphism.HomImageSubmodule.At(
							polynomialRing, vectors, vectors, p.TermAs[Fun[A, A]]("L.mul(b)"), C)))
				idealSpans := p.Have(
					"bC spans L because multiplication by nonzero b maps L onto L",
					"module_span(«wcRing»(rationalFunctions), «wcField», I) = L.carrier",
					By(
						chartSpans,
						linearOverRationalFunctions,
						carriers,
						principal,
						principalImage,
						linear_independence.HomSpan.At(rationalRing, vectors, vectors, p.TermAs[Fun[A, A]]("L.mul(b)"), C),
						field.MulBijective.Read(L).At(bInL)))
				productsInC := p.Have(
					"multiplication by b preserves C",
					"∀u:A. u ∈ C ⇒ b * u ∈ C",
					Derive(func(q *Argument) {
						u := q.FixAs[A]("u")
						inC := q.Assume()
						q.Show(
							"C is closed under multiplication",
							By(inC, data, principal, comm_ring.SubringMul.At(ring, C, b, u)))
					}))
				idealInC := p.Have(
					"bC lies in C",
					"I ⊆ C",
					By(
						Normalized,
						principalImage,
						productsInC,
						set_image.ImageSubsetIff.At(p.TermAs[Fun[A, A]]("L.mul(b)"), C, C)))
				p.Show(
					"bC is a P-submodule of the free chart C spanning it over k(s), so C/bC is finite-dimensional",
					By(
						data,
						chartOverP,
						basis,
						idealOverP,
						idealInC,
						idealSpans,
						carriers,
						polynomialImage,
						generatedField,
						principal_ideal_domain.FullSubmoduleQuotientFinite.Read(L).At(k, C, I, E, sInL)))
			}))
		arg.Show(
			"apply the chart argument in both orientations",
			By(oneChart, curve, CurveSwap.Read(L).At(k, A0, A1, A01, t)))
	}),
})}

// NonzeroIdealFiniteColength — a chart ring modulo a nonzero ideal is
// finite-dimensional over k: the chart is a subring of L holding k whose
// quotients by its nonzero members are finite-dimensional
// (PrincipalColengthFinite), so ideal_colength.NonzeroIdealQuotientFinite
// applies. Chart 1 is chart 0 of the swapped curve.
var NonzeroIdealFiniteColength = nonzeroIdealFiniteColengthThm{family.Add(registry.ProofEntry{
	Name: "NonzeroIdealFiniteColength",
	Key:  "prop_40762c4821f744be",
	Reading: "I ≠ {zero} is load-bearing: A₀ modulo {zero} is " +
		"A₀, infinite-dimensional over k since t is transcendental.",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀I:set(A).",
		Hypotheses: []string{"«wcDatum»"},
		Conclusion: "(ring_ideal(«wcRing»(A₀), I) ∧ I ≠ {L.zero} ⇒ " +
			"    finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(A₀), I))) ∧ " +
			"(ring_ideal(«wcRing»(A₁), I) ∧ I ≠ {L.zero} ⇒ " +
			"    finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(A₁), I)))",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		I *Expr[Set[A]],
		curve Fact,
	) {
		oneChart := arg.Have(
			"the first chart of any curve has finite colength at the nonzero ideal I",
			Statement{
				Binders: "∀C D H:set(A). ∀s:A.",
				Hypotheses: []string{
					"curve_over_line(L, k, s, C, D, H)",
					"ring_ideal(«wcRing»(C), I)",
					"I ≠ {L.zero}",
				},
				Conclusion: "finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(C), I))",
			},
			Derive(func(p *Argument) {
				C, D, H := p.FixAs[Set[A]]("C"), p.FixAs[Set[A]]("D"), p.FixAs[Set[A]]("H")
				s := p.FixAs[A]("s")
				given := p.Conjuncts(
					p.Assume(),
					"C is the first chart of a curve over the line of s",
					"I is an ideal of C",
					"I is not the zero ideal")
				chartCurve, ideal, nonzero := given[0], given[1], given[2]
				data := p.Have(
					"k is a subfield of L inside the subring C",
					"subfield(L, k) ∧ subring(field_ring(L), C) ∧ k ⊆ C",
					BySets(chartCurve, CurveOverItsLine.Read(L).At(k, C, D, H, s)))
				p.Show(
					"C modulo each nonzero principal ideal is finite-dimensional "+
						"over k, so C modulo the nonzero ideal I is too",
					By(
						data,
						chartCurve,
						PrincipalColengthFinite.Read(L).At(k, C, D, H, s),
						ideal,
						nonzero,
						ideal_colength.NonzeroIdealQuotientFinite.Read(L).At(k, C, I)))
			}))
		arg.Show(
			"apply the chart argument in both orientations",
			By(oneChart, curve, CurveSwap.Read(L).At(k, A0, A1, A01, t)))
	}),
})}

// ---------------------------------------------------------------------------
// Invertible pairs: free over the polynomial rings, and the sandwich
// ---------------------------------------------------------------------------

// InvertibleFreeBasis — each chart of an invertible pair is free of
// finite rank over its polynomial ring: fst(M) has a finite basis over
// k[t] and snd(M) one over k[1/t], as the datum gives the structure pair.
var InvertibleFreeBasis = invertibleFreeBasisThm{family.Add(registry.ProofEntry{
	Name: "InvertibleFreeBasis",
	Key:  "prop_7bfbb6c331be90f",
	Reading: "The datum hands the structure pair its bases; an invertible pair gets them from " +
		"the structure theory of modules over the principal ideal domain k[t]: fst(M) is finitely " +
		"generated over A₀ and so over k[t], and torsion-free inside the field. Invertibility enters " +
		"only through finite generation. Each basis has [L : k(t)] members, as the datum's do, since " +
		"fst(M) spans L over k(t) — not stated here, where finiteness is all the sandwich asks.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
		},
		Conclusion: "(∃E:set(A). " +
			"    finite(E) ∧ module_basis(«wcRing»(«wcPolynomials»), «wcVectors»(fst(M)), E)) ∧ " +
			"(∃F:set(A). finite(F) ∧ module_basis(«wcRing»(«wcInversePolynomials»), «wcVectors»(snd(M)), F))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the curve datum",
				"and an invertible pair on it")
			datum := a.Simplified(GroupPremises(hypotheses[0], CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))
			basis0 := a.Have(
				"chart 0 is free of finite rank over k[t]",
				"∃E:set(A). finite(E) ∧ «wcBasisOfChart»(E)",
				By(datum))
			basis1 := a.Have(
				"and chart 1 over k[1/t]",
				"∃E:set(A). finite(E) ∧ «wcBasisOfInverseChart»(E)",
				By(datum))

			chart0 := a.Have(
				"chart 0 is a subring of L",
				"subring(field_ring(L), A₀)",
				By(datum))
			chart1 := a.Have(
				"and so is chart 1",
				"subring(field_ring(L), A₁)",
				By(datum))
			ideals := a.Conjuncts(
				a.Unfolded(hypotheses[1], invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) one of A₁",
				"M is a lattice pair over A₀₁")

			principal0 := a.Have(
				"t is transcendental, so k[t] is a principal ideal domain",
				"principal_ideal_domain(«wcRing»(«wcPolynomials»))",
				By(datum, principal_ideal_domain.PolynomialImagePrincipalIdealDomain.Read(L).At(k, tm)))
			principal1 := a.Have(
				"so is k[1/t], inv(t) being transcendental too",
				"principal_ideal_domain(«wcRing»(«wcInversePolynomials»))",
				By(
					datum,
					principal_ideal_domain.PolynomialImagePrincipalIdealDomain.Read(L).At(
						k, field.InvIn.Read(L).At(tm))))

			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			fstM, sndM := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")

			// Chart 0, over k[t].
			E, chartBasis0 := a.UnpackAs[Set[A]](basis0, "E")
			ofE := a.Conjuncts(
				chartBasis0,
				"E is finite",
				"E is a basis of chart 0 over k[t]")
			onE := a.Conjuncts(
				a.Unfolded(ofE[1], linear_independence.ModuleBasisDef),
				"E is independent over k[t]",
				"E spans chart 0 over k[t]")
			chartGenerated0 := a.Have(
				"so chart 0 is finitely generated over k[t], by its basis E, which lies in it",
				"module_finitely_generated(«wcRing»(«wcPolynomials»), «wcVectors»(A₀))",
				Unfold(principal_ideal_domain.FinitelyGeneratedDef),
				Witness(E),
				By(ofE[0], onE[1], linear_independence.IndependentInCarrier.Read(onE[0])))
			over0 := a.Have(
				"L is a module over chart 0",
				"module_on(«wcRing»(A₀), «wcField»)",
				By(chart0, fractional_ideal.FieldModuleOn.Read(L).At(A0)))
			fractional0 := a.Conjuncts(
				a.Unfolded(ideals[0], fractional_ideal.InvertibleFractionalDef),
				"fst(M) is an A₀-submodule of L",
				"whose product with its inverse is A₀")
			G, generators0 := a.UnpackAs[Set[A]](
				GroupPremises(
					chart0, ideals[0], invertible_fractional_ideal.InvertibleGenerated.Read(L).At(A0, fstM)),
				"G")
			ofG := a.Conjuncts(
				generators0,
				"G is finite",
				"G lies in fst(M)",
				"G spans fst(M) over A₀ inside L")
			generated0 := a.Have(
				"so fst(M), invertible, is finitely generated over "+
					"chart 0, G spanning it inside itself as inside L",
				"module_finitely_generated(«wcRing»(A₀), «wcVectors»(fst(M)))",
				Unfold(principal_ideal_domain.FinitelyGeneratedDef),
				Witness(G),
				By(
					ofG[0],
					ofG[1],
					ofG[2],
					fractional0[0],
					linear_independence.SpanningRestrict.Read(over0).At(fstM, G),
					module_record.RestrictModuleDef.At(vectors, fstM)))
			free0 := a.Have(
				"fst(M), a finitely generated A₀-submodule of L, is free of finite rank over k[t]",
				"∃E:set(A). finite(E) ∧ module_basis(«wcRing»(«wcPolynomials»), «wcVectors»(fst(M)), E)",
				By(
					datum,
					chart0,
					principal0,
					chartGenerated0,
					fractional0[0],
					generated0,
					principal_ideal_domain.FinitelyGeneratedFree.Read(L).At(
						a.TermAs[Set[A]]("«wcPolynomials»"), A0, fstM)))

			// Chart 1, over k[1/t].
			F, chartBasis1 := a.UnpackAs[Set[A]](basis1, "F")
			ofF := a.Conjuncts(
				chartBasis1,
				"F is finite",
				"F is a basis of chart 1 over k[1/t]")
			onF := a.Conjuncts(
				a.Unfolded(ofF[1], linear_independence.ModuleBasisDef),
				"F is independent over k[1/t]",
				"F spans chart 1 over k[1/t]")
			chartGenerated1 := a.Have(
				"so chart 1 is finitely generated over k[1/t], by its basis F, which lies in it",
				"module_finitely_generated(«wcRing»(«wcInversePolynomials»), «wcVectors»(A₁))",
				Unfold(principal_ideal_domain.FinitelyGeneratedDef),
				Witness(F),
				By(ofF[0], onF[1], linear_independence.IndependentInCarrier.Read(onF[0])))
			over1 := a.Have(
				"L is a module over chart 1",
				"module_on(«wcRing»(A₁), «wcField»)",
				By(chart1, fractional_ideal.FieldModuleOn.Read(L).At(A1)))
			fractional1 := a.Conjuncts(
				a.Unfolded(ideals[1], fractional_ideal.InvertibleFractionalDef),
				"snd(M) is an A₁-submodule of L",
				"whose product with its inverse is A₁")
			H, generators1 := a.UnpackAs[Set[A]](
				GroupPremises(
					chart1, ideals[1], invertible_fractional_ideal.InvertibleGenerated.Read(L).At(A1, sndM)),
				"H")
			ofH := a.Conjuncts(
				generators1,
				"H is finite",
				"H lies in snd(M)",
				"H spans snd(M) over A₁ inside L")
			generated1 := a.Have(
				"so snd(M), invertible, is finitely generated over "+
					"chart 1, H spanning it inside itself as inside L",
				"module_finitely_generated(«wcRing»(A₁), «wcVectors»(snd(M)))",
				Unfold(principal_ideal_domain.FinitelyGeneratedDef),
				Witness(H),
				By(
					ofH[0],
					ofH[1],
					ofH[2],
					fractional1[0],
					linear_independence.SpanningRestrict.Read(over1).At(sndM, H),
					module_record.RestrictModuleDef.At(vectors, sndM)))
			free1 := a.Have(
				"snd(M), a finitely generated A₁-submodule of L, is free of finite rank over k[1/t]",
				"∃F:set(A). finite(F) ∧ module_basis(«wcRing»(«wcInversePolynomials»), «wcVectors»(snd(M)), F)",
				By(
					datum,
					chart1,
					principal1,
					chartGenerated1,
					fractional1[0],
					generated1,
					principal_ideal_domain.FinitelyGeneratedFree.Read(L).At(
						a.TermAs[Set[A]]("«wcInversePolynomials»"), A1, sndM)))
			a.Show(
				"each chart of M is free of finite rank over its polynomial ring",
				By(free0, free1))
		}),
})}

// InvertibleSandwich — in a basis E of fst(M) over k[t], the ambient of
// an invertible pair M is the k[t, 1/t]-span of E and snd(M) lies between
// the k[1/t]-spans of t^(−N) · E and t^N · E for one N: M sits between
// the free line pairs O(−N)^E and O(N)^E written in E; and the same with
// the charts exchanged.
var InvertibleSandwich = invertibleSandwichThm{family.Add(registry.ProofEntry{
	Name: "InvertibleSandwich",
	Key:  "prop_6a8ff6bd922fae46",
	Reading: "The half in E is InvertibleSandwichChart at M. The half in F is the same statement for " +
		"the curve read from chart 1: with inv(t) for t and A₀, A₁ exchanged the datum is again a curve " +
		"over the line (CurveSwap), and (snd(M), fst(M)) is an invertible pair of it with the ambient of " +
		"M (InvertiblePairSwap); InvertibleSandwichChart there speaks of inv(inv(t)) and of k[1/t] with " +
		"inv(t) inverted, which inv(inv(t)) = t and LaurentThroughInverse read back as t and k[t, 1/t].",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
		},
		Conclusion: "(∀E:set(A). " +
			"    finite(E) ∧ module_basis(«wcRing»(«wcPolynomials»), «wcVectors»(fst(M)), E) ⇒ " +
			"    lattice_pair_ambient(«wcOverlap», «wcField», M) = " +
			"    module_span(«wcRing»(«wcLaurent»), «wcField», E) ∧ " +
			"    (∃N:num. " +
			"        module_span(«wcRing»(«wcInversePolynomials»), " +
			"            «wcField», " +
			"            {L.mul(monoid_pow(L.mul, L.one, L.inv(t), N), e) | e:A | e ∈ E}) ⊆ " +
			"        snd(M) ∧ " +
			"        snd(M) ⊆ " +
			"        module_span(«wcRing»(«wcInversePolynomials»), " +
			"            «wcField», " +
			"            {L.mul(monoid_pow(L.mul, L.one, t, N), e) | e:A | e ∈ E}))) ∧ " +
			"(∀F:set(A). " +
			"    finite(F) ∧ module_basis(«wcRing»(«wcInversePolynomials»), «wcVectors»(snd(M)), F) ⇒ " +
			"    lattice_pair_ambient(«wcOverlap», «wcField», M) = " +
			"    module_span(«wcRing»(«wcLaurent»), «wcField», F) ∧ " +
			"    (∃N:num. " +
			"        module_span(«wcRing»(«wcPolynomials»), " +
			"            «wcField», " +
			"            {L.mul(monoid_pow(L.mul, L.one, t, N), f) | f:A | f ∈ F}) ⊆ " +
			"        fst(M) ∧ " +
			"        fst(M) ⊆ " +
			"        module_span(«wcRing»(«wcPolynomials»), " +
			"            «wcField», " +
			"            {L.mul(monoid_pow(L.mul, L.one, L.inv(t), N), f) | f:A | f ∈ F})))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the curve over the line",
				"M is an invertible pair")
			curve := hypotheses[0]
			datum := a.Simplified(GroupPremises(hypotheses[0], CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))

			swappedCurve := a.Have(
				"read from chart 1, with inv(t) for t, the datum is again a curve over the line",
				"curve_over_line(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, CurveSwap.Read(L).At(k, A0, A1, A01, t)))
			swappedPair := a.Conjuncts(
				GroupPremises(hypotheses[1], invertible_lattice_pair.InvertiblePairSwap.Read(L).At(A0, A1, A01, M)),
				"with its charts exchanged M is an invertible pair of that curve",
				"whose ambient is the ambient of M")
			inverseInverse := a.Have(
				"inv(inv(t)) is t",
				"L.inv(L.inv(t)) = t",
				By(field.InvInvOn.Read(L).At(tm)))
			laurent := a.Have(
				"the Laurent ring read through inv(t) is k[t, 1/t]",
				"ring_away(field_ring(L), «wcInversePolynomials», L.inv(t)) = «wcLaurent»",
				By(datum, projective_line.LaurentThroughInverse.Read(L).At(k, tm)))
			// The sandwich is cited with its basis still quantified, a partial
			// instantiation the typed At (which takes E) does not spell.
			exchanged := a.TermAs[_LatticePair]("(snd(M), fst(M))")
			chartOne := a.Simplified(
				GroupPremises(
					swappedCurve,
					swappedPair[0],
					Read(InvertibleSandwichChart, L).At(k, A1, A0, A01, a.TermAs[A]("L.inv(t)"), exchanged)),
				Fwd(inverseInverse),
				Fwd(pairs.Fst),
				Fwd(pairs.Snd),
				Fwd(swappedPair[1]),
				Fwd(laurent))
			a.Show(
				"chart 0 is the sandwich at M, and chart 1 the sandwich read from chart 1",
				By(
					curve,
					hypotheses[1],
					swappedCurve,
					swappedPair[0],
					Read(InvertibleSandwichChart, L).At(k, A0, A1, A01, t, M),
					chartOne))
		}),
})}

// InvertibleSandwichChart — the sandwich read from chart 0: in a finite
// basis E of fst(M) over k[t], the ambient of an invertible pair M is the
// k[t, 1/t]-span of E, and snd(M) lies between the k[1/t]-spans of
// inv(t)ᴺ · E and tᴺ · E for one N. The ambient is M's ambient on the line
// (CurvePairOnLine), the k[t, 1/t]-span of fst(M), and fst(M) is the
// k[t]-span of E. The ambient is also snd(M) localized at inv(t), so a
// power of inv(t) brings each e ∈ E into snd(M), and one power all of the
// finite E. A finite basis F of snd(M) over k[1/t] lies in the ambient,
// the k[1/t]-span of E localized at inv(t), so one power inv(t)ᴺ brings F
// into that span, and tᴺ carries that span onto the span of tᴺ · E.
var InvertibleSandwichChart = invertibleSandwichChartThm{family.Add(registry.ProofEntry{
	Name: "InvertibleSandwichChart",
	Key:  "prop_5986148a07e4560a",
	Reading: "Of the basis only its spanning is used: E lies in fst(M) and spans it " +
		"over k[t]; its independence plays no part. E finite gives the one N of the lower " +
		"bound, an exponent beyond those its members need; the upper bound needs snd(M) " +
		"finitely generated over k[1/t], which invertibility gives (InvertibleFreeBasis).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)). ∀E:set(A).",
		Hypotheses: []string{
			"«wcDatum»",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
			"finite(E) ∧ module_basis(«wcRing»(«wcPolynomials»), «wcVectors»(fst(M)), E)",
		},
		Conclusion: "lattice_pair_ambient(«wcOverlap», «wcField», M) = " +
			"module_span(«wcRing»(«wcLaurent»), «wcField», E) ∧ " +
			"(∃N:num. " +
			"    module_span(«wcRing»(«wcInversePolynomials»), " +
			"        «wcField», " +
			"        {L.mul(monoid_pow(L.mul, L.one, L.inv(t), N), e) | e:A | e ∈ E}) ⊆ " +
			"    snd(M) ∧ " +
			"    snd(M) ⊆ " +
			"    module_span(«wcRing»(«wcInversePolynomials»), " +
			"        «wcField», " +
			"        {L.mul(monoid_pow(L.mul, L.one, t, N), e) | e:A | e ∈ E}))",
		Abbrev: Abbrev{
			// The k[t, 1/t]-span and the k[1/t]-span of a set, and that of E localized at inv(t).
			{Name: "laurentSpan", Text: "module_span(«wcRing»(«wcLaurent»), «wcField»)"},
			{Name: "inverseSpan", Text: "module_span(«wcRing»(«wcInversePolynomials»), «wcField», E)"},
			{Name: "localizedSpan", Text: "{v:A | " +
				"    v ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) * v ∈ «inverseSpan»)}"},
			// One exponent N = n₁ + n₂ serves both bounds: tᴺ and inv(t)ᴺ, the sets inv(t)ᴺ · E and tᴺ · E, and the k[1/t]-span of the latter.
			{Name: "powerT", Text: "monoid_pow(L.mul, L.one, t, n₁ + n₂)"},
			{Name: "powerInvT", Text: "monoid_pow(L.mul, L.one, L.inv(t), n₁ + n₂)"},
			{Name: "lowerSet", Text: "{L.mul(«powerInvT», e) | e:A | e ∈ E}"},
			{Name: "upperSet", Text: "{L.mul(«powerT», e) | e:A | e ∈ E}"},
			{Name: "upperSpan", Text: "module_span(«wcRing»(«wcInversePolynomials»), «wcField», «upperSet»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
			E *Expr[Set[A]],
			basisGiven Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the curve over the line",
				"M is an invertible pair")
			invertible := hypotheses[1]
			datum := a.Simplified(GroupPremises(hypotheses[0], CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))

			// The line.
			inverseInLaurent := a.Have(
				"k[1/t] lies in k[t, 1/t]",
				"«wcInversePolynomials» ⊆ «wcLaurent»",
				By(datum))
			laurentSubring := a.Have(
				"k[t, 1/t] is a subring of L",
				"subring(field_ring(L), «wcLaurent»)",
				By(datum))
			inverseSubring := a.Have(
				"k[1/t] is a subring of L",
				"subring(field_ring(L), «wcInversePolynomials»)",
				By(datum))
			invTInInverse := a.Have(
				"holding inv(t)",
				"L.inv(t) ∈ «wcInversePolynomials»",
				By(datum))
			overInverse := a.Have(
				"L is a module over k[1/t]",
				"module_on(«wcRing»(«wcInversePolynomials»), «wcField»)",
				By(datum))
			overLaurent := a.Have(
				"and over k[t, 1/t]",
				"module_on(«wcRing»(«wcLaurent»), «wcField»)",
				By(datum))
			overPolynomials := a.Have(
				"and over k[t]",
				"module_on(«wcRing»(«wcPolynomials»), «wcField»)",
				By(datum))
			inverseInL := a.Have(
				"so k[1/t] lies in L",
				"«wcInversePolynomials» ⊆ L.carrier",
				BySets(inverseInLaurent, comm_ring.SubringSubset.Read(laurentSubring)))

			// The pair.
			pair := a.Conjuncts(
				a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(M) is an invertible fractional ideal of A₀",
				"snd(M) is one of A₁",
				"M is a lattice pair over the overlap")
			lattice := a.Conjuncts(
				a.Unfolded(pair[2], lattice_pair.LatticePairDef),
				"L is a module over the overlap",
				"fst(M) is an A₀-submodule of L",
				"snd(M) is an A₁-submodule of L",
				"the two charts span one submodule")
			overOverlap, firstChart, secondChart, sameSpan := lattice[0], lattice[1], lattice[2], lattice[3]
			overlapOps := a.TermAs[module_record.RingOps[A]]("«wcOverlap»")
			laurentOps := a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)")
			polynomialOps := a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcPolynomials»)")
			inverseOps := a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcInversePolynomials»)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			polynomialSet, inverseSet :=
				a.TermAs[Set[A]]("«wcPolynomials»"), a.TermAs[Set[A]]("«wcInversePolynomials»")
			first, second := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("snd(M)")
			invT := a.TermAs[A]("L.inv(t)")
			firstOverPolynomials := a.Have(
				"fst(M) is a k[t]-submodule of L, k[t] lying in A₀",
				"submodule(«wcRing»(«wcPolynomials»), «wcField», fst(M))",
				By(submodule.SubmoduleRestrictScalars.Read(firstChart).At(polynomialOps), datum))
			secondOverInverse := a.Have(
				"and snd(M) a k[1/t]-submodule, k[1/t] lying in A₁",
				"submodule(«wcRing»(«wcInversePolynomials»), «wcField», snd(M))",
				By(submodule.SubmoduleRestrictScalars.Read(secondChart).At(inverseOps), datum))

			// The ambient.
			basis := a.Conjuncts(
				basisGiven,
				"E is finite",
				"E is a basis of fst(M) over k[t]")
			finiteE := basis[0]
			spanned := a.Conjuncts(
				a.Have(
					"a basis of the k[t]-submodule fst(M) spans it inside "+
						"fst(M), so it lies in fst(M) and spans it inside L",
					"E ⊆ fst(M) ∧ module_span(«wcRing»(«wcPolynomials»), «wcField», E) = fst(M)",
					By(
						firstOverPolynomials,
						a.Unfolded(basis[1], linear_independence.ModuleBasisDef),
						module_record.RestrictModuleDef.At(vectors, first),
						linear_independence.SpanningRestrict.Read(overPolynomials).At(first, E))),
				"E lies in fst(M)",
				"fst(M) is the k[t]-span of E")
			eInFirst, firstIsSpan := spanned[0], spanned[1]
			eInL := a.Have(
				"so E lies in L",
				"E ⊆ L.carrier",
				BySets(eInFirst, submodule.SubmoduleSubset.Read(firstChart)))
			onLine := a.Conjuncts(
				GroupPremises(hypotheses[0], pair[2], CurvePairOnLine.Read(L).At(k, A0, A1, A01, t, M)),
				"M is a lattice pair on the line",
				"with the curve's ambient",
				"and the curve's H¹")
			ambient := a.Have(
				"so the ambient is the k[t, 1/t]-span of E",
				"lattice_pair_ambient(«wcOverlap», «wcField», M) = «laurentSpan»(E)",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«laurentSpan»(fst(M))"),
						"the ambient is M's ambient on the line, the k[t, 1/t]-span of fst(M)",
						By(onLine[1], lattice_pair.LatticePairAmbientDef.At(laurentOps, vectors, M))),
					Leg(
						a.TermAs[Set[A]]("«laurentSpan»(module_span(«wcRing»(«wcPolynomials»), «wcField», E))"),
						"fst(M) is the k[t]-span of E",
						firstIsSpan.Rw(),
						Basic()),
					FinalLeg(
						"and the k[t, 1/t]-span of the k[t]-span of E is the k[t, 1/t]-span of E",
						By(submodule.SpanOfSubringSpan.Read(overLaurent).At(polynomialOps, E), datum, eInL)),
				))

			// The lower bound.
			onSecond := a.Have(
				"the A₀₁-span of snd(M) is snd(M) localized at inv(t)",
				"module_span(«wcOverlap», «wcField», snd(M)) = "+
					"{v:A | v ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) * v ∈ snd(M))}",
				By(
					lattice_pair.ChartSpanAway.At(overlapOps, A1, A0, invT, t, vectors, second),
					lattice_pair.BiaffineSwap.At(overlapOps, A0, A1, t, invT),
					datum,
					overOverlap,
					secondChart))
			secondMembers := a.Have(
				"so its members are the members of L a power of inv(t) brings into snd(M)",
				"∀v:A. "+
					"    v ∈ module_span(«wcOverlap», «wcField», snd(M)) ⇔ "+
					"    v ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) * v ∈ snd(M))",
				BySets(onSecond))
			lowerPowers := a.Have(
				"a power of inv(t) brings each e ∈ E into snd(M): e lies in fst(M), so in the span of snd(M)",
				"∀e:A. e ∈ E ⇒ ∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) * e ∈ snd(M)",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					inE := b.Assume()
					inSpan := b.Have(
						"e lies in the A₀₁-span of fst(M), which is that of snd(M)",
						"e ∈ module_span(«wcOverlap», «wcField», snd(M))",
						sameSpan.RwRev(),
						BySets(inE, eInFirst, submodule.SubsetSpan.At(overlapOps, vectors, first)))
					b.Show(
						"so a power of inv(t) brings it into snd(M)",
						By(secondMembers.At(e), inSpan))
				}))
			n1, lower := a.ObtainAs[Nat](
				"so from one exponent n₁ on, every power of inv(t) brings all of the finite E into snd(M)",
				"∃n:num. ∀m:num. n ≤ m ⇒ ∀e:A. e ∈ E ⇒ monoid_pow(L.mul, L.one, L.inv(t), m) * e ∈ snd(M)",
				By(
					inverseInL,
					inverseSubring,
					invTInInverse,
					secondOverInverse,
					finiteE,
					eInL,
					lowerPowers,
					ring_away.CommonPower.Read(L).At(inverseSet, second, E, invT)),
				Named("n₁"))

			// The upper bound.
			bases := a.Conjuncts(
				GroupPremises(hypotheses[0], hypotheses[1], InvertibleFreeBasis.Read(L).At(k, A0, A1, A01, t, M)),
				"fst(M) has a finite basis over k[t]",
				"snd(M) has a finite basis over k[1/t]")
			F, fGiven := a.UnpackAs[Set[A]](bases[1], "F")
			fBasis := a.Conjuncts(
				fGiven,
				"F is finite",
				"F is a basis of snd(M) over k[1/t]")
			fSpanned := a.Conjuncts(
				a.Have(
					"a basis of the k[1/t]-submodule snd(M) spans it inside "+
						"snd(M), so it lies in snd(M) and spans it inside L",
					"F ⊆ snd(M) ∧ module_span(«wcRing»(«wcInversePolynomials»), «wcField», F) = snd(M)",
					By(
						secondOverInverse,
						a.Unfolded(fBasis[1], linear_independence.ModuleBasisDef),
						module_record.RestrictModuleDef.At(vectors, second),
						linear_independence.SpanningRestrict.Read(overInverse).At(second, F))),
				"F lies in snd(M)",
				"snd(M) is the k[1/t]-span of F")
			fInL := a.Have(
				"so F lies in L",
				"F ⊆ L.carrier",
				BySets(fSpanned[0], submodule.SubmoduleSubset.Read(secondChart)))
			spanE := a.TermAs[Set[A]]("«inverseSpan»")
			spanESubmodule := a.Have(
				"the k[1/t]-span of E is a k[1/t]-submodule of L",
				"submodule(«wcRing»(«wcInversePolynomials»), «wcField», «inverseSpan»)",
				By(submodule.SpanSubmodule.Read(overInverse).At(E), eInL))
			spanEOverLine := a.Have(
				"so a submodule over the line's chart 1",
				"submodule(restrict_ring(«wcRing»(«wcLaurent»), «wcInversePolynomials»), «wcField», «inverseSpan»)",
				By(submodule.SubmoduleRestrictScalars.Read(spanESubmodule), set_order.SubsetRefl.At(inverseSet)))
			laurentAway := a.Have(
				"the k[t, 1/t]-span of E is the k[1/t]-span of E localized at inv(t)",
				"«laurentSpan»(E) = «localizedSpan»",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«laurentSpan»(«inverseSpan»)"),
						"it is the k[t, 1/t]-span of the k[1/t]-span of E",
						By(submodule.SpanOfSubringSpan.Read(overLaurent).At(inverseOps, E), inverseInLaurent, eInL)),
					FinalLeg(
						"which is that span localized at inv(t)",
						By(
							lattice_pair.ChartSpanAway.At(laurentOps, inverseSet, polynomialSet, invT, t, vectors, spanE),
							lattice_pair.BiaffineSwap.At(laurentOps, polynomialSet, inverseSet, t, invT),
							datum,
							overLaurent,
							spanEOverLine)),
				))
			ambientMembers := a.Have(
				"so the members of the ambient are the members of L "+
					"a power of inv(t) brings into the k[1/t]-span of E",
				"∀v:A. "+
					"    v ∈ lattice_pair_ambient(«wcOverlap», «wcField», M) ⇔ "+
					"    v ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) * v ∈ «inverseSpan»)",
				ambient.Rw(),
				BySets(laurentAway))
			contains := a.Conjuncts(
				GroupPremises(pair[2], lattice_pair.AmbientContains.At(overlapOps, A0, A1, vectors, M)),
				"the ambient is an A₀₁-submodule of L",
				"holding fst(M)",
				"and snd(M)")
			upperPowers := a.Have(
				"a power of inv(t) brings each f ∈ F into the "+
					"k[1/t]-span of E: f lies in snd(M), so in the ambient",
				"∀f:A. f ∈ F ⇒ ∃n:num. monoid_pow(L.mul, L.one, L.inv(t), n) * f ∈ «inverseSpan»",
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					inF := b.Assume()
					inAmbient := b.Have(
						"f lies in the ambient",
						"f ∈ lattice_pair_ambient(«wcOverlap», «wcField», M)",
						BySets(inF, fSpanned[0], contains[2]))
					b.Show(
						"so a power of inv(t) brings it into the span of E",
						By(ambientMembers.At(f), inAmbient))
				}))
			n2, upper := a.ObtainAs[Nat](
				"so from one exponent n₂ on, every power of inv(t) "+
					"brings all of the finite F into the k[1/t]-span of E",
				"∃n:num. ∀m:num. n ≤ m ⇒ ∀f:A. f ∈ F ⇒ monoid_pow(L.mul, L.one, L.inv(t), m) * f ∈ «inverseSpan»",
				By(
					inverseInL,
					inverseSubring,
					invTInInverse,
					spanESubmodule,
					fBasis[0],
					fInL,
					upperPowers,
					ring_away.CommonPower.Read(L).At(inverseSet, spanE, F, invT)),
				Named("n₂"))

			N := a.TermAs[Nat]("n₁ + n₂")
			ringL := field.RingOn.Read(L)
			powersL := comm_ring.MulMonoidOn.Read(ringL)
			invTm := field.InvIn.Read(L).At(tm)
			tN, invTN := comm_monoid.PowIn.Read(powersL).At(tm, N), comm_monoid.PowIn.Read(powersL).At(invTm, N)
			unit := a.Have(
				"t · inv(t) = one, so tᴺ · inv(t)ᴺ = one",
				"«powerT» * «powerInvT» = L.one",
				By(comm_monoid.PowInverseOn.Read(powersL).At(tm, invTm, N), datum))
			lowerAtN := a.Have(
				"inv(t)ᴺ brings every e ∈ E into snd(M), N being at least n₁",
				"∀e:A. e ∈ E ⇒ «powerInvT» * e ∈ snd(M)",
				By(lower.At(N), nat_order.LessEqAdd.At(n1, n2)))
			lowerInSecond := a.Have(
				"so inv(t)ᴺ · E lies in snd(M)",
				"«lowerSet» ⊆ snd(M)",
				Simp(Fwd(set_image.SimpleImage), Fwd(set_image.ImageSubsetIff)),
				By(lowerAtN))
			lowerBound := a.Have(
				"and snd(M), a k[1/t]-submodule, holds its k[1/t]-span",
				"module_span(«wcRing»(«wcInversePolynomials»), «wcField», «lowerSet») ⊆ snd(M)",
				By(
					submodule.SpanLeast.At(inverseOps, vectors, a.TermAs[Set[A]]("«lowerSet»"), second),
					secondOverInverse,
					lowerInSecond))
			upperAtN := a.Have(
				"inv(t)ᴺ brings every f ∈ F into the k[1/t]-span of E, N being at least n₂",
				"∀f:A. f ∈ F ⇒ «powerInvT» * f ∈ «inverseSpan»",
				By(upper.At(N), nat_order.LessEqAddLeft.At(n1, n2)))
			scale := a.TermAs[Fun[A, A]]("L.mul(«powerT»)")
			scaled := a.Have(
				"multiplication by tᴺ carries the k[1/t]-span of E onto the k[1/t]-span of tᴺ · E",
				"image(L.mul(«powerT»), «inverseSpan») = "+
					"module_span(«wcRing»(«wcInversePolynomials»), «wcField», image(L.mul(«powerT»), E))",
				By(
					linear_independence.HomSpan.At(inverseOps, vectors, vectors, scale, E),
					field_extension.ScaleLinear.Read(L).At(inverseSet, tN),
					inverseInL,
					inverseSubring,
					eInL))
			image := a.Have(
				"tᴺ · E is the image of E under multiplication by tᴺ",
				"image(L.mul(«powerT»), E) = «upperSet»",
				By(set_image.SimpleImage.At(scale, E)))
			eachInUpper := a.Have(
				"each f ∈ F is tᴺ · (inv(t)ᴺ · f), the image of a member of the k[1/t]-span of E",
				"∀f:A. f ∈ F ⇒ f ∈ «upperSpan»",
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					inF := b.Assume()
					fL := b.Have(
						"f lies in L",
						"f ∈ L.carrier",
						BySets(inF, fInL))
					pulled := b.TermAs[A]("«powerInvT» * f")
					imaged := b.Have(
						"tᴺ · (inv(t)ᴺ · f) is the image of a member of the span of E",
						"«powerT» * («powerInvT» * f) ∈ image(L.mul(«powerT»), «inverseSpan»)",
						By(set_image.FunInImage.At(scale, spanE, pulled), upperAtN.At(f), inF))
					back := b.Have(
						"and it is f",
						"«powerT» * («powerInvT» * f) = f",
						ByArith(ringL, fL, tN, invTN, Scaled(f, unit)))
					b.Show(
						"so f lies in the k[1/t]-span of tᴺ · E, the image of the k[1/t]-span of E",
						image.RwRev(),
						scaled.RwRev(),
						By(imaged, back))
				}))
			fInUpper := a.Have(
				"so F lies in the k[1/t]-span of tᴺ · E",
				"F ⊆ «upperSpan»",
				By(eachInUpper, set_basic.SubsetDef))
			upperInL := a.Have(
				"tᴺ · E lies in L",
				"«upperSet» ⊆ L.carrier",
				Simp(Fwd(set_image.SimpleImage), Fwd(set_image.ImageSubsetIff)),
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					inE := b.Assume()
					em := b.MemberOf[on.L](e, b.Have(
						"e lies in L",
						"e ∈ L.carrier",
						BySets(inE, eInL)))
					b.Show(
						"so does tᴺ · e, a product of members of L",
						By(comm_ring.MulIn.Read(ringL).At(tN, em)))
				}))
			upperBound := a.Have(
				"so snd(M), the k[1/t]-span of F, lies in the k[1/t]-span of tᴺ · E",
				"snd(M) ⊆ «upperSpan»",
				fSpanned[1].RwRev(),
				By(
					submodule.SpanLeast.At(inverseOps, vectors, F, a.TermAs[Set[A]]("«upperSpan»")),
					submodule.SpanSubmodule.Read(overInverse).At(a.TermAs[Set[A]]("«upperSet»")),
					upperInL,
					fInUpper))
			a.Show(
				"the ambient is the k[t, 1/t]-span of E, and snd(M) "+
					"lies between the k[1/t]-spans of inv(t)ᴺ · E and tᴺ · E",
				SplitConj(
					Case(
						"the ambient is the k[t, 1/t]-span of E",
						By(ambient)),
					Case(
						"the one exponent N = n₁ + n₂ squeezes snd(M)",
						Derive(func(b *Argument) {
							b.Take(N)
							b.Show(
								"between the two spans",
								By(lowerBound, upperBound))
						})),
				))
		}),
})}

// InvertibleFinite — every invertible lattice pair of a curve has
// finite-dimensional cohomology: in a finite basis E of chart 0 over k[t],
// M has the chart 0 of the free line pairs O(N)^E and O(−N)^E and the
// ambient of O(−N)^E, and its chart 1 lies between theirs, so H⁰(M) is a
// subspace of H⁰(O(N)^E) and H¹(M) a quotient of H¹(O(−N)^E), both
// finite-dimensional on the line.
var InvertibleFinite = invertibleFiniteThm{family.Add(registry.ProofEntry{
	Name: "InvertibleFinite",
	Key:  "prop_4a5a2daf22023660",
	Reading: "Invertibility is load-bearing: it gives chart 0 its finite basis over k[t] and chart " +
		"1 its upper bound (InvertibleFreeBasis). A lattice pair need not have finite cohomology: (L, " +
		"L) is one, and its H⁰ is all of L, infinite-dimensional over k since t is transcendental.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
		},
		Conclusion: "lattice_pair_finite(«wcOverlap», k, «wcField», M)",
		Abbrev: Abbrev{
			{Name: "sandwichLower", Text: "{L.mul(monoid_pow(L.mul, L.one, L.inv(t), N), e) | e:A | e ∈ E}"},
			{Name: "sandwichUpper", Text: "{L.mul(monoid_pow(L.mul, L.one, t, N), e) | e:A | e ∈ E}"},
			{Name: "invertibleFiniteLaurentOverK", Text: "restrict_ring(«wcRing»(«wcLaurent»), k)"},
			{Name: "invertibleFiniteOverK", Text: "restrict_ring(«wcOverlap», k)"},
			{Name: "invertibleFiniteUp", Text: "projective_line_free_pair(L, k, t, E, λe:A. &N)"},
			{Name: "invertibleFiniteDown", Text: "projective_line_free_pair(L, k, t, E, λe:A. -&N)"},
			{Name: "invertibleFiniteUpSections", Text: "fst(«invertibleFiniteUp») ∩ snd(«invertibleFiniteUp»)"},
			{Name: "invertibleFiniteDownSum", Text: "set_mul(L.add, " +
				"    fst(«invertibleFiniteDown»), " +
				"    snd(«invertibleFiniteDown»))"},
			{Name: "invertibleFiniteChartSum", Text: "set_mul(L.add, fst(M), snd(M))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the curve datum",
				"M is an invertible pair")
			invertible := hypotheses[1]
			overlapOps, laurentOps :=
				a.TermAs[module_record.RingOps[A]]("«wcOverlap»"),
				a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcLaurent»)")
			polynomialOps, overK :=
				a.TermAs[module_record.RingOps[A]]("«wcRing»(«wcPolynomials»)"),
				a.TermAs[module_record.RingOps[A]]("«invertibleFiniteOverK»")
			V := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
			polynomials, inversePolynomials :=
				a.TermAs[Set[A]]("«wcPolynomials»"), a.TermAs[Set[A]]("«wcInversePolynomials»")
			first, sections := a.TermAs[Set[A]]("fst(M)"), a.TermAs[Set[A]]("fst(M) ∩ snd(M)")
			// The field's inverse, with which k is a field under its scalars' operations.
			inv := a.TermAs[Fun[A, A]]("L.inv")

			datum := a.Simplified(GroupPremises(hypotheses[0], CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			tm := a.MemberOf[on.L](t, a.Have(
				"t lies in L",
				"t ∈ L.carrier",
				By(datum)))
			subfield := a.Have(
				"k is a subfield of L",
				"subfield(L, k)",
				By(datum))
			kField := a.Have(
				"k is a field",
				"field_on(restrict_field(L, k))",
				By(datum))
			kRing := a.Have(
				"so k is a commutative ring under the overlap's operations",
				"comm_ring_on(restrict_ring(«wcOverlap», k))",
				By(
					field.RingOn.Read(kField),
					field.FieldRingDef.At(a.TermAs[field.FieldOps[A]]("restrict_field(L, k)")),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("«wcOverlap»"), k)))
			kInCharts := a.Conjuncts(
				a.Have(
					"k lies in both charts",
					"k ⊆ A₀ ∧ k ⊆ A₁",
					BySets(datum)),
				"k lies in chart 0",
				"k lies in chart 1")
			overlapRing := a.Have(
				"the overlap, a subring of L, is a ring",
				"comm_ring_on(«wcOverlap»)",
				By(datum, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A01)))
			kInOverlap := a.Have(
				"k lies in the overlap, as chart 0 does",
				"k ⊆ A₀₁",
				BySets(datum))
			kSubring := a.Have(
				"so k is a subring of the overlap",
				"subring(«wcOverlap», k)",
				By(kRing, kInOverlap, comm_ring.SubringRingOn.Read(overlapRing).At(k)))
			vectorSpaceK := a.Have(
				"L is a vector space over k",
				"module_on(«invertibleFiniteLaurentOverK», «wcField»)",
				By(datum))
			overPolynomials := a.Have(
				"and a module over k[t]",
				"module_on(«wcRing»(«wcPolynomials»), «wcField»)",
				By(datum))
			overLaurent := a.Have(
				"and over k[t, 1/t]",
				"module_on(«wcRing»(«wcLaurent»), «wcField»)",
				By(datum))
			lattice := a.Have(
				"M is a lattice pair over the overlap",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», M)",
				By(a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef)))
			chart0 := a.Have(
				"chart 0 of M is an A₀-submodule of L",
				"submodule(restrict_ring(«wcOverlap», A₀), «wcField», fst(M))",
				By(a.Unfolded(lattice, lattice_pair.LatticePairDef)))
			chartsInL := a.Have(
				"the charts of M lie in L",
				"fst(M) ⊆ L.carrier ∧ snd(M) ⊆ L.carrier",
				By(invertible, invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M)))

			bases := a.Conjuncts(
				GroupPremises(hypotheses[0], hypotheses[1], InvertibleFreeBasis.Read(L).At(k, A0, A1, A01, t, M)),
				"chart 0 of M has a finite basis over k[t]",
				"chart 1 of M has a finite basis over k[1/t]")
			E, basisE := a.UnpackAs[Set[A]](bases[0], "E")
			finiteBasis := a.Conjuncts(
				basisE,
				"E is finite",
				"E is a basis of chart 0 over k[t]")
			finiteE, basis := finiteBasis[0], finiteBasis[1]
			inChart := a.Conjuncts(
				a.Unfolded(basis, linear_independence.ModuleBasisDef),
				"E is independent over k[t] in chart 0",
				"E spans chart 0 over k[t] inside chart 0")
			restricted := module_record.RestrictModuleDef.At(V, first)
			spanning := a.Conjuncts(
				a.Have(
					"so E lies in chart 0 and spans it over k[t] inside L",
					"E ⊆ fst(M) ∧ module_span(«wcRing»(«wcPolynomials»), «wcField», E) = fst(M)",
					By(
						datum,
						submodule.SubmoduleRestrictScalars.Read(chart0).At(polynomialOps),
						inChart[1],
						restricted,
						linear_independence.SpanningRestrict.Read(overPolynomials).At(first, E))),
				"E lies in chart 0",
				"E spans chart 0 over k[t] inside L")
			EinL := a.Have(
				"so E lies in L",
				"E ⊆ L.carrier",
				BySets(spanning[0], chartsInL))
			independent := a.Have(
				"and E is independent over k[t] in L",
				"module_independent(«wcRing»(«wcPolynomials»), «wcField», E)",
				By(
					inChart[0],
					restricted,
					chartsInL,
					linear_independence.IndependentRestrict.At(polynomialOps, V, first, E)))

			sandwich := a.Conjuncts(
				GroupPremises(
					hypotheses[0],
					hypotheses[1],
					finiteBasis[0],
					finiteBasis[1],
					InvertibleSandwichChart.Read(L).At(k, A0, A1, A01, t, M, E)),
				"the ambient of M is the k[t, 1/t]-span of E",
				"for some N, chart 1 of M lies between the two spans")
			_, between := a.UnpackAs[Nat](sandwich[1], "N")
			bounds := a.Conjuncts(
				between,
				"the k[1/t]-span of the t⁻ᴺ · e lies in chart 1 of M",
				"chart 1 of M lies in the k[1/t]-span of the tᴺ · e")
			lower, upper := bounds[0], bounds[1]

			// The free line pairs O(N)^E and O(−N)^E along E, every e twisted by N and by −N.
			nUp, nDown := a.TermAs[Fun[A, Int]]("λe:A. &N"), a.TermAs[Fun[A, Int]]("λe:A. -&N")
			up, down :=
				a.TermAs[_LatticePair]("«invertibleFiniteUp»"), a.TermAs[_LatticePair]("«invertibleFiniteDown»")
			upCharts := a.Conjuncts(
				a.Have(
					"O(N)^E has chart 0 the k[t]-span of E and chart 1 the k[1/t]-span of the tᴺ · e",
					"fst(«invertibleFiniteUp») = module_span(«wcRing»(«wcPolynomials»), «wcField», E) ∧ "+
						"snd(«invertibleFiniteUp») = "+
						"module_span(«wcRing»(«wcInversePolynomials»), «wcField», «sandwichUpper»)",
					Simp(
						Fwd(projective_line_free_pair.ProjectiveLineFreePairDef),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd),
						Fwd(laurent_polynomial.LaurentMonomialOfNum)),
					Basic()),
				"chart 0 of O(N)^E",
				"chart 1 of O(N)^E")
			downCharts := a.Conjuncts(
				a.Have(
					"O(−N)^E has chart 0 the k[t]-span of E and chart 1 the k[1/t]-span of the t⁻ᴺ · e",
					"fst(«invertibleFiniteDown») = module_span(«wcRing»(«wcPolynomials»), «wcField», E) ∧ "+
						"snd(«invertibleFiniteDown») = "+
						"module_span(«wcRing»(«wcInversePolynomials»), «wcField», «sandwichLower»)",
					Simp(
						Fwd(projective_line_free_pair.ProjectiveLineFreePairDef),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd),
						Fwd(laurent_polynomial.LaurentMonomialOfNum)),
					Basic()),
				"chart 0 of O(−N)^E",
				"chart 1 of O(−N)^E")
			upLattice := a.Have(
				"O(N)^E is a lattice pair on the line",
				"lattice_pair(«wcRing»(«wcLaurent»), "+
					"    «wcPolynomials», "+
					"    «wcInversePolynomials», "+
					"    «wcField», "+
					"    «invertibleFiniteUp»)",
				By(datum, EinL, projective_line_free_pair.FreeLinePairIsLattice.Read(L).At(k, tm, E, nUp)))
			downLattice := a.Have(
				"so is O(−N)^E",
				"lattice_pair(«wcRing»(«wcLaurent»), "+
					"    «wcPolynomials», "+
					"    «wcInversePolynomials», "+
					"    «wcField», "+
					"    «invertibleFiniteDown»)",
				By(datum, EinL, projective_line_free_pair.FreeLinePairIsLattice.Read(L).At(k, tm, E, nDown)))
			upFinite := a.Have(
				"H⁰(O(N)^E) is finite-dimensional over k",
				"finite_dimensional(«invertibleFiniteLaurentOverK», "+
					"    lattice_pair_h0(«wcField», «invertibleFiniteUp»))",
				By(
					datum,
					finiteE,
					independent,
					projective_line_free_pair.FreeLinePairH0Dim.Read(L).At(k, tm, E, nUp)))
			downFinite := a.Have(
				"H¹(O(−N)^E) is finite-dimensional over k",
				"finite_dimensional(«invertibleFiniteLaurentOverK», "+
					"    lattice_pair_h1(«wcRing»(«wcLaurent»), «wcField», «invertibleFiniteDown»))",
				By(
					datum,
					finiteE,
					independent,
					projective_line_free_pair.FreeLinePairH1Dim.Read(L).At(k, tm, E, nDown)))
			ringsAgree := a.Have(
				"read on k, the line's ring and the overlap's are both the field's ring on k",
				"«invertibleFiniteLaurentOverK» = «invertibleFiniteOverK»",
				Unfold(module_record.RestrictRingDef))

			a.Show(
				"both cohomology spaces of M are finite-dimensional over k",
				Simp(Fwd(lattice_pair.LatticePairFiniteDef)),
				SplitConj(
					Case(
						"H⁰(M) is finite-dimensional, a k-subspace of H⁰(O(N)^E)",
						Derive(func(b *Argument) {
							upSections := b.TermAs[Set[A]]("«invertibleFiniteUpSections»")
							sectionsInside := b.Have(
								"every section of M is one of O(N)^E: the two share "+
									"chart 0, and chart 1 of M lies in that of O(N)^E",
								"fst(M) ∩ snd(M) ⊆ «invertibleFiniteUpSections»",
								upCharts[0].Rw(),
								upCharts[1].Rw(),
								spanning[1].Rw(),
								BySets(upper))
							upSubspace := b.Have(
								"the sections of O(N)^E form a k-subspace of L",
								"submodule(«invertibleFiniteLaurentOverK», «wcField», «invertibleFiniteUpSections»)",
								By(
									upLattice,
									datum,
									lattice_pair.H0Submodule.At(laurentOps, polynomials, inversePolynomials, k, V, up)))
							sectionsSubspace := b.Have(
								"so do the sections of M",
								"submodule(«invertibleFiniteOverK», «wcField», fst(M) ∩ snd(M))",
								By(lattice, kInCharts[0], kInCharts[1], lattice_pair.H0Submodule.At(overlapOps, A0, A1, k, V, M)))
							upSpace := b.Have(
								"H⁰(O(N)^E) is a vector space over k",
								"module_on(«invertibleFiniteLaurentOverK», "+
									"    restrict_module(«wcField», «invertibleFiniteUpSections»))",
								By(upSubspace, submodule.SubmoduleModuleOn.Read(vectorSpaceK).At(upSections)))
							insideUp := b.Have(
								"H⁰(M) is a k-subspace of H⁰(O(N)^E)",
								"submodule(«invertibleFiniteLaurentOverK», "+
									"    restrict_module(«wcField», «invertibleFiniteUpSections»), "+
									"    fst(M) ∩ snd(M))",
								ringsAgree.Rw(),
								By(
									sectionsSubspace,
									sectionsInside,
									submodule.SubmoduleRestrict.At(overK, V, upSections, sections)))
							subspaceFinite := b.Have(
								"a subspace of a finite-dimensional space is finite-dimensional",
								"finite_dimensional(«invertibleFiniteLaurentOverK», "+
									"    restrict_module(restrict_module(«wcField», «invertibleFiniteUpSections»), fst(M) ∩ snd(M)))",
								By(
									subfield,
									field.SubfieldRingSubfield.Read(L).At(k, b.TermAs[Set[A]]("«wcLaurent»")),
									field.RingSubfieldRestrict.At(laurentOps, k, inv, k),
									b.Unfolded(upFinite, lattice_pair.LatticePairH0Def),
									insideUp,
									module_dimension.SubmoduleDim.Read(upSpace).At(inv, sections)))
							twice := b.Have(
								"restricting L's module twice is restricting it once",
								"restrict_module(restrict_module(«wcField», «invertibleFiniteUpSections»), fst(M) ∩ snd(M)) = "+
									"restrict_module(«wcField», fst(M) ∩ snd(M))",
								Unfold(module_record.RestrictModuleDef))
							b.Show(
								"so H⁰(M) is finite-dimensional over k",
								Simp(Fwd(lattice_pair.LatticePairH0Def)),
								ringsAgree.RwRev(),
								twice.RwRev(),
								By(subspaceFinite))
						})),
					Case(
						"H¹(M) is finite-dimensional, a quotient of H¹(O(−N)^E)",
						Derive(func(b *Argument) {
							ambient, chartSum, downSum :=
								b.TermAs[Set[A]]("«ambientOnCurve»"),
								b.TermAs[Set[A]]("«invertibleFiniteChartSum»"),
								b.TermAs[Set[A]]("«invertibleFiniteDownSum»")
							overSubring := b.Conjuncts(
								b.Have(
									"over k, L is a vector space and the ambient and the chart sum of M are subspaces of it",
									"module_on(«invertibleFiniteOverK», «wcField») ∧ "+
										"submodule(«invertibleFiniteOverK», «wcField», «ambientOnCurve») ∧ "+
										"submodule(«invertibleFiniteOverK», «wcField», «invertibleFiniteChartSum»)",
									By(
										datum,
										kSubring,
										kInCharts[0],
										kInCharts[1],
										lattice,
										lattice_pair.PairOverSubring.At(overlapOps, A0, A1, t, b.TermAs[A]("L.inv(t)"), k, V, M))),
								"L is a vector space over k",
								"the ambient of M is a k-subspace of L",
								"so is the chart sum of M")
							vectorSpace, ambientSubspace, sumSubspace := overSubring[0], overSubring[1], overSubring[2]
							downSumSubspace := b.Have(
								"the chart sum of O(−N)^E is a k-subspace of L",
								"submodule(«invertibleFiniteOverK», «wcField», «invertibleFiniteDownSum»)",
								ringsAgree.RwRev(),
								By(datum, downLattice, projective_line.LineH1Module.Read(L).At(k, tm, V, down)))
							downInside := b.Have(
								"O(−N)^E lies inside M chart by chart: the two share chart 0",
								"fst(«invertibleFiniteDown») ⊆ fst(M) ∧ snd(«invertibleFiniteDown») ⊆ snd(M)",
								downCharts[0].Rw(),
								downCharts[1].Rw(),
								spanning[1].Rw(),
								By(lower, set_order.SubsetRefl.At(first)))
							sumsInside := b.Have(
								"so its chart sum lies in that of M",
								"«invertibleFiniteDownSum» ⊆ «invertibleFiniteChartSum»",
								By(downInside, lattice_pair.SubpairInclusions.At(overlapOps, V, M, down)))
							sumInAmbient := b.Have(
								"which lies in the ambient of M",
								"«invertibleFiniteChartSum» ⊆ «ambientOnCurve»",
								By(lattice, lattice_pair.ChartSumInAmbient.At(overlapOps, A0, A1, V, M)))
							ambients := b.Have(
								"O(−N)^E and M have one ambient, the k[t, 1/t]-span of E",
								"lattice_pair_ambient(«wcRing»(«wcLaurent»), «wcField», «invertibleFiniteDown») = «ambientOnCurve»",
								sandwich[0].Rw(),
								Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
								downCharts[0].Rw(),
								By(datum, EinL, submodule.SpanOfSubringSpan.Read(overLaurent).At(polynomialOps, E)))
							downQuotient := b.Have(
								"so H¹(O(−N)^E) is the ambient of M modulo the chart sum of O(−N)^E, finite-dimensional over k",
								"finite_dimensional(«invertibleFiniteOverK», "+
									"    quotient_module(restrict_module(«wcField», «ambientOnCurve»), «invertibleFiniteDownSum»))",
								ringsAgree.RwRev(),
								ambients.RwRev(),
								By(b.Unfolded(downFinite, lattice_pair.LatticePairH1Def)))
							b.Show(
								"and H¹(M), its quotient by the larger chart sum of M, is finite-dimensional too",
								Simp(Fwd(lattice_pair.LatticePairH1Def)),
								By(
									subfield,
									field.SubfieldRingSubfield.Read(L).At(k, A01),
									field.RingSubfieldRestrict.At(overlapOps, k, inv, k),
									ambientSubspace,
									sumSubspace,
									downSumSubspace,
									sumsInside,
									sumInAmbient,
									downQuotient,
									module_dimension.QuotientChainDim.Read(vectorSpace).At(inv, ambient, chartSum, downSum)))
						})),
				))
		}),
})}

// TwistFinite — twisting an invertible pair at a regular point keeps its
// cohomology finite-dimensional.
var TwistFinite = twistFiniteThm{family.Add(registry.ProofEntry{
	Name: "TwistFinite",
	Key:  "prop_5c9d2b31e740d105",
	Reading: "The point's regularity is load-bearing only through the twist staying " +
		"invertible: its ideals are invertible, so P⁻¹ · M is a product of invertible pairs.",
	Deps: []registry.EntryLike{
		InvertibleFinite,
		lattice_pair_twist.LatticePairTwistDef,
		lattice_pair_twist.BiaffineRegularPointDef,
		lattice_pair_twist.TwistInvertible,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
		},
		Conclusion: "lattice_pair_finite(«wcOverlap», " +
			"    k, " +
			"    «wcField», " +
			"    lattice_pair_twist(field_ring(L), A₀, A₁, M, P))",
	},
		"the twist of an invertible pair at a regular point is "+
			"invertible (lattice_pair's TwistInvertible); InvertibleFinite"),
})}

// ---------------------------------------------------------------------------
// Chart quotients between pairs, finite-dimensional over k
// ---------------------------------------------------------------------------

// InvertibleMeetStructure — an invertible pair M meets the structure pair
// in a lattice pair K = (fst(M) ∩ A₀, snd(M) ∩ A₁) whose chart quotients
// inside the structure pair and inside M are finite-dimensional over k.
var InvertibleMeetStructure = invertibleMeetStructureThm{family.Add(registry.ProofEntry{
	Name: "InvertibleMeetStructure",
	Key:  "prop_6ab2b67d8755f040",
	Reading: "Each chart's two quotients are ideal_colength.InvertibleMeetQuotientsFinite read " +
		"at that chart and the chart of M on it, the chart's nonzero principal quotients being " +
		"finite (PrincipalColengthFinite). K need not be invertible: the cusp A₀ = k[u², u³], A₁ = " +
		"k[1/u] inside k(u), with t = u², is a curve, and the invertible pair u · O meets O in u · " +
		"(u², u³) on chart 0, whose product with its inverse is (u², u³) ≠ A₀. Nor need the curve " +
		"be regular: that K is a lattice pair is lattice_pair.AmbientOfIntersection, which asks of " +
		"M and O only that they be lattice pairs over the biaffine datum.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
		},
		Conclusion: "lattice_pair(«wcOverlap», A₀, A₁, «wcField», (fst(M) ∩ A₀, snd(M) ∩ A₁)) ∧ " +
			"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(A₀), fst(M) ∩ A₀)) ∧ " +
			"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(A₁), snd(M) ∩ A₁)) ∧ " +
			"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(fst(M)), fst(M) ∩ A₀)) ∧ " +
			"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(snd(M)), snd(M) ∩ A₁))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
		) {
			data := arg.Conjuncts(
				GroupPremises(given, CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			biaffine, subfield, structurePair, kInCharts := data[1], data[2], data[3], data[7]
			kInEachChart := arg.Have(
				"so k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(kInCharts))
			charts := arg.Have(
				"both charts are subrings of L",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁)",
				By(given, CurveOverItsLine.Read(L).AsFact().At(k, A0, A1, A01, t)))
			invertible := arg.Have(
				"the charts of M are invertible fractional ideals and M is a lattice pair",
				"invertible_fractional(field_ring(L), A₀, fst(M)) ∧ "+
					"invertible_fractional(field_ring(L), A₁, snd(M)) ∧ "+
					"lattice_pair(«wcOverlap», A₀, A₁, «wcField», M)",
				By(
					given,
					invertible_lattice_pair.InvertibleLatticePairDef.At(
						arg.TermAs[module_record.RingOps[A]]("field_ring(L)"), A0, A1, A01, M)))
			meet := arg.Have(
				"the intersection with the structure pair is a lattice pair",
				"lattice_pair(«wcOverlap», A₀, A₁, «wcField», (fst(M) ∩ A₀, snd(M) ∩ A₁))",
				By(
					biaffine,
					structurePair,
					invertible,
					lattice_pair.AmbientOfIntersection.At(
						arg.TermAs[module_record.RingOps[A]]("«wcOverlap»"), A0, A1, t, arg.TermAs[A]("L.inv(t)"),
						arg.TermAs[module_record.ModuleOps[A, A]]("«wcField»"), M, arg.TermAs[_LatticePair]("(A₀, A₁)")),
					pairs.Fst,
					pairs.Snd))
			principal := arg.Conjuncts(
				GroupPremises(given, PrincipalColengthFinite.Read(L).At(k, A0, A1, A01, t)),
				"nonzero principal quotients on chart zero are finite",
				"and on chart one")
			fractions := arg.Conjuncts(
				GroupPremises(given, FractionFieldBothCharts.Read(L).At(k, A0, A1, A01, t)),
				"L is the fraction field of chart zero",
				"of chart one",
				"and of the overlap")
			quotients0 := arg.Have(
				"L being the fraction field of chart zero, both chart-zero quotients by the meet are finite",
				"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(A₀), fst(M) ∩ A₀)) ∧ "+
					"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(fst(M)), fst(M) ∩ A₀))",
				By(
					fractions[0],
					principal[0],
					charts,
					subfield,
					kInEachChart,
					invertible,
					ideal_colength.InvertibleMeetQuotientsFinite.Read(L).At(k, A0, arg.TermAs[Set[A]]("fst(M)"))))
			quotients1 := arg.Have(
				"L being the fraction field of chart one, both chart-one quotients by the meet are finite",
				"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(A₁), snd(M) ∩ A₁)) ∧ "+
					"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(snd(M)), snd(M) ∩ A₁))",
				By(
					fractions[1],
					principal[1],
					charts,
					subfield,
					kInEachChart,
					invertible,
					ideal_colength.InvertibleMeetQuotientsFinite.Read(L).At(k, A1, arg.TermAs[Set[A]]("snd(M)"))))
			arg.Show(
				"the meet is a lattice pair and has all four finite chart quotients",
				By(meet, quotients0, quotients1))
		}),
})}

// InvertibleQuotientFinite — between two invertible pairs M ⊆ N the chart
// quotients are finite-dimensional over k.
var InvertibleQuotientFinite = invertibleQuotientFiniteThm{family.Add(registry.ProofEntry{
	Name: "InvertibleQuotientFinite",
	Key:  "prop_b23c885a38fc863b",
	Reading: "Invertibility is load-bearing on both pairs: M's puts a nonzero principal ideal m · " +
		"A₀ inside fst(M) (invertible_fractional_ideal.InvertibleContainsPrincipal), and N's gives " +
		"fst(N) a finite basis over k[t] (InvertibleFreeBasis). For a basis E of A₀ over k[t], m · E ⊆ " +
		"m · A₀ ⊆ fst(M) spans L over k(t) as E does, multiplication by the nonzero m being onto L, so " +
		"fst(N) lies in the k(t)-span of fst(M), and principal_ideal_domain.FullSubmoduleQuotientFinite " +
		"makes fst(N)/fst(M) finite-dimensional; chart 1 likewise, through the swapped curve and pairs.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
			"«wdInvertible»(N)",
			"fst(M) ⊆ fst(N)",
			"snd(M) ⊆ snd(N)",
		},
		Conclusion: "finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(fst(N)), fst(M))) ∧ " +
			"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(snd(N)), snd(M)))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			chartQuotient := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
				Hypotheses: []string{
					"«wcDatum»",
					"«wdInvertible»(M)",
					"«wdInvertible»(N)",
					"fst(M) ⊆ fst(N)",
				},
				Conclusion: "finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(fst(N)), fst(M)))",
			}, func(
				a *Argument,
				L field.FieldFact[on.L],
				k, A0, A1, A01 *Expr[Set[A]],
				t *Expr[A],
				M, N *Expr[_LatticePair],
				h Fact,
			) {
				given := a.Conjuncts(
					h,
					"the curve datum",
					"the smaller pair is invertible",
					"the larger pair is invertible",
					"the smaller chart lies in the larger")
				_, polynomials := a.LetAs[Set[A]]("B", "«wcPolynomials»")
				U, largerChart := a.LetAs[Set[A]]("U", "fst(N)")
				V, smallerChart := a.LetAs[Set[A]]("V", "fst(M)")
				ring := a.TermAs[RingOps[A]]("field_ring(L)")
				vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wcField»")
				chartScalars := a.TermAs[RingOps[A]]("«wcRing»(A₀)")
				polynomialScalars := a.TermAs[RingOps[A]]("«wcRing»(B)")
				rationalFunctions := a.TermAs[Set[A]]("«wcRationalFunctions»")
				rationalScalars := a.TermAs[RingOps[A]]("«wcRing»(«wcRationalFunctions»)")
				curve := a.Have(
					"the curve supplies polynomial charts, a finite "+
						"chart basis, and L as the fraction field of the chart",
					"subfield(L, k) ∧ "+
						"t ∈ L.carrier ∧ "+
						"B ⊆ A₀ ∧ "+
						"(∃E:set(A). finite(E) ∧ module_basis(«wcRing»(B), «wcVectors»(A₀), E)) ∧ "+
						"fraction_field_carrier(field_ring(L), A₀)",
					By(
						Normalized,
						polynomials,
						given[0],
						CurveOverLineDef.At(a.TermAs[field.FieldOps[A]]("L"), k, t, A0, A1, A01)))
				chartRing := a.Have(
					"the chart is a subring of L",
					"subring(field_ring(L), A₀) ∧ A₀ ⊆ L.carrier",
					By(given[0], CurveOverItsLine.Read(L).At(k, A0, A1, A01, t), comm_ring.SubringSubset.At(ring, A0)))
				fractionals := a.Have(
					"both charts are invertible fractional ideals over A₀",
					"invertible_fractional(field_ring(L), A₀, V) ∧ invertible_fractional(field_ring(L), A₀, U)",
					By(
						Normalized,
						given[1],
						given[2],
						smallerChart,
						largerChart,
						invertible_lattice_pair.InvertibleLatticePairDef.At(ring, A0, A1, A01, M),
						invertible_lattice_pair.InvertibleLatticePairDef.At(ring, A0, A1, A01, N)))
				chartSubmodules := a.Have(
					"the two fractional ideals are chart submodules",
					"submodule(«wcRing»(A₀), «wcField», V) ∧ submodule(«wcRing»(A₀), «wcField», U)",
					By(
						fractionals,
						fractional_ideal.InvertibleFractionalDef.At(ring, A0, V),
						fractional_ideal.InvertibleFractionalDef.At(ring, A0, U)))
				submodules := a.Have(
					"restricting scalars makes them k[t]-submodules",
					"submodule(«wcRing»(B), «wcField», V) ∧ submodule(«wcRing»(B), «wcField», U)",
					By(
						chartSubmodules,
						curve,
						submodule.SubmoduleRestrictScalars.At(chartScalars, vectors, V, polynomialScalars),
						submodule.SubmoduleRestrictScalars.At(chartScalars, vectors, U, polynomialScalars)))
				carriers := a.Have(
					"both charts lie in L",
					"U ⊆ L.carrier ∧ V ⊆ L.carrier",
					By(
						submodules,
						submodule.SubmoduleSubset.At(polynomialScalars, vectors, V),
						submodule.SubmoduleSubset.At(polynomialScalars, vectors, U)))

				m, principal := a.ObtainAs[A](
					"the invertible ideal V contains a nonzero principal ideal m · A₀",
					"∃m:A. m ∈ A₀ ∧ m ≠ L.zero ∧ image(L.mul(m), A₀) ⊆ V",
					By(
						chartRing,
						curve,
						fractionals,
						invertible_fractional_ideal.InvertibleContainsPrincipal.Read(L).At(A0, V)))
				nonzero := a.Have(
					"m is a nonzero member of L",
					"m ∈ L.carrier ∧ m ≠ L.zero",
					BySets(principal, chartRing))
				E, chartBasis := a.ObtainAs[Set[A]](
					"choose a finite basis of the chart over k[t]",
					"∃E:set(A). finite(E) ∧ module_basis(«wcRing»(B), «wcVectors»(A₀), E)",
					By(curve),
					Named("E"))
				rationalField := a.Have(
					"k(t) is a subfield of L",
					"subfield(L, «wcRationalFunctions»)",
					By(
						curve,
						field.SubfieldSubset.At(a.TermAs[field.FieldOps[A]]("L"), k),
						set_order.SingSubset.At(a.TermAs[Set[A]]("L.carrier"), t),
						algebraic_element.AdjoinSubfield.Read(L).At(k, a.TermAs[Set[A]]("{t}"))))
				basisSpans := a.Have(
					"its elements lie in the chart, and it spans L over k(t)",
					"E ⊆ A₀ ∧ E ⊆ L.carrier ∧ module_span(«wcRing»(«wcRationalFunctions»), «wcField», E) = L.carrier",
					BySets(
						Normalized,
						given[0],
						chartBasis,
						chartRing,
						polynomials,
						linear_independence.BasisInCarrier.At(
							polynomialScalars, a.TermAs[module_record.ModuleOps[A, A]]("«wcVectors»(A₀)"), E),
						ChartBasisSpansFunctionField.Read(L).At(k, A0, A1, A01, t, E)))
				rationalModules := a.Have(
					"L is a module over the subring k(t)",
					"subring(field_ring(L), «wcRationalFunctions») ∧ "+
						"module_on(«wcRing»(«wcRationalFunctions»), «wcField»)",
					By(rationalField, field_extension.SubfieldScalars.Read(L).At(rationalFunctions)))
				linear := a.Have(
					"multiplication by m is k(t)-linear on L",
					"module_homomorphism(«wcRing»(«wcRationalFunctions»), «wcField», «wcField», L.mul(m))",
					By(nonzero, rationalModules, field_extension.ScaleLinear.Read(L).AsFact().At(rationalFunctions, m)))
				onBasis := a.Have(
					"the chart basis lies in A₀, so multiplication by m sends it into m · A₀ ⊆ V",
					"image(L.mul(m), E) ⊆ V",
					By(
						principal,
						basisSpans,
						set_image.ImageSubset.At(a.TermAs[Fun[A, A]]("L.mul(m)"), E, A0),
						set_order.SubsetTrans.At(
							a.TermAs[Set[A]]("image(L.mul(m), E)"), a.TermAs[Set[A]]("image(L.mul(m), A₀)"), V)))
				scaledBasisSpans := a.Have(
					"the scaled basis spans L because multiplication by nonzero m is surjective",
					"module_span(«wcRing»(«wcRationalFunctions»), «wcField», image(L.mul(m), E)) = L.carrier",
					By(
						basisSpans,
						linear,
						nonzero,
						linear_independence.HomSpan.At(
							rationalScalars, vectors, vectors, a.TermAs[Fun[A, A]]("L.mul(m)"), E),
						field.MulBijective.Read(L).AsFact().At(m)))
				spansL := a.Have(
					"V therefore spans all of L over k(t)",
					"L.carrier ⊆ module_span(«wcRing»(«wcRationalFunctions»), «wcField», V)",
					BySets(
						scaledBasisSpans,
						onBasis,
						submodule.SpanMono.At(rationalScalars, vectors, a.TermAs[Set[A]]("image(L.mul(m), E)"), V)))

				F, largerBasis := a.ObtainAs[Set[A]](
					"choose a finite k[t]-basis of the larger chart U",
					"∃F:set(A). finite(F) ∧ module_basis(«wcRing»(B), «wcVectors»(U), F)",
					By(
						Normalized,
						given[0],
						given[2],
						largerChart,
						polynomials,
						InvertibleFreeBasis.Read(L).At(k, A0, A1, A01, t, N)),
					Named("F"))
				inLocalizedSpan := a.Have(
					"the larger chart lies in the k(t)-span of the smaller",
					"U ⊆ module_span(«wcRing»(«wcRationalFunctions»), «wcField», V)",
					BySets(carriers, spansL))
				a.Show(
					"V is a k[t]-submodule of the free chart U spanning it over k(t), so U/V is finite-dimensional",
					By(
						curve,
						submodules,
						largerBasis,
						given[3],
						inLocalizedSpan,
						polynomials,
						largerChart,
						smallerChart,
						principal_ideal_domain.FullSubmoduleQuotientFinite.Read(L).AsFact().At(k, U, V, F, t)))
			})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					L field.FieldFact[on.L],
					k, A0, A1, A01 *Expr[Set[A]],
					t *Expr[A],
					M, N *Expr[_LatticePair],
					h Fact,
				) {
					swappedCurve := a.Have(
						"exchange the two charts of the curve",
						"curve_over_line(L, k, L.inv(t), A₁, A₀, A₀₁)",
						By(h, CurveSwap.Read(L).At(k, A0, A1, A01, t)))
					swappedPairs := a.Have(
						"exchange the charts of both invertible pairs",
						"invertible_lattice_pair(field_ring(L), A₁, A₀, A₀₁, (snd(M), fst(M))) ∧ "+
							"invertible_lattice_pair(field_ring(L), A₁, A₀, A₀₁, (snd(N), fst(N)))",
						By(
							h,
							invertible_lattice_pair.InvertiblePairSwap.Read(L).At(A0, A1, A01, M),
							invertible_lattice_pair.InvertiblePairSwap.Read(L).At(A0, A1, A01, N)))
					first := a.Have(
						"the quotient on chart zero is finite-dimensional",
						"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(fst(N)), fst(M)))",
						By(h, Read(chartQuotient, L).At(k, A0, A1, A01, t, M, N)))
					second := a.Have(
						"the same chart argument gives the quotient on chart one",
						"finite_dimensional(«wcRing»(k), quotient_module(«wcVectors»(snd(N)), snd(M)))",
						By(
							h,
							swappedCurve,
							swappedPairs,
							Read(chartQuotient, L).At(
								k,
								A1,
								A0,
								A01,
								a.TermAs[A]("L.inv(t)"),
								a.TermAs[_LatticePair]("(snd(M), fst(M))"),
								a.TermAs[_LatticePair]("(snd(N), fst(N))")),
							pairs.Fst.At(a.TermAs[Set[A]]("snd(M)"), a.TermAs[Set[A]]("fst(M)")),
							pairs.Fst.At(a.TermAs[Set[A]]("snd(N)"), a.TermAs[Set[A]]("fst(N)"))))
					a.Show(
						"both chart quotients are finite-dimensional",
						By(first, second))
				})
		}),
})}
