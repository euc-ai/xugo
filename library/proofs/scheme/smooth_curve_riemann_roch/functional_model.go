// functional_model.go — a dualizing model read off a nonzero linear functional.
// For a finite extension L of k(t) and a nonzero k(t)-linear l : L → k(t), the
// multiplication pairing l(x * y) identifies each Hom module over the line with
// a fractional ideal of L: the maps of the overlap into k[t, 1/t] with the dual of
// the overlap, and the two charts of the dualizing pair with the duals of the
// charts valued in the charts of O(−2). No trace enters, so nothing asks the
// extension to be separable.

package smooth_curve_riemann_roch

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// FunctionFieldOverLine — a smooth curve over its line: k(t) is a subfield of L
// over which L is finite, k[t] and k[t, 1/t] are subrings inside it, inside the
// chart and the overlap, and one finite set E is a basis of the chart over k[t], of
// L over k(t) and of the overlap over k[t, 1/t].
var FunctionFieldOverLine = functionFieldOverLineThm{family.Add(registry.ProofEntry{
	Name: "FunctionFieldOverLine",
	Key:  "prop_f7a442571ea0ffd1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "subfield(L, «rational») ∧ " +
			"finite_extension(L, «rational», L.carrier) ∧ " +
			"«polynomials» ⊆ «rational» ∧ " +
			"«polynomials» ⊆ A₀ ∧ " +
			"«polynomials» ⊆ «laurent» ∧ " +
			"«laurent» ⊆ «rational» ∧ " +
			"«laurent» ⊆ A₀₁ ∧ " +
			"subring(field_ring(L), «polynomials») ∧ " +
			"subring(field_ring(L), A₀) ∧ " +
			"subring(field_ring(L), «laurent») ∧ " +
			"subring(field_ring(L), A₀₁) ∧ " +
			"fraction_field_carrier(«rings»(«rational»), «polynomials») ∧ " +
			"fraction_field_carrier(field_ring(L), A₀) ∧ " +
			"(∃E:set(A). " +
			"    finite(E) ∧ " +
			"    module_basis(«rings»(«polynomials»), «vectors»(A₀), E) ∧ " +
			"    module_basis(«rings»(«rational»), regular_module(field_ring(L)), E) ∧ " +
			"    module_basis(«rings»(«laurent»), «vectors»(A₀₁), E))",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "rational", Text: "field_adjoin(L, k, {t})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
			{Name: "laurent", Text: "ring_away(field_ring(L), «polynomials», t)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			record := a.TermAs[FieldOps[A]]("L")
			carrierRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			rational := a.TermAs[Set[A]]("«rational»")
			polynomials := a.TermAs[Set[A]]("«polynomials»")
			datum := a.Have(
				"the charts make a curve over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			line := a.Conjuncts(
				a.Have(
					"the curve supplies its constants, its parameter and its rings",
					"subfield(L, k) ∧ "+
						"t ∈ L.carrier ∧ "+
						"t * L.inv(t) = L.one ∧ "+
						"subring(field_ring(L), A₀₁) ∧ "+
						"subring(field_ring(L), A₀) ∧ "+
						"«polynomials» ⊆ A₀ ∧ "+
						"«polynomials» ⊆ «laurent» ∧ "+
						"subring(field_ring(L), «polynomials») ∧ "+
						"subring(field_ring(L), «laurent») ∧ "+
						"t ∈ «polynomials» ∧ "+
						"(∃E:set(A). finite(E) ∧ module_basis(«rings»(«polynomials»), «vectors»(A₀), E))",
					By(datum, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t))),
				"k is a subfield of L",
				"t lies in L",
				"t times its inverse is one",
				"the overlap is a subring of L",
				"the chart is a subring of L",
				"k[t] lies in the chart",
				"k[t] lies in k[t, 1/t]",
				"k[t] is a subring of L",
				"k[t, 1/t] is a subring of L",
				"t lies in k[t]",
				"the chart has a finite basis over k[t]")
			constants, tm, product := line[0], a.MemberOf[on.L](t, line[1]), line[2]
			overlapSubring, chartSubring, polynomialsInChart, polynomialsInLaurent :=
				line[3], line[4], line[5], line[6]
			polynomialsSubring, laurentSubring, tInPolynomials, basisOverPolynomials :=
				line[7], line[8], line[9], line[10]
			polynomialsInRational := a.Have(
				"k[t] lies in k(t)",
				"«polynomials» ⊆ «rational»",
				By(constants, algebraic_element.PolynomialImageRing.Read(L).At(k, tm)))
			finiteness := a.Conjuncts(
				GroupPremises(datum, algebraic_curve.FiniteOverRationalFunctions.Read(L).At(k, A0, A1, A01, t)),
				"k(t) is a subfield of L",
				"L is finite over k(t)",
				"a chart basis is a basis of L over k(t)",
				"so is a basis of the other chart")
			rationalField := finiteness[0]
			rationalSubring := a.Have(
				"k(t) is a subring of L",
				"subring(field_ring(L), «rational»)",
				By(rationalField, field_extension.SubfieldScalars.Read(L).At(rational)))
			inverseParts := a.Conjuncts(
				a.Have(
					"t lies in k(t), and so does its inverse",
					"t ∈ «rational» ∧ L.inv(t) ∈ «rational»",
					By(
						tInPolynomials,
						polynomialsInRational,
						rationalField,
						set_basic.SubsetDef,
						field.SubfieldInv.At(record, rational, t))),
				"t lies in k(t)",
				"its inverse lies in k(t)")
			sameAway := a.Have(
				"inverting t over k[t] in k(t) is inverting it in L",
				"ring_away(«rings»(«rational»), «polynomials», t) = «laurent»",
				By(
					field.RingOn.Read(L),
					rationalSubring,
					inverseParts[0],
					polynomialsInRational,
					inverseParts[1],
					product,
					ring_away.RingAwayInSubring.At(carrierRing, rational, polynomials, t, a.TermAs[A]("L.inv(t)"))))
			laurentInRational := a.Have(
				"so k[t, 1/t] lies in k(t)",
				"«laurent» ⊆ «rational»",
				sameAway.RwRev(),
				Simp(Fwd(ring_away.RingAwayDef), Fwd(module_record.RestrictRingDef)),
				BySets())
			E, basis := a.UnpackAs[Set[A]](basisOverPolynomials, "E")
			basisParts := a.Conjuncts(
				basis,
				"E is finite",
				"E is a basis of the chart over k[t]")
			finiteE, chartBasis := basisParts[0], basisParts[1]
			overRational := a.Conjuncts(
				GroupPremises(basisParts[0], basisParts[1], finiteness[2].At(E)),
				"E is a basis of L over k(t)",
				"whose degree is its size")[0]
			overLaurent := a.Conjuncts(
				GroupPremises(datum, algebraic_curve.BasisSpansOverlap.Read(L).At(k, A0, A1, A01, t)),
				"a basis of the chart is a basis of the overlap",
				"so is a basis of the other chart")[0].At(E)
			basisExists := a.Have(
				"so E is a common basis of the chart, of L and of the overlap",
				"∃E:set(A). "+
					"    finite(E) ∧ "+
					"    module_basis(«rings»(«polynomials»), «vectors»(A₀), E) ∧ "+
					"    module_basis(«rings»(«rational»), regular_module(field_ring(L)), E) ∧ "+
					"    module_basis(«rings»(«laurent»), «vectors»(A₀₁), E)",
				Derive(func(b *Argument) {
					b.Take(E)
					b.Show(
						"E is one",
						By(finiteE, chartBasis, overRational, overLaurent))
				}))
			laurentInOverlap := a.Have(
				"k[t, 1/t] lies in the overlap",
				"«laurent» ⊆ A₀₁",
				By(datum, algebraic_curve.LaurentRingInOverlap.Read(L).At(k, A0, A1, A01, t)))
			chartFractions := a.Have(
				"L is the fraction field of the chart",
				"fraction_field_carrier(field_ring(L), A₀)",
				By(a.Unfolded(datum, algebraic_curve.CurveOverLineDef)))
			a.Show(
				"those are the clauses",
				By(
					rationalField,
					finiteness[1],
					polynomialsInRational,
					polynomialsInChart,
					polynomialsInLaurent,
					laurentInRational,
					laurentInOverlap,
					polynomialsSubring,
					chartSubring,
					laurentSubring,
					overlapSubring,
					constants,
					integral_element.RationalFunctionsFractionField.Read(L).At(k, tm),
					chartFractions,
					basisExists))
		}),
})}

// ChartFunctionalInvertible — on a chart of a smooth curve the dual of the
// chart over its polynomial ring is an invertible fractional ideal: the chart
// is finite free over k[t] on a k(t)-basis of L, and every nonzero ideal of the
// chart is invertible (smooth_curve.ChartIdealInvertible), so the dual, a
// bounded fractional ideal, is invertible
// (functional_dual.FunctionalDualBoundedInvertible).
var ChartFunctionalInvertible = chartFunctionalInvertibleThm{family.Add(registry.ProofEntry{
	Name: "ChartFunctionalInvertible",
	Key:  "prop_4ce9b36e9f3e0478",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀l:(A → A).",
		Hypotheses: []string{
			"«scCurve»",
			"module_homomorphism(«rings»(«rational»), regular_module(field_ring(L)), «vectors»(«rational»), l)",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
		},
		Conclusion: "invertible_fractional(field_ring(L), " +
			"    A₀, " +
			"    functional_dual(field_ring(L), l, A₀, «polynomials»))",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "rational", Text: "field_adjoin(L, k, {t})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			l *Arrow[A, A],
			curve, linear, nonzero Fact,
		) {
			rational := a.TermAs[Set[A]]("«rational»")
			polynomials := a.TermAs[Set[A]]("«polynomials»")
			data := a.Conjuncts(
				GroupPremises(curve, FunctionFieldOverLine.Read(L).At(k, A0, A1, A01, t)),
				"k(t) is a subfield of L",
				"L is finite over it",
				"k[t] lies in k(t)",
				"k[t] lies in the chart",
				"k[t] lies in k[t, 1/t]",
				"k[t, 1/t] lies in k(t)",
				"k[t, 1/t] lies in the overlap",
				"k[t] is a subring of L",
				"the chart is a subring of L",
				"k[t, 1/t] is a subring of L",
				"the overlap is a subring of L",
				"k(t) is the fractions of k[t]",
				"L is the fractions of the chart",
				"a finite set is a basis of all three")
			E, basis := a.UnpackAs[Set[A]](data[13], "E")
			bases := a.Conjuncts(
				basis,
				"E is finite",
				"E is a basis of the chart over k[t]",
				"E is a basis of L over k(t)",
				"E is a basis of the overlap over k[t, 1/t]")
			ideals := a.Have(
				"every nonzero ideal of the chart is invertible",
				Statement{
					Binders: "∀H:set(A).",
					Hypotheses: []string{
						"ring_ideal(«rings»(A₀), H)",
						"H ≠ {L.zero}",
					},
					Conclusion: "invertible_fractional(field_ring(L), A₀, H)",
				},
				Derive(func(b *Argument) {
					H := b.FixAs[Set[A]]("H")
					ideal := b.Assume()
					b.Show(
						"the chart of a smooth curve is one where this holds",
						By(curve, ideal, smooth_curve.ChartIdealInvertible.Read(L).At(k, A0, A1, A01, t, H)))
				}))
			a.Show(
				"so the dual of the chart, valued in k[t], is invertible",
				By(
					data[0],
					linear,
					nonzero,
					data[2],
					data[3],
					data[7],
					data[8],
					data[12],
					bases[0],
					bases[1],
					bases[2],
					ideals,
					functional_dual.FunctionalDualBoundedInvertible.Read(L).At(rational, l, polynomials, A0, E)))
		}),
})}

// OverlapDualIsomorphism — the pairing identifies the dual of the overlap, valued
// in k[t, 1/t], with the dualizing container. One finite set is a basis of the
// overlap over k[t, 1/t] and of L over k(t) (FunctionFieldOverLine), so the pairing
// is an isomorphism onto the k[t, 1/t]-linear maps from the overlap
// (functional_dual.FunctionalDualHomIso); and those maps are the vectors of the container.
var OverlapDualIsomorphism = overlapDualIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "OverlapDualIsomorphism",
	Key:  "prop_83a17aa5267a2548",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀l:(A → A).",
		Hypotheses: []string{
			"«scCurve»",
			"«functional»",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
		},
		Conclusion: "module_isomorphism(«rings»(A₀₁), " +
			"    «vectors»(«whole»), " +
			"    curve_dualizing_module(field_ring(L), k, t, A₀₁), " +
			"    «pairing»)",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "rational", Text: "field_adjoin(L, k, {t})"},
			{Name: "laurent", Text: "ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)"},
			{Name: "whole", Text: "functional_dual(field_ring(L), l, A₀₁, «laurent»)"},
			{Name: "functional", Text: "module_homomorphism(«rings»(«rational»), " +
				"    regular_module(field_ring(L)), " +
				"    «vectors»(«rational»), " +
				"    l)"},
			{Name: "pairing", Text: "λz:A. λb:A. COND(b ∈ A₀₁, l(z * b), L.zero)"},
			{Name: "coextension", Text: "coextend_scalars(«rings»(«laurent»), " +
				"    «rings»(A₀₁), " +
				"    λa:A. a, " +
				"    «vectors»(«laurent»))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			l *Arrow[A, A],
			curve, linear, nonzero Fact,
		) {
			rational := a.TermAs[Set[A]]("«rational»")
			laurent := a.TermAs[Set[A]]("«laurent»")
			line := a.Conjuncts(
				a.Have(
					"over the line, k[t, 1/t] lies in k(t) and in the overlap, with a common basis",
					"subfield(L, «rational») ∧ "+
						"«laurent» ⊆ «rational» ∧ "+
						"«laurent» ⊆ A₀₁ ∧ "+
						"subring(field_ring(L), «laurent») ∧ "+
						"subring(field_ring(L), A₀₁) ∧ "+
						"(∃E:set(A). "+
						"    finite(E) ∧ "+
						"    module_basis(«rings»(polynomial_image(field_ring(L), k, t)), «vectors»(A₀), E) ∧ "+
						"    module_basis(«rings»(«rational»), regular_module(field_ring(L)), E) ∧ "+
						"    module_basis(«rings»(«laurent»), «vectors»(A₀₁), E))",
					By(curve, FunctionFieldOverLine.Read(L).At(k, A0, A1, A01, t))),
				"k(t) is a subfield of L",
				"k[t, 1/t] lies in k(t)",
				"k[t, 1/t] lies in the overlap",
				"k[t, 1/t] is a subring of L",
				"the overlap is a subring of L",
				"a finite set is a basis of chart 0, of L and of the overlap")
			rationalField, laurentInRational, laurentInOverlap, laurentSubring, overlapSubring :=
				line[0], line[1], line[2], line[3], line[4]
			E, basis := a.UnpackAs[Set[A]](line[5], "E")
			bases := a.Conjuncts(
				basis,
				"E is finite",
				"E is a basis of chart 0 over k[t]",
				"E is a basis of L over k(t)",
				"E is a basis of the overlap over k[t, 1/t]")
			laurentSubmodule := a.Have(
				"k[t, 1/t] is a submodule of k(t) over itself",
				"submodule(«rings»(«laurent»), «vectors»(«rational»), «laurent»)",
				By(
					rationalField,
					laurentInRational,
					laurentSubring,
					functional_dual.SubringInFieldSubmodule.Read(L).At(rational, laurent)))
			iso := a.Have(
				"the pairing is an isomorphism of the dual of the "+
					"overlap onto the k[t, 1/t]-linear maps from the overlap",
				"module_isomorphism(«rings»(A₀₁), «vectors»(«whole»), «coextension», «pairing»)",
				By(
					rationalField,
					linear,
					nonzero,
					laurentInRational,
					laurentInOverlap,
					laurentSubring,
					overlapSubring,
					bases[0],
					bases[3],
					bases[2],
					laurentSubmodule,
					functional_dual.FunctionalDualHomIso.Read(L).At(rational, l, laurent, A01, E, laurent)))
			a.Show(
				"and those maps are the vectors of the dualizing container",
				Simp(Fwd(serre_duality.CurveDualizingModuleDef)),
				By(iso))
		}),
})}

// ChartDualInOverlapDual — the dual of chart 0 valued inside k[t, 1/t] lies in the
// dual of the overlap. A basis E of the overlap over k[t, 1/t] lies in chart 0
// (FunctionFieldOverLine), so a member of the dual of the chart passes the test of
// the overlap on E, and testing on a basis tests on the overlap
// (functional_dual.FunctionalDualOnBasis).
var ChartDualInOverlapDual = chartDualInOverlapDualThm{family.Add(registry.ProofEntry{
	Name: "ChartDualInOverlapDual",
	Key:  "prop_ce090892ca41ab0c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀l:(A → A). ∀P:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"«functional»",
			"P ⊆ «laurent»",
		},
		Conclusion: "functional_dual(field_ring(L), l, A₀, P) ⊆ «whole»",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "rational", Text: "field_adjoin(L, k, {t})"},
			{Name: "laurent", Text: "ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)"},
			{Name: "whole", Text: "functional_dual(field_ring(L), l, A₀₁, «laurent»)"},
			{Name: "functional", Text: "module_homomorphism(«rings»(«rational»), " +
				"    regular_module(field_ring(L)), " +
				"    «vectors»(«rational»), " +
				"    l)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			l *Arrow[A, A],
			P *Expr[Set[A]],
			curve, linear, inLaurent Fact,
		) {
			carrierRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			rational := a.TermAs[Set[A]]("«rational»")
			laurent := a.TermAs[Set[A]]("«laurent»")
			whole := a.TermAs[Set[A]]("«whole»")
			line := a.Conjuncts(
				a.Have(
					"over the line, k[t, 1/t] lies in k(t) and in the "+
						"overlap, and chart 0 and the overlap have a common basis",
					"subfield(L, «rational») ∧ "+
						"«laurent» ⊆ «rational» ∧ "+
						"«laurent» ⊆ A₀₁ ∧ "+
						"subring(field_ring(L), «laurent») ∧ "+
						"subring(field_ring(L), A₀₁) ∧ "+
						"(∃E:set(A). "+
						"    finite(E) ∧ "+
						"    module_basis(«rings»(polynomial_image(field_ring(L), k, t)), «vectors»(A₀), E) ∧ "+
						"    module_basis(«rings»(«rational»), regular_module(field_ring(L)), E) ∧ "+
						"    module_basis(«rings»(«laurent»), «vectors»(A₀₁), E))",
					By(curve, FunctionFieldOverLine.Read(L).At(k, A0, A1, A01, t))),
				"k(t) is a subfield of L",
				"k[t, 1/t] lies in k(t)",
				"k[t, 1/t] lies in the overlap",
				"k[t, 1/t] is a subring of L",
				"the overlap is a subring of L",
				"a finite set is a basis of chart 0, of L and of the overlap")
			rationalField, laurentInRational, laurentInOverlap, laurentSubring, overlapSubring :=
				line[0], line[1], line[2], line[3], line[4]
			E, basis := a.UnpackAs[Set[A]](line[5], "E")
			bases := a.Conjuncts(
				basis,
				"E is finite",
				"E is a basis of chart 0 over k[t]",
				"E is a basis of L over k(t)",
				"E is a basis of the overlap over k[t, 1/t]")
			independent := a.Conjuncts(
				a.Unfolded(bases[1], linear_independence.ModuleBasisDef),
				"E is independent over k[t]",
				"E spans chart 0")[0]
			basisInChart := a.Have(
				"E lies in chart 0",
				"E ⊆ A₀",
				By(linear_independence.IndependentInCarrier.Read(independent)))
			laurentSubmodule := a.Have(
				"k[t, 1/t] is a submodule of k(t) over itself",
				"submodule(«rings»(«laurent»), «vectors»(«rational»), «laurent»)",
				By(
					rationalField,
					laurentInRational,
					laurentSubring,
					functional_dual.SubringInFieldSubmodule.Read(L).At(rational, laurent)))
			inside := a.Have(
				"each member of the dual of the chart lies in the dual of the overlap",
				"∀x:A. x ∈ functional_dual(field_ring(L), l, A₀, P) ⇒ x ∈ «whole»",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					ofX := b.Conjuncts(
						b.Have(
							"x lies in L and passes the test of the chart",
							"x ∈ L.carrier ∧ (∀u:A. u ∈ A₀ ⇒ l(x * u) ∈ P)",
							By(xIn, functional_dual.FunctionalDualMember.At(carrierRing, l, A0, P, x))),
						"x lies in L",
						"x passes the test of the chart")
					tests := b.Have(
						"so it passes the test of the overlap on E",
						"∀e:A. e ∈ E ⇒ l(x * e) ∈ «laurent»",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							value := c.Have(
								"e lies in the chart, so the value lies in P",
								"l(x * e) ∈ P",
								By(ofX[1].At(e), eIn, basisInChart, set_basic.SubsetDef))
							c.Show(
								"P lies in k[t, 1/t]",
								By(value, inLaurent, set_basic.SubsetDef))
						}))
					b.Show(
						"and testing on a basis tests on the overlap",
						By(
							rationalField,
							linear,
							laurentInRational,
							laurentInOverlap,
							laurentSubring,
							overlapSubring,
							bases[3],
							laurentSubmodule,
							ofX[0],
							tests,
							At(Read(functional_dual.FunctionalDualOnBasis, L), rational, l, laurent, A01, E, laurent, x)))
				}))
			a.Show(
				"so the dual of the chart lies in the dual of the overlap",
				By(
					inside,
					set_basic.SubsetDef.At(a.TermAs[Set[A]]("functional_dual(field_ring(L), l, A₀, P)"), whole)))
		}),
})}

// DualizingFromLinearFunctional — a nonzero k(t)-linear functional l on the
// function field gives a model of the dualizing pair: (N₀, t⁻² · N₁), with Nᵢ the
// l-dual of the chart over its polynomial ring, is an invertible lattice pair
// isomorphic to the curve's dualizing pair. The factor t⁻² is there because the
// line's dualizing pair is O(−2), whose charts are k[t] and t⁻² · k[1/t]. Each Nᵢ
// is invertible (ChartFunctionalInvertible, the second through the swap). The
// pairing z ↦ l(z·) is an isomorphism of the l-dual of the overlap onto the
// dualizing container (OverlapDualIsomorphism), the charts of the model lie in
// that dual (ChartDualInOverlapDual), and it carries them onto the two charts of
// the dualizing pair (functional_dual.FunctionalDualChartImage). The lattice structure and the
// isomorphism are then carried back from the dualizing pair
// (lattice_pair_map.LatticePairFromIsomorphism).
var DualizingFromLinearFunctional = dualizingFromLinearFunctionalThm{family.Add(registry.ProofEntry{
	Name: "DualizingFromLinearFunctional",
	Key:  "prop_37dfd3a5d9324071",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀l:(A → A).",
		Hypotheses: []string{
			"«scCurve»",
			"module_homomorphism(restrict_ring(field_ring(L), field_adjoin(L, k, {t})), " +
				"    regular_module(field_ring(L)), " +
				"    restrict_module(regular_module(field_ring(L)), field_adjoin(L, k, {t})), " +
				"    l)",
			"∃x:A. x ∈ L.carrier ∧ l(x) ≠ L.zero",
		},
		Conclusion: "dualizing_model(L, " +
			"    k, " +
			"    t, " +
			"    A₀, " +
			"    A₁, " +
			"    A₀₁, " +
			"    (functional_dual(field_ring(L), l, A₀, polynomial_image(field_ring(L), k, t)), " +
			"        image(L.mul(monoid_pow(L.mul, L.one, L.inv(t), 2)), " +
			"            functional_dual(field_ring(L), " +
			"                l, " +
			"                A₁, " +
			"                polynomial_image(field_ring(L), k, L.inv(t))))))",
		Abbrev: Abbrev{
			{Name: "rings", Text: "restrict_ring(field_ring(L))"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "rational", Text: "field_adjoin(L, k, {t})"},
			{Name: "inverseRational", Text: "field_adjoin(L, k, {L.inv(t)})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
			{Name: "inversePolynomials", Text: "polynomial_image(field_ring(L), k, L.inv(t))"},
			{Name: "laurent", Text: "ring_away(field_ring(L), «polynomials», t)"},
			{Name: "inverseLaurent", Text: "ring_away(field_ring(L), «inversePolynomials», L.inv(t))"},
			{Name: "scale", Text: "monoid_pow(L.mul, L.one, L.inv(t), 2)"},
			{Name: "monomial", Text: "laurent_monomial(t, -&2)"},
			{Name: "dual0", Text: "functional_dual(field_ring(L), l, A₀, «polynomials»)"},
			{Name: "dual1", Text: "functional_dual(field_ring(L), l, A₁, «inversePolynomials»)"},
			{Name: "scaledValues", Text: "image(L.mul(«scale»), «inversePolynomials»)"},
			{Name: "scaledDual", Text: "image(L.mul(«scale»), «dual1»)"},
			{Name: "model", Text: "(«dual0», «scaledDual»)"},
			{Name: "whole", Text: "functional_dual(field_ring(L), l, A₀₁, «laurent»)"},
			{Name: "pairing", Text: "λz:A. λb:A. COND(b ∈ A₀₁, l(z * b), L.zero)"},
			{Name: "container", Text: "curve_dualizing_module(field_ring(L), k, t, A₀₁)"},
			{Name: "omega", Text: "curve_dualizing_pair(L, k, t, A₀, A₁, A₀₁)"},
			{Name: "fieldVectors", Text: "regular_module(field_ring(L))"},
			{Name: "inverse", Text: "λw:(A → A). " +
				"    COND(w ∈ «container».carrier, inverse_on(«whole», «pairing», w), «fieldVectors».zero)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			l *Arrow[A, A],
			curve, linear, nonzero Fact,
		) {
			carrierRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			overlapOps := a.TermAs[module_record.RingOps[A]]("«overlap»")
			fieldVectors := a.TermAs[module_record.ModuleOps[A, A]]("«fieldVectors»")
			container := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«container»")
			omega := a.TermAs[Prod[Set[Fun[A, A]], Set[Fun[A, A]]]]("«omega»")
			model := a.TermAs[Prod[Set[A], Set[A]]]("«model»")
			rational := a.TermAs[Set[A]]("«rational»")
			laurent := a.TermAs[Set[A]]("«laurent»")
			polynomials := a.TermAs[Set[A]]("«polynomials»")
			whole := a.TermAs[Set[A]]("«whole»")
			scale := a.TermAs[A]("«scale»")
			inverseT := a.TermAs[A]("L.inv(t)")
			inversePolynomials := a.TermAs[Set[A]]("«inversePolynomials»")
			scaledValues := a.TermAs[Set[A]]("«scaledValues»")
			pairing := a.TermAs[Fun2[A, A, A]]("«pairing»")
			zero := a.TermAs[A]("L.zero")
			carrier := a.TermAs[Set[Fun[A, A]]]("«container».carrier")
			datum := a.Have(
				"the charts make a curve over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			line := a.Conjuncts(
				a.Have(
					"the curve supplies its constants, its parameter and its rings",
					"subfield(L, k) ∧ "+
						"t ∈ L.carrier ∧ "+
						"t ≠ L.zero ∧ "+
						"subring(field_ring(L), A₀₁) ∧ "+
						"subring(field_ring(L), A₁) ∧ "+
						"A₀ ⊆ A₀₁ ∧ "+
						"A₁ ⊆ A₀₁",
					By(datum, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t))),
				"k is a subfield of L",
				"t lies in L",
				"t is nonzero",
				"the overlap is a subring of L",
				"chart 1 is a subring of L",
				"chart 0 lies in the overlap",
				"chart 1 lies in the overlap")
			constants, tInL, tNonzero, overlapSubring, chart1Subring, chart0InOverlap, chart1InOverlap :=
				line[0], line[1], line[2], line[3], line[4], line[5], line[6]

			// The function field over the line, read from each chart.
			here := a.Conjuncts(
				a.Have(
					"over the line, k(t) is a subfield of L, and k[t, 1/t] lies between k[t] and k(t)",
					"subfield(L, «rational») ∧ "+
						"«polynomials» ⊆ «laurent» ∧ "+
						"«laurent» ⊆ «rational» ∧ "+
						"subring(field_ring(L), «laurent»)",
					By(curve, FunctionFieldOverLine.Read(L).At(k, A0, A1, A01, t))),
				"k(t) is a subfield of L",
				"k[t] lies in k[t, 1/t]",
				"k[t, 1/t] lies in k(t)",
				"k[t, 1/t] is a subring of L")
			rationalField, polynomialsInLaurent, laurentInRational, laurentSubring :=
				here[0], here[1], here[2], here[3]
			swapped := a.Have(
				"read from its other chart it is the same smooth curve",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			there := a.Conjuncts(
				a.Have(
					"the same read from chart 1",
					"«inversePolynomials» ⊆ «inverseRational» ∧ «inversePolynomials» ⊆ «inverseLaurent»",
					By(swapped, FunctionFieldOverLine.Read(L).At(k, A1, A0, A01, inverseT))),
				"k[1/t] lies in k(1/t)",
				"k[1/t] lies in k[1/t, t]")
			sameRational := a.Have(
				"k(1/t) is k(t)",
				"«inverseRational» = «rational»",
				By(constants, tInL, At(Read(algebraic_element.AdjoinInverse, L), k, t)))
			sameLaurent := a.Have(
				"and k[1/t, t] is k[t, 1/t]",
				"«inverseLaurent» = «laurent»",
				By(constants, tInL, tNonzero, At(Read(projective_line.LaurentThroughInverse, L), k, t)))

			// The two charts are invertible, the second after scaling by t⁻².
			linearInverse := a.Have(
				"l is linear over k(1/t)",
				"module_homomorphism(«rings»(«inverseRational»), "+
					"    regular_module(field_ring(L)), "+
					"    «vectors»(«inverseRational»), "+
					"    l)",
				sameRational.Rw(),
				By(linear))
			fractional0 := a.Have(
				"N₀ is invertible",
				"invertible_fractional(field_ring(L), A₀, «dual0»)",
				By(curve, linear, nonzero, ChartFunctionalInvertible.Read(L).At(k, A0, A1, A01, t, l)))
			invertible1 := a.Have(
				"and so is N₁, the same statement at the other chart",
				"invertible_fractional(field_ring(L), A₁, «dual1»)",
				By(
					swapped,
					linearInverse,
					nonzero,
					ChartFunctionalInvertible.Read(L).At(k, A1, A0, A01, inverseT, l)))
			monomial := a.Have(
				"t⁻² is the square of 1/t",
				"«monomial» = «scale»",
				By(laurent_polynomial.LaurentMonomialOfNum.At(
					a.TermAs[Op[A]]("L.mul"),
					a.TermAs[A]("L.one"),
					a.TermAs[Fun[A, A]]("L.inv"),
					t,
					a.TermAs[Nat]("2"))))
			nonzeroScale := a.Conjuncts(
				a.Have(
					"t⁻² is a nonzero member of L",
					"«scale» ∈ L.carrier ∧ «scale» ≠ L.zero",
					monomial.RwRev(),
					By(tInL, tNonzero, laurent_polynomial.LaurentMonomialProduct.Read(L).AsFact().At(t))),
				"t⁻² lies in L",
				"t⁻² is nonzero")
			scaleInLaurent := a.Have(
				"it lies in k[t, 1/t]",
				"«scale» ∈ «laurent»",
				monomial.RwRev(),
				By(
					constants,
					tInL,
					tNonzero,
					At(Read(laurent_polynomial.LaurentMonomialInRing, L), k, t, a.TermAs[Int]("-&2"))))
			scaleInRational := a.Have(
				"so it lies in k(t)",
				"«scale» ∈ «rational»",
				BySets(scaleInLaurent, laurentInRational))
			valuesInRational := a.Have(
				"k[1/t] lies in k(t)",
				"«inversePolynomials» ⊆ «rational»",
				sameRational.RwRev(),
				By(there[0]))
			scaled := a.Have(
				"so t⁻² · N₁ is the dual of chart 1 valued in t⁻² · k[1/t]",
				"«scaledDual» = functional_dual(field_ring(L), l, A₁, «scaledValues»)",
				By(
					rationalField,
					linear,
					comm_ring.SubringSubset.Read(chart1Subring),
					valuesInRational,
					scaleInRational,
					nonzeroScale[1],
					functional_dual.FunctionalDualValueScale.Read(L).At(rational, l, A1, inversePolynomials, scale)))
			fractional1 := a.Have(
				"so t⁻² · N₁, a nonzero multiple of N₁, is invertible",
				"invertible_fractional(field_ring(L), A₁, «scaledDual»)",
				By(
					invertible1,
					chart1Subring,
					nonzeroScale[0],
					nonzeroScale[1],
					functional_dual.FunctionalDualSubset.At(carrierRing, l, A1, inversePolynomials),
					fractional_ideal.InvertibleScale.Read(L).AsFact().At(A1, a.TermAs[Set[A]]("«dual1»"), scale)))

			// The pairing identifies the dual of the overlap with the container.
			iso := a.Have(
				"the pairing is an isomorphism of the dual of the overlap onto the container",
				"module_isomorphism(«overlap», restrict_module(«fieldVectors», «whole»), «container», «pairing»)",
				By(curve, linear, nonzero, OverlapDualIsomorphism.Read(L).At(k, A0, A1, A01, t, l)))
			onto := a.Conjuncts(
				a.Unfolded(iso, module_homomorphism.ModuleIsomorphismDef),
				"the pairing is linear",
				"one-to-one on the dual of the overlap",
				"and onto the container")[2]

			// The charts of the model lie in the dual of the overlap, the second through the swap.
			laurentRing := a.Have(
				"k[t, 1/t] is a ring under L's operations",
				"comm_ring_on(«rings»(«laurent»))",
				By(laurentSubring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(laurent)))
			inverseInLaurent := a.Have(
				"k[1/t] lies in k[t, 1/t]",
				"«inversePolynomials» ⊆ «laurent»",
				sameLaurent.RwRev(),
				By(there[1]))
			multiples := a.Have(
				"t⁻² times a member of k[1/t] lies in k[t, 1/t]",
				"∀p:A. p ∈ «inversePolynomials» ⇒ «scale» * p ∈ «laurent»",
				Derive(func(b *Argument) {
					p := b.FixAs[A]("p")
					pIn := b.Have(
						"p lies in k[t, 1/t]",
						"p ∈ «laurent»",
						By(b.Assume(), inverseInLaurent, set_basic.SubsetDef))
					b.Show(
						"k[t, 1/t] is a ring holding t⁻² and p",
						By(comm_ring.MulIn.Read(laurentRing).At(
							proof.MemberOf(scale, scaleInLaurent), proof.MemberOf(p, pIn))))
				}))
			scaledValuesIn := a.Have(
				"so t⁻² · k[1/t] lies in k[t, 1/t], which is k[1/t, t]",
				"«scaledValues» ⊆ «inverseLaurent»",
				sameLaurent.Rw(),
				By(
					multiples,
					set_image.ImageSubsetIff.At(a.TermAs[Fun[A, A]]("L.mul(«scale»)"), inversePolynomials, laurent)))
			dual0Inside := a.Have(
				"N₀ lies in the dual of the overlap",
				"«dual0» ⊆ «whole»",
				By(
					curve,
					linear,
					polynomialsInLaurent,
					ChartDualInOverlapDual.Read(L).At(k, A0, A1, A01, t, l, polynomials)))
			dual1Inside := a.Have(
				"and so does t⁻² · N₁, the same statement at the other chart",
				"functional_dual(field_ring(L), l, A₁, «scaledValues») ⊆ «whole»",
				sameLaurent.RwRev(),
				By(
					swapped,
					linearInverse,
					scaledValuesIn,
					ChartDualInOverlapDual.Read(L).At(k, A1, A0, A01, inverseT, l, scaledValues)))

			// So it carries the charts of the model onto the charts of the dualizing pair.
			image0 := a.Have(
				"so the pairing carries N₀ onto the maps of the container carrying chart 0 into k[t]",
				"image(«pairing», «dual0») = {φ:A → A | φ ∈ «container».carrier ∧ image(φ, A₀) ⊆ «polynomials»}",
				By(
					chart0InOverlap,
					dual0Inside,
					onto,
					functional_dual.FunctionalDualChartImage.At(
						carrierRing, l, A01, A0, laurent, polynomials, carrier, zero)))
			image1 := a.Have(
				"and t⁻² · N₁ onto those carrying chart 1 into t⁻² · k[1/t]",
				"image(«pairing», functional_dual(field_ring(L), l, A₁, «scaledValues»)) = "+
					"{φ:A → A | φ ∈ «container».carrier ∧ image(φ, A₁) ⊆ «scaledValues»}",
				By(
					chart1InOverlap,
					dual1Inside,
					onto,
					functional_dual.FunctionalDualChartImage.At(
						carrierRing, l, A01, A1, laurent, scaledValues, carrier, zero)))
			omega0 := a.Have(
				"chart 0 of the dualizing pair is the maps carrying chart 0 into k[t]",
				"fst(«omega») = {φ:A → A | φ ∈ «container».carrier ∧ image(φ, A₀) ⊆ «polynomials»}",
				Simp(
					Fwd(serre_duality.CurveDualizingPairDef),
					Fwd(pairs.Fst),
					Fwd(projective_line.ProjectiveLinePairDef)),
				Basic())
			omega1 := a.Have(
				"and chart 1 the maps carrying chart 1 into t⁻² · k[1/t]",
				"snd(«omega») = {φ:A → A | φ ∈ «container».carrier ∧ image(φ, A₁) ⊆ «scaledValues»}",
				Simp(
					Fwd(serre_duality.CurveDualizingPairDef),
					Fwd(pairs.Snd),
					Fwd(projective_line.ProjectiveLinePairDef)),
				By(monomial))
			firstOfModel := a.Have(
				"chart 0 of the model is N₀",
				"fst(«model») = «dual0»",
				By(pairs.Fst))
			secondOfModel := a.Have(
				"and chart 1 of the model is t⁻² · N₁",
				"snd(«model») = «scaledDual»",
				By(pairs.Snd))

			lattice := a.Conjuncts(
				GroupPremises(datum, serre_duality.DualizingIsLattice.Read(L).At(k, A0, A1, A01, t)),
				"the container is a module over the overlap",
				"the dualizing pair is a lattice pair in it",
				"its ambient is the whole container")
			overRegular := a.Have(
				"L is a module over the overlap",
				"module_on(«overlap», «fieldVectors»)",
				By(overlapSubring, fractional_ideal.FieldModuleOn.Read(L).At(A01)))
			submodule0 := a.Have(
				"so N₀ is a submodule over chart 0",
				"submodule(restrict_ring(«overlap», A₀), «fieldVectors», fst(«model»))",
				firstOfModel.Rw(),
				By(
					a.Unfolded(fractional0, fractional_ideal.InvertibleFractionalDef),
					module_record.RestrictRingTwice.At(carrierRing, A01, A0)))
			submodule1 := a.Have(
				"and t⁻² · N₁ a submodule over chart 1",
				"submodule(restrict_ring(«overlap», A₁), «fieldVectors», snd(«model»))",
				secondOfModel.Rw(),
				By(
					a.Unfolded(fractional1, fractional_ideal.InvertibleFractionalDef),
					module_record.RestrictRingTwice.At(carrierRing, A01, A1)))
			inside0 := a.Have(
				"chart 0 of the model lies in the dual of the overlap",
				"fst(«model») ⊆ «whole»",
				firstOfModel.Rw(),
				By(dual0Inside))
			inside1 := a.Have(
				"and so does chart 1",
				"snd(«model») ⊆ «whole»",
				secondOfModel.Rw(),
				scaled.Rw(),
				By(dual1Inside))
			carried0 := a.Have(
				"the pairing carries chart 0 of the model onto chart 0 of the dualizing pair",
				"image(«pairing», fst(«model»)) = fst(«omega»)",
				firstOfModel.Rw(),
				omega0.Rw(),
				By(image0))
			carried1 := a.Have(
				"and chart 1 onto chart 1",
				"image(«pairing», snd(«model»)) = snd(«omega»)",
				secondOfModel.Rw(),
				scaled.Rw(),
				omega1.Rw(),
				By(image1))
			transported := a.Conjuncts(
				a.Have(
					"so the model is a lattice pair, and the inverse of the pairing an isomorphism onto it",
					"lattice_pair(«overlap», A₀, A₁, «fieldVectors», «model») ∧ "+
						"lattice_pair_isomorphism(«overlap», «container», «omega», «fieldVectors», «model», «inverse»)",
					By(
						lattice[1],
						lattice[2],
						overRegular,
						functional_dual.FunctionalDualSubset.At(carrierRing, l, A01, laurent),
						submodule0,
						submodule1,
						inside0,
						inside1,
						iso,
						carried0,
						carried1,
						lattice_pair_map.LatticePairFromIsomorphism.At(
							overlapOps, A0, A1, fieldVectors, container, whole, model, omega, pairing))),
				"the model is a lattice pair",
				"the inverse of the pairing is an isomorphism onto it")
			invertiblePair := a.Have(
				"so the model is an invertible lattice pair",
				"«scInvertible»(«model»)",
				Unfold(invertible_lattice_pair.InvertibleLatticePairDef),
				By(firstOfModel, secondOfModel, fractional0, fractional1, transported[0]))
			exists := a.Have(
				"and isomorphic to the dualizing pair",
				"∃f:((A → A) → A). "+
					"    lattice_pair_isomorphism(«overlap», «container», «omega», «fieldVectors», «model», f)",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Fun[A, A], A]]("«inverse»"))
					b.Show(
						"the inverse of the pairing is one",
						By(transported[1]))
				}))
			a.Show(
				"an invertible lattice pair isomorphic to the dualizing pair is a model of it",
				Unfold(serre_duality.DualizingModelDef),
				By(invertiblePair, exists))
		}),
})}
