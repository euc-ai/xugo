// birational_charts.go — two curves over the line with one function field, read
// through their first charts, count alike up to a fixed bound.

package curve_point_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartFibreBound — the first chart of a curve over the line has boundedly many
// points over each value of t, one bound for every subfield of values: read in M,
// the chart is a subring holding k and t (CurveOverLineChartsInField), free of
// finite rank over k[t] (CurveOverLineFirstChart), so finitely generated over it
// (principal_ideal_domain.FiniteBasisFinitelyGenerated), and k, a subfield of K,
// is one of M, so algebra_points.UniformFibreBound applies.
var ChartFibreBound = chartFibreBoundThm{family.Add(registry.ProofEntry{
	Name: "ChartFibreBound",
	Key:  "prop_1b1407e12611d0f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "∃m:num. ∀l:set(A). ∀y:A. " +
			"    subfield(M, l) ⇒ finite(«over»(l, y)) ∧ card(«over»(l, y)) ≤ m",
		Abbrev: Abbrev{
			{Name: "over", Text: "λl:set(A). λy:A. " +
				"    {e:A → A | " +
				"        e ∈ " +
				"        algebra_points(restrict_ring(field_ring(M), A₀), " +
				"            restrict_ring(field_ring(M), l), " +
				"            k, " +
				"            λx:A. x) ∧ " +
				"        e(t) = y}"},
			{Name: "line", Text: "polynomial_image(field_ring(M), k, t)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			inField, curve Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			functionOps := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			scalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «line»)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(M)), A₀)")
			constantsSubfield := a.Have(
				"k is a subfield of K, so of M",
				"subfield(M, k)",
				By(
					inField,
					curve,
					algebraic_curve.CurveOverLineDef.At(functionOps, k, t, A0, A1, A01),
					field.SubfieldTrans.At(ops, K, k)))
			generated := a.Have(
				"read in M, the chart has a finite basis over k[t], so it is finitely generated over k[t]",
				"module_finitely_generated(restrict_ring(field_ring(M), «line»), "+
					"    restrict_module(regular_module(field_ring(M)), A₀))",
				By(
					inField,
					curve,
					CurveOverLineFirstChart.Read(M).At(K, k, A0, A1, A01, t),
					principal_ideal_domain.FiniteBasisFinitelyGenerated.At(scalars, vectors)))
			a.Show(
				"read in M, the chart is a subring holding k and t, finitely "+
					"generated over k[t], so the uniform fibre bound applies",
				By(
					inField,
					curve,
					constantsSubfield,
					generated,
					CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t),
					algebra_point_bounds.UniformFibreBound.Read(M).At(A0, k, t)))
		}),
})}

// ChartDividesLinePolynomial — a nonzero element h of the first chart of a curve
// over the line divides there the value at t of a nonzero polynomial over k. h is
// algebraic over k(t), so a nonzero d in k[t] carries 1/h into k[t][h], inside the
// chart (integral_element.AdjoinCommonDenominator); d is the value at t of a
// polynomial c, and d = h · d/h.
var ChartDividesLinePolynomial = chartDividesLinePolynomialThm{family.Add(registry.ProofEntry{
	Name: "ChartDividesLinePolynomial",
	Key:  "prop_5c2e53109d795403",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t h:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"h ∈ A₀",
			"h ≠ M.zero",
		},
		Conclusion: "∃c:(num → A). ∃w:A. " +
			"    polynomial_over(k, c) ∧ c ≠ vec_zero ∧ w ∈ A₀ ∧ polynomial_eval(c, t) = h * w",
		Abbrev: Abbrev{
			{Name: "line", Text: "polynomial_image(field_ring(restrict_field(M, K)), k, t)"},
			{Name: "rational", Text: "field_adjoin(restrict_field(M, K), k, {t})"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t, h *Expr[A],
			inField, curve, hIn, hNonzero Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			functionOps := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			functionRing := a.TermAs[RingOps[A]]("field_ring(restrict_field(M, K))")
			line := a.TermAs[Set[A]]("«line»")
			rational := a.TermAs[Set[A]]("«rational»")
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			datum := a.Conjuncts(
				a.Have(
					"read in K, k is a subfield, t lies in K, and A₀ is a subring holding the subring k[t]",
					"subfield(restrict_field(M, K), k) ∧ "+
						"t ∈ restrict_field(M, K).carrier ∧ "+
						"subring(field_ring(restrict_field(M, K)), A₀) ∧ "+
						"subring(field_ring(restrict_field(M, K)), «line») ∧ "+
						"«line» ⊆ A₀",
					By(functionField, curve, algebraic_curve.CurveOverItsLine.At(functionOps, k, A0, A1, A01, t))),
				"k is a subfield of K",
				"t lies in K",
				"A₀ is a subring of K",
				"k[t] is a subring of K",
				"k[t] lies in A₀")
			rationalField := a.Have(
				"k(t) is a subfield of K",
				"subfield(restrict_field(M, K), «rational»)",
				By(
					functionField,
					curve,
					algebraic_curve.FiniteOverRationalFunctions.At(functionOps, k, A0, A1, A01, t)))
			fractions := a.Have(
				"k(t) is the field of fractions of k[t]",
				"fraction_field_carrier(restrict_ring(field_ring(restrict_field(M, K)), «rational»), «line»)",
				By(
					functionField,
					datum[0],
					datum[1],
					integral_element.RationalFunctionsFractionField.At(functionOps, k, t)))
			hInK := a.Have(
				"h lies in K",
				"h ∈ restrict_field(M, K).carrier",
				BySets(hIn, datum[2], comm_ring.SubringSubset.At(functionRing, A0)))
			algebraic := a.Have(
				"h is algebraic over k(t)",
				"algebraic_over(restrict_field(M, K), «rational», h)",
				By(
					functionField,
					curve,
					hInK,
					algebraic_curve.ElementAlgebraicOverRationalFunctions.At(functionOps, k, A0, A1, A01, t, h)))
			adjoinedSet := a.TermAs[Set[A]]("field_adjoin(restrict_field(M, K), «rational», {h})")
			adjoined := a.Have(
				"k(t)(h) is a subfield holding h",
				"subfield(restrict_field(M, K), field_adjoin(restrict_field(M, K), «rational», {h})) ∧ "+
					"h ∈ field_adjoin(restrict_field(M, K), «rational», {h})",
				By(
					functionField,
					rationalField,
					hInK,
					algebraic_element.AdjoinElementSubfield.At(functionOps, rational, h)))
			inverse := a.TermAs[A]("M.inv(h)")
			inverseIn := a.Have(
				"so it holds 1/h",
				"M.inv(h) ∈ field_adjoin(restrict_field(M, K), «rational», {h})",
				By(adjoined, field.SubfieldInv.At(functionOps, adjoinedSet, h)))
			d, cleared := a.ObtainAs[A](
				"a nonzero d in k[t] carries 1/h into k[t][h]",
				"∃d:A. "+
					"    d ∈ «line» ∧ "+
					"    d ≠ M.zero ∧ "+
					"    d * M.inv(h) ∈ polynomial_image(field_ring(restrict_field(M, K)), «line», h)",
				By(
					functionField,
					rationalField,
					datum[3],
					fractions,
					hInK,
					algebraic,
					inverseIn,
					integral_element.AdjoinCommonDenominator.At(functionOps, rational, line, h, inverse)))
			clearedParts := a.Conjuncts(
				cleared,
				"d lies in k[t]",
				"d is not zero",
				"d/h lies in k[t][h]")
			chartRing := a.Have(
				"A₀ is a ring under K's operations",
				"comm_ring_on(restrict_ring(field_ring(restrict_field(M, K)), A₀))",
				By(functionField, datum[2], comm_ring.SubringRingOn.Read(field.RingOn.Read(functionField)).At(A0)))
			quotientIn := a.Have(
				"k[t][h] lies in A₀, so d/h lies in A₀",
				"d * M.inv(h) ∈ A₀",
				BySets(
					functionField,
					chartRing,
					datum[4],
					hIn,
					clearedParts[2],
					algebraic_element.PolynomialImageLeast.At(functionOps, line, A0, h)))
			c, value := a.ObtainAs[Fun[Nat, A]](
				"d is the value at t of a polynomial c over k",
				"∃c:(num → A). polynomial_over(k, c) ∧ polynomial_eval(c, t) = d",
				BySets(clearedParts[0], algebraic_element.PolynomialImageDef.At(functionRing, k, t)))
			members := a.Conjuncts(
				a.Have(
					"t, h and d lie in M",
					"t ∈ M.carrier ∧ h ∈ M.carrier ∧ d ∈ M.carrier",
					BySets(
						datum[1],
						hInK,
						inField,
						clearedParts[0],
						datum[3],
						field.SubfieldSubset.At(ops, K),
						comm_ring.SubringSubset.At(functionRing, line))),
				"t lies in M",
				"h lies in M",
				"d lies in M")
			tm := a.MemberOf[on.M](t, members[0])
			hm := a.MemberOf[on.M](h, members[1])
			dm := a.MemberOf[on.M](d, members[2])
			nonzero := a.Have(
				"c is not the zero polynomial, its value d not being zero",
				"c ≠ vec_zero",
				By(
					Normalized,
					value,
					clearedParts[1],
					polynomial_evaluation.EvalVecZero.Read(field.RingOn.Read(M)).At(tm)))
			cancel := a.Have(
				"h times d/h is d",
				"h * (d * M.inv(h)) = d",
				ByArith(
					M,
					Scaled(d, field.MulRightInverseOn.Read(M).At(hm)),
					hNonzero,
					dm,
					field.InvIn.Read(M).At(hm)))
			a.Take(c)
			a.Take(a.TermAs[A]("d * M.inv(h)"))
			a.Show(
				"so c and d/h witness the division",
				By(Normalized, value, nonzero, quotientIn, cancel))
		}),
})}

// ChartInsideAway — of two curves over the line with one function field and one
// field of constants, the first chart B₀ of the second lies in the first chart A₀ of
// the first with one nonzero element d inverted. B₀ has a finite basis E over k[u]
// (CurveOverLineFirstChart), which spans it; d clears the denominators of u
// and of E (integral_element.FiniteCommonDenominator), so A₀[1/d] holds k, u and E,
// hence the ring k[u][E] they generate; that ring is B₀, being a k[u]-submodule of
// B₀ holding E, which spans B₀.
var ChartInsideAway = chartInsideAwayThm{family.Add(registry.ProofEntry{
	Name: "ChartInsideAway",
	Key:  "prop_14088adaa513be6f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀B₀ B₁ B₀₁:set(A). ∀u:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"curve_over_line(restrict_field(M, K), k, u, B₀, B₁, B₀₁)",
		},
		Conclusion: "∃d:A. d ∈ A₀ ∧ d ≠ M.zero ∧ B₀ ⊆ ring_away(field_ring(M), A₀, d)",
		Abbrev: Abbrev{
			{Name: "line", Text: "polynomial_image(field_ring(M), k, u)"},
			{Name: "generated", Text: "λG:set(A). generated_subring(field_ring(M), «line», G)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			B0, B1, B01 *Expr[Set[A]],
			u *Expr[A],
			inField, curveA, curveB Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			functionOps := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			ring := a.TermAs[RingOps[A]]("field_ring(M)")
			fieldRing := field.RingOn.Read(M)
			carrier := a.TermAs[Set[A]]("M.carrier")
			line := a.TermAs[Set[A]]("«line»")
			scalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «line»)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(M)), B₀)")
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			dataA := a.Conjuncts(
				a.Have(
					"read in K, A₀ is a subring holding k, with fraction field K",
					"subring(field_ring(restrict_field(M, K)), A₀) ∧ "+
						"k ⊆ A₀ ∧ "+
						"fraction_field_carrier(field_ring(restrict_field(M, K)), A₀)",
					BySets(
						functionField,
						curveA,
						algebraic_curve.CurveOverItsLine.At(functionOps, k, A0, A1, A01, t),
						algebraic_curve.CurveOverLineDef.At(functionOps, k, t, A0, A1, A01))),
				"A₀ is a subring of K",
				"k lies in A₀",
				"K is the field of fractions of A₀")
			subA := a.Have(
				"read in M, A₀ is a subring",
				"subring(field_ring(M), A₀)",
				By(inField, curveA, CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t)))
			modelB := a.Conjuncts(
				a.Have(
					"read in M, k[u] and B₀ are subrings, and B₀ holds k[u] and has a finite basis over it",
					"subring(field_ring(M), «line») ∧ "+
						"subring(field_ring(M), B₀) ∧ "+
						"«line» ⊆ B₀ ∧ "+
						"(∃E:set(A). "+
						"    finite(E) ∧ "+
						"    module_basis(restrict_ring(field_ring(M), «line»), "+
						"        restrict_module(regular_module(field_ring(M)), B₀), "+
						"        E))",
					By(inField, curveB, CurveOverLineFirstChart.Read(M).At(K, k, B0, B1, B01, u))),
				"read in M, k[u] is a subring",
				"so is B₀",
				"B₀ holds k[u]",
				"B₀ has a finite basis over k[u]")
			E, basis := a.UnpackAs[Set[A]](modelB[3], "E")
			spans := a.Conjuncts(
				a.Have(
					"the basis E is finite, lies in B₀ and spans it over k[u]",
					"finite(E) ∧ "+
						"E ⊆ B₀ ∧ "+
						"module_span(restrict_ring(field_ring(M), «line»), "+
						"    restrict_module(regular_module(field_ring(M)), B₀), "+
						"    E) = "+
						"B₀",
					By(
						basis,
						linear_independence.ModuleBasisDef.At(scalars, vectors, E),
						linear_independence.IndependentInCarrier.At(scalars, vectors, E))),
				"E is finite",
				"E lies in B₀",
				"E spans B₀ over k[u]")
			generators := a.TermAs[Set[A]]("insert(u, E)")
			generatorsInK := a.Have(
				"u and E are finitely many elements of K",
				"finite(insert(u, E)) ∧ insert(u, E) ⊆ K",
				BySets(
					inField,
					curveB,
					CurveOverLineChartsInField.Read(M).At(K, k, B0, B1, B01, u),
					spans[0],
					spans[1],
					finite_set.FiniteInsert.At(u, E)))
			d, clearing := a.ObtainAs[A](
				"a nonzero d in A₀ clears the denominators of u and E",
				"∃d:A. d ∈ A₀ ∧ d ≠ M.zero ∧ image(M.mul(d), insert(u, E)) ⊆ A₀",
				By(
					functionField,
					dataA[0],
					dataA[2],
					generatorsInK,
					integral_element.FiniteCommonDenominator.At(functionOps, A0, generators)))
			clearingParts := a.Conjuncts(
				clearing,
				"d lies in A₀",
				"d is not zero",
				"d carries u and E into A₀")
			away := a.TermAs[Set[A]]("ring_away(field_ring(M), A₀, d)")
			awayParts := a.Conjuncts(
				a.Have(
					"A₀[1/d] is a subring of M holding A₀ and 1/d",
					"subring(field_ring(M), ring_away(field_ring(M), A₀, d)) ∧ "+
						"A₀ ⊆ ring_away(field_ring(M), A₀, d) ∧ "+
						"M.inv(d) ∈ ring_away(field_ring(M), A₀, d)",
					By(
						subA,
						clearingParts[0],
						clearingParts[1],
						field.CarrierSubfield.Read(M),
						comm_ring.SubringSubset.At(ring, A0),
						ring_away.RingAwayInSubfield.Read(M).At(A0, carrier, d))),
				"A₀[1/d] is a subring",
				"it holds A₀",
				"it holds 1/d")
			dInField := a.Conjuncts(
				a.Have(
					"d and K lie in M",
					"d ∈ M.carrier ∧ K ⊆ M.carrier",
					BySets(
						clearingParts[0],
						subA,
						inField,
						comm_ring.SubringSubset.At(ring, A0),
						field.SubfieldSubset.At(ops, K))),
				"d lies in M",
				"K lies in M")
			dm := a.MemberOf[on.M](d, dInField[0])
			generatorsIn := a.Have(
				"A₀[1/d] holds u and E, each z being d z times 1/d",
				"∀z:A. z ∈ insert(u, E) ⇒ z ∈ ring_away(field_ring(M), A₀, d)",
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					zIn := b.Assume()
					cleared := b.Conjuncts(
						b.Have(
							"z lies in M, and d z in A₀",
							"z ∈ M.carrier ∧ d * z ∈ A₀",
							BySets(zIn, generatorsInK, dInField[1], clearingParts[2])),
						"z lies in M",
						"d z lies in A₀")
					zm := b.MemberOf[on.M](z, cleared[0])
					restored := b.Have(
						"z is d z times 1/d",
						"z = d * z * M.inv(d)",
						ByArith(
							M,
							Scaled(z, field.MulRightInverseOn.Read(M).At(dm)),
							clearingParts[1],
							zm,
							field.InvIn.Read(M).At(dm)))
					b.Show(
						"a product of members of A₀[1/d]",
						BySets(
							restored,
							cleared[1],
							awayParts[0],
							awayParts[1],
							awayParts[2],
							comm_ring.SubringDef.At(ring, away)))
				}))
			awayRing := a.Have(
				"A₀[1/d] is a ring under M's operations",
				"comm_ring_on(restrict_ring(field_ring(M), ring_away(field_ring(M), A₀, d)))",
				By(awayParts[0], comm_ring.SubringRingOn.Read(fieldRing).At(away)))
			lineIn := a.Have(
				"it holds k and u, so it holds k[u]",
				"«line» ⊆ ring_away(field_ring(M), A₀, d)",
				BySets(
					awayRing,
					dataA[1],
					awayParts[1],
					generatorsIn,
					algebraic_element.PolynomialImageLeast.Read(M).At(k, away, u)))
			eInField := a.Have(
				"E lies in M",
				"E ⊆ M.carrier",
				BySets(spans[1], modelB[1], comm_ring.SubringSubset.At(ring, B0)))
			generated := a.TermAs[Set[A]]("«generated»(E)")
			structure := a.Conjuncts(
				a.Have(
					"k[u][E] is the least subring holding k[u] and E",
					"subring(field_ring(M), «generated»(E)) ∧ "+
						"«line» ∪ E ⊆ «generated»(E) ∧ "+
						"(∀B:set(A). subring(field_ring(M), B) ∧ «line» ∪ E ⊆ B ⇒ «generated»(E) ⊆ B)",
					By(modelB[0], eInField, algebraic_element.GeneratedSubringStructure.Read(M).At(line, E))),
				"k[u][E] is a subring",
				"it holds k[u] and E",
				"it lies in every subring holding k[u] and E")
			inclusions := a.Conjuncts(
				a.Have(
					"B₀ and A₀[1/d] both hold k[u] and E, so both hold k[u][E]",
					"«generated»(E) ⊆ B₀ ∧ «generated»(E) ⊆ ring_away(field_ring(M), A₀, d)",
					BySets(structure[2], modelB[1], modelB[2], awayParts[0], lineIn, spans[1], generatorsIn)),
				"k[u][E] lies in B₀",
				"k[u][E] lies in A₀[1/d]")
			submoduleOfB := a.Have(
				"k[u][E] is a k[u]-submodule of B₀",
				"submodule(restrict_ring(field_ring(M), «line»), "+
					"    restrict_module(regular_module(field_ring(M)), B₀), "+
					"    «generated»(E))",
				// A submodule is an additive subgroup closed under the scalars of k[u]:
				// unfolded, its clauses are closure laws of the subring k[u][E] ⊇ k[u].
				Unfold(submodule.SubmoduleDef),
				Unfold(group.SubgroupDef),
				BySets(structure[0], structure[1], inclusions[0], comm_ring.SubringDef.At(ring, generated)))
			equal := a.Have(
				"holding E, it holds the span of E, which is B₀; so k[u][E] is B₀",
				"«generated»(E) = B₀",
				BySets(
					submoduleOfB,
					spans[2],
					structure[1],
					inclusions[0],
					submodule.SpanLeast.At(scalars, vectors, E, generated)))
			a.Take(d)
			a.Show(
				"d is a nonzero element of A₀, and B₀ = k[u][E] lies in A₀[1/d]",
				By(Normalized, clearingParts[0], clearingParts[1], equal, inclusions[1]))
		}),
})}

// CurveCountNearAway — for a nonzero h in the first chart A₀ of a curve over the
// line there is a bound C such that, for every finite subfield l, the rational point
// count of the curve lies between the number of points of A₀[1/h] and that number
// plus C. The count is the points of A₀ and those at infinity
// (CurveCountAtInfinity); the points of A₀ are those of A₀[1/h] and those killing h
// (algebra_points.AlgebraPointsAwayInField); h divides c(t) for a nonzero polynomial
// c (ChartDividesLinePolynomial), so the points killing h kill c(t) and number at
// most deg c · m₀ (algebra_points.KilledPointsBound), m₀ bounding the points of A₀
// over a value of t (ChartFibreBound); the points at infinity lie over 0 in the other
// chart, at most m₁ of them.
var CurveCountNearAway = curveCountNearAwayThm{family.Add(registry.ProofEntry{
	Name: "CurveCountNearAway",
	Key:  "prop_5332e6fe4928bb3a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t h:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"h ∈ A₀",
			"h ≠ M.zero",
		},
		Conclusion: "∃C:num. ∀l:set(A). " +
			"    subfield(M, l) ∧ finite(l) ⇒ " +
			"    card(«pointsOf»(l, ring_away(field_ring(M), A₀, h))) ≤ «count»(l) ∧ " +
			"    «count»(l) ≤ card(«pointsOf»(l, ring_away(field_ring(M), A₀, h))) + C",
		Abbrev: Abbrev{
			{Name: "pointsOf", Text: "λl:set(A). λX:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), restrict_ring(field_ring(M), l), k, λx:A. x)"},
			{Name: "count", Text: "λl:set(A). curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁)"},
			{Name: "over", Text: "λl:set(A). λy:A. {e:A → A | e ∈ «pointsOf»(l, A₀) ∧ e(t) = y}"},
			{Name: "overInfinity", Text: "λl:set(A). λy:A. " +
				"    {e:A → A | e ∈ «pointsOf»(l, A₁) ∧ e(M.inv(t)) = y}"},
			{Name: "killedBy", Text: "λl:set(A). λx:A. {e:A → A | e ∈ «pointsOf»(l, A₀) ∧ e(x) = M.zero}"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t, h *Expr[A],
			inField, curve, hIn, hNonzero Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := field.RingOn.Read(M)
			zero := a.TermAs[A]("M.zero")
			identity := a.TermAs[Fun[A, A]]("λx:A. x")
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			swapped := a.Have(
				"read from its other chart, the curve lies over t⁻¹",
				"curve_over_line(restrict_field(M, K), k, M.inv(t), A₁, A₀, A₀₁)",
				By(curve, algebraic_curve.CurveSwap.Read(functionField).At(k, A0, A1, A01, t)))
			m0, fibres := a.ObtainAs[Nat](
				"each value of t carries at most m₀ points of A₀",
				"∃m₀:num. ∀l:set(A). ∀y:A. subfield(M, l) ⇒ finite(«over»(l, y)) ∧ card(«over»(l, y)) ≤ m₀",
				By(inField, curve, ChartFibreBound.Read(M).At(K, k, A0, A1, A01, t)))
			_, infinity := a.ObtainAs[Nat](
				"each value of t⁻¹ carries at most m₁ points of A₁",
				"∃m₁:num. ∀l:set(A). ∀y:A. "+
					"    subfield(M, l) ⇒ finite(«overInfinity»(l, y)) ∧ card(«overInfinity»(l, y)) ≤ m₁",
				By(inField, swapped, ChartFibreBound.Read(M).At(K, k, A1, A0, A01, a.TermAs[A]("M.inv(t)"))))
			c, w, division := a.Obtain2As[Fun[Nat, A], A](
				"h divides the value at t of a nonzero polynomial c over k",
				"∃c:(num → A). ∃w:A. polynomial_over(k, c) ∧ c ≠ vec_zero ∧ w ∈ A₀ ∧ polynomial_eval(c, t) = h * w",
				By(inField, curve, hIn, hNonzero, ChartDividesLinePolynomial.Read(M).At(K, k, A0, A1, A01, t, h)))
			divisionParts := a.Conjuncts(
				division,
				"c lies over k",
				"c is not zero",
				"w lies in A₀",
				"c(t) = h w")
			chart := a.Conjuncts(
				a.Have(
					"read in M, A₀ is a subring holding k and t",
					"subring(field_ring(M), A₀) ∧ k ⊆ A₀ ∧ t ∈ A₀",
					By(inField, curve, CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t))),
				"A₀ is a subring of M",
				"k lies in A₀",
				"t lies in A₀")
			a.Take(a.TermAs[Nat]("polynomial_degree(c) * m₀ + m₁"))
			l := a.FixAs[Set[A]]("l")
			given := a.Conjuncts(
				a.Assume(),
				"l is a subfield",
				"l is finite")
			counted := a.Conjuncts(
				GroupPremises(
					inField, curve, given[0], given[1], CurveCountAtInfinity.Read(M).At(K, k, A0, A1, A01, t, l)),
				"there are finitely many points at infinity",
				"the count is the points of A₀ and those at infinity")
			finiteChart := a.Have(
				"A₀ has finitely many points",
				"finite(«pointsOf»(l, A₀))",
				By(inField, curve, given[1], CurvePointSetsFinite.Read(M).At(K, k, A0, A1, A01, t, l)))
			split := a.Have(
				"inverting h splits off the points killing h",
				"card(«pointsOf»(l, A₀)) = "+
					"card(«pointsOf»(l, ring_away(field_ring(M), A₀, h))) + card(«killedBy»(l, h))",
				By(
					chart[0],
					given[0],
					chart[1],
					hIn,
					hNonzero,
					finiteChart,
					algebra_point_bounds.AlgebraPointsAwayInField.Read(M).At(A0, k, l, h)))
			killedBound := a.Conjuncts(
				a.Have(
					"at most deg c · m₀ points kill c(t)",
					"finite(«killedBy»(l, polynomial_eval(c, t))) ∧ "+
						"card(«killedBy»(l, polynomial_eval(c, t))) ≤ polynomial_degree(c) * m₀",
					By(
						chart[0],
						given[0],
						chart[1],
						chart[2],
						divisionParts[0],
						divisionParts[1],
						fibres.At(l),
						algebra_point_bounds.KilledPointsBound.Read(M).At(A0, k, l, t, c, m0))),
				"they are finite",
				"at most deg c · m₀ of them")
			source := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), A₀)")
			target := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), l)")
			killing := a.Have(
				"a point killing h kills c(t) = h w",
				"∀ψ:(A → A). ψ ∈ «pointsOf»(l, A₀) ∧ ψ(h) = M.zero ⇒ ψ(polynomial_eval(c, t)) = M.zero",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, A]]("ψ")
					point := b.Assume()
					ringMap := b.Have(
						"ψ is a ring map on A₀",
						"ring_homomorphism(restrict_ring(field_ring(M), A₀), restrict_ring(field_ring(M), l), ψ)",
						BySets(point, algebra_points.AlgebraPointsMember.At(source, target, k, identity, ψ)))
					image := b.Have(
						"ψ(w) lies in l, inside M",
						"ψ(w) ∈ M.carrier",
						BySets(
							divisionParts[2],
							given[0],
							ring_homomorphism.MapIn.Read(ringMap).AsFact().At(w),
							field.SubfieldSubset.At(ops, l)))
					b.Show(
						"ψ(h w) = ψ(h) ψ(w) = 0",
						By(
							point,
							divisionParts[3],
							hIn,
							divisionParts[2],
							ring_homomorphism.MapMul.Read(ringMap).AsFact().At(h, w),
							comm_ring.MulLeftZeroOn.Read(fieldRing).At(b.MemberOf[on.M](b.TermAs[A]("ψ(w)"), image))))
				}))
			killedH := a.TermAs[Set[Fun[A, A]]]("«killedBy»(l, h)")
			killedC := a.TermAs[Set[Fun[A, A]]]("«killedBy»(l, polynomial_eval(c, t))")
			inclusion := a.Have(
				"so the points killing h are among those killing c(t)",
				"«killedBy»(l, h) ⊆ «killedBy»(l, polynomial_eval(c, t))",
				BySets(killing))
			smaller := a.Have(
				"and at most as many",
				"card(«killedBy»(l, h)) ≤ card(«killedBy»(l, polynomial_eval(c, t)))",
				By(killedBound[0], inclusion, cardinality.CardSubset.At(killedH, killedC)))
			atInfinity := a.Have(
				"a point at infinity lies over 0 in A₁, at most m₁ of them",
				"card(«overInfinity»(l, M.zero)) ≤ m₁",
				By(given[0], infinity.At(l, zero)))
			a.Show(
				"so the count lies between those points and those points plus deg c · m₀ + m₁",
				ByArith(smaller, atInfinity, split, killedBound[1], counted[1]))
		}),
})}

// BirationalBiaffinePointCountBound — two curves over the line with one function
// field K, so birational, each covered by its two affine charts, one through t and
// one through u, have rational point counts within a bound B of each other over
// every finite subfield l. Each first chart lies in the other with one element
// inverted (ChartInsideAway), so inverting h in A₀ and g in B₀ makes them one ring
// (ring_away.CommonRingAway); each count is the number of points of that
// ring up to a bound fixed before l (CurveCountNearAway), and B is the sum of the
// two bounds.
var BirationalBiaffinePointCountBound = birationalBiaffinePointCountBoundThm{family.Add(registry.ProofEntry{
	Name: "BirationalBiaffinePointCountBound",
	Key:  "prop_7eb5f09c1bf2d078",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀B₀ B₁ B₀₁:set(A). ∀u:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"curve_over_line(restrict_field(M, K), k, u, B₀, B₁, B₀₁)",
		},
		Conclusion: "∃B:num. ∀l:set(A). " +
			"    subfield(M, l) ∧ finite(l) ⇒ " +
			"    dist((curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁), " +
			"            curve_rational_point_count(field_ring(M), k, l, B₀, B₁, B₀₁))) ≤ " +
			"    B",
		Abbrev: Abbrev{
			{Name: "pointsOf", Text: "λl:set(A). λX:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), restrict_ring(field_ring(M), l), k, λx:A. x)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			B0, B1, B01 *Expr[Set[A]],
			u *Expr[A],
			inField, curveA, curveB Fact,
		) {
			d, bInAway := a.ObtainAs[A](
				"B₀ lies in A₀ with some d inverted",
				"∃d:A. d ∈ A₀ ∧ d ≠ M.zero ∧ B₀ ⊆ ring_away(field_ring(M), A₀, d)",
				By(inField, curveA, curveB, ChartInsideAway.Read(M).At(K, k, A0, A1, A01, t, B0, B1, B01, u)))
			e, aInAway := a.ObtainAs[A](
				"and A₀ lies in B₀ with some e inverted",
				"∃e:A. e ∈ B₀ ∧ e ≠ M.zero ∧ A₀ ⊆ ring_away(field_ring(M), B₀, e)",
				By(inField, curveA, curveB, ChartInsideAway.Read(M).At(K, k, B0, B1, B01, u, A0, A1, A01, t)))
			h, g, common := a.Obtain2As[A, A](
				"both charts are subrings of M, so inverting h in A₀ and g in B₀ makes them one ring",
				"∃h g:A. "+
					"    h ∈ A₀ ∧ "+
					"    h ≠ M.zero ∧ "+
					"    g ∈ B₀ ∧ "+
					"    g ≠ M.zero ∧ "+
					"    ring_away(field_ring(M), A₀, h) = ring_away(field_ring(M), B₀, g)",
				By(
					inField,
					curveA,
					curveB,
					CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t),
					CurveOverLineChartsInField.Read(M).At(K, k, B0, B1, B01, u),
					bInAway,
					aInAway,
					ring_away.CommonRingAway.Read(M).At(A0, B0, d, e)))
			parts := a.Conjuncts(
				common,
				"h lies in A₀",
				"h is not zero",
				"g lies in B₀",
				"g is not zero",
				"A₀[1/h] is B₀[1/g]")
			_, nearA := a.ObtainAs[Nat](
				"the count of the first curve is, up to C₁, the number of points of A₀[1/h]",
				"∃C₁:num. ∀l:set(A). "+
					"    subfield(M, l) ∧ finite(l) ⇒ "+
					"    card(«pointsOf»(l, ring_away(field_ring(M), A₀, h))) ≤ "+
					"    curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁) ∧ "+
					"    curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁) ≤ "+
					"    card(«pointsOf»(l, ring_away(field_ring(M), A₀, h))) + C₁",
				By(inField, curveA, parts[0], parts[1], CurveCountNearAway.Read(M).At(K, k, A0, A1, A01, t, h)))
			_, nearB := a.ObtainAs[Nat](
				"the count of the second is, up to C₂, the number of points of B₀[1/g]",
				"∃C₂:num. ∀l:set(A). "+
					"    subfield(M, l) ∧ finite(l) ⇒ "+
					"    card(«pointsOf»(l, ring_away(field_ring(M), B₀, g))) ≤ "+
					"    curve_rational_point_count(field_ring(M), k, l, B₀, B₁, B₀₁) ∧ "+
					"    curve_rational_point_count(field_ring(M), k, l, B₀, B₁, B₀₁) ≤ "+
					"    card(«pointsOf»(l, ring_away(field_ring(M), B₀, g))) + C₂",
				By(inField, curveB, parts[2], parts[3], CurveCountNearAway.Read(M).At(K, k, B0, B1, B01, u, g)))
			a.Take(a.TermAs[Nat]("C₁ + C₂"))
			l := a.FixAs[Set[A]]("l")
			given := a.Conjuncts(
				a.Assume(),
				"l is a subfield",
				"l is finite")
			same := a.Have(
				"the one ring has one number of points",
				"card(«pointsOf»(l, ring_away(field_ring(M), A₀, h))) = "+
					"card(«pointsOf»(l, ring_away(field_ring(M), B₀, g)))",
				By(Normalized, parts[4]))
			a.Show(
				"each count is within C₁ + C₂ of the other",
				Simp(Fwd(nat_monus.DistLessEqCases)),
				ByArith(nearA.At(l), nearB.At(l), given[0], given[1], same))
		}),
})}

// ExtensionCountComparison — two curves over lines with one function field K,
// regular over the finite field k of an algebraically closed M, have extension
// counts within a fixed B of each other at every m > 0: at m the count is the
// rational point count over the field with card(k)^m points, a finite subfield
// of M, where BirationalBiaffinePointCountBound holds.
var ExtensionCountComparison = extensionCountComparisonThm{family.Add(registry.ProofEntry{
	Name: "ExtensionCountComparison",
	Key:  "prop_c989b54e270fd2ea",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "λm:num. finite_constants(field_ring(M), card(k), m)"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀B₀ B₁ B₀₁:set(A). ∀u:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"finite(k)",
			"regular_function_field(M, k, K)",
			"curve_over_line(restrict_field(M, K), k, u, B₀, B₁, B₀₁)",
		},
		Conclusion: "∃B:num. ∀m:num. " +
			"    0 < m ⇒ " +
			"    dist((curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m), " +
			"            curve_extension_count(field_ring(M), k, B₀, B₁, B₀₁, m))) ≤ " +
			"    B",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			B0, B1, B01 *Expr[Set[A]],
			u *Expr[A],
			closed, curveA, finiteK, regular, curveB Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(M)")
			subfields := a.Have(
				"k and K are subfields of M",
				"subfield(M, k) ∧ subfield(M, K)",
				By(regular, function_field.RegularFunctionFieldDef.At(a.TermAs[FieldOps[A]]("M"), k, K)))
			bound, overFields := a.ObtainAs[Nat](
				"over every finite subfield the rational point counts lie within a fixed B",
				"∃B:num. ∀l:set(A). "+
					"    subfield(M, l) ∧ finite(l) ⇒ "+
					"    dist((curve_rational_point_count(field_ring(M), k, l, A₀, A₁, A₀₁), "+
					"            curve_rational_point_count(field_ring(M), k, l, B₀, B₁, B₀₁))) ≤ "+
					"    B",
				By(
					subfields,
					curveA,
					curveB,
					BirationalBiaffinePointCountBound.Read(M).At(K, k, A0, A1, A01, t, B0, B1, B01, u)))
			a.Take(bound)
			m := a.FixAs[Nat]("m")
			positive := a.Assume()
			constants := a.TermAs[Set[A]]("«constants»(m)")
			fieldAtM := a.Have(
				"the constants at m are a finite subfield",
				"subfield(M, «constants»(m)) ∧ finite(«constants»(m))",
				By(
					closed,
					subfields,
					finiteK,
					positive,
					finite_field.FiniteConstantsSubfield.Read(M).At(k, m),
					cardinality.HasSizeDef))
			countA := a.Have(
				"at positive m the first count is its rational point count",
				"curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m) = "+
					"curve_rational_point_count(field_ring(M), k, «constants»(m), A₀, A₁, A₀₁)",
				ByArith(positive, CurveExtensionCountDef.At(ring, k, A0, A1, A01, m)))
			countB := a.Have(
				"and so is the second",
				"curve_extension_count(field_ring(M), k, B₀, B₁, B₀₁, m) = "+
					"curve_rational_point_count(field_ring(M), k, «constants»(m), B₀, B₁, B₀₁)",
				ByArith(positive, CurveExtensionCountDef.At(ring, k, B0, B1, B01, m)))
			a.Show(
				"the bound over the constants at m is the statement at m",
				By(overFields.At(constants), fieldAtM, countA, countB))
		}),
})}
