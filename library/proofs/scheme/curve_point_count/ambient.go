// ambient.go — a curve read inside a larger field. The chapter states a curve
// at one field; a constant extension compares subfields K ⊆ K' of a field M, so
// it reads those statements at restrict_field(M, K). That field keeps M's
// operations and its ring is M's ring restricted to K: InAmbient is that reading
// as one rewrite. A subring of K is a subring of M, which is no rewrite, so the
// charts are stated in M once: CurveChartsInField for a smooth curve,
// CurveOverLineChartsInField for a curve over the line, whose first chart
// CurveOverLineFirstChart reads over k[t].

package curve_point_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/registry"
)

// InAmbient — read in M a statement at restrict_field(M, K): the ring of that
// field is M's ring restricted to K, and a further restriction forgets K. M's
// operations need no rule, a law read at the fact field_on(restrict_field(M, K))
// stating them already. A statement about that ring itself keeps K as its
// carrier, as in subring(«ambientRing», A₀).
var InAmbient = RuleSet(
	Rev(field.RestrictFieldRing),
	Fwd(module_record.RestrictRingTwice),
	Fwd(module_record.RegularModuleRestrict),
	Fwd(module_record.RestrictModuleTwice))

// CurveChartsInField — the charts of a smooth curve over K read in M: the
// constants are a subfield of M lying in A₀, the charts are subrings of M, and
// the overlap is A₀ with t inverted, inside itself and inside M, the powers of t
// lying in A₀ and inverting those of its inverse in the overlap; read from its
// other chart, the curve is a curve in the inverse of t under M's operations. K
// lies in M, so a subring of K is one of M; the rest is smooth_curve.ChartSubring, smooth_curve.ChartOverlap
// and smooth_curve.SmoothCurveSwap at K, whose operations are M's.
var CurveChartsInField = curveChartsInFieldThm{family.Add(registry.ProofEntry{
	Name: "CurveChartsInField",
	Key:  "prop_c0ef2f5e42dc20f0",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"subfield(M, K)", "«ambientCurve»"},
		Conclusion: "subfield(M, k) ∧ " +
			"k ⊆ A₀ ∧ " +
			"subring(field_ring(M), A₀) ∧ " +
			"subring(field_ring(M), A₀₁) ∧ " +
			"comm_ring_on(«overlap») ∧ " +
			"A₀ ⊆ A₀₁ ∧ " +
			"t ∈ A₀ ∧ " +
			"t ≠ M.zero ∧ " +
			"M.inv(t) ∈ A₀₁ ∧ " +
			"t * M.inv(t) = M.one ∧ " +
			"A₀₁ = ring_away(«overlap», A₀, t) ∧ " +
			"A₀₁ = ring_away(field_ring(M), A₀, t) ∧ " +
			"(∀j:num. «tPow»(j) ∈ A₀ ∧ «sPow»(j) ∈ A₀₁ ∧ «tPow»(j) * «sPow»(j) = M.one) ∧ " +
			"smooth_finite_curve(restrict_field(M, K), k, M.inv(t), A₁, A₀, A₀₁)",
		Abbrev: Abbrev{
			{Name: "overlap", Text: "restrict_ring(field_ring(M), A₀₁)"},
			{Name: "tPow", Text: "λj:num. monoid_pow(M.mul, M.one, t, j)"},
			{Name: "sPow", Text: "λj:num. monoid_pow(M.mul, M.one, M.inv(t), j)"},
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
			ring := a.TermAs[RingOps[A]]("field_ring(M)")
			functionRing := a.TermAs[RingOps[A]]("«ambientRing»")
			inverse := a.TermAs[A]("M.inv(t)")
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			chart := a.Simplified(
				GroupPremises(curve, smooth_curve.ChartSubring.Read(functionField).At(k, A0, A1, A01, t)),
				InAmbient)
			overlap := a.Simplified(
				GroupPremises(curve, smooth_curve.ChartOverlap.Read(functionField).At(k, A0, A1, A01, t)),
				InAmbient)
			inCarrier := a.Have(
				"the chart and the overlap lie in K, inside M",
				"A₀ ⊆ M.carrier ∧ A₀₁ ⊆ M.carrier",
				BySets(
					inField,
					overlap,
					comm_ring.SubringSubset.At(functionRing, A01),
					field.SubfieldSubset.At(ops, K)))
			rings := a.Have(
				"under M's operations, which are K's, the chart and the overlap are rings",
				"comm_ring_on(restrict_ring(field_ring(M), A₀)) ∧ comm_ring_on(«overlap»)",
				By(
					a.Simplified(
						GroupPremises(curve, smooth_curve.ChartCommRing.Read(functionField).At(k, A0, A1, A01, t)),
						InAmbient),
					a.Simplified(
						GroupPremises(curve, smooth_curve.OverlapCommRing.Read(functionField).At(k, A0, A1, A01, t)),
						InAmbient)))
			subrings := a.Have(
				"so they are subrings of M",
				"subring(field_ring(M), A₀) ∧ subring(field_ring(M), A₀₁)",
				By(
					inCarrier,
					rings,
					comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(A0),
					comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(A01)))
			coordinateIn := a.Have(
				"t lies in the overlap",
				"t ∈ A₀₁",
				BySets(overlap))
			away := a.Have(
				"inverting t inside the overlap and inside M give one ring",
				"ring_away(«overlap», A₀, t) = ring_away(field_ring(M), A₀, t)",
				By(
					subrings,
					coordinateIn,
					overlap,
					field.RingOn.Read(M),
					ring_away.RingAwayInSubring.At(ring, A01, A0, t, inverse)))
			swapped := a.Have(
				"read from its other chart, the curve is a curve in the inverse of t",
				"smooth_finite_curve(restrict_field(M, K), k, M.inv(t), A₁, A₀, A₀₁)",
				By(curve, smooth_curve.SmoothCurveSwap.Read(functionField).At(k, A0, A1, A01, t)))
			a.Show(
				"a subfield of K is a subfield of M, and the clauses stand",
				By(inField, chart, overlap, rings, subrings, away, swapped, field.SubfieldTrans.At(ops, K, k)))
		}),
})}

// CurveOverLineChartsInField — the charts of a curve over the line in K, read in
// M: both charts and the overlap are subrings of M lying between k and K, and t
// lies in the first chart. Read in K the three are subrings, the overlap holds
// both charts and the charts meet in k (algebraic_curve.CurveOverItsLine); K
// keeps M's operations, so a subring of K is a subring of M.
var CurveOverLineChartsInField = curveOverLineChartsInFieldThm{family.Add(registry.ProofEntry{
	Name: "CurveOverLineChartsInField",
	Key:  "prop_594ec9f53f4dc1f9",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "subring(field_ring(M), A₀) ∧ " +
			"subring(field_ring(M), A₁) ∧ " +
			"subring(field_ring(M), A₀₁) ∧ " +
			"k ⊆ A₀ ∧ " +
			"k ⊆ A₁ ∧ " +
			"k ⊆ A₀₁ ∧ " +
			"A₀ ⊆ K ∧ " +
			"A₁ ⊆ K ∧ " +
			"A₀₁ ⊆ K ∧ " +
			"t ∈ A₀",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			inField, curve Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			ring := a.TermAs[RingOps[A]]("field_ring(M)")
			functionRing := a.TermAs[RingOps[A]]("field_ring(restrict_field(M, K))")
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			datum := a.Have(
				"read in K, the charts and the overlap are subrings, the "+
					"overlap holds both charts, the charts meet in k and t lies in A₀",
				"subring(field_ring(restrict_field(M, K)), A₀) ∧ "+
					"subring(field_ring(restrict_field(M, K)), A₁) ∧ "+
					"subring(field_ring(restrict_field(M, K)), A₀₁) ∧ "+
					"A₀ ⊆ A₀₁ ∧ "+
					"A₁ ⊆ A₀₁ ∧ "+
					"A₀ ∩ A₁ = k ∧ "+
					"t ∈ A₀",
				By(curve, algebraic_curve.CurveOverItsLine.Read(functionField).At(k, A0, A1, A01, t)))
			inM := a.Have(
				"a subring of K is a subring of M lying in K",
				"∀X:set(A). subring(field_ring(restrict_field(M, K)), X) ⇒ subring(field_ring(M), X) ∧ X ⊆ K",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					inK := b.Assume()
					b.Show(
						"the two rings have M's operations, and K lies in M",
						BySets(
							inField,
							inK,
							comm_ring.SubringDef.At(ring, X),
							comm_ring.SubringDef.At(functionRing, X),
							field.SubfieldSubset.At(ops, K)))
				}))
			a.Show(
				"so each is a subring of M lying in K, and holds k = A₀ ∩ A₁",
				BySets(datum, inM.At(A0), inM.At(A1), inM.At(A01)))
		}),
})}

// CurveOverLineFirstChart — the first chart of a curve over the line read in
// the ambient field: the chart and the overlap are subrings lying in K, the
// chart holds k and t, a power of t carries the overlap into the chart, k[t] is
// a subring of M lying in the chart, the chart is free of finite rank over
// k[t], and K is its field of fractions. The subrings, K and k are
// CurveOverLineChartsInField; k is a subfield of K, so of M, and t lies in M,
// so k[t] is a subring; the rest are clauses of the curve read in K, which
// keeps M's operations, the overlap being the chart with t inverted.
var CurveOverLineFirstChart = curveOverLineFirstChartThm{family.Add(registry.ProofEntry{
	Name: "CurveOverLineFirstChart",
	Key:  "prop_fdcd9b6a7c0f1f29",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "subring(field_ring(M), A₀) ∧ " +
			"subring(field_ring(M), A₀₁) ∧ " +
			"A₀ ⊆ K ∧ " +
			"A₀₁ ⊆ K ∧ " +
			"k ⊆ A₀ ∧ " +
			"A₀ ⊆ A₀₁ ∧ " +
			"t ∈ A₀ ∧ " +
			"(∀x:A. x ∈ A₀₁ ⇒ ∃n:num. monoid_pow(M.mul, M.one, t, n) * x ∈ A₀) ∧ " +
			"subring(field_ring(M), «polynomials») ∧ " +
			"«polynomials» ⊆ A₀ ∧ " +
			"(∃B:set(A). " +
			"    finite(B) ∧ " +
			"    module_basis(restrict_ring(field_ring(M), «polynomials»), " +
			"        restrict_module(regular_module(field_ring(M)), A₀), " +
			"        B)) ∧ " +
			"fraction_field_carrier(«ambientRing», A₀)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			inField, curve Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			overlapRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), A₀₁)")
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			definition := a.Unfolded(curve, algebraic_curve.CurveOverLineDef)
			datum := a.Simplified(
				GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(functionField).At(k, A0, A1, A01, t)),
				Fwd(field.RestrictFieldRecords),
				Fwd(algebraic_element.RestrictFieldReadings))
			line := a.Conjuncts(
				a.Have(
					"read in M, the overlap holds the chart and is the chart with t "+
						"inverted, and the chart holds k[t] and is free of finite rank over it",
					"A₀ ⊆ A₀₁ ∧ "+
						"A₀₁ = ring_away(restrict_ring(field_ring(M), A₀₁), A₀, t) ∧ "+
						"«polynomials» ⊆ A₀ ∧ "+
						"(∃B:set(A). "+
						"    finite(B) ∧ "+
						"    module_basis(restrict_ring(field_ring(M), «polynomials»), "+
						"        restrict_module(regular_module(field_ring(M)), A₀), "+
						"        B))",
					By(datum)),
				"the overlap holds the chart",
				"the overlap is the chart with t inverted",
				"the chart holds k[t]",
				"the chart is free of finite rank over k[t]")
			clears := a.Have(
				"so a power of t carries each member of the overlap into the chart",
				"∀x:A. x ∈ A₀₁ ⇒ ∃n:num. monoid_pow(M.mul, M.one, t, n) * x ∈ A₀",
				a.ForEach(func(x *Expr[A]) Action {
					return By(line[1], ring_away.RingAwayMember.At(overlapRing, A0, t, x))
				}))
			tIn := a.Have(
				"t lies in K, so in M",
				"t ∈ M.carrier",
				BySets(inField, definition, field.SubfieldSubset.At(ops, K)))
			polynomialRing := a.Have(
				"k is a subfield of K, so of M, and k[t] is a subring of M",
				"subring(field_ring(M), «polynomials»)",
				By(
					inField,
					definition,
					field.SubfieldTrans.At(ops, K, k),
					algebraic_element.PolynomialImageRing.Read(M).At(k, a.MemberOf[on.M](t, tIn))))
			fractions := a.Have(
				"K is the field of fractions of the chart, M's ring on K being the ring of K",
				"fraction_field_carrier(«ambientRing», A₀)",
				By(definition, field.RestrictFieldRing.At(ops, K)))
			a.Show(
				"the charts read in M give the subrings, K and k, and the rest is in hand",
				By(
					inField,
					curve,
					line[0],
					line[2],
					line[3],
					clears,
					polynomialRing,
					fractions,
					CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t)))
		}),
})}
