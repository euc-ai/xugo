// points.go — the rational points of the curve inside its function
// field: the point of a solution (x₀, y₀) of the affine equation, given
// by the ideal of x − x₀ and y − y₀ in chart 0, the origin at infinity,
// given by the ideal of s and u in chart 1, and the conjugation y ↦ −y;
// every rational point is one of them, and each is regular — the origin
// always, an affine point where 2y₀ ≠ 0 or 3x₀² + a ≠ 0, so every point
// when 2 ≠ 0 and 4a³ + 27b² ≠ 0.

package elliptic_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// weierstrassPointDef — `weierstrass_point(L, k, x, y, x₀, y₀)`: the ideal
// pair of the affine point (x₀, y₀): in chart 0 the ideal of x − x₀ and
// y − y₀, in chart 1 the members of chart 1 in the ideal that one
// generates in the overlap.
var weierstrassPointDef = weierstrassPointDefThm{family.Define(registry.DefEntry{
	Name:     "weierstrassPointDef",
	Key:      "prop_75ba82e0353ca87d",
	Const:    "weierstrass_point",
	Type:     "field_ops(A) → set(A) → A → A → A → A → prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀x₀:A. ∀y₀:A. " +
			"    weierstrass_point(F, k, x, y, x₀, y₀) = " +
			"    (ideal_span(restrict_ring(field_ring(F), weierstrass_chart_zero(field_ring(F), k, x, y)), " +
			"            {F.sub(x, x₀), F.sub(y, y₀)}), " +
			"        weierstrass_chart_one(F, k, x, y) ∩ " +
			"        ideal_span(restrict_ring(field_ring(F), " +
			"                ring_away(field_ring(F), weierstrass_chart_zero(field_ring(F), k, x, y), x)), " +
			"            ideal_span( " +
			"                restrict_ring(field_ring(F), weierstrass_chart_zero(field_ring(F), k, x, y)), " +
			"                {F.sub(x, x₀), F.sub(y, y₀)})))",
	},
	Reading: "The representation biaffine_rational_point reads: one ideal per chart. A point " +
		"with x₀ = zero lies off chart 1 — x is in its ideal and a unit of the overlap, so the meet " +
		"is all of chart 1 — and a point with x₀ ≠ zero lies on both charts, its chart-1 ideal that " +
		"of s − 1/x₀ and u − y₀/x₀² (AffinePointCharts). (x₀, y₀) off the curve gives chart 0 itself, " +
		"y² − (x³ + ax + b) = zero putting the nonzero constant y₀² − (x₀³ + ax₀ + b) in the ideal.",
	Deps: []registry.EntryLike{WeierstrassChartZeroDef, WeierstrassChartOneDef},
})}

// WeierstrassOriginDef — `weierstrass_origin(k, x, y)`: the ideal pair of
// the point at infinity: chart 0 itself, off which it lies, and in
// chart 1 the ideal of s = 1/x and u = y/x².
var WeierstrassOriginDef = weierstrassOriginDefThm{family.Define(registry.DefEntry{
	Name:     "WeierstrassOriginDef",
	Key:      "prop_c68aa9ef70efb2fa",
	Const:    "weierstrass_origin",
	Type:     "field_ops(A) → set(A) → A → A → prod(set(A), set(A))",
	Implicit: []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. " +
			"    weierstrass_origin(F, k, x, y) = " +
			"    (weierstrass_chart_zero(field_ring(F), k, x, y), " +
			"        ideal_span(restrict_ring(field_ring(F), weierstrass_chart_one(F, k, x, y)), " +
			"            {F.inv(x), F.mul(y, F.mul(F.inv(x), F.inv(x)))}))",
	},
	Reading: "The point at infinity, the one point of the curve where " +
		"x has a pole: on chart 1, s = zero forces u² = zero by u² = s · (1 " +
		"+ as² + bs³), so s and u vanish together there and nowhere else.",
	Deps: []registry.EntryLike{WeierstrassChartZeroDef, WeierstrassChartOneDef},
})}

// WeierstrassNegPointDef — `weierstrass_neg_point(k, x, y, P)`: the
// conjugation y ↦ −y applied to the ideal pair P chart by chart — p + q·y
// ↦ p − q·y on chart 0 and p + q·u ↦ p − q·u on chart 1, p and q in the
// chart's polynomial ring.
var WeierstrassNegPointDef = weierstrassNegPointDefThm{family.Define(registry.DefEntry{
	Name:     "WeierstrassNegPointDef",
	Key:      "prop_a73aac4a24c87d1d",
	Const:    "weierstrass_neg_point",
	Type:     "field_ops(A) → set(A) → A → A → prod(set(A), set(A)) → prod(set(A), set(A))",
	Implicit: []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀P:prod(set(A), set(A)). " +
			"    weierstrass_neg_point(F, k, x, y, P) = " +
			"    ({F.add(p, F.neg(F.mul(q, y))) | " +
			"            p:A, " +
			"            q:A | " +
			"            p ∈ polynomial_image(field_ring(F), k, x) ∧ " +
			"            q ∈ polynomial_image(field_ring(F), k, x) ∧ " +
			"            F.add(p, F.mul(q, y)) ∈ fst(P)}, " +
			"        {F.add(p, F.neg(F.mul(q, F.mul(y, F.mul(F.inv(x), F.inv(x)))))) | " +
			"            p:A, " +
			"            q:A | " +
			"            p ∈ polynomial_image(field_ring(F), k, F.inv(x)) ∧ " +
			"            q ∈ polynomial_image(field_ring(F), k, F.inv(x)) ∧ " +
			"            F.add(p, F.mul(q, F.mul(y, F.mul(F.inv(x), F.inv(x))))) ∈ snd(P)})",
	},
	Reading: "Defined on every pair of subsets, with no choice: each member of a chart has one " +
		"expression p + q·y, or p + q·u, at a datum (WeierstrassBasisZero, WeierstrassBasisOne), so " +
		"on subsets of the charts this is the image under the conjugation, an automorphism of each " +
		"chart. It sends the point (x₀, y₀) to (x₀, −y₀) and the origin to itself (NegPointValues).",
})}

// ---------------------------------------------------------------------------
// The rational points
// ---------------------------------------------------------------------------

// AffinePointMaximal — a solution (x₀, y₀) in k of the affine equation
// gives a rational point: its chart-0 ideal is the kernel of the
// evaluation at (x₀, y₀), a maximal ideal with residue field k.
var AffinePointMaximal = affinePointMaximalThm{family.Add(registry.ProofEntry{
	Name: "AffinePointMaximal",
	Key:  "prop_1b25a3aaf97a1bd",
	Reading: "The evaluation p(x) + q(x)·y ↦ p(x₀) + q(x₀)·y₀ is defined because 1, y " +
		"is a basis over the polynomial ring k[x], and keeps products because y₀² = x₀³ + " +
		"ax₀ + b. The equation is load-bearing: off the curve the ideal of x − x₀ and y − " +
		"y₀ holds the nonzero constant y₀² − (x₀³ + ax₀ + b) and is chart 0 itself.",
	Deps: []registry.EntryLike{
		weierstrassPointDef,
		AffinePointCharts,
		WeierstrassBasisZero,
		WeierstrassImageIsomorphism,
		biaffine_rational_point.BiaffineRationalPointDef,
		ring_ideal.MaximalIdealDef,
		ring_ideal.IdealSpanDef,
		ring_ideal.SpanInsert,
		polynomial_roots.FactorTheorem,
		polynomial_evaluation.EvalHomomorphism,
		algebraic_element.EvalInjectiveTranscendental,
		ring_away.RingAwayDef,
		field.InvIn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
		},
		Conclusion: "biaffine_rational_point(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    weierstrass_point(L, k, x, y, x₀, y₀)) ∧ " +
			"maximal_ideal(restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"    fst(weierstrass_point(L, k, x, y, x₀, y₀))) ∧ " +
			"fst(weierstrass_point(L, k, x, y, x₀, y₀)) = " +
			"{polynomial_eval(p, x) + polynomial_eval(q, x) * y | " +
			"    p:num → A, " +
			"    q:num → A | " +
			"    polynomial_over(k, p) ∧ " +
			"    polynomial_over(k, q) ∧ " +
			"    polynomial_eval(p, x₀) + polynomial_eval(q, x₀) * y₀ = L.zero}",
	},
		"the evaluation is a ring map from chart 0 onto k (WeierstrassBasisZero for the expression, "+
			"EvalInjectiveTranscendental for the polynomials, EvalHomomorphism; or the evaluation of the "+
			"free algebra through induced_map and WeierstrassImageIsomorphism); its kernel is the ideal "+
			"of x − x₀ and y − y₀, since p + q·y = (p − p(x₀)) + (q − q(x₀))·y + q(x₀)·(y − y₀) + (p(x₀) "+
			"+ q(x₀)·y₀) with x − x₀ dividing p − p(x₀) (FactorTheorem, SpanInsert); a kernel of a map "+
			"onto the field k is maximal with residue field k (MaximalIdealDef). The rational point "+
			"(BiaffineRationalPointDef): chart 1 by AffinePointCharts; for x₀ ≠ zero the evaluation "+
			"extends to the overlap, x ↦ x₀ being invertible (RingAwayDef, InvIn), and its kernel there "+
			"is the ideal both chart ideals generate, proper; for x₀ = zero both generate the overlap"),
})}

// AffinePointCharts — the affine point (x₀, y₀) lies on chart 1 exactly
// when x₀ ≠ 0, and there its ideal is that of s − 1/x₀ and u − y₀/x₀².
var AffinePointCharts = affinePointChartsThm{family.Add(registry.ProofEntry{
	Name: "AffinePointCharts",
	Key:  "prop_13ba199bd0f5a8ac",
	Reading: "x is a unit of the overlap, so a point lies off chart 1 exactly when x " +
		"vanishes at it. For x₀ ≠ zero the point is (1/x₀, y₀/x₀²) in the coordinates of chart " +
		"1: s − 1/x₀ = (x₀ − x)/(x·x₀) and u − y₀/x₀² = (x₀²·(y − y₀) + y₀·(x₀² − x²))/(x²·x₀²) " +
		"lie in the ideal the point generates in the overlap. For x₀ ≠ zero the trace on chart " +
		"1 is proper because evaluation at (x₀, y₀) extends to the overlap, x₀ being invertible.",
	Deps: []registry.EntryLike{
		weierstrassPointDef,
		WeierstrassBasisOne,
		WeierstrassChartOneEquation,
		FactoredRelation,
		ring_away.RingAwayDef,
		ring_ideal.IdealSpanDef,
		ring_ideal.SpanInsert,
		ring_ideal.IdealOneIff,
		ring_ideal.MaximalIdealDef,
		polynomial_roots.FactorTheorem,
		field.MulRightInverseOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
		},
		Conclusion: "(snd(weierstrass_point(L, k, x, y, x₀, y₀)) = weierstrass_chart_one(L, k, x, y) ⇔ " +
			"    x₀ = L.zero) ∧ " +
			"(x₀ ≠ L.zero ⇒ " +
			"    snd(weierstrass_point(L, k, x, y, x₀, y₀)) = " +
			"    ideal_span(restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"        {L.inv(x) - L.inv(x₀), y * (L.inv(x) * L.inv(x)) - y₀ * (L.inv(x₀) * L.inv(x₀))}))",
	},
		"x₀ = zero: x lies in the chart-0 ideal and inv(x) in the overlap, so the generated "+
			"ideal is the overlap (IdealOneIff) and its meet with chart 1 is chart 1. x₀ ≠ zero: the "+
			"two generators lie in chart 1 and, by the reading's expressions, in the generated "+
			"ideal; the ideal they generate in chart 1 is the kernel of the evaluation of chart 1 at "+
			"(1/x₀, y₀/x₀²), a ring map onto k since u₀² = s₀ + as₀³ + bs₀⁴ (WeierstrassBasisOne, "+
			"WeierstrassChartOneEquation, FactorTheorem), so it is maximal (MaximalIdealDef); the "+
			"meet of chart 1 with the generated ideal is proper — the evaluation at (x₀, y₀) extends "+
			"to the overlap, x₀ being invertible, and kills it — so it is that maximal ideal"),
})}

// OriginMaximal — the origin is a rational point: its chart-1 ideal I, the
// ideal of s and u, consists of the P(s) + Q(s)·u with P(0) = zero and is
// maximal with residue field k. Each member of chart 1 is P(s) + Q(s)·u, and
// P(s) = P(0) + w·s with w in k[s] (the factor theorem at zero), so it is
// congruent to P(0) modulo I. One lies outside I: one = c·s + r·u with c and
// r in chart 1 would make one = s·W with W in k[s], one and y being
// independent over k[x, 1/x], and no nonzero member of k[x] is a negative
// power of x times a member of k[1/x]. So I is the ideal of a k-rational
// point, maximal, and meets k only at zero, which pins P(0) = zero on I.
// Both chart ideals generate the overlap: chart 0 holds one, and I holds s,
// the coordinate of the curve read from chart 1.
var OriginMaximal = originMaximalThm{family.Add(registry.ProofEntry{
	Name: "OriginMaximal",
	Key:  "prop_43577b4ed28341e2",
	Reading: "No hypothesis on a and b: the residue of P(s) + Q(s)·u modulo I is " +
		"P(0) for every cubic, the nodal and cuspidal ones included. Off chart 0 the " +
		"origin's chart-0 ideal is the chart, and s = 1/x, a unit of the overlap, " +
		"makes both ideals generate the overlap, as a point on one chart only must.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "biaffine_rational_point(restrict_ring(field_ring(L), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    weierstrass_origin(L, k, x, y)) ∧ " +
			"maximal_ideal(restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"    snd(weierstrass_origin(L, k, x, y))) ∧ " +
			"snd(weierstrass_origin(L, k, x, y)) = " +
			"{polynomial_eval(p, L.inv(x)) + polynomial_eval(q, L.inv(x)) * (y * (L.inv(x) * L.inv(x))) | " +
			"    p:num → A, " +
			"    q:num → A | " +
			"    polynomial_over(k, p) ∧ polynomial_over(k, q) ∧ p(0) = L.zero}",
		Abbrev: Abbrev{
			{Name: "chartOneRing", Text: "restrict_ring(field_ring(L), «curveChart1»)"},
			{Name: "originIdeal", Text: "ideal_span(«chartOneRing», {L.inv(x), «curveU»})"},
			{Name: "uIdeal", Text: "ideal_span(«chartOneRing», {«curveU»})"},
			{Name: "X", Text: "basis_vector(1) - L.zero • basis_vector(0)"},
			// W and D are written over the cofactors p₁, q₁ of c and p₂, q₂ of r that
			// the step "one lies outside I" obtains: one = s · W, D · s² the y-part.
			{Name: "W", Text: "(p₁ + q₂ * (L.one + a * «curveS2» + b * (L.inv(x) * «curveS2»)))"},
			{Name: "D", Text: "(L.inv(x) * q₁ + p₂)"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			ringL := field.RingOn.Read(L)
			fieldL, fieldRing, inv :=
				arg.TermAs[field.FieldOps[A]]("L"),
				arg.TermAs[RingOps[A]]("field_ring(L)"),
				arg.TermAs[Fun[A, A]]("L.inv")
			xm, ym :=
				arg.MemberOf[on.L](x, WeierstrassXInField.Read(datum).AsFact()),
				arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())
			sm := field.InvIn.Read(L).At(xm)
			s, u, zero := arg.TermAs[A]("L.inv(x)"), arg.TermAs[A]("«curveU»"), arg.TermAs[A]("L.zero")
			chartOne, ks, ideal :=
				arg.TermAs[Set[A]]("«curveChart1»"),
				arg.TermAs[Set[A]]("«curveKs»"),
				arg.TermAs[Set[A]]("«originIdeal»")
			chartOneRing, overlapRing :=
				arg.TermAs[RingOps[A]]("«chartOneRing»"), arg.TermAs[RingOps[A]]("«curveOverlapRing»")
			overlapSet := arg.TermAs[Set[A]]("«curveOverlap»")
			// The members of k[s] and of chart 1 written through polynomials over k.
			valuesInKs := arg.Have(
				"the polynomials over k take their values at s in k[s]",
				"∀P:(num → A). polynomial_over(k, P) ⇒ polynomial_eval(P, L.inv(x)) ∈ «curveKs»",
				Unfold(algebraic_element.PolynomialImageDef),
				SetTac())
			chartOnePolynomials := arg.Have(
				"a member of chart 1 is P(s) + Q(s) · u with P and Q polynomials over k",
				Statement{
					Binders:    "∀z:A.",
					Hypotheses: []string{"z ∈ «curveChart1»"},
					Conclusion: "∃P Q:num → A. " +
						"    polynomial_over(k, P) ∧ " +
						"    polynomial_over(k, Q) ∧ " +
						"    z = polynomial_eval(P, L.inv(x)) + polynomial_eval(Q, L.inv(x)) * «curveU»",
				},
				Unfold(WeierstrassChartOneDef),
				Unfold(algebraic_element.PolynomialImageDef),
				SetTac())
			invertible := arg.Conjuncts(
				GroupPremises(datum, WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")

			kSubfield := arg.Simplified(WeierstrassSubfield.Read(datum).AsFact())
			line := arg.Conjuncts(
				arg.Have(
					"k[x] and k[s] are subrings of L, k[s] holding k and s and lying in k[x, 1/x]",
					"subring(field_ring(L), «curveKx») ∧ "+
						"subring(field_ring(L), «curveKs») ∧ "+
						"k ⊆ «curveKs» ∧ "+
						"L.inv(x) ∈ «curveKs» ∧ "+
						"«curveKs» ⊆ «curveLaurent»",
					By(GroupPremises(invertible[0], kSubfield, projective_line.LineDatum.Read(L).At(k, xm)))),
				"k[x] is a subring of L",
				"so is k[s]",
				"k lies in k[s]",
				"s lies in k[s]",
				"k[s] lies in k[x, 1/x]")
			kxSubring, ksSubring, kInKs, sInKs, ksInLaurent := line[0], line[1], line[2], line[3], line[4]
			ksRing := arg.Have(
				"k[s] is a ring under the operations of L",
				"comm_ring_on(restrict_ring(field_ring(L), «curveKs»))",
				By(ksSubring, comm_ring.SubringRingOn.Read(ringL).At(ks)))

			// Chart 1: a ring holding k[s], s and u.
			chartOneFacts := arg.Conjuncts(
				GroupPremises(datum, WeierstrassBasisOne.Read(L).At(k, x, y, a, b)),
				"chart 1 is a subring of L",
				"holding k[s]",
				"free over k[s] on one and u",
				"one is not u")
			chartOneSubring, ksInChartOne := chartOneFacts[0], chartOneFacts[1]
			ringOne := arg.Have(
				"chart 1 is a ring under the operations of L",
				"comm_ring_on(«chartOneRing»)",
				By(chartOneSubring, comm_ring.SubringRingOn.Read(ringL).At(chartOne)))
			inChartOne := arg.Conjuncts(
				arg.Have(
					"k and s lie in chart 1, as k[s] does, and chart 1 lies in L",
					"k ⊆ «curveChart1» ∧ L.inv(x) ∈ «curveChart1» ∧ «curveChart1» ⊆ L.carrier",
					BySets(kInKs, sInKs, ksInChartOne, comm_ring.SubringSubset.Read(chartOneSubring))),
				"k lies in chart 1",
				"s lies in chart 1",
				"chart 1 lies in L")
			kInChartOne, sIn, chartOneInL := inChartOne[0], inChartOne[1], inChartOne[2]
			uExpansion := arg.Have(
				"u is zero + one · u, zero and one lying in k[s]",
				"∃p q:A. p ∈ «curveKs» ∧ q ∈ «curveKs» ∧ «curveU» = p + q * «curveU»",
				Witness(zero),
				Witness(arg.TermAs[A]("L.one")),
				ByArith(ringL, ym, sm, comm_ring.SubringZero.Read(ksSubring), comm_ring.SubringOne.Read(ksSubring)))
			uIn := arg.Have(
				"so u lies in chart 1",
				"«curveU» ∈ «curveChart1»",
				By(uExpansion, WeierstrassChartOneMembers.At(fieldL, k, x, y, u)))

			// I is an ideal of chart 1 holding s and u.
			generatorSet := arg.TermAs[Set[A]]("{L.inv(x), «curveU»}")
			generators := arg.Have(
				"s and u lie in chart 1",
				"{L.inv(x), «curveU»} ⊆ «curveChart1»",
				Simp(Fwd(set_order.InsertSubset), Fwd(set_order.EmptySubset)),
				By(sIn, uIn))
			idealI := arg.Have(
				"they generate an ideal I of chart 1",
				"ring_ideal(«chartOneRing», «originIdeal»)",
				By(generators, ring_ideal.SpanIdeal.Read(ringOne).At(generatorSet)))
			generatorsIn := arg.Conjuncts(
				arg.Have(
					"which holds s and u",
					"L.inv(x) ∈ «originIdeal» ∧ «curveU» ∈ «originIdeal»",
					BySets(ring_ideal.SpanContains.At(chartOneRing, generatorSet))),
				"s lies in I",
				"u lies in I")
			sInI, uInI := generatorsIn[0], generatorsIn[1]

			// One lies outside I.
			proper := arg.Have(
				"one lies outside I: one = c · s + r · u would make one a multiple s · W with W in k[s]",
				"L.one ∉ «originIdeal»",
				Derive(func(d *Argument) {
					oneIn := d.SupposeNot()
					uSingleton := d.Have(
						"{u} lies in chart 1",
						"{«curveU»} ⊆ «curveChart1»",
						Simp(Fwd(set_order.InsertSubset), Fwd(set_order.EmptySubset)),
						By(uIn))
					decomposition := d.Have(
						"a member of I is c · s + t with c in chart 1 and t in the ideal of u",
						"∀z:A. z ∈ «originIdeal» ⇔ ∃c t:A. c ∈ «curveChart1» ∧ t ∈ «uIdeal» ∧ z = c * L.inv(x) + t",
						BySets(
							uSingleton,
							ring_ideal.SpanInsert.Read(ringOne).At(d.TermAs[Set[A]]("{«curveU»}"), d.MemberOf[on.Any](s, sIn))))
					multiples := d.Have(
						"and a member of the ideal of u is r · u with r in chart 1",
						"∀t:A. t ∈ «uIdeal» ⇔ ∃r:A. r ∈ «curveChart1» ∧ t = r * «curveU»",
						BySets(ring_ideal.PrincipalIdealMultiples.Read(ringOne).At(d.MemberOf[on.Any](u, uIn))))
					c, t, oneSum := d.Obtain2As[A, A](
						"one = c · s + t with c in chart 1 and t in the ideal of u",
						"∃c t:A. c ∈ «curveChart1» ∧ t ∈ «uIdeal» ∧ L.one = c * L.inv(x) + t",
						By(decomposition.At(d.TermAs[A]("L.one")), oneIn))
					oneParts := d.Conjuncts(
						oneSum,
						"c lies in chart 1",
						"t lies in the ideal of u",
						"one = c · s + t")
					r, tMultiple := d.ObtainAs[A](
						"t = r · u with r in chart 1",
						"∃r:A. r ∈ «curveChart1» ∧ t = r * «curveU»",
						By(multiples.At(t), oneParts[1]))
					tParts := d.Conjuncts(
						tMultiple,
						"r lies in chart 1",
						"t = r · u")
					oneForm := d.Have(
						"so one = c · s + r · u",
						"L.one = c * L.inv(x) + r * «curveU»",
						By(Normalized, oneParts[2], tParts[1]))
					_, _, cForm := d.Obtain2As[A, A](
						"c = p₁ + q₁ · u with p₁ and q₁ in k[s]",
						"∃p₁ q₁:A. p₁ ∈ «curveKs» ∧ q₁ ∈ «curveKs» ∧ c = p₁ + q₁ * «curveU»",
						By(oneParts[0], WeierstrassChartOneMembers.At(fieldL, k, x, y, c)))
					_, q2, rForm := d.Obtain2As[A, A](
						"r = p₂ + q₂ · u with p₂ and q₂ in k[s]",
						"∃p₂ q₂:A. p₂ ∈ «curveKs» ∧ q₂ ∈ «curveKs» ∧ r = p₂ + q₂ * «curveU»",
						By(tParts[0], WeierstrassChartOneMembers.At(fieldL, k, x, y, r)))
					cParts := d.Conjuncts(
						cForm,
						"p₁ lies in k[s]",
						"q₁ lies in k[s]",
						"c = p₁ + q₁ · u")
					rParts := d.Conjuncts(
						rForm,
						"p₂ lies in k[s]",
						"q₂ lies in k[s]",
						"r = p₂ + q₂ · u")
					coefficientsInK := d.Have(
						"a and b lie in k[s], as k does",
						"a ∈ «curveKs» ∧ b ∈ «curveKs»",
						BySets(WeierstrassCoefficientA.Read(datum), WeierstrassCoefficientB.Read(datum), kInKs))
					members := d.Have(
						"c, r, p₁, q₁, p₂, q₂, a and b lie in L",
						"c ∈ L.carrier ∧ "+
							"r ∈ L.carrier ∧ "+
							"p₁ ∈ L.carrier ∧ "+
							"q₁ ∈ L.carrier ∧ "+
							"p₂ ∈ L.carrier ∧ "+
							"q₂ ∈ L.carrier ∧ "+
							"a ∈ L.carrier ∧ "+
							"b ∈ L.carrier",
						BySets(
							oneParts[0],
							tParts[0],
							cParts[0],
							cParts[1],
							rParts[0],
							rParts[1],
							coefficientsInK,
							ksInChartOne,
							chartOneInL))
					relation := d.Have(
						"so (s · W − one) + (D · s²) · y = zero, u² read as s · (one + a · s² + b · s³)",
						"L.inv(x) * «W» + -L.one + «D» * «curveS2» * y = L.zero",
						ByArith(
							ringL,
							xm,
							ym,
							sm,
							members,
							oneForm,
							Scaled(s, cParts[2]),
							Scaled(u, rParts[2]),
							Scaled(q2, GroupPremises(datum, WeierstrassChartOneEquation.Read(L).At(k, x, y, a, b)))))
					cofactors := d.Have(
						"W and D · s² lie in k[s]",
						"«W» ∈ «curveKs» ∧ «D» * «curveS2» ∈ «curveKs»",
						By(
							cParts[0],
							cParts[1],
							rParts[0],
							rParts[1],
							sInKs,
							coefficientsInK,
							comm_ring.SubringOne.Read(ksSubring),
							comm_ring.SubringAdd.Read(ksSubring),
							comm_ring.SubringMul.Read(ksSubring)))
					laurent := d.Have(
						"so s · W − one and D · s² lie in k[x, 1/x]",
						"L.inv(x) * «W» + -L.one ∈ «curveLaurent» ∧ «D» * «curveS2» ∈ «curveLaurent»",
						By(
							sInKs,
							ksInLaurent,
							cofactors,
							comm_ring.SubringOne.Read(ksSubring),
							comm_ring.SubringNeg.Read(ksSubring),
							comm_ring.SubringAdd.Read(ksSubring),
							comm_ring.SubringMul.Read(ksSubring),
							set_basic.SubsetDef))
					sMultiple := d.Have(
						"one and y being independent over k[x, 1/x], s · W − one is zero",
						"L.inv(x) * «W» + -L.one = L.zero",
						By(
							datum,
							laurent,
							relation,
							WeierstrassLaurentCoefficients.Read(L).At(
								k, x, y, a, b, d.TermAs[A]("L.inv(x) * «W» + -L.one"), d.TermAs[A]("«D» * «curveS2»"))))
					oneMultiple := d.Have(
						"so one = s¹ · W",
						"L.one = monoid_pow(L.mul, L.one, L.inv(x), 1) * «W»",
						ByArith(ringL, xm, sm, members, sMultiple))
					d.Show(
						"a nonzero member of k[x] is no negative power of x times a member of k[1/x]",
						By(
							oneMultiple,
							cofactors,
							kSubfield,
							WeierstrassTranscendental.Read(datum),
							comm_ring.SubringOne.Read(kxSubring),
							field.OneNotZeroOn.Read(L),
							projective_line.LineNegativeSectionsVanish.Read(L).At(
								k, xm, d.TermAs[A]("L.one"), d.TermAs[A]("«W»"), d.TermAs[Nat]("1"))))
				}))

			split := arg.Have(
				"a polynomial P over k has P(s) = P(0) + w · s with w in "+
					"k[s]: s divides P − P(0) by the factor theorem at zero",
				Statement{
					Binders:    "∀P:num → A.",
					Hypotheses: []string{"polynomial_over(k, P)"},
					Conclusion: "∃w:A. w ∈ «curveKs» ∧ polynomial_eval(P, L.inv(x)) = P(0) + w * L.inv(x)",
				},
				Derive(func(d *Argument) {
					P := d.FixAs[Fun[Nat, A]]("P")
					over := d.Assume()
					constant := d.TermAs[A]("P(0)")
					constantPolynomial := d.TermAs[Fun[Nat, A]]("P(0) • basis_vector(0)")
					shifted := d.TermAs[Fun[Nat, A]]("P - P(0) • basis_vector(0)")
					linear := d.TermAs[Fun[Nat, A]]("«X»")
					overKs := d.Have(
						"P is a polynomial over k[s] as well",
						"polynomial_over(«curveKs», P)",
						By(kInKs, over, polynomial.PolynomialOverMono))
					constantIn := d.Have(
						"its constant coefficient lies in k, so in k[s]",
						"P(0) ∈ «curveKs»",
						By(over, kInKs, polynomial.PolynomialOverDef, set_basic.SubsetDef))
					constantOver := d.Have(
						"so the constant polynomial P(0) is a polynomial over k[s]",
						"polynomial_over(«curveKs», P(0) • basis_vector(0))",
						By(
							constantIn,
							polynomial.PolynomialRingDef,
							ring_homomorphism.MapIn.Read(polynomial.ConstantPolynomialHomomorphism.Read(ksRing)).AsFact().At(
								constant)))
					shiftedOver := d.Have(
						"and so is P less it",
						"polynomial_over(«curveKs», P - P(0) • basis_vector(0))",
						By(overKs, constantOver, comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ksRing))))
					root := d.Have(
						"P − P(0) vanishes at zero, where P takes its constant coefficient",
						"polynomial_eval(P - P(0) • basis_vector(0), L.zero) = L.zero",
						ByArith(
							ksRing,
							overKs,
							constantIn,
							constantOver,
							comm_ring.ZeroIn.Read(ksRing),
							polynomial_evaluation.EvalSub.Read(ksRing).AsFact().At(P, constantPolynomial, zero),
							polynomial_evaluation.EvalConstant.Read(ksRing).AsFact().At(constant, zero),
							polynomial_evaluation.EvalAtZero.Read(ksRing).At(P)))
					divides := d.Have(
						"so the variable X divides it",
						"polynomial_divides(restrict_ring(field_ring(L), «curveKs»), «X», P - P(0) • basis_vector(0))",
						By(
							root,
							shiftedOver,
							comm_ring.ZeroIn.Read(ksRing),
							polynomial_roots.FactorTheorem.Read(ksRing).AsFact().At(shifted, zero)))
					W, quotient := d.UnpackAs[Fun[Nat, A]](
						d.Unfolded(divides, polynomial_division.PolynomialDividesDef), "W")
					quotientParts := d.Conjuncts(
						quotient,
						"W is a polynomial over k[s]",
						"P − P(0) is X · W")
					factored := d.Have(
						"at s, P − P(0) takes the value of X times that of W",
						"polynomial_eval(P - P(0) • basis_vector(0), L.inv(x)) = "+
							"polynomial_eval(«X», L.inv(x)) * polynomial_eval(W, L.inv(x))",
						quotientParts[1].Rw(),
						By(
							sInKs,
							quotientParts[0],
							comm_ring.ZeroIn.Read(ksRing),
							polynomial_roots.LinearFactor.Read(ksRing).AsFact().At(zero),
							polynomial_evaluation.EvalMul.Read(ksRing).AsFact().At(linear, W, s)))
					value := d.Have(
						"so P(s) = P(0) + W(s) · s",
						"polynomial_eval(P, L.inv(x)) = P(0) + polynomial_eval(W, L.inv(x)) * L.inv(x)",
						ByArith(
							ksRing,
							factored,
							sInKs,
							constantIn,
							constantOver,
							overKs,
							quotientParts[0],
							comm_ring.ZeroIn.Read(ksRing),
							polynomial_evaluation.EvalSub.Read(ksRing).AsFact().At(P, constantPolynomial, s),
							polynomial_evaluation.EvalConstant.Read(ksRing).AsFact().At(constant, s),
							polynomial_roots.LinearFactor.Read(ksRing).AsFact().At(zero),
							polynomial_evaluation.EvalIn.Read(ksRing).AsFact().At(P, s),
							polynomial_evaluation.EvalIn.Read(ksRing).AsFact().At(W, s)))
					d.Take(d.TermAs[A]("polynomial_eval(W, L.inv(x))"))
					d.Show(
						"W(s) lies in k[s]",
						By(value, sInKs, quotientParts[0], polynomial_evaluation.EvalIn.Read(ksRing).AsFact().At(W, s)))
				}))

			congruence := arg.Have(
				"each member z = P(s) + Q(s) · u of chart 1 is "+
					"congruent to P(0) modulo I: z − P(0) = w · s + Q(s) · u",
				Statement{
					Binders:    "∀z:A.",
					Hypotheses: []string{"z ∈ «curveChart1»"},
					Conclusion: "∃P Q:num → A. " +
						"    polynomial_over(k, P) ∧ " +
						"    polynomial_over(k, Q) ∧ " +
						"    z = polynomial_eval(P, L.inv(x)) + polynomial_eval(Q, L.inv(x)) * «curveU» ∧ " +
						"    z + -P(0) ∈ «originIdeal»",
				},
				Derive(func(d *Argument) {
					z := d.FixAs[A]("z")
					zIn := d.Assume()
					P, Q, zForm := d.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
						GroupPremises(zIn, chartOnePolynomials.At(z)), "P", "Q")
					zParts := d.Conjuncts(
						zForm,
						"P is a polynomial over k",
						"so is Q",
						"z = P(s) + Q(s) · u")
					_, wForm := d.UnpackAs[A](GroupPremises(zParts[0], split.At(P)), "w")
					wParts := d.Conjuncts(
						wForm,
						"w lies in k[s]",
						"P(s) = P(0) + w · s")
					values := d.Have(
						"P(s), Q(s) and P(0) lie in k[s]",
						"polynomial_eval(P, L.inv(x)) ∈ «curveKs» ∧ "+
							"polynomial_eval(Q, L.inv(x)) ∈ «curveKs» ∧ "+
							"P(0) ∈ «curveKs»",
						By(
							zParts[0],
							zParts[1],
							kInKs,
							valuesInKs.At(P),
							valuesInKs.At(Q),
							polynomial.PolynomialOverDef,
							set_basic.SubsetDef))
					members := d.Have(
						"so they, w and z lie in chart 1 and in L",
						"w ∈ «curveChart1» ∧ "+
							"polynomial_eval(Q, L.inv(x)) ∈ «curveChart1» ∧ "+
							"z ∈ L.carrier ∧ "+
							"w ∈ L.carrier ∧ "+
							"polynomial_eval(P, L.inv(x)) ∈ L.carrier ∧ "+
							"polynomial_eval(Q, L.inv(x)) ∈ L.carrier ∧ "+
							"P(0) ∈ L.carrier",
						BySets(zIn, wParts[0], values, ksInChartOne, chartOneInL))
					difference := d.Have(
						"z − P(0) = w · s + Q(s) · u",
						"z + -P(0) = w * L.inv(x) + polynomial_eval(Q, L.inv(x)) * «curveU»",
						ByArith(ringL, ym, sm, members, zParts[2], wParts[1]))
					differenceIn := d.Have(
						"which lies in I, s and u lying in I and w and Q(s) in chart 1",
						"w * L.inv(x) + polynomial_eval(Q, L.inv(x)) * «curveU» ∈ «originIdeal»",
						By(idealI, sInI, uInI, members, ring_ideal.IdealAdd.Read(idealI), ring_ideal.IdealMul.Read(idealI)))
					d.Take(P)
					d.Take(Q)
					d.Show(
						"P and Q are the polynomials sought",
						By(zParts[0], zParts[1], zParts[2], difference, differenceIn))
				}))
			residues := arg.Have(
				"so each member of chart 1 differs by a member of I from its residue in k",
				"∀z:A. z ∈ «curveChart1» ⇒ ∃c:A. c ∈ k ∧ z + -c ∈ «originIdeal»",
				Derive(func(d *Argument) {
					z := d.FixAs[A]("z")
					zIn := d.Assume()
					_, _, zForm := d.Unpack2As[Fun[Nat, A], Fun[Nat, A]](GroupPremises(zIn, congruence.At(z)), "P", "Q")
					d.Take(d.TermAs[A]("P(0)"))
					d.Show(
						"P(0) lies in k, P being a polynomial over k",
						By(zForm, polynomial.PolynomialOverDef))
				}))

			// So I is the ideal of a k-rational point of chart 1, read on the overlap, and maximal.
			datumParts := arg.Conjuncts(
				arg.Have(
					"glued along the overlap the charts are a biaffine "+
						"datum: the overlap is a ring with both charts as subrings",
					"comm_ring_on(«curveOverlapRing») ∧ "+
						"subring(«curveOverlapRing», «curveChart0») ∧ "+
						"subring(«curveOverlapRing», «curveChart1»)",
					By(datum, WeierstrassBiaffine.Read(L).At(k, x, y, a, b), lattice_pair.BiaffineDef)),
				"the overlap is a ring",
				"chart 0 is a subring of it",
				"so is chart 1")
			overlap, chartZeroSubring, chartOneInOverlap := datumParts[0], datumParts[1], datumParts[2]
			overlapSubfield := arg.Have(
				"k is a field under the overlap's operations",
				"ring_subfield(«curveOverlapRing», L.inv, k)",
				By(kSubfield, field.SubfieldRingSubfield.Read(L).At(k, overlapSet)))
			rationalOnOverlap := arg.Have(
				"read on the overlap, I is the ideal of a k-rational point of chart 1",
				"rational_ideal(«curveOverlapRing», k, «curveChart1», «originIdeal»)",
				Unfold(quotient_ring.RationalIdealDef),
				Simp(Fwd(module_record.RestrictRingTwice)),
				By(idealI, proper, residues))
			maximal := arg.Have(
				"so I is maximal, its residues lying in the field k inside chart 1",
				"maximal_ideal(«chartOneRing», «originIdeal»)",
				By(
					overlap,
					overlapSubfield,
					chartOneInOverlap,
					kInChartOne,
					rationalOnOverlap,
					quotient_ring.FieldResiduesMaximal.At(overlapRing, k, inv, chartOne, ideal),
					module_record.RestrictRingTwice.At(fieldRing, overlapSet, chartOne)))

			// I is the set of the P(s) + Q(s) · u with P(0) = zero.
			V, vDef := arg.LetAs[Set[A]](
				"V",
				"{polynomial_eval(p, L.inv(x)) + polynomial_eval(q, L.inv(x)) * «curveU» | "+
					"    p:num → A, "+
					"    q:num → A | "+
					"    polynomial_over(k, p) ∧ polynomial_over(k, q) ∧ p(0) = L.zero}")
			vMember := arg.Have(
				"a member of V is P(s) + Q(s) · u with P(0) = zero",
				"∀z:A. "+
					"    z ∈ V ⇔ "+
					"    ∃p q:num → A. "+
					"        polynomial_over(k, p) ∧ "+
					"        polynomial_over(k, q) ∧ "+
					"        p(0) = L.zero ∧ "+
					"        z = polynomial_eval(p, L.inv(x)) + polynomial_eval(q, L.inv(x)) * «curveU»",
				BySets(vDef))
			idealInV := arg.Have(
				"I lies in V: a member z = P(s) + Q(s) · u of I has P(0) in I and in k, so P(0) = zero",
				"«originIdeal» ⊆ V",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(d *Argument) {
					z := d.FixAs[A]("z")
					zIn := d.Assume()
					zChart := d.Have(
						"z lies in chart 1, as I does",
						"z ∈ «curveChart1»",
						BySets(zIn, ring_ideal.IdealSubset.Read(idealI)))
					P, Q, zForm := d.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
						GroupPremises(zChart, congruence.At(z)), "P", "Q")
					zParts := d.Conjuncts(
						zForm,
						"P is a polynomial over k",
						"so is Q",
						"z = P(s) + Q(s) · u",
						"z − P(0) lies in I")
					constant := d.TermAs[A]("P(0)")
					constantIn := d.Conjuncts(
						d.Have(
							"P(0) lies in k, so in chart 1",
							"P(0) ∈ k ∧ P(0) ∈ «curveChart1»",
							By(zParts[0], kInChartOne, polynomial.PolynomialOverDef, set_basic.SubsetDef)),
						"P(0) lies in k",
						"P(0) lies in chart 1")
					recovered := d.Have(
						"I holds z − (z − P(0))",
						"z + -(z + -P(0)) ∈ «originIdeal»",
						By(
							idealI,
							zIn,
							zParts[3],
							ring_ideal.IdealSub.Read(ringOne).At(ideal, z, d.TermAs[A]("z + -P(0)"))))
					back := d.Have(
						"which is P(0)",
						"z + -(z + -P(0)) = P(0)",
						ByArith(ringOne, zChart, constantIn[1]))
					constantInI := d.Have(
						"so P(0) lies in I",
						"P(0) ∈ «originIdeal»",
						By(recovered, back))
					constantZero := d.Have(
						"a member of k in the proper ideal I is zero",
						"P(0) = L.zero",
						By(
							overlapSubfield,
							kInChartOne,
							idealI,
							proper,
							constantInI,
							constantIn[0],
							module_record.RestrictRingTwice.At(fieldRing, overlapSet, chartOne),
							quotient_ring.ProperIdealMeetsFieldAtZero.At(overlapRing, k, inv, chartOne, ideal, constant)))
					expansion := d.Have(
						"so P and Q exhibit z as a member of V",
						"∃p q:num → A. "+
							"    polynomial_over(k, p) ∧ "+
							"    polynomial_over(k, q) ∧ "+
							"    p(0) = L.zero ∧ "+
							"    z = polynomial_eval(p, L.inv(x)) + polynomial_eval(q, L.inv(x)) * «curveU»",
						Witness(P),
						Witness(Q),
						By(zParts[0], zParts[1], zParts[2], constantZero))
					d.Show(
						"z lies in V",
						By(expansion, vMember.At(z)))
				}))
			vInIdeal := arg.Have(
				"V lies in I: with P(0) = zero, P(s) + Q(s) · u is w · s + Q(s) · u",
				"V ⊆ «originIdeal»",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(d *Argument) {
					z := d.FixAs[A]("z")
					zIn := d.Assume()
					P, Q, zForm := d.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
						"z = P(s) + Q(s) · u with P(0) = zero",
						"∃P Q:num → A. "+
							"    polynomial_over(k, P) ∧ "+
							"    polynomial_over(k, Q) ∧ "+
							"    P(0) = L.zero ∧ "+
							"    z = polynomial_eval(P, L.inv(x)) + polynomial_eval(Q, L.inv(x)) * «curveU»",
						By(vMember.At(z), zIn))
					zParts := d.Conjuncts(
						zForm,
						"P is a polynomial over k",
						"so is Q",
						"P(0) = zero",
						"z = P(s) + Q(s) · u")
					_, wForm := d.UnpackAs[A](GroupPremises(zParts[0], split.At(P)), "w")
					wParts := d.Conjuncts(
						wForm,
						"w lies in k[s]",
						"P(s) = P(0) + w · s")
					coefficients := d.Have(
						"w and Q(s) lie in k[s], so in chart 1",
						"w ∈ «curveChart1» ∧ polynomial_eval(Q, L.inv(x)) ∈ «curveChart1»",
						By(wParts[0], zParts[1], ksInChartOne, valuesInKs.At(Q), set_basic.SubsetDef))
					d.Show(
						"z = zero + w · s + Q(s) · u lies in I",
						zParts[3].Rw(),
						wParts[1].Rw(),
						zParts[2].Rw(),
						By(
							idealI,
							sInI,
							uInI,
							coefficients,
							ring_ideal.IdealZero.Read(idealI),
							ring_ideal.IdealAdd.Read(idealI),
							ring_ideal.IdealMul.Read(idealI)))
				}))
			explicit := arg.Have(
				"so I is V",
				"«originIdeal» = V",
				By(idealInV, vInIdeal, set_order.SubsetAntisym.At(ideal, V)))

			// The origin is a rational point: chart 0 and I generate the whole overlap.
			chartZero := arg.TermAs[Set[A]]("«curveChart0»")
			notChartOne := arg.Have(
				"I is not chart 1, one lying in chart 1 and not in I",
				"«originIdeal» ≠ «curveChart1»",
				By(proper, comm_ring.SubringOne.Read(chartOneSubring)))
			chartZeroIdeal := arg.Have(
				"chart 0 generates an ideal of the overlap",
				"ring_ideal(«curveOverlapRing», ideal_span(«curveOverlapRing», «curveChart0»))",
				By(
					comm_ring.SubringSubset.Read(chartZeroSubring),
					ring_ideal.SpanIdeal.Read(overlap).At(chartZero)))
			chartZeroOne := arg.Have(
				"holding one, which chart 0 holds",
				"L.one ∈ ideal_span(«curveOverlapRing», «curveChart0»)",
				BySets(
					comm_ring.SubringOne.Read(chartZeroSubring),
					ring_ideal.SpanContains.At(overlapRing, chartZero)))
			chartZeroWhole := arg.Have(
				"so chart 0 generates the whole overlap",
				"ideal_span(«curveOverlapRing», «curveChart0») = «curveOverlap»",
				By(
					chartZeroIdeal,
					chartZeroOne,
					ring_ideal.IdealOneIff.Read(overlap).At(
						arg.TermAs[Set[A]]("ideal_span(«curveOverlapRing», «curveChart0»)"))))
			idealWhole := arg.Have(
				"read from chart 1 the curve has coordinate s, which I "+
					"holds inside chart 1, so I generates the whole overlap",
				"ideal_span(«curveOverlapRing», «originIdeal») = «curveOverlap»",
				By(
					datum,
					WeierstrassIsCurve.Read(L).At(k, x, y, a, b),
					algebraic_curve.CurveSwap.Read(L).At(k, chartZero, chartOne, overlapSet, x),
					sInI,
					ring_ideal.IdealSubset.Read(idealI),
					algebraic_curve.CoordinateSpansOverlap.Read(L).At(k, chartOne, chartZero, overlapSet, s, ideal)))
			point := arg.Have(
				"so the pair of chart 0 and I is a rational point, lying off chart 0",
				"biaffine_rational_point(«curveOverlapRing», "+
					"    k, "+
					"    «curveChart0», "+
					"    «curveChart1», "+
					"    («curveChart0», «originIdeal»))",
				Unfold(biaffine_rational_point.BiaffineRationalPointDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(rationalOnOverlap, notChartOne, chartZeroWhole, idealWhole))
			arg.Show(
				"the origin is the pair of chart 0 and I",
				Simp(Fwd(WeierstrassOriginDef), Fwd(pairs.Snd)),
				By(point, maximal, explicit))
		}),
})}

// RationalPointsOfWeierstrass — the rational points of the curve are the
// origin and the points of the solutions in k of the affine equation,
// each solution giving its own point.
var RationalPointsOfWeierstrass = rationalPointsOfWeierstrassThm{family.Add(registry.ProofEntry{
	Name: "RationalPointsOfWeierstrass",
	Key:  "prop_6e24df6b21190d7e",
	Reading: "The coordinates of an affine point are read back from its ideal: x₀ and y₀ " +
		"are the residues of x and y. A point off chart 0 is the origin: it generates the " +
		"overlap, so a power of s lies in its chart-1 ideal, which is prime, so s does, and " +
		"then u² = s · (1 + as² + bs³) puts u in it. No characteristic and no discriminant " +
		"hypothesis: the singular point of a nodal or cuspidal cubic is a rational point too.",
	Deps: []registry.EntryLike{
		AffinePointMaximal,
		OriginMaximal,
		weierstrassPointDef,
		WeierstrassOriginDef,
		WeierstrassChartOneEquation,
		biaffine_rational_point.BiaffineRationalPointDef,
		biaffine_rational_point.RationalPointMaximal,
		biaffine_rational_point.RationalPointOverlap,
		ring_ideal.MaximalIsPrime,
		ring_ideal.UnitNotInProperIdeal,
		ring_away.RingAwayDef,
		field.InvIn,
		WeierstrassIsCurve,
		algebraic_curve.CurveOverLineDef,
		algebraic_curve.CurveLatticeData,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∀P:prod(set(A), set(A)). " +
			"    biaffine_rational_point(restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        k, " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        P) ⇔ " +
			"    P = weierstrass_origin(L, k, x, y) ∨ " +
			"    (∃x₀ y₀:A. " +
			"        x₀ ∈ k ∧ " +
			"        y₀ ∈ k ∧ " +
			"        y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b ∧ " +
			"        P = weierstrass_point(L, k, x, y, x₀, y₀))) ∧ " +
			"(∀x₀ y₀ x₁ y₁:A. " +
			"    x₀ ∈ k ∧ " +
			"    y₀ ∈ k ∧ " +
			"    y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b ∧ " +
			"    x₁ ∈ k ∧ " +
			"    y₁ ∈ k ∧ " +
			"    y₁ * y₁ = x₁ * (x₁ * x₁) + a * x₁ + b ∧ " +
			"    weierstrass_point(L, k, x, y, x₀, y₀) = weierstrass_point(L, k, x, y, x₁, y₁) ⇒ " +
			"    x₀ = x₁ ∧ y₀ = y₁) ∧ " +
			"(∀x₀ y₀:A. " +
			"    x₀ ∈ k ∧ y₀ ∈ k ∧ y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b ⇒ " +
			"    ¬(weierstrass_point(L, k, x, y, x₀, y₀) = weierstrass_origin(L, k, x, y)))",
	},
		"⇐: AffinePointMaximal and OriginMaximal. ⇒ on chart 0: the residues x₀, y₀ ∈ k of x "+
			"and y (BiaffineRationalPointDef) put x − x₀ and y − y₀ in the chart-0 ideal, and y₀² "+
			"− (x₀³ + ax₀ + b), congruent to y² − (x³ + ax + b) = zero and a member of k, is zero, "+
			"a nonzero member of k being a unit (InvIn, UnitNotInProperIdeal); the ideal of x − x₀ "+
			"and y − y₀ is maximal (AffinePointMaximal), so it is the point's; chart 1's ideal is "+
			"the meet of chart 1 with the generated ideal (RationalPointOverlap), or chart 1 when "+
			"the point lies off it, which is that meet too. Off chart 0: as in the reading "+
			"(RationalPointMaximal, MaximalIsPrime, RingAwayDef), the origin's ideal being maximal "+
			"(OriginMaximal). Uniqueness: x₁ − x₀ and y₁ − y₀ lie in the ideal and in k, so are "+
			"zero; the origin's chart-0 ideal is the chart, an affine point's is proper"),
})}

// NegPointValues — the conjugation sends the point (x₀, y₀) to
// (x₀, −y₀) and the origin to itself.
var NegPointValues = negPointValuesThm{family.Add(registry.ProofEntry{
	Name: "NegPointValues",
	Key:  "prop_f1d47e583dabcd67",
	Reading: "On chart 0 the conjugation carries the kernel of the evaluation " +
		"at (x₀, y₀) to the kernel at (x₀, −y₀), p(x₀) + q(x₀)·y₀ = zero being " +
		"p(x₀) − (−q(x₀))·y₀ = zero; −y₀ solves the equation with y₀. On chart 1 " +
		"the origin's ideal, the P(s) + Q(s)·u with P(0) = zero, is kept by Q ↦ −Q.",
	Deps: []registry.EntryLike{
		WeierstrassNegPointDef,
		AffinePointMaximal,
		AffinePointCharts,
		OriginMaximal,
		WeierstrassBasisZero,
		WeierstrassBasisOne,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
		},
		Conclusion: "weierstrass_neg_point(L, k, x, y, weierstrass_point(L, k, x, y, x₀, y₀)) = " +
			"weierstrass_point(L, k, x, y, x₀, -y₀) ∧ " +
			"weierstrass_neg_point(L, k, x, y, weierstrass_origin(L, k, x, y)) = " +
			"weierstrass_origin(L, k, x, y)",
	},
		"chart 0: by the kernel description of AffinePointMaximal at (x₀, y₀) and at (x₀, −y₀), "+
			"each p + q·y written once (WeierstrassBasisZero); chart 1: for x₀ = zero both ideals "+
			"are chart 1, which the conjugation keeps; for x₀ ≠ zero the same with the kernels of "+
			"chart 1's evaluations at (1/x₀, ±y₀/x₀²) (AffinePointCharts, WeierstrassBasisOne). The "+
			"origin: the conjugation keeps chart 0 and the kernel description of OriginMaximal"),
})}

// ---------------------------------------------------------------------------
// Regularity
// ---------------------------------------------------------------------------

// FactoredRelation — the relation read at a point (x₀, y₀) of the curve:
// (y − y₀)(y + y₀) = (x − x₀)(x² + xx₀ + x₀² + a), and on chart 1, for
// x₀ ≠ 0, (u − u₀)(u + u₀) = (s − s₀)(1 + a(s² + ss₀ + s₀²) + b(s³ +
// s²s₀ + ss₀² + s₀³)).
var FactoredRelation = factoredRelationThm{family.Add(registry.ProofEntry{
	Name: "FactoredRelation",
	Key:  "prop_7ce11a348cffbfd1",
	Reading: "The relation in the form v · g = u · h that JacobianRelationInvertible reads, " +
		"u and v the generators of the point's ideal in the chart: at the point g is 2y₀ and h " +
		"is 3x₀² + a on chart 0, and on chart 1 g is 2u₀ and h is 1 + 3as₀² + 4bs₀³, which is " +
		"−s₀² · (3x₀² + a) where y₀ = zero. Only the two equations and the field's laws are used.",
	Deps: []registry.EntryLike{
		WeierstrassDef,
		WeierstrassChartOneEquation,
		field.MulRightInverseOn,
		field.InvIn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
		},
		Conclusion: "(y - y₀) * (y + y₀) = (x - x₀) * (x * x + x * x₀ + x₀ * x₀ + a) ∧ " +
			"(x₀ ≠ L.zero ⇒ " +
			"    (y * (L.inv(x) * L.inv(x)) - y₀ * (L.inv(x₀) * L.inv(x₀))) * " +
			"    (y * (L.inv(x) * L.inv(x)) + y₀ * (L.inv(x₀) * L.inv(x₀))) = " +
			"    (L.inv(x) - L.inv(x₀)) * " +
			"    (L.one + " +
			"        a * (L.inv(x) * L.inv(x) + L.inv(x) * L.inv(x₀) + L.inv(x₀) * L.inv(x₀)) + " +
			"        b * " +
			"        (L.inv(x) * (L.inv(x) * L.inv(x)) + " +
			"            L.inv(x) * (L.inv(x) * L.inv(x₀)) + " +
			"            L.inv(x) * (L.inv(x₀) * L.inv(x₀)) + " +
			"            L.inv(x₀) * (L.inv(x₀) * L.inv(x₀)))))",
	},
		"chart 0: (y − y₀)(y + y₀) = y² − y₀² = (x³ + ax + b) − (x₀³ + ax₀ + b), "+
			"which is (x − x₀)(x² + xx₀ + x₀² + a) by the field's laws; chart 1: u² = s "+
			"+ as³ + bs⁴ (WeierstrassChartOneEquation) and u₀² = s₀ + as₀³ + bs₀⁴, the "+
			"point's equation times s₀⁴ (x₀ · inv(x₀) = one, MulRightInverseOn), so (u − "+
			"u₀)(u + u₀) = (s − s₀) + a(s³ − s₀³) + b(s⁴ − s₀⁴), which factors as stated"),
})}

// AffinePointRegularOrdinary — where 2y₀ ≠ 0 the affine point (x₀, y₀)
// is a regular point: its ideal is invertible on each chart.
var AffinePointRegularOrdinary = affinePointRegularOrdinaryThm{family.Add(registry.ProofEntry{
	Name: "AffinePointRegularOrdinary",
	Key:  "prop_97002d6b729200fb",
	Reading: "2y₀ ≠ 0 is the nonvanishing of ∂F/∂y at the point; the " +
		"discriminant is not asked, a solution with 2y₀ ≠ 0 being a nonsingular " +
		"point of any Weierstrass cubic. 2 ≠ 0 is load-bearing: in characteristic 2, " +
		"y² = x³ + 1 is singular at (0, 1), both partial derivatives vanishing there.",
	Deps: []registry.EntryLike{
		AffinePointMaximal,
		AffinePointCharts,
		FactoredRelation,
		weierstrassPointDef,
		WeierstrassBasisZero,
		WeierstrassBasisOne,
		invertible_fractional_ideal.JacobianRelationInvertible,
		fractional_ideal.InvertibleScale,
		fractional_ideal.InvertibleFractionalDef,
		lattice_pair_twist.BiaffineRegularPointDef,
		invertible_lattice_pair.InvertibleLatticePairDef,
		lattice_pair.LatticePairDef,
		biaffine_rational_point.BiaffineRationalPointDef,
		field.SubfieldInv,
		algebraic_element.PolynomialImageRing,
		algebraic_element.EvalInjectiveTranscendental,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
			"L.one + L.one ≠ L.zero",
			"y₀ ≠ L.zero",
		},
		Conclusion: "biaffine_regular_point(field_ring(L), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
			"    weierstrass_point(L, k, x, y, x₀, y₀))",
	},
		"the point is rational (AffinePointMaximal); unfold invertible_lattice_pair. Chart 0: "+
			"JacobianRelationInvertible at the subring chart 0 (WeierstrassBasisZero), u = x − x₀, v = y "+
			"− y₀ (weierstrassPointDef), g = y + y₀, h = x² + xx₀ + x₀² + a (FactoredRelation), the "+
			"residue clause AffinePointMaximal's: x − x₀ ≠ zero as x ∉ k, and g ∉ m as g − 2y₀ ∈ m with "+
			"2y₀ a nonzero member of k. Chart 1: for x₀ = zero the ideal is chart 1, invertible "+
			"(InvertibleScale at a = one); otherwise the same at s − s₀, u − u₀ (AffinePointCharts), g = "+
			"u + u₀ ≡ 2u₀ ≠ zero. The pair is a lattice pair over the overlap: both chart ideals generate "+
			"one ideal of the overlap (BiaffineRationalPointDef), their span in the field over it"),
})}

// AffinePointRegularTwoTorsion — where y₀ = 0 and 4a³ + 27b² ≠ 0 the
// affine point (x₀, 0) is a regular point.
var AffinePointRegularTwoTorsion = affinePointRegularTwoTorsionThm{family.Add(registry.ProofEntry{
	Name: "AffinePointRegularTwoTorsion",
	Key:  "prop_8a6da4c674de5df8",
	Reading: "With y₀ = zero, x₀ is a root of g = x³ + ax + b, and 4a³ + 27b² ≠ 0 makes it a " +
		"simple root: (27b − 18ax)·g + (6ax² − 9bx + 4a²)·g′ = 4a³ + 27b², so 3x₀² + a ≠ zero, the " +
		"nonvanishing of ∂F/∂x. The roles of x and y are swapped against AffinePointRegularOrdinary, " +
		"and no characteristic is excluded. 4a³ + 27b² ≠ 0 is load-bearing: on y² = x³ the point (0, " +
		"0) is the cusp. 2 ≠ 0 is not needed: the cofactor identity holds over ℤ, so in " +
		"characteristic 2, where 4a³ + 27b² is b², it still forces 3x₀² + a ≠ zero.",
	Deps: []registry.EntryLike{
		AffinePointMaximal,
		AffinePointCharts,
		FactoredRelation,
		weierstrassPointDef,
		WeierstrassBasisZero,
		WeierstrassBasisOne,
		WeierstrassPartialsUnit,
		invertible_fractional_ideal.JacobianRelationInvertible,
		fractional_ideal.InvertibleScale,
		fractional_ideal.InvertibleFractionalDef,
		lattice_pair_twist.BiaffineRegularPointDef,
		invertible_lattice_pair.InvertibleLatticePairDef,
		lattice_pair.LatticePairDef,
		biaffine_rational_point.BiaffineRationalPointDef,
		algebraic_element.PolynomialImageRing,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
			"y₀ = L.zero",
			"monoid_pow(L.add, L.zero, L.one, 4) * (a * (a * a)) + " +
				"monoid_pow(L.add, L.zero, L.one, 27) * (b * b) ≠ " +
				"L.zero",
		},
		Conclusion: "biaffine_regular_point(field_ring(L), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
			"    weierstrass_point(L, k, x, y, x₀, y₀))",
	},
		"the point is rational (AffinePointMaximal). Chart 0: JacobianRelationInvertible's second "+
			"case at u = x − x₀, v = y − y₀ = y, g = y + y₀, h = x² + xx₀ + x₀² + a "+
			"(FactoredRelation): v ≠ zero and h ≡ 3x₀² + a ≠ zero modulo m, by the identity of the "+
			"reading (the cofactors of WeierstrassPartialsUnit). Chart 1: for x₀ = zero the chart "+
			"(InvertibleScale at a = one); otherwise the second case at s − s₀ and u − u₀ = u "+
			"(AffinePointCharts), h = 1 + a(s² + ss₀ + s₀²) + b(s³ + s²s₀ + ss₀² + s₀³) ≡ 1 + 3as₀² + "+
			"4bs₀³ = −s₀² · (3x₀² + a) ≠ zero. The lattice-pair clause as in AffinePointRegularOrdinary"),
})}

// OriginRegular — the origin is a regular point, whatever a and b are.
var OriginRegular = originRegularThm{family.Add(registry.ProofEntry{
	Name: "OriginRegular",
	Key:  "prop_25eba3d7fa5ebc7f",
	Reading: "No characteristic and no discriminant hypothesis: the point at " +
		"infinity of a Weierstrass cubic is always nonsingular, its relation u² = s · (1 " +
		"+ as² + bs³) having the linear term s. In the form v · g = u · h the generators " +
		"are s and u, g = u and h = 1 + as² + bs³, whose class at the origin is one.",
	Deps: []registry.EntryLike{
		OriginMaximal,
		WeierstrassOriginDef,
		WeierstrassChartOneEquation,
		WeierstrassBasisZero,
		WeierstrassBasisOne,
		invertible_fractional_ideal.JacobianRelationInvertible,
		fractional_ideal.InvertibleScale,
		lattice_pair_twist.BiaffineRegularPointDef,
		invertible_lattice_pair.InvertibleLatticePairDef,
		lattice_pair.LatticePairDef,
		algebraic_element.PolynomialImageRing,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "biaffine_regular_point(field_ring(L), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
			"    weierstrass_origin(L, k, x, y))",
	},
		"the origin is rational (OriginMaximal); unfold invertible_lattice_pair: chart 0's ideal "+
			"is chart 0, invertible (InvertibleScale at a = one); chart 1: "+
			"JacobianRelationInvertible's second case at the subring chart 1 (WeierstrassBasisOne), "+
			"u = s, v = u, g = u, h = 1 + as² + bs³ (WeierstrassChartOneEquation): v ≠ zero as x and "+
			"y are nonzero, and h ∉ m as h − one ∈ m and one ∉ m, the residue clause "+
			"OriginMaximal's. Both ideals generate the overlap, so the pair is a lattice pair over it"),
})}

// AllRationalPointsRegular — when 2 ≠ 0 and 4a³ + 27b² ≠ 0 every rational
// point of the curve is regular.
var AllRationalPointsRegular = allRationalPointsRegularThm{family.Add(registry.ProofEntry{
	Name: "AllRationalPointsRegular",
	Key:  "prop_84acffdeac7d9005",
	Reading: "The curve is smooth at its rational points. Both clauses the smooth " +
		"datum adds, 2 ≠ 0 and 4a³ + 27b² ≠ 0, are load-bearing: in characteristic 2, y² " +
		"= x³ + 1 is singular at (0, 1), and y² = x³ is singular at (0, 0). Only rational " +
		"points are read: a closed point of higher degree is no biaffine_rational_point.",
	Deps: []registry.EntryLike{
		RationalPointsOfWeierstrass,
		OriginRegular,
		AffinePointRegularOrdinary,
		AffinePointRegularTwoTorsion,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"biaffine_rational_point(restrict_ring(field_ring(L), " +
				"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
				"    k, " +
				"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
				"    weierstrass_chart_one(L, k, x, y), " +
				"    P)",
		},
		Conclusion: "biaffine_regular_point(field_ring(L), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
			"    P)",
	},
		"RationalPointsOfWeierstrass: P is the origin (OriginRegular) or the point of a solution "+
			"(x₀, y₀); y₀ ≠ zero gives AffinePointRegularOrdinary, y₀ = zero AffinePointRegularTwoTorsion"),
})}
