// lines.go — lines on the curve inside its function field and the ideals
// they cut. The line y = μx + ν over k meets the curve where the cubic
// x³ + ax + b − (μx + ν)² vanishes; when that cubic splits over k as
// (x − x₁)(x − x₂)(x − x₃), the line function y − (μx + ν) generates on
// chart 0 the product of the ideals of the points (xᵢ, μxᵢ + ν), a
// repeated root giving a repeated factor, and its chart-one form
// u − (μs + νs²) generates on chart 1 that product times the ideal of
// the origin. The vertical line x = x₀ cuts (x₀, y₀) and (x₀, −y₀) the
// same way, and s = 1/x generates the square of the origin's ideal. As
// lattice pairs, the line function times the structure pair is
// P₁ · P₂ · P₃ · O⁻³ and x − x₀ times it is P · (−P) · O⁻², O the
// origin's ideal pair: the divisors P₁ + P₂ + P₃ − 3O and P + (−P) − 2O.

package elliptic_curve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// weierstrassLineDef — `weierstrass_line(x, y, μ, ν)`: the line function
// y − (μx + ν), zero where the curve meets the line y = μx + ν.
var weierstrassLineDef = weierstrassLineDefThm{family.Define(registry.DefEntry{
	Name:     "weierstrassLineDef",
	Key:      "prop_7754b87ea0b57ad2",
	Const:    "weierstrass_line",
	Type:     "(A → A → A) → (A → A → A) → (A → A → A) → A → A → A → A → A",
	Implicit: []string{"add", "mul", "sub"},
	Equations: []string{
		"∀add:(A → A → A). ∀mul:(A → A → A). ∀sub:(A → A → A). ∀x y μ ν:A. " +
			"    weierstrass_line(add, mul, sub, x, y, μ, ν) = sub(y, add(mul(μ, x), ν))",
	},
	Reading: "A member of chart 0 once μ and ν lie in k. On the curve it vanishes at " +
		"the points (t, μt + ν) with t a root of x³ + ax + b − (μx + ν)², which it divides: " +
		"that cubic is y² − (μx + ν)², the line function times y + μx + ν. It has a pole of " +
		"order three at the origin, which chart 0 does not see (LineLatticeIdentity).",
})}

// weierstrassChartOneLineDef — `weierstrass_chart_one_line(x, y, μ,
// ν)`: the line read in the coordinates of chart 1, u − (μs + νs²) with
// s = 1/x and u = y/x², the line function times s².
var weierstrassChartOneLineDef = weierstrassChartOneLineDefThm{family.Define(registry.DefEntry{
	Name:     "weierstrassChartOneLineDef",
	Key:      "prop_69e80db82ce58a6e",
	Const:    "weierstrass_chart_one_line",
	Type:     "(A → A → A) → (A → A → A) → (A → A → A) → (A → A) → A → A → A → A → A",
	Implicit: []string{"add", "mul", "sub", "inv"},
	Equations: []string{
		"∀add:(A → A → A). ∀mul:(A → A → A). ∀sub:(A → A → A). ∀inv:(A → A). ∀x y μ ν:A. " +
			"    weierstrass_chart_one_line(add, mul, sub, inv, x, y, μ, ν) = " +
			"    sub(mul(y, mul(inv(x), inv(x))), add(mul(μ, inv(x)), mul(ν, mul(inv(x), inv(x)))))",
	},
	Reading: "A member of chart 1 once μ and ν lie in k, of the form p(s) + q(s)·u with p = " +
		"−(μs + νs²) and q = one. Where x · inv(x) = one it is inv(x)² times the line function. " +
		"It vanishes to order one at the origin — the line's pole of order three against the zero " +
		"of order four of s² (UniformizerAtOrigin) — and at the points of the line on chart 1.",
})}

// ---------------------------------------------------------------------------
// A line and its cubic
// ---------------------------------------------------------------------------

// LineCubicFactors — two roots in k of the cubic of a line, a double one
// where the line is tangent, split it: x³ + ax + b − (μx + ν)² =
// (x − x₁)(x − x₂)(x − x₃) with x₃ = μ² − x₁ − x₂.
var LineCubicFactors = lineCubicFactorsThm{family.Add(registry.ProofEntry{
	Name: "LineCubicFactors",
	Key:  "prop_d4a7ea3f1879095",
	Reading: "The cubic is monic with x²-coefficient −μ², so its three roots sum to μ² " +
		"and the third is read off the first two: the chord and tangent construction. The " +
		"tangency clause is load-bearing at x₁ = x₂: a single root x₁ leaves the quotient " +
		"x² + x₁x + x₁² + a − μ²(x + x₁) − 2μν free to have no root in k. Only the field's " +
		"laws enter, no transcendence, characteristic or discriminant: in characteristic 2 " +
		"the clause reads 3x₁² + a = zero. The conclusion is the polynomial identity read " +
		"at x, and a flex, all three roots one, needs nothing beyond the tangency clause.",
	Deps: []registry.EntryLike{WeierstrassDef, field.SubfieldDef, field.MulEqZeroOn},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b μ ν x₁ x₂:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"μ ∈ k",
			"ν ∈ k",
			"x₁ ∈ k",
			"x₂ ∈ k",
			"(μ * x₁ + ν) * (μ * x₁ + ν) = x₁ * (x₁ * x₁) + a * x₁ + b",
			"(μ * x₂ + ν) * (μ * x₂ + ν) = x₂ * (x₂ * x₂) + a * x₂ + b",
			"x₁ = x₂ ⇒ (L.one + L.one) * (μ * (μ * x₁ + ν)) = (L.one + L.one + L.one) * (x₁ * x₁) + a",
		},
		Conclusion: "x * (x * x) + a * x + b - (μ * x + ν) * (μ * x + ν) = " +
			"(x - x₁) * ((x - x₂) * (x - (μ * μ - x₁ - x₂)))",
	},
		"write c(t) = t³ + at + b − (μt + ν)²; c(t) − c(x₁) = (t − x₁)·q(t) with q(t) = t² + x₁t + x₁² "+
			"+ a − μ²(t + x₁) − 2μν, so c(x) = (x − x₁)·q(x) as c(x₁) = zero. q(x₂) = zero: for x₁ ≠ x₂ "+
			"from (x₂ − x₁)·q(x₂) = c(x₂) = zero (MulEqZeroOn), for x₁ = x₂ because q(x₁) = 3x₁² + a − "+
			"2μ(μx₁ + ν) is the tangency clause; then q(t) − q(x₂) = (t − x₂)(t + x₁ + x₂ − μ²). Every step "+
			"is the field's laws at members of L, k lying in L (SubfieldDef) and x in L (WeierstrassDef)"),
})}

// PointIdealOnLine — each root of the split cubic of a line gives a
// point of the curve on the line: the line function lies in its chart-0
// ideal and the chart-one form in its chart-1 ideal.
var PointIdealOnLine = pointIdealOnLineThm{family.Add(registry.ProofEntry{
	Name: "PointIdealOnLine",
	Key:  "prop_a9ad34dac34585c9",
	Reading: "Transcendence of x is load-bearing for the first conjunct: the factorization in the " +
		"field is one of polynomials over k because x is a root of none, and only as such does it " +
		"hold at the roots. The memberships hold for any point (t, μt + ν): y − (μx + ν) = (y − (μt + " +
		"ν)) − μ·(x − t), and the chart-one form is inv(x)² times it, inv(x)² lying in the overlap, " +
		"whether or not the point lies on chart 1. No characteristic and no discriminant hypothesis.",
	Deps: []registry.EntryLike{
		weierstrassLineDef,
		weierstrassChartOneLineDef,
		WeierstrassDef,
		weierstrassPointDef,
		WeierstrassChartOneDef,
		algebraic_element.EvalInjectiveTranscendental,
		algebraic_element.PolynomialImageDef,
		polynomial_evaluation.EvalHomomorphism,
		ring_ideal.IdealSpanDef,
		ring_ideal.SpanInsert,
		ring_away.RingAwayDef,
		field.MulRightInverseOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b μ ν x₁ x₂ x₃ t:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"μ ∈ k",
			"ν ∈ k",
			"x₁ ∈ k",
			"x₂ ∈ k",
			"x₃ ∈ k",
			"x * (x * x) + a * x + b - (μ * x + ν) * (μ * x + ν) = (x - x₁) * ((x - x₂) * (x - x₃))",
			"t = x₁ ∨ t = x₂ ∨ t = x₃",
		},
		Conclusion: "t ∈ k ∧ " +
			"μ * t + ν ∈ k ∧ " +
			"(μ * t + ν) * (μ * t + ν) = t * (t * t) + a * t + b ∧ " +
			"weierstrass_line(x, y, μ, ν) ∈ fst(weierstrass_point(L, k, x, y, t, μ * t + ν)) ∧ " +
			"weierstrass_chart_one_line(x, y, μ, ν) ∈ snd(weierstrass_point(L, k, x, y, t, μ * t + ν))",
	},
		"c(t) − (t − x₁)(t − x₂)(t − x₃), for c(t) = t³ + at + b − (μt + ν)², is a polynomial over k "+
			"vanishing at x, so it is zero (EvalInjectiveTranscendental, EvalHomomorphism) and its value at "+
			"a root t reads (μt + ν)² = t³ + at + b. The line function is (y − (μt + ν)) − μ·(x − t), in "+
			"the chart-0 ideal (weierstrassPointDef, SpanInsert, μ ∈ k ⊆ chart 0). The chart-one form lies "+
			"in chart 1 (WeierstrassChartOneDef at p = −(μs + νs²), q = one, PolynomialImageDef) and is "+
			"inv(x)² times the line function, inv(x) lying in the overlap (RingAwayDef, MulRightInverseOn), "+
			"so it lies in the meet of chart 1 with the ideal the chart-0 ideal generates there"),
})}

// ---------------------------------------------------------------------------
// The ideals a line cuts
// ---------------------------------------------------------------------------

// LineIdealChartZero — on chart 0 the line function generates the
// product of the ideals of the three points where the line meets the
// curve: ℓ·A₀ = m_{P₁} · m_{P₂} · m_{P₃}.
var LineIdealChartZero = lineIdealChartZeroThm{family.Add(registry.ProofEntry{
	Name: "LineIdealChartZero",
	Key:  "prop_750bf5a6f9c48ee6",
	Reading: "A repeated root is a repeated factor: a tangent line at P cuts m_P² · m_{P₃}, a flex " +
		"m_P³. The smooth datum enters only through the regularity of the three points " +
		"(AllRationalPointsRegular), and is load-bearing: on the cusp y² = x³ the line y = zero has the " +
		"triple root zero, and y·A₀ is not m³ for m the ideal of x and y — along x = t², y = t³ the " +
		"function y vanishes to order three and m³ to order six. In characteristic 2, y² = x³ + 1 has " +
		"the cusp (0, 1), where (y − 1)² = x³ and the line y = 1 fails the same way. Smoothness is what " +
		"matches the multiplicity of a root to the order of ℓ at its point: where yᵢ = zero it gives " +
		"3xᵢ² + a ≠ zero, and elsewhere ℓ's cofactor y + μx + ν is 2yᵢ ≠ zero at the point, a unit there.",
	Deps: []registry.EntryLike{
		weierstrassLineDef,
		PointIdealOnLine,
		weierstrassPointDef,
		WeierstrassBasisZero,
		AffinePointMaximal,
		AllRationalPointsRegular,
		polynomial_division.DivisionExists,
		polynomial.PolynomialsBelowDim,
		biaffine_rational_point.RationalPointColengths,
		lattice_pair_twist.BiaffineRegularPointDef,
		fractional_ideal.FractionalMulDef,
		fractional_ideal.InvertibleProduct,
		ideal_colength.InvertibleQuotientDim,
		module_dimension.QuotientChainDim,
		module_dimension.DimZero,
		WeierstrassIsCurve,
		algebraic_curve.CurveOverLineDef,
		algebraic_curve.CurveLatticeData,
		module_record.RestrictRingDef,
		module_record.RestrictModuleDef,
		algebraic_element.PolynomialImageRing,
		ring_ideal.CarrierIdeal,
		fractional_ideal.FractionalMulOne,
		field.SubfieldFieldOn,
		fractional_ideal.FieldModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b μ ν x₁ x₂ x₃:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"μ ∈ k",
			"ν ∈ k",
			"x₁ ∈ k",
			"x₂ ∈ k",
			"x₃ ∈ k",
			"x * (x * x) + a * x + b - (μ * x + ν) * (μ * x + ν) = (x - x₁) * ((x - x₂) * (x - x₃))",
		},
		Conclusion: "image(L.mul(weierstrass_line(x, y, μ, ν)), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y)) = " +
			"fractional_mul(field_ring(L), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    fst(weierstrass_point(L, k, x, y, x₁, μ * x₁ + ν)), " +
			"    fractional_mul(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        fst(weierstrass_point(L, k, x, y, x₂, μ * x₂ + ν)), " +
			"        fst(weierstrass_point(L, k, x, y, x₃, μ * x₃ + ν))))",
	},
		"⊇: each point's ideal is that of x − xᵢ and ℓ, as y − (μxᵢ + ν) = ℓ + μ(x − xᵢ) "+
			"(PointIdealOnLine), so the product is spanned by multiples of ℓ and ∏(x − xᵢ), which is x³ "+
			"+ ax + b − (μx + ν)² = y² − (μx + ν)² = ℓ · (y + μx + ν). Colengths over k: chart 0 modulo "+
			"ℓ is k[x] modulo the cubic, of dimension three — on the basis 1, y (WeierstrassBasisZero), "+
			"where p + q·y ≡ p + q·(μx + ν), with DivisionExists and PolynomialsBelowDim; chart 0 modulo "+
			"the product has dimension 1 + 1 + 1, each point rational with colength one "+
			"(AffinePointMaximal, RationalPointColengths) and regular (AllRationalPointsRegular), each "+
			"factor adding the colength of the next (InvertibleQuotientDim at the invertible partial "+
			"products, InvertibleProduct). So ℓ·A₀ modulo the product is zero (QuotientChainDim, DimZero)"),
})}

// LineIdealChartOne — on chart 1 the chart-one form of the line
// generates the product of the origin's ideal and the ideals of the
// three points: a point off chart 1 contributes chart 1 itself.
var LineIdealChartOne = lineIdealChartOneThm{family.Add(registry.ProofEntry{
	Name: "LineIdealChartOne",
	Key:  "prop_a94fef727715120d",
	Reading: "The origin is a simple zero of u − (μs + νs²): the line's pole of order three there " +
		"against the zero of order four of s². A root xᵢ = zero gives a point off chart 1, whose chart-1 " +
		"ideal is chart 1 (AffinePointCharts) and drops out of the product; the cubic's constant term b " +
		"− ν² is then zero, and the chart-one cubic s + as³ + bs⁴ − (μs + νs²)² = s · ∏(1 − xᵢs) loses " +
		"its top degree. The smooth datum enters as in LineIdealChartZero, through the regularity of the " +
		"points on chart 1; the origin is regular for every a and b. The origin's exponent is one for " +
		"every μ and ν: u is a uniformizer there and μs + νs² vanishes to order at least two.",
	Deps: []registry.EntryLike{
		weierstrassChartOneLineDef,
		PointIdealOnLine,
		weierstrassPointDef,
		WeierstrassOriginDef,
		WeierstrassBasisOne,
		WeierstrassChartOneEquation,
		AffinePointCharts,
		OriginMaximal,
		OriginRegular,
		AllRationalPointsRegular,
		polynomial_division.DivisionExists,
		polynomial.PolynomialsBelowDim,
		biaffine_rational_point.RationalPointColengths,
		fractional_ideal.FractionalMulDef,
		fractional_ideal.InvertibleProduct,
		ideal_colength.InvertibleQuotientDim,
		module_dimension.QuotientChainDim,
		module_dimension.DimZero,
		field.MulRightInverseOn,
		WeierstrassIsCurve,
		algebraic_curve.CurveOverLineDef,
		algebraic_curve.CurveLatticeData,
		module_record.RestrictRingDef,
		module_record.RestrictModuleDef,
		algebraic_element.PolynomialImageRing,
		ring_ideal.CarrierIdeal,
		fractional_ideal.FractionalMulOne,
		field.SubfieldFieldOn,
		fractional_ideal.FieldModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b μ ν x₁ x₂ x₃:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"μ ∈ k",
			"ν ∈ k",
			"x₁ ∈ k",
			"x₂ ∈ k",
			"x₃ ∈ k",
			"x * (x * x) + a * x + b - (μ * x + ν) * (μ * x + ν) = (x - x₁) * ((x - x₂) * (x - x₃))",
		},
		Conclusion: "image(L.mul(weierstrass_chart_one_line(x, y, μ, ν)), " +
			"    weierstrass_chart_one(L, k, x, y)) = " +
			"fractional_mul(field_ring(L), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    snd(weierstrass_origin(L, k, x, y)), " +
			"    fractional_mul(field_ring(L), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        snd(weierstrass_point(L, k, x, y, x₁, μ * x₁ + ν)), " +
			"        fractional_mul(field_ring(L), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            snd(weierstrass_point(L, k, x, y, x₂, μ * x₂ + ν)), " +
			"            snd(weierstrass_point(L, k, x, y, x₃, μ * x₃ + ν)))))",
	},
		"⊇: write ℓ₁ = u − (μs + νs²); the origin's ideal is that of s and ℓ₁, and a point with "+
			"xᵢ ≠ zero has the ideal of s − 1/xᵢ and ℓ₁ (AffinePointCharts, uᵢ = μsᵢ + νsᵢ² at sᵢ = "+
			"1/xᵢ), one with xᵢ = zero chart 1. The factorization times s⁴ (MulRightInverseOn) is s "+
			"· ∏(1 − xᵢs) = s + as³ + bs⁴ − (μs + νs²)² = u² − (μs + νs²)² = ℓ₁ · (u + μs + νs²) "+
			"(WeierstrassChartOneEquation), with 1 − xᵢs = −xᵢ · (s − 1/xᵢ), or one at xᵢ = zero. "+
			"Colengths: chart 1 modulo ℓ₁ is k[s] modulo s · ∏(1 − xᵢs), of dimension one plus the "+
			"number of nonzero roots (on the basis 1, u, WeierstrassBasisOne, with DivisionExists "+
			"and PolynomialsBelowDim); the product has the same, one for the origin (OriginMaximal, "+
			"OriginRegular) and one for each root on chart 1 (RationalPointColengths, "+
			"AllRationalPointsRegular, InvertibleQuotientDim); QuotientChainDim and DimZero"),
})}

// UniformizerAtOrigin — s = 1/x generates the square of the origin's
// ideal on chart 1: s vanishes to order two at the origin.
var UniformizerAtOrigin = uniformizerAtOriginThm{family.Add(registry.ProofEntry{
	Name: "UniformizerAtOrigin",
	Key:  "prop_1156e6626f52398c",
	Reading: "No hypothesis on a and b and no characteristic: u is a uniformizer at the origin, and " +
		"the relation u² = s · (1 + as² + bs³), with 1 + as² + bs³ a unit there, makes s its square up " +
		"to a unit. So x = 1/s has a double pole at the origin, and y = u/s² a triple one. On chart 1 " +
		"itself, without localizing, s = u² − s·(s·(as + bs²)) puts s in the square of the origin's ideal.",
	Deps: []registry.EntryLike{
		WeierstrassOriginDef,
		WeierstrassChartOneDef,
		WeierstrassChartOneEquation,
		WeierstrassBasisOne,
		fractional_ideal.FractionalMulDef,
		ring_ideal.IdealSpanDef,
		ring_ideal.SpanInsert,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "image(L.mul(L.inv(x)), weierstrass_chart_one(L, k, x, y)) = " +
			"fractional_mul(field_ring(L), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    snd(weierstrass_origin(L, k, x, y)), " +
			"    snd(weierstrass_origin(L, k, x, y)))",
	},
		"the origin's chart-1 ideal is that of s and u (WeierstrassOriginDef), so its square "+
			"is spanned by s², s · u and u² = s · (1 + as² + bs³) (WeierstrassChartOneEquation, "+
			"FractionalMulDef), all multiples of s; conversely s = u² − s² · (as + bs²) with as "+
			"+ bs² in chart 1 (WeierstrassBasisOne), so s lies in the square (SpanInsert)"),
})}

// VerticalIdealChartZero — on chart 0 the vertical line x − x₀ through
// the point (x₀, y₀) generates the product of the ideals of (x₀, y₀) and
// (x₀, −y₀): (x − x₀)·A₀ = m_P · m_{−P}.
var VerticalIdealChartZero = verticalIdealChartZeroThm{family.Add(registry.ProofEntry{
	Name: "VerticalIdealChartZero",
	Key:  "prop_95beb946cc3dcd15",
	Reading: "(x₀, −y₀) is the point −P (NegPointValues). At a two-torsion point, y₀ = zero, the " +
		"two points are one and the right side is m_P²: the vertical line is tangent there. The smooth " +
		"datum makes both points regular and is load-bearing: on the cusp y² = x³ at x₀ = zero, x " +
		"vanishes to order two along x = t², y = t³ and m² to order four, so x·A₀ is not m². At y₀ = " +
		"zero the equality m_P² = (x − x₀)·A₀ uses 3x₀² + a ≠ zero, which the discriminant gives.",
	Deps: []registry.EntryLike{
		weierstrassPointDef,
		FactoredRelation,
		WeierstrassBasisZero,
		AffinePointMaximal,
		AllRationalPointsRegular,
		NegPointValues,
		polynomial_division.DivisionExists,
		biaffine_rational_point.RationalPointColengths,
		fractional_ideal.FractionalMulDef,
		ideal_colength.InvertibleQuotientDim,
		module_dimension.QuotientChainDim,
		module_dimension.DimZero,
		WeierstrassIsCurve,
		algebraic_curve.CurveOverLineDef,
		algebraic_curve.CurveLatticeData,
		module_record.RestrictRingDef,
		module_record.RestrictModuleDef,
		algebraic_element.PolynomialImageRing,
		ring_ideal.CarrierIdeal,
		fractional_ideal.FractionalMulOne,
		field.SubfieldFieldOn,
		fractional_ideal.FieldModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
		},
		Conclusion: "image(L.mul(x - x₀), weierstrass_chart_zero(field_ring(L), k, x, y)) = " +
			"fractional_mul(field_ring(L), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    fst(weierstrass_point(L, k, x, y, x₀, y₀)), " +
			"    fst(weierstrass_point(L, k, x, y, x₀, -y₀)))",
	},
		"⊇: the product is spanned by (x − x₀)², (x − x₀)(y + y₀), (x − x₀)(y − y₀) and (y − y₀)(y + "+
			"y₀) = (x − x₀)(x² + xx₀ + x₀² + a) (FactoredRelation), all multiples of x − x₀. Colengths "+
			"over k: chart 0 modulo x − x₀ has the basis 1, y (WeierstrassBasisZero, DivisionExists at x − "+
			"x₀), dimension two; chart 0 modulo the product has 1 + 1, both points rational with colength "+
			"one ((x₀, −y₀) solves the equation with (x₀, y₀); AffinePointMaximal, RationalPointColengths) "+
			"and regular (AllRationalPointsRegular, InvertibleQuotientDim); QuotientChainDim and DimZero"),
})}

// VerticalIdealChartOne — on chart 1 the chart-one form s − x₀s² of the
// vertical line generates the square of the origin's ideal times the
// ideals of (x₀, y₀) and (x₀, −y₀); chart 1 keeps the factor of a zero
// on the overlap.
var VerticalIdealChartOne = verticalIdealChartOneThm{family.Add(registry.ProofEntry{
	Name: "VerticalIdealChartOne",
	Key:  "prop_7a7c10d0e8e996c8",
	Reading: "s − x₀s² is s² · (x − x₀): the origin is a double zero of it, x − x₀ having " +
		"a double pole there and s² a zero of order four. At x₀ = zero both points lie off " +
		"chart 1, their ideals are chart 1 itself, and the statement is UniformizerAtOrigin; " +
		"for x₀ ≠ zero both lie on chart 1 and their factors stay. The smooth datum enters as " +
		"in VerticalIdealChartZero, through the regularity of the two points.",
	Deps: []registry.EntryLike{
		UniformizerAtOrigin,
		weierstrassPointDef,
		WeierstrassOriginDef,
		FactoredRelation,
		AffinePointCharts,
		WeierstrassBasisOne,
		OriginMaximal,
		OriginRegular,
		AllRationalPointsRegular,
		polynomial_division.DivisionExists,
		biaffine_rational_point.RationalPointColengths,
		fractional_ideal.FractionalMulDef,
		ideal_colength.InvertibleQuotientDim,
		module_dimension.QuotientChainDim,
		module_dimension.DimZero,
		field.MulRightInverseOn,
		WeierstrassIsCurve,
		algebraic_curve.CurveOverLineDef,
		algebraic_curve.CurveLatticeData,
		module_record.RestrictRingDef,
		module_record.RestrictModuleDef,
		algebraic_element.PolynomialImageRing,
		ring_ideal.CarrierIdeal,
		fractional_ideal.FractionalMulOne,
		field.SubfieldFieldOn,
		fractional_ideal.FieldModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
		},
		Conclusion: "image(L.mul(L.inv(x) - x₀ * (L.inv(x) * L.inv(x))), " +
			"    weierstrass_chart_one(L, k, x, y)) = " +
			"fractional_mul(field_ring(L), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    fractional_mul(field_ring(L), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        snd(weierstrass_origin(L, k, x, y)), " +
			"        snd(weierstrass_origin(L, k, x, y))), " +
			"    fractional_mul(field_ring(L), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        snd(weierstrass_point(L, k, x, y, x₀, y₀)), " +
			"        snd(weierstrass_point(L, k, x, y, x₀, -y₀))))",
	},
		"⊇: s − x₀s² = s · (1 − x₀s), s · A₁ is the origin's ideal squared "+
			"(UniformizerAtOrigin), and for x₀ ≠ zero the two points' chart-1 ideals are those of s "+
			"− s₀ and u ∓ u₀ (AffinePointCharts), whose product lies in (s − s₀) · A₁ by the "+
			"chart-1 half of FactoredRelation, while 1 − x₀s = −x₀ · (s − s₀); for x₀ = zero both "+
			"ideals are chart 1 and 1 − x₀s = one. Colengths: chart 1 is free over k[s] on 1, u "+
			"(WeierstrassBasisOne), so modulo s · (1 − x₀s) it has dimension four for x₀ ≠ zero and "+
			"two at x₀ = zero (DivisionExists); the product has two for the origin (OriginMaximal, "+
			"OriginRegular) and one for each point on chart 1 (RationalPointColengths, "+
			"AllRationalPointsRegular, InvertibleQuotientDim); QuotientChainDim and DimZero"),
})}

// ---------------------------------------------------------------------------
// The divisors of a line and of a vertical line
// ---------------------------------------------------------------------------

// LineLatticeIdentity — the line function times the structure pair is
// P₁ · P₂ · P₃ · O⁻³: the divisor of y − (μx + ν) is P₁ + P₂ + P₃ − 3O.
var LineLatticeIdentity = lineLatticeIdentityThm{family.Add(registry.ProofEntry{
	Name: "LineLatticeIdentity",
	Key:  "prop_bcdf1bea557c8944",
	Reading: "Three zeros on chart 0 counted with multiplicity and a pole of order three at the " +
		"origin, which lies off chart 0. Read through the products of invertible pairs, P₁ · P₂ · " +
		"P₃ · O⁻³ is the multiple of the structure pair by a function, so its class is trivial: " +
		"three points on a line sum to zero in the group law with the origin as zero. The smooth " +
		"datum makes the three points regular, which both charts use, and the origin is regular for " +
		"every a and b; on the cusp y² = x³ the line y = zero fails as in LineIdealChartZero.",
	Deps: []registry.EntryLike{
		LineIdealChartZero,
		LineIdealChartOne,
		UniformizerAtOrigin,
		OriginRegular,
		weierstrassLineDef,
		weierstrassChartOneLineDef,
		WeierstrassOriginDef,
		weierstrassPointDef,
		invertible_lattice_pair.LatticePairScaleDef,
		invertible_lattice_pair.LatticePairMulDef,
		invertible_lattice_pair.LatticePairInverseDef,
		lattice_pair_twist.BiaffineRegularPointDef,
		fractional_ideal.FractionalInverseDef,
		fractional_ideal.FractionalMulOne,
		fractional_ideal.FractionalMulAssoc,
		fractional_ideal.FractionalMulComm,
		fractional_ideal.InvertibleScale,
		fractional_ideal.InvertibleProduct,
		fractional_ideal.InvertibleInverse,
		fractional_ideal.FractionalInverseUnique,
		field.MulRightInverseOn,
		WeierstrassBasisZero,
		WeierstrassBasisOne,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b μ ν x₁ x₂ x₃:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"μ ∈ k",
			"ν ∈ k",
			"x₁ ∈ k",
			"x₂ ∈ k",
			"x₃ ∈ k",
			"x * (x * x) + a * x + b - (μ * x + ν) * (μ * x + ν) = (x - x₁) * ((x - x₂) * (x - x₃))",
		},
		Conclusion: "lattice_pair_scale(weierstrass_line(x, y, μ, ν), " +
			"    (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y))) = " +
			"lattice_pair_mul(field_ring(L), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    lattice_pair_mul(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        weierstrass_point(L, k, x, y, x₁, μ * x₁ + ν), " +
			"        lattice_pair_mul(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            weierstrass_point(L, k, x, y, x₂, μ * x₂ + ν), " +
			"            weierstrass_point(L, k, x, y, x₃, μ * x₃ + ν))), " +
			"    lattice_pair_mul(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        lattice_pair_inverse(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            weierstrass_origin(L, k, x, y)), " +
			"        lattice_pair_mul(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            lattice_pair_inverse(field_ring(L), " +
			"                weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y), " +
			"                weierstrass_origin(L, k, x, y)), " +
			"            lattice_pair_inverse(field_ring(L), " +
			"                weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y), " +
			"                weierstrass_origin(L, k, x, y)))))",
	},
		"unfold lattice_pair_scale, lattice_pair_mul and lattice_pair_inverse chart by chart. Chart 0: "+
			"the origin's ideal there is chart 0, whose inverse (chart 0 : chart 0) is chart 0 "+
			"(FractionalInverseDef), absorbed by FractionalMulOne, and ℓ · A₀ is LineIdealChartZero. Chart "+
			"1: ℓ = x² · ℓ₁ (MulRightInverseOn), so ℓ · A₁ is x² times the product of LineIdealChartOne; s "+
			"· A₁ = m_O² (UniformizerAtOrigin) with m_O invertible (OriginRegular) gives x · A₁ = (s · "+
			"A₁)⁻¹ = m_O⁻² (InvertibleScale, FractionalInverseUnique, InvertibleProduct), and m_O⁻⁴ · m_O "+
			"= m_O⁻³ (InvertibleInverse, FractionalMulAssoc, FractionalMulComm)"),
})}

// VerticalLatticeIdentity — x − x₀ times the structure pair is
// P · (−P) · O⁻²: the divisor of x − x₀ is P + (−P) − 2O.
var VerticalLatticeIdentity = verticalLatticeIdentityThm{family.Add(registry.ProofEntry{
	Name: "VerticalLatticeIdentity",
	Key:  "prop_d110bc73154fedc3",
	Reading: "(x₀, −y₀) is the point −P (NegPointValues). The vertical line meets the curve " +
		"at P, at −P and once at the origin, and x − x₀ has a double pole there, x itself " +
		"having one. So the class of P · (−P) · O⁻² is trivial: −P is the inverse of P in the " +
		"group law with the origin as zero, and at a two-torsion point P · P · O⁻² is principal.",
	Deps: []registry.EntryLike{
		VerticalIdealChartZero,
		VerticalIdealChartOne,
		UniformizerAtOrigin,
		OriginRegular,
		WeierstrassOriginDef,
		weierstrassPointDef,
		NegPointValues,
		invertible_lattice_pair.LatticePairScaleDef,
		invertible_lattice_pair.LatticePairMulDef,
		invertible_lattice_pair.LatticePairInverseDef,
		fractional_ideal.FractionalInverseDef,
		fractional_ideal.FractionalMulOne,
		fractional_ideal.FractionalMulAssoc,
		fractional_ideal.FractionalMulComm,
		fractional_ideal.InvertibleScale,
		fractional_ideal.InvertibleProduct,
		fractional_ideal.InvertibleInverse,
		fractional_ideal.FractionalInverseUnique,
		field.MulRightInverseOn,
		WeierstrassBasisZero,
		WeierstrassBasisOne,
		lattice_pair_twist.BiaffineRegularPointDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b x₀ y₀:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"x₀ ∈ k",
			"y₀ ∈ k",
			"y₀ * y₀ = x₀ * (x₀ * x₀) + a * x₀ + b",
		},
		Conclusion: "lattice_pair_scale(x - x₀, " +
			"    (weierstrass_chart_zero(field_ring(L), k, x, y), weierstrass_chart_one(L, k, x, y))) = " +
			"lattice_pair_mul(field_ring(L), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    lattice_pair_mul(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        weierstrass_point(L, k, x, y, x₀, y₀), " +
			"        weierstrass_point(L, k, x, y, x₀, -y₀)), " +
			"    lattice_pair_mul(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        lattice_pair_inverse(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            weierstrass_origin(L, k, x, y)), " +
			"        lattice_pair_inverse(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            weierstrass_origin(L, k, x, y))))",
	},
		"unfold lattice_pair_scale, lattice_pair_mul and lattice_pair_inverse chart by "+
			"chart. Chart 0: the origin's inverse ideal there is chart 0 (FractionalInverseDef, "+
			"FractionalMulOne), and (x − x₀) · A₀ is VerticalIdealChartZero. Chart 1: x − x₀ = "+
			"x² · (s − x₀s²) (MulRightInverseOn), so (x − x₀) · A₁ is x² times the product of "+
			"VerticalIdealChartOne; x · A₁ = (s · A₁)⁻¹ = m_O⁻² (UniformizerAtOrigin, "+
			"OriginRegular, InvertibleScale, FractionalInverseUnique, InvertibleProduct), and "+
			"m_O⁻⁴ · m_O² = m_O⁻² (InvertibleInverse, FractionalMulAssoc, FractionalMulComm)"),
})}
