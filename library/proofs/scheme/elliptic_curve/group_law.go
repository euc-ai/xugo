// group_law.go — the chord-and-tangent construction as the group law of
// the curve. The sum of rational points is the group of Pic⁰ carried to
// the points (picard.go); a line y = μx + ν meeting the curve in three
// points, counted with multiplicity, has divisor P₁ + P₂ + P₃ − 3O
// (lines.go), so the three points sum to the origin, and the sum of two
// points is the reflection of the third point of the chord or the tangent
// through them. Read in coordinates this is the addition table: the slope
// μ of the chord or of the tangent, x₃ = μ² − x₁ − x₂, and the height of
// the third point reflected.

package elliptic_curve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Three points on a line
// ---------------------------------------------------------------------------

// ChordTangentSum — the three points where a line y = μx + ν meets the
// curve, counted with multiplicity, sum to the origin in the transported
// group law: P₁ ⊕ P₂ is the reflection −P₃ of the third point.
var ChordTangentSum = chordTangentSumThm{family.Add(registry.ProofEntry{
	Name: "ChordTangentSum",
	Key:  "prop_f0c79d674dde4c42",
	Reading: "The roots are counted with multiplicity: a line tangent at P has P₁ = P₂ = P and " +
		"gives P ⊕ P = −P₃, a flex P₁ = P₂ = P₃ = P and 3P = O. The line is not vertical, so the " +
		"origin is never among the three; the vertical line x = x₀ is the inverse law P ⊕ (−P) = O, " +
		"which PointGroupTransported states. 2 ≠ 0 and 4a³ + 27b² ≠ 0 are load-bearing twice: they " +
		"make the transported sum a group law (PointGroupTransported) and the line's divisor P₁ + P₂ " +
		"+ P₃ − 3O (LineLatticeIdentity); on the cusp y² = x³ the line y = zero meets the curve only " +
		"at the singular point, which has no invertible ideal, and nothing determines the sum there.",
	Deps: []registry.EntryLike{
		LineLatticeIdentity,
		PointIdealOnLine,
		AffinePointMaximal,
		AllRationalPointsRegular,
		OriginRegular,
		WeierstrassBasisZero,
		WeierstrassIsCurve,
		PointGroupTransported,
		AbelJacobiInjective,
		WeierstrassPointSumDef,
		WeierstrassNegPointDef,
		weierstrassPointDef,
		WeierstrassOriginDef,
		weierstrassLineDef,
		curve_degree.CurvePointClassDef,
		curve_degree.PairClassEqIff,
		curve_degree.PairClassMul,
		lattice_pair_twist.LatticePairTwistDef,
		invertible_lattice_pair.StructurePairInvertible,
		invertible_lattice_pair.InvertibleLatticeScale,
		invertible_lattice_pair.InvertibleLatticeProduct,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.MulAssoc,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.MulOne,
		abelian_group.GroupOn,
		group.InvUniqueOn,
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
		Conclusion: "weierstrass_point_sum(L, " +
			"    k, " +
			"    x, " +
			"    y, " +
			"    weierstrass_point_sum(L, " +
			"        k, " +
			"        x, " +
			"        y, " +
			"        weierstrass_point(L, k, x, y, x₁, μ * x₁ + ν), " +
			"        weierstrass_point(L, k, x, y, x₂, μ * x₂ + ν)), " +
			"    weierstrass_point(L, k, x, y, x₃, μ * x₃ + ν)) = " +
			"weierstrass_origin(L, k, x, y) ∧ " +
			"weierstrass_point_sum(L, " +
			"    k, " +
			"    x, " +
			"    y, " +
			"    weierstrass_point(L, k, x, y, x₁, μ * x₁ + ν), " +
			"    weierstrass_point(L, k, x, y, x₂, μ * x₂ + ν)) = " +
			"weierstrass_neg_point(L, k, x, y, weierstrass_point(L, k, x, y, x₃, μ * x₃ + ν))",
	},
		"each Pᵢ is a rational point (PointIdealOnLine, AffinePointMaximal) and regular "+
			"(AllRationalPointsRegular); with E the origin's ideal pair, regular (OriginRegular), the "+
			"class of O(Pᵢ − O) is that of Pᵢ⁻¹ · E (curve_degree.CurvePointClassDef, "+
			"LatticePairTwistDef). LineLatticeIdentity makes P₁ · P₂ · P₃ · E⁻³ the multiple ℓ · (A₀, A₁) "+
			"by ℓ = y − (μx + ν), nonzero as y lies outside k[x] (WeierstrassBasisZero), so its class is "+
			"the unit (curve_degree.PairClassEqIff at WeierstrassIsCurve, StructurePairInvertible, "+
			"InvertibleLatticeScale); the three point classes times it give the class of the product of "+
			"the Pᵢ⁻¹ · Pᵢ and of E³ · E⁻³, the unit (curve_degree.PairClassMul, MulAssoc, MulComm, "+
			"InvertibleLatticeInverse, MulOne), so the product of the three point classes is the unit. "+
			"PointGroupTransported carries this to the points: (P₁ ⊕ P₂) ⊕ P₃ is rational with the class "+
			"of E⁻¹ · E = (A₀, A₁), the origin's, so it is the origin (AbelJacobiInjective); in that "+
			"group z ⊕ P₃ = O is z = −P₃ (group.InvUniqueOn through abelian_group.GroupOn)"),
})}

// ---------------------------------------------------------------------------
// The addition table
// ---------------------------------------------------------------------------

// GroupLawFormulas — the transported sum in coordinates: the origin is the
// unit; (x₁, y₁) ⊕ (x₁, −y₁) is the origin; and otherwise the sum of
// (x₁, y₁) and (x₂, y₂) is (x₃, −(μ(x₃ − x₁) + y₁)) with x₃ = μ² − x₁ − x₂,
// μ the slope of the chord, or of the tangent where the two points are one.
var GroupLawFormulas = groupLawFormulasThm{family.Add(registry.ProofEntry{
	Name: "GroupLawFormulas",
	Key:  "prop_df71209f4b4a641b",
	Reading: "The clauses cover every pair of rational points: the origin by the first; for " +
		"affine points x₁ ≠ x₂ is the chord, and x₁ = x₂ forces y₂ = ±y₁ — y₂ = −y₁ is the vertical " +
		"line, a 2-torsion point doubling to the origin among them since its tangent is vertical, " +
		"and y₂ = y₁ ≠ −y₁ forces y₁ ≠ zero as 2 ≠ 0, which is the tangent. y₁ ≠ zero is " +
		"load-bearing in the tangent clause: field_on sets inv(zero) = zero, so at a 2-torsion point " +
		"the formula would read μ = zero and the point (−2x₁, 0), while the sum is the origin. The " +
		"chord clause holds also where the line is tangent at one of the two points: x₃ = x₁ gives " +
		"the sum −P. In characteristic 2 the tangent's denominator 2y₁ vanishes at every point, " +
		"which the smooth datum excludes; in characteristic 3, 3x₁² + a is a. The denominators are " +
		"invertible by the clauses' hypotheses: x₂ − x₁ by x₁ ≠ x₂, and 2y₁ by y₁ ≠ zero with 2 ≠ 0.",
	Deps: []registry.EntryLike{
		ChordTangentSum,
		PointGroupTransported,
		LineCubicFactors,
		PointIdealOnLine,
		NegPointValues,
		AffinePointMaximal,
		OriginMaximal,
		WeierstrassPointSumDef,
		WeierstrassNegPointDef,
		weierstrassPointDef,
		WeierstrassOriginDef,
		abelian_group.GroupOn,
		group.LeftIdentityOn,
		group.RightIdentityOn,
		group.RightInverseOn,
		field.SubfieldAdd,
		field.SubfieldSub,
		field.SubfieldMul,
		field.SubfieldInv,
		field.MulEqZeroOn,
		field.MulRightInverseOn,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∀P:prod(set(A), set(A)). " +
			"    biaffine_rational_point(restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        k, " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        P) ⇒ " +
			"    weierstrass_point_sum(L, k, x, y, weierstrass_origin(L, k, x, y), P) = P ∧ " +
			"    weierstrass_point_sum(L, k, x, y, P, weierstrass_origin(L, k, x, y)) = P) ∧ " +
			"(∀x₁ y₁ x₂ y₂:A. " +
			"    x₁ ∈ k ∧ " +
			"    y₁ ∈ k ∧ " +
			"    y₁ * y₁ = x₁ * (x₁ * x₁) + a * x₁ + b ∧ " +
			"    x₂ ∈ k ∧ " +
			"    y₂ ∈ k ∧ " +
			"    y₂ * y₂ = x₂ * (x₂ * x₂) + a * x₂ + b ∧ " +
			"    x₁ = x₂ ∧ " +
			"    y₂ = -y₁ ⇒ " +
			"    weierstrass_point_sum(L, " +
			"        k, " +
			"        x, " +
			"        y, " +
			"        weierstrass_point(L, k, x, y, x₁, y₁), " +
			"        weierstrass_point(L, k, x, y, x₂, y₂)) = " +
			"    weierstrass_origin(L, k, x, y)) ∧ " +
			"(∀x₁ y₁ x₂ y₂ μ x₃ y₃:A. " +
			"    x₁ ∈ k ∧ " +
			"    y₁ ∈ k ∧ " +
			"    y₁ * y₁ = x₁ * (x₁ * x₁) + a * x₁ + b ∧ " +
			"    x₂ ∈ k ∧ " +
			"    y₂ ∈ k ∧ " +
			"    y₂ * y₂ = x₂ * (x₂ * x₂) + a * x₂ + b ∧ " +
			"    x₁ ≠ x₂ ∧ " +
			"    μ = (y₂ - y₁) * L.inv(x₂ - x₁) ∧ " +
			"    x₃ = μ * μ - x₁ - x₂ ∧ " +
			"    y₃ = -(μ * (x₃ - x₁) + y₁) ⇒ " +
			"    weierstrass_point_sum(L, " +
			"        k, " +
			"        x, " +
			"        y, " +
			"        weierstrass_point(L, k, x, y, x₁, y₁), " +
			"        weierstrass_point(L, k, x, y, x₂, y₂)) = " +
			"    weierstrass_point(L, k, x, y, x₃, y₃)) ∧ " +
			"(∀x₁ y₁ μ x₃ y₃:A. " +
			"    x₁ ∈ k ∧ " +
			"    y₁ ∈ k ∧ " +
			"    y₁ * y₁ = x₁ * (x₁ * x₁) + a * x₁ + b ∧ " +
			"    y₁ ≠ L.zero ∧ " +
			"    μ = ((L.one + L.one + L.one) * (x₁ * x₁) + a) * L.inv((L.one + L.one) * y₁) ∧ " +
			"    x₃ = μ * μ - x₁ - x₁ ∧ " +
			"    y₃ = -(μ * (x₃ - x₁) + y₁) ⇒ " +
			"    weierstrass_point_sum(L, " +
			"        k, " +
			"        x, " +
			"        y, " +
			"        weierstrass_point(L, k, x, y, x₁, y₁), " +
			"        weierstrass_point(L, k, x, y, x₁, y₁)) = " +
			"    weierstrass_point(L, k, x, y, x₃, y₃))",
	},
		"the first two clauses are the unit and inverse laws of the group of "+
			"PointGroupTransported (group.LeftIdentityOn, group.RightIdentityOn, group.RightInverseOn "+
			"through abelian_group.GroupOn), the origin and the affine points being rational "+
			"(OriginMaximal, AffinePointMaximal) and (x₁, −y₁) being −P (NegPointValues). Chord: μ ∈ "+
			"k (SubfieldSub, SubfieldInv, SubfieldMul), and with ν = y₁ − μx₁ both points lie on y = "+
			"μx + ν, so LineCubicFactors splits the cubic with third root x₃ = μ² − x₁ − x₂; "+
			"ChordTangentSum gives P ⊕ Q = −(x₃, μx₃ + ν), the third point lying on the curve "+
			"(PointIdealOnLine), which is (x₃, −(μ(x₃ − x₁) + y₁)) by NegPointValues. Tangent: 2y₁ ≠ "+
			"zero (MulEqZeroOn), so μ · 2y₁ = 3x₁² + a (MulRightInverseOn), LineCubicFactors' "+
			"tangency clause at x₁ = x₂ with ν = y₁ − μx₁, and the same argument runs with P₁ = P₂ = P"),
})}
