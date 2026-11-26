// picard.go — the Abel–Jacobi map of the Weierstrass curve. Based at the
// origin, a regular point P goes to the class of O(P − O) in Pic⁰
// (algebraic_curve's picard.go). Riemann–Roch with a trivial canonical
// pair and genus one makes this map one-to-one (ℓ(O(Q)) = 1) and onto (a
// pair of degree one has a section, which pins it to a point), so where
// the curve is smooth its rational points carry the group of Pic⁰, the
// origin its unit and the conjugation y ↦ −y its inverse.

package elliptic_curve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Abel–Jacobi on the Weierstrass curve
// ---------------------------------------------------------------------------

// AbelJacobiInjective — on the Weierstrass curve based at the origin,
// distinct regular points have distinct classes O(P − O).
var AbelJacobiInjective = abelJacobiInjectiveThm{family.Add(registry.ProofEntry{
	Name: "AbelJacobiInjective",
	Key:  "prop_1ad523402180ff0d",
	Reading: "Genus one is what is used: O(Q) has only the constants as sections, ℓ(O(Q)) = 1 by " +
		"WeierstrassRiemannRoch, H⁰(Q) being zero as a constant in a proper ideal is zero. So a multiple " +
		"a · O(Q) holding one has a constant, and O(P) = a · O(Q) forces P = Q. No characteristic and no " +
		"discriminant hypothesis: on a nodal or cuspidal cubic the regular points are what it reads. " +
		"ℓ(O(Q)) = 1 rests on ω being trivial (CanonicalTrivial), as it is on every cubic.",
	Deps: []registry.EntryLike{
		curve_degree.CurvePointClassDef,
		curve_degree.PairClassEqIff,
		WeierstrassRiemannRoch,
		OriginRegular,
		WeierstrassIsCurve,
		WeierstrassGlobalSections,
		WeierstrassOriginDef,
		lattice_pair_twist.LatticePairTwistDef,
		invertible_lattice_pair.InvertibleLatticeInverse,
		lattice_pair_twist.TwistInverseTwist,
		lattice_pair_twist.TwistInvertible,
		invertible_lattice_pair.MulAssoc,
		invertible_lattice_pair.MulOne,
		invertible_lattice_pair.LatticePairScaleDef,
		lattice_pair.LatticePairH0Def,
		lattice_pair_twist.BiaffineRegularPointDef,
		biaffine_rational_point.BiaffineRationalPointDef,
		curve_degree.DegreeTwist,
		curve_degree.DegreeStructure,
		module_dimension.DimZero,
		invertible_lattice_pair.ScaleMulAssoc,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀P Q:prod(set(A), set(A)).",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"biaffine_regular_point(field_ring(L), " +
				"    k, " +
				"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
				"    weierstrass_chart_one(L, k, x, y), " +
				"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
				"    P)",
			"biaffine_regular_point(field_ring(L), " +
				"    k, " +
				"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
				"    weierstrass_chart_one(L, k, x, y), " +
				"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
				"    Q)",
			"curve_point_class(field_ring(L), " +
				"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
				"    weierstrass_chart_one(L, k, x, y), " +
				"    weierstrass_origin(L, k, x, y), " +
				"    P) = " +
				"curve_point_class(field_ring(L), " +
				"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
				"    weierstrass_chart_one(L, k, x, y), " +
				"    weierstrass_origin(L, k, x, y), " +
				"    Q)",
		},
		Conclusion: "P = Q",
	},
		"with E the origin's ideal pair, regular (OriginRegular), the classes agree, so E(P) = P⁻¹ · E "+
			"equals a · (Q⁻¹ · E) for some a ≠ zero (curve_degree.PairClassEqIff, both invertible by "+
			"TwistInvertible); multiplying by E⁻¹ gives P⁻¹ = a · Q⁻¹ (MulAssoc, InvertibleLatticeInverse, "+
			"MulOne, scaling commuting with the product chart by chart). H⁰(Q) = fst(Q) ∩ snd(Q) lies in "+
			"A₀ ∩ A₁ = k (WeierstrassGlobalSections) and in a proper ideal of some chart "+
			"(BiaffineRationalPointDef), so it is {zero} and ℓ(Q) = 0 (DimZero); WeierstrassRiemannRoch at "+
			"Q⁻¹, of degree one (DegreeTwist, DegreeStructure), gives ℓ(Q⁻¹) = 1, and k ⊆ H⁰(Q⁻¹), so "+
			"H⁰(Q⁻¹) = k. one ∈ H⁰(P⁻¹) = a · H⁰(Q⁻¹) gives one = a·c with c ∈ k, so a ∈ k is a unit of "+
			"both charts and a · Q⁻¹ = Q⁻¹; then P = (P⁻¹)⁻¹ = (Q⁻¹)⁻¹ = Q (InvertibleLatticeInverse)"),
})}

// AbelJacobiSurjective — on the Weierstrass curve based at the origin,
// every class of Pic⁰ is the class O(P − O) of a regular point P.
var AbelJacobiSurjective = abelJacobiSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "AbelJacobiSurjective",
	Key:  "prop_829db7781df10357",
	Reading: "Riemann–Roch at degree one: twisting a pair of degree zero at the origin gives " +
		"degree one = g, which has a nonzero section (LargeDegreeHasSection), and a pair of " +
		"degree one with a section is a multiple of O(P) (DegreeOneSectionIsPoint). The point " +
		"found is regular, whatever the curve; no characteristic and no discriminant hypothesis. " +
		"On a nodal or cuspidal cubic this agrees with Pic⁰ being G_m or G_a, the smooth locus.",
	Deps: []registry.EntryLike{
		curve_degree.InPicZero,
		curve_degree.CurvePointClassDef,
		curve_degree.PairClassEqIff,
		OriginRegular,
		WeierstrassIsCurve,
		GenusOne,
		curve_degree.LargeDegreeHasSection,
		curve_degree.DegreeOneSectionIsPoint,
		curve_degree.DegreeTwist,
		lattice_pair_twist.TwistInvertible,
		lattice_pair_twist.TwistInverseTwist,
		lattice_pair_twist.LatticePairTwistDef,
		invertible_lattice_pair.MulAssoc,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.MulOne,
		invertible_lattice_pair.LatticePairScaleDef,
		invertible_lattice_pair.ScaleMulAssoc,
		invertible_lattice_pair.InvertibleLatticeInverse,
		algebraic_curve.CurveLatticeData,
		lattice_pair_twist.BiaffineRegularPointDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀X:set(prod(set(A), set(A))).",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"X ∈ " +
				"curve_pic_zero(field_ring(L), " +
				"    k, " +
				"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
				"    weierstrass_chart_one(L, k, x, y), " +
				"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x))",
		},
		Conclusion: "∃P:prod(set(A), set(A)). " +
			"    biaffine_regular_point(field_ring(L), " +
			"        k, " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
			"        P) ∧ " +
			"    X = " +
			"    curve_point_class(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        weierstrass_origin(L, k, x, y), " +
			"        P)",
	},
		"X is the class of an invertible M of degree zero (curve_degree.InPicZero); with E the "+
			"origin's ideal pair, regular (OriginRegular), N = M(E) is invertible (TwistInvertible) of "+
			"degree one (DegreeTwist); the genus is one (GenusOne) at the curve (WeierstrassIsCurve), "+
			"so N has a nonzero section a (LargeDegreeHasSection) and N = a · (A₀, A₁)(P) = a · P⁻¹ "+
			"for a regular P (DegreeOneSectionIsPoint, LatticePairTwistDef, MulComm, MulOne); then M = "+
			"N · E (TwistInverseTwist) = a · (P⁻¹ · E) = a · E(P), scaling commuting with the product "+
			"(MulAssoc), so X = class(E(P)) (curve_degree.PairClassEqIff), the class of P"),
})}

// AbelJacobiBijection — where the curve is smooth, P ↦ the class of
// O(P − O) is a bijection from the rational points onto Pic⁰: E(k) ≅ Pic⁰(E).
var AbelJacobiBijection = abelJacobiBijectionThm{family.Add(registry.ProofEntry{
	Name: "AbelJacobiBijection",
	Key:  "prop_9cd5073d55178cfe",
	Reading: "2 ≠ 0 and 4a³ + 27b² ≠ 0 make every rational point regular " +
		"(AllRationalPointsRegular), so the rational points are the regular points " +
		"AbelJacobiInjective and AbelJacobiSurjective read. On a singular cubic the " +
		"bijection is from the regular points, the singular point having no invertible ideal.",
	Deps: []registry.EntryLike{
		AbelJacobiInjective,
		AbelJacobiSurjective,
		curve_degree.PointClassDegreeZero,
		AllRationalPointsRegular,
		OriginRegular,
		WeierstrassIsCurve,
		lattice_pair_twist.BiaffineRegularPointDef,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "injective_on({P:prod(set(A), set(A)) | " +
			"        biaffine_rational_point(restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            k, " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            P)}, " +
			"    λP:prod(set(A), set(A)). " +
			"        curve_point_class(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            weierstrass_origin(L, k, x, y), " +
			"            P)) ∧ " +
			"image(λP:prod(set(A), set(A)). " +
			"        curve_point_class(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            weierstrass_origin(L, k, x, y), " +
			"            P), " +
			"    {P:prod(set(A), set(A)) | " +
			"        biaffine_rational_point(restrict_ring(field_ring(L), " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            k, " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            P)}) = " +
			"curve_pic_zero(field_ring(L), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x))",
	},
		"a rational point is regular (AllRationalPointsRegular) and a regular point rational "+
			"(BiaffineRegularPointDef); one-to-one by AbelJacobiInjective; the image lies in "+
			"Pic⁰ by curve_degree.PointClassDegreeZero at the curve (WeierstrassIsCurve) with E "+
			"the origin (OriginRegular), and is all of it by AbelJacobiSurjective"),
})}

// ---------------------------------------------------------------------------
// The group of rational points
// ---------------------------------------------------------------------------

// WeierstrassPointSumDef — `weierstrass_point_sum(L, k, x, y, P, Q)`, written
// P ⊕ Q: a rational point whose class O(R − O) is the product of the
// classes of P and Q.
var WeierstrassPointSumDef = weierstrassPointSumDefThm{family.Define(registry.DefEntry{
	Name:  "WeierstrassPointSumDef",
	Key:   "prop_ce81a0113af5943b",
	Const: "weierstrass_point_sum",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"A → " +
		"A → " +
		"prod(set(A), set(A)) → " +
		"prod(set(A), set(A)) → " +
		"prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀P:prod(set(A), set(A)). ∀Q:prod(set(A), set(A)). " +
			"    weierstrass_point_sum(F, k, x, y, P, Q) = " +
			"    εR:prod(set(A), set(A)). " +
			"        biaffine_rational_point(restrict_ring(field_ring(F), " +
			"                ring_away(field_ring(F), weierstrass_chart_zero(field_ring(F), k, x, y), x)), " +
			"            k, " +
			"            weierstrass_chart_zero(field_ring(F), k, x, y), " +
			"            weierstrass_chart_one(F, k, x, y), " +
			"            R) ∧ " +
			"        curve_point_class(field_ring(F), " +
			"            weierstrass_chart_zero(field_ring(F), k, x, y), " +
			"            weierstrass_chart_one(F, k, x, y), " +
			"            weierstrass_origin(F, k, x, y), " +
			"            R) = " +
			"        curve_class_mul(field_ring(F), " +
			"            weierstrass_chart_zero(field_ring(F), k, x, y), " +
			"            weierstrass_chart_one(F, k, x, y), " +
			"            curve_point_class(field_ring(F), " +
			"                weierstrass_chart_zero(field_ring(F), k, x, y), " +
			"                weierstrass_chart_one(F, k, x, y), " +
			"                weierstrass_origin(F, k, x, y), " +
			"                P), " +
			"            curve_point_class(field_ring(F), " +
			"                weierstrass_chart_zero(field_ring(F), k, x, y), " +
			"                weierstrass_chart_one(F, k, x, y), " +
			"                weierstrass_origin(F, k, x, y), " +
			"                Q))",
	},
	Reading: "The group law of Pic⁰ carried to the points by the Abel–Jacobi map. " +
		"Where the curve is smooth exactly one rational point has the product class " +
		"(AbelJacobiBijection), so the choice is determined (PointGroupTransported); " +
		"elsewhere nothing is said of it. The chord–tangent construction computes it.",
	Deps: []registry.EntryLike{WeierstrassChartZeroDef, WeierstrassChartOneDef, WeierstrassOriginDef},
})}

// NegPointClass — the conjugation y ↦ −y keeps the regular points and
// sends the class of O(P − O) to its inverse: O(−P − O) ≅ O(O − P).
var NegPointClass = negPointClassThm{family.Add(registry.ProofEntry{
	Name: "NegPointClass",
	Key:  "prop_db8d1b27079a26e",
	Reading: "The vertical line x = x₀ through P = (x₀, y₀) meets the curve at P and −P and " +
		"has a double pole at the origin O: with E the origin's ideal pair, (x − x₀) · (A₀, A₁) = " +
		"P · (−P) · E⁻¹ · E⁻¹, the divisor P + (−P) − 2O, so O(−P − O) · O(P − O) is (x − x₀)⁻¹ · " +
		"(A₀, A₁). At a 2-torsion point −P = P and the line is tangent; at the origin both sides " +
		"are the class of the structure pair. P regular is what is asked; no characteristic and " +
		"no discriminant hypothesis. In characteristic 2 the conjugation is the identity, so " +
		"every O(P − O) is 2-torsion; that is true, the cubic being geometrically cuspidal with " +
		"Pic⁰ inside G_a. Carrying invertibility through the conjugation needs it as an " +
		"automorphism of all of L, which the fraction-field clause of the datum gives.",
	Deps: []registry.EntryLike{
		WeierstrassNegPointDef,
		NegPointValues,
		RationalPointsOfWeierstrass,
		curve_degree.CurvePointClassDef,
		curve_degree.PairClassInverse,
		curve_degree.PairClassEqIff,
		OriginRegular,
		WeierstrassIsCurve,
		WeierstrassBasisZero,
		WeierstrassBasisOne,
		FactoredRelation,
		WeierstrassChartOneEquation,
		AffinePointCharts,
		lattice_pair_twist.BiaffineRegularPointDef,
		invertible_lattice_pair.InvertibleLatticePairDef,
		lattice_pair_twist.LatticePairTwistDef,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.MulAssoc,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.MulOne,
		lattice_pair_twist.TwistInvertible,
		invertible_lattice_pair.InvertibleLatticeProduct,
		invertible_lattice_pair.InvertibleLatticeScale,
		invertible_lattice_pair.ScaleMulAssoc,
		curve_degree.PointClassDegreeZero,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"biaffine_regular_point(field_ring(L), " +
				"    k, " +
				"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
				"    weierstrass_chart_one(L, k, x, y), " +
				"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
				"    P)",
		},
		Conclusion: "biaffine_regular_point(field_ring(L), " +
			"    k, " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x), " +
			"    weierstrass_neg_point(L, k, x, y, P)) ∧ " +
			"curve_point_class(field_ring(L), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    weierstrass_origin(L, k, x, y), " +
			"    weierstrass_neg_point(L, k, x, y, P)) = " +
			"curve_class_inverse(field_ring(L), " +
			"    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"    weierstrass_chart_one(L, k, x, y), " +
			"    curve_point_class(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        weierstrass_origin(L, k, x, y), " +
			"        P))",
	},
		"the conjugation p + q·y ↦ p − q·y is a ring automorphism of each chart and of the overlap "+
			"fixing k (WeierstrassBasisZero, WeierstrassBasisOne; on chart 1 it is u ↦ −u), so it carries "+
			"ideals, invertibility and rational points to the same (WeierstrassNegPointDef, "+
			"BiaffineRegularPointDef). P is the origin or the point of (x₀, y₀) "+
			"(RationalPointsOfWeierstrass); the origin is fixed (NegPointValues) and its class is the "+
			"unit, its own inverse. Otherwise −P is the point of (x₀, −y₀) (NegPointValues), and the "+
			"vertical line gives P · (−P) = (x − x₀) · (E · E), E the origin's ideal pair: on chart 0 the "+
			"ideal of x − x₀ is m_P · m_(−P), the four products of generators being x − x₀ times x − x₀, "+
			"y + y₀, y − y₀ and x² + xx₀ + x₀² + a (FactoredRelation), which generate the chart where P "+
			"is regular; on chart 1 the origin's ideal (s, u) squares to s · A₁, as u² = s · (1 + as² + "+
			"bs³) (WeierstrassChartOneEquation), and x − x₀ = (1 − x₀·s)/s, the same factorization in s "+
			"and u where x₀ ≠ zero and a unit where x₀ = zero. Then (−P)⁻¹ · E = (x − x₀)⁻¹ · (P · E⁻¹), "+
			"whose class is the inverse of the class of P⁻¹ · E (curve_degree.PairClassEqIff, "+
			"curve_degree.PairClassInverse, InvertibleLatticeInverse, MulAssoc, MulComm, MulOne)"),
})}

// PointGroupTransported — where the curve is smooth, its rational points
// are an abelian group under the sum carried from Pic⁰, with the origin as
// unit and the conjugation y ↦ −y as inverse, and P ↦ the class of
// O(P − O) carries the sum to the product of classes.
var PointGroupTransported = pointGroupTransportedThm{family.Add(registry.ProofEntry{
	Name: "PointGroupTransported",
	Key:  "prop_e240a6f33a6adb00",
	Reading: "The group of rational points is the group of Pic⁰ (curve_degree.PicZeroAbelian) " +
		"carried along the inverse of the Abel–Jacobi bijection by " +
		"group_homomorphism.ImageAbelianGroupOn: a map from an abelian group onto a bare record that " +
		"keeps the product, the unit and the inverse makes the record an abelian group, so no group " +
		"axiom is checked at the points. What the card proves is the four equations the image law asks " +
		"for — the image is the rational points, and the sum, the origin and the conjugation are the " +
		"images of the product, the unit and the inverse of classes — and the second conjunct, the ε of " +
		"WeierstrassPointSumDef read at a product class that has a rational point. Both clauses the " +
		"smooth datum adds, 2 ≠ 0 and 4a³ + 27b² ≠ 0, are load-bearing through AllRationalPointsRegular: " +
		"on a singular cubic the singular point has no class and the sum leaves it undetermined.",
	Deps: []registry.EntryLike{
		WeierstrassPointSumDef,
		AbelJacobiBijection,
		AbelJacobiInjective,
		AbelJacobiSurjective,
		curve_degree.PicZeroAbelian,
		curve_degree.PicZeroGroupOn,
		NegPointClass,
		curve_degree.PointClassDegreeZero,
		AllRationalPointsRegular,
		OriginRegular,
		OriginMaximal,
		NegPointValues,
		WeierstrassIsCurve,
		group_homomorphism.ImageAbelianGroupOn,
		set_image.FunInImage,
		set_image.ForallInImage,
		lattice_pair_twist.BiaffineRegularPointDef,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.MulComm,
		lattice_pair_twist.LatticePairTwistDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "abelian_group_on(mk_group(λP:prod(set(A), set(A)). λQ:prod(set(A), set(A)). " +
			"            weierstrass_point_sum(L, k, x, y, P, Q), " +
			"        weierstrass_origin(L, k, x, y), " +
			"        λP:prod(set(A), set(A)). weierstrass_neg_point(L, k, x, y, P), " +
			"        {P:prod(set(A), set(A)) | " +
			"            biaffine_rational_point(restrict_ring(field_ring(L), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)), " +
			"                k, " +
			"                weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                weierstrass_chart_one(L, k, x, y), " +
			"                P)})) ∧ " +
			"(∀P Q:prod(set(A), set(A)). " +
			"    biaffine_rational_point(restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        k, " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        P) ∧ " +
			"    biaffine_rational_point(restrict_ring(field_ring(L), " +
			"            ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"        k, " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        Q) ⇒ " +
			"    curve_point_class(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        weierstrass_origin(L, k, x, y), " +
			"        weierstrass_point_sum(L, k, x, y, P, Q)) = " +
			"    curve_class_mul(field_ring(L), " +
			"        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"        weierstrass_chart_one(L, k, x, y), " +
			"        curve_point_class(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            weierstrass_origin(L, k, x, y), " +
			"            P), " +
			"        curve_point_class(field_ring(L), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"            weierstrass_chart_one(L, k, x, y), " +
			"            weierstrass_origin(L, k, x, y), " +
			"            Q)))",
	},
		"take f: a class X ↦ εP. rational(P) ∧ curve_point_class(P) = X, the inverse of "+
			"AbelJacobiBijection, and read ImageAbelianGroupOn at the group of "+
			"curve_degree.PicZeroAbelian (at WeierstrassIsCurve) and the point record; the first "+
			"conjunct is its conclusion once its four hypotheses hold. Image: for X in Pic⁰, "+
			"AbelJacobiSurjective gives a regular, so rational (BiaffineRegularPointDef), point of "+
			"class X, so f(X) is rational with class X (ForallInImage); a rational P is regular "+
			"(AllRationalPointsRegular), its class lies in Pic⁰ (curve_degree.PointClassDegreeZero "+
			"at OriginRegular) and f of its class is P by AbelJacobiInjective (FunInImage). Product: "+
			"f(X) ⊕ f(Y) is the ε of WeierstrassPointSumDef at the classes of f(X) and f(Y), which "+
			"are X and Y, so it is f(X · Y) as a term; the second conjunct is the same ε read at "+
			"rational P, Q, whose product class lies in Pic⁰ (curve_degree.PicZeroGroupOn) and so "+
			"has a rational point. Unit: the origin is rational (OriginMaximal) and its class is "+
			"that of E⁻¹ · E = (A₀, A₁) for its ideal pair E (InvertibleLatticeInverse, MulComm), "+
			"the unit of Pic⁰, so f of the unit is the origin by AbelJacobiInjective. Inverse: the "+
			"conjugation keeps the rational points (NegPointValues) and sends the class of f(X) to "+
			"its inverse (NegPointClass, f(X) regular), so f(X⁻¹) = −f(X) by AbelJacobiInjective"),
})}
