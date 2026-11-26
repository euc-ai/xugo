// projective_model.go — the Weierstrass cubic as a plane projective
// curve: Y²Z − X³ − aXZ² − bZ³, with coefficients in a finite subfield k
// of a field M, is a smooth projective equation curve of genus one when
// 2 ≠ 0 and 4a³ + 27b² ≠ 0.

package elliptic_curve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/registry"
)

// WeierstrassSmoothProjectiveCurve — the Weierstrass cubic over a finite
// subfield, outside characteristic two and with nonzero discriminant, is a
// smooth projective equation curve, of genus one.
var WeierstrassSmoothProjectiveCurve = weierstrassSmoothProjectiveCurveThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassSmoothProjectiveCurve",
	Key:  "prop_e1ea24325b23029e",
	Reading: "M need not be algebraically closed: each clause of " +
		"smooth_projective_equation_curve is read at M's own points and over M's own polynomials. " +
		"finite(k) is asked by the predicate, not by the argument. The points with Z = 0 are the " +
		"one point (0 : 1 : 0), where ∂W/∂Z = Y² is one; at the affine points the partials ∂_X = " +
		"−(3x² + a), ∂_Y = 2y have no common zero on the curve, which is WeierstrassPartialsUnit; " +
		"at (0 : 0 : 1), on the curve only when b = 0, ∂_X = −a and a ≠ 0 since 4a³ ≠ 0. The " +
		"cubic is irreducible over every field, y² − (x³ + ax + b) being no square by odd degree " +
		"and Z not dividing it; characteristic 3 is allowed, the discriminant there being a³.",
	Deps: []registry.EntryLike{
		projective_curve.SmoothProjectiveEquationCurveDef,
		projective_curve.ProjectiveGenusDef,
		projective_curve.PlaneCurveHilbertFunction,
		homogeneous_polynomial.HomogeneousPolynomialDef,
		projective_curve.ProjectiveEquationPointsDef,
		WeierstrassRingDomain,
		WeierstrassPartialsUnit,
		polynomial_algebra.PolynomialAlgebraVarDef,
		polynomial_algebra.PolynomialAlgebraConstDef,
	},
	Build: family.Card(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀a b:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"a ∈ k",
			"b ∈ k",
			"M.add(M.one, M.one) ≠ M.zero",
			"M.add(M.mul(monoid_pow(M.add, M.zero, M.one, 4), M.mul(a, M.mul(a, a))), " +
				"    M.mul(monoid_pow(M.add, M.zero, M.one, 27), M.mul(b, b))) ≠ " +
				"M.zero",
		},
		Conclusion: "smooth_projective_equation_curve(M, k, 2, {«projectiveWeierstrassCubic»}) ∧ " +
			"projective_equation_genus(field_ring(M), k, 2, {«projectiveWeierstrassCubic»}) = 1",
		Abbrev: Abbrev{
			{Name: "projectiveCoefficients", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "projectivePlane", Text: "polynomial_algebra_ring(«projectiveCoefficients», " +
				"    {i:num | i ≤ 2})"},
			{Name: "planeVar", Text: "polynomial_algebra_var(«projectiveCoefficients»)"},
			{Name: "planeConst", Text: "polynomial_algebra_const(«projectiveCoefficients»)"},
			{Name: "planeX", Text: "«planeVar»(0)"},
			{Name: "planeY", Text: "«planeVar»(1)"},
			{Name: "planeZ", Text: "«planeVar»(2)"},
			{Name: "projectiveWeierstrassCubic", Text: "«projectivePlane».sub( " +
				"    «projectivePlane».mul(«projectivePlane».mul(«planeY», «planeY»), «planeZ»), " +
				"    «projectivePlane».add(«projectivePlane».add( " +
				"            «projectivePlane».mul(«projectivePlane».mul(«planeX», «planeX»), «planeX»), " +
				"            «projectivePlane».mul(«projectivePlane».mul(«planeConst»(a), «planeX»), " +
				"                «projectivePlane».mul(«planeZ», «planeZ»))), " +
				"        «projectivePlane».mul(«planeConst»(b), " +
				"            «projectivePlane».mul(«projectivePlane».mul(«planeZ», «planeZ»), «planeZ»))))"},
		},
	},
		"The cubic is a form of degree three over k. Its ideal over M is prime: Z is no zero "+
			"divisor modulo it, and inverting Z gives the affine Weierstrass ring over M with a "+
			"Laurent variable, a domain (WeierstrassRingDomain). (0 : 1 : 0) is a point. The Hilbert "+
			"function is 3d from d = 3 on (PlaneCurveHilbertFunction at e = 3), so the genus is one "+
			"and e = 3. The gradient is nonzero at every point (WeierstrassPartialsUnit at the affine "+
			"points, the point at infinity by hand), so its span has dimension one, which is n − 1."),
})}
