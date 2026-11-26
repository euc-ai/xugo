package plane_model

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed plane_model.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the terms the chapter's
// statements share, written over their binders: the field M, the function
// field K, the constants k, the parameter t, the generator z, the equation F,
// the weight b, a constant field l and a polynomial a over k.
var family = registry.NewFamily("scheme/plane_model", familyCNF).WithAbbrev(Abbrev{
	{Name: "pmRing", Text: "restrict_ring(field_ring(M), K)"},
	{Name: "pmRational", Text: "field_adjoin(M, k, {t})"},
	{Name: "pmPolynomials", Text: "polynomial_image(field_ring(M), k, t)"},
	{Name: "pmInversePolynomials", Text: "polynomial_image(field_ring(M), k, M.inv(t))"},
	{Name: "pmRationalInK", Text: "field_adjoin(restrict_field(M, K), k, {t})"},
	{Name: "pmPolynomialsInK", Text: "polynomial_image(field_ring(restrict_field(M, K)), k, t)"},
	{Name: "pmGenerator", Text: "monoid_pow(M.mul, M.one, M.inv(t), b) * z"},
	{Name: "pmScaled", Text: "λi:num. " +
		"    COND(i ≤ polynomial_degree(F), " +
		"        monoid_pow(M.mul, M.one, M.inv(t), b * (polynomial_degree(F) - i)) * F(i), " +
		"        M.zero)"},
	{Name: "pmChart0", Text: "plane_chart_zero(«pmRing», k, t, z)"},
	{Name: "pmChart1", Text: "plane_chart_one(restrict_field(M, K), k, t, z, b)"},
	{Name: "pmOverlap", Text: "ring_away(«pmRing», «pmChart0», t)"},
	{Name: "pmImage0", Text: "polynomial_image(field_ring(M), «pmPolynomials», z)"},
	{Name: "pmImage1", Text: "polynomial_image(field_ring(M), «pmInversePolynomials», «pmGenerator»)"},
	{Name: "pmPowersZ", Text: "{monoid_pow(M.mul, M.one, z, i) | i:num | i < polynomial_degree(F)}"},
	{Name: "pmPowersW", Text: "{monoid_pow(M.mul, M.one, «pmGenerator», i) | " +
		"    i:num | " +
		"    i < polynomial_degree(F)}"},
	{Name: "pmPoints", Text: "λX:set(A). " +
		"    algebra_points(restrict_ring(field_ring(M), X), restrict_ring(field_ring(M), l), k, λx:A. x)"},
	{Name: "pmCount", Text: "curve_rational_point_count(field_ring(M), " +
		"    k, " +
		"    l, " +
		"    «pmChart0», " +
		"    «pmChart1», " +
		"    «pmOverlap»)"},
	{Name: "pmExtendedField", Text: "restrict_field(M, constant_composite(M, K, l))"},
	{Name: "pmExtendedChart0", Text: "constant_chart(field_ring(M), l, «pmChart0»)"},
	{Name: "pmExtendedChart1", Text: "constant_chart(field_ring(M), l, «pmChart1»)"},
	{Name: "pmExtendedOverlap", Text: "constant_chart(field_ring(M), l, «pmOverlap»)"},
})
