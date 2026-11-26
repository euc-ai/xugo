package projective_affine_piece

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_affine_piece.cnf.pb
var familyCNF []byte

// The chapter's abbreviations are written over the binders M (the ambient
// field), k (the constants), n (the last coordinate), x and j (the point and
// its coordinate that does not vanish), H (an ideal of the affine piece) and
// φ (a point of the piece in M).
var family = registry.NewFamily("scheme/projective_affine_piece", familyCNF).WithOuterAbbrev(
	projective_curve.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "piece", Text: "{polynomial_algebra_eval(«hilbertCoefficients», " +
		"        field_ring(M), " +
		"        (λa:A. a), " +
		"        (λi:num. x(i) * M.inv(x(j))), " +
		"        P) | " +
		"    P:((num → num) → A) | " +
		"    P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})}"},
	{Name: "affine", Text: "λP:((num → num) → A). " +
		"    polynomial_algebra_eval(«hilbertCoefficients», " +
		"        field_ring(M), " +
		"        (λa:A. a), " +
		"        (λi:num. x(i) * M.inv(x(j))), " +
		"        P)"},
	{Name: "affineValues", Text: "λd:num. " +
		"    image(«affine», " +
		"        {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
	{Name: "quotient", Text: "quotient_module( " +
		"    restrict_module(regular_module(field_ring(M)), «piece»), H)"},
	{Name: "classes", Text: "λe:num. image(coset_map(M.add, H), «affineValues»(e))"},
	{Name: "φPoint", Text: "λl:num. φ(x(l) * M.inv(x(j)))"},
	{Name: "gradient", Text: "λy:(num → A). λP:((num → num) → A). λi:num. " +
		"    COND(i ≤ n, " +
		"        polynomial_algebra_eval(«hilbertCoefficients», " +
		"            field_ring(M), " +
		"            (λa:A. a), " +
		"            y, " +
		"            polynomial_algebra_partial(«hilbertCoefficients», i, P)), " +
		"        M.zero)"},
	{Name: "gradients", Text: "{«gradient»(«φPoint», R) | " +
		"    R:((num → num) → A) | " +
		"    R ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ " +
		"    polynomial_algebra_eval(«hilbertCoefficients», " +
		"        field_ring(M), " +
		"        (λa:A. a), " +
		"        (λi:num. x(i) * M.inv(x(j))), " +
		"        R) = " +
		"    M.zero}"},
	{Name: "vectors", Text: "free_module_record(field_ring(M), {i:num | i ≤ n})"},
})
