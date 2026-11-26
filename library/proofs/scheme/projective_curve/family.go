package projective_curve

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_curve.cnf.pb
var familyCNF []byte

// The chapter's abbreviations are written over the binders M (the ambient
// field), k (the constants), K (the generic field), n, E (the equations),
// x (the generic point) and r (the degree of the form a chart divides by).
// The set-builder «chart» is guarded by y ∈ K: over the whole type it would
// hold every point off M's carrier, where M's operations are unconstrained
// and y * H(x)^a = P(x) can hold with P = 0.
var family = registry.NewFamily("scheme/projective_curve", familyCNF).WithAbbrev(Abbrev{
	{Name: "hilbertCoefficients", Text: "restrict_ring(field_ring(M), k)"},
	{Name: "polynomials", Text: "polynomial_algebra_ring(«hilbertCoefficients», {i:num | i ≤ n})"},
	{Name: "genericPoint", Text: "λy:(num → A). " +
		"    y ∈ projective_equation_points(field_ring(M), k, K, n, E) ∧ " +
		"    field_adjoin(M, k, {y(i) | i:num | i ≤ n}) = K ∧ " +
		"    (∀P:((num → num) → A). " +
		"        (∃d:num. homogeneous_polynomial(restrict_ring(field_ring(M), k), n, d, P)) ⇒ " +
		"        (polynomial_algebra_eval(restrict_ring(field_ring(M), k), " +
		"                field_ring(M), " +
		"                (λa:A. a), " +
		"                y, " +
		"                P) = " +
		"            M.zero ⇔ " +
		"            P ∈ " +
		"            ideal_span( " +
		"                polynomial_algebra_ring(restrict_ring(field_ring(M), k), {i:num | i ≤ n}), E)))"},
	{Name: "at", Text: "λP:((num → num) → A). " +
		"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), x, P)"},
	{Name: "valueAt", Text: "λw:(num → A). λP:((num → num) → A). " +
		"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), w, P)"},
	{Name: "chart", Text: "λH:((num → num) → A). " +
		"    {y:A | " +
		"        y ∈ K ∧ " +
		"        ∃a:num. ∃P:((num → num) → A). " +
		"            homogeneous_polynomial(«hilbertCoefficients», n, r * a, P) ∧ " +
		"            y * monoid_pow(M.mul, M.one, «at»(H), a) = «at»(P)}"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
