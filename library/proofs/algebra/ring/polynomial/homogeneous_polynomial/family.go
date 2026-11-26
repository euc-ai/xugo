package homogeneous_polynomial

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed homogeneous_polynomial.cnf.pb
var familyCNF []byte

// The chapter's abbreviations are written over the binders M (a field), k
// (a subfield of it, the coefficients), n (the variables are those up to n)
// and x (a point of M, its coordinates indexed by num).
var family = registry.NewFamily(
	"algebra/ring/polynomial/homogeneous_polynomial", familyCNF).WithAbbrev(Abbrev{
	{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
	{Name: "polynomials", Text: "polynomial_algebra_ring(«scalars», {i:num | i ≤ n})"},
	{Name: "at", Text: "λP:((num → num) → A). " +
		"    polynomial_algebra_eval(«scalars», field_ring(M), (λa:A. a), x, P)"},
	{Name: "valueAt", Text: "λw:(num → A). λP:((num → num) → A). " +
		"    polynomial_algebra_eval(«scalars», field_ring(M), (λa:A. a), w, P)"},
})
