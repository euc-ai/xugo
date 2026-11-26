package projective_transfer

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_transfer.cnf.pb
var familyCNF []byte

// The chapter reads projective_curve's table over its binders M (the
// ambient field the curve is given in), k (the constants), n and E (the
// equations); its own entries are written over ι, the ring homomorphism of M
// into the second field N: «carried» carries a polynomial's coefficients
// along ι and «carriedPoint» a point's coordinates; «carriedCoefficients»
// is ι(k) as a ring and «carriedPolynomials» the polynomials over it;
// «forms»(d) and «carriedForms»(d) are the forms of degree d over k and
// over ι(k).
var family = registry.NewFamily("scheme/projective_transfer", familyCNF).WithOuterAbbrev(
	projective_curve.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "carried", Text: "λP:((num → num) → A). λm:(num → num). ι(P(m))"},
	{Name: "carriedPoint", Text: "λx:(num → A). λi:num. ι(x(i))"},
	{Name: "carriedCoefficients", Text: "restrict_ring(field_ring(N), image(ι, k))"},
	{Name: "carriedPolynomials", Text: "polynomial_algebra_ring(«carriedCoefficients», " +
		"    {i:num | i ≤ n})"},
	{Name: "forms", Text: "λd:num. " +
		"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
	{Name: "carriedForms", Text: "λd:num. " +
		"    {Q:(num → num) → B | homogeneous_polynomial(«carriedCoefficients», n, d, Q)}"},
})
