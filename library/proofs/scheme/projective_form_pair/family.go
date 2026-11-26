package projective_form_pair

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_generic_point"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_form_pair.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/projective_form_pair", familyCNF).WithOuterAbbrev(
	projective_generic_point.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "noCommonZero", Text: "∀z:(num → A). " +
		"    z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E) ⇒ " +
		"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, F) ≠ M.zero ∨ " +
		"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, G) ≠ M.zero"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()

// _Polynomial is a polynomial in the variables num with coefficients in A:
// its coefficient at each exponent vector.
type _Polynomial = Fun[Fun[Nat, Nat], A]

// _Fraction is a member of the fraction field of a quotient of the
// polynomials: a class of pairs of cosets.
type _Fraction = Set[Prod[Set[_Polynomial], Set[_Polynomial]]]
