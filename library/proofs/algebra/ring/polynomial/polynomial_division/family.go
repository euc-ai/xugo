// family.go — the polynomial_division family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=polynomial_division.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/polynomial/polynomial_division go test -run TestRecordFamilyCNF ./library/integrity/gates/

package polynomial_division

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_division.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// polynomial_division/polynomial_division.cnf.pb from the name's basename,
// and the registered entry prefix is `polynomial_division.<Member>`.
var family = registry.NewFamily(
	"algebra/ring/polynomial/polynomial_division", familyCNF).WithOuterAbbrev(
	polynomial.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "fieldPolynomials", Text: "{p:(num → A) | polynomial_over(F.carrier, p)}"},
	{Name: "division", Text: "λc:set(A). λf:(num → A). λg:(num → A). λq:(num → A). λr:(num → A). " +
		"    polynomial_over(c, q) ∧ " +
		"    polynomial_over(c, r) ∧ " +
		"    vec⟨polynomial_degree(g)⟩(r) ∧ " +
		"    f = polynomial_mul(g, q) + r"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
