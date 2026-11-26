// family.go — the polynomial_quotient family manifest: the registry
// handle every member registers into, and the family's ONE shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=polynomial_quotient.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/field/polynomial_quotient go test -run TestRecordFamilyCNF ./library/integrity/gates/

package polynomial_quotient

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_quotient.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// polynomial_quotient/polynomial_quotient.cnf.pb from the name's
// basename, and the registered entry prefix is
// `polynomial_quotient.<Member>`.
var family = registry.NewFamily("algebra/field/polynomial_quotient", familyCNF).WithOuterAbbrev(
	polynomial_division.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "fieldPolynomialRing", Text: "polynomial_ring(field_ring(F))"},
	{Name: "idealOfP", Text: "ideal_span(«fieldPolynomialRing», {p})"},
	{Name: "rootField", Text: "ideal_quotient_field(«fieldPolynomialRing», «idealOfP»)"},
	{Name: "constantClass", Text: "λJ:set(num → A). λa:A. " +
		"    ideal_quotient_projection(«fieldPolynomialRing», J, a • basis_vector(0))"},
	{Name: "variableClass", Text: "ideal_quotient_projection(«fieldPolynomialRing», " +
		"    «idealOfP», " +
		"    basis_vector(1))"},
	{Name: "constantClasses", Text: "image(«constantClass»(«idealOfP»), F.carrier)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
