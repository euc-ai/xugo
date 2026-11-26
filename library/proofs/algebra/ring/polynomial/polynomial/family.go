// family.go — the polynomial family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=polynomial.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/polynomial/polynomial go test -run TestRecordFamilyCNF ./library/integrity/gates/

package polynomial

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// polynomial/polynomial.cnf.pb from the name's basename, and the
// registered entry prefix is `polynomial.<Member>`. The chapter's
// abbreviations name the polynomials over a ring's carrier, the numerals
// n · one of a ring, and «natConv», the product of sequences of naturals
// as power series.
var family = registry.NewFamily("algebra/ring/polynomial/polynomial", familyCNF).WithAbbrev(Abbrev{
	{Name: "polynomialRingCarrier", Text: "{p:(num → A) | polynomial_over(R.carrier, p)}"},
	{Name: "numeral", Text: "λn:num. monoid_pow(R.add, R.zero, R.one, n)"},
	{Name: "natConv", Text: "polynomial_mul(λi:num. λj:num. i + j, 0, λi:num. λj:num. i * j)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
