// family.go — the polynomial_roots family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=polynomial_roots.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/polynomial/polynomial_roots go test -run TestRecordFamilyCNF ./library/integrity/gates/

package polynomial_roots

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_roots.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// polynomial_roots/polynomial_roots.cnf.pb from the name's basename, and the
// registered entry prefix is `polynomial_roots.<Member>`.
var family = registry.NewFamily(
	"algebra/ring/polynomial/polynomial_roots", familyCNF).WithAbbrev(Abbrev{
	{Name: "linear", Text: "λa:A. basis_vector(1) - a • basis_vector(0)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
