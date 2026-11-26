// family.go — the free_algebra family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=free_algebra.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/polynomial/free_algebra go test -run TestRecordFamilyCNF ./library/integrity/gates/

package free_algebra

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed free_algebra.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// free_algebra/free_algebra.cnf.pb from the name's basename, and the
// registered entry prefix is `free_algebra.<Member>`.
var family = registry.NewFamily(
	"algebra/ring/polynomial/free_algebra", familyCNF).WithAbbrev(Abbrev{
	{Name: "corpusPolynomials", Text: "{p:(num → A) | polynomial_over(R.zero, R.carrier, p)}"},
})
