// family.go — the resolution_comparison family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=resolution_comparison.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/resolution_comparison go test -run TestRecordFamilyCNF ./library/integrity/gates/

package resolution_comparison

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed resolution_comparison.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// resolution_comparison/resolution_comparison.cnf.pb from the name's basename, and the
// registered entry prefix is `resolution_comparison.<Member>`.
var family = registry.NewFamily(
	"algebra/cotangent/resolution_comparison", familyCNF).WithAbbrev(Abbrev{
	{Name: "identity", Text: "λn:num. λu:U. u"},
})
