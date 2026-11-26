// family.go — the quasi_category family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=quasi_category.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/quasi_category go test -run TestRecordFamilyCNF ./library/integrity/gates/

package quasi_category

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed quasi_category.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// quasi_category/quasi_category.cnf.pb from the name's basename, and the registered entry
// prefix is `quasi_category.<Member>`.
var family = registry.NewFamily("simplicial/quasi_category", familyCNF).WithAbbrev(Abbrev{
	{Name: "s", Text: "λn:num. nerve_degeneracy(C)"},
	{Name: "H", Text: "homotopy_category(nerve(C))"},
})
