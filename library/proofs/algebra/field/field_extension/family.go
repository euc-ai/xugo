// family.go — the field_extension family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=field_extension.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/field/field_extension go test -run TestRecordFamilyCNF ./library/integrity/gates/

package field_extension

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed field_extension.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// field_extension/field_extension.cnf.pb from the name's basename, and
// the registered entry prefix is `field_extension.<Member>`.
var family = registry.NewFamily("algebra/field/field_extension", familyCNF).WithAbbrev(Abbrev{
	{Name: "scalarsOn", Text: "restrict_ring(field_ring(L))"},
	{Name: "vectorsOn", Text: "restrict_module(regular_module(field_ring(L)))"},
	{Name: "towerProducts", Text: "{b * c | b:A, c:A | b ∈ B ∧ c ∈ C}"},
})
