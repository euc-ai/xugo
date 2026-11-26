// family.go — the yoneda_ext family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=yoneda_ext.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/yoneda_ext go test -run TestRecordFamilyCNF ./library/integrity/gates/

package yoneda_ext

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed yoneda_ext.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// yoneda_ext/yoneda_ext.cnf.pb from the name's basename, and the
// registered entry prefix is `yoneda_ext.<Member>`.
var family = registry.NewFamily("algebra/module/yoneda_ext", familyCNF).WithAbbrev(Abbrev{
	{Name: "freeZero", Text: "free_module_record(R, canonical_resolution_terms(R, M, 0))"},
	{Name: "linearExtension", Text: "free_lift(R.zero, N.add, N.zero, N.smul)"},
	{Name: "ext1", Text: "ext_module(R, M, N, 1).carrier"},
})
