// family.go — the module_extension family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=module_extension.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/module_extension go test -run TestRecordFamilyCNF ./library/integrity/gates/

package module_extension

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed module_extension.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// module_extension/module_extension.cnf.pb from the name's basename, and the
// registered entry prefix is `module_extension.<Member>`.
var family = registry.NewFamily("algebra/module/module_extension", familyCNF).WithAbbrev(Abbrev{
	{Name: "graph", Text: "twisted_graph(N, group_kernel(M.zero, F.carrier, ε))"},
	{Name: "extension", Text: "module_extension_graph(F, M, ε, N)"},
	{Name: "lift", Text: "module_extension_lift(R, F, ε, E)"},
	{Name: "extract", Text: "extract_syzygy_map(F, M, ε, N, E)"},
})
