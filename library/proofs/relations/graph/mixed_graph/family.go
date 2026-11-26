// family.go — the mixed_graph family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=mixed_graph.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/graph/mixed_graph go test -run TestRecordFamilyCNF ./library/integrity/gates/

package mixed_graph

import (
	_ "embed"

	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed mixed_graph.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("relations/graph/mixed_graph", familyCNF)
