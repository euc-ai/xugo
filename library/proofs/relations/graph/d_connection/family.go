// family.go — the d_connection family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=d_connection.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/graph/d_connection go test -run TestRecordFamilyCNF ./library/integrity/gates/

package d_connection

import (
	_ "embed"

	_ "github.com/euc-ai/xugo/library/proofs/datatypes/list"
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed d_connection.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("relations/graph/d_connection", familyCNF)
