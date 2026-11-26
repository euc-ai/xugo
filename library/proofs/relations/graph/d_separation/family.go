// family.go — the d_separation family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=d_separation.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/graph/d_separation go test -run TestRecordFamilyCNF ./library/integrity/gates/

package d_separation

import (
	_ "embed"

	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed d_separation.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("relations/graph/d_separation", familyCNF)
