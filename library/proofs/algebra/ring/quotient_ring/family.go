// family.go — the quotient_ring family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=quotient_ring.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/quotient_ring go test -run TestRecordFamilyCNF ./library/integrity/gates/

package quotient_ring

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed quotient_ring.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// quotient_ring/quotient_ring.cnf.pb from the name's basename, and the
// registered entry prefix is `quotient_ring.<Member>`.
var family = registry.NewFamily("algebra/ring/quotient_ring", familyCNF)
