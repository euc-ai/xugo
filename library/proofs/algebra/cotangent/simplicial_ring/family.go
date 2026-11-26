// family.go — the simplicial_ring family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=simplicial_ring.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/simplicial_ring go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simplicial_ring

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simplicial_ring.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// simplicial_ring/simplicial_ring.cnf.pb from the name's basename, and the
// registered entry prefix is `simplicial_ring.<Member>`.
var family = registry.NewFamily("algebra/cotangent/simplicial_ring", familyCNF)
