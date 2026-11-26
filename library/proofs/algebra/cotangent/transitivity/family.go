// family.go — the transitivity family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=transitivity.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/transitivity go test -run TestRecordFamilyCNF ./library/integrity/gates/

package transitivity

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed transitivity.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// transitivity/transitivity.cnf.pb from the name's basename, and the
// registered entry prefix is `transitivity.<Member>`.
var family = registry.NewFamily("algebra/cotangent/transitivity", familyCNF)
