// family.go — the zariski_cotangent family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=zariski_cotangent.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/zariski_cotangent go test -run TestRecordFamilyCNF ./library/integrity/gates/

package zariski_cotangent

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed zariski_cotangent.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// zariski_cotangent/zariski_cotangent.cnf.pb from the name's basename, and the
// registered entry prefix is `zariski_cotangent.<Member>`.
var family = registry.NewFamily("algebra/ring/zariski_cotangent", familyCNF)
