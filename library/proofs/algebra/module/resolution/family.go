// family.go — the resolution family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=resolution.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/resolution go test -run TestRecordFamilyCNF ./library/integrity/gates/

package resolution

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed resolution.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// resolution/resolution.cnf.pb from the name's basename, and the
// registered entry prefix is `resolution.<Member>`.
var family = registry.NewFamily("algebra/module/resolution", familyCNF)
