// family.go — the submodule family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=submodule.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/submodule go test -run TestRecordFamilyCNF ./library/integrity/gates/

package submodule

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed submodule.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// submodule/submodule.cnf.pb from the name's basename, and the
// registered entry prefix is `submodule.<Member>`.
var family = registry.NewFamily("algebra/module/submodule", familyCNF)
