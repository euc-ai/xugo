// family.go — the flat_module family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=flat_module.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/flat_module go test -run TestRecordFamilyCNF ./library/integrity/gates/

package flat_module

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed flat_module.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// flat_module/flat_module.cnf.pb from the name's basename, and the
// registered entry prefix is `flat_module.<Member>`.
var family = registry.NewFamily("algebra/module/flat_module", familyCNF)
