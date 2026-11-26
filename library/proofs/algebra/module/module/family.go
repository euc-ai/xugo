// family.go — the module family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=module.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/module go test -run TestRecordFamilyCNF ./library/integrity/gates/

package module

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed module.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives module/module.cnf.pb
// from the name's basename, and the registered entry prefix is
// `module.<Member>`.
var family = registry.NewFamily("algebra/module/module", familyCNF)
