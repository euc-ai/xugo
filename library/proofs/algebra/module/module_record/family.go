// family.go — the module_record family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=module_record.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/module_record go test -run TestRecordFamilyCNF ./library/integrity/gates/

package module_record

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed module_record.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// module_record/module_record.cnf.pb from the name's basename, and the
// registered entry prefix is `module_record.<Member>`.
var family = registry.NewFamily("algebra/module/module_record", familyCNF)
