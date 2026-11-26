// family.go — the field family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=field.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/field/field go test -run TestRecordFamilyCNF ./library/integrity/gates/

package field

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed field.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives field/field.cnf.pb
// from the name's basename, and the registered entry prefix is
// `field.<Member>`.
var family = registry.NewFamily("algebra/field/field", familyCNF)
