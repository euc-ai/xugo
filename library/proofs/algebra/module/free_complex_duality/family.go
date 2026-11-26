// family.go — the free_complex_duality family manifest: the registry
// handle every member registers into, and the family's ONE shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=free_complex_duality.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/free_complex_duality go test -run TestRecordFamilyCNF ./library/integrity/gates/

package free_complex_duality

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed free_complex_duality.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// free_complex_duality/free_complex_duality.cnf.pb from the name's
// basename, and the registered entry prefix is
// `free_complex_duality.<Member>`.
var family = registry.NewFamily("algebra/module/free_complex_duality", familyCNF)
