// family.go — the cotangent_complex family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=cotangent_complex.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/cotangent_complex go test -run TestRecordFamilyCNF ./library/integrity/gates/

package cotangent_complex

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cotangent_complex.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// cotangent_complex/cotangent_complex.cnf.pb from the name's basename, and the
// registered entry prefix is `cotangent_complex.<Member>`.
var family = registry.NewFamily("algebra/cotangent/cotangent_complex", familyCNF)
