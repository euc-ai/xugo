// family.go — the square_zero_classification family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=square_zero_classification.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/square_zero_classification go test -run TestRecordFamilyCNF ./library/integrity/gates/

package square_zero_classification

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed square_zero_classification.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// square_zero_classification/square_zero_classification.cnf.pb from the name's basename, and the
// registered entry prefix is `square_zero_classification.<Member>`.
var family = registry.NewFamily("algebra/cotangent/square_zero_classification", familyCNF)
