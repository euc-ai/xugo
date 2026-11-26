// family.go — the partial_derivative family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=partial_derivative.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/partial_derivative go test -run TestRecordFamilyCNF ./library/integrity/gates/

package partial_derivative

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed partial_derivative.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// partial_derivative/partial_derivative.cnf.pb from the name's basename, and the
// registered entry prefix is `partial_derivative.<Member>`.
var family = registry.NewFamily("algebra/ring/partial_derivative", familyCNF)
