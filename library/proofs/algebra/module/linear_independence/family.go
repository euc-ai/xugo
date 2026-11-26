// family.go — the linear_independence family manifest: the registry
// handle every member registers into, and the family's ONE shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=linear_independence.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/linear_independence go test -run TestRecordFamilyCNF ./library/integrity/gates/

package linear_independence

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed linear_independence.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// linear_independence/linear_independence.cnf.pb from the name's
// basename, and the registered entry prefix is
// `linear_independence.<Member>`.
var family = registry.NewFamily("algebra/module/linear_independence", familyCNF)
