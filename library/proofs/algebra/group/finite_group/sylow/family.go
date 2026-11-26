// family.go — the sylow family manifest: the registry handle every member
// registers into, and the family's ONE shared recorded CNF cache.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=sylow.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/group/finite_group/sylow go test -run TestRecordFamilyCNF ./library/integrity/gates/

package sylow

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed sylow.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/group/finite_group/sylow", familyCNF)
