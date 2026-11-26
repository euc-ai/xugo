// family.go — the int_product family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars; they never call InstallCNFCache — the
// replay harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=int_product.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=iterate/int/int_product go test -run TestRecordFamilyCNF ./library/integrity/gates/

package int_product

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed int_product.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("iterate/int/int_product", familyCNF)
