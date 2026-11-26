// family.go — the nat_product family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars; they never call InstallCNFCache — the
// replay harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nat_product.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=iterate/nat/nat_product go test -run TestRecordFamilyCNF ./library/integrity/gates/

package nat_product

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nat_product.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("iterate/nat/nat_product", familyCNF)
