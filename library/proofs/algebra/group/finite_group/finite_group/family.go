// family.go — the finite_group family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars; they never call InstallCNFCache — the
// replay harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=finite_group.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/group/finite_group/finite_group go test -run TestRecordFamilyCNF ./library/integrity/gates/

package finite_group

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed finite_group.cnf.pb
var familyCNF []byte

// family is the family handle. The chapter's statements spell only minted
// constants, so it declares no vocabulary.
var family = registry.NewFamily("algebra/group/finite_group/finite_group", familyCNF)
