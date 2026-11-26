// family.go — the group family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=group.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/group/group go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package group

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed group.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives group/group.cnf.pb
// from the name's basename. The chapter's statements spell only minted
// constants, so it declares no vocabulary.
var family = registry.NewFamily("algebra/group/group", familyCNF)
