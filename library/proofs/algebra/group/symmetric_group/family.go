// family.go — the symmetric_group family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=symmetric_group.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/group/symmetric_group go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package symmetric_group

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed symmetric_group.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// symmetric_group/symmetric_group.cnf.pb from the name's basename. The
// chapter mints its own type and constants and binds no WithInstance
// scope: the group of permutations is this chapter's theorem. Its
// product reads `p * q` through permutation_compose's own notation; the
// other operations are spelled by name.
var family = registry.NewFamily("algebra/group/symmetric_group", familyCNF)
