// family.go — the free_group family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var AppendCongruence =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=free_group.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/group/free_group go test -run TestRecordFamilyCNF ./library/integrity/gates/

package free_group

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed free_group.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path; the
// registered entry prefix is the name's last segment
// (`free_group.<Member>`).
var family = registry.NewFamily("algebra/group/free_group", familyCNF).WithVocabSpec(vocab)
