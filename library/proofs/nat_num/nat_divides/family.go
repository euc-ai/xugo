// family.go — the nat_divides family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var DividesMod =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nat_divides.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/nat_divides go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name (registry.ByName is keyed on it; a bare entry
// name reports "not in proof registry"), while CNF_GC takes the
// family's own Name — the whole domain path — and rejects the bare
// basename with "no such family".

package nat_divides

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nat_divides.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates nat_num/nat_divides/nat_divides.cnf.pb from it, and
// the registered entry prefix is the name's last segment
// (`nat_divides.<Member>`).
var family = registry.NewFamily("nat_num/nat_divides", familyCNF).WithVocabSpec(vocab)
