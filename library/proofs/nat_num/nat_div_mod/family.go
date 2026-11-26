// family.go — the nat_div_mod family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var DivMult = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Define.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nat_div_mod.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/nat_div_mod go test -run TestRecordFamilyCNF ./library/integrity/gates/

package nat_div_mod

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nat_div_mod.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates nat_num/nat_div_mod/nat_div_mod.cnf.pb from it, and
// the registered entry prefix is the name's last segment
// (`nat_div_mod.<Member>`). The vocabulary (vocab.go) is the chapter's
// statement alphabet, installed into every member's ParseScope before
// its first section.
var family = registry.NewFamily("nat_num/nat_div_mod", familyCNF).WithVocabSpec(vocab)
