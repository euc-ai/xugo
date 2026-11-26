// family.go — the nat_prime family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var EuclidLemma = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nat_prime.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/nat_prime go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT spellings and each rejects the other's:
// RECORD_CNF takes the full registered MEMBER name, whose prefix is the
// family name's last segment (registry.ByName is keyed on it), while
// CNF_GC takes the FAMILY name, which is the whole domain path.

package nat_prime

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nat_prime.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates nat_num/nat_prime/nat_prime.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`nat_prime.<Member>`).
var family = registry.NewFamily("nat_num/nat_prime", familyCNF).WithVocabSpec(vocab)
