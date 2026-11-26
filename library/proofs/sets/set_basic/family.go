// family.go — the set_basic family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var InUnion = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=set_basic.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/set_basic go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records one member's refutes and merges them into the
// family pb; the second drops the keys no member reaches any more.

package set_basic

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed set_basic.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates sets/set_basic/set_basic.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`set_basic.<Member>`).
var family = registry.NewFamily("sets/set_basic", familyCNF).WithVocabSpec(vocab)
