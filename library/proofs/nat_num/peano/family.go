// family.go — the peano family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var indSucDef = family.Define(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=peano.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/peano go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records one member's refutes and merges them into the
// family pb; the second drops the keys no member reaches any more.

package peano

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed peano.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates nat_num/peano/peano.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`peano.<Member>`).
var family = registry.NewFamily("nat_num/peano", familyCNF).WithVocabSpec(vocab)
