// family.go — the binomial family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars, born wrapped by the generated
// typed surface; they never call InstallCNFCache — the replay harness
// installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=binomial.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/binomial go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package binomial

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed binomial.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates nat_num/binomial/binomial.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`binomial.<Member>`).
var family = registry.NewFamily("nat_num/binomial", familyCNF)
