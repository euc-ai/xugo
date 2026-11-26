// family.go — the countability family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=countability.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=topology/countability go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package countability

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed countability.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates topology/countability/countability.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`countability.<Member>`).
// The chapter has no vocabulary of its own: every name its statements
// spell resolves through its mint.
var family = registry.NewFamily("topology/countability", familyCNF)
