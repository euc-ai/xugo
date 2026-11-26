// family.go — the nat_sum family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars, born wrapped by the generated
// typed surface (`var Union = unionThm{family.Add(...)}`); they never
// call InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nat_sum.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=iterate/nat/nat_sum go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package nat_sum

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nat_sum.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// nat_sum/nat_sum.cnf.pb from the name's basename. No chapter
// vocabulary (the real_sum precedent): `nat_sum`, `monoidal_op`, `neutral_elem`
// and ℕ's `+` resolve through the text parser's definitional-layer
// fallback.
var family = registry.NewFamily("iterate/nat/nat_sum", familyCNF)
