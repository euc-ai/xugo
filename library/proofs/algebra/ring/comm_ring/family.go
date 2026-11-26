// family.go — the comm_ring family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=comm_ring.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/comm_ring go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name, CNF_GC the family's own Name — the whole
// domain path.

package comm_ring

import (
	_ "embed"

	// monoidal mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/iterate/monoidal"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed comm_ring.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// comm_ring/comm_ring.cnf.pb from the name's basename. The vocabulary
// (vocab.go) declares the fold mechanism's two names.
var family = registry.NewFamily("algebra/ring/comm_ring", familyCNF).WithVocabSpec(vocab)
