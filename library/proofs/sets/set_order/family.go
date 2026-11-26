// family.go — the set_order family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var SubsetTrans = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=set_order.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/set_order go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Live-records one member's refutes and merges them into the family
// pb. This chapter's members reach their own keys through set_tac's residual
// refutation rather than through any seed's, so the per-member record
// is the one that applies.

package set_order

import (
	_ "embed"

	// set_basic mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed set_order.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates sets/set_order/set_order.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`set_order.<Member>`).
var family = registry.NewFamily("sets/set_order", familyCNF).WithVocabSpec(vocab)
