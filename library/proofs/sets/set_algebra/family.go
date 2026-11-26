// family.go — the set_algebra family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars (`var UnionComm = family.Add(...)`); they
// never call InstallCNFCache — the replay harness installs familyCNF
// env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=set_algebra.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/set_algebra go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records ONE member and merges its keys in, and takes
// the FULL registered name. The second re-records the family's union
// from scratch and takes `Family.Name` — the whole domain path — and
// rejects the bare basename with `no such family`. This chapter's
// members reach their keys through set_tac's residual refutation rather
// than through any seed's, so the per-member record is the one that
// applies; there is no seed union to pre-cover from.

package set_algebra

import (
	_ "embed"

	// set_basic mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed set_algebra.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates sets/set_algebra/set_algebra.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`set_algebra.<Member>`).
var family = registry.NewFamily("sets/set_algebra", familyCNF).WithVocabSpec(vocab)
