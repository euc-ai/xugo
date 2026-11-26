// family.go — the real_exp_log family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_exp_log.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_exp_log go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path.

package real_exp_log

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_exp_log.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_exp_log/real_exp_log.cnf.pb from it, and
// the registered entry prefix is the name's last segment
// (`real_exp_log.<Member>`). The vocabulary (vocab.go) declares the
// chapter's numeric domain and is installed into every member's
// ParseScope. The chapter mints two constants, real_exp and real_log;
// every other name a statement spells resolves through its mint.
var family = registry.NewFamily("real/real_exp_log", familyCNF).WithVocabSpec(vocab)
