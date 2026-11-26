// family.go — the real_pow family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var OnePow = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_pow.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_pow go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name (registry.ByName is keyed on it; a bare entry
// name reports "not in proof registry"), while CNF_GC takes the
// family's own Name — the whole domain path — and rejects the bare
// basename with "no such family".

package real_pow

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_pow.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// real_pow/real_pow.cnf.pb from the name's basename. The vocabulary
// (vocab.go) is the chapter's statement alphabet, installed into every
// member's ParseScope before its first section.
var family = registry.NewFamily("real/real_pow", familyCNF).WithVocabSpec(vocab)
