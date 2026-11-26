// family.go — the int_divides family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var IntGcdSpec = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=int_divides.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=int_num/int_divides go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT spellings and each rejects the other's:
// RECORD_CNF takes the full registered MEMBER name, whose prefix is the
// family name's last segment (registry.ByName is keyed on it), while
// CNF_GC takes the FAMILY name, which is the whole domain path.

package int_divides

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed int_divides.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates int_num/int_divides/int_divides.cnf.pb from it, and
// the registered entry prefix is the name's last segment
// (`int_divides.<Member>`).
//
// The vocabulary is the VocabSpec in vocab.go, whose rows also render
// member bodies' build handles (zz_vocab_gen.go).
var family = registry.NewFamily("int_num/int_divides", familyCNF).WithVocabSpec(vocab)
