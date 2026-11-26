// family.go — the machine_word family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=machine_word.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=words/machine_word go test -run TestRecordFamilyCNF ./library/integrity/gates/

package machine_word

import (
	// nat_parity mints constants this family's definitions spell, and no
	// other import reaches it: the import initializes those mints
	// before the definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed machine_word.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates words/machine_word/machine_word.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`machine_word.<Member>`). The statement vocabulary — the chapter's
// minted constants — is declared in vocab.go, beside the mints.
var family = registry.NewFamily("words/machine_word", familyCNF).WithVocabSpec(vocab)
