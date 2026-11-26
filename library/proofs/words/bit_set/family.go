// family.go — the bit_set family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=bit_set.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=words/bit_set go test -run TestRecordFamilyCNF ./library/integrity/gates/

package bit_set

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed bit_set.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates words/bit_set/bit_set.cnf.pb from it, and the registered
// entry prefix is the name's last segment (`bit_set.<Member>`). The
// statement vocabulary is the words substrate's, embedded from
// words/machine_word (the definitional home of the minted constants) by
// vocab.go.
var family = registry.NewFamily("words/bit_set", familyCNF).WithVocabSpec(vocab)
