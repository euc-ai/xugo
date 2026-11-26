// family.go — the word_bits family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=word_bits.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=words/word_bits go test -run TestRecordFamilyCNF ./library/integrity/gates/

package word_bits

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed word_bits.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates words/word_bits/word_bits.cnf.pb from it, and the registered
// entry prefix is the name's last segment (`word_bits.<Member>`). The
// statement vocabulary is the words substrate's, embedded from
// words/machine_word (the definitional home of the minted constants) by
// vocab.go.
var family = registry.NewFamily("words/word_bits", familyCNF).WithVocabSpec(vocab)
