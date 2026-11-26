// family.go — the bitwise_algebra family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=bitwise_algebra.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=words/bitwise_algebra go test -run TestRecordFamilyCNF ./library/integrity/gates/

package bitwise_algebra

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed bitwise_algebra.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates words/bitwise_algebra/bitwise_algebra.cnf.pb from it, and the registered
// entry prefix is the name's last segment (`bitwise_algebra.<Member>`). The
// statement vocabulary is the words substrate's, embedded from
// words/machine_word (the definitional home of the minted constants) by
// vocab.go.
var family = registry.NewFamily("words/bitwise_algebra", familyCNF).WithVocabSpec(vocab)
