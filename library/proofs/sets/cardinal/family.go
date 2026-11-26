// family.go — the cardinal family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var CardLeRefl =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=cardinal.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/cardinal go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path, and the base name fails `no such family`.

package cardinal

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cardinal.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates sets/cardinal/cardinal.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`cardinal.<Member>`). The chapter's statement vocabulary is the
// VocabSpec in vocab.go.
var family = registry.NewFamily("sets/cardinal", familyCNF).
	WithVocabSpec(vocab)
