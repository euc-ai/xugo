// family.go — the real_sequences family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var LimitUnique =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_sequences.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_sequences go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path, and the base name fails `no such family`.

package real_sequences

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_sequences.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_sequences/real_sequences.cnf.pb from it,
// and the registered entry prefix is the name's last segment
// (`real_sequences.<Member>`). The vocabulary (vocab.go) is the
// chapter's statement alphabet, installed into every member's
// ParseScope before its first section.
var family = registry.NewFamily("real/real_sequences", familyCNF).WithVocabSpec(vocab)
