// family.go — the bit_arith family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=bit_arith.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=words/bit_arith go test -run TestRecordFamilyCNF ./library/integrity/gates/

package bit_arith

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed bit_arith.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates words/bit_arith/bit_arith.cnf.pb from it, and the registered
// entry prefix is the name's last segment (`bit_arith.<Member>`). The
// statement vocabulary is the words substrate's, embedded from
// words/machine_word (the definitional home of the minted constants) by
// vocab.go.
var family = registry.NewFamily("words/bit_arith", familyCNF).WithVocabSpec(
	vocab).WithAbbrev(Abbrev{
	{Name: "WindowOpAnd", Text: "(λa:bool.λb:bool. a ∧ b)"},
	{Name: "WindowOpOr", Text: "(λa:bool.λb:bool. a ∨ b)"},
	{Name: "WindowOpNot", Text: "(λa:bool. ¬a)"},
})
