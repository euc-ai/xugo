// family.go — the monoidal family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var Clauses =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=monoidal.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=iterate/monoidal go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the full
// registered entry name (registry.ByName is keyed on it; a bare entry
// name reports "not in proof registry"), while CNF_GC takes the
// family's own Name — the whole domain path — and rejects the bare
// basename with "no such family".

package monoidal

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed monoidal.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// monoidal/monoidal.cnf.pb from the name's basename. The vocabulary is
// vocab.go's rows.
var family = registry.NewFamily("iterate/monoidal", familyCNF).WithVocabSpec(
	vocab).WithAbbrev(Abbrev{
	{Name: "emptyNumbers", Text: "empty_set⟨A:num⟩"},
	{Name: "acceptedHalf", Text: "{x | x ∈ s ∧ P(x)}"},
	{Name: "emptySecond", Text: "empty_set⟨A:var:C⟩"},
})
