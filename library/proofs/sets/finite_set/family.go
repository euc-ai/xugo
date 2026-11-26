// family.go — the finite_set family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// The chapter sets/cardinality imports this package for
// the entries it cites, so nothing here may import it back; its blank import
// lives in sets/sets.go.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=<finite_set.MEMBER> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/finite_set go test -run TestRecordFamilyCNF ./library/integrity/gates/

package finite_set

import (
	_ "embed"

	// set_product mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_product"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed finite_set.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("sets/finite_set", familyCNF).WithVocabSpec(
	vocab).WithAbbrev(Abbrev{
	{Name: "noFamily", Text: "∅⟨A:set(A)⟩"},
})
