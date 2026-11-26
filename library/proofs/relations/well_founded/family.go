// family.go — the well_founded family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded
// CNF cache. Proof files carry entry vars
// (`var Induction = family.Add(...)`); they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header).
// Mind the two spellings: the per-member selectors take the REGISTERED
// name (`well_founded.<Member>`), the family-wide GC takes the family's
// full domain path (`relations/well_founded`).
//
//	XUGO_RECORD_FAMILY_CNF=well_founded.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/well_founded go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records one member and merges its keys in (what a
// restructure needs); the second drops keys no member reaches any more.

package well_founded

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed well_founded.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates relations/well_founded/well_founded.cnf.pb from it,
// and the registered entry prefix is the name's last segment
// (`well_founded.<Member>`). The
// vocabulary (vocab.go) is the chapter's statement alphabet, installed
// into every member's ParseScope before its first section.
var family = registry.NewFamily("relations/well_founded", familyCNF).WithVocabSpec(vocab)
