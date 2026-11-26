// family.go — the functions family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var ComposeAssoc =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header).
// Mind the two spellings: the per-member selectors take the REGISTERED
// name (`functions.<Member>`), the family-wide GC takes the family's
// full domain path.
//
//	XUGO_RECORD_FAMILY_CNF=functions.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/functions go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records one member and merges its keys in (what a
// restructure needs); the second drops keys no member reaches any more.
//
// Only the members that REFUTE have entries: unfolding a definition
// records no CNF key, so the combinators contribute nothing to the blob
// and the set-driver members contribute one apiece.

package functions

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed functions.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates sets/functions/functions.cnf.pb from it, and the
// registered entry prefix is the name's last segment
// (`functions.<Member>`).
// The chapter's statement vocabulary is the VocabSpec in vocab.go.
var family = registry.NewFamily("sets/functions", familyCNF).
	WithVocabSpec(vocab)
