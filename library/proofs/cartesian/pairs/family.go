// family.go — the pairs family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var PairEq = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header).
// Mind the two spellings: the per-member selectors take the REGISTERED
// name (`pairs.<Member>`), the family-wide GC takes the family's full
// domain path.
//
//	XUGO_RECORD_FAMILY_CNF=pairs.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=cartesian/pairs go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records one member and merges its keys in (what a
// restructure needs); the second drops keys no member reaches any more.

package pairs

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed pairs.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates cartesian/pairs/pairs.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`pairs.<Member>`).
// The vocabulary is vocab.go's rows; the generated ops accessor hands
// the chapter the same names as handles.
var family = registry.NewFamily("cartesian/pairs", familyCNF).WithVocabSpec(vocab)
