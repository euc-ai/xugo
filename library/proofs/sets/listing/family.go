// family.go — the listing family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// The dependency direction is one-way: `listing` imports `finite_set`
// and `cardinality` for the entries it cites, and `datatypes/list` for the
// lists themselves, so none of those may import back. That is why this
// package's blank import lives in `sets/sets.go` and not in the parent.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=<listing.MEMBER> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/listing go test -run TestRecordFamilyCNF ./library/integrity/gates/

package listing

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed listing.cnf.pb
var familyCNF []byte

// The registered name is the full path; `registry.Family` takes
// `path.Base` of it for the member prefix, so members read
// `listing.X`.
var family = registry.NewFamily("sets/listing", familyCNF).WithVocabSpec(vocab)
