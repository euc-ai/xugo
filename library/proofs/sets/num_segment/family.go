// family.go — the num_segment family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=<num_segment.MEMBER> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/num_segment go test -run TestRecordFamilyCNF ./library/integrity/gates/

package num_segment

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed num_segment.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("sets/num_segment", familyCNF).WithVocabSpec(vocab)
