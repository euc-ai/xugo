// family.go — the closure family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=closure.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/closure go test -run TestRecordFamilyCNF ./library/integrity/gates/

package closure

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed closure.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path; the
// registered entry prefix is the name's last segment
// (`closure.<Member>`).
var family = registry.NewFamily("relations/closure", familyCNF).WithVocabSpec(vocab)
