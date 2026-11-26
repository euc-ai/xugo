// family.go — the equivalence family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded
// CNF cache.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=equivalence.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/equivalence go test -run TestRecordFamilyCNF ./library/integrity/gates/

package equivalence

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed equivalence.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path; the
// registered entry prefix is the name's last segment
// (`equivalence.<Member>`).
var family = registry.NewFamily("relations/equivalence", familyCNF).WithVocabSpec(vocab)
