// family.go — the real_completeness family manifest. Curates the tower's
// completeness spur — the cross-layer chain that carries the
// Archimedean property from nadd all the way up to the Dedekind
// completeness of the reals.
//
// Each entry's Key is its statement's own normalized key.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=<real_completeness.MEMBER> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/tower/real_completeness go test -run TestRecordFamilyCNF ./library/integrity/gates/

package real_completeness

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_completeness.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("real/tower/real_completeness", familyCNF).WithVocabSpec(vocab)
