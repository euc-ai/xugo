// family.go — the conditional_independence family manifest: the
// registry handle every member registers into and the family's shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=conditional_independence.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/conditional_independence go test -run TestRecordFamilyCNF ./library/integrity/gates/

package conditional_independence

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	_ "github.com/euc-ai/xugo/library/proofs/probability/independence"
	_ "github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed conditional_independence.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/conditional_independence", familyCNF).WithCoerceDomain(
	RealDomain)
