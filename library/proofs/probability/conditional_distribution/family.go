// family.go — the conditional_distribution family manifest: the
// registry handle every member registers into and the family's shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=conditional_distribution.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/conditional_distribution go test -run TestRecordFamilyCNF ./library/integrity/gates/

package conditional_distribution

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/probability/conditional_independence"
	_ "github.com/euc-ai/xugo/library/proofs/probability/probability_kernel"
	_ "github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed conditional_distribution.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/conditional_distribution", familyCNF).WithCoerceDomain(
	RealDomain)
