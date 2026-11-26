// family.go — the lindeberg_bound family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=lindeberg_bound.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/lindeberg_bound go test -run TestRecordFamilyCNF ./library/integrity/gates/

package lindeberg_bound

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	_ "github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	_ "github.com/euc-ai/xugo/library/proofs/probability/filtration"
	_ "github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lindeberg_bound.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/lindeberg_bound", familyCNF).WithCoerceDomain(
	RealDomain)
