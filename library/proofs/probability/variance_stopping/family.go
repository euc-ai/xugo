// family.go — the variance_stopping family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=variance_stopping.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/variance_stopping go test -run TestRecordFamilyCNF ./library/integrity/gates/

package variance_stopping

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/probability/lindeberg_bound"
	_ "github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed variance_stopping.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/variance_stopping", familyCNF).WithCoerceDomain(
	RealDomain)
