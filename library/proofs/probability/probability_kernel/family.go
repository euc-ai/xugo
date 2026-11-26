// family.go — the probability_kernel family manifest: the registry
// handle every member registers into and the family's shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=probability_kernel.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/probability_kernel go test -run TestRecordFamilyCNF ./library/integrity/gates/

package probability_kernel

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/product_measure"
	_ "github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed probability_kernel.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/probability_kernel", familyCNF).WithCoerceDomain(
	RealDomain)
