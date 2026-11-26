// family.go — the intervention family manifest: the registry handle every member registers
// into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=intervention.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/intervention go test -run TestRecordFamilyCNF ./library/integrity/gates/

package intervention

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	_ "github.com/euc-ai/xugo/library/proofs/probability/independence"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed intervention.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("causal/intervention", familyCNF).WithCoerceDomain(RealDomain)
