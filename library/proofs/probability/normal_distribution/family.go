// family.go — the normal_distribution family manifest: the registry
// handle every member registers into and the family's shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=normal_distribution.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=probability/normal_distribution go test -run TestRecordFamilyCNF ./library/integrity/gates/

package normal_distribution

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/density_measure"
	_ "github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	_ "github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed normal_distribution.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/normal_distribution", familyCNF).WithCoerceDomain(
	RealDomain)
