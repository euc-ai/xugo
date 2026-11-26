// family.go — the graphical_markov family manifest: the registry handle every member registers
// into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=graphical_markov.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/graphical_markov go test -run TestRecordFamilyCNF ./library/integrity/gates/

package graphical_markov

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/causal/intervention"
	_ "github.com/euc-ai/xugo/library/proofs/probability/conditional_independence"
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed graphical_markov.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("causal/graphical_markov", familyCNF).WithCoerceDomain(RealDomain)
