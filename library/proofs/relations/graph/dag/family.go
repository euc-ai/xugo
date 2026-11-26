// family.go — the dag family manifest: the registry handle every member
// registers into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=dag.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/graph/dag go test -run TestRecordFamilyCNF ./library/integrity/gates/

package dag

import (
	_ "embed"

	_ "github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/option"
	_ "github.com/euc-ai/xugo/library/proofs/relations/closure"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed dag.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("relations/graph/dag", familyCNF)
