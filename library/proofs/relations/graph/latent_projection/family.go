// family.go — the latent_projection family manifest: the registry
// handle every member registers into and the family's shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=latent_projection.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/graph/latent_projection go test -run TestRecordFamilyCNF ./library/integrity/gates/

package latent_projection

import (
	_ "embed"

	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/mixed_graph"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed latent_projection.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("relations/graph/latent_projection", familyCNF)
