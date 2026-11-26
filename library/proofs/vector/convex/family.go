// family.go — the convex family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=convex.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/convex go test -run TestRecordFamilyCNF ./library/integrity/gates/

package convex

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed convex.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// convex/convex.cnf.pb from the name's basename, and the registered
// entry prefix is `convex.<Member>`.
// The chapter works at ℝ: the module chapters' derived operations read
// the real ring's components, and the instance theorem binds them
// (`add ↦ real_add`, `zero ↦ &0`, …) so that a statement here spells
// `c • x + d • y` and means `vec_add(real_add, vec_scalar_mul(real_mul, c, x),
// vec_scalar_mul(real_mul, d, y))`.
var family = registry.NewFamily("vector/convex", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing)
