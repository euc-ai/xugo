// family.go — the vec_derivative family manifest: the registry handle
// every member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=vec_derivative.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/vec_derivative go test -run TestRecordFamilyCNF ./library/integrity/gates/

package vec_derivative

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed vec_derivative.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `vec_derivative.<Member>`. The chapter works at ℝ, as euclidean does:
// the instance theorem binds the ring's components, so a statement here
// spells `vec⟨n⟩(u)`, `u - v` and `c • u`, and an unanchored numeral `&k`
// is a real one.
var family = registry.NewFamily("vector/vec_derivative", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain)
