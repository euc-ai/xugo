package matrix_norm

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed matrix_norm.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `matrix_norm.<Member>`. The chapter works at ℝ, as euclidean does, so
// a statement here spells `vec⟨n⟩(v)`, `‖v‖_n` and `⟪u, v⟫_n`.
var family = registry.NewFamily("vector/matrix_norm", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain)
