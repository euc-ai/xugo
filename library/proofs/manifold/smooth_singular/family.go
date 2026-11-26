package smooth_singular

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/singular_cohomology"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed smooth_singular.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/smooth_singular", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain)
