package singular_cohomology

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/singular_homology"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed singular_cohomology.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("simplicial/singular_cohomology", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain)
