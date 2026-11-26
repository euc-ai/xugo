package spin_geometry

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/clifford_spin"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/chern_weil"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/embedding_normal"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/projection_geometry"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed spin_geometry.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/spin_geometry", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
