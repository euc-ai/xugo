package manifold_cotangent

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/riemannian"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed manifold_cotangent.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/manifold_cotangent", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
