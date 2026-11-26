package topological_index

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/embedding_normal"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_cotangent"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/riemannian"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	_ "github.com/euc-ai/xugo/library/proofs/topology/bott_periodicity"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_pushforward"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed topological_index.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/topological_index", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
