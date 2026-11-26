package sobolev_section

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_sobolev"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/function_support"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed sobolev_section.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/sobolev_section", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
