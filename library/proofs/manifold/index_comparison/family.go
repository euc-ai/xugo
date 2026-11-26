package index_comparison

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bott_operator"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/analytic_index"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/topological_index"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/torus_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed index_comparison.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/index_comparison", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
