package pseudo_differential

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/fredholm"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_pseudo_differential"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_cotangent"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/sobolev_section"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed pseudo_differential.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/pseudo_differential", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
