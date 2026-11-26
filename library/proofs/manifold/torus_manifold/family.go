package torus_manifold

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_sobolev"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed torus_manifold.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/torus_manifold", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
