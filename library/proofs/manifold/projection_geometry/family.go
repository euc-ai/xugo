package projection_geometry

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	_ "github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projection_geometry.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/projection_geometry", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
