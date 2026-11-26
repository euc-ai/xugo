package smooth_projection_bundle

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	_ "github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed smooth_projection_bundle.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/smooth_projection_bundle", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
