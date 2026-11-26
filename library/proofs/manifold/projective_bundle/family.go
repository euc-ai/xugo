package projective_bundle

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/compact_de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/projection_geometry"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_bundle.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/projective_bundle", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
