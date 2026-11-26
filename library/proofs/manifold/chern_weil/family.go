package chern_weil

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	_ "github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed chern_weil.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/chern_weil", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
