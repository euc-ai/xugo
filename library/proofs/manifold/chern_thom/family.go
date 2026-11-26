package chern_thom

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_thom"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_thom"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed chern_thom.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/chern_thom", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
