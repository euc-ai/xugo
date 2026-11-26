package embedding_normal

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed embedding_normal.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/embedding_normal", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
