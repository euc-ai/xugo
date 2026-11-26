package k_pushforward

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_thom"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed k_pushforward.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/k_pushforward", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
