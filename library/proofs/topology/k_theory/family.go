package k_theory

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed k_theory.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/k_theory", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
