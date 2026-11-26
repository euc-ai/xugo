package bott_periodicity

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_theory"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed bott_periodicity.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/bott_periodicity", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
