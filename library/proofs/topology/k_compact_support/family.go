package k_compact_support

import (
	_ "embed"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	_ "github.com/euc-ai/xugo/library/proofs/topology/k_theory"
	_ "github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	_ "github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed k_compact_support.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("topology/k_compact_support", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
