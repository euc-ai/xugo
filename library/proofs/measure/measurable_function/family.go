package measurable_function

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_topology"
	_ "github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	_ "github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed measurable_function.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/measurable_function", familyCNF).WithCoerceDomain(
	RealDomain)
