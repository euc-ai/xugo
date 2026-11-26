package elliptic_hasse_weil

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

//go:embed elliptic_hasse_weil.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the curve's function field K
// read inside the closed field M, M restricted to K, which keeps M's
// operations: the statements bind M and K and read the Weierstrass datum
// there. The chapter's trace is an integer and its bounds are real; every
// number it writes is a real, and every integer embedding has an integer
// operand beside it. So an `&` no operand anchors is ℝ's embedding, by the
// declaration on the handle.
var family = registry.NewFamily("scheme/elliptic_hasse_weil", familyCNF).WithCoerceDomain(
	proof.RealDomain)
