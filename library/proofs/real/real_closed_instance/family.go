package real_closed_instance

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_closed_instance.cnf.pb
var familyCNF []byte

// The chapter's numbers are reals: an `&` no operand anchors is ℝ's
// embedding, by the declaration on the handle.
var family = registry.NewFamily("real/real_closed_instance", familyCNF).WithCoerceDomain(RealDomain)
