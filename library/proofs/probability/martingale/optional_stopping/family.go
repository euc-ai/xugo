package optional_stopping

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed optional_stopping.cnf.pb
var familyCNF []byte

var family = registry.NewFamily(
	"probability/martingale/optional_stopping", familyCNF).WithCoerceDomain(
	RealDomain)
