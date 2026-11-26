package stopping_time

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/option"
	_ "github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed stopping_time.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/stopping_time", familyCNF).WithCoerceDomain(RealDomain)
