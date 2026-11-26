package boolean_degree

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed boolean_degree.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("sets/boolean_function/boolean_degree", familyCNF).WithCoerceDomain(
	RealDomain)
