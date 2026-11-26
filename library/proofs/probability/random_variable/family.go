package random_variable

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	_ "github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed random_variable.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("probability/random_variable", familyCNF).WithCoerceDomain(
	RealDomain)
