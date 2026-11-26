package totient

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed totient.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("nat_num/totient", familyCNF)
