package nat_multiplicity

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed nat_multiplicity.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("nat_num/nat_multiplicity", familyCNF)
