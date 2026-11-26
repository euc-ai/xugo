package galois_good_fibres

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed galois_good_fibres.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/galois_good_fibres", familyCNF)
