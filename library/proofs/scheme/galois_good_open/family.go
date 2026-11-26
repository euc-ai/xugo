package galois_good_open

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed galois_good_open.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/galois_good_open", familyCNF)
