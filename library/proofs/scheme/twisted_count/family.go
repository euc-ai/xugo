package twisted_count

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed twisted_count.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/twisted_count", familyCNF)
