package twisted_counting

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed twisted_counting.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/group/twisted_counting", familyCNF)
