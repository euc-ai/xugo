package euclidean_domain

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed euclidean_domain.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/ring/euclidean_domain", familyCNF)
