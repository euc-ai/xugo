package zeta_recurrence

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed zeta_recurrence.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/zeta_recurrence", familyCNF)
