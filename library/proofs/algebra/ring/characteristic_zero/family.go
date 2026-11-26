package characteristic_zero

import (
	_ "embed"

	// int_sum mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed characteristic_zero.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/ring/characteristic_zero", familyCNF)
