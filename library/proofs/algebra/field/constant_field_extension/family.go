package constant_field_extension

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed constant_field_extension.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/field/constant_field_extension", familyCNF)
