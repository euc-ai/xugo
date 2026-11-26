package ideal_class_group

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ideal_class_group.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/ring/ideal_class_group", familyCNF).WithAbbrev(Abbrev{
	{Name: "Invertibles", Text: "mk_group(fractional_mul(field_ring(L), S), " +
		"    S, " +
		"    fractional_inverse(field_ring(L), S), " +
		"    invertible_ideals(field_ring(L), S))"},
})
