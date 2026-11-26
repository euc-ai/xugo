package lefschetz

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lefschetz.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives lefschetz/lefschetz.cnf.pb
// from the name's basename, and the registered entry prefix is
// `lefschetz.<Member>`. The table names the comparison the field-level
// stability statements make: «zeroAndPast»(F, G, p, N) says that F is a
// field of characteristic zero and G a field of characteristic p, with p
// past the bound N. LargeCharacteristicStability compares algebraically
// closed fields and spells its comparison out.
var family = registry.NewFamily("algebra/field/lefschetz", familyCNF).WithAbbrev(Abbrev{
	{Name: "zeroAndPast", Text: "λF:field_ops(A). λG:field_ops(B). λp:num. λN:num. " +
		"    field_on(F) ∧ field_characteristic(F, 0) ∧ field_on(G) ∧ field_characteristic(G, p) ∧ N < p"},
})
