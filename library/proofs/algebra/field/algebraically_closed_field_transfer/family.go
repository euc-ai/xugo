package algebraically_closed_field_transfer

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed algebraically_closed_field_transfer.cnf.pb
var familyCNF []byte

// family is the family handle. It reads the ring formulas' table, which names
// the carriers of the fields on A and on B that a quantifier-free equivalent
// is common to.
var family = registry.NewFamily(
	"algebra/field/algebraically_closed_field_transfer", familyCNF).WithOuterAbbrev(
	ring_formula.ChapterAbbrev)
