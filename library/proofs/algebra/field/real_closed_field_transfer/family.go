package real_closed_field_transfer

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_ring_formula"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_closed_field_transfer.cnf.pb
var familyCNF []byte

// family is the family handle. It reads the ordered-ring formulas' table,
// which names the real closed models on A and on B that a quantifier-free
// equivalent is common to.
var family = registry.NewFamily(
	"algebra/field/real_closed_field_transfer", familyCNF).WithOuterAbbrev(
	ordered_ring_formula.ChapterAbbrev)
