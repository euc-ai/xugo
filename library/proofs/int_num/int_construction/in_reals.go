// in_reals.go — the embedding as one rewrite.
//
// A statement about integers is a statement about their
// representatives: an equation is the equation of the representatives,
// a comparison is its definition, and each operation is carried across
// by its bridge. InReals is those readings as one rule set, so that a
// chapter borrowing a theorem of ℝ for ℤ writes one move — read in ℝ —
// and then cites the real theorem.

package int_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
)

// InReals — read a statement about integers in ℝ: every integer
// equation becomes one between representatives, every comparison its
// definition, and every ring operation and numeral crosses by its
// bridge. The absolute value, sign, max and min are not ring
// operations and keep their own bridges.
var InReals = RuleSet(
	Fwd(RepresentativeInjective),
	Fwd(IntLeDef),
	Fwd(IntLtDef),
	Fwd(IntGeDef),
	Fwd(IntGtDef),
	Fwd(OfNumBridge),
	Fwd(NegBridge),
	Fwd(AddBridge),
	Fwd(SubBridge),
	Fwd(MulBridge),
)
