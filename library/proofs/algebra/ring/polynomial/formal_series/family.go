// family.go — the formal_series family manifest: the registry handle every
// member registers into, the chapter's abbreviation table, and the
// family's one shared recorded CNF cache.

package formal_series

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed formal_series.cnf.pb
var familyCNF []byte

// family is the family handle. The chapter's members bind their ring as
// a record (R, or L for a field), whose fields supply the components the
// series operations read.
// The table names the compound terms the chapter's statements share: the
// recurrence's positive indices, the polynomials 1 − T and 1 − Tᵈ in the
// polynomial chapter's basis, the numeral n, which is n ones summed in the
// ring, and the Euler derivative, which weights the n-th coefficient by that
// numeral. The last two read the ring under the name R the statements bind.
var family = registry.NewFamily("algebra/ring/polynomial/formal_series", familyCNF).WithOuterAbbrev(
	polynomial.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "indices", Text: "λj:num. {i:num | 0 < i ∧ i ≤ j}"},
	{Name: "1−T", Text: "basis_vector(0) - basis_vector(1)"},
	{Name: "1−Tᵈ", Text: "λd:num. basis_vector(0) - basis_vector(d)"},
	{Name: "euler", Text: "λf:(num → A). λn:num. monoid_pow(R.add, R.zero, R.one, n) * f(n)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
