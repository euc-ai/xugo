package determinant

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed determinant.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("vector/determinant", familyCNF).WithAbbrev(Abbrev{
	// The maps pinned at k: those sending every point below k below n and fixing every point from k on.
	{Name: "pinned", Text: "λk:num. " +
		"    {f:num → num | (∀j:num. j < k ⇒ f(j) < n) ∧ (∀j:num. k ≤ j ⇒ f(j) = j)}"},
	{Name: "column map", Text: "λw:(num → A). λr:num. " +
		"    module_sum(c.add, c.zero, {k:num | k < n}, λk:num. P(r, k) * w(k))"},
	// The sign of a permutation q of the points below n, read in c: one when q is even, minus one when it is odd.
	{Name: "sign", Text: "λq:permutation(num). COND(permutation_even(n, q), c.one, -c.one)"},
})
