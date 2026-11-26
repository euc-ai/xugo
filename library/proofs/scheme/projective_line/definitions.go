// definitions.go — the lattice pairs O(n) on the projective line.
//
// The line lives inside a field L: chart 0 is k[t], chart 1 is k[1/t]
// and the overlap is k[t, 1/t], all subsets of L, for a subfield k and
// an element t of L transcendental over k. L need not be k(t): a curve's
// lattice pairs are read on the line inside the curve's own function
// field.

package projective_line

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

// ProjectiveLinePairDef — `projective_line_pair(L, k, t, n)`, written O(n):
// the pair (k[t], tⁿ · k[1/t]), the sections of degree at most n at
// infinity. O(0) is the structure pair and O(−2) the dualizing pair.
var ProjectiveLinePairDef = projectiveLinePairDefThm{family.Define(registry.DefEntry{
	Name:     "ProjectiveLinePairDef",
	Key:      "prop_2111c175904e6687",
	Const:    "projective_line_pair",
	Type:     "field_ops(A) → set(A) → A → int → prod(set(A), set(A))",
	Implicit: []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀t:A. ∀n:int. " +
			"    projective_line_pair(F, k, t, n) = " +
			"    (polynomial_image(field_ring(F), k, t), " +
			"        image(F.mul(laurent_monomial(F.mul, F.one, F.inv, t, n)), " +
			"            polynomial_image(field_ring(F), k, F.inv(t))))",
	},
	Deps: []registry.EntryLike{},
})}
