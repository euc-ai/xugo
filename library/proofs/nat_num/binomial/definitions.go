// definitions.go — the chapter's one constant.

package binomial

import (
	"github.com/euc-ai/xugo/library/registry"
)

// BinomialDef — the binomial coefficients, defined by Pascal's rule as a
// recursion on the row. Row 0 holds 1 in column 0 and 0 everywhere
// else; in every later row column 0 holds 1 and each other entry is the
// sum of the two entries above it, binomial(n, k - 1) and
// binomial(n, k). The column rides along as a parameter the recursive
// call is free to move, which is how one recursion on n fills the whole
// table.
var BinomialDef = binomialDefThm{family.Define(registry.DefEntry{
	Name:  "BinomialDef",
	Key:   "prop_d4efef7c317c6269",
	Const: "binomial",
	Type:  "num → num → num",
	Equations: []string{
		"∀k:num. binomial(0, k) = COND(k = 0, 1, 0)",
		"∀n k:num. binomial(suc(n), k) = COND(k = 0, 1, binomial(n, k - 1) + binomial(n, k))",
	},
})}
