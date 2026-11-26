package polynomial_encoding

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_encoding.cnf.pb
var familyCNF []byte

// _Monomial is the Go type of a monomial, an exponent for every variable name.
type _Monomial = Fun[Nat, Nat]

// family is the chapter's handle. Its table names the slots a polynomial code reads — the
// coefficient block at c, and «U», its union with the coordinate block at x — and the powers,
// products and terms of coordinate and coefficient variables the code is built from.
var family = registry.NewFamily(
	"algebra/ring/polynomial/polynomial_encoding", familyCNF).WithAbbrev(Abbrev{
	{Name: "block", Text: "{j:num | c ≤ j ∧ j < c + coefficient_count(n, d)}"},
	{Name: "U", Text: "«block» ∪ {j:num | x ≤ j ∧ j < x + n}"},
	{Name: "power", Text: "λm:(num → num). λi:num. " +
		"    monoid_pow(polynomial_algebra_mul(int_ring), " +
		"        polynomial_algebra_one(int_ring), " +
		"        polynomial_algebra_var(int_ring, x + i), " +
		"        m(i))"},
	{Name: "product", Text: "λm:(num → num). " +
		"    module_sum(polynomial_algebra_mul(int_ring), " +
		"        polynomial_algebra_one(int_ring), " +
		"        {i:num | i < n}, " +
		"        «power»(m))"},
	{Name: "term", Text: "λm:(num → num). " +
		"    polynomial_algebra_mul(int_ring, " +
		"        polynomial_algebra_var(int_ring, c + monomial_slot(n, d, m)), " +
		"        «product»(m))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
