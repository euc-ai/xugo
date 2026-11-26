package weil_curve

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

//go:embed weil_curve.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the terms of a curve inside a closed
// field M: the ring of its function field K, its genus, the numerator of its zeta
// function, its effective-divisor series, its point counts, and the size q of its
// constants k. The names M, K, k, A₀, A₁, A₀₁ are the statements' binders, so a
// statement that binds one of them further in writes the term out.
var family = registry.NewFamily("scheme/weil_curve", familyCNF).WithCoerceDomain(
	proof.RealDomain).WithAbbrev(Abbrev{
	{Name: "functionRing", Text: "restrict_ring(field_ring(M), K)"},
	{Name: "genus", Text: "curve_genus(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "numerator", Text: "curve_zeta_numerator(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "effective", Text: "curve_effective_count(«functionRing», k, A₀, A₁, A₀₁)"},
	{Name: "count", Text: "curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁)"},
	{Name: "q", Text: "real_of_num(card(k))"},
})
