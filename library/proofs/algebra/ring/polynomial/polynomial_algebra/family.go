// family.go — the polynomial_algebra family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=polynomial_algebra.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/polynomial/polynomial_algebra go test -run TestRecordFamilyCNF ./library/integrity/gates/

package polynomial_algebra

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_algebra.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// polynomial_algebra/polynomial_algebra.cnf.pb from the name's basename, and the
// registered entry prefix is `polynomial_algebra.<Member>`. The table is
// written over the binders of the members that spell it: a monomial m in
// «below»; the ring record R and the polynomials f, g in «cross», «sums»
// and «fibre»; and in «lex» a sequence ι : num → D of variables, which
// only the members ordering monomials along it bind.
var family = registry.NewFamily(
	"algebra/ring/polynomial/polynomial_algebra", familyCNF).WithAbbrev(Abbrev{
	{Name: "below", Text: "{m₁:(D → num) | ∀x:D. m₁(x) ≤ m(x)}"},
	{Name: "cross", Text: "set_cross(fun_support(R.zero, f), fun_support(R.zero, g))"},
	{Name: "sums", Text: "image(λp:prod(D → num, D → num). λx:D. fst(p, x) + snd(p, x), «cross»)"},
	{Name: "fibre", Text: "λm:(D → num). " +
		"    {p:prod(D → num, D → num) | p ∈ «cross» ∧ (λx:D. fst(p, x) + snd(p, x)) = m}"},
	{Name: "lex", Text: "λm:(D → num). λn:(D → num). ∃i:num. " +
		"    m(ι(i)) < n(ι(i)) ∧ (∀j:num. j < i ⇒ m(ι(j)) = n(ι(j)))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
