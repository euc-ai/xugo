// family.go — the invertible_lattice_pair family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=invertible_lattice_pair.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/invertible_lattice_pair go test -run TestRecordFamilyCNF ./library/integrity/gates/

package invertible_lattice_pair

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed invertible_lattice_pair.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// invertible_lattice_pair/invertible_lattice_pair.cnf.pb from the name's basename, and
// the registered entry prefix is `invertible_lattice_pair.<Member>`.
var family = registry.NewFamily("scheme/invertible_lattice_pair", familyCNF).WithAbbrev(Abbrev{
	{Name: "wbVectors", Text: "restrict_module(regular_module(field_ring(L)))"},
	{Name: "wbField", Text: "regular_module(field_ring(L))"},
	{Name: "wbRing", Text: "restrict_ring(field_ring(L))"},
	{Name: "wbAmbient", Text: "lattice_pair_ambient(«wbRing»(A₀₁), «wbField»)"},
	{Name: "wbSpan", Text: "module_span(«wbRing»(A₀₁), «wbField»)"},
	{Name: "wbPair", Text: "lattice_pair(«wbRing»(A₀₁), A₀, A₁, «wbField»)"},
	{Name: "wbMul", Text: "lattice_pair_mul(field_ring(L), A₀, A₁)"},
	{Name: "wbInvertible", Text: "invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁)"},
	{Name: "wbInverse", Text: "lattice_pair_inverse(field_ring(L), A₀, A₁)"},
	{Name: "ambientInvertibleInverse", Text: "fractional_inverse(field_ring(L), A₀, fst(M))"},
	{Name: "colonFirst", Text: "{a:A | a ∈ L.carrier ∧ (∀m:A. m ∈ fst(M) ⇒ a * m ∈ fst(N))}"},
	{Name: "colonSecond", Text: "{a:A | a ∈ L.carrier ∧ (∀m:A. m ∈ snd(M) ⇒ a * m ∈ snd(N))}"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
