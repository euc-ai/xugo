// family.go — the kuhn family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=kuhn.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=cartesian/kuhn go test -run TestRecordFamilyCNF ./library/integrity/gates/

package kuhn

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed kuhn.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives kuhn/kuhn.cnf.pb from
// the name's basename, and the registered entry prefix is `kuhn.<Member>`.
// The chapter has no vocabulary of its own: its three constants are
// spelled as applications, and every other name its statements spell —
// the tuples, the finite sets and their counts, parity — resolves through
// its mint. Its table names the terms its statements and proofs share,
// each written over the dimension n (and «cofaces» over p, s and a):
// «cofaces», the Kuhn simplices holding the face of s opposite its vertex
// a, which the face counts read; «vertex»(v, τ, j), the point of the chain
// from v in the order τ after j steps, raising coordinate i at step τ(i);
// «raised»(v, x), the coordinates below n at which x exceeds v, which tell
// the points of a simplex apart; and the three apexes a face of a chain
// can take besides the vertex it was cut from — «lifted»(v, τ), the
// chain's end raised once more in the coordinate of the first step,
// «lowered»(v, τ), its start lowered in the coordinate of the last step,
// and «swapped»(v, τ, m), vertex m with the steps m - 1 and m exchanged.
var family = registry.NewFamily("cartesian/kuhn", familyCNF).WithAbbrev(Abbrev{
	{Name: "cofaces", Text: "{t:set(num → num) | " +
		"    kuhn_simplex(p, n, t) ∧ ∃b:(num → num). b ∈ t ∧ delete(t, b) = delete(s, a)}"},
	{Name: "vertex", Text: "λv:(num → num). λτ:(num → num). λj:num. λi:num. " +
		"    v(i) + COND(i < n ∧ τ(i) < j, 1, 0)"},
	{Name: "raised", Text: "λv:(num → num). λx:(num → num). {i:num | i < n ∧ v(i) < x(i)}"},
	{Name: "lifted", Text: "λv:(num → num). λτ:(num → num). λi:num. " +
		"    «vertex»(v, τ, n, i) + COND(i < n ∧ τ(i) = 0, 1, 0)"},
	{Name: "lowered", Text: "λv:(num → num). λτ:(num → num). λi:num. " +
		"    v(i) - COND(i < n ∧ τ(i) = n - 1, 1, 0)"},
	{Name: "swapped", Text: "λv:(num → num). λτ:(num → num). λm:num. λi:num. " +
		"    v(i) + COND(i < n ∧ (τ(i) < m - 1 ∨ τ(i) = m), 1, 0)"},
})
