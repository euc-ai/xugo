// family.go — the do_calculus family manifest: the registry handle every member registers
// into and the family's shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=do_calculus.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/do_calculus go test -run TestRecordFamilyCNF ./library/integrity/gates/

package do_calculus

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/causal/graphical_markov"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed do_calculus.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the distributions of a
// model M under do(X = v) and do(X ∪ Z = v), and the σ-algebra of the coin
// on the regime family's samples.
var family = registry.NewFamily("causal/do_calculus", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "Px", Text: "scm_distribution(scm_do(M, X, v))"},
	{Name: "Pxz", Text: "scm_distribution(scm_do(M, X ∪ Z, v))"},
	{Name: "flag", Text: "pullback_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), snd, 𝕌⟨A:set(bool)⟩)"},
})
