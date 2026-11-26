// family.go — the euclidean_topology family manifest: the registry handle
// every member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=euclidean_topology.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/euclidean_topology go test -run TestRecordFamilyCNF ./library/integrity/gates/

package euclidean_topology

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed euclidean_topology.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `euclidean_topology.<Member>`. The chapter works at ℝ, as euclidean
// does: the instance theorem binds the ring's components, so a statement
// here spells `vec⟨n⟩(u)` and `dist⟨n⟩(u, v)`, and an unanchored numeral
// `&k` is a real one. Its table names
// «append»(a, t), the tuple a with its coordinate n set to t, which
// appends t to an n-vector a; and «inCell»(q, w, r, s), that r and s lie
// in the cell of width w at q, each of their first n coordinates between
// that of q and it plus w.
var family = registry.NewFamily("vector/euclidean_topology", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "append", Text: "λa:(num → real). λt:real. λi:num. COND(i = n, t, a(i))"},
		{Name: "inCell", Text: "λq:(num → real). λw:real. λr:(num → real). λs:(num → real). ∀j:num. " +
			"    j < n ⇒ q(j) ≤ r(j) ∧ r(j) ≤ q(j) + w ∧ q(j) ≤ s(j) ∧ s(j) ≤ q(j) + w"},
	})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
