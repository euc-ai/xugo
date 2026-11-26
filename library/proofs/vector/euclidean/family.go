// family.go — the euclidean family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=euclidean.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/euclidean go test -run TestRecordFamilyCNF ./library/integrity/gates/

package euclidean

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed euclidean.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// euclidean/euclidean.cnf.pb from the name's basename, and the
// registered entry prefix is `euclidean.<Member>`.
// The chapter works at ℝ: the module chapters' derived operations
// read the real ring's components, and the instance theorem binds
// them (`add ↦ real_add`, `zero ↦ &0`, …) so that a statement here
// spells `vec_add(u, v)`, `vec⟨n⟩(u)`, `dot⟨n⟩(u, v)` — the components
// are the ring's and the text says so once, here. A numeral `&k` no
// operand anchors is a real one.
var family = registry.NewFamily("vector/euclidean", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).WithOuterAbbrev(dot.ChapterAbbrev).
	WithCoerceDomain(RealDomain)
