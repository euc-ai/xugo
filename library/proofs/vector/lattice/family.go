// family.go — the lattice family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=lattice.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/lattice go test -run TestRecordFamilyCNF ./library/integrity/gates/

package lattice

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lattice.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// lattice/lattice.cnf.pb from the name's basename, and the registered
// entry prefix is `lattice.<Member>`.
// The chapter works at ℤ: the instance theorem binds the ring's
// components (`add ↦ int_add`, `zero ↦ &0`, …); README.md says what a
// statement here spells.
var family = registry.NewFamily("vector/lattice", familyCNF).
	WithInstance(comm_ring.CommRing, int_real_lift.CommRing)
