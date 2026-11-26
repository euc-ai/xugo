// family.go — the nat_arith family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var Assoc = family.Add(...)`);
// they never call InstallCNFCache — the replay harness installs
// familyCNF env-side before every member's Define.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=nat_arith.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=nat_num/nat_arith go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The first live-records one member's refutes and merges them into the
// family pb; the second drops the keys no member reaches any more.

package nat_arith

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/solver/ac"
)

//go:embed nat_arith.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates nat_num/nat_arith/nat_arith.cnf.pb from it, and the
// registered entry prefix is the name's last segment (`nat_arith.<Member>`). The vocabulary (vocab.go)
// is the chapter's statement alphabet, installed into every member's
// ParseScope before its first section.
var family = registry.NewFamily("nat_num/nat_arith", familyCNF).WithVocabSpec(vocab)

// AddAC / MulAC — the AC derivers for ℕ's + and ×. A regroup premise
// reads `AddAC(ctx).Eq(lhs, rhs)`; the goal face is
// `ACRegroupWith(AddAC(ctx))`. The deriver reads AddAssoc/AddSym (or
// the × pair) through the caller's own script, so they are the caller's
// deps exactly as if it fetched them itself; it only spares the caller
// the pair of DepNormalized locals.
//
// EXPORTED for the same reason real/tower/real_construction exports its pair:
// these certificates are THIS chapter's theorems, so a consumer
// chapter holding its own deriver is holding one over facts it does
// not own. Owning the pair is what makes the borrow legal; export is
// what makes it possible.
func AddAC(ctx *Script) *ac.Deriver {
	return ac.New(ctx.DepNormalized(AddAssoc), ctx.DepNormalized(AddSym))
}

func MulAC(ctx *Script) *ac.Deriver {
	return ac.New(ctx.DepNormalized(MulAssoc), ctx.DepNormalized(MulSym))
}
