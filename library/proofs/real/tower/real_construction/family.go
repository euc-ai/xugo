// family.go — the real_construction family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var AddSym =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// Naming: the members' names form a mirror ladder with
// eudoxus_slope/nonneg_real/nonneg_real_formal_diff. Each entry's Key is its statement's own
// normalized key.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=<real_construction.MEMBER> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/tower/real_construction go test -run TestRecordFamilyCNF ./library/integrity/gates/

package real_construction

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/solver/ac"
)

//go:embed real_construction.cnf.pb
var familyCNF []byte

// family is the family handle. The subtest name is real/tower/real_construction;
// axioms lives directly under real/tower/ (not under internal/) — it
// is the tower's public interface.
var family = registry.NewFamily("real/tower/real_construction", familyCNF).WithVocabSpec(vocab)

// AddAC / MulAC — the AC derivers for ℝ's two associative-commutative
// operations. A regroup premise reads `AddAC(ctx).Eq(lhs, rhs)`; the
// goal face is `ACRegroupWith(AddAC(ctx))`. The deriver reads the two
// axioms through the caller's own script, so they are the caller's deps
// exactly as if it fetched them itself; it only spares the caller the
// pair of DepNormalized locals.
//
// These are EXPORTED where the corresponding helpers elsewhere in the
// corpus are private, and the asymmetry is the point: an AC deriver is
// built from an assoc/sym certificate pair, and for ℝ that pair is
// THIS chapter's theorems. A consumer chapter holding its own deriver
// is holding one over facts it does not own — real_ring's copy said so
// itself ("the derivers reach OUT of this family into tower/real_construction") —
// and because that copy was unexported, real_field could not borrow it
// and spelled the pair inline instead. Owning them here is what makes
// the borrow legal, and every later ℝ chapter needs the same thing.
// The same argument settles ℕ the same way, and `nat_arith.AddAC` /
// `nat_arith.MulAC` are exported for it. Ownership is not a reason to stay
// private: ownership is what makes EXPORT legal, and whether others
// need to borrow is what decides it.
func AddAC(ctx *Script) *ac.Deriver {
	return ac.New(ctx.DepNormalized(AddAssoc), ctx.DepNormalized(AddSym))
}

func MulAC(ctx *Script) *ac.Deriver {
	return ac.New(ctx.DepNormalized(MulAssoc), ctx.DepNormalized(MulSym))
}
