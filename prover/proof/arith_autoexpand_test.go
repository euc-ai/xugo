package proof

// End-to-end regression for `auto`'s pipeline (arith fast-path →
// AutoExpand): the arith stage's no-hurt contract (bridge emission + hyp
// retention, prover/tactic/arith_tactics.go) must keep the CNF-closable
// probe shapes of nat_divides.DividesLessEqStrong closable: an arith stage that consumed
// the `0*x = 0` bridges would kill both rows.

import (
	"math/big"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"

	"github.com/stretchr/testify/require"
)

// autoPipelineCloses mirrors the engine's `auto` dispatch: ApplyArithSimplify
// (unconditionally here — both goals have arith content), then AutoExpand on
// whatever leaves remain.
func autoPipelineCloses(t *testing.T, goal core.Prop) bool {
	t.Helper()
	var cnfCache utils.Map[core.TermKey, core.Prop]
	env := &ProverEnv{
		ProofService:          MockConstMetaService(),
		CnfRefuterTimeout:     8 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     NewCNFNormalizeCache(),
	}
	ctx := NewScript(env)
	sec := ctx.Section(goal)
	ApplyArithSimplify(t.Context(), sec)
	if sec.Proved() {
		return true
	}
	for _, leaf := range sec.UnsolvedLeaves() {
		if !env.AutoExpand().Apply(leaf) {
			return false
		}
	}
	return sec.Proved()
}

func TestAutoPipelineClosesArgPositionParamodRows(t *testing.T) {
	num := ext.NumType
	m := ext.Var("m", num)
	n := ext.Var("n", num)
	x := ext.Var("x", num)
	zero := ext.WrapTerm(ext.MakeNumeral(big.NewInt(0)))
	mul := ext.WrapTerm(dsl.NatStarMeta.Term())
	lt := ext.WrapTerm(dsl.NatLtMeta.Term())

	// (m = 0) ∨ (0 < m), m*x ≠ 0*x ⊢ 0 < m — the arith stage rewrites the
	// NEQ hyp (0*x → 0); the emitted bridge `0*x = 0` lets CNF paramodulate
	// the division-branch equation m = 0 into the argument position and
	// close by contradiction with the bridge.
	require.True(t, autoPipelineCloses(t, prop.MakeProp(
		lt.Apply(zero, m),
		m.Eq(zero).Or(lt.Apply(zero, m)),
		ext.Not(mul.Apply(m, x).Eq(mul.Apply(zero, x))),
	)), "row 4: rewrite under a function symbol, equation from a division branch")

	// (m = 0) ∨ (0 < m), n ≠ 0, n = m*x, 0*x = 0 ⊢ 0 < m — the retention
	// rule keeps both the ring-true bridge hyp and the num-totality
	// disjunction (CNF's case-split license); AutoExpand closes the
	// original goal.
	require.True(t, autoPipelineCloses(t, prop.MakeProp(
		lt.Apply(zero, m),
		m.Eq(zero).Or(lt.Apply(zero, m)),
		ext.Not(n.Eq(zero)),
		n.Eq(mul.Apply(m, x)),
		mul.Apply(zero, x).Eq(zero),
	)), "row 5: the wild nat_divides.DividesLessEqStrong shape")
}
