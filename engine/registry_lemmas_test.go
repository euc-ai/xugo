package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A session bound to a family refuses a cite of another chapter's
// unexported entry, naming the entries it stands on that the family can
// cite; `known` does not close by it either. The entry's own family
// cites it.
func TestCiteRefusal_UnexportedEntryOfAnotherFamily(t *testing.T) {
	ctx := context.Background()
	e, s := boundSession(t, "algebra/field/finite_field")
	gid := addTextGoal(t, s, "∀m:num. m ^ 0 = 1")
	for _, tactic := range []TacticReq{
		{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "nat_arith.powRightZeroClause"}}},
		{Type: "lemma", LemmaKey: "nat_arith.powRightZeroClause"},
	} {
		res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: gid, Tactic: tactic})
		require.NoError(t, err)
		require.False(t, res.Success, "%s cites an entry finite_field cannot name", tactic.Type)
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "nat_arith.powRightZeroClause is an unexported entry of nat_num/nat_arith")
		assert.Contains(t, res.Diagnostics[0].Message, "It stands on nat_arith.NatPow")
	}
	res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "known"}})
	require.NoError(t, err)
	assert.False(t, res.Success, "known does not close by an entry the family cannot cite")

	e, s = boundSession(t, "nat_num/nat_arith")
	addTextGoal(t, s, "∀m:num. m ^ 0 = 1")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "nat_arith.powRightZeroClause"}}})
	assert.Contains(t, emitSole(t, e, s, "Build_OwnClause"), "By(powRightZeroClause)")
}

// An unbound session's cite of an unexported entry is held to the
// family the member is emitted into: the export refuses it rather than
// print a reference that does not compile.
func TestEmitSection_RefusesUnreachableCite(t *testing.T) {
	e := newEngine(statedSessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀m:num. nat_pow(m, 0) = 1")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "nat_arith.powRightZeroClause"}}})
	_, err = e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: "Build_Probe", Family: "algebra/field/finite_field"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "nat_arith.powRightZeroClause is an unexported entry of nat_num/nat_arith")
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: "Build_Probe", Family: "nat_num/nat_arith"})
	require.NoError(t, err)
	assert.Contains(t, out.Go, "By(powRightZeroClause)")
}

// An entry of a Go internal package is reachable from the packages
// under that package's parent only; a package not yet placed is held to
// the export rule alone.
func TestUnreachableFrom_InternalPackage(t *testing.T) {
	_ = newEngine(statedSessionEnv())
	entry, ok := registry.ByName("eudoxus_slope.IsNaddDef")
	require.True(t, ok)
	require.Equal(t, "real/tower/internal/eudoxus_slope", entry.Family().PackageDir())
	assert.Empty(t, entry.UnreachableFrom("real/tower/internal/eudoxus_slope"))
	assert.Empty(t, entry.UnreachableFrom("real/tower/nonneg_real"))
	assert.Contains(t, entry.UnreachableFrom("algebra/field/finite_field"), "internal package real/tower/internal/eudoxus_slope")
	assert.Empty(t, entry.UnreachableFrom(""))
	unexported, ok := registry.ByName("nat_arith.powRightZeroClause")
	require.True(t, ok)
	assert.Contains(t, unexported.UnreachableFrom(""), "unexported entry of nat_num/nat_arith")
}
