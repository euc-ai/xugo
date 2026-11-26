package engine

// cite-node + term_specialize: install a cited node's ∀-closed conclusion
// already ground-instantiated at named witnesses, in ONE apply — instead of
// the `cite-node` + `instantiate`×N + `clear` ladder that Step-6.6 assembly /
// coordinator steps otherwise pay. The specialization reuses `lemma`'s
// resolveTermSpecializeWitnesses + applyLemmaTermSpecializeChain verbatim, so
// it records as ordinary instantiate/clear ministeps (no proto/emit/replay
// change).

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// proveAndPool proves a ∀-closed, hyp-free `psi` in a fresh session via
// `auto` and returns nothing — the session close publishes psi's cert to
// the engine-global derivation pool, citable by closedNodeID(0, psi).
func proveAndPool(t *testing.T, e *Engine, ctx context.Context, psi core.Prop) {
	t.Helper()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: s.AddGoal(psi),
		Tactic: TacticReq{Type: "auto"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "worker lemma must close via auto: %+v", res.Diagnostics)
}

// TestCiteNode_TermSpecialize_SingleBinder: cite ⊢ ∀x:bool. x=x specialized
// at witness w installs the GROUND hyp `w=w` — with NO ∀-headed residual.
func TestCiteNode_TermSpecialize_SingleBinder(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	x := ext.Var("x", core.TypeBool())
	psi := prop.MakeProp(ext.ForAll(x)(core.Eq(x.Core(), x.Core()))) // ∀x. x=x
	proveAndPool(t, e, ctx, psi)

	// Coordinator focus: w, q ⊢ q  (w free in scope for the witness "w").
	w := ext.Var("w", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	focus := prop.MakeProp(q.Core(), w.Core())
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: s.AddGoal(focus),
		Tactic: TacticReq{
			Type:           "cite-node",
			NodeID:         closedNodeID(0, psi),
			TermSpecialize: map[string]string{"x": "w"},
		},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "cite-node+term_specialize must apply; diag=%+v", res.Diagnostics)

	hyps := findWorkingHyps(t, res, q.Core())
	expectedGround := core.Eq(w.Core(), w.Core()) // w=w
	foundGround := false
	for _, h := range hyps {
		if h.AlphaEquals(expectedGround) {
			foundGround = true
		}
		assert.True(t, ext.MatchesFORALL(h).IsZero(), "no hyp may be ∀-headed after cite-node+term_specialize; got %s", ext.PrintTerm(h))
	}
	assert.True(t, foundGround,
		"focus must carry the ground hyp w=w (not the ∀-form); hyps=%v", printedHyps(hyps))
}

// TestCiteNode_TermSpecialize_MultiBinder: cite ⊢ ∀x y:bool. (x=y ⇒ x=y)
// specialized at {x:a, y:b} installs the fully-ground hyp `(a=b) ⇒ (a=b)`,
// no ∀ at any level — the 2-binder analogue of the coordinator's 6-binder
// W_TARGET graft (six separate instantiate calls otherwise).
func TestCiteNode_TermSpecialize_MultiBinder(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	x := ext.Var("x", core.TypeBool())
	y := ext.Var("y", core.TypeBool())
	psi := prop.MakeProp(ext.ForAll(x, y)(
		ext.WrapTerm(core.Eq(x.Core(), x.Core())).And(core.Eq(y.Core(), y.Core())))) // ∀x y. (x=x ∧ y=y)
	proveAndPool(t, e, ctx, psi)

	a := ext.Var("a", core.TypeBool())
	b := ext.Var("b", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	focus := prop.MakeProp(q.Core(), a.Core(), b.Core())
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: s.AddGoal(focus),
		Tactic: TacticReq{
			Type:           "cite-node",
			NodeID:         closedNodeID(0, psi),
			TermSpecialize: map[string]string{"x": "a", "y": "b"},
		},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "cite-node+term_specialize (2 binders) must apply; diag=%+v", res.Diagnostics)

	hyps := findWorkingHyps(t, res, q.Core())
	expectedGround := ext.WrapTerm(core.Eq(a.Core(), a.Core())).And(core.Eq(b.Core(), b.Core())).Core() // (a=a) ∧ (b=b)
	foundGround := false
	for _, h := range hyps {
		if h.AlphaEquals(expectedGround) {
			foundGround = true
		}
		assert.True(t, ext.MatchesFORALL(h).IsZero(), "no hyp may be ∀-headed after full multi-binder specialize; got %s", ext.PrintTerm(h))
	}
	assert.True(t, foundGround,
		"focus must carry the ground hyp (a=a)∧(b=b); hyps=%v", printedHyps(hyps))
}

// TestCiteNode_NoTermSpecialize_KeepsForAll is the contrast/regression guard:
// a plain cite-node (no term_specialize) still installs the ∀-closed
// conclusion verbatim — the specialization is strictly opt-in.
func TestCiteNode_NoTermSpecialize_KeepsForAll(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	x := ext.Var("x", core.TypeBool())
	psi := prop.MakeProp(ext.ForAll(x)(core.Eq(x.Core(), x.Core())))
	proveAndPool(t, e, ctx, psi)

	w := ext.Var("w", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	focus := prop.MakeProp(q.Core(), w.Core())
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: s.AddGoal(focus),
		Tactic: TacticReq{Type: "cite-node", NodeID: closedNodeID(0, psi)},
	})
	require.NoError(t, err)
	require.True(t, res.Success)

	hyps := findWorkingHyps(t, res, q.Core())
	foundForAll := false
	for _, h := range hyps {
		if !ext.MatchesFORALL(h).IsZero() && h.AlphaEquals(ext.ForAll(x)(core.Eq(x.Core(), x.Core()))) {
			foundForAll = true
		}
	}
	assert.True(t, foundForAll,
		"plain cite-node must install the ∀-closed conclusion verbatim; hyps=%v", printedHyps(hyps))
}
