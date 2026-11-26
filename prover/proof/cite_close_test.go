// cite_close_test.go — Cite's install-vs-close gate (fact.go stage 1 /
// 1.5 / 2), pinned on the iter-#131 shape: a ⇒-guarded law cited at the
// sequent leaf that states it.
//
//	raw:  ∀x. x ≠ e0 ⇒ g(x) = one        (the headline form)
//	norm: ∀x. (x = e0) ∨ (one = g(x))    (what NormalizedThm(Dep) serves)
//	leaf: x0 ≠ e0 ⊢ g(x0) = one
//
// Measured before the stage-1.5 fix: IsStronger is false for BOTH forms
// (stage 1 never fires here); Cite(raw) closed only because eqLemma
// can drive a ⇒-guarded equation as a conditional rewrite, and
// Cite(norm) INSTALLED the clause — the close-vs-install choice was
// made by the resolved install form, which is exactly what a caller
// naming a dep gave up control of. Stage 1.5 (citeNormalizedClose)
// restores the session-parity rule: the leaf IS the fact modulo
// Normalize → close, whichever surface form the resolution produced.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// citeGateEnv builds a fresh env + script with the uninterpreted
// vocabulary of the gate shape. A fresh env per script matters:
// ClaimProvedThm's idempotence check is normalize-keyed across the
// SHARED env cache, so reusing one env would let an earlier sub-test's
// claim shadow a later one's.
func citeGateEnv(t *testing.T) (*Script, *ext.TermWrapper, *ext.TermWrapper, *ext.TermWrapper) {
	t.Helper()
	env := makeStepTestEnv()
	gTy := MakeFun(TypeInd, TypeInd)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("gfun", gTy))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("e0", TypeInd))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("one", TypeInd))
	ctx := NewScript(env)
	g := ctx.Const("gfun", gTy)
	e0 := ctx.Const("e0", TypeInd)
	one := ctx.Const("one", TypeInd)
	return ctx, g, e0, one
}

func citeGateProps(g, e0, one *ext.TermWrapper) (raw Thm, norm Thm, leaf Prop) {
	x := Var("x", TypeInd)
	x0 := Var("x0", TypeInd)
	rawFormula := ext.ForAll(x)(ext.WrapTerm(Not(x.Eq(e0).Core())).Imply(g.Apply(x).Eq(one)))
	raw = core.TestThm(rawFormula)
	normP, _ := Normalize(raw.AsProp())
	norm = core.TestThm(ext.WrapTerm(normP.Conclusion()))
	leaf = prop.MakeProp(g.Apply(x0).Eq(one).Core(), Not(x0.Eq(e0).Core()).Core())
	return raw, norm, leaf
}

// TestCite_NormalizeTierClose: the fix itself. Citing the CLAUSE form
// (what a named target resolves to) at the sequent leaf closes via the
// normalize tier instead of installing — the iter-#131 regression.
// The raw form closes too (it always did; now one stage earlier).
func TestCite_NormalizeTierClose(t *testing.T) {
	{
		ctx, g, e0, one := citeGateEnv(t)
		_, norm, leaf := citeGateProps(g, e0, one)
		sec := ctx.Section(leaf)
		Cite(MakeFact(norm)).applyAction(ctx, sec)
		require.True(t, sec.Proved(),
			"Cite(<clause form>) must CLOSE the normalize-equal sequent leaf, not install")
	}
	{
		ctx, g, e0, one := citeGateEnv(t)
		raw, _, leaf := citeGateProps(g, e0, one)
		sec := ctx.Section(leaf)
		Cite(MakeFact(raw)).applyAction(ctx, sec)
		require.True(t, sec.Proved(), "Cite(<raw ⇒-form>) must still close the leaf")
	}
}

// TestCite_UnrelatedFactStillInstalls: the install stage is untouched —
// a fact that is NOT the leaf modulo Normalize (and closes nothing)
// installs as a hypothesis and leaves the leaf open, exactly as before.
func TestCite_UnrelatedFactStillInstalls(t *testing.T) {
	ctx, g, e0, one := citeGateEnv(t)
	_, _, leaf := citeGateProps(g, e0, one)
	y := Var("y", TypeInd)
	unrelated := core.TestThm(ext.ForAll(y)(g.Apply(g.Apply(y)).Eq(e0)))
	_ = one

	sec := ctx.Section(leaf)
	Cite(MakeFact(unrelated)).applyAction(ctx, sec)
	open := sec.unsolvedLeaf(0)
	require.NotNil(t, open, "an unrelated fact must install, not close")
	require.False(t, sec.Proved())
	found := false
	for h := range open.Goal.HypIter() {
		if h.AlphaEquals(unrelated.AsProp().Conclusion()) {
			found = true
		}
	}
	require.True(t, found, "the unrelated fact's conclusion must be resident after the install")
}

// TestCite_NormalizeCloseIsTargeted: stage 1.5 matches the CITED fact
// only. A resident cache entry that normalize-equals the leaf must NOT
// let a Cite of a DIFFERENT fact close through it — the recorded step's
// thm is what dep extraction reads, so a cache-wide match would
// silently re-attribute the dep.
func TestCite_NormalizeCloseIsTargeted(t *testing.T) {
	ctx, g, e0, one := citeGateEnv(t)
	raw, _, leaf := citeGateProps(g, e0, one)
	y := Var("y", TypeInd)
	unrelated := core.TestThm(ext.ForAll(y)(g.Apply(g.Apply(y)).Eq(e0)))
	_ = one

	// The leaf's own fact sits in the cache…
	ctx.ClaimProvedThm(raw)
	// …but the author cites something else: install, not close.
	sec := ctx.Section(leaf)
	Cite(MakeFact(unrelated)).applyAction(ctx, sec)
	require.False(t, sec.Proved(),
		"Cite must not close via a cached fact the author did not cite")
	require.NotNil(t, sec.unsolvedLeaf(0))
}

// TestCite_GroundedAtAPrefixDischargesItsHypotheses: a statement in the
// standard form cited at a prefix of its binders is installed as the
// telescope at that prefix (prop.PrefixTelescope), so the hypotheses
// about the grounded binders are discharged from the context and the
// instance stands with the rest — `∀y. Q(a, y) ⇒ R(a, y)` from
// `∀x y. P(x) ∧ Q(x, y) ⇒ R(x, y)` at a, with P(a) resident.
func TestCite_GroundedAtAPrefixDischargesItsHypotheses(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	pT, qT := MakeFun(TypeInd, TypeBool), MakeFun(TypeInd, MakeFun(TypeInd, TypeBool))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_cp_P", pT))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_cp_Q", qT))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_cp_R", qT))
	P, Q, R := ctx.Const("zz_cp_P", pT), ctx.Const("zz_cp_Q", qT), ctx.Const("zz_cp_R", qT)
	x, y, a, b := Var("x", TypeInd), Var("y", TypeInd), Var("a", TypeInd), Var("b", TypeInd)
	law := core.TestThm(ext.ForAll(x, y)(P.Apply(x).And(Q.Apply(x, y)).Imply(R.Apply(x, y))).Core())
	leaf := prop.MakeProp(R.Apply(a, b).Core(), P.Apply(a).Core())

	sec := ctx.Section(leaf)
	Cite(MakeFact(law), a).applyAction(ctx, sec)
	open := sec.unsolvedLeaf(0)
	require.NotNil(t, open, "the cite installs; the goal stays open")
	want := ext.ForAll(y)(Q.Apply(a, y).Imply(R.Apply(a, y))).Core()
	found := false
	for h := range open.Goal.HypIter() {
		if h.AlphaEquals(want) {
			found = true
		}
	}
	require.True(t, found, "the instance with P(a) discharged must be resident:\n%s", prop.PrintProp(open.Goal))
}
