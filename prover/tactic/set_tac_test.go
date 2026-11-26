package tactic

// Regression tests for the ∃-one-point fusion rule (set_tac_fuse.go),
// the membership-mode set_tac helper.
//
// The defect they pin: `apply set_tac` panicked "Should not happen."
// (HypExists's Assert) on goals about function spaces and powersets,
// instead of failing gracefully with Success:false. Three faces of one
// missing-normalization family inside tryFuseAt, all reachable from
// user-shaped goals via the membership driver's fire:
//
//  1. SWAPPED CONJUNCT ORDER (the panic met in a session).
//     existsOnePointFuse tries both orders of the outer AND; when the
//     match came through the swapped call (E:=r, R:=l), the original
//     body is AND(R, E) but π₁ rebuilt the discharged hyp as
//     HypAND0/1(E, R) = AND(E, R) — not α-equal — and HypExists's
//     HasHyp precondition panicked.
//     No β-redex needed: a clean `∃w. R(w) ∧ (P ∧ (w = T))` panicked.
//
//  2. β-REDEX IN THE REMAINDER R. RewriteConcl(DeepBeta) normalized
//     both sides of the bridge, so a β-redex inside R made
//     Lhs(bridgeR) = DeepBeta(R) ≠ R and the HypAND1(E,R).DeriveTrans
//     asserted against the un-normalized R.
//
//  3. β-REDEX IN THE WITNESS T. π₂ built `eqTT = (T = T)` and the
//     ∃-elim chain from RAW T while EwT was peeled from the DeepBeta'd
//     bodyT — the two diverged and the DeriveTrans asserted.
//
// Contract pinned here: existsOnePointFuse and the membership driver
// never panic on these inputs — they decline (nil) or fuse correctly
// (order-aware discharge + β-divergence guards). The last test pins
// that the canonical E-left shape still fuses, so the panic fix cannot
// regress into disabling the rule.

import (
	"runtime/debug"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// fuseTestVocab: the fuse itself needs no vocabulary, but the driver
// entry takes the recorded const list — pass the usual suspects.
var fuseTestVocab = []core.TermName{"set_member", "set_comprehension", "comprehension_spec", "subset", "image"}

// fuseNoPanic runs f and fails the test (rather than crashing it) if f
// panics — the graceful-failure contract these regressions pin.
func fuseNoPanic(t *testing.T, name string, f func()) {
	t.Helper()
	defer func() {
		if r := recover(); r != nil {
			t.Errorf("%s: panicked: %v\n%s", name, r, debug.Stack())
		}
	}()
	f()
}

// requireFuseSafe asserts the fuse handles term without panicking; when
// it does fuse, the bridge's LHS must be the input term (sanity).
func requireFuseSafe(t *testing.T, name string, term core.Term) {
	t.Helper()
	fuseNoPanic(t, name, func() {
		w := existsOnePointFuse(term)
		if w != nil && !prop.Lhs(w).AlphaEquals(term) {
			t.Errorf("%s: fuse bridge LHS diverged from input", name)
		}
	})
}

// TestExistsOnePointFuse_SwappedConjunctOrder is the minimal
// reproduction of face 1, the panic met in a session:
//
//	∃w. Z(w) ∧ (b ∧ (w = c))
//
// — the one-point shape with the comprehension conjunct on the RIGHT.
// k=0, no ∃u-prefix, no β-redex, no ε, no COND: the swap alone
// panicked before the order-aware fix.
func TestExistsOnePointFuse_SwappedConjunctOrder(t *testing.T) {
	A := core.TypeA()
	w := ext.Var("w", A)
	c := ext.Var("c", A)
	b := ext.Var("b", core.TypeBool())
	Z := ext.Var("Z", core.MakeFun(A, core.TypeBool()))

	term := ext.Exists(w)(ext.WrapTerm(Z.Apply(w)).And(b.And(w.Eq(c)))).Core()
	requireFuseSafe(t, "swapped-order minimal", term)
}

// TestExistsOnePointFuse_SwappedOrderSessionShape mirrors the original
// failing session's hypothesis LHS after membership expansion —
//
//	∃x. (x₀ = λy. g(x, y)) ∧ (∃u. p(u) ∧ (x = u))
//
// equation conjunct left (a function-typed equation whose RHS mentions
// the witness under a binder), comprehension conjunct right, one
// ∃u-prefix with the bound-var witness T = u.
func TestExistsOnePointFuse_SwappedOrderSessionShape(t *testing.T) {
	A := core.TypeA()
	B := core.MakeVarType("B")
	x := ext.Var("x", A)
	u := ext.Var("u", A)
	y := ext.Var("y", A)
	p := ext.Var("p", core.MakeFun(A, core.TypeBool()))
	g := ext.Var("g", core.MakeFun(A, A, B))
	x0 := ext.Var("x0", core.MakeFun(A, B))

	eqConj := x0.Eq(y.To(g.Apply(x, y)))
	comprehension := ext.Exists(u)(ext.WrapTerm(p.Apply(u)).And(x.Eq(u)))
	term := ext.Exists(x)(eqConj.And(comprehension)).Core()
	requireFuseSafe(t, "swapped-order session shape", term)
}

// TestExistsOnePointFuse_BetaRedexInRemainder pins face 2: a β-redex
// inside the remainder conjunct R.
//
//	∃w. (b ∧ (w = c)) ∧ (λz. Z(z))(w)
func TestExistsOnePointFuse_BetaRedexInRemainder(t *testing.T) {
	A := core.TypeA()
	w := ext.Var("w", A)
	c := ext.Var("c", A)
	z := ext.Var("z", A)
	b := ext.Var("b", core.TypeBool())
	Z := ext.Var("Z", core.MakeFun(A, core.TypeBool()))

	redexR := ext.WrapTerm(core.Apply(z.To(Z.Apply(z)), w))
	term := ext.Exists(w)(ext.WrapTerm(b.And(w.Eq(c)).Core()).And(redexR)).Core()
	requireFuseSafe(t, "beta-redex in R", term)
}

// TestExistsOnePointFuse_BetaRedexInWitness pins face 3: a β-redex
// inside the witness term T, with the comprehension conjunct in the
// "good" LEFT position (so π₁ succeeds and π₂'s raw-T/normalized-T
// divergence is reached).
//
//	∃w. (b ∧ (w = (λz. z)(c))) ∧ Z(w)
func TestExistsOnePointFuse_BetaRedexInWitness(t *testing.T) {
	A := core.TypeA()
	w := ext.Var("w", A)
	c := ext.Var("c", A)
	z := ext.Var("z", A)
	b := ext.Var("b", core.TypeBool())
	Z := ext.Var("Z", core.MakeFun(A, core.TypeBool()))

	redexT := ext.WrapTerm(core.Apply(z.To(z), c))
	term := ext.Exists(w)(ext.WrapTerm(b.And(w.Eq(redexT)).Core()).And(Z.Apply(w))).Core()
	requireFuseSafe(t, "beta-redex in T", term)
}

// TestExistsOnePointFuse_MembershipDriverNoPanic proves tactic-level
// reachability: the membership rewrite driver (the exact function on
// the wild panic's stack, set_tac_membership.go:200/:335) must survive
// goals carrying the swapped-order shape — in the conclusion and in a
// hypothesis (the wild panic fired while walking a hyp).
func TestExistsOnePointFuse_MembershipDriverNoPanic(t *testing.T) {
	A := core.TypeA()
	w := ext.Var("w", A)
	c := ext.Var("c", A)
	b := ext.Var("b", core.TypeBool())
	Z := ext.Var("Z", core.MakeFun(A, core.TypeBool()))

	swapped := ext.Exists(w)(ext.WrapTerm(Z.Apply(w)).And(b.And(w.Eq(c)))).Core()

	fuseNoPanic(t, "driver: swapped shape in conclusion", func() {
		MembershipSetTacExpand(t.Context(), MakeProp(swapped), fuseTestVocab)
	})
	fuseNoPanic(t, "driver: swapped shape in hyp", func() {
		MembershipSetTacExpand(t.Context(), MakeProp(b.Core(), swapped), fuseTestVocab)
	})
}

// TestExistsOnePointFuse_CleanShapeStillFuses is the coverage pin: the
// ∩-over-⋃ shape with the comprehension conjunct in the
// canonical LEFT position must KEEP fusing — a "fix" that silences the
// panics by disabling the rule would regress the membership mode's
// acceptance test and this pin.
//
//	∃w. (∃u. p(u) ∧ (w = u)) ∧ Z(w)   ⇔   ∃u. p(u) ∧ Z(u)
func TestExistsOnePointFuse_CleanShapeStillFuses(t *testing.T) {
	A := core.TypeA()
	w := ext.Var("w", A)
	u := ext.Var("u", A)
	p := ext.Var("p", core.MakeFun(A, core.TypeBool()))
	Z := ext.Var("Z", core.MakeFun(A, core.TypeBool()))

	E := ext.Exists(u)(ext.WrapTerm(p.Apply(u)).And(w.Eq(u)))
	term := ext.Exists(w)(ext.WrapTerm(E.Core()).And(Z.Apply(w))).Core()

	bridge := existsOnePointFuse(term)
	if bridge == nil {
		t.Fatal("canonical E-left one-point shape must fuse")
	}
	want := ext.Exists(u)(ext.WrapTerm(p.Apply(u)).And(Z.Apply(u))).Core()
	if !prop.Rhs(bridge).AlphaEquals(want) {
		t.Errorf("fused form diverged: got %v", prop.Rhs(bridge))
	}
	if bridge.NumHyps() != 0 {
		t.Errorf("fuse bridge must be hyp-free, has %d hyps", bridge.NumHyps())
	}
}
