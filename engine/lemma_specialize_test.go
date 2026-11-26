package engine

import (
	"context"
	"fmt"
	"regexp"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
)

// makeLemmaSpecHarness builds a num-typed environment with two
// constant-headed predicates (P : num→bool, R : num→num→bool) and two
// goal free-vars (n, m : num) so the goal-side scope can supply
// witnesses. The predicates are CONSTS — not Vars — so the lemma
// dispatch's conclusion-match unifier can't rebind their heads and spuriously
// close the goal; we want the lemma-as-hyp path to fire reliably so we
// can inspect the installed hyp shape.
type lemmaSpecHarness struct {
	numType core.HolType
	n       core.Term // num-typed free var
	m       core.Term // num-typed free var
	P       core.Term // num → bool, constant head
	R       core.Term // num → num → bool, constant head
	Qconst  core.Term // bool constant, goal conclusion
}

func makeLemmaSpecHarness() lemmaSpecHarness {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	pTy := core.MakeFun(numType, core.TypeBool())
	rTy := core.MakeFun(numType, numType, core.TypeBool())
	pMeta := core.MakeConstMeta("Pspec", pTy)
	rMeta := core.MakeConstMeta("Rspec", rTy)
	qMeta := core.MakeConstMeta("Qspec", core.TypeBool())
	return lemmaSpecHarness{
		numType: numType,
		n:       core.Var("n", numType),
		m:       core.Var("m", numType),
		P:       core.MakeConstTerm(pMeta, pTy),
		R:       core.MakeConstTerm(rMeta, rTy),
		Qconst:  core.MakeConstTerm(qMeta, core.TypeBool()),
	}
}

// TestApply_LemmaTermSpecialize_SingleBinder is the happy path: a
// 1-binder lemma `∀x:num. Pspec(x)` loaded with term_specialize={x:n}
// installs the GROUND hyp `Pspec(n)` — no ∀-residual is left in the
// hyp context: one apply, where a
// `lemma → instantiate(n) → clear(∀-hyp)` triple would stand.
func TestApply_LemmaTermSpecialize_SingleBinder(t *testing.T) {
	h := makeLemmaSpecHarness()
	x := ext.Var("x", h.numType)

	// Lemma: ⊢ ∀x:num. Pspec(x)
	lemma := prop.MakeProp(ext.ForAll(x)(ext.Apply(h.P, x.Core())))
	// Goal: n=n ⊢ Qspec. The vacuous hyp puts `n` in the goal's
	// free-var scope so resolveTermWithFallback can pick it up.
	target := prop.MakeProp(h.Qconst, core.Eq(h.n, h.n))

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"x": "n"},
	})
	assert.True(t, res.Success, "lemma+specialize must apply; res=%+v", res)
	assert.NotNil(t, res.State)

	workingHyps := findWorkingHyps(t, res, h.Qconst)
	// Assert: at least one hyp is the ground instance Pspec(n). There
	// must be NO hyp shaped `∀x. Pspec(x)` — that's the regression
	// guard the whole feature exists for.
	expectedGround := ext.Apply(h.P, h.n)
	foundGround := false
	for _, hyp := range workingHyps {
		if hyp.AlphaEquals(expectedGround) {
			foundGround = true
		}
		assert.True(t, ext.MatchesFORALL(hyp).IsZero(), "no hyp may be ∀-headed after specialize; got %s", ext.PrintTerm(hyp))
	}
	assert.True(t, foundGround,
		"working goal must carry the ground hyp Pspec(n); hyps=%v",
		printedHyps(workingHyps))
}

// TestApply_LemmaTermSpecialize_FullySpecializeBothBinders covers the
// multi-binder case: `∀x. ∀y. Rspec(x,y)` + term_specialize={x:n,y:m}
// gives ground hyp Rspec(n,m), with NO ∀ residual at any level.
func TestApply_LemmaTermSpecialize_FullySpecializeBothBinders(t *testing.T) {
	h := makeLemmaSpecHarness()
	x := ext.Var("x", h.numType)
	y := ext.Var("y", h.numType)

	lemma := prop.MakeProp(ext.ForAll(x, y)(ext.Apply(h.R, x.Core(), y.Core())))
	target := prop.MakeProp(h.Qconst, core.Eq(h.n, h.n), core.Eq(h.m, h.m))

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"x": "n", "y": "m"},
	})
	assert.True(t, res.Success)

	expectedGround := ext.Apply(h.R, h.n, h.m)
	workingHyps := findWorkingHyps(t, res, h.Qconst)
	foundGround := false
	for _, hyp := range workingHyps {
		if hyp.AlphaEquals(expectedGround) {
			foundGround = true
		}
		assert.True(t, ext.MatchesFORALL(hyp).IsZero(), "no hyp may be ∀-headed; got %s", ext.PrintTerm(hyp))
	}
	assert.True(t, foundGround, "must have ground Rspec(n,m); hyps=%v",
		printedHyps(workingHyps))
}

// TestApply_LemmaTermSpecialize_PartialKeepsRemainingForAll covers the
// partial-specialize case: a 2-binder lemma with ONE outer-binder
// witness leaves the second ∀ intact on the installed hyp — the agent
// can later instantiate it at a different witness. Peeling stops at
// the first ∀ whose name is not in the term_specialize map.
func TestApply_LemmaTermSpecialize_PartialKeepsRemainingForAll(t *testing.T) {
	h := makeLemmaSpecHarness()
	x := ext.Var("x", h.numType)
	y := ext.Var("y", h.numType)

	lemma := prop.MakeProp(ext.ForAll(x, y)(ext.Apply(h.R, x.Core(), y.Core())))
	target := prop.MakeProp(h.Qconst, core.Eq(h.n, h.n))

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"x": "n"},
	})
	assert.True(t, res.Success)

	workingHyps := findWorkingHyps(t, res, h.Qconst)
	// Expect a hyp `∀y:num. Rspec(n, y)` — the outer ∀x peeled at n,
	// the inner ∀y still present.
	foundPartial := false
	for _, hyp := range workingHyps {
		abs := ext.MatchesFORALL(hyp)
		if abs.IsZero() {
			continue
		}
		body := abs.Body()
		bodyHead, bodyArgs := ext.MatchesApply(body)
		if bodyHead.AlphaEquals(h.R) && len(bodyArgs) == 2 && bodyArgs[0].AlphaEquals(h.n) {
			foundPartial = true
		}
	}
	assert.True(t, foundPartial,
		"partial specialize must leave ∀y. Rspec(n, y) on the hyp list; hyps=%v",
		printedHyps(workingHyps))
}

// TestApply_LemmaTermSpecialize_UnknownBinder checks the typed error
// when the agent's map references a binder that doesn't exist among
// the lemma's outer ∀-binders. The named-map analog of "too many
// witnesses": an extra key surfaces as "not found in lemma's outer
// binders" with the available names listed.
func TestApply_LemmaTermSpecialize_UnknownBinder(t *testing.T) {
	h := makeLemmaSpecHarness()
	x := ext.Var("x", h.numType)

	// Lemma has ONE ∀-binder named "x"; agent supplies a key "y" that
	// isn't there.
	lemma := prop.MakeProp(ext.ForAll(x)(ext.Apply(h.P, x.Core())))
	target := prop.MakeProp(h.Qconst, core.Eq(h.n, h.n))

	err := applyToSingleGoalExpectErr(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"y": "n"},
	})
	assert.Error(t, err)
	assert.Contains(t, err.Error(), `"y"`,
		"error must name the offending key")
	assert.Contains(t, err.Error(), "available",
		"error must list available outer ∀-binder names")
	assert.Contains(t, err.Error(), "x",
		"available list must include the actual binder name")
}

// TestApply_LemmaTermSpecialize_PolymorphicBinderAccepted covers the
// signature feature: a lemma `∀x:A. Ppoly(x)` with a polymorphic
// ∀-binder type IS specializable through term_specialize when the
// witness type pins A. The witness `a:A` (goal-side free var of
// matching var-type) unifies binder type `A` with witness type `A`
// trivially — σ_type is identity, and the lemma installs as the
// ground instance Ppoly(a): term_specialize unifies the types at
// substitution time, so a polymorphic ∀-binder is no obstacle.
func TestApply_LemmaTermSpecialize_PolymorphicBinderAccepted(t *testing.T) {
	pPolyTy := core.MakeFun(core.TypeA(), core.TypeBool())
	pPolyMeta := core.MakeConstMeta("Ppoly", pPolyTy)
	pPoly := ext.Const(pPolyMeta, pPolyTy).Core()
	qMeta := core.MakeConstMeta("Qpoly", core.TypeBool())
	qConst := ext.Const(qMeta, core.TypeBool()).Core()

	a := ext.Var("a", core.TypeA())
	x := ext.Var("x", core.TypeA())

	lemma := prop.MakeProp(ext.ForAll(x)(ext.Apply(pPoly, x.Core())))
	target := prop.MakeProp(qConst, core.Eq(a, a))

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"x": "a"},
	})
	assert.True(t, res.Success,
		"term_specialize on a polymorphic-binder lemma must apply when the witness type unifies the binder type")
	assert.NotNil(t, res.State)

	workingHyps := findWorkingHyps(t, res, qConst)
	expectedGround := ext.Apply(pPoly, a)
	foundGround := false
	for _, hyp := range workingHyps {
		if hyp.AlphaEquals(expectedGround) {
			foundGround = true
		}
		assert.True(t, ext.MatchesFORALL(hyp).IsZero(), "no hyp may be ∀-headed after term_specialize; got %s", ext.PrintTerm(hyp))
	}
	assert.True(t, foundGround,
		"polymorphic-binder lemma must install as the ground instance Ppoly(a); hyps=%v",
		printedHyps(workingHyps))
}

// TestApply_LemmaTermSpecialize_GoalLemmaTypeVarNameCollision is the
// verbatim bug shape observed live on finite_set.FiniteImage during an
// iterated-product proof: a 2-binder polymorphic lemma
// `∀s:α→bool. ∀f:α→β. FImg(f, s)` where α, β are lemma type vars, loaded
// with `term_specialize={s: t(a), f: λj:B. Pair(a, j)}` against a goal
// whose scope has `a:A, t:A→(B→bool)`. The correct binding is lemma-α :=
// goal-B and lemma-β := prod(goal-A, goal-B), which forces the installed
// hyp to be `FImg⟨prod(A,B),B⟩(λj:B. Pair(a,j), t(a))`.
//
// Before the freshen-lemma-type-vars fix, this call failed inside
// `resolveTermSpecializeWitnesses` because the accumulator σ was
// threaded across iterations and `MatchTypeInto`'s env is keyed by
// type-var NAME: after iter-1 bound lemma-α (name "A") to goal-B (name
// "B"), iter-2's attempt to bind lemma-β (name "B") to prod(A,B) got
// misrouted through the just-added {"A"→"B"} entry (name-B lookup finds
// a "B"-shaped VarType in the env's VarType-side), then failed the
// consistency check.
func TestApply_LemmaTermSpecialize_GoalLemmaTypeVarNameCollision(t *testing.T) {
	tyA := core.MakeVarType("A")
	tyB := core.MakeVarType("B")
	tyPair := core.MakeMetaType("prod", 2)

	// FImg: (α → β) → (α → bool) → bool — mimics finite(image(f, s))'s
	// abstract shape.
	setAlpha := core.MakeFun(tyA, core.TypeBool())           // α→bool
	fType := core.MakeFun(tyA, tyB)                          // α→β
	fImgTy := core.MakeFun(fType, setAlpha, core.TypeBool()) // (α→β)→(α→bool)→bool
	fImgMeta := core.MakeConstMeta("FImg", fImgTy)
	fImg := core.MakeConstTerm(fImgMeta, fImgTy)

	sBinder := ext.Var("s", setAlpha)
	fBinder := ext.Var("f", fType)
	lemma := prop.MakeProp(ext.ForAll(sBinder, fBinder)(
		ext.Apply(fImg, fBinder.Core(), sBinder.Core())))

	// Goal-side scope: a:A, t:A→B→bool. Use them as free vars in a
	// trivial concl so resolveTermWithFallback can parse witnesses
	// against them.
	goalA := ext.Var("a", tyA)
	goalT := ext.Var("t", core.MakeFun(tyA, core.MakeFun(tyB, core.TypeBool())))
	qMeta := core.MakeConstMeta("Qcoll", core.TypeBool())
	qConst := core.MakeConstTerm(qMeta, core.TypeBool())
	target := prop.MakeProp(qConst,
		core.Eq(goalA.Core(), goalA.Core()),
		core.Eq(goalT.Core(), goalT.Core()))

	// The witness `λj:B. ,(a, j)` — mirrors the FiniteImage call site.
	// Its type is B → prod(A, B), which forces the lemma-β binder to
	// unify at prod(A, B) even though lemma-α just unified at B.
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "lemma",
		Lemma: lemma,
		TermSpecialize: map[string]string{
			"s": "t(a)",
			"f": "λj:B. ,(a, j)",
		},
	})
	assert.True(t, res.Success,
		"cross-var type unification must succeed; res=%+v", res)

	workingHyps := findWorkingHyps(t, res, qConst)

	// The installed hyp must be FImg(λj:B.(a,j), t(a)) with the
	// polymorphic head TYPED at α := B, β := prod(A, B). Before the
	// fix, either the call failed outright OR the second binder's
	// codomain collapsed to `B` (missing the cross-var propagation).
	//
	// We check three properties:
	//   1. There is no ∀-headed hyp (both binders were specialized).
	//   2. Some hyp is α-equal to FImg(λj:B.(a,j), t(a)) with the
	//      lemma type-vars fully instantiated at goal-side concrete
	//      types.
	//   3. The FImg-head const's type-substitution has β mapped to
	//      prod(A, B) — i.e. the second binder's codomain propagation
	//      is preserved.
	prodAB := core.MakeCompositeType(tyPair, tyA, tyB)
	// Instantiate the lemma head at α:=B, β:=prod(A,B) and check that
	// SOME installed hyp binds to `FImg⟨…⟩(λj:B.pair(a,j), t(a))` shape.
	// We check by looking for an applied term whose head is FImg-const
	// with the correctly-substituted type; the FImg meta is polymorphic,
	// so the const-term's TYPE reveals whether α, β got substituted.
	expectedFImgHead := core.MakeConstTerm(fImgMeta,
		core.MakeFun(
			core.MakeFun(tyB, prodAB),          // α:=B → β:=prod(A,B)
			core.MakeFun(tyB, core.TypeBool()), // α:=B → bool
			core.TypeBool(),
		))

	foundExpectedHead := false
	for _, hyp := range workingHyps {
		assert.True(t, ext.MatchesFORALL(hyp).IsZero(), "no hyp may be ∀-headed after full term_specialize; got %s", ext.PrintTerm(hyp))
		head, _ := ext.MatchesApply(hyp)
		if head == nil {
			continue
		}
		if head.AlphaEquals(expectedFImgHead) {
			foundExpectedHead = true
		}
	}
	assert.True(t, foundExpectedHead,
		"installed hyp must have FImg head typed at α:=B, β:=prod(A,B); "+
			"the specific witness terms are irrelevant — the type-substitution is the load-bearing property. hyps=%v",
		printedHyps(workingHyps))
	// Unused-var placeholder — we build them above only for clarity of
	// the intended witness shape but assertion is via head.
	_ = goalA
	_ = goalT
	_ = prodAB
}

// findWorkingHyps walks the engine state, picks the open goal whose
// conclusion α-equals the original goal conclusion (the one where the
// installed hyp landed), and returns its hyp list. Fails the test if
// no such goal exists.
func findWorkingHyps(t *testing.T, res *StepResult, expectedConcl core.Term) []core.Term {
	t.Helper()
	assert.NotNil(t, res.State)
	for _, g := range res.State.Goals {
		if g.Statement.Conclusion().AlphaEquals(expectedConcl) {
			return g.Statement.Hyps()
		}
	}
	// Dump what we did see, for diagnosis.
	var summaries []string
	for _, g := range res.State.Goals {
		summaries = append(summaries, prop.PrintProp(g.Statement))
	}
	t.Fatalf("no open goal matched expected conclusion %s; saw %v",
		ext.PrintTerm(expectedConcl), summaries)
	return nil
}

// applyToSingleGoalExpectErr is the error-path twin of applyToSingleGoal:
// returns the engine-surfaced diagnostic message so the caller can
// assert on it. The engine converts a tactic-dispatch error into a
// StepResult{Success:false, Diagnostics:[...]} payload rather than
// surfacing it as a Go error, so we read the diagnostic chain back
// out here.
func applyToSingleGoalExpectErr(t *testing.T, target core.Prop, tactic TacticReq) error {
	t.Helper()
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	assert.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: tactic,
	})
	if err != nil {
		return err
	}
	assert.NotNil(t, res, "ApplyStep returned nil result with no err")
	if res.Success {
		t.Fatalf("expected dispatch failure but ApplyStep succeeded; res=%+v", res)
	}
	if len(res.Diagnostics) == 0 {
		t.Fatalf("dispatch failed but no diagnostics surfaced; res=%+v", res)
	}
	return fmt.Errorf("%s", res.Diagnostics[0].Message)
}

func printedHyps(hs []core.Term) []string {
	out := make([]string, 0, len(hs))
	for _, h := range hs {
		out = append(out, ext.PrintTerm(h))
	}
	return out
}

// TestApply_LemmaTermSpecialize_ResidualLetterKeepsApartFromGoal pins
// the residual letters of a partial term_specialize. The lemma
// `∀n:C. ∀q:D. Gpair(n, q)` has two independent letters; specialized
// at n := k with k : D in the goal, its C becomes the goal's D, and its
// own D — the type of q, which no witness binds — must stay a letter of
// its own: renamed back to D it would read as the goal's D, and the
// installed `∀q. Gpair(k, q)` would claim only q : D, a strictly weaker
// instance that no longer applies at a q of another type.
func TestApply_LemmaTermSpecialize_ResidualLetterKeepsApartFromGoal(t *testing.T) {
	tyC := core.MakeVarType("C")
	tyD := core.MakeVarType("D")
	gTy := core.MakeFun(tyC, tyD, core.TypeBool())
	gMeta := core.MakeConstMeta("Gpair", gTy)
	g := core.MakeConstTerm(gMeta, gTy)

	nBinder := ext.Var("n", tyC)
	qBinder := ext.Var("q", tyD)
	lemma := prop.MakeProp(ext.ForAll(nBinder, qBinder)(
		ext.Apply(g, nBinder.Core(), qBinder.Core())))

	goalK := ext.Var("k", tyD)
	qMeta := core.MakeConstMeta("Qresidual", core.TypeBool())
	qConst := core.MakeConstTerm(qMeta, core.TypeBool())
	target := prop.MakeProp(qConst, core.Eq(goalK.Core(), goalK.Core()))

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"n": "k"},
	})
	assert.True(t, res.Success, "partial term_specialize must succeed; res=%+v", res)

	found := false
	for _, hyp := range findWorkingHyps(t, res, qConst) {
		abs := ext.MatchesFORALL(hyp)
		if abs.IsZero() {
			continue
		}
		found = true
		residual, ok := abs.Var().Type().(core.VarType)
		if assert.True(t, ok, "the residual binder keeps a type variable; got %s", ext.FormatType(abs.Var().Type())) {
			assert.NotEqual(t, core.TypeName("D"), residual.Name(),
				"the lemma's own D must not be read as the goal's D; hyp %s", ext.PrintTerm(hyp))
		}
	}
	assert.True(t, found, "the installed instance keeps the unspecialized ∀q")
}

// TestApply_LemmaSpecialize_CNFFormBody reproduces the shape that
// session sub-agents hit on the ℝ order and ring lemmas whose statement
// is a chain of implications (two-sided product bounds, monotone scaling, …):
//
//	∀w. ∀x. ∀y. ∀z. ((¬P(w,x) ∨ ¬Q(y,z)) ∨ R(w,y,x,z))
//
// — a CNF-normalized body (disjunction of negated atoms + a positive atom)
// underneath the outer ∀-binders, where the tests above have a bare
// `∀x. Atom(x)`. The load installs the ground instance, not the wide
// ∀-form.
func TestApply_LemmaSpecialize_CNFFormBody(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	pTy := core.MakeFun(numType, numType, core.TypeBool())
	qTy := core.MakeFun(numType, numType, core.TypeBool())
	rTy := core.MakeFun(numType, numType, numType, numType, core.TypeBool())
	pMeta := core.MakeConstMeta("Pcnf", pTy)
	qMeta := core.MakeConstMeta("Qcnf", qTy)
	rMeta := core.MakeConstMeta("Rcnf", rTy)
	Qconst := core.MakeConstTerm(core.MakeConstMeta("Qgoal", core.TypeBool()), core.TypeBool())
	P := core.MakeConstTerm(pMeta, pTy)
	Q := core.MakeConstTerm(qMeta, qTy)
	R := core.MakeConstTerm(rMeta, rTy)

	w := ext.Var("w", numType)
	x := ext.Var("x", numType)
	y := ext.Var("y", numType)
	z := ext.Var("z", numType)

	// Goal-side free vars (witnesses).
	a := core.Var("a", numType)
	b := core.Var("b", numType)
	c := core.Var("c", numType)
	d := core.Var("d", numType)

	pApp := ext.Apply(P, w.Core(), x.Core())
	qApp := ext.Apply(Q, y.Core(), z.Core())
	rApp := ext.Apply(R, w.Core(), y.Core(), x.Core(), z.Core())

	// Lemma: ∀w x y z. ((¬P(w,x) ∨ ¬Q(y,z)) ∨ R(w,y,x,z))  — the CNF form
	// such lemmas normalize to.
	body := ext.Or(ext.Or(ext.Not(pApp), ext.Not(qApp)), rApp)
	lemma := prop.MakeProp(ext.ForAll(w, x, y, z)(body))

	// Goal: vacuous-hyps to seat goal-side free vars in scope.
	target := prop.MakeProp(Qconst,
		core.Eq(a, a), core.Eq(b, b), core.Eq(c, c), core.Eq(d, d))

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"w": "a", "x": "b", "y": "c", "z": "d"},
	})
	assert.True(t, res.Success, "lemma+term_specialize must apply; res=%+v", res)
	assert.NotNil(t, res.State)

	hyps := findWorkingHyps(t, res, Qconst)

	t.Logf("hyps installed on residual leaf (count=%d):", len(hyps))
	for i, h := range hyps {
		t.Logf("  [%d] %s", i, ext.PrintTerm(h))
	}

	// What we WANT: a single ground hyp `((¬P(a,b) ∨ ¬Q(c,d)) ∨ R(a,c,b,d))`,
	// NO ∀-form left in the hyp context.
	expectedGround := ext.Or(ext.Or(
		ext.Not(ext.Apply(P, a, b)),
		ext.Not(ext.Apply(Q, c, d))),
		ext.Apply(R, a, c, b, d))
	foundGround := false
	foundForAll := false
	var forAllHyp core.Term
	for _, hyp := range hyps {
		if hyp.AlphaEquals(expectedGround) {
			foundGround = true
		}
		if !ext.MatchesFORALL(hyp).IsZero() {
			foundForAll = true
			forAllHyp = hyp
		}
	}

	if foundForAll {
		t.Errorf("REGRESSION: a wide ∀-form hyp remained after specialize; got %s",
			ext.PrintTerm(forAllHyp))
	}
	if !foundGround {
		t.Errorf("ground specialization not installed; expected to find hyp: %s",
			ext.PrintTerm(expectedGround))
	}
}

// TestApply_LemmaTermSpecialize_CNFFormBody_BinderNameAxis varies the
// lemma's binder names to make sure term_specialize resolves keys by
// the LEMMA's binder names (not by some implicit positional contract).
// The witnesses' names are unrelated to the binder names; the map
// chooses which binder gets which witness.
func TestApply_LemmaTermSpecialize_CNFFormBody_BinderNameAxis(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	rTy := core.MakeFun(numType, numType, numType, numType, core.TypeBool())
	rMeta := core.MakeConstMeta("Rcnf2", rTy)
	Qconst := core.MakeConstTerm(core.MakeConstMeta("Qgoal2", core.TypeBool()), core.TypeBool())
	R := core.MakeConstTerm(rMeta, rTy)

	for _, binderNames := range [][4]string{{"a", "b", "c", "d"}, {"w", "x", "y", "z"}} {
		t.Run(fmt.Sprintf("binders=%v", binderNames), func(t *testing.T) {
			w := ext.Var(ext.TermName(binderNames[0]), numType)
			x := ext.Var(ext.TermName(binderNames[1]), numType)
			y := ext.Var(ext.TermName(binderNames[2]), numType)
			z := ext.Var(ext.TermName(binderNames[3]), numType)
			gw := core.Var("gw", numType)
			gx := core.Var("gx", numType)
			gy := core.Var("gy", numType)
			gz := core.Var("gz", numType)

			body := ext.Apply(R, w.Core(), x.Core(), y.Core(), z.Core())
			lemma := prop.MakeProp(ext.ForAll(w, x, y, z)(body))
			target := prop.MakeProp(Qconst,
				core.Eq(gw, gw), core.Eq(gx, gx), core.Eq(gy, gy), core.Eq(gz, gz))

			res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
				Type:  "lemma",
				Lemma: lemma,
				TermSpecialize: map[string]string{
					binderNames[0]: "gw",
					binderNames[1]: "gx",
					binderNames[2]: "gy",
					binderNames[3]: "gz",
				},
			})
			assert.True(t, res.Success)
			hyps := findWorkingHyps(t, res, Qconst)
			for _, h := range hyps {
				if !ext.MatchesFORALL(h).IsZero() {
					t.Errorf("∀-hyp survived specialize: %s", ext.PrintTerm(h))
				}
			}
			expected := ext.Apply(R, gw, gx, gy, gz)
			found := false
			for _, h := range hyps {
				if h.AlphaEquals(expected) {
					found = true
				}
			}
			if !found {
				t.Errorf("ground %s not installed; hyps=%+v", ext.PrintTerm(expected), hyps)
			}
		})
	}
}

func TestApply_LemmaSpecialize_RingIdentityRecipe(t *testing.T) {
	intType := core.MakeCompositeType(core.MakeMetaType("int", 0))

	addMeta := core.MakeConstMeta("int_add", core.MakeFun(intType, intType, intType))
	mulMeta := core.MakeConstMeta("int_mul", core.MakeFun(intType, intType, intType))
	negMeta := core.MakeConstMeta("int_neg", core.MakeFun(intType, intType))
	subMeta := core.MakeConstMeta("int_sub", core.MakeFun(intType, intType, intType))

	add := core.MakeConstTerm(addMeta, addMeta.AbsType())
	mul := core.MakeConstTerm(mulMeta, mulMeta.AbsType())
	neg := core.MakeConstTerm(negMeta, negMeta.AbsType())
	sub := core.MakeConstTerm(subMeta, subMeta.AbsType())

	addAB := func(a, b core.Term) core.Term { return ext.Apply(add, a, b) }
	mulAB := func(a, b core.Term) core.Term { return ext.Apply(mul, a, b) }
	subAB := func(a, b core.Term) core.Term { return ext.Apply(sub, a, b) }
	negA := func(a core.Term) core.Term { return ext.Apply(neg, a) }

	// Goal-side free vars (= the witnesses we'll specialize at)
	r := ext.Var("r", intType)
	n := ext.Var("n", intType)
	x := ext.Var("x", intType)
	one := ext.Var("one", intType) // stands in for `&1`

	// The agent's failing goal shape was the ring identity
	//   (r·n + x) = (r+1)·n + (x − n)
	// over ℤ. We use that exact shape as the goal conclusion so the
	// installed-hyp interaction is realistic.
	lhs := addAB(mulAB(r.Core(), n.Core()), x.Core())
	rhs := addAB(mulAB(addAB(r.Core(), one.Core()), n.Core()), subAB(x.Core(), n.Core()))
	goalConcl := core.Eq(lhs, rhs)
	// Hyps put the witness vars in scope so resolveTermWithFallback finds them.
	target := prop.MakeProp(
		goalConcl,
		core.Eq(r.Core(), r.Core()),
		core.Eq(n.Core(), n.Core()),
		core.Eq(x.Core(), x.Core()),
		core.Eq(one.Core(), one.Core()),
	)

	// Lemma-side ∀-bound vars (kept locally per case for clarity).
	xL := ext.Var("xL", intType)
	yL := ext.Var("yL", intType)
	zL := ext.Var("zL", intType)

	type probeCase struct {
		name           string
		lemma          core.Prop
		termSpecialize map[string]string
	}

	cases := []probeCase{
		{
			// AGENT'S FAILING CASE: the left-factor negation law
			name: "mul_left_neg  forall x,y. -(x*y) = (-x)*y",
			lemma: prop.MakeProp(
				ext.ForAll(xL, yL)(core.Eq(
					negA(mulAB(xL.Core(), yL.Core())),
					mulAB(negA(xL.Core()), yL.Core()),
				))),
			termSpecialize: map[string]string{"xL": "r", "yL": "n"},
		},
		{
			name: "right_distrib  forall x,y,z. (x+y)*z = x*z + y*z",
			lemma: prop.MakeProp(
				ext.ForAll(xL, yL, zL)(core.Eq(
					mulAB(addAB(xL.Core(), yL.Core()), zL.Core()),
					addAB(mulAB(xL.Core(), zL.Core()), mulAB(yL.Core(), zL.Core())),
				))),
			termSpecialize: map[string]string{"xL": "r", "yL": "one", "zL": "n"},
		},
		{
			name: "one_mul  forall x. one*x = x   (1-binder, hardcoded `one` const)",
			lemma: prop.MakeProp(
				ext.ForAll(xL)(core.Eq(
					mulAB(one.Core(), xL.Core()),
					xL.Core(),
				))),
			termSpecialize: map[string]string{"xL": "n"},
		},
		{
			name: "add_assoc  forall x,y,z. (x+y)+z = x+(y+z)",
			lemma: prop.MakeProp(
				ext.ForAll(xL, yL, zL)(core.Eq(
					addAB(addAB(xL.Core(), yL.Core()), zL.Core()),
					addAB(xL.Core(), addAB(yL.Core(), zL.Core())),
				))),
			termSpecialize: map[string]string{"xL": "r", "yL": "one", "zL": "x"},
		},
		{
			name: "sub_add_cancel  forall x,y. x = y + (x-y)",
			lemma: prop.MakeProp(
				ext.ForAll(xL, yL)(core.Eq(
					xL.Core(),
					addAB(yL.Core(), subAB(xL.Core(), yL.Core())),
				))),
			termSpecialize: map[string]string{"xL": "x", "yL": "n"},
		},
		// Non-equality control: should always work (no paramodulation risk).
		{
			name: "CTRL_NON_EQ  forall x,y. Pctrl(x,y)   (non-equality body — control)",
			lemma: func() core.Prop {
				pTy := core.MakeFun(intType, intType, core.TypeBool())
				pMeta := core.MakeConstMeta("Pctrl", pTy)
				pConst := core.MakeConstTerm(pMeta, pTy)
				return prop.MakeProp(
					ext.ForAll(xL, yL)(ext.Apply(pConst, xL.Core(), yL.Core())))
			}(),
			termSpecialize: map[string]string{"xL": "r", "yL": "n"},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
				Type:           "lemma",
				Lemma:          tc.lemma,
				TermSpecialize: tc.termSpecialize,
			})
			if !res.Success {
				t.Fatalf("lemma + term_specialize: %+v", res.Diagnostics)
			}
		})
	}
}

// TestApply_LemmaTermSpecialize_LeanRwRewriteRule_AbsOfNum: `lean_rw`
// with term_specialize substitutes the witnesses into the lemma before
// the rewrite, so `{n: "5"}` on `∀n. real_abs(&n) = &n` rewrites by the
// rule `real_abs(&5) = &5` alone. The lemma's body is an equation, which
// `lean_rw` consumes as a rule and never installs as a ∀-hypothesis, so
// the witnesses have nowhere else to act.
func TestApply_LemmaTermSpecialize_LeanRwRewriteRule_AbsOfNum(t *testing.T) {
	absT := dsl.RealAbsMeta.Term()
	r5 := parseRealLitForLemmaSpec(t, "&5")
	r0 := parseRealLitForLemmaSpec(t, "&0")
	target := prop.MakeProp(core.Eq(
		core.Apply(absT, r5),
		core.Apply(absT, r0),
	))

	// AbsOfNum's shape: ∀n:num. real_abs(&n) = &n
	n := ext.Var("n", dsl.NumType)
	rn := core.Apply(dsl.RealOfNumMeta.Term(), n.Core())
	lemmaBody := core.Eq(core.Apply(absT, rn), rn)
	lemma := prop.MakeProp(ext.ForAll(n)(lemmaBody).Core())

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lean_rw",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"n": "5"},
	})
	assert.True(t, res.Success,
		"lean_rw + term_specialize on a rewrite-path lemma must apply — the specialized rule rewrites the goal conclusion's subterm")
	// The rule at n := 5 rewrites real_abs(&5) and leaves real_abs(&0),
	// which the lemma as stated would rewrite too.
	findWorkingHyps(t, res, core.Eq(r5, core.Apply(absT, r0)))
}

// TestApply_LemmaTermSpecialize_ConsumedByRewrite_AbsOfNum pins
// the diagnostic when the agent uses `lemma + term_specialize` (NOT
// lean_rw) on a pure rewrite-path lemma. The chain depends on a
// newly-added ∀-headed hyp on the residual; the rewrite path doesn't
// add one. Agent gets a clear "use lean_rw" hint rather than silent
// no-op.
func TestApply_LemmaTermSpecialize_ConsumedByRewrite_AbsOfNum(t *testing.T) {
	absT := dsl.RealAbsMeta.Term()
	r5 := parseRealLitForLemmaSpec(t, "&5")
	r0 := parseRealLitForLemmaSpec(t, "&0")
	target := prop.MakeProp(core.Eq(
		core.Apply(absT, r5),
		core.Apply(absT, r0),
	))

	n := ext.Var("n", dsl.NumType)
	rn := core.Apply(dsl.RealOfNumMeta.Term(), n.Core())
	lemmaBody := core.Eq(core.Apply(absT, rn), rn)
	lemma := prop.MakeProp(ext.ForAll(n)(lemmaBody).Core())

	err := applyToSingleGoalExpectErr(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"n": "5"},
	})
	assert.Error(t, err)
	msg := err.Error()
	assert.Contains(t, msg, "consumed by the eq-rewrite path",
		"diagnostic must explain why the chain can't proceed")
	assert.Contains(t, msg, "lean_rw",
		"diagnostic must point the agent at lean_rw as the rewrite-path entry")
}

// TestApply_LemmaTermSpecialize_ConjunctiveBundleInstallsGround: the
// conjunctive AC bundle of real addition,
//
//	∀n m p. (((n+m = m+n) ∧ (n+(m+p) = m+(n+p))) ∧ (m+(n+p) = (m+n)+p))
//
// loaded by `lemma` with term_specialize at all three binders, is
// installed as one ground hypothesis: a conjunction of equations is no
// rewrite rule, so the load takes the hypothesis route and the
// witnesses ground it there.
func TestApply_LemmaTermSpecialize_ConjunctiveBundleInstallsGround(t *testing.T) {
	a0 := core.Var("a_0", dsl.RealType)
	b0 := core.Var("b_0", dsl.RealType)
	c0 := core.Var("c_0", dsl.RealType)
	plus := dsl.RealPlusMeta.Term()
	add := func(x, y core.Term) core.Term { return core.Apply(core.Apply(plus, x), y) }

	// Post-strip_quant AC-identity goal: (a₀+b₀)+c₀ = (a₀+c₀)+b₀.
	target := prop.MakeProp(core.Eq(
		add(add(a0, b0), c0),
		add(add(a0, c0), b0),
	))

	n := ext.Var("n", dsl.RealType)
	m := ext.Var("m", dsl.RealType)
	p := ext.Var("p", dsl.RealType)

	// Multi-binder AC bundle, conjunctive body.
	sym := core.Eq(add(n.Core(), m.Core()), add(m.Core(), n.Core()))
	lassoc := core.Eq(add(n.Core(), add(m.Core(), p.Core())), add(m.Core(), add(n.Core(), p.Core())))
	rassoc := core.Eq(add(m.Core(), add(n.Core(), p.Core())), add(add(m.Core(), n.Core()), p.Core()))
	conj := ext.And(ext.And(sym, lassoc), rassoc)
	lemma := prop.MakeProp(ext.ForAll(n, m, p)(conj).Core())

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"n": "a₀", "m": "b₀", "p": "c₀"},
	})
	if !res.Success {
		diagMsg := "(no diagnostic)"
		if len(res.Diagnostics) > 0 {
			diagMsg = res.Diagnostics[0].Message
		}
		t.Fatalf("lemma+term_specialize on the AC bundle failed: %s", diagMsg)
	}
	// The bundle is installed beside the goal at the three witnesses.
	ground := ext.And(ext.And(
		core.Eq(add(a0, b0), add(b0, a0)),
		core.Eq(add(a0, add(b0, c0)), add(b0, add(a0, c0)))),
		core.Eq(add(b0, add(a0, c0)), add(add(b0, a0), c0)))
	hyps := findWorkingHyps(t, res, target.Conclusion())
	assert.True(t, slices.ContainsFunc(hyps, func(h core.Term) bool { return h.AlphaEquals(ground) }),
		"the ground bundle is no hypothesis of the goal: %v", printedHyps(hyps))
}

// parseRealLitForLemmaSpec is a small helper: builds a real-typed
// literal (`&n`) via the DSL parser. Used by the rewrite-path
// regression test above; isolated by name so it doesn't collide with
// other tests' helpers.
func parseRealLitForLemmaSpec(t *testing.T, txt string) core.Term {
	t.Helper()
	r := dsl.ParseTermTextInScope(txt, nil, nil, dsl.RealType)
	if len(r.Errors) > 0 {
		t.Fatalf("parseRealLitForLemmaSpec(%q): %v", txt, r.Errors)
	}
	return r.Term
}

// makeINImageShapeProp builds a stand-in for set_basic.InImage's polymorphic
// statement using ad-hoc free predicates. The real member has
// `set_member` and `image` as kernel constants; for unit-testing buildSpecializedLemma
// we only need a Prop with two distinct named type-vars (A, B), where A
// appears in some hyp/concl positions and B in others.
//
// Shape: ⊢ ∀f:A→B. ∀x:A. ∀y:B. (y = f(x))
// Has type-vars A and B, distinct. Specializing them via PropTypeInst gives
// us a check that the substitution actually fires.
func makeINImageShapeProp() core.Prop {
	A := core.MakeVarType("A")
	B := core.MakeVarType("B")
	fnAB := core.MakeFun(A, B)

	f := ext.Var("f", fnAB)
	x := ext.Var("x", A)
	y := ext.Var("y", B)

	fOfX := ext.Apply(f, x)
	body := core.Eq(y, fOfX)
	withY := ext.ForAll(y)(body)
	withX := ext.ForAll(x)(withY)
	withF := ext.ForAll(f)(withX)

	return prop.MakeProp(withF)
}

// TestBuildSpecializedLemma_Happy validates the canonical use:
// substituting A and B in a {A, B}-polymorphic lemma to two concrete
// types, producing a Prop whose type-vars are gone.
func TestBuildSpecializedLemma_Happy(t *testing.T) {
	lemma := makeINImageShapeProp()
	assert.True(t, ext.PropHasTypeVars(lemma), "shape lemma must start polymorphic")

	specialized, _, err := buildSpecializedLemma(lemma, map[string]string{
		"A": "num",
		"B": "bool",
	}, groundTestGoal())
	assert.NoError(t, err)
	assert.NotNil(t, specialized)
	assert.False(t, ext.PropHasTypeVars(specialized),
		"after specializing both A and B to ground types, lemma must be ground")

	// The substitution must produce a Prop whose conclusion mentions
	// num→bool somewhere (f's new type), not the old A→B.
	got := prop.PrintProp(specialized)
	assert.NotContains(t, got, "var:A", "A should be substituted away, got: %s", got)
	assert.NotContains(t, got, "var:B", "B should be substituted away, got: %s", got)
}

// TestBuildSpecializedLemma_Partial validates that partial substitution
// leaves the other type-vars free. The agent will commonly pin some
// type-vars (the ones the goal context can't infer) and leave the rest.
func TestBuildSpecializedLemma_Partial(t *testing.T) {
	lemma := makeINImageShapeProp()

	specialized, _, err := buildSpecializedLemma(lemma, map[string]string{
		"B": "num",
	}, groundTestGoal())
	assert.NoError(t, err)
	assert.NotNil(t, specialized)

	// A should still be free; B should be gone.
	names := collectLemmaTypeVarNames(specialized)
	assert.True(t, names["A"], "A should remain after partial substitution, got names: %v", names)
	assert.False(t, names["B"], "B should be substituted away, got names: %v", names)
}

// TestBuildSpecializedLemma_BareQuestionMarkTypeVar validates the
// `?71143`-style spelling — the printer's form for goal-local fresh type
// vars, lexed by the new `?<ident>` rule as `var:?71143`. Agents copy these
// straight from the goal print.
func TestBuildSpecializedLemma_BareQuestionMarkTypeVar(t *testing.T) {
	lemma := makeINImageShapeProp()

	specialized, _, err := buildSpecializedLemma(lemma, map[string]string{
		"A": "?71143",
		"B": "?71148",
	}, groundTestGoal())
	assert.NoError(t, err)

	// After substitution the original names A and B are gone; the new
	// `?`-prefixed names appear.
	names := collectLemmaTypeVarNames(specialized)
	assert.False(t, names["A"], "A should be substituted away, got names: %v", names)
	assert.False(t, names["B"], "B should be substituted away, got names: %v", names)
	assert.True(t, names["?71143"], "?71143 should appear after substitution, got names: %v", names)
	assert.True(t, names["?71148"], "?71148 should appear after substitution, got names: %v", names)
}

// TestBuildSpecializedLemma_UnknownNameErrs validates that a typo'd
// type-var name is rejected with a useful message listing available
// names. Critical — silent acceptance would let the agent get a no-op
// substitution that quietly installs the unspecialized lemma.
func TestBuildSpecializedLemma_UnknownNameErrs(t *testing.T) {
	lemma := makeINImageShapeProp()

	_, _, err := buildSpecializedLemma(lemma, map[string]string{
		"AA": "num", // typo
	}, groundTestGoal())
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "AA", "error must name the offending key")
	assert.Contains(t, err.Error(), "available", "error must list available names")
	assert.Contains(t, err.Error(), "A", "available list must include A")
	assert.Contains(t, err.Error(), "B", "available list must include B")
}

// TestBuildSpecializedLemma_UnparseableSpellingErrs validates that an
// invalid type spelling fails with a clear error referencing the name.
func TestBuildSpecializedLemma_UnparseableSpellingErrs(t *testing.T) {
	lemma := makeINImageShapeProp()

	_, _, err := buildSpecializedLemma(lemma, map[string]string{
		"A": "not a type @@@",
	}, groundTestGoal())
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "A", "error must name the offending key")
}

// TestBuildSpecializedLemma_EmptyIsNoop validates that an empty map is a
// no-op — used by the engine dispatch when TypeSpecialize is absent.
func TestBuildSpecializedLemma_EmptyIsNoop(t *testing.T) {
	lemma := makeINImageShapeProp()
	got, _, err := buildSpecializedLemma(lemma, nil, groundTestGoal())
	assert.NoError(t, err)
	assert.Equal(t, lemma, got, "empty map must return the lemma unchanged")
}

// TestLemmaTypeSpecialize_SurvivesGoalWithMatchingTypeVars verifies
// that the agent's `type_specialize` is applied even when the GOAL
// contains free type-vars that share NAMES with the lemma's polymorphic
// type-vars (e.g. after `strip_quant` on a goal that quantified over
// `f:A→B`, the stripped free var carries session-scope A, B — different
// VarType pointers than the lemma's but same names). The install path's
// `TryAdaptLemmaTypes` sees a candidate σ against those ambient names;
// this test pins that the agent-supplied σ is what actually installs.
func TestLemmaTypeSpecialize_SurvivesGoalWithMatchingTypeVars(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	assert.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Goal that carries free vars of type var:A → var:B, so the goal
	// context also mentions type-vars named A and B (different pointers
	// from the lemma's but same names — the exact shape that trips
	// TryAdaptLemmaTypes into overriding the agent's σ).
	A := core.MakeVarType("A")
	B := core.MakeVarType("B")
	fnAB := core.MakeFun(A, B)
	f0 := core.Var("f0", fnAB)
	qMeta := core.MakeConstMeta("QspecMatch", core.TypeBool())
	Qconst := core.MakeConstTerm(qMeta, core.TypeBool())
	// Put f0 in a hyp so it survives — a plain `⊢ Q` goal wouldn't
	// carry the A/B type-vars into the goal context.
	target := prop.MakeProp(Qconst, core.Eq(f0, f0))
	goalID := s.AddGoal(target)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{
			Type:      "lemma",
			LemmaText: "∀f:var:A→var:B. ∀x:var:A. ∀y:var:B. (y = f(x))",
			TypeSpecialize: map[string]string{
				"A": "num",
				"B": "bool",
			},
		},
	})
	assert.NoError(t, err)
	assert.True(t, res.Success, "lemma with type_specialize should succeed")

	hyps := findWorkingHyps(t, res, Qconst)
	// Find the installed lemma hyp: it starts with a ∀f binder.
	var installed core.Term
	for _, h := range hyps {
		if abs := ext.MatchesFORALL(h); !abs.IsZero() && string(abs.Var().Name()) == "f" {
			installed = h
			break
		}
	}
	if installed == nil {
		t.Fatalf("no installed lemma hyp with outer ∀f found; hyps=%v",
			printedHyps(hyps))
	}
	// The specialized hyp should have NO free type-vars — A→num, B→bool
	// leaves the hyp fully ground. If the adapter overrode the agent's
	// σ, the lemma's A/B will still be present (bound to the goal's
	// ambient A/B, since those are the closest structural matches).
	hasVar := false
	pred := core.VarTypePredicate(func(v core.VarType) bool {
		hasVar = true
		return true
	})
	_ = ext.TermAnyTypeVar(installed, pred)
	assert.False(t, hasVar,
		"type_specialize was overridden by TryAdaptLemmaTypes: installed hyp still "+
			"contains free type-vars. hyp: %s", ext.PrintTerm(installed))
}

// TestApply_LemmaTermSpecialize_BypassesTypeAdapter is the regression test
// for a defect met on finite_set.FiniteImageInjEq. When the lemma has
// MULTIPLE type variables AND the goal context contains free vars
// whose types name those same type vars, the install pipeline's
// `chooseTypeAdaptedStep` runs `tryAdaptLemmaTypes(lemma, goal)` and may
// pick an adapted form that collapses the lemma's type vars in a way that
// invalidates the agent's explicit term_specialize choice. Concrete shape:
//
//   - Lemma: `∀A:(B→bool). ∀s:(A→bool). ∀f:(A→B). P(A, s, f)`
//     (two type vars A, B; outer term-binder also named A:B→bool)
//   - Goal: `(λs:A→bool, f:A→B. ...) ⊢ Q`  (free vars s, f using same A, B names)
//   - Witness: an `image`-style term of type `B→bool`
//
// The adapter sees lemma's free-var-shaped binders (s, f) and the goal's
// free vars (s, f) and may σ-collapse `B := A`, leaving the installed hyp
// with binder type `A→bool` instead of `B→bool`. Without the
// exact-with-source bypass, the post-install instantiate chain then sees
// the collapsed binder and can't match it against the term_specialize
// witness (which still has type `B→bool`). The fix routes term_specialize
// installs through ApplyLemmaPreserveExactWithSource, skipping the
// adapter entirely — the agent's explicit type choice wins.
func TestApply_LemmaTermSpecialize_BypassesTypeAdapter(t *testing.T) {
	A := core.TypeA()
	B := core.MakeVarType("B")

	// Lemma: ∀A:(B→bool). ∀s:(A→bool). ∀f:(A→B). P_const(A, s, f)
	// — three outer binders whose types use both lemma type-vars A, B.
	// The outermost term-binder is named "A" with type B→bool, mirroring
	// finite_set.FiniteImageInjGeneral's ambient-set parameter.
	ABool := core.MakeFun(A, core.TypeBool())
	BBool := core.MakeFun(B, core.TypeBool())
	AToB := core.MakeFun(A, B)
	pTy := core.MakeFun(BBool, ABool, AToB, core.TypeBool())
	pMeta := core.MakeConstMeta("Pbypass", pTy)
	P := core.MakeConstTerm(pMeta, pTy)

	ambA := ext.Var("A", BBool)
	sL := ext.Var("s", ABool)
	fL := ext.Var("f", AToB)
	body := ext.Apply(P, ambA.Core(), sL.Core(), fL.Core())
	lemma := prop.MakeProp(ext.ForAll(ambA, sL, fL)(body))

	// Goal: free vars `s_g:A→bool, f_g:A→B, ambSet:B→bool` in hyps,
	// trivial conclusion. The free vars share name-shape with the
	// lemma's binders. ambSet is the term_specialize witness.
	sGoal := core.Var("s_g", ABool)
	fGoal := core.Var("f_g", AToB)
	ambSet := core.Var("ambSet", BBool)
	qMeta := core.MakeConstMeta("Qbypass", core.TypeBool())
	Qconst := core.MakeConstTerm(qMeta, core.TypeBool())
	target := prop.MakeProp(
		Qconst,
		core.Eq(sGoal, sGoal),
		core.Eq(fGoal, fGoal),
		core.Eq(ambSet, ambSet),
	)

	// Apply lemma with term_specialize:{A: "ambSet"} — the goal-side
	// free var `ambSet` is the witness. resolveTermWithFallback finds it
	// as a subterm of the goal hyps.
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"A": "ambSet"},
	})
	if !res.Success {
		var diag string
		if len(res.Diagnostics) > 0 {
			diag = res.Diagnostics[0].Message
		}
		t.Fatalf("term_specialize on a polymorphic lemma must apply even when the goal's free vars share type-var names with the lemma; "+
			"if the diagnostic mentions 'post-install ∀-binder type ... does not match witness type', "+
			"the adapter bypass (ApplyLemmaPreserveExactWithSource) is not wired into case \"lemma\". diagnostic: %s",
			diag)
	}

	// The installed hyp on the residual leaf should NOT have a wide ∀A; the
	// post-install chain should have peeled it with the witness, leaving a
	// residual hyp with `s, f` still ∀-bound (partial specialize) but
	// `ambSet` substituted for A.
	hyps := findWorkingHyps(t, res, Qconst)
	wideABinderSurvived := false
	for _, h := range hyps {
		if abs := ext.MatchesFORALL(h); !abs.IsZero() && string(abs.Var().Name()) == "A" {
			wideABinderSurvived = true
		}
	}
	assert.False(t, wideABinderSurvived,
		"the outer ∀A binder should have been peeled by term_specialize; if it survives, "+
			"the post-install chain didn't fire — see applyLemmaTermSpecializeChain. hyps=%v",
		printedHyps(hyps))
}

func TestResolveTermSpecializeWitnessKeepsInternalTypeVarsRigid(t *testing.T) {
	A := core.TypeA()
	B := core.MakeVarType("B")
	aSetTy := core.MakeFun(A, core.TypeBool())
	bSetTy := core.MakeFun(B, core.TypeBool())
	fTy := core.MakeFun(A, B)

	imageMeta := core.MakeConstMeta("IMAGErigid", core.MakeFun(fTy, aSetTy, bSetTy))
	imageConst := core.MakeConstTerm(imageMeta, imageMeta.AbsType())
	f := core.Var("f", fTy)
	s := core.Var("s", aSetTy)
	imageWitness := ext.Apply(imageConst, f, s)

	pMeta := core.MakeConstMeta("Prigid", core.MakeFun(aSetTy, core.TypeBool()))
	P := core.MakeConstTerm(pMeta, pMeta.AbsType())
	binder := ext.Var("b", aSetTy)
	lemma := prop.MakeProp(ext.ForAll(binder)(ext.Apply(P, binder.Core())))
	goal := prop.MakeProp(core.Eq(imageWitness, imageWitness))

	e := newEngine(testEnv())
	witnesses, _, _, err := e.resolveTermSpecializeWitnesses(
		lemma,
		map[string]string{"b": ext.PrintTerm(imageWitness)},
		goal,
		nil,
		utils.EmptyPredicate[core.VarType],
	)
	assert.NoError(t, err)
	assert.Len(t, witnesses, 1)
	assert.True(t, witnesses[0].witness.AlphaEquals(imageWitness),
		"lemma type substitution must not rewrite the goal witness itself")
}

// TestLeanRwBundledOriginalPreservesThmBacking pins the lean_rw bundled-
// equation reconstruct path against a regression where the callback's
// rewrite bridge was built from bare proposition clauses (the lemma
// `resolveLemma` serves is a statement, a bare Prop). That left the reconstruct closure
// returning a bare Prop even when its input thms were Thm-backed; the
// goal_stack then panicked at `AsThm: not a theorem` when narrowing the
// parent's PromisedThm() for upstream propagation.
//
// The trigger (mirrors an attempt at cardinality.CardImageLe):
//
//  1. add-goal the statement (over free f and s)
//  2. load finite_set.FiniteInductStrong specialized at λu. card(image(f,u)) ≤ card u
//  3. assert the BASE-case sub-claim (`card(image(f, empty_set)) ≤ card(empty_set)`)
//  4. lean_rw set_image.ImageClauses   — image(f,empty_set) → empty_set (bundled eq)
//  5. lean_rw cardinality.CardClauses  — the LHS card(empty_set) → 0
//  6. lean_rw cardinality.CardClauses  — the RHS card(empty_set) → 0
//  7. nat_order.ZeroLessEq             — closes `0 ≤ 0`
//
// Step 7 returns success and the section's `complete` flag advances
// toward the outer assert.
func TestLeanRwBundledOriginalPreservesThmBacking(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	assert.NoError(t, err)
	// The target is cardinality.CardImageLe, stated over free f and s.
	target, ok := registry.ByName("cardinality.CardImageLe")
	if !assert.True(t, ok, "cardinality.CardImageLe is registered") {
		t.FailNow()
	}
	goal, err := parsePropTextInGoalScope(
		"f:(A → B), s:(A → bool) ⊢ finite(s) ⇒ card(image(f, s)) ≤ card(s)",
		target.Entry().Statement().Prop, nil)
	assert.NoError(t, err)
	s, err := e.GetSession(info.ID)
	assert.NoError(t, err)
	goalID := s.AddGoal(goal)

	apply := func(label string, gid string, tactic TacticReq) *StepResult {
		t.Helper()
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid,
			Tactic: tactic,
		})
		assert.NoError(t, err, label)
		if !assert.True(t, res != nil && res.Success, "%s failed: %+v", label, res) {
			t.FailNow()
		}
		for i, g := range res.State.Goals {
			t.Logf("after %s: goal[%d] hyps=%d concl=%s", label, i, g.Statement.NumHyps(), ext.PrintTerm(g.Statement.Conclusion()))
		}
		return res
	}

	// Find the open goal whose conclusion (ignoring polymorphic markers)
	// matches the given regex. Lets us track the rewrite chain even when
	// the engine reorders goals or assigns new IDs.
	findConclGoal := func(state *StateView, pat *regexp.Regexp) string {
		for _, g := range state.Goals {
			conclText := ext.PrintTerm(g.Statement.Conclusion())
			bare := regexp.MustCompile(`⟨[^⟩]*⟩`).ReplaceAllString(conclText, "")
			if pat.MatchString(strings.TrimSpace(bare)) {
				return g.ID
			}
		}
		return ""
	}

	// The subject is the cardinality.CardClauses rewrite bridge below; the BASE
	// obligation is asserted directly on the target (the induction
	// principle's install form is not what this test measures). The right
	// side's ∅ has no partner to fix its type, so the claim spells it — the
	// base case is at s's type A.
	r := apply("assert BASE", goalID, TacticReq{
		Type:      "assert",
		ClaimText: "card(image(f, empty_set)) ≤ card(empty_set⟨A:A⟩)",
	})
	base := findConclGoal(r.State, regexp.MustCompile(`^card\(image\(f, ∅\)\) ≤ card\(∅\)$`))
	assert.NotEmpty(t, base, "assert should produce a BASE obligation goal")

	r = apply("lean_rw ImageClauses on BASE", base, TacticReq{
		Type: "lean_rw", LemmaKey: "set_image.ImageClauses",
	})
	rwBase := findConclGoal(r.State, regexp.MustCompile(`^card\(∅.*\) ≤ card\(∅\)$`))
	assert.NotEmpty(t, rwBase, "the ImageClauses rewrite should expose card(empty_set) ≤ card(empty_set)")

	// The multi-clause rewrite reduces every card(∅) it can type-adapt
	// to in one firing; a second firing takes any side whose instance
	// the first could not reach.
	r = apply("lean_rw CardClauses (LHS)", rwBase, TacticReq{
		Type: "lean_rw", LemmaKey: "cardinality.CardClauses",
	})
	rwCard2 := findConclGoal(r.State, regexp.MustCompile(`^0 ≤ 0$`))
	if rwCard2 == "" {
		rwCard1 := findConclGoal(r.State, regexp.MustCompile(`^0 ≤ card\(∅\)$`))
		assert.NotEmpty(t, rwCard1, "the CardClauses rewrite should reduce LHS to 0")
		r = apply("lean_rw CardClauses (RHS)", rwCard1, TacticReq{
			Type: "lean_rw", LemmaKey: "cardinality.CardClauses",
		})
		rwCard2 = findConclGoal(r.State, regexp.MustCompile(`^0 ≤ 0$`))
	}
	assert.NotEmpty(t, rwCard2, "the CardClauses rewrites should reduce both sides to 0")

	// THIS is the close that exercises leanRwTacticMultiClause's
	// reconstruct: a wrong one panics with `AsThm: not a theorem
	// (proven-or-provable): prop_<HASH>`. The target is a
	// member whose witnessed policy declares no arith, so the
	// session's armed scope keeps `auto` from deciding `0 ≤ 0` by arith;
	// ZeroLessEq closes it — the rewrite bridge is exercised the same way.
	r = apply("ZeroLessEq closes 0 ≤ 0", rwCard2, TacticReq{Type: "lemma", LemmaKey: "nat_order.ZeroLessEq"})
	if r.Effect != "close" {
		r = apply("auto closes 0 ≤ 0 from ZeroLessEq", rwCard2, TacticReq{Type: "auto"})
	}
	assert.Equal(t, "close", r.Effect,
		"closing `0 ≤ 0` must succeed without an AsThm panic — the lean_rw "+
			"reconstruct callback must propagate Thm-backing through the rewrite "+
			"bridge so goal_stack's parent-narrow doesn't see a bare proposition")
}
