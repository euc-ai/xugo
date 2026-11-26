package engine

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// groundTestGoal is a goal spelling no type letter, for a
// type_specialize whose targets are read against no goal in particular.
func groundTestGoal() core.Prop {
	return prop.MakeProp(core.MakeConstTerm(core.MakeConstMeta("ground_test_goal", core.TypeBool()), core.TypeBool()))
}

// A lemma over the letters A and B, ∀n:num. ∀x:A. ∀y:B. Gtri(n, x, y),
// cited at a goal holding k : A and w : num, with type_specialize
// naming the goal's A and term_specialize grounding n at w. The
// instance installs at the goal's A — the letter asked for, not one
// renamed apart from it — whether or not B is named too, and a witness
// at num for a binder of the goal's A is refused: the goal's letter is
// rigid.
func TestApply_LemmaTypeSpecialize_GoalLetterHeldUnderTermSpecialize(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	tyA, tyB := core.MakeVarType("A"), core.MakeVarType("B")
	gTy := core.MakeFun(numType, tyA, tyB, core.TypeBool())
	g := core.MakeConstTerm(core.MakeConstMeta("Gtri", gTy), gTy)
	n, x, y := ext.Var("n", numType), ext.Var("x", tyA), ext.Var("y", tyB)
	lemma := prop.MakeProp(ext.ForAll(n, x, y)(ext.Apply(g, n.Core(), x.Core(), y.Core())))

	k, w := core.Var("k", tyA), core.Var("w", numType)
	qConst := core.MakeConstTerm(core.MakeConstMeta("Qtri", core.TypeBool()), core.TypeBool())
	target := prop.MakeProp(qConst, core.Eq(k, k), core.Eq(w, w))

	// installed applies the cite and returns the installed instance's
	// binder types: x's, then y's.
	installed := func(t *testing.T, tactic TacticReq) (core.HolType, core.HolType) {
		res, _, _, _ := applyToSingleGoal(t, target, tactic)
		require.True(t, res.Success, "res=%+v", res)
		for _, hyp := range findWorkingHyps(t, res, qConst) {
			abs := ext.MatchesFORALL(hyp)
			if abs.IsZero() {
				continue
			}
			inner := ext.MatchesFORALL(abs.Body())
			require.False(t, inner.IsZero(), "the instance keeps ∀y under ∀x; got %s", ext.PrintTerm(hyp))
			return abs.Var().Type(), inner.Var().Type()
		}
		t.Fatalf("no ∀-headed hypothesis installed")
		return nil, nil
	}

	t.Run("both letters named", func(t *testing.T) {
		xTy, yTy := installed(t, TacticReq{Type: "lemma", Lemma: lemma,
			TypeSpecialize: map[string]string{"A": "A", "B": "num"},
			TermSpecialize: map[string]string{"n": "w"}})
		assert.True(t, tyA.Equals(xTy), "x : A, the goal's letter; got %s", ext.FormatType(xTy))
		assert.True(t, numType.Equals(yTy), "y : num; got %s", ext.FormatType(yTy))
	})
	t.Run("one letter named", func(t *testing.T) {
		xTy, yTy := installed(t, TacticReq{Type: "lemma", Lemma: lemma,
			TypeSpecialize: map[string]string{"A": "A"},
			TermSpecialize: map[string]string{"n": "w"}})
		assert.True(t, tyA.Equals(xTy), "x : A, the goal's letter; got %s", ext.FormatType(xTy))
		assert.True(t, tyB.Equals(yTy), "y : B, the lemma's own letter, which the goal does not spell; got %s", ext.FormatType(yTy))
	})
	t.Run("a witness at another type is refused", func(t *testing.T) {
		err := applyToSingleGoalExpectErr(t, target, TacticReq{Type: "lemma", Lemma: lemma,
			TypeSpecialize: map[string]string{"A": "A"},
			TermSpecialize: map[string]string{"n": "w", "x": "w"}})
		assert.Contains(t, err.Error(), "does not fit the binder")
	})
}

// A `by` premise over the letter A — a finite set's subsets are finite,
// behind a guard on n — named with type_specialize at the goal's A and
// term_specialize grounding n. The premise installs at the goal's A,
// where the leaf's sets live, and the close reads it there twice, down
// the chain U₀ ⊆ T₀ ⊆ S₀; a hypothesis's type letters being rigid in the
// leaf, a premise at a letter renamed apart from A would reach none of
// them. The leaf is no instance of the law, so the session's auto-match
// leaves it to the close.
func TestBy_PremiseTypeSpecializeGoalLetterHeldUnderTermSpecialize(t *testing.T) {
	const law = "∀n:num. 0 < n ⇒ ∀s t:set(A). finite(s) ∧ t ⊆ s ⇒ finite(t)"
	e, s := boundSession(t, "sets/set_basic")
	addTextGoal(t, s, law)
	source := s.sections[0].root
	require.True(t, proof.ApplyCiteKnown(source, core.TestThm(source.Goal.Conclusion())))
	addTextGoal(t, s, "∀w:num. ∀S T U:set(A). 0 < w ∧ finite(S) ∧ T ⊆ S ∧ U ⊆ T ⇒ finite(U)")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	premise := LemmaWithSpec{Text: law,
		TypeSpecialize: map[string]string{"A": "A"},
		TermSpecialize: map[string]string{"n": "w₀"}}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)}, WithLemmas: []LemmaWithSpec{premise}})
	require.True(t, s.sections[1].root.Proved())
}

// The rewrite-rule path lean_rw, auto_with and simp_with share holds the
// letter an explicit type_specialize read at the goal's the same way:
// the rule ∀n:num. ∀x:A. Gf(n, x) = Gg(n, x), named at the goal's A and
// grounded at n := w, keeps ∀x at A.
func TestBuildTermSpecializedLemma_GoalLetterHeld(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	tyA := core.MakeVarType("A")
	fTy := core.MakeFun(numType, tyA, tyA)
	f := core.MakeConstTerm(core.MakeConstMeta("Gf", fTy), fTy)
	g := core.MakeConstTerm(core.MakeConstMeta("Gg", fTy), fTy)
	n, x := ext.Var("n", numType), ext.Var("x", tyA)
	lemma := prop.MakeProp(ext.ForAll(n, x)(core.Eq(ext.Apply(f, n.Core(), x.Core()), ext.Apply(g, n.Core(), x.Core()))))
	k, w := core.Var("k", tyA), core.Var("w", numType)
	goal := prop.MakeProp(core.Eq(ext.Apply(f, w, k), ext.Apply(g, w, k)))

	e := newEngine(testEnv())
	specialized, fixed, err := buildSpecializedLemma(lemma, map[string]string{"A": "A"}, goal)
	require.NoError(t, err)
	rule, err := e.buildTermSpecializedLemma(specialized, map[string]string{"n": "w"}, goal, nil, fixed)
	require.NoError(t, err)
	abs := ext.MatchesFORALL(rule.Conclusion())
	require.False(t, abs.IsZero(), "the rule keeps ∀x; got %s", prop.PrintProp(rule))
	assert.True(t, tyA.Equals(abs.Var().Type()), "x : A, the goal's letter; got %s", ext.FormatType(abs.Var().Type()))
}
