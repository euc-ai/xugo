package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	extprop "github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// findHypIdx returns the index of the first hyp whose printed form
// contains marker. Hyp lists are canonically sorted, so tests locate
// hyps by content — the same way an agent reads them off `inspect`.
func findHypIdx(t *testing.T, s *Session, gid string, marker string) int {
	t.Helper()
	entry, ok := s.goalIndex[gid]
	require.True(t, ok, "goal %s not in index", gid)
	g := entry.node.Goal
	for i := 0; i < g.NumHyps(); i++ {
		if containsStr(ext.PrintTerm(g.Hyp(i)), marker) {
			return i
		}
	}
	t.Fatalf("no hyp containing %q", marker)
	return -1
}

func containsStr(s, sub string) bool {
	return len(sub) == 0 || (len(s) >= len(sub) && indexOf(s, sub) >= 0)
}

func indexOf(s, sub string) int {
	for i := 0; i+len(sub) <= len(s); i++ {
		if s[i:i+len(sub)] == sub {
			return i
		}
	}
	return -1
}

// TestByTactic_ResidentPremises_ClearFirstAndOneComposite: `by` with
// resident premises clears the unnamed ∀-noise hyp, closes by one
// refutation, and records ONE `by` composite ministep (no clear_hyps /
// cnf_refute expansion on the session tree).
func TestByTactic_ResidentPremises_ClearFirstAndOneComposite(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("p:bool, q:bool, (∀x:num. x = x), p, p ⇒ q ⊢ q")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	ip := findHypIdx(t, s, gid, "⇒")
	iq := findHypIdx(t, s, gid, "p")
	if iq == ip {
		// "p" also matches the implication — take the other bare-p hyp.
		g := s.goalIndex[gid].node.Goal
		for i := 0; i < g.NumHyps(); i++ {
			txt := ext.PrintTerm(g.Hyp(i))
			if i != ip && !containsStr(txt, "∀") {
				iq = i
				break
			}
		}
	}

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type: "by",
			ByHyps: []ByHypSpec{
				{HypIndex: &iq},
				{HypIndex: &ip},
			},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("by diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success)
	assert.Equal(t, 0, out.State.NumOpen, "p + p⇒q must refute to q")

	// The recorded tree carries exactly ONE ministep: the composite.
	var byCount, otherCount int
	var walk func(n *proof.GoalStackNode)
	walk = func(n *proof.GoalStackNode) {
		if desc := n.StepDescription(); desc != "" {
			if containsStr(desc, "By(") {
				byCount++
			} else {
				otherCount++
			}
		}
		for _, c := range n.Children() {
			walk(c)
		}
	}
	for _, sec := range s.sections {
		walk(sec.root)
	}
	assert.Equal(t, 1, byCount, "one recorded by composite")
	assert.Equal(t, 0, otherCount, "no expansion ministeps on the session tree")
}

// TestByTactic_WitnessedResidentPremise: grounding a resident ∀-hyp at
// witnesses inside the by (the math layer's f.At(w…)).
func TestByTactic_WitnessedResidentPremise(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// ∀-hyp gives p(x) at any x; ground at a to meet p(a) ⇒ q.
	res := dsl.ParsePropText("q:bool, a:num, p:(num → bool), (∀x:num. p(x)), p(a) ⇒ q ⊢ q")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	iall := findHypIdx(t, s, gid, "∀")
	iimp := findHypIdx(t, s, gid, "⇒")

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type: "by",
			ByHyps: []ByHypSpec{
				{HypIndex: &iall, Terms: []string{"a"}},
				{HypIndex: &iimp},
			},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("by diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success)
	assert.Equal(t, 0, out.State.NumOpen)
}

// TestByTactic_WitnessesGroundThroughAnAntecedent: a resident hyp's
// witnesses follow its stated binders through an antecedent, as the Go
// Fact.At reads them — `∀c. s(c) ⇒ ∀e. p(c, e)` at (a, b) grounds both,
// its guard s(a) discharged from the premises.
func TestByTactic_WitnessesGroundThroughAnAntecedent(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("q:bool, a:num, b:num, s:(num → bool), p:(num → num → bool), " +
		"(∀c:num. s(c) ⇒ ∀e:num. p(c, e)), s(a), p(a, b) ⇒ q ⊢ q")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	iall := findHypIdx(t, s, gid, "∀")
	iimp := findHypIdx(t, s, gid, "⇒ q")
	g := s.goalIndex[gid].node.Goal
	iguard := -1
	for i := 0; i < g.NumHyps(); i++ {
		if ext.PrintTerm(g.Hyp(i)) == "s(a)" {
			iguard = i
		}
	}
	require.GreaterOrEqual(t, iguard, 0)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type: "by",
			ByHyps: []ByHypSpec{
				{HypIndex: &iall, Terms: []string{"a", "b"}},
				{HypIndex: &iguard},
				{HypIndex: &iimp},
			},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("by diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success)
	assert.Equal(t, 0, out.State.NumOpen)
}

// TestInstantiate_WitnessesGroundThroughAnAntecedent: `instantiate`
// reads a tuple in the same stated order — the guard travels with the
// instance, as Specialize derives it.
func TestInstantiate_WitnessesGroundThroughAnAntecedent(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("a:num, b:num, s:(num → bool), p:(num → num → bool), " +
		"(∀c:num. s(c) ⇒ ∀e:num. p(c, e)) ⊢ p(a, b)")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	iall := findHypIdx(t, s, gid, "∀")

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "instantiate", HypIndex: &iall, Terms: []string{"a", "b"}},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "instantiate: %+v", out.Diagnostics)
	var hyps []string
	for _, g := range s.sections[len(s.sections)-1].root.UnsolvedLeaves() {
		for _, h := range g.Goal.Hyps() {
			hyps = append(hyps, ext.PrintTerm(h))
		}
	}
	assert.Contains(t, hyps, "s(a) ⇒ p(a, b)")
}

// TestByTactic_EmptyPremises_Errors: `by` without premises is an
// authoring error with its own message (a bare refutation is `auto`).
func TestByTactic_EmptyPremises_Errors(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("p:bool, p ⊢ p")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	refusal := stepRefusal(t, e, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "by"},
	})
	assert.Contains(t, refusal, "empty premise list")
}

// TestByTactic_MissingPremise_FailsCloseOrFail: naming only an
// irrelevant hyp leaves the closer without the load-bearing premise —
// close-or-fail, session untouched, diagnostics carry the cleared-hyp
// list (the By premise-economy message).
func TestByTactic_MissingPremise_FailsCloseOrFail(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("p:bool, q:bool, r:bool, r, p, p ⇒ q ⊢ q")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	ir := findHypIdx(t, s, gid, "r")

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:   "by",
			ByHyps: []ByHypSpec{{HypIndex: &ir}},
		},
	})
	require.NoError(t, err)
	assert.False(t, out.Success, "by must fail when the premise list omits the load-bearing hyps")

	stateRes, gerr := e.InspectState(ctx, info.ID)
	require.NoError(t, gerr)
	assert.Equal(t, 1, stateRes.NumOpen, "session goal must remain open after failed by")
}

// TestByTactic_SuccessReportsAnAvoidableRefute — a `by` that closes by
// refuting a leaf Basic() would have closed says so on SUCCESS, as the
// recorder's audit would after a key was written: the session is where
// the spelling is chosen. Spelled with the marker the close reports
// nothing.
func TestByTactic_SuccessReportsAnAvoidableRefute(t *testing.T) {
	ind := TypeInd
	R := ext.Var("R", core.MakeFun(ind, core.MakeFun(ind, core.TypeBool())))
	Q := ext.Var("Q", core.MakeFun(ind, core.TypeBool()))
	f := ext.Var("f", core.MakeFun(ind, ind))
	y, w, a := ext.Var("y", ind), ext.Var("w", ind), ext.Var("a", ind)
	hyp := ext.ForAll(y)(ext.ForAll(w)(ext.Not(R.Apply(w, y)).And(R.Apply(w, y).Or(Q.Apply(w)))))
	goal := extprop.MakeProp(Q.Apply(f.Apply(a)).Core(), hyp.Core())

	economy := func(shape *ByShapeReq) []Diagnostic {
		e := newEngine(testEnv())
		info, err := e.CreateSession(context.Background())
		require.NoError(t, err)
		s, _ := e.getSession(info.ID)
		s.mu.Lock()
		gid := s.AddGoal(goal)
		s.mu.Unlock()
		zero := 0
		res, err := e.ApplyStep(context.Background(), info.ID, &ApplyStepRequest{
			GoalID: gid,
			Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &zero}}, ByShape: shape},
		})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		require.Equal(t, "close", res.Effect)
		var out []Diagnostic
		for _, d := range res.Diagnostics {
			if d.Type == DiagByEconomy {
				out = append(out, d)
			}
		}
		return out
	}

	bare := economy(nil)
	if assert.Len(t, bare, 1, "one refuted leaf, one finding") {
		assert.Contains(t, bare[0].Message, "closes under Basic()")
		assert.Contains(t, bare[0].Message, `by_shape:{"normalized":true}`)
	}
	assert.Empty(t, economy(&ByShapeReq{Normalized: true}), "with the marker there is nothing to report")
}
