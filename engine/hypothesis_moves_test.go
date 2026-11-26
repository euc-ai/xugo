package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"
)

// recordedSteps is the flat step list the session's one section recorded.
func recordedSteps(t *testing.T, e *Engine, sid string) []*proof.StepProto {
	t.Helper()
	s, err := e.getSession(sid)
	require.NoError(t, err)
	detailed := s.sections[0].root.DetailedProofProto()
	require.NotNil(t, detailed)
	return detailed.GetSteps()
}

// applyAt applies a tactic to one goal and returns the result, which
// the test reads for success or refusal.
func applyAt(t *testing.T, e *Engine, sid, gid string, tactic TacticReq) (*StepResult, error) {
	t.Helper()
	return e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: tactic})
}

// ringHypIndex is the index, in the session's sole open goal, of the
// hypothesis that is the ring's structure fact — the hyp list is kept
// sorted, so an install renumbers it.
func ringHypIndex(t *testing.T, e *Engine, sid string) int {
	t.Helper()
	state, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	for i := range state.Goals[0].Statement.NumHyps() {
		if strings.HasPrefix(ext.PrintTerm(state.Goals[0].Statement.Hyp(i)), "comm_ring(") {
			return i
		}
	}
	t.Fatalf("no ring hypothesis in %s", ext.PrintTerm(state.Goals[0].Statement.Conclusion()))
	return -1
}

// TestLemmaReadAt_ClosesTheGoalTheReadingStates: `lemma {key, read_at}`
// on a goal that IS the reading's conclusion closes it on the cite —
// Go's `Cite(Law.Read(h))` — under the resident structure hypothesis and
// at an instance entry alike, and the record is a known theorem that
// carries the reading. Refused on the old code: `lemma` took no
// read_at.
func TestLemmaReadAt_ClosesTheGoalTheReadingStates(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	zero := 0

	t.Run("under a resident hypothesis", func(t *testing.T) {
		stmt := "R:ring_ops(A) ⊢ comm_ring(R) ⇒ ∀x:A. R.zero * x = R.zero"
		sid, gid := bareArithLeaf(t, e, stmt, "strip_imp")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: &zero}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, "close", res.Effect)
		assert.Equal(t, 0, res.State.NumOpen)
		steps := recordedSteps(t, e, sid)
		var closes int
		for _, st := range steps {
			if k, ok := st.Step.(*proof.StepProto_KnownThm); ok {
				closes++
				require.NotNil(t, k.KnownThm.GetReading(), "the close records what it was read from")
				assert.NotNil(t, k.KnownThm.GetReading().GetUnder(), "a reading under the hypothesis")
			}
		}
		assert.Equal(t, 1, closes, "one known-theorem close: %d steps", len(steps))
	})
	t.Run("at an instance entry", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, "∀x:real. &0 * x = &0")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{Key: "real_ring.CommRing"}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, 0, res.State.NumOpen)
		for _, st := range recordedSteps(t, e, sid) {
			if k, ok := st.Step.(*proof.StepProto_KnownThm); ok {
				assert.NotNil(t, k.KnownThm.GetReading().GetInstance(), "a reading at the entry")
			}
		}
	})
}

// readingRightZeroLeaf is a ring's right absorption under the structure
// hypothesis: a goal the left absorption law's reading neither closes
// nor rewrites, so a cite of that reading installs it.
const readingRightZeroLeaf = "R:ring_ops(A) ⊢ comm_ring(R) ⇒ ∀y:A. y * R.zero = R.zero"

// TestLemmaReadAt_InstallsTheReadingForTheMovesThatFollow: on a goal the
// reading does not state, `lemma {key, read_at}` installs the reading
// as a resident hypothesis — Go's `a.Simplified(Law.Read(h))` — the
// hypothesis the reading is under kept beside it, and the moves that
// follow address the new hypothesis; a term_specialize prefix grounds
// it at the tuple with the ∀-source dropped (Go's `.At(w…)`). The
// record is the exact install, the reading's known-theorem claim and,
// grounded, the specialize. An install whose chain closes the goal at
// the very instance the tuple names is accepted, as Go's witnessed
// Cite accepts it.
func TestLemmaReadAt_InstallsTheReadingForTheMovesThatFollow(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	zero := 0
	at := &ReadAtSpec{HypIndex: &zero}
	// closeByRightZero closes the sole open goal by the right absorption
	// law read at the ring hypothesis, wherever the installs left it.
	closeByRightZero := func(t *testing.T, sid, gid string) {
		t.Helper()
		ring := ringHypIndex(t, e, sid)
		closed, err := applyAt(t, e, sid, gid, TacticReq{Type: "by",
			WithLemmas: []LemmaWithSpec{{Key: "comm_ring.MulRightZero", ReadAt: &ReadAtSpec{HypIndex: &ring}}}})
		require.NoError(t, err)
		require.True(t, closed.Success, "diagnostics: %+v", closed.Diagnostics)
	}

	t.Run("bare", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, readingRightZeroLeaf, "strip_imp")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: at})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, "simplify", res.Effect)
		require.Len(t, res.NewHyps, 1, "the reading joins the hypotheses")
		installed := res.NewHyps[0]
		assert.Equal(t, "∀x. R.zero * x = R.zero", installed.Term)
		require.Len(t, res.Produced, 1)
		// A move that follows addresses the installed hypothesis.
		grounded, err := applyAt(t, e, sid, res.Produced[0].GoalID,
			TacticReq{Type: "instantiate", HypIndex: &installed.Index, Terms: []string{"R.one"}})
		require.NoError(t, err)
		require.True(t, grounded.Success, "diagnostics: %+v", grounded.Diagnostics)
		require.Len(t, grounded.NewHyps, 1)
		assert.Equal(t, "R.zero * R.one = R.zero", grounded.NewHyps[0].Term)
		closeByRightZero(t, sid, grounded.Produced[0].GoalID)

		var install, claim bool
		for _, st := range recordedSteps(t, e, sid) {
			switch k := st.Step.(type) {
			case *proof.StepProto_LemmaPreserve:
				install = true
			case *proof.StepProto_KnownThm:
				if k.KnownThm.GetReading().GetLaw() != nil {
					claim = true
				}
			}
		}
		assert.True(t, install, "the preserving install is recorded")
		assert.True(t, claim, "the claim child closes on the reading's record")
	})
	t.Run("grounded at a tuple", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, readingRightZeroLeaf, "strip_imp")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: at,
			TermSpecialize: map[string]string{"x": "R.one"}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		require.Len(t, res.NewHyps, 1)
		assert.Equal(t, "R.zero * R.one = R.zero", res.NewHyps[0].Term, "the ground instance, the ∀-source dropped")
		assert.Equal(t, 1, res.Produced[0].Changes.HypsAdded)
		closeByRightZero(t, sid, res.Produced[0].GoalID)
		var grounds bool
		for _, st := range recordedSteps(t, e, sid) {
			if _, ok := st.Step.(*proof.StepProto_Specialize); ok {
				grounds = true
			}
		}
		assert.True(t, grounds, "the grounding is a recorded specialize")
	})
	t.Run("the install closes the goal at the tuple's instance", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, readingRingLeaf, "strip_imp")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: at,
			TermSpecialize: map[string]string{"x": "x"}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, "close", res.Effect)
	})
	t.Run("refusals", func(t *testing.T) {
		for name, tactic := range map[string]TacticReq{
			"a text law":                   {Type: "lemma", LemmaText: "∀x:A. R.zero * x = R.zero", ReadAt: at},
			"type_specialize beside it":    {Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: at, TypeSpecialize: map[string]string{"A": "num"}},
			"a binder pinned by name":      {Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: at, TermSpecialize: map[string]string{"y": "x"}},
			"an instance that is no entry": {Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{Key: "no_such.Entry"}},
		} {
			t.Run(name, func(t *testing.T) {
				sid, gid := bareArithLeaf(t, e, readingRingLeaf, "strip_imp")
				res, err := applyAt(t, e, sid, gid, tactic)
				require.NoError(t, err)
				require.False(t, res.Success, "refused by name")
				require.NotEmpty(t, res.Diagnostics)
				t.Log(res.Diagnostics[0].Message)
			})
		}
	})
}

// TestSplitConj_AtAHypothesis: `split_conj {hyp_index}` splits THAT
// conjunctive hypothesis into its flat conjuncts — Go's
// `a.Conjuncts(fact, …)`: the conjuncts join the hypotheses, the
// conjunction stays, the conclusion is not touched, and the record is
// the verb's, one assert per conjunct closed by `By(Normalized, fact)`.
// On the old code the index was ignored and the move split the
// conclusion, which is no conjunction here ("split_conj does not apply:
// goal shape does not match"). Refused now in the verb's words for a
// conjunct that is the conclusion or already resident, and for a
// hypothesis that is no conjunction.
func TestSplitConj_AtAHypothesis(t *testing.T) {
	e := newEngine(testEnv())
	zero := 0

	sid, gid := bareArithLeaf(t, e, "∀P Q R:bool. P ∧ Q ∧ R ⇒ R ∨ P", "strip_quant", "strip_imp")
	res, err := applyAt(t, e, sid, gid, TacticReq{Type: "split_conj", HypIndex: &zero})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	require.Len(t, res.Produced, 1, "one residual, the conclusion untouched")
	assert.Equal(t, 3, res.Produced[0].Changes.HypsAdded)
	assert.Equal(t, 0, res.Produced[0].Changes.HypsDropped, "the conjunction stays, as in Go")
	assert.False(t, res.Produced[0].Changes.ConclusionChanged)
	state, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	leaf := state.Goals[0].Statement
	assert.Equal(t, "R₀ ∨ P₀", ext.PrintTerm(leaf.Conclusion()))
	require.Equal(t, 4, leaf.NumHyps())
	p := hypIndexPrinting(t, e, sid, "P₀")
	closed, err := applyAt(t, e, sid, state.Goals[0].ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(p)},
		ByShape: &ByShapeReq{Normalized: true}})
	require.NoError(t, err)
	require.True(t, closed.Success, "diagnostics: %+v", closed.Diagnostics)
	var asserts, normalizedBys int
	for _, st := range recordedSteps(t, e, sid) {
		switch k := st.Step.(type) {
		case *proof.StepProto_Assert:
			asserts++
		case *proof.StepProto_By:
			if k.By.GetShape() != nil && len(k.By.GetPremises()) == 1 && k.By.GetPremises()[0].GetResident() {
				normalizedBys++
			}
		case *proof.StepProto_SplitHypConj:
			t.Fatalf("a.Conjuncts records no split step")
		}
	}
	assert.Equal(t, 3, asserts, "one assert per conjunct")
	assert.Equal(t, 4, normalizedBys, "each conjunct closed from the conjunction, then the close")

	t.Run("a conjunct that is the conclusion", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, "∀P Q:bool. P ∧ Q ⇒ Q", "strip_quant", "strip_imp")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "split_conj", HypIndex: &zero})
		require.NoError(t, err)
		require.False(t, res.Success)
		assert.Contains(t, res.Diagnostics[0].Message, "is the goal's conclusion")
	})
	t.Run("a conjunct already resident", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, "∀P Q R:bool. P ⇒ P ∧ Q ⇒ R", "strip_quant", "strip_imp", "strip_imp")
		state, err := e.InspectState(context.Background(), sid)
		require.NoError(t, err)
		conj := -1
		for i := range state.Goals[0].Statement.NumHyps() {
			if _, _, ok := ext.MatchesAND(state.Goals[0].Statement.Hyp(i)); ok {
				conj = i
			}
		}
		require.GreaterOrEqual(t, conj, 0)
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "split_conj", HypIndex: &conj})
		require.NoError(t, err)
		require.False(t, res.Success)
		assert.Contains(t, res.Diagnostics[0].Message, "is already resident")
	})
	t.Run("a conjunct that repeats an earlier one", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, "∀P Q R:bool. (P ∧ Q) ∧ P ⇒ R", "strip_quant", "strip_imp")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "split_conj", HypIndex: &zero})
		require.NoError(t, err)
		require.False(t, res.Success)
		assert.Contains(t, res.Diagnostics[0].Message, "repeats an earlier conjunct")
	})
	t.Run("a hypothesis that is no conjunction", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, "∀P Q:bool. P ⇒ Q ∧ P", "strip_quant", "strip_imp")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "split_conj", HypIndex: &zero})
		require.NoError(t, err)
		require.False(t, res.Success)
		assert.Contains(t, res.Diagnostics[0].Message, "is not A ∧ B")
	})
	t.Run("without an index the conclusion splits as before", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, "∀P Q:bool. P ⇒ Q ⇒ Q ∧ P", "strip_quant", "strip_imp", "strip_imp")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "split_conj"})
		require.NoError(t, err)
		require.True(t, res.Success)
		assert.Len(t, res.Produced, 2)
	})
}

// TestDefExpand_AtAHypothesis: `def_expand {const, hyp_index}` opens the
// constant in THAT hypothesis alone — Go's `a.Unfolded(fact, "c")`: the
// unfolded statement joins the hypotheses, the folded one stays, the
// conclusion is untouched, and the record is the assert the verb makes
// with its claim closed by the unfold. On the old code the index was
// ignored and the goal unfolded in place.
func TestDefExpand_AtAHypothesis(t *testing.T) {
	e, s := boundSession(t, "sets/set_product")
	addTextGoal(t, s, "∀s:set(A). ∀t:set(B). ∀x:A. ∀y:B. (x, y) ∈ set_cross(s, t) ⇒ x ∈ s")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	zero := 0
	res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "def_expand", Const: "set_cross", HypIndex: &zero})
	require.Len(t, res.Produced, 1)
	assert.Equal(t, 1, res.Produced[0].Changes.HypsAdded)
	assert.Equal(t, 0, res.Produced[0].Changes.HypsDropped, "the folded hypothesis stays")
	assert.False(t, res.Produced[0].Changes.ConclusionChanged)
	require.Len(t, res.NewHyps, 1)
	assert.NotContains(t, res.NewHyps[0].Term, "set_cross", "the new hypothesis is the unfolded one: %s", res.NewHyps[0].Term)
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	folded := false
	for i := range state.Goals[0].Statement.NumHyps() {
		if strings.Contains(ext.PrintTerm(state.Goals[0].Statement.Hyp(i)), "set_cross") {
			folded = true
		}
	}
	assert.True(t, folded, "the folded hypothesis is still resident")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{{HypIndex: &res.NewHyps[0].Index}},
		WithLemmas: []LemmaWithSpec{{Key: "pairs.PairEq"}}})
	require.True(t, s.sections[0].root.Proved())

	var asserted, unfolded bool
	for _, st := range s.sections[0].root.DetailedProofProto().GetSteps() {
		switch st.Step.(type) {
		case *proof.StepProto_Assert:
			asserted = true
		case *proof.StepProto_DefExpand:
			unfolded = true
		}
	}
	assert.True(t, asserted && unfolded, "the verb's record: an assert whose claim the unfold closes")

	t.Run("refusals", func(t *testing.T) {
		e, s := boundSession(t, "sets/set_product")
		addTextGoal(t, s, "∀s:set(A). ∀t:set(B). ∀x:A. ∀y:B. (x, y) ∈ set_cross(s, t) ⇒ x ∈ s")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		gid := state.Goals[0].ID
		two := 2
		for name, tactic := range map[string]TacticReq{
			"a constant the hypothesis does not mention": {Type: "def_expand", Const: "union", HypIndex: &zero},
			"an index out of range":                      {Type: "def_expand", Const: "set_cross", HypIndex: &two},
		} {
			t.Run(name, func(t *testing.T) {
				res, err := applyAt(t, e, s.ID, gid, tactic)
				require.NoError(t, err)
				require.False(t, res.Success)
				require.NotEmpty(t, res.Diagnostics)
				t.Log(res.Diagnostics[0].Message)
			})
		}
	})
}

// sequentOf reads `∀x⃗. hyp ⇒ concl` as the sequent `hyp ⊢ concl`, the
// binders left free.
func sequentOf(t *testing.T, s *Session, text string) core.Prop {
	t.Helper()
	parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "parse %q", text)
	body := parsed.Prop.Conclusion()
	for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
		body = abs.Body()
	}
	hyp, concl, ok := ext.MatchesIMPLY(body)
	require.True(t, ok, "%s is no implication", text)
	return core.MakeProp(concl, hyp)
}

// twinSession is a session of a fresh engine bound to the lineage
// family, with the definitions minted and the sequent added last.
func twinSession(t *testing.T, define []DefineRecursive, sequent string) (*Engine, *Session, core.Prop, string) {
	t.Helper()
	e := newEngine(testEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, lineageFamily, nil)
	require.NoError(t, err)
	for i := range define {
		_, err := e.Define(&DefineRequest{SessionID: info.ID, Recursive: &define[i]})
		require.NoError(t, err)
	}
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	goal := sequentOf(t, s, sequent)
	s.mu.Lock()
	gid := s.AddGoal(goal)
	s.mu.Unlock()
	return e, s, goal, gid
}

// requireSameRecord fails unless the session's last section and the Go
// section recorded the same ministeps, byte for byte.
func requireSameRecord(t *testing.T, s *Session, goSection *proof.GoalStackNode) {
	t.Helper()
	session := s.sections[len(s.sections)-1].root
	require.True(t, session.Proved())
	require.True(t, goSection.Proved())
	marshal := proto.MarshalOptions{Deterministic: true}
	got, err := marshal.Marshal(session.DetailedProofProto())
	require.NoError(t, err)
	want, err := marshal.Marshal(goSection.DetailedProofProto())
	require.NoError(t, err)
	if string(got) != string(want) {
		kinds := func(n *proof.GoalStackNode) []string {
			var out []string
			for _, st := range n.DetailedProofProto().GetSteps() {
				out = append(out, fmt.Sprintf("%T", st.Step))
			}
			return out
		}
		t.Fatalf("the session's record differs from the Go verb's\n  session: %v\n  Go:      %v", kinds(session), kinds(goSection))
	}
}

// TestSplitConj_RecordsWhatConjunctsRecords: the session's `split_conj
// {hyp_index}` and the Go `a.Conjuncts(fact, …)` it twins, each followed
// by the same close, record the same section byte for byte — the
// emitted verb replays the session's steps.
func TestSplitConj_RecordsWhatConjunctsRecords(t *testing.T) {
	e, s, goal, gid := twinSession(t, nil, "∀P Q R:bool. P ∧ Q ∧ R ⇒ R ∨ P")
	zero := 0
	split, err := applyAt(t, e, s.ID, gid, TacticReq{Type: "split_conj", HypIndex: &zero})
	require.NoError(t, err)
	require.True(t, split.Success, "diagnostics: %+v", split.Diagnostics)
	p := hypIndexPrinting(t, e, s.ID, "P")
	closed, err := applyAt(t, e, s.ID, split.Produced[0].GoalID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(p)},
		ByShape: &ByShapeReq{Normalized: true}})
	require.NoError(t, err)
	require.True(t, closed.Success, "diagnostics: %+v", closed.Diagnostics)

	section := proof.NewScript(s.env).Section(goal)
	section.Do(proof.Derive(func(a *proof.Argument) {
		parts := a.Conjuncts(proof.ResidentHyp(goal.Hyp(0)), "P", "Q", "R")
		a.Show("R or P", proof.By(proof.Normalized, parts[0]))
	}))
	requireSameRecord(t, s, section)
}

// TestDefExpand_RecordsWhatUnfoldedRecords: the session's `def_expand
// {const, hyp_index}` and the Go `a.Unfolded(fact, "c")` it twins, each
// followed by the same close, record the same section byte for byte.
func TestDefExpand_RecordsWhatUnfoldedRecords(t *testing.T) {
	both := DefineRecursive{Name: "zz_hyp_verbs_both", Type: "bool → bool → bool",
		Equations: []string{"∀p q:bool. zz_hyp_verbs_both(p, q) ⇔ p ∧ q"}}
	e, s, goal, gid := twinSession(t, []DefineRecursive{both}, "∀P Q:bool. zz_hyp_verbs_both(P, Q) ⇒ Q")
	zero := 0
	opened, err := applyAt(t, e, s.ID, gid, TacticReq{Type: "def_expand", Const: both.Name, HypIndex: &zero})
	require.NoError(t, err)
	require.True(t, opened.Success, "diagnostics: %+v", opened.Diagnostics)
	require.Len(t, opened.NewHyps, 1)
	closed, err := applyAt(t, e, s.ID, opened.Produced[0].GoalID, TacticReq{Type: "by",
		ByHyps: []ByHypSpec{hyp(opened.NewHyps[0].Index)}, ByShape: &ByShapeReq{Normalized: true}})
	require.NoError(t, err)
	require.True(t, closed.Success, "diagnostics: %+v", closed.Diagnostics)

	section := proof.NewScript(s.env).Section(goal)
	section.Do(proof.Derive(func(a *proof.Argument) {
		defined, err := e.lookupDefConst(both.Name)
		require.NoError(t, err)
		unfolded := a.Unfolded(proof.ResidentHyp(goal.Hyp(0)), proof.DefinitionOf(defined))
		a.Show("Q", proof.By(proof.Normalized, unfolded))
	}))
	requireSameRecord(t, s, section)
}

// TestLemmaReadAt_AtAPolymorphicInstance: a law read at an instance
// ENTRY that is itself polymorphic — symmetric_group.SymmetricGroup is
// `group⟨A:permutation(A)⟩(mk_group(…))` — keeps the entry's letter
// loose, so the reading `∀x:permutation(A). inv(x) * x = e` is no
// explicit instance. The cite pins the letter as the two sibling doors
// pin it: off the tuple when witnessed (ReadingAtWitnessTypes), off the
// goal when bare, as a bare `by` premise of the reading and a bare
// `lemma` of a polymorphic entry are pinned. Refused or left at the
// letter on the old code: the witnessed cite that closed the goal
// compared the tuple against the reading BEFORE its typing and refused
// "at an instance the tuple does not name"; the bare cite installed
// exactly, `∀x:permutation(A). …` resident beside a goal at num.
func TestLemmaReadAt_AtAPolymorphicInstance(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	const stated = "∀p:permutation(num). permutation_inverse(p) * p = permutation_identity"
	symmetric := &ReadAtSpec{Key: "symmetric_group.SymmetricGroup"}

	t.Run("witnessed, the tuple names the instance the install closed with", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, stated, "strip_quant")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "group.LeftInverse", ReadAt: symmetric,
			TermSpecialize: map[string]string{"x": "p"}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, "close", res.Effect)
		src := emitProved(t, e, sid, "algebra/group/symmetric_group", "Build_ZzReadingAtPolymorphicInstanceWitnessed")
		assert.Contains(t, src, "LeftInverse.Read(SymmetricGroup)", "--- source: ---\n%s", src)
		for _, banned := range []string{"TODO", "CiteKnown(", "LemmaPreserve("} {
			assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
		}
	})
	t.Run("bare, the reading at the goal's type closes the goal it states", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, stated, "strip_quant")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "group.LeftInverse", ReadAt: symmetric})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, "close", res.Effect)
		src := emitProved(t, e, sid, "algebra/group/symmetric_group", "Build_ZzReadingAtPolymorphicInstanceBare")
		assert.Contains(t, src, "Cite(group.LeftInverse.Read(SymmetricGroup))", "--- source: ---\n%s", src)
		for _, banned := range []string{"TODO", "CiteKnown(", "LemmaPreserve("} {
			assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
		}
	})
	t.Run("bare on a goal it bears on, nothing is left at the loose letter", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e,
			"∀n:num. ∀p:permutation(num). permutation_even(n, permutation_inverse(p) * p)", "intro")
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "group.LeftInverse", ReadAt: symmetric})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		for _, g := range res.State.Goals {
			assert.False(t, ext.PropHasTypeVars(g.Statement), "a letter the goal never meets: %s", ext.PrintTerm(g.Statement.Conclusion()))
		}
	})
}

// TestLemmaReadAt_TheInstallRewroteTheGoal: `lemma {key, read_at}` with
// a tuple, on a goal the reading REWRITES — an equational reading whose
// left side occurs in the goal — is refused, and the refusal says what
// the install did and names the roads: the bare cite takes the
// rewrite, a `by` premise at the tuple brings the instance to bear. On
// the old code the refusal said only that no hypothesis stated the
// reading.
func TestLemmaReadAt_TheInstallRewroteTheGoal(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e,
		"∀n:num. ∀p:permutation(num). permutation_even(n, permutation_inverse(p) * p)", "intro")
	res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "group.LeftInverse",
		ReadAt: &ReadAtSpec{Key: "symmetric_group.SymmetricGroup"}, TermSpecialize: map[string]string{"x": "p"}})
	require.NoError(t, err)
	require.False(t, res.Success, "the tuple grounds nothing the install left")
	require.NotEmpty(t, res.Diagnostics)
	msg := res.Diagnostics[0].Message
	for _, want := range []string{"rewrote the goal", "permutation_even(n₀, permutation_identity)", "with_lemmas"} {
		assert.Contains(t, msg, want, "--- message: ---\n%s", msg)
	}
}
