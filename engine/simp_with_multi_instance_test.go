package engine

// Regression tests for simp_with's MULTI-INSTANCE polymorphic adaptation
// (see simp_with_multi_instance.go): a polymorphic rule entry WITHOUT an
// explicit per-entry σ expands to one resolved rule copy per distinct
// goal type-instance, while an entry WITH an explicit
// type_specialize keeps exact single-instance semantics.
//
// The tests drive the full pipeline on cardinality.CardClauses with
// goals carrying card(∅) at 2-4 distinct set element types, built from
// the member's own specializations so all terms are engine-canonical by
// construction.

import (
	"context"
	"fmt"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// termContainsConstNamed walks t and reports whether any const named
// `name` occurs — the "was every card occurrence rewritten?" oracle.
func termContainsConstNamed(t core.Term, name core.TermName) bool {
	switch ct := t.Core().(type) {
	case core.ConstTerm:
		return ct.Name() == name
	case core.AppliedTerm:
		return termContainsConstNamed(ct.Fun(), name) ||
			termContainsConstNamed(ct.Arg(), name)
	case core.AbsTerm:
		return termContainsConstNamed(ct.Body(), name)
	}
	return false
}

// multiInstanceCardSession builds a session whose single goal is the
// conjunction of CardClauses' empty-set clause specialized at each of
// `elemTypes` — i.e. card⟨τᵢ⟩(∅⟨τᵢ⟩) = 0 for each τᵢ, all in one
// conclusion. Returns the engine, session info/handle and the member's
// polymorphic statement.
func multiInstanceCardSession(
	t *testing.T, elemTypes []string,
) (*Engine, string, *Session, core.Prop) {
	t.Helper()
	member := cardClauses(t)
	e := newEngine(serveLikeEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	lenProp := member.Statement().Prop

	tvNames := collectLemmaTypeVarNames(lenProp)
	require.NotEmpty(t, tvNames, "CardClauses must be polymorphic")

	nilClauseAt := func(elemType string) core.Term {
		spec := map[string]string{}
		for name := range tvNames {
			spec[name] = elemType
		}
		specialized, _, serr := buildSpecializedLemma(lenProp, spec, groundTestGoal())
		require.NoError(t, serr)
		require.False(t, ext.PropHasTypeVars(specialized))
		body := specialized.Conclusion()
		for {
			abs := ext.MatchesFORALL(body)
			if abs.IsZero() {
				break
			}
			body = abs.Body()
		}
		nilClause, _, isAnd := ext.MatchesAND(body)
		require.True(t, isAnd, "CardClauses must be a conjunction, got %s", ext.PrintTerm(body))
		return nilClause
	}

	var conj core.Term
	for _, ty := range elemTypes {
		clause := nilClauseAt(ty)
		if conj == nil {
			conj = clause
		} else {
			conj = ext.And(conj, clause).Core()
		}
	}
	goal := prop.MakeProp(conj)

	s.AddGoal(goal)
	s.rebuildGoalIndex()
	return e, info.ID, s, lenProp
}

// applySimpWithCard fires one simp_with call with the given entries on
// the session's single open goal and returns the StepResult.
func applySimpWithCard(
	t *testing.T, e *Engine, sid string, entries []LemmaWithSpec,
) *StepResult {
	t.Helper()
	stateRes, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	require.Len(t, stateRes.Goals, 1)
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: stateRes.Goals[0].ID,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: entries},
	})
	require.NoError(t, err)
	return out
}

// openConclusionsContainingCARD counts surviving open leaves whose
// conclusion still mentions the card const.
func openConclusionsContainingCARD(t *testing.T, e *Engine, sid string) int {
	t.Helper()
	stateRes, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	n := 0
	for _, g := range stateRes.Goals {
		if termContainsConstNamed(g.Statement.Conclusion(), "card") {
			t.Logf("open leaf still mentions card: %s", prop.PrintProp(g.Statement))
			n++
		}
	}
	return n
}

func autoTypeInstanceDiags(res *StepResult) []Diagnostic {
	var out []Diagnostic
	for _, d := range res.Diagnostics {
		if d.Type == DiagAutoTypeInstances {
			out = append(out, d)
		}
	}
	return out
}

// TestSimpWith_PolymorphicRule_MultiInstance_RewritesAllInstances is the
// probe-first regression test for the v1 single-instance boundary: goal
// `card⟨num⟩(∅) = 0 ∧ card⟨bool⟩(∅) = 0`, ONE simp_with entry
// {key: CardClauses} with no explicit σ. Pre-upgrade the rule auto-adapted to
// ONE instance and only one conjunct was rewritten (the residual kept a
// card occurrence); now both instances fire in the single call.
//
// It then closes the residuals and asserts store-decomposition RESOLVES
// with the CardClauses member as a dep — the Bug-A regression class
// (per-session KnownThm payloads detonating at store time), extended to
// the multi-instance rule children: BOTH must close through the
// _TypeInstStep channel against the SAME polymorphic member.
func TestSimpWith_PolymorphicRule_MultiInstance_RewritesAllInstances(t *testing.T) {
	e, sid, _, _ := multiInstanceCardSession(t, []string{"num", "bool"})
	res := applySimpWithCard(t, e, sid, []LemmaWithSpec{{Key: cardClauses(t).Key}})
	require.True(t, res.Success,
		"simp_with with the polymorphic CardClauses rule must fire; diagnostics: %+v", res.Diagnostics)

	// THE core assertion: no surviving open leaf may still mention
	// card — both type instances of the redex must have been rewritten
	// by the ONE polymorphic entry.
	assert.Equal(t, 0, openConclusionsContainingCARD(t, e, sid),
		"both card type-instances must be rewritten by one polymorphic simp_with entry")

	// Diagnostics must name the expansion (never silent): one
	// auto_type_instances diagnostic naming 2 instances.
	diags := autoTypeInstanceDiags(res)
	require.Len(t, diags, 1, "multi-instance expansion must be diagnosed; got %+v", res.Diagnostics)
	assert.Contains(t, diags[0].Message, "2 distinct goal type-instance(s)")

	// The rule children (one per instance) must be visible as
	// AutoMatched entries against the CardClauses member.
	lengthMatches := 0
	for _, m := range res.AutoMatched {
		if m.MatchedKey == cardClauses(t).Key {
			lengthMatches++
		}
	}
	assert.Equal(t, 2, lengthMatches,
		"both adapted rule children must auto-close against the CardClauses member; AutoMatched=%+v",
		res.AutoMatched)

	// Close the surviving residuals (0 = 0 shapes) and store-decompose.
	for range 8 {
		stateRes, gerr := e.InspectState(context.Background(), sid)
		require.NoError(t, gerr)
		if stateRes.NumOpen == 0 {
			break
		}
		closed := false
		for _, og := range stateRes.Goals {
			for _, tac := range []string{"simplify", "auto"} {
				aout, aerr := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
					GoalID: og.ID,
					Tactic: TacticReq{Type: tac},
				})
				if aerr == nil && aout.Success {
					closed = true
					break
				}
			}
			if closed {
				break
			}
		}
		require.True(t, closed, "every residual must close by simplify/auto")
	}
	stateRes, gerr := e.InspectState(context.Background(), sid)
	require.NoError(t, gerr)
	require.Equal(t, 0, stateRes.NumOpen, "proof tree must be fully closed before emit")

	// The emit must resolve BOTH adapted rule children's deps — a
	// failure here means an instance child was recorded as a
	// per-session KnownThm instead of a TypeInst against the
	// polymorphic member.
	deps := emittedDepNames(t, e, sid, 0)
	lengthDeps := 0
	for _, dep := range deps {
		if dep == cardClauses(t).Name {
			lengthDeps++
		}
	}
	assert.Equal(t, 1, lengthDeps,
		"the two instance children must dedup to ONE CardClauses dep; deps=%v", deps)
}

// TestSimpWith_PolymorphicRule_OwnInstanceBesideAnother is the regression
// for a goal that carries the rule's constant at the rule's OWN letters
// and at another instance in one conclusion — `card⟨A⟩(∅) = 0 ∧
// card⟨num⟩(∅) = 0` with A the entry's own type letter. The adaptation
// enumeration returns the num instance only (the identity is dropped by
// contract), which alone would leave the A redex with no rule to match
// and the call firing at num; the rule at its own letters stays in the
// set beside the adapted copy, and both instances rewrite in one call.
func TestSimpWith_PolymorphicRule_OwnInstanceBesideAnother(t *testing.T) {
	member := cardClauses(t)
	e := newEngine(serveLikeEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	lenProp := member.Statement().Prop

	// The ∅-clause at the entry's OWN instance: the statement's body,
	// unspecialized.
	ownBody := lenProp.Conclusion()
	for abs := ext.MatchesFORALL(ownBody); !abs.IsZero(); abs = ext.MatchesFORALL(ownBody) {
		ownBody = abs.Body()
	}
	ownClause, _, isAnd := ext.MatchesAND(ownBody)
	require.True(t, isAnd)
	require.True(t, ext.PropHasTypeVars(prop.MakeProp(ownClause)), "the own-instance clause keeps the entry's type letter")

	// The ∅-clause at num.
	spec := map[string]string{}
	for name := range collectLemmaTypeVarNames(lenProp) {
		spec[name] = "num"
	}
	atNum, _, serr := buildSpecializedLemma(lenProp, spec, groundTestGoal())
	require.NoError(t, serr)
	numBody := atNum.Conclusion()
	for abs := ext.MatchesFORALL(numBody); !abs.IsZero(); abs = ext.MatchesFORALL(numBody) {
		numBody = abs.Body()
	}
	numClause, _, _ := ext.MatchesAND(numBody)

	s.AddGoal(prop.MakeProp(ext.And(ownClause, numClause).Core()))
	s.rebuildGoalIndex()

	res := applySimpWithCard(t, e, info.ID, []LemmaWithSpec{{Key: member.Key}})
	require.True(t, res.Success, "the bare rule must fire at both instances; diagnostics: %+v", res.Diagnostics)
	assert.Equal(t, 0, openConclusionsContainingCARD(t, e, info.ID),
		"the rule's own instance and the num instance must both be rewritten by one bare entry")
}

func TestSimpWith_PolymorphicRule_CompletesFiniteInstances(t *testing.T) {
	for _, count := range []int{4, 20} {
		t.Run(fmt.Sprint(count), func(t *testing.T) {
			types := make([]string, count)
			for i := range types {
				types[i] = strings.Repeat("bool→", i) + "bool"
			}
			e, sid, _, _ := multiInstanceCardSession(t, types)
			res := applySimpWithCard(t, e, sid, []LemmaWithSpec{{Key: cardClauses(t).Key}})
			require.True(t, res.Success, "%+v", res.Diagnostics)
			require.Zero(t, openConclusionsContainingCARD(t, e, sid), "all finite instances must be rewritten")
		})
	}
}

// TestSimpWith_ExplicitTypeSpecialize_ExactSingleInstance guards the
// Exact-bypass contract: an entry WITH an explicit
// type_specialize is honored verbatim as a SINGLE instance — never
// multi-expanded, never re-adapted. On the two-instance goal only the
// σ-pinned conjunct is rewritten.
func TestSimpWith_ExplicitTypeSpecialize_ExactSingleInstance(t *testing.T) {
	e, sid, _, lenProp := multiInstanceCardSession(t, []string{"num", "bool"})
	tvNames := collectLemmaTypeVarNames(lenProp)
	spec := map[string]string{}
	for name := range tvNames {
		spec[name] = "num"
	}
	res := applySimpWithCard(t, e, sid, []LemmaWithSpec{{
		Key:            cardClauses(t).Key,
		TypeSpecialize: spec,
	}})
	require.True(t, res.Success,
		"simp_with with the explicitly specialized rule must fire on the num conjunct; "+
			"diagnostics: %+v", res.Diagnostics)

	// The bool instance must SURVIVE: explicit σ = exact single instance.
	assert.Equal(t, 1, openConclusionsContainingCARD(t, e, sid),
		"explicit type_specialize must rewrite ONLY the pinned instance")

	// And no multi-instance expansion diagnostic may appear.
	assert.Empty(t, autoTypeInstanceDiags(res),
		"an explicit-σ entry must not be auto-expanded")

	// Exactly one rule child closes against the entry.
	lengthMatches := 0
	for _, m := range res.AutoMatched {
		if m.MatchedKey == cardClauses(t).Key {
			lengthMatches++
		}
	}
	assert.Equal(t, 1, lengthMatches,
		"exactly one (specialized) rule child must close against the CardClauses member; AutoMatched=%+v",
		res.AutoMatched)
}

// TestSimpWith_DuplicateEntries_DedupToOneCopyPerInstance: two identical
// polymorphic entries expand to the SAME instances; the duplicates are
// deduplicated (one rule copy per instance, diagnosed) rather than
// recorded twice.
func TestSimpWith_DuplicateEntries_DedupToOneCopyPerInstance(t *testing.T) {
	e, sid, _, _ := multiInstanceCardSession(t, []string{"num", "bool"})
	res := applySimpWithCard(t, e, sid, []LemmaWithSpec{
		{Key: cardClauses(t).Key},
		{Key: cardClauses(t).Key},
	})
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)

	assert.Equal(t, 0, openConclusionsContainingCARD(t, e, sid))

	// Both instances fire exactly once each: 2 rule children, not 4.
	lengthMatches := 0
	for _, m := range res.AutoMatched {
		if m.MatchedKey == cardClauses(t).Key {
			lengthMatches++
		}
	}
	assert.Equal(t, 2, lengthMatches,
		"duplicate entries must dedup to one rule copy per instance; AutoMatched=%+v",
		res.AutoMatched)

	// The dedup must be diagnosed (rule #1 collapsing into rule #0's
	// instances), alongside rule #0's expansion note.
	var dedupSeen bool
	for _, d := range autoTypeInstanceDiags(res) {
		if strings.Contains(d.Message, "deduplicated") {
			dedupSeen = true
		}
	}
	assert.True(t, dedupSeen,
		"the duplicate entry's dedup must be diagnosed; diagnostics=%+v", res.Diagnostics)
}

// TestDescribeSimpWithEntry_RuneSafeClip: the text-form label clips
// rune-safe — it lands in RPC diagnostics whose marshal is strict
// UTF-8, and the byte cut this replaced could split a math glyph
// (same defect class as the session `by` diagnostic failure).
func TestDescribeSimpWithEntry_RuneSafeClip(t *testing.T) {
	long := strings.Repeat("∀s ⊆ 𝕌.", 30)
	got := describeSimpWithEntry(LemmaWithSpec{Text: long})
	require.True(t, utf8.ValidString(got), "clipped label must remain valid UTF-8: %q", got)
	require.True(t, strings.HasPrefix(got, "text "))
	require.True(t, strings.HasSuffix(got, "…"))

	// Key-loaded entries pass through unclipped.
	require.Equal(t, "key prop_123", describeSimpWithEntry(LemmaWithSpec{Key: "prop_123"}))
}
