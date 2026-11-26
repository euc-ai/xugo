package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// sectionPremiseSession proves `∀x:real. x ≤ x + &1` as section 0 and
// opens section 1 on a statement that wants it at f(c). Returns the
// session id, section 0's root id, and section 1's working leaf.
func sectionPremiseSession(t *testing.T, e *Engine) (sid, proved, leaf string) {
	t.Helper()
	ctx := context.Background()
	sid, proved = bareArithLeaf(t, e, "∀x:real. x ≤ x + &1")
	closed, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: proved, Tactic: TacticReq{Type: "arith"}})
	require.NoError(t, err)
	require.True(t, closed.Success)

	s, err := e.getSession(sid)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope("∀f:(real → real). ∀c:real. f(c) ≤ f(c) + &1", &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	stripped, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "strip_quant"}})
	require.NoError(t, err)
	require.Len(t, stripped.Produced, 1)
	return sid, proved, stripped.Produced[0].GoalID
}

// A proved section of the session is cited in a `by` by its STATEMENT,
// as a text premise: the claim the premise leaves certifies against
// the section, and emit renders the cite as the Go a chapter writes —
// `At(<section>, w…)` — with no hypothesis cleared and no proof
// inlined. This is the session twin of a `family.Sections` member's
// local lemma.
func TestBy_CitesAProvedSectionByItsStatement(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	for _, row := range []struct {
		name    string
		premise LemmaWithSpec
		cite    string
	}{
		{"bare", LemmaWithSpec{Text: "∀x:real. x ≤ x + &1"}, "By(lemma1)"},
		{"ground", LemmaWithSpec{Text: "∀x:real. x ≤ x + &1", TermSpecialize: map[string]string{"x": "f₀(c₀)"}},
			`By(At(lemma1, a.TermAs[Real]("f(c)")))`},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, _, leaf := sectionPremiseSession(t, e)
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: leaf, Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{row.premise}},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)

			emitted, err := e.EmitSection(&EmitSectionRequest{
				SessionID: sid, Section: 1, FuncName: "Build_Probe", Family: "real/real_order_ring"})
			require.NoError(t, err)
			require.Equal(t, []int{0, 1}, emitted.SectionsIncluded)
			require.Contains(t, emitted.Go, row.cite)
			require.NotContains(t, emitted.Go, "ClearHyps")
			require.NotContains(t, emitted.Go, "CiteNode")
		})
	}
}

// The key slot names registry entries. Handed a node of the session —
// the id `inspect` prints beside a section — it refuses, and the
// refusal is the repair: it says the section is cited by its
// statement and carries the statement to paste.
func TestBy_SectionIdInTheKeySlotNamesTheTextPremise(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	sid, proved, leaf := sectionPremiseSession(t, e)
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: leaf, Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: proved}}},
	})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.Len(t, res.Diagnostics, 1)
	msg := res.Diagnostics[0].Message
	require.Contains(t, msg, "is a node of this session, not a registry entry")
	// The statement is carried in the chapter's spelling — the output
	// door re-prints it — so the paste reads as the chapter writes.
	const pasted = "∀x:real. x ≤ x + &1"
	require.Contains(t, msg, `with_lemmas:[{"text":"`+pasted+`"}]`)

	// The statement the refusal carries, pasted, is the premise that works.
	again, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: leaf, Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Text: pasted}}},
	})
	require.NoError(t, err)
	require.True(t, again.Success, "diagnostics: %+v", again.Diagnostics)

	// An open node is told apart, and a key that is no node of the
	// session keeps the registry's own miss.
	sid, _, leaf = sectionPremiseSession(t, e)
	open, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: leaf, Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: leaf}}},
	})
	require.NoError(t, err)
	require.False(t, open.Success)
	// the leaf is a node under section 1's root, not the root itself: the registry's miss stands
	require.Contains(t, open.Diagnostics[0].Message, "names no proof-registry entry")
	unknown, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: leaf, Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "no_such.Member"}}},
	})
	require.NoError(t, err)
	require.Contains(t, unknown.Diagnostics[0].Message, "names no proof-registry entry")
}
