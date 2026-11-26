package engine

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/emit"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// deferApply applies one tactic request and requires success.
func deferApply(t *testing.T, e *Engine, sid, gid string, tactic TacticReq) *StepResult {
	t.Helper()
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: tactic})
	require.NoError(t, err)
	require.True(t, res.Success, "%s on %s: %+v", tactic.Type, gid, res.Diagnostics)
	return res
}

// deferParse parses a statement in the session's scope (a card's
// identity is computed from the same parse the agent's add-goal uses).
func deferParse(t *testing.T, s *Session, text string) *dsl.ParseResult {
	t.Helper()
	parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
		ConstResolver:      envConstResolver(s.env),
		StrictResolution:   true,
		FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "parse %q: %v", text, parsed.Errors)
	return &parsed
}

// assertThenDefer builds the deferral idiom: a target, an asserted
// lemma, the residual closed, the claim deferred. Returns the session,
// the target's section and the defer result.
func assertThenDefer(t *testing.T, e *Engine) (string, int, *DeferResult) {
	t.Helper()
	return assertThenDeferWith(t, e, "P:bool→bool ⊢ ∀x y:bool. zz_defer_both(x, y) ⇒ P(x)",
		"∀a b:bool. a ∧ b ⇒ P(a)", "ConjSym", "commutativity of ∧, stated for the chapter")
}

// assertThenDeferWith is assertThenDefer for a given target, claim,
// card name and deps: the residual must close by simp + auto.
func assertThenDeferWith(t *testing.T, e *Engine, target, claim, name, note string, deps ...string) (string, int, *DeferResult) {
	t.Helper()
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sid := info.ID
	_, err = e.SetSessionFamily(sid, lineageFamily, nil)
	require.NoError(t, err)

	// A definition the residual proof must unfold: the card is then
	// no logical triviality (the card is not the target in disguise).
	_, err = e.Define(&DefineRequest{SessionID: sid, Recursive: &DefineRecursive{
		Name: "zz_defer_both", Type: "bool → bool → bool",
		Equations: []string{"∀p q:bool. zz_defer_both(p, q) ⇔ p ∧ q"},
	}})
	require.NoError(t, err)
	sec, res, err := deferClaim(t, e, sid, target, claim, name, note, deps)
	require.NoError(t, err)
	return sid, sec, res
}

// deferClaim adds target to the session as a section, asserts claim on
// it, closes the residual by simp + auto, and defers the claim leaf as
// name with note and deps. Returns the section and the defer's result.
func deferClaim(t *testing.T, e *Engine, sid, target, claim, name, note string, deps []string) (int, *DeferResult, error) {
	t.Helper()
	s, err := e.getSession(sid)
	require.NoError(t, err)
	g := lineageText(t, s, target)
	asserted := deferApply(t, e, sid, g, TacticReq{Type: "assert", ClaimText: claim})
	require.Len(t, asserted.Produced, 2, "assert produces the claim and the residual")
	var claimID, residualID string
	for _, p := range asserted.Produced {
		if p.Changes.HypsAdded > 0 {
			residualID = p.GoalID
		} else {
			claimID = p.GoalID
		}
	}
	require.NotEmpty(t, claimID)
	require.NotEmpty(t, residualID)
	unfolded := deferApply(t, e, sid, residualID, TacticReq{Type: "simp"})
	require.Len(t, unfolded.Produced, 1)
	require.Equal(t, "close", deferApply(t, e, sid, unfolded.Produced[0].GoalID, TacticReq{Type: "auto"}).Effect)
	// The target is the session's last section.
	sec := len(s.sections) - 1
	require.False(t, s.sections[sec].root.Proved(), "the claim leaf is still open")

	res, err := e.Defer(context.Background(), &DeferRequest{SessionID: sid, GoalID: claimID, Name: name, Note: note, Deps: deps})
	return sec, res, err
}

// assertClaim asserts claim on the open goal g and returns the claim
// leaf's id.
func assertClaim(t *testing.T, e *Engine, sid, g, claim string) string {
	t.Helper()
	asserted := deferApply(t, e, sid, g, TacticReq{Type: "assert", ClaimText: claim})
	for _, p := range asserted.Produced {
		if p.Changes.HypsAdded == 0 {
			return p.GoalID
		}
	}
	t.Fatalf("assert %q produced no claim leaf: %+v", claim, asserted.Produced)
	return ""
}

// The claim leaf of an assert becomes a card and closes by it: the
// section is proved, the card is minted under the family's name, and
// nothing but the cite is recorded for the leaf.
func TestDefer_ClaimLeafBecomesACardAndClosesByIt(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	sid, sec, res := assertThenDefer(t, e)
	s, _ := e.getSession(sid)

	require.Equal(t, "deferred", res.Status)
	require.NotNil(t, res.Card)
	assert.Equal(t, "ConjSym", res.Card.Name)
	assert.Equal(t, lineageFamily+".ConjSym", res.Card.Entry, "the registered name the cite spells")
	assert.Equal(t, "commutativity of ∧, stated for the chapter", res.Card.Note)
	assert.Equal(t, sec, res.Card.Section)
	assert.NotEmpty(t, res.Card.StatementTyped)
	assert.Equal(t, res.Card.Key, string(registry.KeyOf(deferParse(t, s, res.Card.StatementTyped).Prop)),
		"the paste-ready spelling parses back to the card")
	assert.True(t, s.sections[sec].root.Proved(), "the leaf closed by the card")
	require.NotNil(t, res.Section)
	assert.True(t, res.Section.Proved)
	require.Len(t, res.Section.Cards, 1)
	assert.Equal(t, res.Card.Key, res.Section.Cards[0].Key)
	card := s.cardFor(res.Card.Entry)
	require.NotNil(t, card, "the session holds the card under its registered name")
	assert.Same(t, card, s.cardFor(res.Card.Key), "and under its key")
	assert.True(t, card.axiom.Proved(), "served as a realized axiom")
	assert.True(t, card.axiom.AlphaEquals(card.statement))
}

// A leaf carrying hypotheses defers too: the card is its conclusion
// closed over the free variables, and the cite closes the leaf under
// its hypotheses.
func TestDefer_LeafWithHypothesesClosesByTheCard(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sid := info.ID
	_, err = e.SetSessionFamily(sid, lineageFamily, nil)
	require.NoError(t, err)
	s, _ := e.getSession(sid)
	g := lineageText(t, s, "P:bool→bool, Q:bool→bool ⊢ ∀x:bool. Q(x) ⇒ P(x)")
	stripped := deferApply(t, e, sid, g, TacticReq{Type: "strip_quant"})
	require.Len(t, stripped.Produced, 1)
	imp := deferApply(t, e, sid, stripped.Produced[0].GoalID, TacticReq{Type: "strip_imp"})
	require.Len(t, imp.Produced, 1)
	leaf := imp.Produced[0].GoalID
	require.Greater(t, goalHypCount(s, leaf), 0, "the leaf carries Q(x) as a hypothesis")

	// x was introduced by strip_quant: section-local, so the card may
	// not mention it — the ∀-closed statement is asserted first.
	_, err = e.Defer(ctx, &DeferRequest{SessionID: sid, GoalID: leaf, Name: "AllP", Note: "every x satisfies P"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "section-local variable")

	asserted := deferApply(t, e, sid, leaf, TacticReq{Type: "assert", ClaimText: "∀y:bool. P(y)"})
	var claimID string
	for _, p := range asserted.Produced {
		if p.Changes.HypsAdded == 0 {
			claimID = p.GoalID
		}
	}
	require.NotEmpty(t, claimID)
	res, err := e.Defer(ctx, &DeferRequest{SessionID: sid, GoalID: claimID, Name: "AllP", Note: "every x satisfies P"})
	require.NoError(t, err)
	assert.Equal(t, "deferred", res.Status)
	_, open := s.goalIndex[claimID]
	assert.False(t, open, "the claim leaf closed by the card")
}

// goalText prints an open leaf's goal by its index id.
func goalText(s *Session, id string) string {
	s.mu.Lock()
	defer s.mu.Unlock()
	entry, ok := s.goalIndex[id]
	if !ok {
		return ""
	}
	return prop.PrintProp(entry.node.Goal)
}

func goalHypCount(s *Session, id string) int {
	s.mu.Lock()
	defer s.mu.Unlock()
	entry, ok := s.goalIndex[id]
	if !ok {
		return -1
	}
	return entry.node.Goal.NumHyps()
}

// The refusals, each naming its fix.
func TestDefer_Refusals(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	ctx := context.Background()

	bare, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sb, _ := e.getSession(bare.ID)
	g := lineageText(t, sb, "p:bool ⊢ p ⇒ p")
	_, err = e.Defer(ctx, &DeferRequest{SessionID: bare.ID, GoalID: g, Name: "Refl", Note: "a note"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "bound to no family")

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, lineageFamily, nil)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	g = lineageText(t, s, "p:bool, q:bool ⊢ p ∧ q ⇒ p")
	_, err = e.Defer(ctx, &DeferRequest{SessionID: info.ID, GoalID: g, Name: "  ", Note: "a note"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "name is required")
	_, err = e.Defer(ctx, &DeferRequest{SessionID: info.ID, GoalID: g, Name: "conjLeft", Note: "a note"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "not a member name")
	_, err = e.Defer(ctx, &DeferRequest{SessionID: info.ID, GoalID: g, Name: "ConjLeft"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "note is required")
	_, err = e.Defer(ctx, &DeferRequest{SessionID: info.ID, GoalID: g, Name: "ConjLeft", Note: "a note"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "section's own conclusion")

	g = lineageText(t, s, "∀x:num. x = x ⇒ x = x")
	stripped := deferApply(t, e, info.ID, g, TacticReq{Type: "strip_quant"})
	require.Len(t, stripped.Produced, 1)
	_, err = e.Defer(ctx, &DeferRequest{SessionID: info.ID, GoalID: stripped.Produced[0].GoalID, Name: "Refl", Note: "a note"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "section-local variable")
}

// A card an entry already states is not minted: a proved entry says
// "proved", a landed card says "card", both naming what to cite.
func TestDefer_StatedByAnEntry(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	ctx := context.Background()
	fam := registry.NewFamily("zz_defer_stated", nil)
	stub := registry.Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	proved := fam.Add(registry.ProofEntry{
		Name:  "Proved",
		Key:   fixtureKey(fam, "∀P:(bool → bool). ∀a b:bool. a ∧ b ⇒ P(a) ∨ P(b)"),
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀P:(bool → bool). ∀a b:bool. a ∧ b ⇒ P(a) ∨ P(b)"},
	})
	card := fam.Add(registry.ProofEntry{
		Name:  "Card",
		Key:   fixtureKey(fam, "∀P:(bool → bool). ∀a b:bool. a ∨ b ⇒ P(a) ∧ P(b)"),
		Build: fam.Card("∀P:(bool → bool). ∀a b:bool. a ∨ b ⇒ P(a) ∧ P(b)", "a landed card of the fixture"),
	})

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, lineageFamily, nil)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	for _, tc := range []struct{ target, claim, status, by string }{
		{"P:bool→bool ⊢ ∀x y:bool. x ∧ y ⇒ P(x) ∨ P(y) ∨ P(x)", "∀a b:bool. a ∧ b ⇒ P(a) ∨ P(b)", "proved", proved.Name},
		{"P:bool→bool ⊢ ∀x y:bool. x ∨ y ⇒ P(x) ∧ P(y) ∧ P(x)", "∀a b:bool. a ∨ b ⇒ P(a) ∧ P(b)", "card", card.Name},
	} {
		g := lineageText(t, s, tc.target)
		asserted := deferApply(t, e, info.ID, g, TacticReq{Type: "assert", ClaimText: tc.claim})
		var claimID string
		for _, p := range asserted.Produced {
			if p.Changes.HypsAdded == 0 {
				claimID = p.GoalID
			}
		}
		res, err := e.Defer(ctx, &DeferRequest{SessionID: info.ID, GoalID: claimID, Name: "Twin", Note: "a note"})
		require.NoError(t, err)
		assert.Equal(t, tc.status, res.Status)
		assert.Equal(t, []string{tc.by}, res.StatedBy)
		_, open := s.goalIndex[claimID]
		assert.True(t, open, "nothing was minted and the leaf is still the agent's to close by the cite")
	}
}

// fixtureKey mints a fixture entry's own key from its statement, as
// the key lint would paste it: every entry carries its key in source.
func fixtureKey(fam *registry.Family, text string) string {
	return string(registry.NewStatement(fam.ParseScript(testEnv()).MakePropText(text)).Key())
}

// The same lemma deferred from two sections is one card, under its
// first name.
func TestDefer_SameLemmaTwiceIsOneCard(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	sid, _, first := assertThenDefer(t, e)
	s, _ := e.getSession(sid)
	g := lineageText(t, s, "Q:bool→bool ⊢ ∀x y:bool. zz_defer_both(x, y) ⇒ Q(x)")
	asserted := deferApply(t, e, sid, g, TacticReq{Type: "assert", ClaimText: "∀a b:bool. a ∧ b ⇒ Q(a)"})
	var claimID string
	for _, p := range asserted.Produced {
		if p.Changes.HypsAdded == 0 {
			claimID = p.GoalID
		}
	}
	second, err := e.Defer(context.Background(), &DeferRequest{SessionID: sid, GoalID: claimID, Name: "ConjSymAgain", Note: "the same lemma"})
	require.NoError(t, err)
	assert.Equal(t, "deferred", second.Status)
	assert.Equal(t, first.Card.Key, second.Card.Key)
	assert.Equal(t, first.Card.Entry, second.Card.Entry, "one card, its first name")
	assert.Len(t, s.cards, 1)

	g = lineageText(t, s, "R:bool→bool ⊢ ∀x y:bool. zz_defer_both(x, y) ⇒ R(x) ∨ R(y)")
	asserted = deferApply(t, e, sid, g, TacticReq{Type: "assert", ClaimText: "∀a b:bool. a ⇒ R(a) ∨ R(b)"})
	for _, p := range asserted.Produced {
		if p.Changes.HypsAdded == 0 {
			claimID = p.GoalID
		}
	}
	_, err = e.Defer(context.Background(), &DeferRequest{SessionID: sid, GoalID: claimID, Name: "ConjSym", Note: "another lemma"})
	require.Error(t, err, "a minted name is not reused for another statement")
	assert.Contains(t, err.Error(), "taken in this session")
}

// emit-section renders the card as a family.Card entry beside the
// member, and the member's typed Deps name it.
func TestDefer_EmitRendersTheCardEntry(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	sid, sec, res := assertThenDefer(t, e)
	emit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: sid, Section: sec, FuncName: "Build_WithCard", Family: lineageFamily, IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted:\n%s", emit.Go)
	assert.Contains(t, emit.Go, "var ConjSym = family.Add(registry.ProofEntry{")
	assert.Contains(t, emit.Go, `Key:  "`+res.Card.Key+`"`)
	assert.Contains(t, emit.Go, "Build: family.Card(")
	assertRendersStatement(t, emit.Go, res.Card.StatementTyped)
	assert.Contains(t, emit.Go, `"commutativity of ∧, stated for the chapter"`)
	assert.Contains(t, emit.DepNames, res.Card.Entry, "the member cites the card by its registered name")
	assert.Regexp(t, `(Cite|By|At)\(ConjSym\b`, emit.Go, "and its proof cites it by the card's var")
	assert.NotRegexp(t, `(?m)^var WithCard[\s\S]*Deps:`, emit.Go, "and the member spells no Deps")
	assert.NotContains(t, emit.Go, "Cards:")
	assert.NotContains(t, emit.Go, "TODO")
	assert.Less(t, strings.Index(emit.Go, "var ConjSym ="), strings.Index(emit.Go, "var WithCard ="), "the card is declared before the member")
}

// Resume re-mints the card and the recorded cite re-closes the leaf.
func TestDefer_ResumeReplaysTheDefer(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(store, dir)
	sid, secIdx, res := assertThenDefer(t, a)

	b := lineageEngine(store, dir)
	resumed, err := b.ResumeSession(context.Background(), sid)
	require.NoError(t, err)
	require.Nil(t, resumed.Diverged, "%+v", resumed.Diverged)
	require.Len(t, resumed.Sections, secIdx+1)
	sec := resumed.Sections[secIdx]
	assert.True(t, sec.Proved)
	require.NotNil(t, sec.RecordMatches)
	assert.True(t, *sec.RecordMatches, "the re-closed section matches its record")
	require.Len(t, sec.Cards, 1)
	assert.Equal(t, res.Card.Key, sec.Cards[0].Key)
	s, _ := b.getSession(sid)
	require.NotNil(t, s.cardFor(res.Card.Entry), "the card is minted again")
}

// A proved entry states the card while the lineage sleeps: resume
// still re-mints (the transcript is replayed as recorded), the cards
// view no longer lists the card, and a fresh defer says "proved".
func TestDefer_ResumeAfterTheCardIsProved(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(store, dir)
	sid, secIdx, res := assertThenDeferWith(t, a, "P:bool→bool ⊢ ∀x y:bool. zz_defer_both(x, y) ⇒ P(x) ∧ P(y)",
		"∀a b:bool. a ∧ b ⇒ P(a) ∧ P(b)", "ConjBoth", "both conjuncts under P")
	require.Equal(t, "deferred", res.Status)

	stub := registry.Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	fam := registry.NewFamily("zz_cards_resume", nil)
	fam.Add(registry.ProofEntry{
		Name:  "ConjBoth",
		Key:   res.Card.Key,
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀P:(bool → bool). ∀a b:bool. a ∧ b ⇒ P(a) ∧ P(b)"},
	})

	b := lineageEngine(store, dir)
	resumed, err := b.ResumeSession(context.Background(), sid)
	require.NoError(t, err)
	require.Nil(t, resumed.Diverged, "a proved card does not diverge the transcript: %+v", resumed.Diverged)
	sec := resumed.Sections[secIdx]
	assert.True(t, sec.Proved)
	require.NotNil(t, sec.RecordMatches)
	assert.True(t, *sec.RecordMatches)

	cards, err := b.Cards(&CardsRequest{Key: res.Card.Key})
	require.NoError(t, err)
	assert.Empty(t, cards.Cards, "a card a proved entry states is no card")

	s, _ := b.getSession(sid)
	g := lineageText(t, s, "Q:bool→bool ⊢ ∀x y:bool. zz_defer_both(x, y) ⇒ Q(x) ∧ Q(y)")
	asserted := deferApply(t, b, sid, g, TacticReq{Type: "assert", ClaimText: "∀a b:bool. a ∧ b ⇒ Q(a) ∧ Q(b)"})
	var claimID string
	for _, p := range asserted.Produced {
		if p.Changes.HypsAdded == 0 {
			claimID = p.GoalID
		}
	}
	again, err := b.Defer(context.Background(), &DeferRequest{SessionID: sid, GoalID: claimID, Name: "ConjBoth", Note: "a note"})
	require.NoError(t, err)
	assert.Equal(t, "proved", again.Status)
	assert.Equal(t, []string{"zz_cards_resume.ConjBoth"}, again.StatedBy)
}

// The cards view: a session's card with its parent section and its
// attacker, read off the store; a restore rolls a defer out of it.
func TestCards_SessionCardParentsAndAttackers(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	e := lineageEngine(store, dir)
	sid, sec, res := assertThenDefer(t, e)

	// A second lineage whose target states the card attacks it.
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s2, _ := e.getSession(info.ID)
	lineageText(t, s2, "P:bool→bool ⊢ ∀a b:bool. a ∧ b ⇒ P(a)")

	cards, err := ViewCards(dir, &CardsRequest{Key: res.Card.Key})
	require.NoError(t, err)
	require.Len(t, cards.Cards, 1)
	c := cards.Cards[0]
	assert.Equal(t, res.Card.Key, c.Key)
	assert.Equal(t, "ConjSym", c.Name)
	assert.Equal(t, lineageFamily+".ConjSym", c.Entry)
	assert.Equal(t, lineageFamily, c.Family)
	assert.False(t, c.Landed)
	require.NotEmpty(t, c.StatementTyped, "a session's card is paste-ready off the store")
	require.Len(t, c.Parents, 1)
	assert.Equal(t, sid, c.Parents[0].Lineage)
	assert.Equal(t, sec, c.Parents[0].Section)
	require.Len(t, c.AttackedBy, 1)
	assert.Equal(t, info.ID, c.AttackedBy[0].Lineage)

	byLineage, err := e.Cards(&CardsRequest{Lineage: info.ID})
	require.NoError(t, err)
	require.Len(t, byLineage.Cards, 1, "filtered to the attacker's lineage, the card still shows")
}

func TestCards_RestoreUndoesADefer(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sid := info.ID
	_, err = e.SetSessionFamily(sid, lineageFamily, nil)
	require.NoError(t, err)
	s, _ := e.getSession(sid)
	g := lineageText(t, s, "P:num→bool, Q:num→bool, R:num→bool ⊢ (∀a:num. P(a) ⇒ P(a) ∨ Q(a)) ∧ (∀a:num. P(a) ⇒ R(a))")
	cp, err := e.Checkpoint(ctx, sid, "before")
	require.NoError(t, err)
	split := deferApply(t, e, sid, g, TacticReq{Type: "split_conj"})
	var impID string
	for _, p := range split.Produced {
		if !strings.Contains(goalText(s, p.GoalID), "∨") {
			impID = p.GoalID
		}
	}
	_, err = e.Defer(ctx, &DeferRequest{SessionID: sid, GoalID: impID, Name: "Undone", Note: "rolled back below"})
	require.NoError(t, err)
	require.NoError(t, e.Restore(ctx, sid, cp))
	assert.Empty(t, s.sections[0].deferred, "restore rolls the section's cards back")

	cards, err := e.Cards(&CardsRequest{})
	require.NoError(t, err)
	for _, c := range cards.Cards {
		assert.NotEqual(t, "Undone", c.Name, "and the index, which replays the transcript, lists no parent")
	}
}

// Landed cards: the view lists one a lineage knows of, landed, and
// none the store does not name — those are the corpus's, read with
// their citers and in fill order off the registry, which puts a card
// after every card its dependencies reach.
func TestCards_LandedCardsAttackersCitersAndFillOrder(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	fam := registry.NewFamily("zz_cards_landed", recordedDepsBlob(map[string][]string{
		"zz_cards_landed.Proved": {"zz_cards_landed.Leaf"},
	}))
	stub := registry.Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	leaf := fam.Add(registry.ProofEntry{
		Name:  "Leaf",
		Key:   fixtureKey(fam, "∀n:num. suc(n) = 1 ⇒ n + n = n"),
		Build: fam.Card("∀n:num. suc(n) = 1 ⇒ n + n = n", "the leaf card"),
	})
	proved := fam.Add(registry.ProofEntry{
		Name:  "Proved",
		Key:   fixtureKey(fam, "∀n m:num. suc(n) = 1 ⇒ n + m = m"),
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀n m:num. suc(n) = 1 ⇒ n + m = m"},
	})
	top := fam.Add(registry.ProofEntry{
		Name:  "Top",
		Key:   fixtureKey(fam, "∀n:num. suc(n) = 1 ⇒ n * n = n"),
		Deps:  []registry.EntryLike{proved},
		Build: fam.Card("∀n:num. suc(n) = 1 ⇒ n * n = n", "stands on Leaf through Proved"),
	})

	cards, err := e.Cards(&CardsRequest{})
	require.NoError(t, err)
	assert.Empty(t, cards.Cards, "no lineage knows of a card")

	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	lineageText(t, s, "∀n:num. suc(n) = 1 ⇒ n + n = n")
	cards, err = e.Cards(&CardsRequest{})
	require.NoError(t, err)
	require.Len(t, cards.Cards, 1, "the attacked card alone: Top no lineage knows of")
	c := cards.Cards[0]
	assert.Equal(t, leaf.Name, c.Entry)
	assert.True(t, c.Landed)
	assert.Equal(t, "the leaf card", c.Note)
	assert.Empty(t, c.Parents)
	require.Len(t, c.AttackedBy, 1)
	assert.Equal(t, info.ID, c.AttackedBy[0].Lineage)

	citers := registry.CardCiters()
	assert.Equal(t, []string{proved.Name}, citers[leaf])
	assert.Empty(t, citers[top])
	var order []string
	for _, name := range registry.CardFillOrder() {
		if entry, ok := registry.ByName(name); ok && entry.Family() == fam {
			order = append(order, name)
		}
	}
	assert.Equal(t, []string{leaf.Name, top.Name}, order, "leaves first")
	assert.Empty(t, c.Deps, "Leaf declares no Deps")

	attacker, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	sa, _ := e.getSession(attacker.ID)
	lineageText(t, sa, "∀n:num. suc(n) = 1 ⇒ n * n = n")
	cards, err = e.Cards(&CardsRequest{Lineage: attacker.ID})
	require.NoError(t, err)
	require.Len(t, cards.Cards, 1)
	assert.Equal(t, top.Name, cards.Cards[0].Entry)
	assert.Equal(t, []string{proved.Name}, cards.Cards[0].Deps, "a landed card's deps are its Deps")

	assert.Equal(t, []string{leaf.Name}, registry.CardFrontier(proved), "a proved member's frontier is the cards it reaches")
	assert.Equal(t, []string{leaf.Name, top.Name}, registry.CardFrontier(top), "a card's frontier includes itself")
	assert.True(t, top.IsCard())
	assert.Equal(t, "stands on Leaf through Proved", top.CardNote())
	assert.False(t, proved.IsCard())
}

// A specialized card cited by its name must emit the same dep as by key.
func TestDefer_PolymorphicCardNameEmits(t *testing.T) {
	for _, byName := range []bool{false, true} {
		t.Run(fmt.Sprint(byName), func(t *testing.T) {
			e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
			info, err := e.CreateSession(context.Background())
			require.NoError(t, err)
			_, err = e.SetSessionFamily(info.ID, lineageFamily, nil)
			require.NoError(t, err)
			s, _ := e.getSession(info.ID)
			g := lineageText(t, s, "∀f:(A → A). ∀x:A. f(f(x)) = x")
			asserted := deferApply(t, e, info.ID, g, TacticReq{Type: "assert", ClaimText: "∀f:(A → A). ∀x:A. f(x) = x"})
			var claim string
			for _, child := range asserted.Produced {
				if child.Changes.HypsAdded == 0 {
					claim = child.GoalID
				}
			}
			require.NotEmpty(t, claim)
			g = claim
			card, err := e.Defer(context.Background(), &DeferRequest{SessionID: info.ID, GoalID: g, Name: "IdentityMap", Note: "test card"})
			require.NoError(t, err)
			resolver := sessionCardLeafResolver(s, func(core.PropKey) (emit.ExternalLeaf, bool) { return emit.ExternalLeaf{}, false })
			_, named := resolver(core.PropKey(card.Card.Entry))
			require.True(t, named, "the recorded polymorphic source may be the entry name")
			g = lineageText(t, s, "∀f:(bool → bool). ∀x:bool. f(x) = x")
			key := card.Card.Key
			if byName {
				key = card.Card.Entry
			}
			deferApply(t, e, info.ID, g, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: key}}})
			out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 1, FuncName: "Build_UseIdentity", Family: lineageFamily, IncludePrior: []int{}})
			require.NoError(t, err)
			require.NotContains(t, out.Go, "TODO")
			require.Contains(t, out.DepNames, card.Card.Entry)
		})
	}
}

// deferDepEntry and deferOtherDepEntry are corpus entries of other
// families a card may stand on: exported and outside any internal
// package, so every family's package can import them.
const (
	deferDepEntry      = "comm_monoid.RightIdentityOn"
	deferOtherDepEntry = "group.RightIdentityOn"
)

// A defer's deps are the card's: carried on the result, rendered as the
// card entry's Deps — a card of the session by its var, rendered beside
// it though no section cites it, another family's entry qualified and
// imported — recorded where the defer named some, and held by a resume
// and the cards view.
func TestDefer_DepsAreRecordedEmittedAndResumed(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(store, dir)
	sid, _, base := assertThenDefer(t, a)
	require.Empty(t, base.Card.Deps, "a defer naming no deps mints a card standing on none")
	deps := []string{base.Card.Entry, deferDepEntry}
	sec, res, err := deferClaim(t, a, sid, "Q:bool→bool ⊢ ∀x y z:bool. zz_defer_both(x, y) ⇒ Q(x) ∨ Q(z)",
		"∀a b c:bool. a ∧ b ⇒ Q(a) ∨ Q(c)", "ConjSome", "a true conjunction makes a disjunct true",
		[]string{base.Card.Entry, " " + deferDepEntry + " ", deferDepEntry})
	require.NoError(t, err)
	require.Equal(t, "deferred", res.Status)
	assert.Equal(t, deps, res.Card.Deps, "trimmed, each once, in the order named")
	require.Len(t, res.Section.Cards, 1)
	assert.Equal(t, deps, res.Section.Cards[0].Deps)

	out, err := a.EmitSection(&EmitSectionRequest{
		SessionID: sid, Section: sec, FuncName: "Build_WithSome", Family: lineageFamily, IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted:\n%s", out.Go)
	dep, ok := registry.ByName(deferDepEntry)
	require.True(t, ok)
	assert.Contains(t, out.Go, "var ConjSome = family.Add(registry.ProofEntry{\n\tName: \"ConjSome\",\n\tKey:  \""+res.Card.Key+"\",\n"+
		"\tDeps: []registry.EntryLike{ConjSym, "+deferDepEntry+"},\n\tBuild: family.Card(")
	assert.Contains(t, out.Go, "\t\"github.com/euc-ai/xugo/library/proofs/"+dep.Family().PackageDir()+"\"\n", "the other family's package is imported")
	assert.Contains(t, out.Go, "var ConjSym = family.Add(registry.ProofEntry{\n\tName: \"ConjSym\",\n\tKey:  \""+base.Card.Key+"\",\n\tBuild: family.Card(",
		"the card a rendered card stands on is rendered, though no section cites it, with no Deps of its own")
	assert.NotContains(t, out.Go, "TODO")
	assert.Contains(t, out.DepNames, res.Card.Entry)
	assert.NotContains(t, out.DepNames, base.Card.Entry, "the member's own deps are its proof's")

	saved, err := os.ReadFile(filepath.Join(lineageDir(dir, sid), lineageFileName))
	require.NoError(t, err)
	assert.Equal(t, 1, strings.Count(string(saved), `"deps"`), "a defer naming no deps records no deps field")
	s, _ := a.getSession(sid)
	var recorded [][]string
	for _, ev := range s.lineage.Events {
		if ev.Kind == kindDefer {
			recorded = append(recorded, ev.Defer.Deps)
		}
	}
	assert.Equal(t, [][]string{nil, deps}, recorded, "the lineage records what each defer named")

	b := lineageEngine(store, dir)
	resumed, err := b.ResumeSession(context.Background(), sid)
	require.NoError(t, err)
	require.Nil(t, resumed.Diverged, "%+v", resumed.Diverged)
	require.Len(t, resumed.Sections[sec].Cards, 1)
	assert.Equal(t, deps, resumed.Sections[sec].Cards[0].Deps, "resume re-issues the deps")
	sb, _ := b.getSession(sid)
	assert.Empty(t, sb.cardFor(base.Card.Entry).deps)

	cards, err := ViewCards(dir, &CardsRequest{Key: res.Card.Key})
	require.NoError(t, err)
	require.Len(t, cards.Cards, 1)
	assert.Equal(t, deps, cards.Cards[0].Deps, "the cards view reads them off the store")
}

// A dep the card cannot stand on is refused, the fix named, and the
// leaf stays open: an empty name; a name no entry and no card of the
// session registers, a sibling written bare told its registered name;
// an entry the family's package cannot name in Go; the card itself;
// and a card standing on the card.
func TestDefer_DepsRefusals(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	ctx := context.Background()
	hidden := registry.NewFamily("zz_defer_hidden", nil)
	hidden.Add(registry.ProofEntry{
		Name:  "hiddenFact",
		Key:   fixtureKey(hidden, "∀n:num. suc(suc(n)) = n ⇒ n = 0"),
		Build: hidden.Card("∀n:num. suc(suc(n)) = n ⇒ n = 0", "an unexported card of the fixture"),
	})
	sid, _, base := assertThenDefer(t, e)
	s, _ := e.getSession(sid)
	g := lineageText(t, s, "Q:bool→bool ⊢ ∀x y z:bool. zz_defer_both(x, y) ⇒ Q(x) ∨ Q(z)")
	claim := assertClaim(t, e, sid, g, "∀a b c:bool. a ∧ b ⇒ Q(a) ∨ Q(c)")
	for _, tc := range []struct {
		deps []string
		want string
	}{
		{[]string{deferDepEntry, " "}, "deps[1] is empty"},
		{[]string{lineageFamily + ".NoSuch"}, "no registered member and no card this session minted"},
		{[]string{"ConjSym"}, "qualified too: " + base.Card.Entry},
		{[]string{"zz_defer_hidden.hiddenFact"}, "unexported entry"},
	} {
		_, err := e.Defer(ctx, &DeferRequest{SessionID: sid, GoalID: claim, Name: "ConjSome", Note: "a note", Deps: tc.deps})
		require.Error(t, err, "%q", tc.deps)
		assert.Contains(t, err.Error(), tc.want)
		_, open := s.goalIndex[claim]
		assert.True(t, open, "a refused defer leaves the leaf open")
	}
	assert.Len(t, s.cards, 1, "and mints nothing")

	some, err := e.Defer(ctx, &DeferRequest{SessionID: sid, GoalID: claim, Name: "ConjSome", Note: "a note", Deps: []string{base.Card.Entry}})
	require.NoError(t, err)
	require.Equal(t, "deferred", some.Status)
	g = lineageText(t, s, "R:bool→bool ⊢ ∀x y:bool. zz_defer_both(x, y) ⇒ R(x)")
	again := assertClaim(t, e, sid, g, "∀a b:bool. a ∧ b ⇒ R(a)")
	_, err = e.Defer(ctx, &DeferRequest{SessionID: sid, GoalID: again, Name: "ConjSym", Note: "a note", Deps: []string{base.Card.Entry}})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "the card itself")
	_, err = e.Defer(ctx, &DeferRequest{SessionID: sid, GoalID: again, Name: "ConjSymAgain", Note: "a note", Deps: []string{some.Card.Entry}})
	require.Error(t, err, "the same lemma under another name is the same card")
	assert.Contains(t, err.Error(), "stands on the card "+base.Card.Entry+" ("+some.Card.Entry+" → "+base.Card.Entry+")")
	assert.Empty(t, s.cardFor(base.Card.Entry).deps)
}

// The same lemma deferred twice is one card standing on what either
// defer named. The second defer — a section newly standing on the card,
// deps the card gains — is recorded, so a resume holds both sections'
// cards and the union, and the cards view lists both parents.
func TestDefer_SameLemmaTwiceUnionsItsDeps(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(store, dir)
	sid, firstSec, first := assertThenDeferWith(t, a, "P:bool→bool ⊢ ∀x y:bool. zz_defer_both(x, y) ⇒ P(x)",
		"∀a b:bool. a ∧ b ⇒ P(a)", "ConjSym", "commutativity of ∧, stated for the chapter", deferDepEntry)
	assert.Equal(t, []string{deferDepEntry}, first.Card.Deps)
	s, _ := a.getSession(sid)
	g := lineageText(t, s, "Q:bool→bool ⊢ ∀x y:bool. zz_defer_both(x, y) ⇒ Q(x)")
	secondSec := len(s.sections) - 1
	claim := assertClaim(t, a, sid, g, "∀a b:bool. a ∧ b ⇒ Q(a)")
	second, err := a.Defer(context.Background(), &DeferRequest{SessionID: sid, GoalID: claim, Name: "ConjSymAgain",
		Note: "the same lemma", Deps: []string{deferOtherDepEntry, deferDepEntry}})
	require.NoError(t, err)
	union := []string{deferDepEntry, deferOtherDepEntry}
	assert.Equal(t, first.Card.Entry, second.Card.Entry, "one card, its first name")
	assert.Equal(t, union, second.Card.Deps, "standing on what either defer named, in the order first named")
	assert.Equal(t, union, s.cardFor(first.Card.Entry).deps)

	b := lineageEngine(store, dir)
	resumed, err := b.ResumeSession(context.Background(), sid)
	require.NoError(t, err)
	require.Nil(t, resumed.Diverged, "%+v", resumed.Diverged)
	for _, sec := range []int{firstSec, secondSec} {
		require.Len(t, resumed.Sections[sec].Cards, 1, "section %d", sec)
		assert.Equal(t, union, resumed.Sections[sec].Cards[0].Deps, "section %d", sec)
	}

	cards, err := ViewCards(dir, &CardsRequest{Key: first.Card.Key})
	require.NoError(t, err)
	require.Len(t, cards.Cards, 1)
	assert.Equal(t, union, cards.Cards[0].Deps)
	assert.Len(t, cards.Cards[0].Parents, 2, "both sections stand on the card")
}

// zzDeferDepsPkg is the scratch package a member and its cards are
// emitted into to be compiled; its family is registered here, so that
// a session binds it.
const zzDeferDepsPkg = "zz_defer_deps"

var _ = registry.NewFamily(emitScratchFamily(zzDeferDepsPkg), nil)

// The card entries a member lands with compile with their Deps, and the
// member replays: one card stands on another card of the session, which
// no section cites, and on another family's entry through its import.
func TestDefer_DepsCompileAndReplay(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, emitScratchFamily(zzDeferDepsPkg), nil)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	deferAsserted := func(target, claim, name string, deps ...string) *DeferResult {
		t.Helper()
		g := lineageText(t, s, target)
		res, err := e.Defer(ctx, &DeferRequest{SessionID: info.ID, GoalID: assertClaim(t, e, info.ID, g, claim),
			Name: name, Note: "a probe card", Deps: deps})
		require.NoError(t, err)
		require.Equal(t, "deferred", res.Status)
		return res
	}
	base := deferAsserted("∀f:(A → A). ∀x:A. f(f(f(x))) = x", "∀f:(A → A). ∀x:A. f(f(x)) = x", "ZzDeferBase")
	top := deferAsserted("∀g:(A → A). ∀y:A. g(g(g(y))) = g(y)", "∀f:(A → A). ∀x:A. f(x) = x", "ZzDeferTop",
		base.Card.Entry, deferDepEntry)
	g := lineageText(t, s, "∀f:(bool → bool). ∀x:bool. f(x) = x")
	deferApply(t, e, info.ID, g, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: top.Card.Entry}}})
	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: len(s.sections) - 1, FuncName: "Build_ZzDeferUse",
		Family: emitScratchFamily(zzDeferDepsPkg), IncludePrior: []int{},
	})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, "\tDeps: []registry.EntryLike{ZzDeferBase, "+deferDepEntry+"},\n", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "var ZzDeferBase = family.Add(", "--- source: ---\n%s", out.Go)
	replayEmitted(t, zzDeferDepsPkg, "ZzDeferUse", out.Go)
}
