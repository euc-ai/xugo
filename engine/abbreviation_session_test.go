package engine

// A session goal stated with an abbreviation table (Session.AddGoalWith):
// the goal's texts are read under it, the output door folds a goal
// back into the names, the lineage records the table and a resume
// replays it, and emit-section renders the member as a Statement
// literal declaring the entries its texts spell.

import (
	"context"
	"go/format"
	"regexp"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean" // vec_dist, a constant at a dimension
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// abbreviatedGoal is `∀x:ind. ∀P:(bool → bool). (∀y:bool. P(y)) ⇒ P(«R»)`
// with R = F(x), over the emit fixture's F: not propositionally
// trivial, closed by auto.
func abbreviatedGoal(t *testing.T) (*dsl.AbbreviationTable, dsl.ParseResult) {
	t.Helper()
	table, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "R", Text: "F(x)"}})
	require.NoError(t, err)
	metaF, _ := curateF()
	scope := &dsl.ParseScope{
		ConstMetas:          map[string]core.ConstTermMeta{"F": metaF},
		StrictResolution:    true,
		FreshenMetaLetters:  true,
		Abbreviations:       table,
		AbbreviationBinders: map[string]bool{"x": true, "P": true},
	}
	res := dsl.ParsePropTextInScope("∀x:ind. ∀P:(bool → bool). (∀y:bool. P(y)) ⇒ P(«R»)", scope)
	require.Empty(t, res.Errors)
	return table, res
}

func TestAbbreviations_SessionReadsAndFolds(t *testing.T) {
	e := newEngine(emitSectionEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	table, parsed := abbreviatedGoal(t)
	goalID, err := s.AddGoalWith(parsed.Prop, table)
	require.NoError(t, err)

	// The root goal displays as stated: its leading binders are what
	// the entry is written over.
	assert.Equal(t, "⊢ ∀x P. (∀y. P(y)) ⇒ P(«R»)", s.Spelling().Prop(s.sections[0].root.Goal))

	// Under the strips the goal's minted x₀ is still the entry's x.
	for _, ty := range []string{"strip_quant", "strip_imp"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: ty}})
		require.NoError(t, err)
		require.True(t, res.Success, "%s: %v", ty, res.Diagnostics)
		require.NotEmpty(t, res.State.Goals)
		goalID = res.State.Goals[0].ID
	}
	ins, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
	require.NoError(t, err)
	require.Len(t, ins.Goals, 1)
	assert.Equal(t, "P₀(«R»)", s.Spelling().Term(ins.Goals[0].Statement.Conclusion()))
	// A term at another type than bool prints through the same door.
	x := ins.Goals[0].Statement.Conclusion().Frees(nil)
	for _, v := range x {
		assert.NotEmpty(t, s.Spelling().Term(v), "a %s variable prints", v.Type())
	}

	// A claim text under the goal spells the name; one that rebinds x
	// is refused.
	_, err = parseClaimTextInGoalScope("P(«R»)", ins.Goals[0].Statement, s.familyScope())
	require.NoError(t, err)
	_, err = parseClaimTextInGoalScope("∃x:num. P(«R»)", ins.Goals[0].Statement, s.familyScope())
	require.Error(t, err)
	assert.Contains(t, err.Error(), "rebinds")

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, res.Success, "auto: %v", res.Diagnostics)
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_Abbreviated", Family: "real/real_field"})
	require.NoError(t, err)
	assert.Contains(t, out.Go, "family.Theorem(Statement{\n"+
		"\t\tBinders: \"∀x:ind. ∀P:(bool → bool).\",\n"+
		"\t\tHypotheses: []string{\n"+
		"\t\t\t\"∀y:bool. P(y)\",\n"+
		"\t\t},\n"+
		"\t\tConclusion: \"P(«R»)\",\n"+
		"\t\tAbbrev: Abbrev{\n"+
		"\t\t\t{Name: \"R\", Text: \"F(x)\"},\n"+
		"\t\t},\n"+
		"\t},\n"+
		"\t\tfunc(a *Argument, x *Expr[Ind], P *Expr[Set[Bool]], _ Fact) {")
	formatted, err := format.Source([]byte(out.Go))
	require.NoError(t, err)
	assert.Equal(t, string(formatted), out.Go, "the member is gofmt-clean")
}

func TestAbbreviations_LineageReplaysTheTable(t *testing.T) {
	memory := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(memory, dir)
	metaF, _ := curateF()
	a.env.ProofService.LoadOrStoreConstMeta(metaF)
	ctx := context.Background()
	info, err := a.CreateSession(ctx)
	require.NoError(t, err)
	s, err := a.getSession(info.ID)
	require.NoError(t, err)
	table, parsed := abbreviatedGoal(t)
	s.mu.Lock()
	goalID, err := s.AddGoalWith(parsed.Prop, table)
	s.mu.Unlock()
	require.NoError(t, err)
	res, err := a.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, res.Success, "auto: %v", res.Diagnostics)

	b := lineageEngine(memory, dir)
	b.env.ProofService.LoadOrStoreConstMeta(metaF)
	resumed, err := b.ResumeSession(ctx, info.ID)
	require.NoError(t, err)
	require.NotNil(t, resumed)
	s2, err := b.getSession(info.ID)
	require.NoError(t, err)
	require.Len(t, s2.sections, 1)
	require.NotNil(t, s2.sections[0].abbreviations, "the resumed section carries the recorded table")
	assert.Equal(t, []string{"R"}, s2.sections[0].abbreviations.Names())
	assert.True(t, s2.sections[0].root.Proved())
}

// assertRendersStatement checks that src renders the statement text as
// emit-section writes it: in parts where it has a premise (each part
// quoted as the literal spells it), the one string otherwise.
func assertRendersStatement(t *testing.T, src, text string) {
	t.Helper()
	parts, ok := dsl.SplitStatement(text)
	require.True(t, ok, "the statement %q splits", text)
	if len(parts.Hypotheses) == 0 {
		canonical, err := dsl.FormatStmtText(text)
		require.NoError(t, err)
		assert.True(t, strings.Contains(src, strconv.Quote(text)) || strings.Contains(src, strconv.Quote(canonical)),
			"the one string %q is rendered", text)
		return
	}
	if parts.Binders != "" {
		assert.Contains(t, src, "Binders: "+strconv.Quote(parts.Binders))
	}
	for _, h := range parts.Hypotheses {
		assert.Contains(t, src, strconv.Quote(h)+",")
	}
	assert.Regexp(t, `Conclusion: +`+regexp.QuoteMeta(strconv.Quote(parts.Conclusion)), src)
}

// A session bound to a family that declares a table
// (registry.Family.WithAbbrev) reads every text under it before any
// goal is added: the statement door declares the chapter's names, the
// session's one table holds them, and a goal's own table is read under
// them.
func TestAbbreviations_FamilyTableIsTheSessionsOuterTable(t *testing.T) {
	fam := registry.NewFamily("zz_session_chapter_abbrev", nil).WithAbbrev(dsl.Abbrev{{Name: "R", Text: "F(x)"}})
	e := newEngine(emitSectionEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, fam.Name, nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	require.True(t, s.StatementDoorScope().Abbreviations.Has("R"), "the statement door declares the chapter's names")
	require.True(t, s.abbreviationTable().Has("R"), "the session's table holds the chapter's before any goal")
	require.True(t, s.familyScope().abbreviations.Has("R"))

	own, err := s.StatementDoorScope().Abbreviations.Extend(dsl.Abbrev{{Name: "S", Text: "G(«R»)"}})
	require.NoError(t, err)
	require.Equal(t, []string{"R", "S"}, own.Names(), "a goal's own entries are read under the chapter's")
	_, err = s.StatementDoorScope().Abbreviations.Extend(dsl.Abbrev{{Name: "R", Text: "x"}})
	require.Error(t, err, "a goal redeclaring the chapter's name is refused")
	assert.Contains(t, err.Error(), "one name, one meaning")

	vocab := familyVocabForEmit(fam.Name)
	assert.Equal(t, map[string]bool{"R": true}, vocab.Abbrev, "emit is told the chapter's names")
}

// A session's sections spell one table: a later goal may declare a
// name an earlier section declares with the same text (one entry), and
// a goal declaring it with another text is refused, the error naming
// the section and both texts — a claim never reads a name with another
// section's meaning.
func TestAbbreviations_ASecondTextForANameIsRefused(t *testing.T) {
	e := newEngine(emitSectionEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	table, parsed := abbreviatedGoal(t)
	_, err = s.AddGoalWith(parsed.Prop, table)
	require.NoError(t, err)

	other, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "R", Text: "F(F(x))"}})
	require.NoError(t, err)
	_, err = s.AddGoalWith(parsed.Prop, other)
	require.Error(t, err)
	assert.Contains(t, err.Error(), "«R» is declared by section 0 as `F(x)` and by this goal as `F(F(x))`")
	assert.Contains(t, err.Error(), "one name, one meaning")
	assert.Len(t, s.sections, 1, "the refused goal adds no section")
	assert.Equal(t, []string{"R"}, s.abbreviationTable().Names())

	alike, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "R", Text: "F(x)"}, {Name: "S", Text: "F(«R»)"}})
	require.NoError(t, err)
	_, err = s.AddGoalWith(parsed.Prop, alike)
	require.NoError(t, err, "the same text is one entry")
	assert.Len(t, s.sections, 2)
	assert.Equal(t, []string{"R", "S"}, s.abbreviationTable().Names(), "the session's table declares each name once")
	assert.Equal(t, "⊢ ∀x P. (∀y. P(y)) ⇒ P(«R»)", s.Spelling().Prop(s.sections[0].root.Goal), "the first section still reads its own name")
}

// A goal stated through an abbreviation of a constant at its dimension,
// applied — «d»(v) for d ≔ vec_dist⟨n⟩(u), in a session bound to the
// chapter that declares the dimension — is the goal its text written
// out states. The session serves it spelling the abbreviation, and the
// claim door reads what the session serves back as the goal.
func TestAbbreviations_AppliedAtADimension(t *testing.T) {
	e := newEngine(familySessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "vector/euclidean", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	table, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "d", Text: "vec_dist⟨n⟩(u)"}})
	require.NoError(t, err)
	scope := s.StatementDoorScope()
	scope.Abbreviations = table
	scope.AbbreviationBinders = map[string]bool{"n": true, "u": true, "v": true}
	short := dsl.ParsePropTextAtDoor("∀n:num. ∀u v:(num → real). «d»(v) = «d»(v)", scope)
	require.Empty(t, short.Errors)
	written := dsl.ParsePropTextAtDoor("∀n:num. ∀u v:(num → real). vec_dist⟨n⟩(u, v) = vec_dist⟨n⟩(u, v)", s.StatementDoorScope())
	require.Empty(t, written.Errors)
	require.Equal(t, written.Prop.AlphaKey(), short.Prop.AlphaKey(), "the applied abbreviation and the text written out are one statement")

	goalID, err := s.AddGoalWith(short.Prop, table)
	require.NoError(t, err)
	assert.Equal(t, "⊢ ∀n u v. «d»(v) = «d»(v)", s.Spelling().Prop(s.sections[0].root.Goal))
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "strip_quant"}})
	require.NoError(t, err)
	require.True(t, res.Success, "strip_quant: %v", res.Diagnostics)
	ins, err := e.Inspect(ctx, info.ID, &InspectRequest{})
	require.NoError(t, err)
	require.Len(t, ins.Goals, 1)
	goal := ins.Goals[0].Statement
	served := s.Spelling().Term(goal.Conclusion())
	assert.Equal(t, "«d»(v₀) = «d»(v₀)", served)
	back, err := parseClaimTextInGoalScope(served, goal, s.familyScope())
	require.NoError(t, err, "the session reads back the goal it serves")
	assert.True(t, back.Conclusion().AlphaEquals(goal.Conclusion()), "read back as %s", s.Spelling().Term(back.Conclusion()))
}
