package engine

// Tests for emit-section: a closed session section → in-memory
// DetailedProofProto → emit.EmitMember → a family member plus the CNF
// certificates its replay reads. See emit_section.go.

import (
	"context"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"regexp"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/xugofmt"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// emitSectionEnv is testEnv() with curateF's F meta registered so
// PoolReader-driven decode (emit's decodeSections, CollectCNFCache)
// can resolve the "F" const during proto deserialization.
func emitSectionEnv(t *testing.T) *proof.ProverEnv {
	t.Helper()
	env := testEnv()
	metaF, _ := curateF()
	env.ProofService.LoadOrStoreConstMeta(metaF)
	return env
}

// emitSectionSequent is a sequent auto closes that is NOT
// propositionally trivial (a section whose statement normalizes to ⊤ has
// no body to render, and emit refuses it): ∀x. F(x), F(a) ⇒ q ⊢ q.
func emitSectionSequent() core.Prop {
	_, F := curateF()
	a := ext.Var("a", TypeInd)
	x := ext.WrapTerm(ext.Var("x", TypeInd))
	q := ext.Var("q", core.TypeBool())
	return prop.MakeProp(q,
		ext.ForAll(x)(F.Apply(x)).Core(),
		ext.WrapTerm(F.Apply(a).Core()).Imply(q).Core())
}

// closedStatement is sequent's closed statement: its hypotheses curried
// onto the conclusion as premises, its free variables left free. A
// section states a closed theorem, which emit requires.
func closedStatement(sequent core.Prop) core.Prop {
	closed := sequent.Conclusion()
	for i := sequent.NumHyps() - 1; i >= 0; i-- {
		closed = ext.WrapTerm(sequent.Hyp(i)).Imply(closed).Core()
	}
	return prop.MakeProp(closed)
}

// addStrippedGoal adds sequent's closed statement as a new section and
// strips the premises with strip_imp, returning the id of the goal the
// strips leave, which states sequent: a fixture's steps are written
// against the stripped goal.
func addStrippedGoal(t *testing.T, e *Engine, sessionID string, sequent core.Prop) string {
	t.Helper()
	ctx := context.Background()
	s, err := e.getSession(sessionID)
	require.NoError(t, err)
	goalID := s.AddGoal(closedStatement(sequent))
	section := fmt.Sprintf("s%d_", len(s.sections)-1)
	for range sequent.NumHyps() {
		res, err := e.ApplyStep(ctx, sessionID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "strip_imp"}})
		require.NoError(t, err)
		require.True(t, res.Success, "strip_imp failed; diagnostics: %v", res.Diagnostics)
		state, err := e.InspectState(ctx, sessionID)
		require.NoError(t, err)
		goalID = ""
		for _, g := range state.Goals {
			if strings.HasPrefix(g.ID, section) {
				goalID = g.ID
				if g.Statement.AlphaEquals(sequent) {
					return goalID
				}
			}
		}
		require.NotEmpty(t, goalID, "the stripped section has no open goal")
	}
	t.Fatalf("stripping %s did not reach the sequent", prop.PrintProp(closedStatement(sequent)))
	return ""
}

// addClosedSequent adds emitSectionSequent's closed statement as a new
// section and closes it with auto, returning the section index.
func addClosedSequent(t *testing.T, e *Engine, sessionID string) int {
	t.Helper()
	ctx := context.Background()
	s, err := e.getSession(sessionID)
	require.NoError(t, err)
	goalID := s.AddGoal(closedStatement(emitSectionSequent()))
	res, err := e.ApplyStep(ctx, sessionID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "auto"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "auto should close the sequent; diagnostics: %v", res.Diagnostics)
	idx := len(s.sections) - 1
	require.True(t, s.sections[idx].root.Proved())
	return idx
}

// TestEmitSection_RefusesASequentGoal: a section states a closed
// theorem, so a section proved on a goal with hypotheses — the session
// stated a sequent — is refused, naming the closed spelling the goal
// should have stated.
func TestEmitSection_RefusesASequentGoal(t *testing.T) {
	e := newEngine(emitSectionEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	goalID := s.AddGoal(emitSectionSequent())
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, res.Success, "auto should close the sequent; diagnostics: %v", res.Diagnostics)

	_, err = e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_Sequent", Family: "real/real_field"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "a section states a closed theorem")
	assert.Contains(t, err.Error(), "((∀x:ind.F(x)) ⇒ ((F(a) ⇒ q) ⇒ q))")
}

// TestEmitSection_DefaultsFuncName: caller omits func_name → the member
// is named Draft.
func TestEmitSection_DefaultsFuncName(t *testing.T) {
	e := newEngine(emitSectionEnv(t))
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	addClosedSequent(t, e, info.ID)

	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID,
		Section:   0,
		Family:    "real/real_field",
	})
	require.NoError(t, err)
	assert.Equal(t, "Build_Draft", out.FuncName)
	assert.Contains(t, out.Go, "var Draft = family.Add(registry.ProofEntry{")
}

// TestEmitSection_NeedsAFamily: every emitted file is a family member,
// so a session bound to no family must name one; a bound session's
// family is the default.
func TestEmitSection_NeedsAFamily(t *testing.T) {
	e := newEngine(emitSectionEnv(t))
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	addClosedSequent(t, e, info.ID)

	_, err = e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_NoFamily"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "no family")

	bound, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(bound.ID, "sets/set_order", nil)
	require.NoError(t, err)
	addClosedSequent(t, e, bound.ID)
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: bound.ID, Section: 0, FuncName: "Build_BoundFamily"})
	require.NoError(t, err)
	assert.Contains(t, out.Go, "package set_order")
}

// TestEmitSection_UnprovedSectionRejected: emit-section requires a
// closed section — an open one must error, not emit garbage.
func TestEmitSection_UnprovedSectionRejected(t *testing.T) {
	_, F := curateF()
	a := ext.Var("a", TypeInd)
	// Uninterpreted F(a) — no way for auto to close it (nothing is
	// known about F). The section root stays unproved.
	goalProp := prop.MakeProp(F.Apply(a))

	e := newEngine(emitSectionEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	s.AddGoal(goalProp)
	require.False(t, s.sections[0].root.Proved())

	_, err = e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID,
		Section:   0,
		FuncName:  "Build_UnprovedSection",
		Family:    "real/real_field",
	})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "not proved")
}

// TestEmitSection_OutOfRangeSection: caller passes a section index the
// session doesn't have.
func TestEmitSection_OutOfRangeSection(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	_, err = e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID,
		Section:   5,
		FuncName:  "Build_OOR",
		Family:    "real/real_field",
	})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "out of range")
}

// TestEmitSection_UnknownSession: unknown session id errors cleanly.
func TestEmitSection_UnknownSession(t *testing.T) {
	e := newEngine(testEnv())
	_, err := e.EmitSection(&EmitSectionRequest{
		SessionID: "does-not-exist",
		Section:   0,
		FuncName:  "Build_X",
		Family:    "real/real_field",
	})
	require.Error(t, err)
}

// lemmaAndCitingSession proves `∀n:num. n ≤ n + 1` as section 0 of a
// fresh session bound to nat_order, opens `goal` as section 1 and
// strips its binders; it returns the engine, the session and section
// 0's node id for a `cite-node`.
func lemmaAndCitingSession(t *testing.T, goal string) (*Engine, *Session, string) {
	t.Helper()
	e := newEngine(statedSessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "nat_num/nat_order", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	addTextGoal(t, s, "∀n:num. n ≤ n + 1")
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "arith"})
	require.True(t, s.sections[0].root.Proved(), "section 0 must close")

	addTextGoal(t, s, goal)
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
	return e, s, closedNodeID(0, s.sections[0].root.Goal)
}

// TestEmitSection_IncludePriorEmpty: IncludePrior=[]int{} (non-nil,
// empty) leaves every other section out, the one the target cites
// with them, where the default would bring that one in as a lemma. The
// member has the target section alone, and its `cite-node` of the
// section left out renders as the assert it recorded, that section's
// proof inline under the claim.
func TestEmitSection_IncludePriorEmpty(t *testing.T) {
	e, s, lemmaNode := lemmaAndCitingSession(t, "∀k:num. k ≤ k + 1 + 1")
	hyp := 0
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "cite-node", NodeID: lemmaNode})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "instantiate", HypIndex: &hyp, Terms: []string{"k + 1"}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "arith"})
	require.True(t, s.sections[1].root.Proved(), "section 1 must close")

	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: s.ID, Section: 1, FuncName: "Build_TargetOnly", IncludePrior: []int{},
	})
	require.NoError(t, err)
	assert.Equal(t, []int{1}, out.SectionsIncluded, "the target alone")
	parsesAsGo(t, out.Go)
	assert.NotContains(t, out.Go, "ctx.Lemma(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, `AssertStep(ctx.MakePropText("∀n:num. n ≤ n + 1"),`, "--- source: ---\n%s", out.Go)
}

// TestEmitSection_IncludePriorCiteNode: a `cite-node` of an included
// earlier section's root renders as a cite of that section's lemma
// variable — at its witnesses, where the cite is grounded — and the
// section's proof is rendered once, as the lemma's own body. The
// recorded shape is an assert of the section's statement whose claim
// branch is the section's proof again.
func TestEmitSection_IncludePriorCiteNode(t *testing.T) {
	e, s, lemmaNode := lemmaAndCitingSession(t, "∀k:num. k ≤ k + 1 + 1")
	hyp := 0
	// Once grounded by the cite itself, once by the step after it.
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "cite-node", NodeID: lemmaNode, TermSpecialize: map[string]string{"n": "k"}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "cite-node", NodeID: lemmaNode})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "instantiate", HypIndex: &hyp, Terms: []string{"k + 1"}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "arith"})
	require.True(t, s.sections[1].root.Proved(), "section 1 must close")

	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: s.ID, Section: 1, FuncName: "Build_CitesItsLemma", IncludePrior: []int{0},
	})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Equal(t, []int{0, 1}, out.SectionsIncluded)
	assert.Contains(t, out.Go, `lemma1 := ctx.Lemma("∀n:num. n ≤ n + 1",`, "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "Cite(lemma1, k),", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, `Cite(lemma1, a.TermAs[Nat]("k + 1")),`,
		"a witness that is no variable is the text the session read, typed by its phantom\n--- source: ---\n%s", out.Go)
	assert.Equal(t, 2, strings.Count(out.Go, "Cite(lemma1, "),
		"each cite-node is one cite of the lemma variable at its witness\n--- source: ---\n%s", out.Go)
	// Section 0's proof — strip, arith — stands once, under ctx.Lemma;
	// section 1 strips and closes by arith once itself. Each strip is its
	// closure's parameter.
	assert.Contains(t, out.Go, "func(a *Argument, n *Expr[Nat]) {", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "func(a *Argument, k *Expr[Nat]) {", "--- source: ---\n%s", out.Go)
	assert.Equal(t, 0, strings.Count(out.Go, "StripQuant(),"), "--- source: ---\n%s", out.Go)
	assert.Equal(t, 2, strings.Count(out.Go, "Arith(),"), "--- source: ---\n%s", out.Go)
	for _, inlined := range []string{"AssertStep(", "ClearHyps(", "Specialize("} {
		assert.NotContains(t, out.Go, inlined, "--- source: ---\n%s", out.Go)
	}
}

// TestEmitSection_CiteNodeClaimClosesOnTheSection: where the cite verb,
// run on the citing goal, would do more than the recorded assert did —
// here the section's statement matches the goal's conclusion, so a
// cite would chain backward and close it — the assert keeps its own
// rendering, and its claim branch closes on the lemma variable in
// place of the section's proof.
func TestEmitSection_CiteNodeClaimClosesOnTheSection(t *testing.T) {
	e, s, lemmaNode := lemmaAndCitingSession(t, "∀k:num. k + 1 ≤ k + 1 + 1")
	hyp := 0
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "cite-node", NodeID: lemmaNode})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "instantiate", HypIndex: &hyp, Terms: []string{"k + 1"}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "arith"})
	require.True(t, s.sections[1].root.Proved(), "section 1 must close")

	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: s.ID, Section: 1, FuncName: "Build_ClaimOnItsLemma", IncludePrior: []int{0},
	})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Regexp(t, regexp.MustCompile(`AssertStep\(ctx\.MakePropText\("∀n:num\. n ≤ n \+ 1"\),\n\s*Case\(\n\s*"claim: [^"]*",\n(\s*//[^\n]*\n)*\s*Cite\(lemma1\),\n\s*\),`), out.Go,
		"the claim branch is the cite of the lemma variable")
	assert.Equal(t, 1, strings.Count(out.Go, "Cite(lemma1"), "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "Specialize(InstHyp(0, ", "the recorded grounding stays the assert's continuation\n--- source: ---\n%s", out.Go)
	assert.Equal(t, 0, strings.Count(out.Go, "StripQuant(),"), "each strip is its closure's parameter\n--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "ClearHyps(", "--- source: ---\n%s", out.Go)
}

// TestEmitSection_IncludePriorRejectsInvalid exercises the validation
// paths on IncludePrior — target self-reference, OOR, a section the
// target does not cite, duplicate, unproved. Each must error cleanly
// with an informative message.
func TestEmitSection_IncludePriorRejectsInvalid(t *testing.T) {
	_, F := curateF()
	a := ext.Var("a", TypeInd)

	e := newEngine(emitSectionEnv(t))
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)

	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	// Sections 0, 1, 2 — all closed.
	for i := 0; i < 3; i++ {
		addClosedSequent(t, e, info.ID)
	}
	// Section 3 open (unproved).
	s.AddGoal(prop.MakeProp(F.Apply(a))) // uninterpreted, won't close
	require.False(t, s.sections[3].root.Proved())
	// Section 4 closed.
	addClosedSequent(t, e, info.ID)

	for _, tc := range []struct {
		name    string
		section int
		prior   []int
		want    string
	}{
		{"target listed", 2, []int{0, 2}, "is the target section"},
		{"out of range", 2, []int{99}, "out of range"},
		{"uncited", 1, []int{2}, "sections [2] are cited by no section the target reaches"},
		{"duplicate", 2, []int{0, 0}, "duplicate"},
		{"unproved prior", 4, []int{3}, "not proved"},
	} {
		_, err = e.EmitSection(&EmitSectionRequest{
			SessionID:    info.ID,
			Section:      tc.section,
			IncludePrior: tc.prior,
			Family:       "real/real_field",
		})
		require.Error(t, err, tc.name)
		assert.Contains(t, err.Error(), tc.want, tc.name)
	}
}

// TestEmitSection_FamilyProfile: the member scaffold (family.Add entry
// var + family.Theorem binder closure), in xugo_fmt's layout, with the
// entry Key the statement's own normalized key; the CNF certificates
// the replay reads come back beside the source, never wired into it.
func TestEmitSection_FamilyProfile(t *testing.T) {
	e := newEngine(emitSectionEnv(t))
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	addClosedSequent(t, e, info.ID)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID,
		Section:   0,
		FuncName:  "Build_Taut",
		Family:    "real/real_field",
	})
	require.NoError(t, err)
	require.NotNil(t, out)
	assert.Equal(t, 0, out.SectionID)
	assert.Equal(t, "Build_Taut", out.FuncName)
	assert.Equal(t, []int{0}, out.SectionsIncluded)

	if _, err := parser.ParseFile(token.NewFileSet(), "fam.go", out.Go, parser.AllErrors); err != nil {
		t.Fatalf("family output does not parse: %v\n--- source: ---\n%s", err, out.Go)
	}

	// Package clause from the family's last path segment; the member
	// scaffold is code.
	assert.Contains(t, out.Go, "package real_field")
	assert.Contains(t, out.Go, `"github.com/euc-ai/xugo/library/registry"`)
	assert.Contains(t, out.Go, "var Taut = family.Add(registry.ProofEntry{")
	assert.Contains(t, out.Go, `Name: "Taut",`)
	// The entry's Key is the statement's OWN normalized key (what the
	// harness recomputes from the headline).
	assert.Contains(t, out.Go, fmt.Sprintf("Key:  %q,", string(registry.KeyOf(s.sections[0].root.Goal))))
	// One declaration per entry: the Build constructor sits inline as
	// the literal's last field (the entry lint's E1).
	// The statement is the Theorem call's first argument, inline — no
	// hoisted GoalText const for a text with one site — in parts, since
	// the standard form of the curried sequent has premises.
	assert.Contains(t, out.Go, "\tBuild: family.Theorem(Statement{\n")
	assert.Contains(t, out.Go, "\t\tHypotheses: []string{\n\t\t\t\"∀x:ind. F(x)\",\n\t\t\t\"F(a) ⇒ q\",\n\t\t},\n\t\tConclusion: \"q\",\n")
	assert.Contains(t, out.Go, ",\n\t\tfunc(a *Argument) {")
	if formatted, err := xugofmt.Source([]byte(out.Go)); err != nil {
		t.Fatalf("family output does not format: %v\n--- source: ---\n%s", err, out.Go)
	} else if string(formatted) != out.Go {
		t.Errorf("family output is not in xugo_fmt's layout\n--- emitted: ---\n%s\n--- xugo_fmt: ---\n%s", out.Go, formatted)
	}
	for _, banned := range []string{"go:embed", "InstallCNFCache", "DO NOT EDIT"} {
		assert.NotContains(t, out.Go, banned)
	}
}

// TestEmitSection_FamilyDepResolver: the typed-dep resolver against the
// REAL proof registry (populated via curate_session_test.go's blank
// import of the chapter aggregator). Same-family hits render the bare member
// name; cross-family hits render the package-qualified registered name
// plus its import; misses fall back (→ DepNames strings).
func TestEmitSection_FamilyDepResolver(t *testing.T) {
	e := newEngine(testEnv())
	resolve := e.familyDepEntryForEmit("real/real_field", map[string]*registry.ProofEntry{})

	// Same family: bare member name, no import.
	ref, ok := resolve("real_field.MulRightInverse", "")
	require.True(t, ok, "real_field.MulRightInverse should resolve")
	assert.Equal(t, "MulRightInverse", ref.Expr)
	assert.Empty(t, ref.ImportPath)

	// Cross family: the registered name IS the qualified Go spelling.
	ref, ok = resolve("real_ring.NegNeg", "")
	require.True(t, ok, "real_ring.NegNeg should resolve")
	assert.Equal(t, "real_ring.NegNeg", ref.Expr)
	assert.Equal(t, "github.com/euc-ai/xugo/library/proofs/real/real_ring", ref.ImportPath)

	// A name no entry claims stays on the string arm.
	_, ok = resolve("NO_SUCH_THEOREM_ANYWHERE", "")
	assert.False(t, ok)

	// A member of another tree's internal package is no dependency here.
	_, ok = resolve("eudoxus_slope.AddSym", "")
	assert.False(t, ok, "eudoxus_slope is internal to real/tower")
}

// TestEmitSection_LemmaCloseCitesTheEntryVar: a leaf closed by `lemma
// {lemma_key}` on a landed member renders the cite as the entry var —
// bare for a sibling, package-qualified with its import across
// families — the spelling a By premise and the Deps list give the same
// member; the quoted registered name is for a name no entry carries.
func TestEmitSection_LemmaCloseCitesTheEntryVar(t *testing.T) {
	entry, ok := registry.ByName("set_order.SubsetRefl")
	require.True(t, ok)
	for _, tc := range []struct {
		family, cite, dep string
		imported          bool
	}{
		{"sets/set_order", "Cite(SubsetRefl),", "SubsetRefl", false},
		{"real/real_field", "Cite(set_order.SubsetRefl),", "set_order.SubsetRefl", true},
	} {
		e := newEngine(statedSessionEnv())
		info, err := e.CreateSession(context.Background())
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		s.AddGoal(entry.Statement().Prop)
		applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "lemma", LemmaKey: "set_order.SubsetRefl"})
		require.True(t, s.sections[0].root.Proved(), "the cite closes the goal it states")

		out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_CitesByKey", Family: tc.family})
		require.NoError(t, err, tc.family)
		parsesAsGo(t, out.Go)
		assert.Contains(t, out.Go, tc.cite, "--- source: ---\n%s", out.Go)
		assert.NotContains(t, unspaced(out.Go), `Cite("`, "the string channel beside a typed dep\n--- source: ---\n%s", out.Go)
		assert.NotContains(t, out.Go, "Deps:", "a proved member renders no Deps — its recording observes what it reads\n--- source: ---\n%s", out.Go)
		assert.Equal(t, tc.imported, strings.Contains(out.Go, `"github.com/euc-ai/xugo/library/proofs/sets/set_order"`),
			"--- source: ---\n%s", out.Go)
		assert.Contains(t, out.DepNames, "set_order.SubsetRefl")
	}
}

// equivalenceInstanceSession opens `equivalence(nadd_eq)` in a session
// bound to the slope family and returns the engine and the session.
func equivalenceInstanceSession(t *testing.T) (*Engine, *Session) {
	t.Helper()
	e := newEngine(statedSessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "real/tower/eudoxus_slope", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "equivalence(nadd_eq)")
	return e, s
}

// applyOnGoalProving applies a tactic to the open goal whose conclusion
// prints as concl.
func applyOnGoalProving(t *testing.T, e *Engine, s *Session, concl string, tactic TacticReq) {
	t.Helper()
	ctx := context.Background()
	state, err := e.InspectState(ctx, s.ID)
	require.NoError(t, err)
	var open []string
	for _, g := range state.Goals {
		printed := ext.PrintTerm(g.Statement.Conclusion())
		if printed != concl {
			open = append(open, printed)
			continue
		}
		res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: tactic})
		require.NoError(t, err)
		require.True(t, res.Success, "%s failed; diagnostics: %v", tactic.Type, res.Diagnostics)
		return
	}
	t.Fatalf("no open goal proves %s; open: %v", concl, open)
}

// TestEmitSection_StructureInstanceRendersTheInstanceDoor: a section
// whose statement applies a registered structure's predicate, and
// whose proof unfolds the predicate and closes one branch per conjunct,
// renders as family.Instance — the structure's var, the statement, one
// Case per conjunct with the binary splits flattened — the form the
// chapters land an instance in (eudoxus_slope.NaddEqEquivalence is this one).
func TestEmitSection_StructureInstanceRendersTheInstanceDoor(t *testing.T) {
	e, s := equivalenceInstanceSession(t)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "def_expand", Const: "equivalence"})
	// The definition's conjunction is split in two binary steps.
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "split_conj"})
	applyOnGoalProving(t, e, s, "reflexive(nadd_eq) ∧ symmetric(nadd_eq)", TacticReq{Type: "split_conj"})
	applyOnGoalProving(t, e, s, "reflexive(nadd_eq)", TacticReq{Type: "def_expand", Const: "reflexive"})
	applyOnGoalProving(t, e, s, "∀x.nadd_eq(x, x)", TacticReq{Type: "lemma", LemmaKey: "eudoxus_slope.NaddEqRefl"})
	applyOnGoalProving(t, e, s, "symmetric(nadd_eq)", TacticReq{Type: "def_expand", Const: "symmetric"})
	applyOnGoalProving(t, e, s, "∀x.∀y.(nadd_eq(x, y) ⇒ nadd_eq(y, x))", TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "eudoxus_slope.NaddEqSym"}}})
	applyOnGoalProving(t, e, s, "transitive(nadd_eq)", TacticReq{Type: "def_expand", Const: "transitive"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "eudoxus_slope.NaddEqTrans"}}})
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: "Build_ZzNaddEqEquivalence"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	if formatted, err := xugofmt.Source([]byte(out.Go)); err != nil {
		t.Fatalf("instance output does not format: %v\n--- source: ---\n%s", err, out.Go)
	} else if string(formatted) != out.Go {
		t.Errorf("instance output is not in xugo_fmt's layout\n--- emitted: ---\n%s\n--- xugo_fmt: ---\n%s", out.Go, formatted)
	}
	for _, want := range []string{
		`"github.com/euc-ai/xugo/library/proofs/relations/equivalence"`,
		"\tBuild: family.Instance(equivalence.Equivalence, \"equivalence(nadd_eq)\",\n",
		"\t\tCase(\n\t\t\t\"case_0: reflexive(nadd_eq)\",\n",
		"\t\t\tUnfold(equivalence.ReflexiveDef),\n\t\t\tCite(NaddEqRefl),\n\t\t),\n",
		"\t\tCase(\n\t\t\t\"case_1: symmetric(nadd_eq)\",\n",
		"\t\t\tUnfold(equivalence.SymmetricDef),\n\t\t\tBy(NaddEqSym),\n\t\t),\n",
		"\t\tCase(\n\t\t\t\"case_2: transitive(nadd_eq)\",\n",
		"\t\t\tUnfold(equivalence.TransitiveDef),\n\t\t\tBy(NaddEqTrans),\n\t\t),\n\t),\n})\n",
	} {
		assert.Contains(t, out.Go, want, "--- source: ---\n%s", out.Go)
	}
	assert.NotContains(t, out.Go, "Deps:", "a proved member renders no Deps — its recording observes what it reads\n--- source: ---\n%s", out.Go)
	// The door unfolds the predicate and splits the conjunction itself.
	for _, banned := range []string{"family.Theorem(", "SplitConj", "Unfold(equivalence.Equivalence)", "func(a *Argument)"} {
		assert.NotContains(t, out.Go, banned, "--- source: ---\n%s", out.Go)
	}

	// The same statement proved any other way than the door's own —
	// here closed outright by the landed instance — stays a
	// family.Theorem.
	e, s = equivalenceInstanceSession(t)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "lemma", LemmaKey: "eudoxus_slope.NaddEqEquivalence"})
	require.True(t, s.sections[0].root.Proved())
	cited, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: "Build_ZzNaddEqEquivalence"})
	require.NoError(t, err)
	parsesAsGo(t, cited.Go)
	assert.Contains(t, cited.Go, "\tBuild: family.Theorem(\"equivalence(nadd_eq)\",\n", "--- source: ---\n%s", cited.Go)
	assert.NotContains(t, cited.Go, "family.Instance(", "--- source: ---\n%s", cited.Go)
}

// headlineOf reads the statement literal a rendered single-section
// member hands its constructor.
func headlineOf(t *testing.T, src string) string {
	t.Helper()
	f, err := parser.ParseFile(token.NewFileSet(), "member.go", src, 0)
	require.NoError(t, err, "the emitted member parses:\n%s", src)
	headline, found := "", false
	ast.Inspect(f, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || found || len(call.Args) == 0 {
			return true
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		if !ok || sel.Sel.Name != "Theorem" {
			return true
		}
		if x, ok := sel.X.(*ast.Ident); !ok || x.Name != "family" {
			return true
		}
		headline, found = statementArgText(t, call.Args[0]), true
		return false
	})
	require.True(t, found, "no family.Theorem headline in:\n%s", src)
	return headline
}

// statementArgText is the statement a constructor's first argument
// states: a string, the one literal or the chain xugofmt lays a long
// one out as, read on one line (dsl.OneLine); a Statement literal
// assembled as the constructor assembles it (dsl.Statement.Text).
func statementArgText(t *testing.T, arg ast.Expr) string {
	t.Helper()
	unquote := func(e ast.Expr) string {
		s, ok := xugofmt.StringValue(e)
		require.True(t, ok, "a statement part is a string literal or a chain of them")
		return dsl.OneLine(s)
	}
	if _, ok := xugofmt.StringValue(arg); ok {
		return unquote(arg)
	}
	cl, ok := arg.(*ast.CompositeLit)
	require.True(t, ok, "the statement is a string or a Statement literal")
	var st dsl.Statement
	for _, elt := range cl.Elts {
		kv := elt.(*ast.KeyValueExpr)
		switch kv.Key.(*ast.Ident).Name {
		case "Binders":
			st.Binders = unquote(kv.Value)
		case "Conclusion":
			st.Conclusion = unquote(kv.Value)
		case "Hypotheses":
			for _, h := range kv.Value.(*ast.CompositeLit).Elts {
				st.Hypotheses = append(st.Hypotheses, unquote(h))
			}
		default:
			t.Fatalf("statementArgText reads no %s of a Statement literal", kv.Key.(*ast.Ident).Name)
		}
	}
	text, err := st.Text()
	require.NoError(t, err)
	return text
}

// TestEmitSection_SetBuilderHeadlineIsTheSurfaceForm: a headline whose
// statement holds a two-index set-builder prints it as one — the
// chapter's surface form, the binders with their types — and the text
// reads back, at the statement door of the family the member lands in,
// as the statement. The name-faithful payload print spells the
// comprehension's encoding and the binder name the encoding hides.
func TestEmitSection_SetBuilderHeadlineIsTheSurfaceForm(t *testing.T) {
	landed, ok := registry.ByName("symmetric_group.SymmetricGroupInsert")
	require.True(t, ok)

	e := newEngine(statedSessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "algebra/group/symmetric_group", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀a:A. ∀s:set(A). symmetric_group(insert(a, s)) = "+
		"{permutation_compose(transposition(a, b), p) | b:A, p:permutation(A) | b ∈ insert(a, s) ∧ p ∈ symmetric_group(s)}")
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "lemma", LemmaKey: "symmetric_group.SymmetricGroupInsert"})
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ZzSymmetricGroupInsert"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	headline := headlineOf(t, out.Go)
	assert.Regexp(t, regexp.MustCompile(`= \{[^|{}]+ \| b:A, p:permutation\(A\) \| b ∈ insert\(a, s\) ∧ p ∈ symmetric_group\(s\)\}$`), headline)
	for _, machine := range []string{"GEN%PVAR", "set_comprehension(", "comprehension_spec("} {
		assert.NotContains(t, out.Go, machine, "--- source: ---\n%s", out.Go)
	}
	key, err := landed.KeyOfText(headline)
	require.NoError(t, err, "the headline reads at the member's statement door")
	assert.Equal(t, landed.Key, key, "and reads as the statement")
}

// TestEmitSection_SetBuilderClaimIsTheSurfaceForm: an asserted claim is
// stated as the headline is — a set-builder as a set-builder. The
// comprehension stands after a Skolem, whose printed name is longer
// than the name the author typed: the parser names the binder a
// comprehension's encoding hides after the comprehension's place in
// the text, so here the name the record holds is not the name a
// re-print reads back, and only a text checked by the statement's key
// takes the sugar.
func TestEmitSection_SetBuilderClaimIsTheSurfaceForm(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "sets/set_order", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	// onGoalWith applies a tactic to the open goal with that many
	// hypotheses: an assert's claim branch carries one fewer than its
	// continuation.
	onGoalWith := func(hyps int, tactic TacticReq) {
		t.Helper()
		state, err := e.InspectState(ctx, info.ID)
		require.NoError(t, err)
		for _, g := range state.Goals {
			if g.Statement.NumHyps() != hyps {
				continue
			}
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: tactic})
			require.NoError(t, err)
			require.True(t, res.Success, "%s failed; diagnostics: %v", tactic.Type, res.Diagnostics)
			return
		}
		t.Fatalf("no open goal with %d hypotheses before %s", hyps, tactic.Type)
	}
	addTextGoal(t, s, "∀s t:(num → bool). s ⊆ t ⇒ {x:num | x ∈ s} ⊆ {x:num | x ∈ t}")
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
	onGoalWith(0, TacticReq{Type: "assert", ClaimText: "s = {x:num | x ∈ s}"})
	onGoalWith(0, TacticReq{Type: "set_tac"})
	onGoalWith(1, TacticReq{Type: "assert", ClaimText: "t = {x:num | x ∈ t}"})
	onGoalWith(1, TacticReq{Type: "set_tac"})
	onGoalWith(2, TacticReq{Type: "set_tac"})
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ZzComprehensionOfMembers"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	// The claims are the Haves' statement strings, read at the block's
	// claim door under the binders' own names.
	assert.Contains(t, out.Go, "\t\t\t\t\"s = {x:num | x ∈ s}\",\n", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "\t\t\t\t\"t = {x:num | x ∈ t}\",\n", "--- source: ---\n%s", out.Go)
	assert.Equal(t, 2, strings.Count(out.Go, ".Have("), "--- source: ---\n%s", out.Go)
	for _, machine := range []string{"GEN%PVAR", "set_comprehension(", "MakeProp("} {
		assert.NotContains(t, out.Go, machine, "--- source: ---\n%s", out.Go)
	}

	// Each text reads, at the family's own Script with the Skolems
	// declared as the member declares them, as the claim the session
	// recorded.
	fam, ok := registry.FamilyByName("sets/set_order")
	require.True(t, ok)
	script := fam.ParseScript(e.env)
	set := core.MakeFun(dsl.NumType, core.TypeBool())
	script.Var("s_0", set)
	script.Var("t_0", set)
	detailed := s.sections[0].root.DetailedProofProto()
	reader := ext.NewPoolReader(detailed.Pool, e.env.ProofService.LoadConstMeta)
	var recorded []core.PropKey
	for _, step := range detailed.Steps {
		if asserted, isAssert := step.Step.(*proof.StepProto_Assert); isAssert {
			claim, _ := reader.Prop(asserted.Assert)
			recorded = append(recorded, claim.AlphaKey())
		}
	}
	assert.ElementsMatch(t, recorded, []core.PropKey{
		script.MakePropText("s₀ = {x:num | x ∈ s₀}").AlphaKey(),
		script.MakePropText("t₀ = {x:num | x ∈ t₀}").AlphaKey(),
	})
}

// TestEmitSection_IntegerLiteralHeadlineIsTheChapterSpelling: the
// served statement over ℤ omits an integer embedding where the other
// operand supplies its type. The emitted headline keeps the landed
// member's authored spelling. Both read back at the statement door.
func TestEmitSection_IntegerLiteralHeadlineIsTheChapterSpelling(t *testing.T) {
	landed, ok := registry.ByName("lattice.DotPosLe")
	require.True(t, ok)

	e := newEngine(statedSessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "vector/lattice", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	s.AddGoal(landed.Statement().Prop)
	served, ok := FormatStatementTypedUnder(landed.Statement().Prop, s.family)
	require.True(t, ok)
	assert.Contains(t, served, ". 0 ≤ ")
	assert.NotContains(t, served, "int_of_num(")

	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "lemma", LemmaKey: "lattice.DotPosLe"})
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ZzDotPosLe"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	headline := headlineOf(t, out.Go)
	assert.Contains(t, headline, "&0 ≤ ")
	assert.NotContains(t, out.Go, "int_of_num(", "--- source: ---\n%s", out.Go)
	key, err := landed.KeyOfText(headline)
	require.NoError(t, err, "the headline reads at the member's statement door")
	assert.Equal(t, landed.Key, key, "and reads as the statement")
}

// TestBasicTactic_ClosesTheResidueARewriteLeaves: a `rw` whose result is
// reflexive leaves `⊢ ⊤` open, which `refl` refuses — the conclusion
// is no longer an equation; `basic` closes it, as the chapter verb
// `Basic()` does, and the emitted ladder ends on that verb.
func TestBasicTactic_ClosesTheResidueARewriteLeaves(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "nat_num/nat_order", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀f:(num → num). ∀x:num. ∀y:num. x = y ⇒ f(x) = f(y)")
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "strip_imp"})
	hyp := 0
	rewritten := applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "rw", HypIndex: &hyp})
	require.Equal(t, "simplify", rewritten.Effect, "the reflexive result is left open as ⊤")

	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	require.Equal(t, "⊤", ext.PrintTerm(state.Goals[0].Statement.Conclusion()), "residue: %s", prop.PrintProp(state.Goals[0].Statement))
	refused, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: TacticReq{Type: "refl"}})
	require.NoError(t, err)
	require.False(t, refused.Success, "refl closes an equation, and ⊤ is none")

	closed := applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "basic"})
	require.Equal(t, "close", closed.Effect)
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ZzRewriteThenBasic"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, "Basic()", "--- source: ---\n%s", out.Go)
}

// A record field's projection equation is cited by the name its field
// registers: the family's generated file declares that variable, a typed
// wrapper like any entry's. A datatype's derived principle has no such
// variable and is reached through its handle, a bare entry.
func TestEmitSection_RecordFieldReferences(t *testing.T) {
	entry, ok := registry.ByName("module_record.RingCarrierDef")
	require.True(t, ok)
	for _, tc := range []struct{ family, expr string }{
		{"algebra/module/module_record", "RingCarrierDef"},
		{"simplicial/simplicial_chain", "module_record.RingCarrierDef"},
	} {
		e := newEngine(statedSessionEnv())
		ref, ok := e.familyDepEntryForEmit(tc.family, map[string]*registry.ProofEntry{})(entry.Name, "")
		require.True(t, ok)
		assert.Equal(t, tc.expr, ref.Expr)
		assert.False(t, ref.BareEntry, "a record field's projection equation has a generated variable")
		ref, ok = e.familyDepEntryForEmit(tc.family, map[string]*registry.ProofEntry{})("unknown_by_name", core.PropKey(entry.Key))
		require.True(t, ok)
		assert.Equal(t, tc.expr, ref.Expr)
		assert.False(t, ref.BareEntry, "a record field's projection equation has a generated variable")
		info, err := e.CreateSession(context.Background())
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		s.AddGoal(entry.Statement().Prop)
		applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "lemma", LemmaKey: entry.Name})
		out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ReadsRecordField", Family: tc.family})
		require.NoError(t, err)
		parsesAsGo(t, out.Go)
		assert.Contains(t, out.Go, "Cite("+tc.expr+")")
		assert.NotContains(t, out.Go, "Deps:", "a proved member renders no Deps — its recording observes what it reads\n--- source: ---\n%s", out.Go)
	}
	induction, ok := registry.ByName("module_record.RingOpsInduction")
	require.True(t, ok)
	ref, ok := newEngine(statedSessionEnv()).familyDepEntryForEmit("simplicial/simplicial_chain", map[string]*registry.ProofEntry{})(induction.Name, "")
	require.True(t, ok)
	assert.Equal(t, "module_record.RingOpsData.Induct", ref.Expr)
	assert.True(t, ref.BareEntry, "a datatype's principle is reached through its handle")
}

// unspaced is s with its blanks and line breaks removed: a test that
// asks whether the emitted source holds a piece of code reads both
// sides so, since the formatter lays a call past the width out over
// lines.
func unspaced(s string) string { return strings.Join(strings.Fields(s), "") }
