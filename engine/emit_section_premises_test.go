package engine

// How emit-section renders a `by`'s premises, a `simp_with`'s rules and
// the names a member cites them by, each rendering replayed as emitted
// (emit_section_replay_test.go).

import (
	"context"
	"os"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// openGoalWhere is the one open goal of s that keep accepts.
func openGoalWhere(t *testing.T, e *Engine, s *Session, keep func(core.Prop) bool) *GoalView {
	t.Helper()
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	var kept []*GoalView
	for i := range state.Goals {
		if keep(state.Goals[i].Statement) {
			kept = append(kept, &state.Goals[i])
		}
	}
	require.Len(t, kept, 1, "one open goal is selected")
	return kept[0]
}

// applyTo applies tactic to the one open goal keep accepts.
func applyTo(t *testing.T, e *Engine, s *Session, keep func(core.Prop) bool, tactic TacticReq) {
	t.Helper()
	g := openGoalWhere(t, e, s, keep)
	t.Logf("before %s: %s", tactic.Type, prop.PrintProp(g.Statement))
	res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: tactic})
	require.NoError(t, err)
	require.True(t, res.Success, "%s failed; diagnostics: %v", tactic.Type, res.Diagnostics)
}

// concluding keeps the goal whose conclusion prints as printed.
func concluding(printed string) func(core.Prop) bool {
	return func(g core.Prop) bool { return ext.PrintTerm(g.Conclusion()) == printed }
}

// holding keeps the goal with a hypothesis printing as printed.
func holding(printed string) func(core.Prop) bool {
	return func(g core.Prop) bool {
		return g.AnyHyp(func(h core.Term) bool { return ext.PrintTerm(h) == printed })
	}
}

// lacking keeps the goal with no hypothesis printing as printed.
func lacking(printed string) func(core.Prop) bool {
	return func(g core.Prop) bool { return !holding(printed)(g) }
}

// sole keeps every goal: the one open goal.
func sole(core.Prop) bool { return true }

// hypAt is the index, in the one open goal keep accepts, of the one
// hypothesis whose print opens with prefix.
func hypAt(t *testing.T, e *Engine, s *Session, keep func(core.Prop) bool, prefix string) *int {
	t.Helper()
	goal := openGoalWhere(t, e, s, keep).Statement
	var found []int
	for i := range goal.NumHyps() {
		if strings.HasPrefix(ext.PrintTerm(goal.Hyp(i)), prefix) {
			found = append(found, i)
		}
	}
	require.Len(t, found, 1, "one hypothesis opens with %s in %s", prefix, prop.PrintProp(goal))
	return &found[0]
}

// TestEmitSection_ReplayHarnessRunsAMember: the replay harness compiles
// and runs a member whose rendering is settled — the probe shape of
// TestEmitSection_ProbeMemberWriteOut, emitted into a scratch family.
func TestEmitSection_ReplayHarnessRunsAMember(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	addTextGoal(t, s, "∀s t:set(num). s = t ⇒ t ⊆ s")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "intro"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: "set_order.SubsetAntisymEq"}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "expand"})
	const pkg = "zzharness"
	src := emitInto(t, e, s, pkg, "ZzHarnessProbe")
	assert.Contains(t, src, "set_order.SubsetAntisymEq", "--- source: ---\n%s", src)
	replayEmitted(t, pkg, "ZzHarnessProbe", src)
}

// TestEmitSection_ALooseLawReadAtAHaveIsItsRead: a law carrying a type
// letter its instance does not fix (module.ModuleSumIn's index letter),
// read under a Have's structure fact and grounded, is cited by the
// session as the law beside the fact with the components prefixed; the
// member spells what the author asked for, `At(Law.Read(fact), w…)`,
// whose Go macro makes the same expansion.
func TestEmitSection_ALooseLawReadAtAHaveIsItsRead(t *testing.T) {
	e, s := boundSession(t, "algebra/module/module_homomorphism")
	addStatement(t, s, "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). module_homomorphism(R, M, N, f) ⇒ "+
		"∀s:set(num). ∀F:(num → B). finite(s) ⇒ (∀x:num. x ∈ s ⇒ F(x) ∈ M.carrier) ⇒ module_sum(M.add, M.zero, s, F) ∈ M.carrier")
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	module := "module_on(R₀, M₀)"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: module})
	applyTo(t, e, s, concluding(module), TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
		{Key: "module_homomorphism.HomSource", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, concluding(module), "module_homomorphism(")}}}})
	both := "finite(s₀) ∧ (∀x:num. x ∈ s₀ ⇒ F₀(x) ∈ M₀.carrier)"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: both})
	claim := func(g core.Prop) bool { return strings.HasPrefix(ext.PrintTerm(g.Conclusion()), "finite(s₀) ∧") }
	applyTo(t, e, s, claim, TacticReq{Type: "by",
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, claim, "finite(")}, {HypIndex: hypAt(t, e, s, claim, "∀")}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by",
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, sole, "finite(s₀) ∧")}},
		WithLemmas: []LemmaWithSpec{{Key: "module.ModuleSumIn", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "module_on(")},
			TermSpecialize: map[string]string{"s": "s₀", "F": "F₀"}}}})
	const pkg = "zzlooseread"
	src := emitInto(t, e, s, pkg, "ZzLooseRead")
	assert.Contains(t, src, "fact1 := ", "--- source: ---\n%s", src)
	assert.Contains(t, src, "At(module.ModuleSumIn.Read(fact1), s, F)", "--- source: ---\n%s", src)
	assert.NotContains(t, unspaced(src), "At(module.ModuleSumIn,", "the law is read at the fact, not cited beside it\n--- source: ---\n%s", src)
	replayEmitted(t, pkg, "ZzLooseRead", src)
}

// TestEmitSection_ANestedGivenKeepsTheLawHandleApart: a branch that
// rewrites with the one equation its assert introduced takes that
// equation as a Given closure's Fact, and a law read inside it at the
// structure hypothesis the Law door binds reads at the door's handle:
// the closure's name is allocated apart from it.
func TestEmitSection_ANestedGivenKeepsTheLawHandleApart(t *testing.T) {
	e, s := boundSession(t, "simplicial/simplicial_set")
	addStatement(t, s, "∀X:simplicial_ops(A). simplicial_set(X) ⇒ "+
		"∀x₀:A. ∀n:num. x₀ ∈ X.simplices(0) ⇒ X.d(n + 1, 0, base_simplex(x₀, n + 1)) = base_simplex(x₀, n)")
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	simplicial := "simplicial_set("
	vertex := "x₀ ∈ simplicial_simplices(X₀, 0)"
	below := "base_simplex(simplicial_degeneracy(X₀), x₀, n₀) ∈ simplicial_simplices(X₀, n₀)"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: below})
	applyTo(t, e, s, concluding(below), TacticReq{Type: "by",
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, concluding(below), vertex)}},
		WithLemmas: []LemmaWithSpec{{Key: "simplicial_set.BaseSimplexIn", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, concluding(below), simplicial)},
			TermSpecialize: map[string]string{"n": "n₀", "x_0": "x₀"}}}})
	inRange := "0 ≤ n₀"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: inRange})
	applyTo(t, e, s, concluding(inRange), TacticReq{Type: "by", Arith: true})
	// A case split whose one branch asserts the degeneracy equation
	// alone, so the equation is the one hypothesis its continuation takes
	// as a Given closure's Fact; the other branch holds a contradiction.
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "case_split", Const: vertex + " ∨ ¬(" + vertex + ")"})
	contradiction := func(g core.Prop) bool {
		return g.AnyHyp(func(h core.Term) bool { return strings.HasPrefix(ext.PrintTerm(h), "¬(") })
	}
	consistent := func(g core.Prop) bool { return !contradiction(g) }
	degenerate := "base_simplex(simplicial_degeneracy(X₀), x₀, n₀ + 1) = simplicial_degeneracy(X₀, n₀, 0, base_simplex(simplicial_degeneracy(X₀), x₀, n₀))"
	applyTo(t, e, s, consistent, TacticReq{Type: "assert", ClaimText: degenerate})
	applyTo(t, e, s, concluding(degenerate), TacticReq{Type: "by",
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, concluding(degenerate), vertex)}, {HypIndex: hypAt(t, e, s, concluding(degenerate), inRange)}},
		WithLemmas: []LemmaWithSpec{{Key: "simplicial_set.BaseSimplexDegeneracy", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, concluding(degenerate), simplicial)},
			TermSpecialize: map[string]string{"i": "0", "n": "n₀", "x_0": "x₀"}}}})
	applyTo(t, e, s, holding(degenerate), TacticReq{Type: "rw", HypIndex: hypAt(t, e, s, holding(degenerate), "base_simplex(simplicial_degeneracy(X₀), x₀, n₀ + 1) =")})
	applyTo(t, e, s, consistent, TacticReq{Type: "by",
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, consistent, below)}, {HypIndex: hypAt(t, e, s, consistent, inRange)}},
		WithLemmas: []LemmaWithSpec{{Key: "simplicial_set.FaceDegeneracyEqual", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, consistent, simplicial)},
			TermSpecialize: map[string]string{"i": "0", "n": "n₀", "x": "base_simplex(simplicial_degeneracy(X₀), x₀, n₀)"}}}})
	applyTo(t, e, s, contradiction, TacticReq{Type: "by",
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, contradiction, "¬(")}}})
	const pkg = "zznestedgiven"
	src := emitInto(t, e, s, pkg, "ZzNestedGiven")
	assert.Contains(t, src, "func(a *Argument, X Fact, x0 *Expr[A], n *Expr[Nat], h Fact)", "the structure over its record is the bundle binder X\n--- source: ---\n%s", src)
	assert.Contains(t, src, "Given(func(b *Argument, h_2 Fact)", "the closure's name is allocated apart from the door's\n--- source: ---\n%s", src)
	assert.Contains(t, src, "h_2.Rw()", "--- source: ---\n%s", src)
	assert.Contains(t, src, "simplicial_set.FaceDegeneracyEqual.Read(X)", "the law reads at the bundle binder\n--- source: ---\n%s", src)
	replayEmitted(t, pkg, "ZzNestedGiven", src)
}

// antisymAtTwoInstances opens a session on `s = t ∧ u = v ⇒ s ⊆ t ∧ u ⊆
// v` over sets of num and sets of bool, rewrites it by `simp_with` over
// the polymorphic set_order.SubsetAntisymEq — pinned at num when pin is
// set, adapted to the goal otherwise — and closes what is left by the
// set driver.
func antisymAtTwoInstances(t *testing.T, pin bool) (*Engine, *Session) {
	t.Helper()
	e, s := boundSession(t, "sets/set_order")
	addTextGoal(t, s, "∀s t:set(num). ∀u v:set(bool). s = t ∧ u = v ⇒ s ⊆ t ∧ u ⊆ v")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "intro"})
	rule := LemmaWithSpec{Key: "set_order.SubsetAntisymEq"}
	if pin {
		rule.TypeSpecialize = map[string]string{"A": "num"}
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{rule}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: hyp0()})
	return e, s
}

// TestEmitSection_ASimpRuleGoAdaptsIsTheBareEntry: a polymorphic rule the
// session adapted to the goal's two instances, both of which Go's Simp
// adapts from the bare entry, is cited once and bare — not one
// `ctx.AtTypes` cite per instance — and the member replays.
func TestEmitSection_ASimpRuleGoAdaptsIsTheBareEntry(t *testing.T) {
	e, s := antisymAtTwoInstances(t, false)
	const pkg = "zzsimpbare"
	src := emitInto(t, e, s, pkg, "ZzSimpBare")
	assert.Contains(t, src, "Simp(Fwd(set_order.SubsetAntisymEq))", "--- source: ---\n%s", src)
	assert.Equal(t, 1, strings.Count(src, "SubsetAntisymEq"), "the entry is cited once\n--- source: ---\n%s", src)
	assert.NotContains(t, src, "AtTypes(", "--- source: ---\n%s", src)
	assert.NotContains(t, src, "Inst[", "--- source: ---\n%s", src)
	replayEmitted(t, pkg, "ZzSimpBare", src)
}

// TestEmitSection_ASimpRulePinnedOnAWiderGoalKeepsItsInstance: the same
// rule pinned at num on the goal that spells bool too fires at num
// alone, where Go's Simp from the bare entry would rewrite both — so the
// instance stays spelled, the sole-letter wrapper's `Inst[Nat]()`, and
// the member replays the session's rewrite.
func TestEmitSection_ASimpRulePinnedOnAWiderGoalKeepsItsInstance(t *testing.T) {
	e, s := antisymAtTwoInstances(t, true)
	const pkg = "zzsimppinned"
	src := emitInto(t, e, s, pkg, "ZzSimpPinned")
	assert.Contains(t, src, "Simp(Fwd(set_order.SubsetAntisymEq.Inst[Nat]()))", "--- source: ---\n%s", src)
	replayEmitted(t, pkg, "ZzSimpPinned", src)
}

// TestEmitSection_ABranchLocalSimpKeepsTheOuterHandle: a `simp_with` at
// a Have's hypothesis inside a later Have's claim branch, the main line
// citing the same fact after that Have, renders the branch over a fact
// of its own — `c.Hyp(<the hypothesis>)`, rewritten in its place and
// cited there — since Fact.Simp moves the handle it rewrites into the
// branch; the main line goes on citing the Have's fact, and the member
// replays as emitted.
func TestEmitSection_ABranchLocalSimpKeepsTheOuterHandle(t *testing.T) {
	e, s := boundSession(t, "algebra/module/function_module")
	addTextGoal(t, s, "∀zero:A. ∀c:set(A). ∀S:set(D). ∀f:(D → A). f ∈ finite_supp(zero, c, S) ∧ zero ∈ c ⇒ "+
		"finite(fun_support(zero, f)) ∧ f ∈ finite_supp(zero, c, S)")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	member := "f₀ ∈ finite_supp(zero₀, c₀, S₀)"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: member})
	applyTo(t, e, s, concluding(member), TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, concluding(member), "("+member+") ∧")}}})
	support := "finite(fun_support(zero₀, f₀))"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: support})
	claim := concluding("finite(fun_support(zero₀, f₀))")
	applyTo(t, e, s, claim, TacticReq{Type: "simp_with", HypIndex: hypAt(t, e, s, claim, member),
		WithLemmas: []LemmaWithSpec{{Key: "function_module.FiniteSuppDef"}, {Key: "function_module.FiniteSupportDef"}}})
	// The definitions open the member into the set-builder; the set
	// driver reads the comprehension.
	rewritten := func(g core.Prop) bool {
		return claim(g) && g.AnyHyp(func(h core.Term) bool { return strings.Contains(ext.PrintTerm(h), "finite(fun_support(") })
	}
	applyTo(t, e, s, rewritten, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, rewritten, "f₀ ∈ {f")}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{
		{HypIndex: hypAt(t, e, s, sole, member)}, {HypIndex: hypAt(t, e, s, sole, "finite(fun_support(")}}})
	const pkg = "zzbranchsimp"
	src := emitInto(t, e, s, pkg, "ZzBranchSimp")
	assert.Regexp(t, `fact3 := [a-z]\.Hyp\(ctx\.MakePropText\("f₀ ∈ finite_supp\(zero₀, c₀, S₀\)"`, src, "the branch binds a fact of its own\n--- source: ---\n%s", src)
	assert.Contains(t, src, "fact3.Simp(Fwd(function_module.", "--- source: ---\n%s", src)
	assert.NotContains(t, src, "fact1.Simp(", "the Have's fact is not rewritten in the branch\n--- source: ---\n%s", src)
	assert.Contains(t, src, "Fwd(function_module.FiniteSuppDef)", "the definition adapted at the goal's instance is cited bare\n--- source: ---\n%s", src)
	assert.NotContains(t, src, "AtTypes(", "--- source: ---\n%s", src)
	assert.Contains(t, src, "BySets(fact3)", "the branch's fact names the rewritten hypothesis\n--- source: ---\n%s", src)
	assert.Contains(t, src, "By(fact1, fact2)", "the main line cites the Have's fact after the branch\n--- source: ---\n%s", src)
	replayEmitted(t, pkg, "ZzBranchSimp", src)
}

// TestEmitSection_ATypeDefinitionTheoremIsItsDoorsField: a type
// definition's theorem is exported through its door's handle and field
// alone (`NaddDef.Membership`), so a cite of it spells that field —
// qualified by the package from another family, bare in its own.
func TestEmitSection_ATypeDefinitionTheoremIsItsDoorsField(t *testing.T) {
	e := newEngine(statedSessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "real/tower/real_completeness", []string{"real/tower/eudoxus_slope"})
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀r:(num → num). is_nadd(r) ⇒ dest_nadd(mk_nadd(r)) = r ∧ is_nadd(r)")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: hyp0(), ByShape: &ByShapeReq{Normalized: true},
		WithLemmas: []LemmaWithSpec{{Key: "eudoxus_slope.NaddMembership", TermSpecialize: map[string]string{"r": "r₀"}}}})
	const pkg = "zztypedefcite"
	src := emitInto(t, e, s, pkg, "ZzTypedefCite")
	assert.Contains(t, src, "At(eudoxus_slope.NaddDef.Membership, r)", "--- source: ---\n%s", src)
	assert.NotContains(t, src, "NaddMembership", "--- source: ---\n%s", src)
	// The slope chapter is internal to the tower: the member compiles
	// inside it.
	replayEmittedUnder(t, "../library/proofs/real/tower", pkg, "ZzTypedefCite", src)

	own, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: "Build_ZzTypedefCite", Family: "real/tower/eudoxus_slope", IncludePrior: []int{}})
	require.NoError(t, err)
	parsesAsGo(t, own.Go)
	assert.Contains(t, own.Go, "At(NaddDef.Membership, r)", "in its own family the field is bare\n--- source: ---\n%s", own.Go)
}

// TestEmitSection_StoredSighting is a tool: it resumes a stored session
// — the session store and the CNF store a serve wrote, or copies of
// them, named by XUGO_SIGHTING_SESSION_STORE and XUGO_SIGHTING_CNF_STORE,
// the session by XUGO_SIGHTING_SESSION — and emits its section 0 into
// XUGO_SIGHTING_FAMILY as Build_Sighting, logging the Go: a rendering
// read against the session that reported it. The resume writes the
// session's lineage back into the store it was read from, so point the
// variables at a copy. Without them the test is skipped.
func TestEmitSection_StoredSighting(t *testing.T) {
	store, id := os.Getenv("XUGO_SIGHTING_SESSION_STORE"), os.Getenv("XUGO_SIGHTING_SESSION")
	if store == "" || id == "" {
		t.Skip("XUGO_SIGHTING_SESSION_STORE and XUGO_SIGHTING_SESSION name no stored session")
	}
	env := statedSessionEnv()
	if dir := os.Getenv("XUGO_SIGHTING_CNF_STORE"); dir != "" {
		cnf, err := OpenSessionCNFStore(dir)
		require.NoError(t, err)
		env.ProofService.CNFStore = cnf
	}
	e := newEngine(env, WithSessionStore(store))
	resumed, err := e.ResumeSession(context.Background(), id)
	require.NoError(t, err)
	require.Nil(t, resumed.Diverged, "the lineage replays to its end: %+v", resumed.Diverged)
	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: id, Section: 0, FuncName: "Build_Sighting", Family: os.Getenv("XUGO_SIGHTING_FAMILY"), IncludePrior: []int{},
	})
	if out != nil {
		t.Logf("emitted (%d bytes of CNF blob):\n%s", len(out.CNFCache), out.Go)
	}
	require.NoError(t, err)
}
