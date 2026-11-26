package engine

import (
	"context"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/utils/wallclock"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// hypKeySet snapshots a goal's hyp α-keys (test-side helper; the
// production per-rung chain that used it was replaced by the composite
// specialize step).
func hypKeySet(goal core.Prop) map[core.TermKey]bool {
	s := make(map[core.TermKey]bool, goal.NumHyps())
	for i := range goal.NumHyps() {
		s[goal.Hyp(i).AlphaKey()] = true
	}
	return s
}

// parseEMatchGoal parses a goal with the registry's const resolver (pattern_abstraction,
// set_comprehension, comprehension_spec, set_member, … are polymorphic chapter constants).
func parseEMatchGoal(t *testing.T, text string) core.Prop {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{ConstResolver: registryConstResolver})
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	return res.Prop
}

// ematchSessionWithGoal builds a session over the corpus's constants
// with the goal added.
func ematchSessionWithGoal(t *testing.T, goalText string) (*Engine, *Session, string) {
	t.Helper()
	// testEnv's mock const-meta service doesn't know the chapters'
	// constants (set_member/set_comprehension/comprehension_spec/...),
	// which def_expand's lookupDefConst needs; route LoadConstMeta
	// through the registry, falling back to the mock for test-local
	// consts.
	env := testEnv()
	mockLoad := env.ProofService.LoadConstMeta
	env.ProofService.LoadConstMeta = func(n core.TermName) (core.ConstTermMeta, bool) {
		if meta := registryConstResolver(string(n)); !meta.IsZero() {
			return meta, true
		}
		return mockLoad(n)
	}
	e := newEngine(env)
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goal := parseEMatchGoal(t, goalText)
	s.AddGoal(goal)
	s.rebuildGoalIndex()
	return e, s, info.ID
}

// ematchOpenLeafID returns the goal id of the first unsolved leaf.
func ematchOpenLeafID(t *testing.T, s *Session) string {
	t.Helper()
	s.rebuildGoalIndex()
	for id, entry := range s.goalIndex {
		if !entry.node.Proved() {
			leaves := entry.node.UnsolvedLeaves()
			if len(leaves) > 0 && entry.node == leaves[0] {
				return id
			}
		}
	}
	for id, entry := range s.goalIndex {
		if !entry.node.Proved() {
			return id
		}
	}
	t.Fatal("no open leaf")
	return ""
}

// c2BridgeGoalText is the comprehension equality an iterated-product
// proof bridges through, in pointwise set_member-form — the
// acceptance shape of the e-matching probes.
const c2BridgeGoalText = "t:(var:A → (var:B → bool)), s:(var:A → bool), a:var:A, p:prod(var:A, var:B) ⊢ set_member(p, set_comprehension(λg:prod(var:A, var:B).(∃x:var:A.∃y:var:B.comprehension_spec(g, set_member(x, insert(a, s)) ∧ set_member(y, t(x)), (x, y))))) ⇔ set_member(p, union(image(λy:var:B.(a, y), t(a)), set_comprehension(λg:prod(var:A, var:B).(∃x:var:A.∃y:var:B.comprehension_spec(g, set_member(x, s) ∧ set_member(y, t(x)), (x, y))))))"

// c2KitRow is one row of the membership kit: the member stating it,
// or, for the row no member states, the statement it loads inline
// from.
type c2KitRow struct {
	member string
	inline string
}

// c2LemmaKit is the six-lemma membership kit the manual grounding
// ladder used. The third row, membership in a comprehension of pairs,
// is the one no member states.
var c2LemmaKit = []c2KitRow{
	{member: "pairs.PairEq"},
	{member: "pairs.PairSurjective"},
	{inline: "∀P:(var:A → (var:B → bool)). ∀a:var:A. ∀b:var:B. " +
		"set_member((a, b), set_comprehension(λg:prod(var:A, var:B).(∃x:var:A.∃y:var:B." +
		"comprehension_spec(g, P(x, y), (x, y))))) ⇔ P(a, b)"},
	{member: "set_basic.InUnion"},
	{member: "set_basic.InImage"},
	{member: "set_basic.InInsert"},
}

// TestEMatch_GroundsMembershipKit: on the C2 bridge with the membership
// kit resident, `ematch` grounds the kit at the goal's comprehension
// sites (the grounding ladder, mechanized), and the `auto` close becomes
// reachable.
func TestEMatch_GroundsMembershipKit(t *testing.T) {
	wallclock.SkipOnSlowMachine(t)
	e, s, sid := ematchSessionWithGoal(t, c2BridgeGoalText)
	root := s.sections[0].root

	// InUnion and InImage are needed at the prod(A,B) instance (the
	// goal's top-level membership atoms live there); the goal-derived
	// adapter pins them elsewhere, so direct the loads explicitly —
	// instance selection at LOAD time (type_specialize), grounding by
	// ematch (the two-σ-source division).
	kitSpecialize := map[string]map[string]string{
		"set_basic.InUnion": {"A": "prod(var:A, var:B)"},
	}
	for _, row := range c2LemmaKit {
		name := row.member
		var key string
		req := TacticReq{Type: "lemma", TypeSpecialize: kitSpecialize[row.member]}
		inline := row.member == ""
		if !inline {
			entry, found := registry.ByName(row.member)
			require.True(t, found, "no member %s", row.member)
			key = entry.Key
			req.LemmaKey = key
		} else {
			// The kit row no member states is not citable: it loads
			// inline, and its reproduction child — the author's to
			// prove — is closed white-box below.
			name = "the pair-comprehension row"
			req = TacticReq{Type: "lemma", Lemma: parseEMatchGoal(t, row.inline)}
		}
		if row.member == "set_basic.InImage" {
			// InImage needs BOTH type vars pinned; the two-key
			// type_specialize map hits the σ name-collision class, so
			// pin via term_specialize instead — the ground witnesses'
			// types pin the polymorphic binders, and the keyed load
			// keeps the reproduction child auto-matchable.
			req = TacticReq{Type: "lemma", LemmaKey: key,
				TermSpecialize: map[string]string{"f": "λy:var:B.(a, y)", "s": "t(a)"}}
		}
		out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: ematchOpenLeafID(t, s),
			Tactic: req,
		})
		require.NoError(t, err, "lemma(%s)", name)
		require.True(t, out.Success, "lemma(%s): %+v", name, out)
		if inline {
			closeReproductionChildrenTrusted(t, s, root)
		}
		for gi, g := range out.State.Goals {
			t.Logf("after lemma(%s): goal[%d] hyps=%d concl=%.100s", name, gi, g.Statement.NumHyps(), ext.PrintTerm(g.Statement.Conclusion()))
		}
	}

	// The six freshly loaded kit hyps (by α-key) — cleared after
	// grounding, keeping their ground offspring.
	kitKeys := hypKeySet(firstUnsolvedLeaf(root).Goal)

	hypsBefore := firstUnsolvedLeaf(root).Goal.NumHyps()
	t.Logf("hyps before ematch: %d", hypsBefore)
	for i := range firstUnsolvedLeaf(root).Goal.NumHyps() {
		t.Logf("  pre-hyp[%d]: %.120s", i, ext.PrintTerm(firstUnsolvedLeaf(root).Goal.Hyp(i)))
	}
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: ematchOpenLeafID(t, s),
		Tactic: TacticReq{Type: "ematch"},
	})
	require.NoError(t, err, "ematch must apply on the kit-resident goal")
	require.True(t, out.Success)

	leaf := firstUnsolvedLeaf(root)
	require.NotNil(t, leaf)
	hypsAfter := leaf.Goal.NumHyps()
	t.Logf("ematch: hyps %d → %d", hypsBefore, hypsAfter)
	assert.Greater(t, hypsAfter, hypsBefore, "ematch must add ground instances")
	for i := range leaf.Goal.NumHyps() {
		t.Logf("  hyp[%d]: %.140s", i, ext.PrintTerm(leaf.Goal.Hyp(i)))
	}

	// The acceptance close: clear the ORIGINAL kit hyps that act as
	// junk amplifiers (flexible-literal ELIM, bare-var-equality PS,
	// and the instance-pinned membership iffs whose ground instances
	// ematch just extracted), KEEPING PairEq and InInsert resident —
	// the refuter needs their single-rung content at Skolem points the
	// grounding pass cannot name.
	leaf = firstUnsolvedLeaf(root)
	var wide []int
	for i := range leaf.Goal.NumHyps() {
		h := leaf.Goal.Hyp(i)
		if !kitKeys[h.AlphaKey()] {
			continue
		}
		if keepEMatchResident(h) {
			continue
		}
		wide = append(wide, i)
	}
	if len(wide) > 0 {
		out, err = e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: ematchOpenLeafID(t, s),
			Tactic: TacticReq{Type: "clear", HypIndices: wide},
		})
		require.NoError(t, err)
		t.Logf("clear wide ∀-hyps %v: success=%v", wide, out.Success)
	}
	// Golden-instance assertions — the exact ground facts the manual
	// grounding ladder produced by hand:
	//   - PairSurjective at p,
	//   - the full InUnion instance at (p, image(λy.(a,y), t(a)), set_comprehension₂).
	// The ∃ block is spelled x-then-y: the row is proved by
	// pairs.PairSurjective, whose statement — the form a key cite
	// serves — writes `∃x:A. ∃y:B. p = (x, y)`, and ematch grounds the
	// served form. (A type-sorted print of the block reads it
	// y-then-x; the pair's component order is unrelated to the binder
	// order, both spellings being one theorem.) The hand ladder wrote
	// the image's map η-long, λy.(a, y); ematch grounds at the goal's
	// own terms, which Normalize keeps η-short ((,)(a)), so the golden
	// is read through the basic rewrite.
	psInstance := parseEMatchGoal(t,
		"p:prod(var:A, var:B) ⊢ ∃x:var:A.∃y:var:B.(p = (x, y))").Conclusion()
	require.GreaterOrEqual(t, hypIndexByAlphaKey(leaf.Goal, psInstance), 0,
		"ematch must ground pairs.PairSurjective at p")
	unionInstance := parseEMatchGoal(t,
		"t:(var:A → (var:B → bool)), s:(var:A → bool), a:var:A, p:prod(var:A, var:B) ⊢ set_member(p, union(image(λy:var:B.(a, y), t(a)), set_comprehension(λg:prod(var:A, var:B).(∃x:var:A.∃y:var:B.comprehension_spec(g, set_member(x, s) ∧ set_member(y, t(x)), (x, y)))))) ⇔ (set_member(p, image(λy:var:B.(a, y), t(a))) ∨ set_member(p, set_comprehension(λg:prod(var:A, var:B).(∃x:var:A.∃y:var:B.comprehension_spec(g, set_member(x, s) ∧ set_member(y, t(x)), (x, y))))))").Conclusion()
	unionInstance = prop.Rhs(prop.RewriteOrRefl(prop.BasicRewrite, unionInstance))
	require.GreaterOrEqual(t, hypIndexByAlphaKey(leaf.Goal, unionInstance), 0,
		"ematch must ground set_basic.InUnion at (p, image, set_comprehension₂)")

	// Split the iff so each direction is closed independently (the iter
	// #66 "split_iff FIRST" recipe). The pre-ematch baseline closes ZERO
	// of these (probes C2/C3/C5/C7,);
	// the def_expand cascade + final auto below do the closing.
	out, err = e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: ematchOpenLeafID(t, s),
		Tactic: TacticReq{Type: "split_iff"},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "split_iff must apply")

	// NOTE: an earlier "Phase-A" auto+case_split loop (2 rounds, 5s
	// budgets) ran here BEFORE the def_expand cascade. Removed as pure
	// waste: its autos fire before def_expand exposes the raw
	// set-membership structure, so they cannot close and each burned
	// ~18-20s failing (~75s total, and the 5s budget was not honored).
	// The cascade + final auto below close the bridge end-to-end without
	// it (verified: root still proves). The dominant remaining cost is
	// def_expand's no-net-reduction path (~15s per non-firing call on the
	// wide grounded goal), not the auto — see the timing post-mortem.

	// The def_expand(set_member/set_comprehension/comprehension_spec) cascade — the ladder's final
	// move — on whatever remains open. Safe post-fix
	// (ext/prop/eq_rewrite.go isProjectionPattern; see
	// engine.TestDefExpandSetComprehension_NoTreadmill): before that fix this loop
	// would oscillate forever on set_comprehension. If it ever regresses, this loop
	// hangs to the test timeout — that failure mode IS the regression
	// signal, deliberately not guarded against here.
	for {
		fired := false
		for _, lid := range allOpenLeafIDs(s) {
			entry, ok := s.goalIndex[lid]
			if !ok || entry.node.Proved() {
				continue
			}
			for _, cn := range []string{"set_member", "set_comprehension", "comprehension_spec"} {
				out, derr := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
					GoalID: lid, Tactic: TacticReq{Type: "def_expand", Const: cn},
				})
				if derr == nil && out.Success {
					t.Logf("  def_expand(%s) on %s: true", cn, lid)
					fired = true
					break
				}
			}
			if fired {
				break
			}
		}
		if !fired {
			break
		}
	}
	for _, lid := range allOpenLeafIDs(s) {
		entry, ok := s.goalIndex[lid]
		if !ok || entry.node.Proved() {
			continue
		}
		out, err = e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: lid, Tactic: TacticReq{Type: "auto"}, BudgetMs: 5000,
		})
		require.NoError(t, err)
		t.Logf("  auto after def_expand cascade on %s: %v", lid, out.Success)
	}

	t.Logf("FINAL: root proved=%v", root.Proved())
	assert.True(t, root.Proved(),
		"ACCEPTANCE: with ematch grounding + the def_expand(set_member/set_comprehension/comprehension_spec) cascade, "+
			"the full C2 bridge must close end-to-end (pre-ematch baseline: 0/4 branches; "+
			"pre-set_comprehension-fix: cascade never terminated)")
}

// TestEMatch_TypeFallback_PairSurjective: a hyp with no ground-matchable
// trigger (pairs.PairSurjective's matrix ∃x y. q = (x,y)) gets its leading
// binder instantiated at pool terms of the binder's type (L3).
func TestEMatch_TypeFallback_PairSurjective(t *testing.T) {
	e, s, sid := ematchSessionWithGoal(t,
		"Q:(prod(var:A, var:B) → bool), p:prod(var:A, var:B), ∀q:prod(var:A, var:B).(∃x:var:A.∃y:var:B.(q = (x, y))) ⊢ Q(p)")
	root := s.sections[0].root

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: ematchOpenLeafID(t, s),
		Tactic: TacticReq{Type: "ematch"},
	})
	require.NoError(t, err)
	require.True(t, out.Success)

	leaf := firstUnsolvedLeaf(root)
	require.NotNil(t, leaf)
	expected := parseEMatchGoal(t,
		"p:prod(var:A, var:B) ⊢ ∃x:var:A.∃y:var:B.(p = (x, y))").Conclusion()
	assert.GreaterOrEqual(t, hypIndexByAlphaKey(leaf.Goal, expected), 0,
		"L3 fallback must add the ground pairs.PairSurjective instance at p; hyps: %s",
		prop.PrintProp(leaf.Goal))
}

// TestEMatch_NoQuantifiedHyps: without any ∀-hyp the tactic reports a
// clean no-application error.
func TestEMatch_NoQuantifiedHyps(t *testing.T) {
	e, s, sid := ematchSessionWithGoal(t, "a:num, b:num, a = b ⊢ a = b")

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: ematchOpenLeafID(t, s),
		Tactic: TacticReq{Type: "ematch"},
	})
	if err == nil {
		assert.False(t, out.Success, "ematch on a ∀-free goal must not apply")
	}
}

// keepEMatchResident reports whether a kit hyp should stay resident
// for the refuter's single-rung work at Skolem points: the PairEq
// (pair-equality decomposition) and InInsert (insert-membership
// unfold) shapes. Identified structurally: a ∀-matrix whose LHS atom
// is a pair equality, or a set_member-insert iff.
func keepEMatchResident(h core.Term) bool {
	_, matrix := stripLeadingForalls(h)
	l, _, ok := ext.MatchesIFF(matrix)
	if !ok {
		return false
	}
	// PairEq: (a,b) = (x,y)
	if lhs, _, eqOK := ext.MatchesEQ(l); eqOK {
		if head, _ := ext.MatchesApply(lhs); head != nil {
			if c, isConst := head.AsConst(); isConst && c.Name() == "," {
				return true
			}
		}
	}
	// InInsert: set_member(x', insert(x, s))
	if head, args := ext.MatchesApply(l); head != nil && len(args) == 2 {
		if c, isConst := head.AsConst(); isConst && c.Name() == "set_member" {
			if h2, _ := ext.MatchesApply(args[1]); h2 != nil {
				if c2, isConst2 := h2.AsConst(); isConst2 && c2.Name() == "insert" {
					return true
				}
			}
		}
	}
	return false
}

// allOpenLeafIDs returns the goal ids of every unsolved leaf, sorted.
func allOpenLeafIDs(s *Session) []string {
	s.rebuildGoalIndex()
	var out []string
	for id, entry := range s.goalIndex {
		if entry.node.Proved() {
			continue
		}
		leaves := entry.node.UnsolvedLeaves()
		if len(leaves) > 0 && entry.node == leaves[0] && len(entry.node.UnsolvedLeaves()) == 1 {
			out = append(out, id)
		}
	}
	slices.Sort(out)
	return out
}
