package engine

// End-to-end tests for the specialized-reference transport: a session
// cites a REGISTRY entry at a type instance — a `by` premise grounded
// by term_specialize, a `simp_with` rule auto-adapted to the goal's
// type — and emit-section renders the instance under the entry's
// registered name — the typed wrapper's `X.Inst[τ]()` for a landed sole-letter entry, `ctx.AtTypes(ctx.Dep(name), τ…)` otherwise — with the entry in
// dep_names. Before, the claim child's stamped source (the registry
// NAME the agent cited) resolved to nothing and the premise rendered as
// a nil-cert TODO, absent from dep_names.

import (
	"context"
	"go/parser"
	"go/token"
	"os"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/emit"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// statedSessionEnv is the chapter-const-aware env with a CNF store in
// front, as the serve wires one (engine.SessionCNFStore there): a session's live refute
// writes its certificate where emit-section's strict collection reads
// it back. Without a store the collection MISSes by construction.
func statedSessionEnv() *proof.ProverEnv {
	env := familySessionEnv()
	env.ProofService.CNFStore = proof.NewMemoryCNFStore()
	return env
}

// instanceBodyAtNum instantiates a registered polymorphic statement's
// type variable A at num and strips its leading ∀s, leaving their
// variables free — the matrix a session states about a concrete type.
func instanceBodyAtNum(stated core.Prop) core.Term {
	return instanceBodyAt(stated, dsl.NumType)
}

// instanceBodyAt is instanceBodyAtNum at any type.
func instanceBodyAt(stated core.Prop, at core.HolType) core.Term {
	inst := core.PropTypeInst(stated, core.MakeTypeSubst(core.MakeVarType("A"), at))
	body := inst.Conclusion()
	for {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			return body
		}
		body = abs.Body()
	}
}

func parsesAsGo(t *testing.T, src string) {
	t.Helper()
	if _, err := parser.ParseFile(token.NewFileSet(), "emitted.go", src, parser.AllErrors); err != nil {
		t.Fatalf("emitted source does not parse: %v\n--- source: ---\n%s", err, src)
	}
}

// TestEmitSection_ByPremiseEntryAtTypeInstance: `by` with the
// polymorphic set_order.SubsetRefl grounded at a num-typed set — the
// witness pins A := num, the claim child closes as a TypeInst of the
// entry stamped with the registry name — renders the premise as the
// entry at that instance and declares the dep.
func TestEmitSection_ByPremiseEntryAtTypeInstance(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	goal := prop.MakeProp(instanceBodyAtNum(set_order.SubsetRefl.Entry().Statement().Prop)) // ⊢ s ⊆ s, s: num → bool
	goalID := s.AddGoal(goal)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
			{Key: "set_order.SubsetRefl", TermSpecialize: map[string]string{"s": "s"}},
		}},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "by should close s ⊆ s from SubsetRefl at s; diagnostics: %v", res.Diagnostics)
	require.True(t, s.sections[0].root.Proved())

	// The same-family sibling is a typed Dep, the entry's Key is the
	// statement's own.
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ReflAtNum", Family: "sets/set_order"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, `At(SubsetRefl.Inst[Nat](), `,
		"the premise renders as the entry at its instance, in the family's own spelling — the typed wrapper's Inst, not the ctx.AtTypes string channel\n--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AtTypes(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.DepNames, "set_order.SubsetRefl")
	assert.NotContains(t, out.Go, "Deps:", "a proved member renders no Deps — its recording observes what it reads\n--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, `Key:  "`+string(registry.KeyOf(goal))+`",`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "TODO", "--- source: ---\n%s", out.Go)
	// The premise renders by reference, so its statement's vocabulary
	// (subset at the entry's own letter) is not declared beside the
	// family's own; the witness `s` keeps its Go binding.
	assert.NotContains(t, out.Go, "ctx.Const(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, `s := ctx.Var("s", `, "--- source: ---\n%s", out.Go)

	// A member spelling is not a family path.
	_, err = e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ReflAtNum", Family: "sets/set_order.SubsetRefl"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "registered PATH")

	// The same entry cited at its OWN type (no instance): the bare
	// registered name — the entry's headline is what the session served
	// and what ctx.Dep serves, so nothing is instantiated.
	info2, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s2, err := e.getSession(info2.ID)
	require.NoError(t, err)
	polyBody := set_order.SubsetRefl.Entry().Statement().Prop.Conclusion()
	for abs := ext.MatchesFORALL(polyBody); !abs.IsZero(); abs = ext.MatchesFORALL(polyBody) {
		polyBody = abs.Body()
	}
	goal2ID := s2.AddGoal(prop.MakeProp(polyBody)) // ⊢ s ⊆ s, s: A → bool
	res, err = e.ApplyStep(ctx, info2.ID, &ApplyStepRequest{
		GoalID: goal2ID,
		Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "set_order.SubsetRefl"}}},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	out, err = e.EmitSection(&EmitSectionRequest{SessionID: info2.ID, Section: 0, FuncName: "Build_ReflPoly", Family: "sets/set_order"})
	require.NoError(t, err)
	// A polymorphic dep cited at no particular instance is the entry var
	// itself — the By premise machinery installs its normalized clause
	// — never the registered name as a string.
	assert.Contains(t, out.Go, `By(SubsetRefl)`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AtTypes(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.DepNames, "set_order.SubsetRefl")
}

// TestEmitSection_SimpRuleEntryAtTypeInstance: `simp_with` over the
// polymorphic set_order.SubsetAntisymEq, auto-adapted to the goal's
// num-typed sets (the rule child is a TypeInst of the entry), renders
// the rule as the bare entry under its stated orientation (Fwd: the
// session fired the headline as written) — Go's Simp adapts the entry
// to the same instance — and declares the dep.
func TestEmitSection_SimpRuleEntryAtTypeInstance(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	// From `s = t ⇔ s ⊆ t ∧ t ⊆ s` at num: the goal `s = t ⇒ s ⊆ t`.
	body := instanceBodyAtNum(set_order.SubsetAntisymEq.Entry().Statement().Prop)
	eq, both, ok := core.MatchesEQ(body)
	require.True(t, ok, "the headline is an iff: %s", ext.PrintTerm(body))
	conj := ext.DecomposesAND(both)
	require.Len(t, conj, 2)
	goal := prop.MakeProp(ext.WrapTerm(eq).Imply(conj[0]).Core())
	goalID := s.AddGoal(goal)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: "set_order.SubsetAntisymEq"}}},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "simp_with should rewrite s = t; diagnostics: %v", res.Diagnostics)
	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1, "one residual after the rewrite")
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, res.Success, "auto should close the residual; diagnostics: %v", res.Diagnostics)
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_AntisymAtNum", Family: "sets/set_order"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, `Simp(Fwd(SubsetAntisymEq))`,
		"the rule renders as the bare entry, which Go's Simp adapts to the goal's instance\n--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AtTypes(", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "Inst[", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "TODO: external lemma", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.DepNames, "set_order.SubsetAntisymEq")
}

// emitAntisymRulePinnedAt rewrites `s = t ∧ u = v ⇒ s ⊆ t ∧ u ⊆ v`, s and
// t sets of the given element type, u and v sets of num, by `simp_with`
// over the polymorphic set_order.SubsetAntisymEq pinned at the element
// type — a goal that spells more than the pin, so the rule's instance
// is one Go's Simp would not fire alone and stays spelled — closes the
// residual by the set driver and emits the section into the named
// family.
func emitAntisymRulePinnedAt(t *testing.T, element string, family string) *EmitSectionResult {
	t.Helper()
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	// The sets are free variables, as the matrix a session states about
	// concrete types has them: the member's statement binds none.
	parsed := dsl.ParsePropTextInScope("∀s t:set("+element+"). ∀u v:set(num). s = t ∧ u = v ⇒ s ⊆ t ∧ u ⊆ v", &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors)
	body := parsed.Prop.Conclusion()
	for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
		body = abs.Body()
	}
	s.AddGoal(prop.MakeProp(body))
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{
		{Key: "set_order.SubsetAntisymEq", TypeSpecialize: map[string]string{"A": element}}}})
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "by", Settac: true, ByHyps: hyp0()})
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_AntisymAtInstance", Family: family})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	return out
}

// TestEmitSection_SimpRuleEntryAtRealInstance: the rule pinned at sets
// of reals and emitted into a family whose statements bind reals renders
// as the wrapper's instance at the typedef's phantom, `Inst[Real]()` —
// never through the ctx.AtTypes string channel.
func TestEmitSection_SimpRuleEntryAtRealInstance(t *testing.T) {
	out := emitAntisymRulePinnedAt(t, "real", "real/real_topology")
	assert.Contains(t, out.Go, `Simp(Fwd(set_order.SubsetAntisymEq.Inst[Real]()))`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AtTypes(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.DepNames, "set_order.SubsetAntisymEq")
}

// TestEmitSection_SimpRuleEntryAtIntInstance: the same rule pinned at
// sets of integers, emitted into a family whose statements bind
// integers, renders `Inst[Int]()`.
func TestEmitSection_SimpRuleEntryAtIntInstance(t *testing.T) {
	out := emitAntisymRulePinnedAt(t, "int", "int_num/int_divides")
	assert.Contains(t, out.Go, `Simp(Fwd(set_order.SubsetAntisymEq.Inst[Int]()))`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AtTypes(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.DepNames, "set_order.SubsetAntisymEq")
}

// TestEmitSection_ChapterPhantomOnlyWhereTheFamilyHasIt: the phantom
// of a type a CHAPTER mints is aliased in a family's generated wrapper
// file only where a signature of the family names the type. The set
// chapter binds no complex number, so `Complex` is undefined in its
// proof files, and the rule emitted there keeps the instance its string
// channel spells — a line that compiles — where `Inst[Complex]()` would
// not; emitted into a chapter whose statements bind complex numbers,
// the same rule renders the wrapper's instance.
//
// A type minted below the chapters is another matter. `Real` is a name
// of library/authoring, in every proof file's scope, so the rule over
// sets of reals renders `Inst[Real]()` in the set chapter as well.
func TestEmitSection_ChapterPhantomOnlyWhereTheFamilyHasIt(t *testing.T) {
	out := emitAntisymRulePinnedAt(t, "complex", "sets/set_order")
	assert.Contains(t, out.Go, `Simp(Fwd(ctx.AtTypes(ctx.Dep(SubsetAntisymEq), MakeType("complex"))))`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "Inst[Complex]", "--- source: ---\n%s", out.Go)

	out = emitAntisymRulePinnedAt(t, "complex", "complex/complex_exp")
	assert.Contains(t, out.Go, `Simp(Fwd(set_order.SubsetAntisymEq.Inst[Complex]()))`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AtTypes(", "--- source: ---\n%s", out.Go)

	out = emitAntisymRulePinnedAt(t, "real", "sets/set_order")
	assert.Contains(t, out.Go, `Simp(Fwd(SubsetAntisymEq.Inst[Real]()))`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AtTypes(", "--- source: ---\n%s", out.Go)
}

// TestEmitSection_ByLiveRefuteCollects: a `by` whose close reaches the
// resolution stage (three clauses, no propositional shortcut) writes
// its certificate to the env's CNF store, and emit-section's strict
// collection reads it back into the returned blob — the session →
// emit certificate path, in process. Without a store the collection
// MISSes by construction (strictness is the design: emit never
// re-proves), which the second half pins as the loud failure it is.
func TestEmitSection_ByLiveRefuteCollects(t *testing.T) {
	// ∀x. P(x) ⇒ Q(x), P(a) ⊢ Q(a): Normalize does not close it (the
	// instance x := a is the refuter's to find), and the ∀-premise is
	// kept bare, so the close is a genuine resolution refute.
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(TypeInd, core.TypeBool())))
	Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(TypeInd, core.TypeBool())))
	a := ext.Var("a", TypeInd)
	x := ext.WrapTerm(ext.Var("x", TypeInd))
	goal := prop.MakeProp(Q.Apply(a).Core(),
		ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x))).Core(), P.Apply(a).Core())

	run := func(t *testing.T, env *proof.ProverEnv, shape *ByShapeReq) (*EmitSectionResult, error) {
		t.Helper()
		e := newEngine(env)
		ctx := context.Background()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		goalID := addStrippedGoal(t, e, info.ID, goal)
		g := s.goalIndex[goalID].node.Goal
		hyps := make([]ByHypSpec, g.NumHyps())
		for i := range hyps {
			idx := i
			hyps[i] = ByHypSpec{HypIndex: &idx}
		}
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "by", ByHyps: hyps, ByShape: shape},
		})
		require.NoError(t, err)
		require.True(t, res.Success, "by should close Q(a); diagnostics: %v", res.Diagnostics)
		require.True(t, s.sections[0].root.Proved())
		return e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_Resolve", Family: "real/real_field"})
	}
	storedProofs := func(store *proof.MemoryCNFStore) int {
		n := 0
		store.ScanProofs(func(core.PropKey, *refuter.CNFRefuteProofProto) bool { n++; return true })
		return n
	}

	// Raw: the conditioning stage is off, so the close IS a refute.
	t.Run("raw, store", func(t *testing.T) {
		env := testEnv()
		store := proof.NewMemoryCNFStore()
		env.ProofService.CNFStore = store
		out, err := run(t, env, &ByShapeReq{Raw: true})
		require.NoError(t, err)
		parsesAsGo(t, out.Go)
		assert.Contains(t, out.Go, "By(Raw, h, h2)")
		require.Equal(t, 1, storedProofs(store), "the session's live refute writes one certificate")
		require.NotEmpty(t, out.CNFCache, "the certificate must be collected into the blob")
	})
	t.Run("raw, no store", func(t *testing.T) {
		out, err := run(t, testEnv(), &ByShapeReq{Raw: true})
		require.Error(t, err)
		assert.Contains(t, err.Error(), "CNF cache MISS")
		// The rendering reads no certificate: the member comes back
		// beside the collection error, its cache empty.
		require.NotNil(t, out, "the rendered member is returned beside the collection error")
		parsesAsGo(t, out.Go)
		assert.Contains(t, out.Go, "By(Raw, h, h2)")
		assert.Empty(t, out.CNFCache)
	})
}

// TestEmitSection_StrictProbeReadsBareCertificate: a `by` the session
// closed BARE (its certificate under the bare working leaf's key) must
// be read back by the strict collection's rung-1 probe — the ladder's
// cache-only bare attempt — and never fall through to the conditioned
// rung, whose leaf keys differently and MISSes. The record is the Raw
// close's proto with the Raw flag cleared, i.e. the same close
// re-recorded under the default ladder. The guard is spelled ¬¬P(a):
// the apply rung declines it, so the keyless probe the strict ladder
// asks first does not close the leaf, and the certificate is what
// closes it.
func TestEmitSection_StrictProbeReadsBareCertificate(t *testing.T) {
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(TypeInd, core.TypeBool())))
	Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(TypeInd, core.TypeBool())))
	a := ext.Var("a", TypeInd)
	x := ext.WrapTerm(ext.Var("x", TypeInd))
	goal := prop.MakeProp(Q.Apply(a).Core(),
		ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x))).Core(), ext.Not(ext.Not(P.Apply(a))).Core())

	env := testEnv()
	store := proof.NewMemoryCNFStore()
	env.ProofService.CNFStore = store
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	goalID := s.AddGoal(goal)
	g := s.goalIndex[goalID].node.Goal
	hyps := make([]ByHypSpec, g.NumHyps())
	for i := range hyps {
		idx := i
		hyps[i] = ByHypSpec{HypIndex: &idx}
	}
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "by", ByHyps: hyps, ByShape: &ByShapeReq{Raw: true}},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	require.Equal(t, 1, store.Len(), "the bare close wrote one certificate")

	detailed := s.sections[0].root.DetailedProofProto()
	require.NotNil(t, detailed)
	cleared := false
	for _, step := range detailed.Steps {
		if st, ok := step.Step.(*proof.StepProto_By); ok && st.By.GetShape() != nil && st.By.GetShape().GetRaw() {
			st.By.Shape.Raw = false
			cleared = true
		}
	}
	require.True(t, cleared, "the record carries the Raw close")

	cache, err := emit.CollectCNFCache(env, []*proof.DetailedProofProto{detailed})
	require.NoError(t, err, "the strict probe must read the bare certificate back")
	require.NotEmpty(t, cache.GetEntries(), "the bare certificate is what the blob carries")
}

// TestEmitSection_ProbeMemberWriteOut is the session → emit → compile →
// replay recipe's first half, kept as a tool: with
// XUGO_EMIT_PROBE_OUT=<path under library/proofs/sets/set_order/>
// it proves `∀s t:(num → bool). s = t ⇒ s ⊆ t` in a session (intro,
// simp_with the polymorphic set_order.SubsetAntisymEq at the goal's
// instance, expand), emits the family member ZzProbeAntisymAtNum
// and writes the file there. The second half is the harness:
//
//	XUGO_REPLAY_ONE=set_order.ZzProbeAntisymAtNum go test ./library/integrity/gates/ -run TestReplayAll
//
// then delete the file. Without the variable the test only checks the
// emitted rendering.
func TestEmitSection_ProbeMemberWriteOut(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "sets/set_order", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	stated := set_order.SubsetAntisymEq.Entry().Statement().Prop
	inst := core.PropTypeInst(stated, core.MakeTypeSubst(core.MakeVarType("A"), dsl.NumType))
	// ∀s t. s = t ⇒ s ⊆ t, rebuilt from the instantiated headline's
	// binders and matrix.
	sAbs := ext.MatchesFORALL(inst.Conclusion())
	require.False(t, sAbs.IsZero())
	tAbs := ext.MatchesFORALL(sAbs.Body())
	require.False(t, tAbs.IsZero())
	eq, both, ok := core.MatchesEQ(tAbs.Body())
	require.True(t, ok)
	conj := ext.DecomposesAND(both)
	require.Len(t, conj, 2)
	matrix := ext.WrapTerm(eq).Imply(conj[0])
	goal := prop.MakeProp(ext.ForAll(ext.WrapTerm(sAbs.Var()), ext.WrapTerm(tAbs.Var()))(matrix).Core())
	goalID := s.AddGoal(goal)

	apply := func(tactic TacticReq) {
		t.Helper()
		state, err := e.InspectState(ctx, info.ID)
		require.NoError(t, err)
		require.Len(t, state.Goals, 1, "one open goal before %s", tactic.Type)
		t.Logf("before %s: %s", tactic.Type, prop.PrintProp(state.Goals[0].Statement))
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: tactic})
		require.NoError(t, err)
		require.True(t, res.Success, "%s failed; diagnostics: %v", tactic.Type, res.Diagnostics)
	}
	_ = goalID
	apply(TacticReq{Type: "intro"}) // strips both ∀s
	apply(TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: "set_order.SubsetAntisymEq"}}})
	apply(TacticReq{Type: "expand"})
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: 0, FuncName: "Build_ZzProbeAntisymAtNum", Family: "sets/set_order",
	})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, `Simp(Fwd(SubsetAntisymEq))`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "Deps:", "a proved member renders no Deps — its recording observes what it reads\n--- source: ---\n%s", out.Go)
	// No declaration wall: the rule renders by reference (its
	// polymorphic source — subset at A, the η-binder ẋ — is never
	// printed), the family's vocabulary declares subset, and no body
	// text mentions the Skolems s / t.
	assert.NotContains(t, out.Go, "ctx.Const(", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "ctx.Var(", "--- source: ---\n%s", out.Go)
	t.Logf("emitted member (%d bytes of CNF blob):\n%s", len(out.CNFCache), out.Go)
	if path := os.Getenv("XUGO_EMIT_PROBE_OUT"); path != "" {
		require.NoError(t, os.WriteFile(path, []byte(out.Go), 0o644))
		t.Logf("wrote %s", path)
	}
}

// numGoal parses a goal text in the session's scope (the define battery's
// addGoal) and adds it.
func addTextGoal(t *testing.T, s *Session, text string) string {
	t.Helper()
	parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
		ConstResolver:      envConstResolver(s.env),
		StrictResolution:   true,
		FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "goal %q", text)
	return s.AddGoal(parsed.Prop)
}

// applyOnSoleGoal applies a tactic to the session's one open goal.
func applyOnSoleGoal(t *testing.T, e *Engine, sid string, tactic TacticReq) *StepResult {
	t.Helper()
	ctx := context.Background()
	state, err := e.InspectState(ctx, sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1, "one open goal before %s", tactic.Type)
	t.Logf("before %s: %s", tactic.Type, prop.PrintProp(state.Goals[0].Statement))
	res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: tactic})
	require.NoError(t, err)
	require.True(t, res.Success, "%s failed; diagnostics: %v", tactic.Type, res.Diagnostics)
	return res
}

// TestEmitSection_LeanRwEntryAtTypeInstance: a session `lean_rw` by a
// polymorphic entry, adapted to the goal's instance, renders the rule
// as the entry's stated form at that instance — no statement text, no
// const wall — and declares the dep. With
// XUGO_EMIT_PROBE_LEANRW_OUT=<file under library/proofs/sets/set_order/>
// the family member is written out for the harness
// (XUGO_REPLAY_ONE=set_order.ZzProbeLeanRwAtNum).
func TestEmitSection_LeanRwEntryAtTypeInstance(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "sets/set_order", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀s t:(num → bool). s = t ⇒ s ⊆ t")
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
	// The rewrite closes the rewritten residual itself (it normalizes to
	// ⊤), and the rule's reproduction obligation — the entry at the
	// goal's instance — closes on the cite: the entry the author named
	// certifies its own instance.
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "lean_rw", LemmaKey: "set_order.SubsetAntisymEq"})
	require.True(t, s.sections[0].root.Proved())

	// The session is bound to set_order, so the family is the default.
	fam, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ZzProbeLeanRwAtNum"})
	require.NoError(t, err)
	parsesAsGo(t, fam.Go)
	assert.Contains(t, fam.Go, `LeanRw(ctx.AtTypes(ctx.Dep(SubsetAntisymEq), NumType).Reference())`, "--- source: ---\n%s", fam.Go)
	assert.NotContains(t, unspaced(fam.Go), `LeanRw(ctx.MakePropText(`, "--- source: ---\n%s", fam.Go)
	assert.Contains(t, fam.DepNames, "set_order.SubsetAntisymEq")
	assert.NotContains(t, fam.Go, "Deps:", "a proved member renders no Deps — its recording observes what it reads\n--- source: ---\n%s", fam.Go)
	if path := os.Getenv("XUGO_EMIT_PROBE_LEANRW_OUT"); path != "" {
		require.NoError(t, os.WriteFile(path, []byte(fam.Go), 0o644))
	}
}

// TestEmitSection_ACRegroupRenders: a session `ac_regroup` records the
// composite and emits as the kit's goal face over the two entries,
// both declared, where it once emitted as an unresolved TODO
// placeholder. With XUGO_EMIT_PROBE_AC_OUT=<file under
// library/proofs/nat_num/nat_arith/> the family member is written out
// (XUGO_REPLAY_ONE=nat_arith.ZzProbeAcRegroup).
func TestEmitSection_ACRegroupRenders(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "nat_num/nat_arith", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀a b c:num. (a + b) + c = c + (b + a)")
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "ac_regroup", Assoc: "nat_arith.AddAssoc", Sym: "nat_arith.AddSym"})
	require.True(t, s.sections[0].root.Proved())
	detailed := s.sections[0].root.DetailedProofProto()
	sawComposite := false
	for _, st := range detailed.Steps {
		if _, ok := st.Step.(*proof.StepProto_AcRegroup); ok {
			sawComposite = true
		}
	}
	require.True(t, sawComposite, "the session records the AC composite")

	fam, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ZzProbeAcRegroup"})
	require.NoError(t, err)
	parsesAsGo(t, fam.Go)
	assert.Contains(t, fam.Go, `ACRegroup(ctx.Dep(AddAssoc), ctx.Dep(AddSym))`, "--- source: ---\n%s", fam.Go)
	assert.NotContains(t, fam.Go, "TODO", "--- source: ---\n%s", fam.Go)
	assert.Contains(t, fam.DepNames, "nat_arith.AddAssoc")
	assert.Contains(t, fam.DepNames, "nat_arith.AddSym")
	assert.NotContains(t, fam.Go, "Deps:", "a proved member renders no Deps — its recording observes what it reads\n--- source: ---\n%s", fam.Go)
	if path := os.Getenv("XUGO_EMIT_PROBE_AC_OUT"); path != "" {
		require.NoError(t, os.WriteFile(path, []byte(fam.Go), 0o644))
	}
}

// TestEmitSection_PinnedSimpRuleNote: a `simp_with` rule pinned by
// term_specialize is spelled out with the pin named, never fused into a
// Simp over the ∀-form.
func TestEmitSection_PinnedSimpRuleNote(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	// ⊢ (a + 0) + b = a + b, a and b free under their own names (the
	// pin names a); the pinned instance a + 0 = a rewrites a proper
	// subterm (a rule equal to the goal itself is refused as circular).
	parsed := dsl.ParsePropTextInScope("∀a b:num. (a + 0) + b = a + b", &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors)
	body := parsed.Prop.Conclusion()
	for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
		body = abs.Body()
	}
	s.AddGoal(prop.MakeProp(body))
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{
		{Key: "nat_arith.AddZero", TermSpecialize: map[string]string{"m": "a"}},
	}})
	if !s.sections[0].root.Proved() {
		applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "expand"})
	}
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_Pinned", Family: "nat_num/nat_arith"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.NotContains(t, out.Go, "Simp(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "nat_arith.AddZero pinned at a —", "--- source: ---\n%s", out.Go)
	t.Logf("pinned rendering:\n%s", out.Go)
}

// TestEmitSection_DefineAuthorText: the define door's emitted literal
// carries the author's own type and equation texts, not the printer's.
func TestEmitSection_DefineAuthorText(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	const eq = "∀m n:num. zz_probe_author_t(m, n) ⇔ m = n"
	res, err := e.Define(&DefineRequest{SessionID: info.ID, Recursive: &DefineRecursive{
		Name: "zz_probe_author_t", Type: "num → num → bool", Equations: []string{eq},
	}})
	require.NoError(t, err)
	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: res.Section, FuncName: "Build_ZzProbeAuthorT", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, `Type:  "num → num → bool",`, "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, `"`+eq+`",`, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "var:", "the printer's type-variable spelling must not appear\n--- source: ---\n%s", out.Go)
}

// TestResolveLemma_KeyAndNameServeOneForm: a member cited by its own
// KEY serves the member's statement — the form its NAME serves, the
// form `query member` prints for the key, and the form ctx.Dep(<member>)
// serves at replay.
func TestResolveLemma_KeyAndNameServeOneForm(t *testing.T) {
	stated := nat_order.SucLessEqSucIff.Entry().Statement().Prop
	memberKey := nat_order.SucLessEqSucIff.Entry().Key

	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	goal := prop.MakeProp(ext.Var("C", core.TypeBool()).Core())

	byKey, err := e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: memberKey}, goal)
	require.NoError(t, err)
	byName, err := e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: "nat_order.SucLessEqSucIff"}, goal)
	require.NoError(t, err)
	assert.True(t, byKey.AlphaEquals(stated), "by key: want the member's statement, got %s", prop.PrintProp(byKey))
	assert.True(t, byName.AlphaEquals(stated), "by name: want the member's statement, got %s", prop.PrintProp(byName))

}

// TestEmitSection_SimpMarkerAcrossKeyAndName: two sessions rewrite with
// the same member — by name and by its own key — and emit renders ONE
// marker for both, read against the statement the emitted target
// serves.
func TestEmitSection_SimpMarkerAcrossKeyAndName(t *testing.T) {
	memberKey := nat_order.SucLessEqSucIff.Entry().Key

	run := func(t *testing.T, rule LemmaWithSpec) *EmitSectionResult {
		t.Helper()
		e := newEngine(statedSessionEnv())
		ctx := context.Background()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		// ⊢ suc(a) ≤ suc(b) ⇒ a ≤ b: the rewrite folds the antecedent to
		// a ≤ b and the residual is a tautology.
		parsed := dsl.ParsePropTextInScope("∀a b:num. suc(a) ≤ suc(b) ⇒ a ≤ b", &dsl.ParseScope{
			ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors)
		body := parsed.Prop.Conclusion()
		for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
			body = abs.Body()
		}
		s.AddGoal(prop.MakeProp(body))
		applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{rule}})
		if !s.sections[0].root.Proved() {
			applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "expand"})
		}
		require.True(t, s.sections[0].root.Proved())
		out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_Marker", Family: "nat_num/nat_order"})
		require.NoError(t, err)
		parsesAsGo(t, out.Go)
		return out
	}
	byName := run(t, LemmaWithSpec{Key: "nat_order.SucLessEqSucIff"})
	byKey := run(t, LemmaWithSpec{Key: memberKey})
	// The marker: Fwd for both, and the rule is the entry var either way
	// (a same-family sibling, so the bare member name) — the cite never
	// spells the registered name as a string.
	for _, c := range []struct {
		name string
		out  *EmitSectionResult
	}{{"by name", byName}, {"by key", byKey}} {
		assert.Contains(t, c.out.Go, `Simp(Fwd(`, "%s\n--- source: ---\n%s", c.name, c.out.Go)
		assert.Contains(t, c.out.Go, `Simp(Fwd(SucLessEqSucIff))`, "%s\n--- source: ---\n%s", c.name, c.out.Go)
		assert.NotContains(t, c.out.Go, `Rev(`, "%s: the marker is recomputed against the member's statement\n--- source: ---\n%s", c.name, c.out.Go)
	}
}

// An explicit identity type binding remains exact even when another
// carrier in the goal gives the automatic adapter a competing instance:
// the emitted premise is the entry's typed wrapper at its own letters,
// `CyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())`, which
// installs as the recorded `ctx.AtTypes(ctx.Dep(CyclesDef), A, B)` did.
func TestEmitSection_ByPremiseExactIdentity(t *testing.T) {
	for _, bound := range []bool{false, true} {
		name := "unbound"
		if bound {
			name = "bound"
		}
		t.Run(name, func(t *testing.T) {
			e := newEngine(statedSessionEnv())
			ctx := context.Background()
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			if bound {
				_, err = e.SetSessionFamily(info.ID, "algebra/module/chain_complex", nil)
				require.NoError(t, err)
			}
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			parsed := dsl.ParsePropTextInScope("∀P:complex_ops(A, B). ∀Q:complex_ops(A, D). ∀n:num. ∀z:D. ∀w:B. z ∈ cycles(Q, n) ∧ w ∈ cycles(P, n) ⇒ w ∈ P.terms(n)", s.StatementDoorScope())
			require.Empty(t, parsed.Errors)
			gid := s.AddGoal(parsed.Prop)
			for _, typ := range []string{"strip_quant", "strip_imp"} {
				res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
				require.NoError(t, err)
				require.Len(t, res.Produced, 1)
				gid = res.Produced[0].GoalID
			}
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
				GoalID: gid,
				Tactic: TacticReq{Type: "by", Settac: true, ByHyps: hyp0(), WithLemmas: []LemmaWithSpec{{
					Key: "chain_complex.CyclesDef", TypeSpecialize: map[string]string{"A": "A", "B": "B"},
				}}},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
			require.True(t, s.sections[0].root.Proved())
			var found bool
			for _, step := range s.sections[0].root.DetailedProofProto().GetSteps() {
				for _, premise := range step.GetBy().GetPremises() {
					found = found || premise.GetExact()
				}
			}
			require.True(t, found, "the session must record an exact premise")
			out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ExactCycles", Family: "algebra/module/chain_complex"})
			require.NoError(t, err)
			parsesAsGo(t, out.Go)
			require.Contains(t, out.Go, "BySets(h, CyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))",
				"the identity binding must survive emission:\n%s", out.Go)
			require.NotContains(t, out.Go, "AtTypes(", "a landed entry is cited through its wrapper:\n%s", out.Go)
			require.Contains(t, out.DepNames, "chain_complex.CyclesDef")
			if bound {
				replayEmittedInFamily(t, "algebra/module/chain_complex", "ExactCycles", out)
			}
		})
	}
}

// TestEmitSection_ByPrefixAtTypeInstance keeps a named premise whose
// positional prefix fixes its type while leaving later binders quantified.
func TestEmitSection_ByPrefixAtTypeInstance(t *testing.T) {
	e, s := boundSession(t, "algebra/field/finite_field")
	addTextGoal(t, s, "∀p:num. ring_ideal(int_ring, ideal_span(int_ring, {int_of_num(p)})) ⇒ int_of_num(p) ∈ ideal_span(int_ring, {int_of_num(p)}) ⇒ image(λz:int. int_of_num(p) * z, 𝕌) ⊆ ideal_span(int_ring, {int_of_num(p)})")
	for _, step := range []string{"strip_quant", "strip_imp", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{
		Type:   "by",
		Settac: true,
		ByHyps: []ByHypSpec{
			{HypIndex: hypAt(t, e, s, sole, "ring_ideal(")},
			{HypIndex: hypAt(t, e, s, sole, "int_of_num(p₀) ∈")},
		},
		WithLemmas: []LemmaWithSpec{
			{Key: "ring_ideal.IdealMul", TermSpecialize: map[string]string{
				"R": "int_ring", "I": "ideal_span(int_ring, {int_of_num(p₀)})",
			}},
			{Key: "int_real_lift.MulSym", TermSpecialize: map[string]string{"x": "int_of_num(p₀)"}},
		},
	})
	const pkg = "zzbytypedprefix"
	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: s.ID, Section: 0, FuncName: "Build_ZzByTypedPrefix", Family: emitScratchFamily(pkg),
	})
	require.NoError(t, err)
	assert.Contains(t, out.DepNames, "ring_ideal.IdealMul")
	require.NotContains(t, out.Go, "TODO: unresolved lemma", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "ring_ideal.IdealMul")
	replayEmitted(t, pkg, "ZzByTypedPrefix", out.Go)
}

// TestEmitSection_ByPrefixInstallOffClause keeps a named ⇔ premise
// whose positional prefix fixes its types. The premise installs its
// clause form, the entry's normalized statement at the instance, and
// neither that clause nor its Normalize is the recorded install or the
// install's Normalize: the ∀-prefix comes out in another order. However
// the claim child certifies, its close names no key the emitter looks
// the install up by, so the premise is named only through the entry the
// session recorded for it.
func TestEmitSection_ByPrefixInstallOffClause(t *testing.T) {
	e, s := boundSession(t, "sets/set_product")
	addTextGoal(t, s, "∀s:set(num). ∀t:set(num). s = ∅ ⇒ set_cross(s, t) = ∅")
	for _, step := range []string{"strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{
		Type:   "by",
		ByHyps: hyp0(),
		WithLemmas: []LemmaWithSpec{
			{Key: "set_product.CrossEmptyIff", TermSpecialize: map[string]string{"s": "s₀", "t": "t₀"}},
		},
	})
	detailed := s.sections[0].root.DetailedProofProto()
	r := ext.NewPoolReader(detailed.Pool, e.env.ProofService.LoadConstMeta)
	var exact int
	for _, step := range detailed.GetSteps() {
		for _, premise := range step.GetBy().GetPremises() {
			if premise.GetClause() == nil {
				continue
			}
			exact++
			install, _ := r.Prop(premise.GetInstall())
			clause, _ := r.Prop(premise.GetClause())
			normalized, _ := prop.Normalize(install)
			normalizedClause, _ := prop.Normalize(clause)
			for _, k := range []core.PropKey{install.AlphaKey(), normalized.AlphaKey()} {
				require.NotContains(t, []core.PropKey{clause.AlphaKey(), normalizedClause.AlphaKey()}, k,
					"install %s\nclause %s", prop.PrintProp(install), prop.PrintProp(clause))
			}
		}
	}
	require.Equal(t, 1, exact, "the session records one explicit instance")
	const pkg = "zzbyinstalloffclause"
	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: s.ID, Section: 0, FuncName: "Build_ZzByInstallOffClause", Family: emitScratchFamily(pkg),
	})
	require.NoError(t, err)
	assert.Contains(t, out.DepNames, "set_product.CrossEmptyIff")
	require.NotContains(t, out.Go, "TODO: unresolved lemma", "--- source: ---\n%s", out.Go)
	replayEmitted(t, pkg, "ZzByInstallOffClause", out.Go)
}
