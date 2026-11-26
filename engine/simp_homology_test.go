package engine

import (
	"context"
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/stretchr/testify/require"
)

// Class exactness must unfold in the presence of all the element-level
// structure facts: their type instances must not hide the class instance.
func TestSimp_ExactnessOfHomologyClasses(t *testing.T) {
	rule, ok := registry.ByName("module_homomorphism.ExactAtDef")
	require.True(t, ok)
	for _, name := range []string{"chain_complex.LongExactMiddle", "chain_complex.LongExactSub", "chain_complex.CoLongExactMiddle"} {
		t.Run(name, func(t *testing.T) {
			member, ok := registry.ByName(name)
			require.True(t, ok)
			conclusion := member.Statement().Prop.Conclusion()
			var hyps []core.Term
			for {
				_, conclusion = ext.DecomposesFORALL(conclusion)
				premise, body, implies := ext.MatchesIMPLY(conclusion)
				if !implies {
					break
				}
				hyps = append(hyps, premise)
				conclusion = body
			}
			goal := prop.MakeProp(conclusion, hyps...)
			instances := typematch.EnumerateLemmaTypeAdaptations(rule.Statement().Prop, goal)
			fired := false
			for _, instance := range instances {
				if sub := tactic.SimpWithExpandFlipped(goal, []core.Prop{instance}, nil); sub != nil {
					fired = true
				}
			}
			require.True(t, fired, "no enumerated instance unfolds exact_at in %s", prop.PrintProp(goal))
			e := newEngine(servedEnv(t))
			info, err := e.CreateSession(context.Background())
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			gid := s.AddGoal(goal)
			res, err := e.ApplyStep(context.Background(), info.ID, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: rule.Name}}},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "%+v", res.Diagnostics)
			require.Zero(t, openLeavesMentioning(t, e, info.ID, "exact_at"))
		})
	}
}

// A resident reading retains its free components in its hypotheses;
// a partial witness tuple must not mistake a remaining binder for a
// closure-added free variable.
func TestByRead_PartialTupleUnderResidentComplex(t *testing.T) {
	member, ok := registry.ByName("chain_complex.CycleLiftPullback")
	require.True(t, ok)
	_, body := ext.DecomposesFORALL(member.Statement().Prop.Conclusion())
	hyp, body, ok := ext.MatchesIMPLY(body)
	require.True(t, ok)
	n := ext.MatchesFORALL(body)
	require.False(t, n.IsZero())
	goal := prop.MakeProp(n.Body(), hyp)
	e := newEngine(servedEnv(t))
	info, err := e.CreateSession(t.Context())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	gid := s.AddGoal(goal)
	index := 0
	out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "by", WithLemmas: []LemmaWithSpec{{Key: member.Name,
			ReadAt: &ReadAtSpec{HypIndex: &index}, TermSpecialize: map[string]string{string(n.Var().Name()): ext.PrintTerm(n.Var())}}},
	}})
	require.NoError(t, err)
	require.True(t, out.Success, "%+v", out.Diagnostics)
	require.Zero(t, out.State.NumOpen)
}

type homologyReadDep string

func (d homologyReadDep) DepName() string { return string(d) }

// The projected subcomplex fixes A and B while its surrounding short
// exact sequence already names C. HomologyMapCoset's independent target
// carrier is therefore ♭C, and its witnesses must instantiate that
// letter without changing the sequence hypothesis.
func TestByRead_NestedHomologyMapWitnessTypes(t *testing.T) {
	env := servedEnv(t)
	projection, ok := registry.ByName("chain_complex.ShortExactSubComplex")
	require.True(t, ok)
	member, ok := registry.ByName("chain_complex.HomologyMapCoset")
	require.True(t, ok)
	if env.LibraryThms == nil {
		env.LibraryThms = map[string]core.Thm{}
	}
	// Script.Dep consumes realized certificates; this unit fixture
	// exercises the registry statements without replaying their proofs.
	env.LibraryThms[projection.Name] = core.TestThm(projection.Statement().Prop.Conclusion())
	env.LibraryThms[member.Name] = core.TestThm(member.Statement().Prop.Conclusion())
	_, body := ext.DecomposesFORALL(projection.Statement().Prop.Conclusion())
	sequence, _, ok := ext.MatchesIMPLY(body)
	require.True(t, ok)
	inner, err := proof.ReadLawAt(serve.EntryThm(env, projection), core.Assume(sequence))
	require.NoError(t, err)
	reading, err := proof.ReadLawAt(serve.EntryThm(env, member), inner)
	require.NoError(t, err)
	require.True(t, ext.TermAnyTypeVar(reading.Conclusion(), func(v core.VarType) bool { return v.Name() == "♭C" }))
	typed := core.PropTypeInst(reading, core.MakeTypeSubst(core.MakeVarType("♭C"), core.MakeVarType("C")))
	var witnesses []core.Term
	table := map[string]string{}
	hyps := []core.Term{sequence}
	body = typed.Conclusion()
	for {
		if abs := ext.MatchesFORALL(body); !abs.IsZero() {
			w := core.Var(fmt.Sprintf("readTarget%d", len(witnesses)), abs.Var().Type())
			witnesses = append(witnesses, w)
			table[string(abs.Var().Name())] = ext.PrintTerm(w)
			body = abs.Body().Substitute(core.MakeTermSubst(abs.Var(), w))
			continue
		}
		if hyp, next, ok := ext.MatchesIMPLY(body); ok {
			hyps = append(hyps, hyp)
			body = next
			continue
		}
		break
	}
	goal := prop.MakeProp(body, hyps...)
	t.Run("Go", func(t *testing.T) {
		script := proof.NewScript(env)
		section := script.Section(goal)
		read := proof.Read(homologyReadDep(member.Name), proof.Read(homologyReadDep(projection.Name), proof.ResidentHyp(sequence)))
		terms := make([]proof.TermLike, len(witnesses))
		for i, w := range witnesses {
			terms[i] = w
		}
		premises := []any{read.At(terms...)}
		for _, h := range goal.Hyps() {
			if !h.AlphaEquals(sequence) {
				premises = append(premises, proof.ResidentHyp(h))
			}
		}
		section.Do(proof.Derive(func(a *proof.Argument) {
			a.Show("the map on the representative", proof.By(premises...))
		}))
		require.True(t, section.Proved())
	})
	t.Run("session", func(t *testing.T) {
		e := newEngine(env)
		info, err := e.CreateSession(t.Context())
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		gid := s.AddGoal(goal)
		sequenceIndex := -1
		var listed []ByHypSpec
		for i, hyp := range goal.Hyps() {
			if hyp.AlphaEquals(sequence) {
				sequenceIndex = i
			} else {
				idx := i
				listed = append(listed, ByHypSpec{HypIndex: &idx})
			}
		}
		require.NotEqual(t, -1, sequenceIndex)
		out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
			Type: "by", ByHyps: listed, WithLemmas: []LemmaWithSpec{{Key: member.Name,
				ReadAt: &ReadAtSpec{Key: projection.Name, ReadAt: &ReadAtSpec{HypIndex: &sequenceIndex}}, TermSpecialize: table}},
		}})
		require.NoError(t, err)
		require.True(t, out.Success, "%+v", out.Diagnostics)
		require.Zero(t, out.State.NumOpen)
	})
	t.Run("Go/bare", func(t *testing.T) {
		script := proof.NewScript(env)
		section := script.Section(goal)
		read := proof.Read(homologyReadDep(member.Name), proof.Read(homologyReadDep(projection.Name), proof.ResidentHyp(sequence)))
		premises := []any{read}
		for _, h := range goal.Hyps() {
			if !h.AlphaEquals(sequence) {
				premises = append(premises, proof.ResidentHyp(h))
			}
		}
		section.Do(proof.Derive(func(a *proof.Argument) {
			a.Show("the map on the representative", proof.By(premises...))
		}))
		require.True(t, section.Proved())
	})
	t.Run("session/bare", func(t *testing.T) {
		e := newEngine(env)
		info, err := e.CreateSession(t.Context())
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		gid := s.AddGoal(goal)
		sequenceIndex := -1
		var listed []ByHypSpec
		for i, hyp := range goal.Hyps() {
			if hyp.AlphaEquals(sequence) {
				sequenceIndex = i
			} else {
				idx := i
				listed = append(listed, ByHypSpec{HypIndex: &idx})
			}
		}
		require.NotEqual(t, -1, sequenceIndex)
		out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
			Type: "by", ByHyps: listed, WithLemmas: []LemmaWithSpec{{Key: member.Name,
				ReadAt: &ReadAtSpec{Key: projection.Name, ReadAt: &ReadAtSpec{HypIndex: &sequenceIndex}}}},
		}})
		require.NoError(t, err)
		require.True(t, out.Success, "%+v", out.Diagnostics)
		require.Zero(t, out.State.NumOpen)
	})
}

// The degreewise exactness and boundary-image facts are already resident
// when LongExactMiddle unfolds its exactness at homology classes. They
// offer element-level rule instances beside the required class instance.
func TestSimp_ExactnessWithExpandedHomologyContext(t *testing.T) {
	member, ok := registry.ByName("chain_complex.LongExactMiddle")
	require.True(t, ok)
	conclusion := member.Statement().Prop.Conclusion()
	var hyps []core.Term
	for {
		_, conclusion = ext.DecomposesFORALL(conclusion)
		premise, body, implies := ext.MatchesIMPLY(conclusion)
		if !implies {
			break
		}
		hyps = append(hyps, premise)
		conclusion = body
	}
	goal := prop.MakeProp(conclusion, hyps...)
	env := servedEnv(t)
	for _, text := range []string{
		"∀k:num. (injective_on(P'.terms(k), i(k)) ∧ exact_at(P''.zero, P'.terms(k), P.terms(k), i(k), p(k))) ∧ image(p(k), P.terms(k)) = P''.terms(k)",
		"boundaries(P, n) = image(P.d(n + 1), P.terms(n + 1))",
		"boundaries(P'', n) = image(P''.d(n + 1), P''.terms(n + 1))",
		"left_coset(P''.add, P''.zero, image(P''.d(n + 1), P''.terms(n + 1))) = image(P''.d(n + 1), P''.terms(n + 1))",
		"subgroup(mk_group(P''.add, P''.zero, P''.neg, P''.terms(n)), image(P''.d(n + 1), P''.terms(n + 1)))",
		"exact_complexes(P', P, P'', i, p)",
		"submodule(R, complex_module(P, n), image(P.d(n + 1), P.terms(n + 1)))",
		"submodule(R, complex_module(P'', n), image(P''.d(n + 1), P''.terms(n + 1)))",
		"module_on(R, complex_module(P'', n))",
	} {
		parsed, err := parseClaimTextInGoalScope(text, goal, nil)
		require.NoError(t, err, "%s", text)
		hyps = append(hyps, parsed.Conclusion())
	}
	goal = prop.MakeProp(conclusion, hyps...)
	ruleNames := []string{"module_homomorphism.ExactAtDef", "set_basic.Extension", "group_homomorphism.InKernel"}
	t.Run("Go", func(t *testing.T) {
		script := proof.NewScript(env)
		var rules []proof.SimpRule
		for _, name := range ruleNames {
			entry, ok := registry.ByName(name)
			require.True(t, ok)
			rule := core.Prop(serve.EntryThm(env, entry))
			if name == "set_basic.Extension" {
				rule = core.PropTypeInst(rule, core.MakeTypeSubst(core.TypeA(), core.MakeFun(core.MakeVarType("C"), core.TypeBool())))
			}
			rules = append(rules, proof.Fwd(proof.MakeFact(rule)))
		}
		section := script.Section(goal)
		section.Do(proof.Simp(rules...))
		leaves := section.UnsolvedLeaves()
		require.Len(t, leaves, 1)
		for _, name := range []core.TermName{"exact_at", "group_kernel"} {
			require.False(t, termContainsConstNamed(leaves[0].Goal.Conclusion(), name), "%s", prop.PrintProp(leaves[0].Goal))
		}
		require.Equal(t, goal.NumHyps(), leaves[0].Goal.NumHyps())
		for _, hyp := range goal.Hyps() {
			require.True(t, leaves[0].Goal.HasHyp(hyp), "simplifying the conclusion must preserve the hypotheses")
		}
	})
	t.Run("session", func(t *testing.T) {
		e := newEngine(env)
		info, err := e.CreateSession(t.Context())
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		gid := s.AddGoal(goal)
		res, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
			Type: "simp_with", WithLemmas: []LemmaWithSpec{
				{Key: ruleNames[0]}, {Key: ruleNames[1], TypeSpecialize: map[string]string{"A": "set(C)"}}, {Key: ruleNames[2]},
			},
		}})
		require.NoError(t, err)
		require.True(t, res.Success, "%+v", res.Diagnostics)
		require.Zero(t, openLeavesMentioning(t, e, info.ID, "exact_at", "group_kernel"))
	})
}
