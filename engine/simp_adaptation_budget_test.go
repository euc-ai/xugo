package engine

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// Each rewrite reveals the next constant at a type not mentioned in
// any previous target. Thus the final rule needs exactly rounds
// residual adaptation passes after the initial goal's enumeration.
// The constants come back too, for a test stating a further rule over
// the last one.
func simpAdaptationChainConsts(t *testing.T, rounds int) (*proof.ProverEnv, core.Prop, core.Term, []core.Prop, []LemmaWithSpec, []core.ConstTermMeta) {
	t.Helper()
	env := testEnv()
	var metas []core.ConstTermMeta
	for i := 0; i <= rounds+1; i++ {
		meta := core.MakeConstMeta(core.TermName(fmt.Sprintf("adaptChain%d", i)), core.MakeFun(core.TypeA(), core.TypeBool()))
		env.ProofService.LoadOrStoreConstMeta(meta)
		metas = append(metas, meta)
	}
	var rules []core.Prop
	var entries []LemmaWithSpec
	x := core.Var("x", core.TypeA())
	for i := 0; i <= rounds; i++ {
		lhs := core.Apply(core.MakeConstTerm(metas[i], core.MakeFun(core.TypeA(), core.TypeBool())), x)
		rhs := core.Apply(core.MakeConstTerm(metas[i+1], core.MakeFun(core.TypeA(), core.TypeBool())), x)
		rule := core.TestThm(ext.ForAll(x)(ext.Eq(lhs, rhs)).Core())
		rules = append(rules, rule)
		entries = append(entries, LemmaWithSpec{Key: fmt.Sprintf("adaptation.Chain%d", i)})
	}
	y := core.Var("y", TypeInd)
	at := func(i int) core.Term {
		return core.Apply(core.MakeConstTerm(metas[i], core.MakeFun(TypeInd, core.TypeBool())), y)
	}
	return env, core.MakeProp(at(0)), at(rounds + 1), rules, entries, metas
}

func simpAdaptationChain(t *testing.T, rounds int) (*proof.ProverEnv, core.Prop, core.Term, []core.Prop, []LemmaWithSpec) {
	t.Helper()
	env, goal, want, rules, entries, _ := simpAdaptationChainConsts(t, rounds)
	return env, goal, want, rules, entries
}

// The session cites the same constants and rules as Go through card
// entries. A text fixture would parse later, not-yet-visible heads as
// free functions because these test constants are outside the corpus.
func installSimpAdaptationCards(s *Session, rules []core.Prop, entries []LemmaWithSpec) {
	if s.cards == nil {
		s.cards = map[string]*sessionCard{}
	}
	for i, rule := range rules {
		s.cards[entries[i].Key] = &sessionCard{key: rule.AlphaKey(), statement: rule.AsProp(), entry: entries[i].Key, axiom: core.AsThm(rule).AsThmCert()}
	}
}

// recoveredPanic runs f, which must panic, and returns the panic's text.
func recoveredPanic(t *testing.T, f func()) (message string) {
	t.Helper()
	defer func() {
		r := recover()
		require.NotNil(t, r, "no panic")
		message = fmt.Sprint(r)
	}()
	f()
	return ""
}

// A chain as deep as the bound adapts to its end; one deeper is refused
// at the bound, naming the rule the last round exposed, the instance,
// and the spelling that pins it, with nothing committed. The session
// surfaces every round's instance diagnostics beside the refusal.
func TestSimp_AdaptationRoundBudget(t *testing.T) {
	for _, rounds := range []int{proof.MaxSimpAdaptRounds, proof.MaxSimpAdaptRounds + 1} {
		t.Run(fmt.Sprint(rounds), func(t *testing.T) {
			env, goal, want, rules, entries := simpAdaptationChain(t, rounds)
			// The chain's last rule, exposed at ind by the round past
			// the bound.
			exposed := fmt.Sprintf("adaptChain%d", rounds)
			t.Run("Go", func(t *testing.T) {
				script := proof.NewScript(env)
				section := script.Section(goal)
				var marked []proof.SimpRule
				for _, rule := range rules {
					marked = append(marked, proof.Fwd(proof.MakeFact(rule)))
				}
				if rounds > proof.MaxSimpAdaptRounds {
					message := recoveredPanic(t, func() { section.Do(proof.Simp(marked...)) })
					require.Contains(t, message, fmt.Sprintf("Simp: the rewrite keeps exposing rule instances that rewrite further, %d residual rounds deep", proof.MaxSimpAdaptRounds))
					require.Contains(t, message, fmt.Sprintf("rule %d is polymorphic", rounds+1))
					require.Contains(t, message, exposed)
					require.Contains(t, message, "A := ind")
					require.Contains(t, message, "Inst[τ]")
					require.True(t, section.UnsolvedLeaves()[0].Goal.AlphaEquals(goal), "nothing is committed on the refusal")
					return
				}
				section.Do(proof.Simp(marked...))
				require.Len(t, section.UnsolvedLeaves(), 1)
				require.True(t, section.UnsolvedLeaves()[0].Goal.Conclusion().AlphaEquals(want))
			})
			t.Run("session", func(t *testing.T) {
				e := newEngine(env)
				info, err := e.CreateSession(t.Context())
				require.NoError(t, err)
				s, err := e.getSession(info.ID)
				require.NoError(t, err)
				installSimpAdaptationCards(s, rules, entries)
				gid := s.AddGoal(goal)
				out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "simp_with", WithLemmas: entries}})
				require.NoError(t, err)
				var failures, exposures []string
				for _, d := range out.Diagnostics {
					switch d.Type {
					case DiagTacticFailure:
						failures = append(failures, d.Message)
					case DiagAutoTypeInstances:
						exposures = append(exposures, d.Message)
					}
				}
				// One instance diagnostic per residual round, the
				// refusing round's among them.
				require.Len(t, exposures, rounds, "%+v", out.Diagnostics)
				state, err := e.InspectState(t.Context(), info.ID)
				require.NoError(t, err)
				if rounds > proof.MaxSimpAdaptRounds {
					require.False(t, out.Success)
					require.Len(t, failures, 1, "%+v", out.Diagnostics)
					require.Contains(t, failures[0], fmt.Sprintf("the rewrite keeps exposing rule instances that rewrite further, %d residual rounds deep", proof.MaxSimpAdaptRounds))
					require.Contains(t, failures[0], fmt.Sprintf("rule #%d (key %s)", rounds, entries[rounds].Key))
					require.Contains(t, failures[0], exposed)
					require.Contains(t, failures[0], "type_specialize")
					require.Len(t, state.Goals, 1)
					require.True(t, state.Goals[0].Statement.AlphaEquals(goal), "nothing is committed on the refusal")
					return
				}
				require.True(t, out.Success, "%+v", out.Diagnostics)
				require.Empty(t, failures)
				found := false
				for _, g := range state.Goals {
					found = found || g.Statement.Conclusion().AlphaEquals(want)
				}
				require.True(t, found)
			})
		})
	}
}

// A copy added at the bound with no redex in the residual is inert: the
// next residual would be the same, so the set is complete and the step
// proceeds. The rule's anchor is the constant the chain's last rule
// exposes, so its copy at ind arrives exactly at the bound.
func TestSimp_InertCopyAtTheRoundBound(t *testing.T) {
	env, goal, want, rules, entries, metas := simpAdaptationChainConsts(t, proof.MaxSimpAdaptRounds)
	h := core.MakeConstMeta("adaptInertH", core.MakeFun(core.TypeA(), core.TypeBool()))
	k := core.MakeConstMeta("adaptInertK", core.MakeFun(core.TypeBool(), core.TypeBool()))
	env.ProofService.LoadOrStoreConstMeta(h)
	env.ProofService.LoadOrStoreConstMeta(k)
	x := core.Var("x", core.TypeA())
	last := core.Apply(core.MakeConstTerm(metas[len(metas)-1], core.MakeFun(core.TypeA(), core.TypeBool())), x)
	inert := core.TestThm(ext.ForAll(x)(ext.Eq(
		core.Apply(core.MakeConstTerm(h, core.MakeFun(core.TypeA(), core.TypeBool())), x),
		core.Apply(core.MakeConstTerm(k, core.MakeFun(core.TypeBool(), core.TypeBool())), last))).Core())
	rules = append(rules, inert)
	entries = append(entries, LemmaWithSpec{Key: "adaptation.Inert"})
	t.Run("Go", func(t *testing.T) {
		section := proof.NewScript(env).Section(goal)
		var marked []proof.SimpRule
		for _, rule := range rules {
			marked = append(marked, proof.Fwd(proof.MakeFact(rule)))
		}
		section.Do(proof.Simp(marked...))
		require.Len(t, section.UnsolvedLeaves(), 1)
		require.True(t, section.UnsolvedLeaves()[0].Goal.Conclusion().AlphaEquals(want))
	})
	t.Run("session", func(t *testing.T) {
		e := newEngine(env)
		info, err := e.CreateSession(t.Context())
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		installSimpAdaptationCards(s, rules, entries)
		gid := s.AddGoal(goal)
		out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "simp_with", WithLemmas: entries}})
		require.NoError(t, err)
		require.True(t, out.Success, "%+v", out.Diagnostics)
		state, err := e.InspectState(t.Context(), info.ID)
		require.NoError(t, err)
		found := false
		for _, g := range state.Goals {
			found = found || g.Statement.Conclusion().AlphaEquals(want)
		}
		require.True(t, found)
	})
}

func TestSimp_HypothesisResidualAdaptation(t *testing.T) {
	for _, verb := range []string{"simp", "simp_with", "simp_all"} {
		t.Run(verb, func(t *testing.T) {
			env, target, want, rules, entries := simpAdaptationChain(t, 2)
			concl := core.Var("unrelated", core.TypeBool())
			goal := core.MakeProp(concl, target.Conclusion())
			e := newEngine(env)
			info, err := e.CreateSession(t.Context())
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			installSimpAdaptationCards(s, rules, entries)
			if verb != "simp_with" {
				for _, rule := range rules {
					s.simpRules = append(s.simpRules, sessionSimpRule{rule: rule, cert: core.AsThm(rule)})
				}
			}
			gid := s.AddGoal(goal)
			hyp := 0
			req := TacticReq{Type: verb, HypIndex: &hyp}
			if verb == "simp_all" {
				req.HypIndex = nil
			}
			if verb == "simp_with" {
				req.WithLemmas = entries
			}
			out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: req})
			require.NoError(t, err)
			require.True(t, out.Success, "%+v", out.Diagnostics)
			state, err := e.InspectState(t.Context(), info.ID)
			require.NoError(t, err)
			found := false
			for _, g := range state.Goals {
				if g.Statement.Conclusion().AlphaEquals(concl) {
					found = g.Statement.HasHyp(want)
				}
			}
			require.True(t, found, "the selected hypothesis must reach the final instance")
		})
	}
}

// A closure rule can be necessary without rewriting the target by
// itself. Its adapted instance must accompany the conditional rule,
// and neither may invent the missing guard in the negative control.
func TestSimp_ConditionalClosureInstances(t *testing.T) {
	for _, guarded := range []bool{true, false} {
		t.Run(fmt.Sprint(guarded), func(t *testing.T) {
			env := testEnv()
			for _, name := range []string{"adaptConditionalF", "adaptConditionalG", "adaptConditionalP"} {
				result := core.HolType(core.TypeA())
				if name == "adaptConditionalP" {
					result = core.TypeBool()
				}
				env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta(core.TermName(name), core.MakeFun(core.TypeA(), result)))
			}
			scope := &dsl.ParseScope{ConstResolver: envConstResolver(env), StrictResolution: true, FreshenMetaLetters: true}
			parse := func(text string) core.Prop {
				parsed := dsl.ParsePropTextInScope(text, scope)
				require.Empty(t, parsed.Errors)
				return parsed.Prop
			}
			rules := []core.Prop{
				core.TestThm(parse("∀x:A. adaptConditionalP(x) ⇒ adaptConditionalF(x) = x").Conclusion()),
				core.TestThm(parse("∀x:A. adaptConditionalP(x) ⇒ adaptConditionalP(adaptConditionalG(x))").Conclusion()),
			}
			text := "q:B→bool, a:B"
			if guarded {
				text += ", adaptConditionalP(a)"
			}
			goal := parse(text + " ⊢ q(adaptConditionalF(adaptConditionalG(a)))")
			want := parse("q:B→bool, a:B ⊢ q(adaptConditionalG(a))").Conclusion()
			t.Run("Go", func(t *testing.T) {
				section := proof.NewScript(env).Section(goal)
				run := func() {
					section.Do(proof.Simp(proof.Fwd(proof.MakeFact(rules[0])), proof.Fwd(proof.MakeFact(rules[1]))))
				}
				if !guarded {
					require.Panics(t, run)
					require.True(t, section.UnsolvedLeaves()[0].Goal.AlphaEquals(goal))
					return
				}
				run()
				require.Len(t, section.UnsolvedLeaves(), 1)
				require.True(t, section.UnsolvedLeaves()[0].Goal.Conclusion().AlphaEquals(want))
			})
			t.Run("session", func(t *testing.T) {
				e := newEngine(env)
				info, err := e.CreateSession(t.Context())
				require.NoError(t, err)
				s, err := e.getSession(info.ID)
				require.NoError(t, err)
				for _, rule := range rules {
					s.simpRules = append(s.simpRules, sessionSimpRule{rule: rule, cert: core.AsThm(rule)})
				}
				gid := s.AddGoal(goal)
				out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "simp"}})
				if !guarded {
					if err == nil {
						require.False(t, out.Success)
					}
				} else {
					require.NoError(t, err)
					require.True(t, out.Success, "%+v", out.Diagnostics)
				}
				state, err := e.InspectState(t.Context(), info.ID)
				require.NoError(t, err)
				require.Len(t, state.Goals, 1)
				if guarded {
					require.True(t, state.Goals[0].Statement.Conclusion().AlphaEquals(want))
				} else {
					require.True(t, state.Goals[0].Statement.AlphaEquals(goal))
				}
			})
		})
	}
}
