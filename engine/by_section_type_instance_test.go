package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// A text premise can cite a proved local section at an explicit type
// instance, including a swap inferred from its term witnesses.
func TestBy_SectionPremiseAtSwappedTypes(t *testing.T) {
	const statement = "∀P:(B → bool). ∀f:(A → B). ∀x:A. (∀y:B. P(y)) ⇒ P(f(x))"
	for _, name := range []string{"inferred", "explicit", "renamed sparse binder"} {
		explicit := name != "inferred"
		t.Run(name, func(t *testing.T) {
			e := newEngine(testEnv())
			info, err := e.CreateSession(context.Background())
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			script := proof.NewScript(s.env)
			lemma := script.Lemma(statement, func(a *proof.Argument, P, f, x proof.Term, all proof.Fact) {
				a.Show("Specialize the universal premise", proof.By(all))
			})
			s.sections = append(s.sections, &sectionState{root: lemma})
			parsed := dsl.ParsePropTextInScope("Q:(A → bool), g:(B → A), b:B, ∀a:A. Q(a) ⊢ Q(g(b))", &dsl.ParseScope{
				ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
			})
			require.Empty(t, parsed.Errors)
			gid := addStrippedGoal(t, e, info.ID, parsed.Prop)
			root := s.sections[1].root
			premise := LemmaWithSpec{Text: statement, TermSpecialize: map[string]string{"P": "Q", "f": "g", "x": "b"}}
			if explicit {
				premise.TypeSpecialize = map[string]string{"A": "B", "B": "A"}
			}
			if name == "renamed sparse binder" {
				premise.Text = "∀P:(B → bool). ∀f:(A → B). ∀z:A. (∀y:B. P(y)) ⇒ P(f(z))"
				premise.TermSpecialize = map[string]string{"z": "b"}
			}
			idx := 0
			out, err := e.ApplyStep(context.Background(), info.ID, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &idx}}, WithLemmas: []LemmaWithSpec{premise}},
			})
			require.NoError(t, err)
			require.True(t, out.Success, "diagnostics: %+v", out.Diagnostics)
			require.True(t, root.Proved())
			core.Force(t.Context(), root.PromisedThm())
			emitted, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 1, FuncName: "Build_Probe", Family: "sets/functions"})
			require.NoError(t, err)
			require.Equal(t, []int{0, 1}, emitted.SectionsIncluded)
			require.NotContains(t, emitted.Go, "TODO")
			if name == "renamed sparse binder" {
				require.Contains(t, emitted.Go, `Where(ctx.AtTypeVars(lemma1, TypeBinder.BindA[B](), TypeBinder.BindB[A]()), "x",`)
				require.NotContains(t, emitted.Go, `"z",`)
			}
		})
	}
}

// Existing normalized-equivalent text remains citable, while an open
// section cannot certify even a logically valid text premise.
func TestBy_SectionPremiseCertificationBoundary(t *testing.T) {
	const statement = "∀P:(B → bool). ∀f:(A → B). ∀x:A. (∀y:B. P(y)) ⇒ P(f(x))"
	const equivalent = "∀P:(B → bool). ∀f:(A → B). ∀x:A. ¬(∀y:B. P(y)) ∨ P(f(x))"
	for _, proved := range []bool{true, false} {
		name := "unproved"
		if proved {
			name = "equivalent surface"
		}
		t.Run(name, func(t *testing.T) {
			e := newEngine(testEnv())
			info, err := e.CreateSession(context.Background())
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			ctx := proof.NewScript(s.env)
			lemma := ctx.Lemma(statement, func(a *proof.Argument, P, f, x proof.Term, all proof.Fact) {
				a.Show("Specialize the premise", proof.By(all))
			})
			root := lemma
			if !proved {
				root = proof.CreateGoalStack(lemma.Goal)
			}
			s.sections = append(s.sections, &sectionState{root: root})
			parsed := dsl.ParsePropTextInScope("Q:(B → bool), g:(A → B), b:A, ∀y:B. Q(y) ⊢ Q(g(b))", &dsl.ParseScope{
				ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
			})
			require.Empty(t, parsed.Errors)
			gid := s.AddGoal(parsed.Prop)
			text := statement
			if proved {
				text = equivalent
			}
			idx := 0
			out, err := e.ApplyStep(context.Background(), info.ID, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &idx}}, WithLemmas: []LemmaWithSpec{{Text: text, TermSpecialize: map[string]string{"P": "Q", "f": "g", "x": "b"}}}},
			})
			require.NoError(t, err)
			if proved {
				require.True(t, out.Success, "diagnostics: %+v", out.Diagnostics)
				core.Force(t.Context(), s.sections[1].root.PromisedThm())
			} else {
				require.False(t, out.Success)
				require.Contains(t, out.Diagnostics[0].Message, "did not certify")
				require.False(t, s.sections[0].root.Proved())
			}
		})
	}
}
