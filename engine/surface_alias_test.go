// surface_alias_test.go — goal-local surface-name aliases for session
// claim/term texts (surface_alias.go).
//
// The mint-forcing decoy in these tests is a BOUND inner binder that
// reuses the surface name: stripping the outer ∀n must rename its
// variable away from every name in the goal — bound included — so the
// goal's free variable is the minted n₀ while the bare spelling `n`
// stays free for the alias.

package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestSurfaceAlias_ResidentBundleClaims(t *testing.T) {
	parsed := dsl.ParsePropTextInScope("∀P:chain_complex(A, B). ∀n:num. cycles(P, n) = boundaries(P, n)",
		&dsl.ParseScope{ConstResolver: registryConstResolver, Syntax: constSyntax(), FreshenMetaLetters: true})
	require.Empty(t, parsed.Errors)
	concl := parsed.Prop.Conclusion()
	var hyps []core.Term
	for {
		_, concl = ext.DecomposesFORALL(concl)
		premise, body, ok := ext.MatchesIMPLY(concl)
		if !ok {
			break
		}
		hyps = append(hyps, premise)
		concl = body
	}
	for _, keepSubject := range []bool{false, true} {
		t.Run(fmt.Sprint(keepSubject), func(t *testing.T) {
			var goal core.Prop = prop.MakeProp(concl, hyps...)
			vars := goalFreeVarTypes(goal)
			var renames []core.TermSubst
			for name, typ := range vars {
				if keepSubject && name == "P" {
					continue
				}
				renames = append(renames, core.MakeTermSubst(core.Var(core.TermName(name), typ), core.Var(core.TermName(name+"_0"), typ)))
			}
			goal = substituteParsedProp(goal, renames)
			for _, texts := range [][2]string{
				{"cycles(P, n) = boundaries(P, n)", "cycles(P₀, n₀) = boundaries(P₀, n₀)"},
				{"P.d(n)(P.zero) = P.zero", "P₀.d(n₀)(P₀.zero) = P₀.zero"},
			} {
				if keepSubject {
					texts[1] = strings.ReplaceAll(texts[1], "P₀", "P")
				}
				surface, err := parseClaimTextInGoalScope(texts[0], goal, nil)
				require.NoError(t, err, "%s", texts[0])
				minted, err := parseClaimTextInGoalScope(texts[1], goal, nil)
				require.NoError(t, err, "%s", texts[1])
				require.True(t, surface.AlphaEquals(minted), "surface and minted bundle spellings must denote the same claim")
			}
		})
	}

}

// TestGoalSurfaceAliases_Derivation: the alias environment is derived
// from the goal's frees — minted spellings alias their base, ambiguity
// and taken base names abstain.
func TestGoalSurfaceAliases_Derivation(t *testing.T) {
	A := core.TypeA()
	R := ext.Var("R", core.MakeFun(A, core.TypeBool()))
	n0 := ext.Var("n_0", A)
	n1 := ext.Var("n_1", A)
	n := ext.Var("n", A)

	// One mint, base free-name absent → alias n → n_0.
	g := prop.MakeProp(R.Apply(n0))
	aliases := goalSurfaceAliases(g)
	require.Len(t, aliases, 1)
	require.Equal(t, "n_0", string(aliases["n"].Name()))

	// Two mints share the base → abstain.
	g = prop.MakeProp(R.Apply(n0), R.Apply(n1))
	assert.Empty(t, goalSurfaceAliases(g))

	// The base itself is free → the real n owns the bare spelling.
	g = prop.MakeProp(R.Apply(n0), R.Apply(n))
	assert.Empty(t, goalSurfaceAliases(g))
}

// surfaceSessionGoal builds the shared session fixture:
//
//	∀n:A. (R(n) ∧ (∀n:bool. Q(n))) ⇒ R'(n)
//
// The inner bound n:bool forces the outer strip to mint n₀:A.
func surfaceSessionGoal() core.Prop {
	A := core.TypeA()
	R := ext.Var("R", core.MakeFun(A, core.TypeBool()))
	R2 := ext.Var("RR", core.MakeFun(A, core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeBool(), core.TypeBool()))
	n := ext.Var("n", A)
	nb := ext.Var("n", core.TypeBool())
	return prop.MakeProp(ext.ForAll(n)(
		R.Apply(n).And(ext.ForAll(nb)(Q.Apply(nb))).Imply(R2.Apply(n))))
}

// TestSurfaceAlias_SessionAssertClaim: after strip_quant, an assert
// claim may spell the statement binder's bare name; the inspect view
// advertises the alias.
func TestSurfaceAlias_SessionAssertClaim(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	goalID := s.AddGoal(surfaceSessionGoal())
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID, Tactic: TacticReq{Type: "strip_quant"},
	})
	require.NoError(t, err)
	require.True(t, res.Success)

	// The inspect view advertises the alias.
	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.Equal(t, 1, state.NumOpen)
	stripped := state.Goals[0]
	require.Contains(t, stripped.SurfaceNames, "n",
		"the stripped goal must advertise the surface alias")
	assert.NotEqual(t, "n", stripped.SurfaceNames["n"])

	// Locate the minted variable off the goal's frees.
	var minted core.VarTerm
	for _, v := range stripped.Statement.Conclusion().Frees(nil) {
		if v.Type().Equals(core.TypeA()) {
			minted = v
		}
	}
	require.False(t, minted.IsZero())
	require.NotEqual(t, "n", string(minted.Name()), "the strip must have renamed the binder")

	// Assert through the surface spelling; the claim child must carry
	// the MINTED instance.
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: stripped.ID, Tactic: TacticReq{Type: "assert", ClaimText: "R(n)"},
	})
	require.NoError(t, err)
	require.True(t, res.Success)
	want := R.Apply(minted).Core()
	found := false
	for _, g := range res.State.Goals {
		if g.Statement.Conclusion().Equals(want) {
			found = true
		}
	}
	assert.True(t, found, "the assert claim must resolve `n` to the minted variable")
}

// TestSurfaceAlias_SessionWitnessTerm: a witness term parameter may
// spell the bare surface name — the term path (resolveTermWithFallback)
// resolves it to the minted variable and the goal's frees guard passes.
func TestSurfaceAlias_SessionWitnessTerm(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// ∀n:A. (∀n:bool. Q(n)) ⇒ ∃j:A. j = n
	A := core.TypeA()
	Q := ext.Var("Q", core.MakeFun(core.TypeBool(), core.TypeBool()))
	n := ext.Var("n", A)
	nb := ext.Var("n", core.TypeBool())
	j := ext.Var("j", A)
	goal := prop.MakeProp(ext.ForAll(n)(
		ext.ForAll(nb)(Q.Apply(nb)).Imply(ext.Exists(j)(ext.Eq(j, n)))))

	goalID := s.AddGoal(goal)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID, Tactic: TacticReq{Type: "strip_quant"},
	})
	require.NoError(t, err)
	require.True(t, res.Success)
	require.Equal(t, 1, res.State.NumOpen)
	stripped := res.State.Goals[0]

	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: stripped.ID, Tactic: TacticReq{Type: "strip_imp"},
	})
	require.NoError(t, err)
	require.True(t, res.Success)
	afterImp := res.State.Goals[0]

	// Witness the ∃ through the surface spelling.
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: afterImp.ID, Tactic: TacticReq{Type: "witness", Const: "n"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "witness via the surface name must resolve to the minted variable")

	// The residual goal is n₀ = n₀ — a reflexive equality over the mint.
	require.Equal(t, 1, res.State.NumOpen)
	concl := res.State.Goals[0].Statement.Conclusion()
	lhs, rhs, ok := ext.MatchesEQ(concl)
	require.True(t, ok, "residual goal should be an equality, got %s", ext.PrintTerm(concl))
	assert.True(t, lhs.Equals(rhs), "witnessing with the surface name must produce the reflexive instance")
}
