package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// The gauss-sum bridge reads identically through the session's production
// statement and term scopes, including the overloaded natural remainder.
func TestImplicitInt_GaussSumBridge(t *testing.T) {
	byArithEngine(t)
	scope := StatementDoorScope(nil)
	prefix := "∀a k p:num. "
	short := dsl.ParsePropTextInScope(prefix+"rem(a * k, p) ≡ &a * k (mod &p)", scope)
	long := dsl.ParsePropTextInScope(prefix+"int_of_num(rem(a * k, p)) ≡ int_of_num(a) * int_of_num(k) (mod int_of_num(p))", scope)
	require.Empty(t, short.Errors)
	require.Empty(t, long.Errors)
	require.True(t, short.Prop.AlphaEquals(long.Prop))

	vars := map[string]core.HolType{"a": dsl.NumType, "k": dsl.NumType, "p": dsl.NumType}
	for _, tc := range []struct{ short, long string }{
		{"a * k", "int_of_num(a * k)"},
		{"a - k", "int_of_num(a - k)"},
		{"&a * k", "int_of_num(a) * int_of_num(k)"},
		{"rem(a * k, p)", "int_of_num(rem(a * k, p))"},
		{"legendre_symbol(a, p)", "legendre_symbol(int_of_num(a), p)"},
	} {
		got := dsl.ParseTermTextInScope(tc.short, vars, scope, dsl.IntType)
		want := dsl.ParseTermTextInScope(tc.long, vars, scope, dsl.IntType)
		require.Empty(t, got.Errors, tc.short)
		require.Empty(t, want.Errors, tc.long)
		require.True(t, got.Term.AlphaEquals(want.Term), tc.short)
	}
}

// A session reads an `&` nothing anchors under the domain of the family
// it is bound to, at the claim door as the family's Go reads it: the
// text `&0 < &n` is one claim in both. Bound to no family, the session
// refuses it, as a chapter declaring no domain does.
func TestSession_ReadsTheFamilysCoercionDomain(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	leaf := func(family string) (*Session, string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		if family != "" {
			_, err = e.SetSessionFamily(info.ID, family, nil)
			require.NoError(t, err)
		}
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		parsed := dsl.ParsePropTextInScope("∀n:num. 0 < n ⇒ real_of_num(0) ≤ real_of_num(n)", &dsl.ParseScope{
			ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors)
		s.mu.Lock()
		gid := s.AddGoal(parsed.Prop)
		s.mu.Unlock()
		for _, typ := range []string{"strip_quant", "strip_imp"} {
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
			require.NoError(t, err, typ)
			require.Len(t, res.Produced, 1, typ)
			gid = res.Produced[0].GoalID
		}
		return s, gid
	}
	const claim, longhand = "&0 < &n", "real_of_num(0) < real_of_num(n)"

	for _, family := range []string{"real/real_derivative", "real/real_sequences"} {
		s, gid := leaf(family)
		require.NotNil(t, s.CoerceDomain(), family)
		entry, _, err := e.resolveFocusedGoal(s, gid)
		require.NoError(t, err)
		goal := entry.node.Goal
		short, err := parseClaimTextInGoalScope(claim, goal, s.familyScope())
		require.NoError(t, err, "%s: the claim door reads the family's domain", family)
		long, err := parseClaimTextInGoalScope(longhand, goal, s.familyScope())
		require.NoError(t, err)
		require.True(t, short.AlphaEquals(long), "%s: one claim, two spellings", family)

		res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "assert", ClaimText: claim}})
		require.NoError(t, err)
		require.True(t, res.Success, "%s: diagnostics: %+v", family, res.Diagnostics)
	}

	s, gid := leaf("")
	require.Nil(t, s.CoerceDomain())
	res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "assert", ClaimText: claim}})
	if err == nil {
		require.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		require.Contains(t, res.Diagnostics[0].Message, "unanchored")
	} else {
		require.Contains(t, err.Error(), "unanchored")
	}
}

// A proof opened without a family may land in a real chapter. Its
// intermediate claim is printed with the destination's real numerals.
func TestEmitSection_ReadsDestinationCoercionDomain(t *testing.T) {
	e := byArithEngine(t)
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀x:real. x ≤ x + real_of_num(2)")
	applyInEmitSection(t, e, s.ID, 0, TacticReq{Type: "strip_quant"})
	applyInEmitSection(t, e, s.ID, 0, TacticReq{Type: "assert", ClaimText: "real_of_num(0) ≤ real_of_num(2)"})
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	for _, g := range state.Goals {
		r, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		require.True(t, r.Success, "%+v", r.Diagnostics)
	}
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Family: "iterate/real/real_sum"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	require.Contains(t, out.Go, "&0 ≤ &2")
}

// A claim that states a relation between `&` numerals alone is read at
// the type the session's domain gives it, which the claim's echo cannot
// show, so the step says it: bound to a family that declares ℂ, the
// assert `&2 ≠ &0` is a statement about reals, and the step's
// numeral_domain diagnostic says real, says what decided it, and names
// the lift that states it at ℂ. The same claim with one side lifted is
// about complex numbers and carries no such diagnostic.
func TestSession_SaysWhereAClaimsNumeralsAreRead(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	numeral := func(claim string) []string {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		_, err = e.SetSessionFamily(info.ID, "complex/complex_exp", nil)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		parsed := dsl.ParsePropTextInScope("∀n:num. 0 < n ⇒ real_of_num(0) ≤ real_of_num(n)", &dsl.ParseScope{
			ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors)
		s.mu.Lock()
		gid := s.AddGoal(parsed.Prop)
		s.mu.Unlock()
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "assert", ClaimText: claim}})
		require.NoError(t, err)
		require.True(t, res.Success, "%s: %+v", claim, res.Diagnostics)
		var said []string
		for _, d := range res.Diagnostics {
			if d.Type == DiagNumeralDomain {
				said = append(said, d.Message)
			}
		}
		return said
	}
	said := numeral("&2 ≠ &0")
	require.Len(t, said, 1)
	require.Contains(t, said[0], "in `&2 ≠ &0`: the relation `≠` at position")
	require.Contains(t, said[0], "stands between numerals alone and is read at real")
	require.Contains(t, said[0], "the scope's `&` domain is complex")
	require.Contains(t, said[0], "to state it at complex, lift one side, `complex_of_real(&…)`")

	require.Empty(t, numeral("complex_of_real(&2) ≠ &0"), "one side names the type")
}
