package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestByArith_CoefficientIsReadAtThePremisesCarrier: the coefficient of
// a scaled premise is read at the type of the equation it scales. A
// cast written `&q` beside an equation over ℤ is the integer the goal
// prints as `&q₀`, and beside one over ℝ the real. A coefficient of
// another carrier is refused where it is read, naming the type the
// premise asks for.
func TestByArith_CoefficientIsReadAtThePremisesCarrier(t *testing.T) {
	e := byArithEngine(t)
	ctx := context.Background()
	idx := func(i int) *int { return &i }
	open := func(t *testing.T, stmt string) (sid, gid string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
			ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors, "add-goal %q", stmt)
		s.mu.Lock()
		gid = s.AddGoal(parsed.Prop)
		s.mu.Unlock()
		for _, typ := range []string{"strip_quant", "strip_imp"} {
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
			require.NoError(t, err)
			require.Len(t, res.Produced, 1)
			gid = res.Produced[0].GoalID
		}
		return info.ID, gid
	}
	scaled := func(sid, gid, coefficient string) (*StepResult, error) {
		return e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid,
			Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: idx(0), Coefficient: coefficient}}}})
	}

	rows := []struct {
		name, stmt   string
		coefficients []string
	}{
		{"a cast over ℤ",
			"∀q:num. ∀p r u v:int. p + r = u * v ⇒ (p + r) * int_of_num(q) = u * v * int_of_num(q)",
			[]string{"&q", "int_of_num(q)"}},
		{"a numeral over ℤ",
			"∀p r u v w:int. p + r = u * v ⇒ (p + r) * (w + int_of_num(2)) = u * v * (w + int_of_num(2))",
			[]string{"w + &2", "w + int_of_num(2)"}},
		{"a cast over ℝ",
			"∀q:num. ∀p r u v:real. p + r = u * v ⇒ (p + r) * &q = u * v * &q",
			[]string{"&q", "real_of_num(q)"}},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			sid, gid := open(t, r.stmt)
			// The equation defines no variable, so the close needs its
			// coefficient.
			bare, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid,
				Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: idx(0)}}}})
			require.True(t, err != nil || bare.Effect != "close", "closed without the coefficient")
			for _, c := range r.coefficients {
				sid, gid := open(t, r.stmt)
				res, err := scaled(sid, gid, c)
				require.NoError(t, err, "coefficient %q", c)
				require.Equal(t, "close", res.Effect, "coefficient %q did not close", c)
			}
		})
	}

	t.Run("a coefficient of another carrier is refused where it is read", func(t *testing.T) {
		sid, gid := open(t, "∀x:real. ∀p r u v:int. p + r = u * v ⇒ x = x ⇒ (p + r) * u = u * v * u")
		res, err := scaled(sid, gid, "x")
		require.NoError(t, err)
		require.NotEqual(t, "close", res.Effect)
		require.NotEmpty(t, res.Diagnostics)
		require.Contains(t, res.Diagnostics[0].Message, "coefficient, read at int")
		require.Contains(t, res.Diagnostics[0].Message, "term has type real but expected int")
	})
}
