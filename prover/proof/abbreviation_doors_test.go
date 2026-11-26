// abbreviation_doors_test.go — an abbreviation whose text is a λ,
// applied in a claim or a statement, reads as its body at the
// arguments (ext/dsl, astApp.reduced): the doors that read a binder off
// the claim — Obtain's ∃, Take's ∃ on the goal, At's ∀ on a resident
// fact — see the body's, and a leaf's plan key is the body's whatever
// order the abbreviation took its arguments in (cnf_store.go, planKey).
// Measured before: `«HasPP»(J)` as an Obtain claim was refused "only 0
// leading ∃-binder(s)", as a goal the Witness ministep failed on the
// redex, `«Motive»(v).At(w)` failed to ground, and «Without»(m, w) and
// «Delete»(w, m) for one body were two plans (#1510, #1530, #1542).
package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

func hasPointStatement(conclusion string) dsl.Statement {
	return dsl.Statement{
		Binders:    "∀J P:(num → bool). ∀v:num.",
		Hypotheses: []string{"J(v)", "P(v)"},
		Conclusion: conclusion,
		Abbrev:     dsl.Abbrev{{Name: "HasPP", Text: "λH:(num → bool). ∃x:num. H(x) ∧ P(x)"}},
	}
}

func TestAbbreviationDoors_ObtainOnAnAppliedAbbreviation(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(hasPointStatement("∃w:num. P(w)"),
			func(a *Argument, J, P *ext.Expr[natSet], v *ext.Expr[ext.Nat], jv, pv Fact) {
				w, spec := a.Obtain("J has a P-point", "«HasPP»(J)", By(jv, pv))
				a.Take(w)
				a.Show("the point", By(spec))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

func TestAbbreviationDoors_TakeOnAGoalHeadedByAnAppliedAbbreviation(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(hasPointStatement("«HasPP»(J)"),
			func(a *Argument, J, P *ext.Expr[natSet], v *ext.Expr[ext.Nat], jv, pv Fact) {
				a.Take(v)
				a.Show("the point", By(jv, pv))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	expanded := ctx.MakePropText("∀J P:(num → bool). ∀v:num. J(v) ∧ P(v) ⇒ ∃x:num. J(x) ∧ P(x)")
	require.True(t, sec.Goal.AlphaEquals(expanded), "the statement reads the abbreviation at J; got %s", PrintProp(sec.Goal))
}

func TestAbbreviationDoors_AtThroughAnAppliedAbbreviation(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	st := dsl.Statement{
		Binders:    "∀Q:(num → num → bool). ∀v w:num.",
		Hypotheses: []string{"∀x z:num. Q(x, z)"},
		Conclusion: "Q(v, w)",
		Abbrev:     dsl.Abbrev{{Name: "Motive", Text: "λx:num. ∀z:num. Q(x, z)"}},
	}
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(st, func(a *Argument, Q *ext.Expr[ext.Fun[ext.Nat, natSet]], v, w *ext.Expr[ext.Nat], all Fact) {
			m := a.Have("the motive at v", "«Motive»(v)", By(all))
			a.Show("at w", By(m.At(w)))
		})
	})
	require.True(t, sec != nil && sec.Proved())
}

// One body under two abbreviations that take their arguments in either
// order is one plan key.
func TestAbbreviationDoors_PlanKeyIsTheBodys(t *testing.T) {
	table, err := dsl.ParseAbbreviations(dsl.Abbrev{
		{Name: "Without", Text: "λm:num. λw:num. R(m) ∧ S(w)"},
		{Name: "Delete", Text: "λw:num. λm:num. R(m) ∧ S(w)"},
	})
	require.NoError(t, err)
	num := ext.NumType
	scope := &dsl.ParseScope{
		Vars: map[string]core.HolType{
			"R": core.MakeFun(num, core.TypeBool()),
			"S": core.MakeFun(num, core.TypeBool()),
			"m": num, "w": num, "Q": core.TypeBool(),
		},
		Abbreviations: table,
	}
	parse := func(text string) Prop {
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop
	}
	without, del := parse("«Without»(m, w) ⇒ Q"), parse("«Delete»(w, m) ⇒ Q")
	require.True(t, without.AlphaEquals(parse("R(m) ∧ S(w) ⇒ Q")), "the application reads as the body; got %s", PrintProp(without))
	require.Equal(t, planKey(without), planKey(del))
	// A redex the kernel makes is keyed by its reduction too.
	motive := dsl.ParseTermTextInScope("λm:num. R(m) ∧ S(w)", scope.Vars, scope, nil)
	require.Empty(t, motive.Errors)
	redex := core.MakeProp(core.Apply(motive.Term, core.Var("m", num)))
	require.Equal(t, planKey(parse("R(m) ∧ S(w)")), planKey(redex))
}
