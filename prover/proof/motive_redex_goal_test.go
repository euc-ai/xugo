// motive_redex_goal_test.go — a By leaf whose goal is a resident law
// up to β: the goal spells a predicate abbreviation applied at the
// variable it quantifies, `∀E. fin(E) ⇒ «Motive»(E)` with «Motive» a λ,
// and the context holds the same law β-reduced, `∀s. fin(s) ⇒ body(s)`
// — the conclusion a cited induction principle hands its terminal By
// (ByInduction reads its obligations and its conclusion β-collapsed,
// and the author's goal names the predicate). Such a leaf closes by
// assumption before the conditioning stage strips it: stripped, it is a
// redex no resident law matches. The second test holds the stage sound
// where grounding instantiates the law at a set and at its η-expansion.
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// motiveRedexScope is the vocabulary of the tests below: a predicate
// fin on sets of numbers, a relation R between a function and a set, a
// relation K between a function and a number, a predicate P on
// numbers, a function g from numbers to sets, a function h, and the
// set-builder's constants.
func motiveRedexScope() *dsl.ParseScope {
	num := ext.NumType
	set := core.MakeFun(num, core.TypeBool())
	fn := core.MakeFun(num, num)
	return &dsl.ParseScope{
		Vars: map[string]core.HolType{
			"fin": core.MakeFun(set, core.TypeBool()),
			"R":   core.MakeFun(fn, core.MakeFun(set, core.TypeBool())),
			"K":   core.MakeFun(fn, core.MakeFun(num, core.TypeBool())),
			"P":   core.MakeFun(num, core.TypeBool()),
			"g":   core.MakeFun(num, set),
			"h":   fn,
		},
		ConstMetas: setBuilderVocabulary(),
	}
}

func parseMotiveRedex(t *testing.T, text string) core.Term {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, motiveRedexScope())
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	return res.Prop.Conclusion()
}

// A goal resident up to β is closed by the apply rung by assumption,
// before any strip: stripped, its conclusion is the redex alone, which
// no resident law matches. The β-reduced spelling is the control; it
// is resident as written. The ⇒-headed motive is closed by the same
// test only where the motive spells a membership in a set-builder: the
// membership reading β-collapses the leaf it reads, so the head of the
// motive's body is not what decides the close.
func TestConditionLeaf_GoalResidentUpToBetaClosesBeforeTheStrips(t *testing.T) {
	const (
		forallBody     = "∀u:(num → num). R(u, E) ⇒ ∃q:num. K(u, q)"
		impliesBody    = "(∀m:num. m ∈ E ⇒ P(m)) ⇒ ∀u:(num → num). R(u, E) ⇒ ∃q:num. K(u, q)"
		membershipBody = "(∀m:num. m ∈ E ⇒ m ∈ {x:num | P(x)}) ⇒ ∀u:(num → num). R(u, E) ⇒ ∃q:num. K(u, q)"
	)
	law := func(body string) string { return "∀E:set(num). fin(E) ⇒ " + body }
	applied := func(body string) string {
		return "∀E:set(num). fin(E) ⇒ (λE:set(num). " + body + ")(E)"
	}
	for name, c := range map[string]struct{ goal, law string }{
		"∀-headed motive applied":               {applied(forallBody), law(forallBody)},
		"⇒-headed motive applied":               {applied(impliesBody), law(impliesBody)},
		"⇒-headed motive spelling a membership": {applied(membershipBody), law(membershipBody)},
		"β-reduced goal (control)":              {law(forallBody), law(forallBody)},
		"β-reduced ⇒-headed goal (control)":     {law(impliesBody), law(impliesBody)},
	} {
		t.Run(name, func(t *testing.T) {
			goal := prop.MakeProp(parseMotiveRedex(t, c.goal), parseMotiveRedex(t, c.law))
			root := CreateGoalStack(goal)
			cond := &conditioner{env: makeStepTestEnv(), ctx: t.Context(), s4: &byS4State{}}
			cond.conditionLeaf(root, conditionOpts{applyClose: true})
			require.True(t, root.Proved(), "the apply rung closes the leaf by assumption; left open:\n%s",
				openLeaves(root))
		})
	}
}

// The whole stage over the same leaf, beside two facts that spell a
// set and its η-expansion — the stage the By executor runs live. The
// leaf closes, and the stage raises nothing: a stripped leaf goes on
// to the grounding, which instantiates the resident law at both sets
// of the η-pair, and to the denote of the motive the instances repeat,
// whose reconstruction must still be one of the goal (the denote's own
// contract over η-variant hypotheses is held in prover/tactic,
// denote_eta_sibling_test.go). The By's ladder takes a panic in the
// stage for a failed rung, so the stage is asked here directly.
func TestConditionLeaf_MotiveRedexBesideAnEtaPairCloses(t *testing.T) {
	law := parseMotiveRedex(t, "∀s:set(num). fin(s) ⇒ ∀u:(num → num). R(u, s) ⇒ ∃q:num. K(u, q)")
	goalConcl := parseMotiveRedex(t, "∀E:set(num). fin(E) ⇒ (λE:set(num). ∀u:(num → num). R(u, E) ⇒ ∃q:num. K(u, q))(E)")
	pair := []core.Term{parseMotiveRedex(t, "R(h, g(0))"), parseMotiveRedex(t, "R(h, λq:num. g(0, q))")}
	goal := prop.MakeProp(goalConcl, append([]core.Term{law}, pair...)...)

	env := groundTestEnv(t)
	newGroundByStore().wire(env, true)
	root := CreateGoalStack(goal)
	cond := &conditioner{env: env, ctx: t.Context(), s4: &byS4State{}}
	require.NotPanics(t, func() {
		cond.conditionLeaf(root, conditionOpts{ground: true, denote: true, applyClose: true})
	})
	require.True(t, root.Proved(), "left open:\n%s", openLeaves(root))
}

// openLeaves prints the leaves a test left open.
func openLeaves(root *GoalStackNode) string {
	out := ""
	for _, l := range byWorkingLeaves(root, nil) {
		out += prop.PrintProp(l.Goal) + "\n"
	}
	return out
}
