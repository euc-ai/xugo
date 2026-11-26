// apply_close_eta_test.go — the apply rung's head match identifies a
// term and its η-expansion, as its antecedent check does
// (residentModuloBetaEta): the rung's identity is βη on both sides of
// the match. Measured: a cite of category.FunctorFromHomIff with the
// witnesses `H := λT S. continuous_hom_set(T, S)`, `F := λT. ⋃T` at a
// goal `def_expand` left η-reduced (`mk_functor(big_union, …)`) fell to
// the refuter, where the η-reduced witnesses reached the rung
// (topology_category.TopologyForgetful); a grounded reading whose
// record part computes to `λr x. r * x` never met a claim spelling
// `mul` (serre_duality.DualizingIsLattice).
package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// etaTestScope is a parse scope with the constants the tests below
// state: a predicate zz_eta_q on functions, a packer zz_eta_mk of a
// function into a number, a predicate zz_eta_p on numbers, and a
// two-place predicate zz_eta_p2 on a function and a number.
func etaTestScope() (*dsl.ParseScope, core.HolType) {
	numFn := core.MakeFun(ext.NumType, ext.NumType)
	return &dsl.ParseScope{
		Vars: map[string]core.HolType{"g": numFn, "x": ext.NumType},
		ConstMetas: map[string]core.ConstTermMeta{
			"zz_eta_q":  core.MakeConstMeta("zz_eta_q", core.MakeFun(numFn, core.TypeBool())),
			"zz_eta_mk": core.MakeConstMeta("zz_eta_mk", core.MakeFun(numFn, ext.NumType)),
			"zz_eta_p":  core.MakeConstMeta("zz_eta_p", core.MakeFun(ext.NumType, core.TypeBool())),
			"zz_eta_p2": core.MakeConstMeta("zz_eta_p2", core.MakeFun(numFn, core.MakeFun(ext.NumType, core.TypeBool()))),
			"zz_eta_q2": core.MakeConstMeta("zz_eta_q2", core.MakeFun(ext.NumType, core.TypeBool())),
		},
	}, numFn
}

func parseEtaProp(t *testing.T, scope *dsl.ParseScope, text string) core.Term {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, scope)
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	return res.Prop.Conclusion()
}

// A stated head pinned by name at an η-expanded witness, `F := λx. g(x)`,
// applies to the goal spelled with the bare `g` — the #1448 shape: the
// author's λ against a goal `def_expand` η-reduced. The η-reduced
// witness is the control: it reached the rung before this test.
func TestApplyStatedHead_SeededWitnessUpToEta(t *testing.T) {
	scope, numFn := etaTestScope()
	parse := func(text string) core.Term { return parseEtaProp(t, scope, text) }
	law := prop.MakeProp(parse("∀F:(num → num). zz_eta_q(F) ⇒ zz_eta_p(zz_eta_mk(F))"))
	goal := prop.MakeProp(parse("zz_eta_p(zz_eta_mk(g))"), parse("zz_eta_q(g)"))
	g := ext.Var("g", numFn)
	x := core.Var("x", ext.NumType)
	for name, witness := range map[string]core.Term{
		"η-reduced":  g.Core(),
		"η-expanded": ext.Abs(x, ext.Apply(g, ext.WrapTerm(x)).Core()).Core(),
	} {
		t.Run(name, func(t *testing.T) {
			sec := NewScript(makeStepTestEnv()).Section(goal)
			hd := applyHead{stated: law, describe: "the law", named: []NamedWitness{{Binder: "F", Witness: witness}}}
			var claims []*GoalStackNode
			ok, miss := applyStatedHead(sec, &claims, sec, hd, rungOpts{depth: antecedentApplies})
			require.True(t, ok, "the seeded head at %s: %s", ext.PrintTerm(witness), miss)
			require.Empty(t, byWorkingLeaves(sec, claims), "closed up to the head's claim")
		})
	}
}

// A resident law whose conclusion spells an abstraction, `zz_eta_p2(λy.
// g(y), x)` — what a grounded reading hands over when a record part is
// a λ — applies to the goal spelled with the constant, and the other way
// round: the η-pair is one statement to the rung whichever side spells
// the λ (the #1452 shape).
func TestApplyClose_ResidentHeadUpToEta(t *testing.T) {
	scope, _ := etaTestScope()
	parse := func(text string) core.Term { return parseEtaProp(t, scope, text) }
	for name, c := range map[string]struct{ head, goal string }{
		"the head spells the λ":     {"∀x:num. zz_eta_q2(x) ⇒ zz_eta_p2(λy:num. g(y), x)", "zz_eta_p2(g, x)"},
		"the goal spells the λ":     {"∀x:num. zz_eta_q2(x) ⇒ zz_eta_p2(g, x)", "zz_eta_p2(λy:num. g(y), x)"},
		"neither spells the λ":      {"∀x:num. zz_eta_q2(x) ⇒ zz_eta_p2(g, x)", "zz_eta_p2(g, x)"},
		"the λ is another function": {"∀x:num. zz_eta_q2(x) ⇒ zz_eta_p2(λy:num. g(g(y)), x)", "zz_eta_p2(g, x)"},
	} {
		t.Run(name, func(t *testing.T) {
			goal := prop.MakeProp(parse(c.goal), parse(c.head), parse("zz_eta_q2(x)"))
			sec := NewScript(makeStepTestEnv()).Section(goal)
			var claims []*GoalStackNode
			closed, diag := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
			if name == "the λ is another function" {
				require.False(t, closed, "a different function is no η-variant")
				return
			}
			require.True(t, closed, "the resident head: %s", diag)
			require.True(t, sec.Proved(), "the leaf is closed")
		})
	}
}
