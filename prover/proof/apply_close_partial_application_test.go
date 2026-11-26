// apply_close_partial_application_test.go — a law stated for an arbitrary
// operation applies where the goal's operation is a PARTIAL APPLICATION
// of a constant: the head `add(x, y) = add(y, x)` reads `vec_add(add₀, u,
// v) = vec_add(add₀, v, u)` at add := vec_add(add₀), the first-order
// approximation that binds a flexible head to the target's head applied
// to the arguments the pattern does not spell. Measured at equal arity:
// the polynomials' addition `vec_add(add)` matched no head whose
// operation is a binder, and a bare structure-law cite that is keyless
// where the operation is the ring's own `add` (module.RegularModuleOn)
// cost a key and a plan at the polynomial module
// (polynomial.PolynomialModuleOn, "addition commutes"), whatever the
// carrier.
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// The law at its own letter A, the goal at num → A with the operation
// zz_vadd(add) — vec_add's shape — at a comprehension carrier and at a
// variable one alike.
func TestApplyStatedHead_OperationBinderAtAPartialApplication(t *testing.T) {
	A := core.TypeA()
	vecT := core.MakeFun(ext.NumType, A)
	opT := func(T core.HolType) core.HolType { return core.MakeFun(T, core.MakeFun(T, T)) }
	setT := func(T core.HolType) core.HolType { return core.MakeFun(T, core.TypeBool()) }
	S := core.MakeConstMeta("zz_partial_s", core.MakeFun(opT(A), core.MakeFun(setT(A), core.TypeBool())))
	vadd := core.MakeConstMeta("zz_vadd", core.MakeFun(opT(A), opT(vecT)))
	scope := &dsl.ParseScope{
		Vars: map[string]core.HolType{
			"P": core.MakeFun(vecT, core.TypeBool()), "u": vecT, "v": vecT, "add": opT(A), "c": setT(vecT),
		},
		ConstMetas: map[string]core.ConstTermMeta{"zz_partial_s": S, "zz_vadd": vadd},
	}
	parse := func(text string) core.Term {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop.Conclusion()
	}
	law := prop.MakeProp(parse("∀add:(A → A → A). ∀c:set(A). zz_partial_s(add, c) ⇒ ∀x y:A. x ∈ c ∧ y ∈ c ⇒ add(x, y) = add(y, x)"))
	concl := parse("zz_vadd(add, u, v) = zz_vadd(add, v, u)")
	hd := applyHead{stated: law, describe: "the commutativity law"}

	for name, hyps := range map[string][]core.Term{
		"a comprehension carrier": {parse("zz_partial_s(zz_vadd(add), {p:(num → A) | P(p)})"), parse("u ∈ {p:(num → A) | P(p)}"), parse("v ∈ {p:(num → A) | P(p)}")},
		"a variable carrier":      {parse("zz_partial_s(zz_vadd(add), c)"), parse("u ∈ c"), parse("v ∈ c")},
	} {
		t.Run(name, func(t *testing.T) {
			sec := NewScript(makeStepTestEnv()).Section(prop.MakeProp(concl, hyps...))
			var claims []*GoalStackNode
			ok, miss := applyStatedHead(sec, &claims, sec, hd, rungOpts{depth: antecedentApplies})
			require.True(t, ok, "the operation binder at zz_vadd(add): %s", miss)
			require.True(t, sec.Proved() || len(byWorkingLeaves(sec, claims)) == 0, "closed up to the head's claim")
		})
	}
}
