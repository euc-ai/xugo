// definitions.go — the value of a causal expression in a model at an
// environment, by structural recursion on the expression.

package do_semantics

import (
	"github.com/euc-ai/xugo/library/registry"
)

// EvalDef — `do_expr_eval(M, v, e)`: an atom do_prob(Y, X, W) is the
// conditional probability, under M intervened at X with v's values, that
// the Y-coordinates agree with v given that the W-coordinates do; a sum
// over Z adds the body at each environment that overrides v on Z with
// values in the state carriers; products and quotients are pointwise,
// the quotient the total real division.
var EvalDef = evalDefThm{family.Define(registry.DefEntry{
	Name:  "EvalDef",
	Key:   "prop_7ed79facd9e2cde5",
	Const: "do_expr_eval",
	Type:  "scm_model(A, B, I) → (I → B) → do_expr(I) → real",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀v:(I → B). ∀Y X W:set(I). " +
			"    do_expr_eval(M, v, do_prob(Y, X, W)) = " +
			"    cond_prob(scm_distribution(scm_do(M, X, v)), agree_on(Y, v), agree_on(W, v))",
		"∀M:scm_model(A, B, I). ∀v:(I → B). ∀Z:set(I). ∀e:do_expr(I). " +
			"    do_expr_eval(M, v, do_sum(Z, e)) = " +
			"    real_sum(indexed_functions(Z, v, M.states), λw:(I → B). do_expr_eval(M, w, e))",
		"∀M:scm_model(A, B, I). ∀v:(I → B). ∀a b:do_expr(I). " +
			"    do_expr_eval(M, v, do_mul(a, b)) = do_expr_eval(M, v, a) * do_expr_eval(M, v, b)",
		"∀M:scm_model(A, B, I). ∀v:(I → B). ∀a b:do_expr(I). " +
			"    do_expr_eval(M, v, do_div(a, b)) = do_expr_eval(M, v, a) / do_expr_eval(M, v, b)",
	},
})}
