// definitions.go — the laws of node groups of a model and their
// conditional distributions, and the variables of the randomized regime,
// which draws the intervened values beside the coin.

package kernel_do_calculus

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ScmMarginalDef — `scm_marginal(M, K)` is the law of V_K, the solution
// restricted to K, a measure on the configurations of K.
var ScmMarginalDef = scmMarginalDefThm{family.Define(registry.DefEntry{
	Name:  "ScmMarginalDef",
	Key:   "prop_af0e49dd4fe8accd",
	Const: "scm_marginal",
	Type:  "scm_model(A, B, I) → set(I) → set(I → B) → extended_nonneg_real",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀K:set(I). " +
			"    scm_marginal(M, K) = " +
			"    pushforward_measure(M.sample, M.prob, λu:A. override_on(K, scm_solve(M, u), M.default))",
	},
})}

// ScmJointLawDef — `scm_joint_law(M, W, Y)` is the law of the pair (V_W,
// V_Y), a measure on pairs of configurations of W and of Y.
var ScmJointLawDef = scmJointLawDefThm{family.Define(registry.DefEntry{
	Name:  "ScmJointLawDef",
	Key:   "prop_e197d88b355011c7",
	Const: "scm_joint_law",
	Type:  "scm_model(A, B, I) → set(I) → set(I) → set(prod(I → B, I → B)) → extended_nonneg_real",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀W Y:set(I). " +
			"    scm_joint_law(M, W, Y) = " +
			"    pushforward_measure(M.sample, " +
			"        M.prob, " +
			"        λu:A. " +
			"            (override_on(W, scm_solve(M, u), M.default), " +
			"                override_on(Y, scm_solve(M, u), M.default)))",
	},
})}

// ScmCondKernelDef — `scm_cond_kernel(M, W, Y, K)`: K, a kernel from the
// configurations of W to those of Y, is a version of the conditional
// distribution of V_Y given V_W in M — a disintegration of their joint
// law.
var ScmCondKernelDef = scmCondKernelDefThm{family.Define(registry.DefEntry{
	Name:  "ScmCondKernelDef",
	Key:   "prop_aa413e881474cbb7",
	Const: "scm_cond_kernel",
	Type: "scm_model(A, B, I) → " +
		"set(I) → " +
		"set(I) → " +
		"((I → B) → set(I → B) → extended_nonneg_real) → " +
		"bool",
	Deps: []registry.EntryLike{ScmJointLawDef},
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀W Y:set(I). ∀K:((I → B) → set(I → B) → extended_nonneg_real). " +
			"    scm_cond_kernel(M, W, Y, K) ⇔ " +
			"    is_disintegration(indexed_functions(W, M.default, M.states), " +
			"        indexed_product_sigma(W, M.default, M.states, M.state_sigma), " +
			"        indexed_functions(Y, M.default, M.states), " +
			"        indexed_product_sigma(Y, M.default, M.states, M.state_sigma), " +
			"        scm_joint_law(M, W, Y), " +
			"        K)",
	},
})}

// randomRegimeSolveDef — the variables of the randomized regime of M and
// do(Z = ·), on samples ((u, z), r): a background sample u, intervened
// values z drawn beside it, and a fair coin r. On r = ⊤ they are the
// solution at u of M intervened at Z with the values z, on r = ⊥ the
// solution of M at u. The regime root carries (z, r).
var randomRegimeSolveDef = randomRegimeSolveDefThm{family.Define(registry.DefEntry{
	Name:  "randomRegimeSolveDef",
	Key:   "prop_e23b58f535a852f3",
	Const: "random_regime_solve",
	Type:  "scm_model(A, B, I) → set(I) → prod(prod(A, I → B), bool) → I → B",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀Z:set(I). ∀p:prod(prod(A, I → B), bool). " +
			"    random_regime_solve(M, Z, p) = " +
			"    COND(snd(p), scm_solve(scm_do(M, Z, snd(fst(p))), fst(fst(p))), scm_solve(M, fst(fst(p))))",
	},
})}
