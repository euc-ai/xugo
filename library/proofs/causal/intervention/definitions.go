// definitions.go — the deterministic intervention as an operator on the
// model record, and the variables of the regime family that holds a
// model and one of its interventions in one probability space.

package intervention

import (
	"github.com/euc-ai/xugo/library/registry"
)

// DoDef — `scm_do(M, X, x)` is M with the mechanism of each node of X
// replaced by the constant x(i) and the edges into X deleted; the
// background, the noise, the states and the values off the nodes stay.
// x is read on X only.
var DoDef = doDefThm{family.Define(registry.DefEntry{
	Name:  "DoDef",
	Key:   "prop_8283c6b15557d9bc",
	Const: "scm_do",
	Type:  "scm_model(A, B, I) → set(I) → (I → B) → scm_model(A, B, I)",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀X:set(I). ∀x:(I → B). " +
			"    scm_do(M, X, x) = " +
			"    mk_scm(M.sample, " +
			"        M.events, " +
			"        M.prob, " +
			"        M.nodes, " +
			"        dag_delete_in(M.edges, X), " +
			"        M.states, " +
			"        M.state_sigma, " +
			"        M.default, " +
			"        M.noise, " +
			"        override_on(X, λi:I. λp:(I → B). λu:A. x(i), M.mech))",
	},
})}

// RegimeSolveDef — the variables of the regime family of M and do(Z = z),
// on samples (u, r) of the background beside a fair coin: on the face r
// = ⊤ the solution of the intervened model at u, on r = ⊥ the solution
// of M at u. Its probability space is `set_cross(M.sample, 𝕌)` with
// `bool_mixture_sigma` and `bool_mixture_measure`; the regime variable
// is the coin, snd.
var RegimeSolveDef = regimeSolveDefThm{family.Define(registry.DefEntry{
	Name:  "RegimeSolveDef",
	Key:   "prop_555f73c5235348b4",
	Const: "regime_solve",
	Type:  "scm_model(A, B, I) → set(I) → (I → B) → prod(A, bool) → I → B",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀Z:set(I). ∀z:(I → B). ∀p:prod(A, bool). " +
			"    regime_solve(M, Z, z, p) = " +
			"    COND(snd(p), scm_solve(scm_do(M, Z, z), fst(p)), scm_solve(M, fst(p)))",
	},
	Deps: []registry.EntryLike{DoDef},
})}
