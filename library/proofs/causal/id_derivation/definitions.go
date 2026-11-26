// definitions.go — an order of the observed nodes compatible with
// ancestry, and three operations on causal expressions that the lines of
// ID build their outputs with: adding an intervention group to every
// atom, the product of a list, and the chain of conditionals of a
// district.

package id_derivation

import (
	"github.com/euc-ai/xugo/library/registry"
)

// TopologicalListDef — `dag_topological_list(E, O, l)`: l lists the
// nodes of O once each, and no node of l is an ancestor of one before
// it.
var TopologicalListDef = topologicalListDefThm{family.Define(registry.DefEntry{
	Name:  "TopologicalListDef",
	Key:   "prop_9709f6f2106bfcd0",
	Const: "dag_topological_list",
	Type:  "(I → I → bool) → set(I) → list(I) → bool",
	Equations: []string{
		"∀E:(I → I → bool). ∀O:set(I). ∀l:list(I). " +
			"    dag_topological_list(E, O, l) ⇔ " +
			"    list_distinct(l) ∧ " +
			"    (∀u:I. list_member(u, l) ⇔ u ∈ O) ∧ " +
			"    (∀l₁ l₂:list(I). ∀u w:I. " +
			"        l = list_append(l₁, cons(u, l₂)) ∧ list_member(w, l₂) ⇒ ¬transitive_closure(E, w, u))",
	},
})}

// interveneDef — `do_expr_intervene(D, e)`: e with D added to the
// intervention group of every atom. A subproblem's observational
// expression, read in the graph where D is intervened on, is this.
var interveneDef = interveneDefThm{family.Define(registry.DefEntry{
	Name:  "interveneDef",
	Key:   "prop_e5d53f1f1656fbbb",
	Const: "do_expr_intervene",
	Type:  "set(I) → do_expr(I) → do_expr(I)",
	Equations: []string{
		"∀D Y X W:set(I). do_expr_intervene(D, do_prob(Y, X, W)) = do_prob(Y, X ∪ D, W)",
		"∀D Z:set(I). ∀e:do_expr(I). " +
			"    do_expr_intervene(D, do_sum(Z, e)) = do_sum(Z, do_expr_intervene(D, e))",
		"∀D:set(I). ∀a b:do_expr(I). " +
			"    do_expr_intervene(D, do_mul(a, b)) = do_mul(do_expr_intervene(D, a), do_expr_intervene(D, b))",
		"∀D:set(I). ∀a b:do_expr(I). " +
			"    do_expr_intervene(D, do_div(a, b)) = do_div(do_expr_intervene(D, a), do_expr_intervene(D, b))",
	},
})}

// prodDef — `do_prod(l)`: the product of a list of expressions, the
// constant 1 for the empty list.
var prodDef = prodDefThm{family.Define(registry.DefEntry{
	Name:  "prodDef",
	Key:   "prop_b8ff91d4fa46f81b",
	Const: "do_prod",
	Type:  "list(do_expr(I)) → do_expr(I)",
	Equations: []string{
		"do_prod(nil⟨A:do_expr(I)⟩) = do_prob(∅⟨A:I⟩, ∅⟨A:I⟩, ∅⟨A:I⟩)",
		"∀e:do_expr(I). ∀t:list(do_expr(I)). do_prod(cons(e, t)) = do_mul(e, do_prod(t))",
	},
})}

// chainDef — `do_chain(S, l)`: along a list l of nodes, latest first, the
// product over the nodes v of S of P(v | the nodes after v in l). Read on
// the reverse of a topological list it is Π_{v_i ∈ S} P(v_i | v_π^{(i−1)}),
// the factor ID's last lines give a district.
var chainDef = chainDefThm{family.Define(registry.DefEntry{
	Name:  "chainDef",
	Key:   "prop_83abaa358ec4f87a",
	Const: "do_chain",
	Type:  "set(I) → list(I) → do_expr(I)",
	Equations: []string{
		"∀S:set(I). do_chain(S, nil) = do_prob(∅, ∅, ∅)",
		"∀S:set(I). ∀v:I. ∀t:list(I). " +
			"    do_chain(S, cons(v, t)) = " +
			"    COND(v ∈ S, do_mul(do_prob({v}, ∅, set_of_list(t)), do_chain(S, t)), do_chain(S, t))",
	},
})}
