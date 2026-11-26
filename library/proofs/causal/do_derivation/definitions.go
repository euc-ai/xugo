// definitions.go — causal expressions over node sets, their free nodes,
// well-formedness and observational fragment, and the derivation
// relation of the do-calculus as the least relation its rules generate.

package do_derivation

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// DoExprData — the datatype `do_expr(I)`. `do_prob(Y, X, W)` is the atom
// P(v_Y | do(v_X), v_W); `do_sum(Z, e)` sums e over the values of Z;
// `do_mul` and `do_div` are the product and the quotient. Arguments are
// node sets; the values come from the environment an expression is read
// at.
var DoExprData = family.DefineData(registry.DataEntry{
	Name:   "DoExpr",
	Type:   "do_expr",
	Params: []string{"I"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "do_prob", Args: []string{"set(I)", "set(I)", "set(I)"}},
		{Name: "do_sum", Args: []string{"set(I)", "do_expr(I)"}},
		{Name: "do_mul", Args: []string{"do_expr(I)", "do_expr(I)"}},
		{Name: "do_div", Args: []string{"do_expr(I)", "do_expr(I)"}},
	},
	Principles: registry.DataPrinciples{
		Induction: "DoExprInduction",
		Recursion: "DoExprRecursion",
		Injective: "DoExprInjective",
		Distinct:  "DoExprDistinct",
	},
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		peano.SucNotZero,
		peano.SucInjective,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
})

// FreeDef — the free nodes of an expression: an atom's three groups; a
// sum's body without the summed group; a product's or quotient's two
// sides together.
var FreeDef = freeDefThm{family.Define(registry.DefEntry{
	Name:  "FreeDef",
	Key:   "prop_320c08a4f40a3c8d",
	Const: "do_expr_free",
	Type:  "do_expr(I) → set(I)",
	Equations: []string{
		"∀Y X W:set(I). do_expr_free(do_prob(Y, X, W)) = Y ∪ X ∪ W",
		"∀Z:set(I). ∀e:do_expr(I). do_expr_free(do_sum(Z, e)) = do_expr_free(e) ∖ Z",
		"∀a b:do_expr(I). do_expr_free(do_mul(a, b)) = do_expr_free(a) ∪ do_expr_free(b)",
		"∀a b:do_expr(I). do_expr_free(do_div(a, b)) = do_expr_free(a) ∪ do_expr_free(b)",
	},
	Deps: []registry.EntryLike{DoExprData.Recursion},
})}

// WellFormedDef — an expression is well formed over the observed nodes O
// when each atom's three groups are pairwise disjoint and observed, and
// each summed group is observed.
var WellFormedDef = wellFormedDefThm{family.Define(registry.DefEntry{
	Name:  "WellFormedDef",
	Key:   "prop_e0f8b954b509bee7",
	Const: "do_expr_wf",
	Type:  "set(I) → do_expr(I) → bool",
	Equations: []string{
		"∀O Y X W:set(I). " +
			"    do_expr_wf(O, do_prob(Y, X, W)) ⇔ Y ⊆ O ∧ X ⊆ O ∧ W ⊆ O ∧ Y ∩ X = ∅ ∧ Y ∩ W = ∅ ∧ X ∩ W = ∅",
		"∀O Z:set(I). ∀e:do_expr(I). do_expr_wf(O, do_sum(Z, e)) ⇔ Z ⊆ O ∧ do_expr_wf(O, e)",
		"∀O:set(I). ∀a b:do_expr(I). do_expr_wf(O, do_mul(a, b)) ⇔ do_expr_wf(O, a) ∧ do_expr_wf(O, b)",
		"∀O:set(I). ∀a b:do_expr(I). do_expr_wf(O, do_div(a, b)) ⇔ do_expr_wf(O, a) ∧ do_expr_wf(O, b)",
	},
	Deps: []registry.EntryLike{DoExprData.Recursion},
})}

// ObservationalDef — an expression is observational when no atom
// intervenes.
var ObservationalDef = observationalDefThm{family.Define(registry.DefEntry{
	Name:  "ObservationalDef",
	Key:   "prop_4989a8cd678b8c28",
	Const: "do_expr_observational",
	Type:  "do_expr(I) → bool",
	Equations: []string{
		"∀Y X W:set(I). do_expr_observational(do_prob(Y, X, W)) ⇔ X = ∅",
		"∀Z:set(I). ∀e:do_expr(I). do_expr_observational(do_sum(Z, e)) ⇔ do_expr_observational(e)",
		"∀a b:do_expr(I). " +
			"    do_expr_observational(do_mul(a, b)) ⇔ do_expr_observational(a) ∧ do_expr_observational(b)",
		"∀a b:do_expr(I). " +
			"    do_expr_observational(do_div(a, b)) ⇔ do_expr_observational(a) ∧ do_expr_observational(b)",
	},
	Deps: []registry.EntryLike{DoExprData.Recursion},
})}

// doDerivable — `do_derivable(E, O, e₁, e₂)`, e₁ derives to e₂ in the
// graph E with observed nodes O: the least relation the rules below
// generate, in order:
// reflexivity; symmetry; transitivity; sum congruence; product congruence; quotient congruence; Rule 1, observation; Rule 2, exchange; Rule 3, deletion; conditioning; marginalisation; the empty event; commutativity; associativity; unit; a quotient by itself; a quotient as a product with a reciprocal; a factor out of a sum; nested sums; the empty sum.
// The three causal rules take their separation condition in E with the
// edges into X deleted, and further edges deleted as each rule asks;
// every disjointness a rule needs is written in it.
var doDerivable = family.DefineInductive(registry.InductiveEntry{
	Name: "DoDerivable",
	Keys: registry.InductiveKeys{
		Rules:        "prop_ed5d025af9d425d3",
		Induct:       "prop_899ebb92359c5b9b",
		Cases:        "prop_c2c8ff587839198",
		InductStrong: "prop_f5b0b1ce420e09ec",
	},
	Const:  "do_derivable",
	Type:   "(I → I → bool) → set(I) → do_expr(I) → do_expr(I) → bool",
	Params: []string{"E", "O"},
	Rules: []string{
		"∀e:do_expr(I). do_expr_wf(O, e) ⇒ do_derivable(E, O, e, e)",
		"∀e₁ e₂:do_expr(I). do_derivable(E, O, e₁, e₂) ⇒ do_derivable(E, O, e₂, e₁)",
		"∀e₁ e₂ e₃:do_expr(I). do_derivable(E, O, e₁, e₂) ∧ " +
			"do_derivable(E, O, e₂, e₃) ⇒ do_derivable(E, O, e₁, e₃)",
		"∀Z:set(I). ∀e₁ e₂:do_expr(I). Z ⊆ O ∧ do_derivable(E, O, " +
			"e₁, e₂) ⇒ do_derivable(E, O, do_sum(Z, e₁), do_sum(Z, e₂))",
		"∀a₁ a₂ b₁ b₂:do_expr(I). do_derivable(E, O, a₁, a₂) ∧ do_derivable(E, " +
			"O, b₁, b₂) ⇒ do_derivable(E, O, do_mul(a₁, b₁), do_mul(a₂, b₂))",
		"∀a₁ a₂ b₁ b₂:do_expr(I). do_derivable(E, O, a₁, a₂) ∧ do_derivable(E, " +
			"O, b₁, b₂) ⇒ do_derivable(E, O, do_div(a₁, b₁), do_div(a₂, b₂))",
		"∀X Y Z W:set(I). X ⊆ O ∧ Y ⊆ O ∧ Z ⊆ O ∧ W ⊆ O ∧ X ∩ Y = ∅ ∧ X ∩ Z = ∅ ∧ X " +
			"∩ W = ∅ ∧ Y ∩ Z = ∅ ∧ Y ∩ W = ∅ ∧ Z ∩ W = ∅ ∧ d_separated(dag_delete_in(E, " +
			"X), Y, Z, X ∪ W) ⇒ do_derivable(E, O, do_prob(Y, X, Z ∪ W), do_prob(Y, X, W))",
		"∀X Y Z W:set(I). X ⊆ O ∧ Y ⊆ O ∧ Z ⊆ O ∧ W ⊆ O ∧ X ∩ Y = ∅ ∧ X ∩ Z = ∅ ∧ X ∩ W = ∅ " +
			"∧ Y ∩ Z = ∅ ∧ Y ∩ W = ∅ ∧ Z ∩ W = ∅ ∧ d_separated(dag_delete_out(dag_delete_in(E, " +
			"X), Z), Y, Z, X ∪ W) ⇒ do_derivable(E, O, do_prob(Y, X ∪ Z, W), do_prob(Y, X, Z ∪ W))",
		"∀X Y Z W:set(I). X ⊆ O ∧ Y ⊆ O ∧ Z ⊆ O ∧ W ⊆ O ∧ X ∩ Y = ∅ ∧ X ∩ Z = ∅ ∧ X ∩ W = " +
			"∅ ∧ Y ∩ Z = ∅ ∧ Y ∩ W = ∅ ∧ Z ∩ W = ∅ ∧ " +
			"d_separated(dag_delete_in(dag_delete_in(E, X), Z ∖ dag_ancestors(dag_delete_in(E, " +
			"X), W)), Y, Z, X ∪ W) ⇒ do_derivable(E, O, do_prob(Y, X ∪ Z, W), do_prob(Y, X, W))",
		"∀X Y W:set(I). X ⊆ O ∧ Y ⊆ O ∧ W ⊆ O ∧ X ∩ Y = ∅ ∧ X ∩ W = ∅ ∧ Y ∩ W = ∅ ⇒ " +
			"do_derivable(E, O, do_prob(Y, X, W), do_div(do_prob(Y ∪ W, X, ∅), do_prob(W, X, ∅)))",
		"∀X Y Z W:set(I). X ⊆ O ∧ Y ⊆ O ∧ Z ⊆ O ∧ W ⊆ O ∧ X ∩ Y = ∅ ∧ X ∩ Z = ∅ ∧ X ∩ W = ∅ ∧ Y ∩ Z = ∅ " +
			"∧ Y ∩ W = ∅ ∧ Z ∩ W = ∅ ⇒ do_derivable(E, O, do_sum(Z, do_prob(Y ∪ Z, X, W)), do_prob(Y, X, W))",
		"∀X W:set(I). X ⊆ O ∧ W ⊆ O ∧ X ∩ W = ∅ ⇒ do_derivable(E, O, do_prob(∅, X, W), do_prob(∅, ∅, ∅))",
		"∀a b:do_expr(I). do_expr_wf(O, a) ∧ do_expr_wf(O, " +
			"b) ⇒ do_derivable(E, O, do_mul(a, b), do_mul(b, a))",
		"∀a b c:do_expr(I). do_expr_wf(O, a) ∧ do_expr_wf(O, b) ∧ do_expr_wf(O, " +
			"c) ⇒ do_derivable(E, O, do_mul(a, do_mul(b, c)), do_mul(do_mul(a, b), c))",
		"∀a:do_expr(I). do_expr_wf(O, a) ⇒ do_derivable(E, O, do_mul(do_prob(∅, ∅, ∅), a), a)",
		"∀a:do_expr(I). do_expr_wf(O, a) ⇒ do_derivable(E, O, do_div(a, a), do_prob(∅, ∅, ∅))",
		"∀a b:do_expr(I). do_expr_wf(O, a) ∧ do_expr_wf(O, b) ⇒ do_derivable(E, " +
			"O, do_div(a, b), do_mul(a, do_div(do_prob(∅, ∅, ∅), b)))",
		"∀Z:set(I). ∀a b:do_expr(I). Z ⊆ O ∧ do_expr_wf(O, a) ∧ do_expr_wf(O, b) ∧ do_expr_free(a) " +
			"∩ Z = ∅ ⇒ do_derivable(E, O, do_sum(Z, do_mul(a, b)), do_mul(a, do_sum(Z, b)))",
		"∀Z₁ Z₂:set(I). ∀e:do_expr(I). Z₁ ⊆ O ∧ Z₂ ⊆ O ∧ Z₁ ∩ Z₂ = ∅ ∧ do_expr_wf(O, " +
			"e) ⇒ do_derivable(E, O, do_sum(Z₁, do_sum(Z₂, e)), do_sum(Z₁ ∪ Z₂, e))",
		"∀e:do_expr(I). do_expr_wf(O, e) ⇒ do_derivable(E, O, do_sum(∅, e), e)",
	},
	Deps: []registry.EntryLike{FreeDef, WellFormedDef},
})

// DoDerivableRules — the rules of the derivation relation, verbatim.
var DoDerivableRules = doDerivableRulesThm{doDerivable.Rules}

// DoDerivableInduct — rule induction along derivation: a relation that
// the rules preserve contains every derivation.
var DoDerivableInduct = doDerivableInductThm{doDerivable.Induct}

// DoDerivableInductStrong — rule induction whose steps also know their
// premises are derivations.
var DoDerivableInductStrong = doDerivableInductStrongThm{doDerivable.InductStrong}

// DoDerivableCases — a derivation is an instance of one of the rules.
var DoDerivableCases = doDerivableCasesThm{doDerivable.Cases}

// DoExprInduction — a property of every atom, preserved by sums,
// products and quotients, holds of every expression.
var DoExprInduction = doExprInductionThm{DoExprData.Induct}

// DoExprRecursion — a function on expressions is fixed by its values at
// the four constructors.
var DoExprRecursion = doExprRecursionThm{DoExprData.Recursion}

// DoExprInjective — each constructor determines its arguments.
var DoExprInjective = doExprInjectiveThm{DoExprData.Inj}

// DoExprDistinct — expressions built by different constructors differ.
var DoExprDistinct = doExprDistinctThm{DoExprData.Distinct}
