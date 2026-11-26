package ring_formula_combinators

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ringTrueFormulaDef — the true formula is the atom of the zero polynomial.
var ringTrueFormulaDef = ringTrueFormulaDefThm{family.Define(registry.DefEntry{
	Name: "ringTrueFormulaDef", Const: "ring_true_formula", Type: "fo_formula((num → num) → int)",
	Key:       "prop_30d1aa9b24f964b4",
	Equations: []string{"ring_true_formula = fo_atom(fun_zero(int_of_num(0)))"},
})}

// ringEqualityFormulaDef — equality of two polynomial expressions is one difference atom.
var ringEqualityFormulaDef = ringEqualityFormulaDefThm{family.Define(registry.DefEntry{
	Name:  "ringEqualityFormulaDef",
	Const: "ring_equality_formula",
	Type:  "((num → num) → int) → ((num → num) → int) → fo_formula((num → num) → int)",
	Key:   "prop_62f5b5a4ff92cd9b",
	Equations: []string{
		"∀p q:((num → num) → int). ring_equality_formula(p, q) = fo_atom(λm:(num → num). p(m) - q(m))",
	},
})}

// RingTrueFormulaSupport — the true formula is a well-formed atom with no free variables: it is
// the atom of the zero polynomial, a valid polynomial with no variable.
var RingTrueFormulaSupport = ringTrueFormulaSupportThm{family.Add(registry.ProofEntry{
	Name: "RingTrueFormulaSupport",
	Key:  "prop_8302de9daf3840aa",
	Build: family.Theorem(
		"polynomial_formula_wf(ring_true_formula) ∧ polynomial_formula_fv(ring_true_formula) = ∅",
		func(a *Argument) {
			a.Show(
				"the true formula is the atom of the zero polynomial, which has no variables",
				Simp(
					Fwd(ringTrueFormulaDef),
					Fwd(polynomial_formula.FormulaValidDef),
					Fwd(polynomial_formula.FormulaVarsDef),
					Fwd(first_order.WellFormedDef),
					Fwd(first_order.FreeVarsDef)),
				By(polynomial_formula.ZeroPolynomialValid))
		}),
})}

// RingTrueFormulaHolds — the true formula holds in every field at every environment: it is the
// atom of the zero polynomial, which evaluates to zero.
var RingTrueFormulaHolds = ringTrueFormulaHoldsThm{family.Add(registry.ProofEntry{
	Name: "RingTrueFormulaHolds",
	Key:  "prop_9fb936f502ebc52f",
	Build: family.Theorem(
		"∀F:field_ops(A). ∀ρ:(num → A). ring_formula_eval(F, ρ, ring_true_formula)",
		func(a *Argument, F *Expr[FieldOps[A]], ρ *Arrow[Nat, A]) {
			a.Show(
				"the true formula is the atom of the zero polynomial, which evaluates to zero",
				Simp(
					Fwd(ring_formula.RingFormulaEvalDef),
					Fwd(ringTrueFormulaDef),
					Fwd(first_order.EvalDef),
					Fwd(ring_formula.RingFormulaAtomDef)),
				By(polynomial_formula.ZeroPolynomialValue.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"), ρ)))
		}),
})}

// RingEqualityFormulaSupport — the equation between two integer polynomials is a well-formed
// atom whose variables are among theirs: it is the atom of their difference, an integer polynomial
// in their variables.
var RingEqualityFormulaSupport = ringEqualityFormulaSupportThm{family.Add(registry.ProofEntry{
	Name: "RingEqualityFormulaSupport",
	Key:  "prop_e710733e7b3cdc6d",
	Build: family.Theorem(Statement{
		Binders: "∀p q:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
			"integer_polynomial(q)",
		},
		Conclusion: "polynomial_formula_wf(ring_equality_formula(p, q)) ∧ " +
			"polynomial_formula_fv(ring_equality_formula(p, q)) ⊆ " +
			"integer_polynomial_vars(p) ∪ integer_polynomial_vars(q)",
	}, func(a *Argument, p, q *Arrow[Fun[Nat, Nat], Int], pPolynomial, qPolynomial Fact) {
		a.Show(
			"the equation is the atom of the difference, an integer polynomial in the variables of p and q",
			Simp(
				Fwd(ringEqualityFormulaDef),
				Fwd(polynomial_formula.FormulaValidDef),
				Fwd(polynomial_formula.FormulaVarsDef),
				Fwd(first_order.WellFormedDef),
				Fwd(first_order.FreeVarsDef)),
			By(pPolynomial, qPolynomial, polynomial_formula.PolynomialDifference.At(p, q)))
	}),
})}

// RingEqualityFormulaEval — over a field, the equation between two integer polynomials holds at an
// environment carrier-valued on their variables exactly when the two take the same value: the
// atom says their difference evaluates to zero, and the difference evaluates to the difference of
// the values.
var RingEqualityFormulaEval = ringEqualityFormulaEvalThm{family.Add(registry.ProofEntry{
	Name: "RingEqualityFormulaEval",
	Key:  "prop_63c74aceb794e660",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀ρ:(num → A). ∀p q:((num → num) → int).",
		Hypotheses: []string{
			"field_on(F)",
			"integer_polynomial(p)",
			"integer_polynomial(q)",
			"fo_env_ok(F.carrier, integer_polynomial_vars(p) ∪ integer_polynomial_vars(q), ρ)",
		},
		Conclusion: "ring_formula_eval(F, ρ, ring_equality_formula(p, q)) ⇔ " +
			"integer_polynomial_eval(field_ring(F), ρ, p) = integer_polynomial_eval(field_ring(F), ρ, q)",
	}, func(a *Argument, F *Expr[FieldOps[A]], ρ *Arrow[Nat, A], p, q *Arrow[Fun[Nat, Nat], Int],
		isField field.FieldFact[on.F], pPolynomial, qPolynomial, env Fact) {
		R := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		carrier := a.TermAs[Set[A]]("F.carrier")
		variablesP := a.TermAs[Set[Nat]]("integer_polynomial_vars(p)")
		variablesQ := a.TermAs[Set[Nat]]("integer_polynomial_vars(q)")
		ring := field.RingOn.Read(isField)
		difference := GroupPremises(
			pPolynomial, qPolynomial, env, polynomial_formula.EvaluationDifference.Read(ring).At(ρ, p, q))
		values := a.Have(
			"the two values lie in F",
			"integer_polynomial_eval(field_ring(F), ρ, p) ∈ F.carrier ∧ "+
				"integer_polynomial_eval(field_ring(F), ρ, q) ∈ F.carrier",
			By(
				pPolynomial,
				qPolynomial,
				env,
				ring,
				first_order.EnvOKUnion.At(carrier, variablesP, variablesQ, ρ),
				polynomial_formula.EvaluationInCarrier.At(R, ρ, p),
				polynomial_formula.EvaluationInCarrier.At(R, ρ, q)))
		a.Show(
			"the equation is the atom of the difference, which evaluates to the difference of the values",
			Simp(
				Fwd(ring_formula.RingFormulaEvalDef),
				Fwd(ringEqualityFormulaDef),
				Fwd(first_order.EvalDef),
				Fwd(ring_formula.RingFormulaAtomDef)),
			difference.Rw(),
			Derive(func(b *Argument) {
				b.Iff()
				b.Forward(
					"a difference of two elements that is zero makes them equal",
					func(c *Argument, zero Fact) {
						c.Show(
							"the values of p and q agree",
							ByArith(isField, zero, values))
					})
				b.Backward(
					"equal elements have difference zero",
					func(c *Argument, same Fact) {
						c.Show(
							"the difference of the values is zero",
							ByArith(isField, same, values))
					})
			}))
	}),
})}
