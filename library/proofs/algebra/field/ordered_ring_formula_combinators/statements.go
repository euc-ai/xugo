package ordered_ring_formula_combinators

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_ring_formula"
	// mints fun_zero, which trueFormulaDef's equation spells
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	// mints int_of_num, which trueFormulaDef's equation spells
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// trueFormulaDef — the true formula denies that the zero polynomial is negative; it seeds the
// finite conjunctions.
var trueFormulaDef = trueFormulaDefThm{family.Define(registry.DefEntry{
	Name: "trueFormulaDef", Const: "ordered_ring_true_formula", Type: "fo_formula((num → num) → int)",
	Key:       "prop_a7227508cdc2e5d6",
	Equations: []string{"ordered_ring_true_formula = fo_not(fo_atom(fun_zero(int_of_num(0))))"},
})}

// LeFormulaDef — the weak inequality p ≤ q is the negation of q < p.
var LeFormulaDef = leFormulaDefThm{family.Define(registry.DefEntry{
	Name:  "LeFormulaDef",
	Const: "polynomial_weak_inequality_formula",
	Type:  "((num → num) → int) → ((num → num) → int) → fo_formula((num → num) → int)",
	Key:   "prop_310475aa37d07cf",
	Equations: []string{
		"∀p q:((num → num) → int). " +
			"    polynomial_weak_inequality_formula(p, q) = fo_not(fo_atom(λm:(num → num). q(m) - p(m)))",
	},
})}

// eqFormulaDef — equality is the conjunction of the two weak inequalities.
var eqFormulaDef = eqFormulaDefThm{family.Define(registry.DefEntry{
	Name:  "eqFormulaDef",
	Const: "ordered_ring_equality_formula",
	Type:  "((num → num) → int) → ((num → num) → int) → fo_formula((num → num) → int)",
	Key:   "prop_1dbe6c70172db6a9",
	Equations: []string{
		"∀p q:((num → num) → int). " +
			"    ordered_ring_equality_formula(p, q) = " +
			"    fo_and(polynomial_weak_inequality_formula(p, q), polynomial_weak_inequality_formula(q, p))",
	},
	Deps: []registry.EntryLike{LeFormulaDef},
})}

// OrderedTrueFormulaSupport — the true formula of the ordered chapter is a well-formed sentence: it
// negates the atom of the zero polynomial, a valid polynomial with no variable.
var OrderedTrueFormulaSupport = orderedTrueFormulaSupportThm{family.Add(registry.ProofEntry{
	Name: "OrderedTrueFormulaSupport",
	Key:  "prop_e31d8f328244f13",
	Build: family.Theorem(
		"polynomial_formula_wf(ordered_ring_true_formula) ∧ "+
			"polynomial_formula_fv(ordered_ring_true_formula) = ∅",
		func(a *Argument) {
			a.Show(
				"the ordered true formula negates the atom of the "+
					"zero polynomial, a valid polynomial with no variable",
				Simp(
					Fwd(trueFormulaDef),
					Fwd(polynomial_formula.FormulaValidDef),
					Fwd(polynomial_formula.FormulaVarsDef),
					Fwd(first_order.WellFormedDef),
					Fwd(first_order.FreeVarsDef)),
				By(polynomial_formula.ZeroPolynomialValid))
		}),
})}

// OrderedTrueFormulaHolds — the true formula of the ordered chapter holds in an ordered field at
// every environment: it denies that the zero polynomial is negative, and zero is not below itself.
var OrderedTrueFormulaHolds = orderedTrueFormulaHoldsThm{family.Add(registry.ProofEntry{
	Name: "OrderedTrueFormulaHolds",
	Key:  "prop_e2886f9d476b79b3",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
		},
		Conclusion: "ordered_ring_formula_eval(F, lt, ρ, ordered_ring_true_formula)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ρ *Arrow[Nat, A],
		ordered ordered_field.OrderedFieldFact[on.F],
	) {
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		a.Show(
			"the zero polynomial evaluates to zero, which is not negative",
			Simp(
				Fwd(trueFormulaDef),
				Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef),
				Fwd(first_order.EvalDef),
				Fwd(ordered_ring_formula.OrderedRingFormulaAtomDef),
				Fwd(polynomial_formula.ZeroPolynomialValue)),
			By(ordered_field.Irreflexive.Read(ordered).At(zero)))
	}),
})}

// WeakInequalityFormulaSupport — the weak inequality p ≤ q between two integer polynomials is a
// well-formed formula whose variables are among theirs: it negates the atom of the difference
// q − p, a valid polynomial in their variables.
var WeakInequalityFormulaSupport = weakInequalityFormulaSupportThm{family.Add(registry.ProofEntry{
	Name: "WeakInequalityFormulaSupport",
	Key:  "prop_9b48088f82b6e35c",
	Build: family.Theorem(Statement{
		Binders: "∀p q:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
			"integer_polynomial(q)",
		},
		Conclusion: "polynomial_formula_wf(polynomial_weak_inequality_formula(p, q)) ∧ " +
			"polynomial_formula_fv(polynomial_weak_inequality_formula(p, q)) ⊆ " +
			"integer_polynomial_vars(p) ∪ integer_polynomial_vars(q)",
	}, func(a *Argument, p, q *Arrow[Fun[Nat, Nat], Int], pPolynomial, qPolynomial Fact) {
		a.Show(
			"p ≤ q negates the atom of q − p, which reads the variables of q and of p",
			Simp(
				Fwd(LeFormulaDef),
				Fwd(polynomial_formula.FormulaValidDef),
				Fwd(polynomial_formula.FormulaVarsDef),
				Fwd(first_order.WellFormedDef),
				Fwd(first_order.FreeVarsDef)),
			BySets(pPolynomial, qPolynomial, polynomial_formula.PolynomialDifference.At(q, p)))
	}),
})}

// OrderedEqualityFormulaSupport — the equation p = q of the ordered chapter between two integer
// polynomials is a well-formed formula whose variables are among theirs: it is the conjunction of
// p ≤ q and q ≤ p.
var OrderedEqualityFormulaSupport = orderedEqualityFormulaSupportThm{family.Add(registry.ProofEntry{
	Name: "OrderedEqualityFormulaSupport",
	Key:  "prop_b735f87207005a53",
	Build: family.Theorem(Statement{
		Binders: "∀p q:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
			"integer_polynomial(q)",
		},
		Conclusion: "polynomial_formula_wf(ordered_ring_equality_formula(p, q)) ∧ " +
			"polynomial_formula_fv(ordered_ring_equality_formula(p, q)) ⊆ " +
			"integer_polynomial_vars(p) ∪ integer_polynomial_vars(q)",
	}, func(a *Argument, p, q *Arrow[Fun[Nat, Nat], Int], pPolynomial, qPolynomial Fact) {
		a.Show(
			"p = q is the conjunction of p ≤ q and q ≤ p",
			Simp(
				Fwd(eqFormulaDef),
				Fwd(polynomial_formula.FormulaValidDef),
				Fwd(polynomial_formula.FormulaVarsDef),
				Fwd(first_order.WellFormedDef),
				Fwd(first_order.FreeVarsDef)),
			BySets(
				pPolynomial,
				qPolynomial,
				WeakInequalityFormulaSupport.At(p, q),
				WeakInequalityFormulaSupport.At(q, p),
				polynomial_formula.FormulaValidDef,
				polynomial_formula.FormulaVarsDef))
	}),
})}

// StrictComparisonBridge — over an ordered field, at an environment carrier-valued on the
// variables of p and q, the atom of the difference p − q holds exactly when the value of p lies
// below the value of q: the atom says that the difference evaluates below 0, the difference
// evaluates to the difference of the values, and translation by the value of q turns x − y < 0
// into x < y.
var StrictComparisonBridge = strictComparisonBridgeThm{family.Add(registry.ProofEntry{
	Name: "StrictComparisonBridge",
	Key:  "prop_48739314931cfe9f",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀p q:((num → num) → int).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"integer_polynomial(p)",
			"integer_polynomial(q)",
			"fo_env_ok(F.carrier, integer_polynomial_vars(p) ∪ integer_polynomial_vars(q), ρ)",
		},
		Conclusion: "ordered_ring_formula_eval(F, lt, ρ, fo_atom(λm:(num → num). p(m) - q(m))) ⇔ " +
			"lt(integer_polynomial_eval(field_ring(F), ρ, p), integer_polynomial_eval(field_ring(F), ρ, q))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ρ *Arrow[Nat, A],
		p, q *Arrow[Fun[Nat, Nat], Int],
		ordered ordered_field.OrderedFieldFact[on.F],
		pPolynomial, qPolynomial, env Fact,
	) {
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		R := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		x, xDef := a.LetAs[A]("x", "integer_polynomial_eval(field_ring(F), ρ, p)")
		y, yDef := a.LetAs[A]("y", "integer_polynomial_eval(field_ring(F), ρ, q)")
		difference := a.Have(
			"the difference p − q evaluates to x − y",
			"integer_polynomial_eval(field_ring(F), ρ, λm:(num → num). p(m) - q(m)) = x - y",
			By(
				xDef,
				yDef,
				pPolynomial,
				qPolynomial,
				env,
				polynomial_formula.EvaluationDifference.Read(ring).At(ρ, p, q)))
		values := a.Conjuncts(
			a.Have(
				"the values x and y lie in F",
				"x ∈ F.carrier ∧ y ∈ F.carrier",
				By(
					xDef,
					yDef,
					pPolynomial,
					qPolynomial,
					env,
					ring,
					first_order.EnvOKUnion.At(
						a.TermAs[Set[A]]("F.carrier"),
						a.TermAs[Set[Nat]]("integer_polynomial_vars(p)"),
						a.TermAs[Set[Nat]]("integer_polynomial_vars(q)"),
						ρ),
					polynomial_formula.EvaluationInCarrier.At(R, ρ, p),
					polynomial_formula.EvaluationInCarrier.At(R, ρ, q))),
			"x lies in F",
			"y lies in F")
		xm, ym := a.MemberOf[on.F](x, values[0]), a.MemberOf[on.F](y, values[1])
		a.Show(
			"the atom says that p − q, worth x − y, lies below 0; translated by y, that is x below y",
			Simp(
				Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef),
				Fwd(first_order.EvalDef),
				Fwd(ordered_ring_formula.OrderedRingFormulaAtomDef)),
			difference.Rw(),
			By(ordered_field.SubNegative.Read(ordered).At(xm, ym)))
	}),
})}

// ComparisonBridge — over an ordered field, at an environment carrier-valued on the variables of
// p and q, the weak inequality formula between p and q holds exactly when the value of p is at
// most the value of q, and the equality formula exactly when the two values agree. The atom of
// the weak inequality is the difference q − p, which by StrictComparisonBridge holds exactly when
// the value of q lies below the value of p; trichotomy turns its denial into weak order, and the
// two weak inequalities together into equality.
var ComparisonBridge = comparisonBridgeThm{family.Add(registry.ProofEntry{
	Name: "ComparisonBridge",
	Key:  "prop_1695175da6e7bd5b",
	Reading: "The environment guard places both polynomial values in the carrier, where " +
		"trichotomy applies. Outside the carrier negating reverse strict order need not be weak order.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀p q:((num → num) → int).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"integer_polynomial(p)",
			"integer_polynomial(q)",
			"fo_env_ok(F.carrier, integer_polynomial_vars(p) ∪ integer_polynomial_vars(q), ρ)",
		},
		Conclusion: "(ordered_ring_formula_eval(F, lt, ρ, polynomial_weak_inequality_formula(p, q)) ⇔ " +
			"    ordered_le(lt, " +
			"        integer_polynomial_eval(field_ring(F), ρ, p), " +
			"        integer_polynomial_eval(field_ring(F), ρ, q))) ∧ " +
			"(ordered_ring_formula_eval(F, lt, ρ, ordered_ring_equality_formula(p, q)) ⇔ " +
			"    integer_polynomial_eval(field_ring(F), ρ, p) = integer_polynomial_eval(field_ring(F), ρ, q))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ρ *Arrow[Nat, A],
		p, q *Arrow[Fun[Nat, Nat], Int],
		ordered ordered_field.OrderedFieldFact[on.F],
		pPolynomial, qPolynomial, env Fact,
	) {
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		R := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		x, xDef := a.LetAs[A]("x", "integer_polynomial_eval(field_ring(F), ρ, p)")
		y, yDef := a.LetAs[A]("y", "integer_polynomial_eval(field_ring(F), ρ, q)")
		swapped := a.Have(
			"the strict bridge at q and p takes the union of their variables the other way round",
			"fo_env_ok(F.carrier, integer_polynomial_vars(q) ∪ integer_polynomial_vars(p), ρ)",
			By(
				Normalized,
				env,
				set_algebra.UnionComm.At(
					a.TermAs[Set[Nat]]("integer_polynomial_vars(p)"),
					a.TermAs[Set[Nat]]("integer_polynomial_vars(q)"))))
		qBelowP := a.Simplified(
			GroupPremises(
				ordered, qPolynomial, pPolynomial, swapped, StrictComparisonBridge.At(F, lt, ρ, q, p)),
			Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef),
			Fwd(first_order.EvalDef))
		pBelowQ := a.Simplified(
			GroupPremises(ordered, pPolynomial, qPolynomial, env, StrictComparisonBridge.At(F, lt, ρ, p, q)),
			Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef),
			Fwd(first_order.EvalDef))
		values := a.Conjuncts(
			a.Have(
				"the values x and y lie in F",
				"x ∈ F.carrier ∧ y ∈ F.carrier",
				By(
					xDef,
					yDef,
					pPolynomial,
					qPolynomial,
					env,
					ring,
					first_order.EnvOKUnion.At(
						a.TermAs[Set[A]]("F.carrier"),
						a.TermAs[Set[Nat]]("integer_polynomial_vars(p)"),
						a.TermAs[Set[Nat]]("integer_polynomial_vars(q)"),
						ρ),
					polynomial_formula.EvaluationInCarrier.At(R, ρ, p),
					polynomial_formula.EvaluationInCarrier.At(R, ρ, q))),
			"x lies in F",
			"y lies in F")
		xm, ym := a.MemberOf[on.F](x, values[0]), a.MemberOf[on.F](y, values[1])
		a.Show(
			"p ≤ q denies the atom of q − p, which holds exactly when y lies below "+
				"x, and by trichotomy that denial is x ≤ y; p = q is both, so x = y",
			Simp(
				Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef),
				Fwd(eqFormulaDef),
				Fwd(LeFormulaDef),
				Fwd(first_order.EvalDef)),
			By(
				xDef,
				yDef,
				qBelowP,
				pBelowQ,
				ordered_field.OrderedLeDef.At(lt, x, y),
				ordered_field.Trichotomy.Read(ordered).At(xm, ym),
				ordered_field.Irreflexive.Read(ordered).At(xm),
				ordered_field.Transitive.Read(ordered).At(xm, ym, xm)))
	}),
})}
