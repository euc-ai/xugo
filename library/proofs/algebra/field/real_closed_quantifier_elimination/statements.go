// statements.go — quantifier elimination over the real closed fields: a
// quantifier-free formula read through the sign vector of its atoms, a
// quantifier-free formula cutting out each set of sign vectors, the
// elimination of one existential, and its lift to every formula.

package real_closed_quantifier_elimination

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_ring_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_sign_table"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/uniform_sign_table"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// SignVectorValue — a quantifier-free formula whose atoms lie in a list P
// takes the value the signs of its atoms give it: read through any sign
// assignment σ whose list along P is the sign vector of P, an atom p holding
// exactly when σ(p) = −1. That reading is propositional: it evaluates φ over
// a placeholder carrier, 𝕌 of num, at a placeholder environment, λn. 0, which
// its atom test never reads. The atom p < 0 holds exactly when the sign of p
// is −1, and σ agrees with that sign on every member of P, so the ordered
// atoms and the sign reading agree on every atom of φ.
var SignVectorValue = signVectorValueThm{family.Add(registry.ProofEntry{
	Name: "SignVectorValue",
	Key:  "prop_da8d15a151463b54",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀ρ:(num → A). " +
			"∀P:list((num → num) → int). " +
			"∀σ:(((num → num) → int) → int). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"fo_qf(φ)",
			"fo_wf(λp:((num → num) → int). list_member(p, P), φ)",
			"polynomial_signs(F, lt, ρ, P) = list_map(σ, P)",
		},
		Conclusion: "ordered_ring_formula_eval(F, lt, ρ, φ) ⇔ " +
			"fo_eval(𝕌, λp:((num → num) → int). λτ:(num → num). σ(p) = -1, λn:num. 0, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ρ *Arrow[Nat, A],
		P *Expr[List[IntegerPolynomial]],
		σ *Arrow[IntegerPolynomial, Int],
		φ *Expr[Formula[IntegerPolynomial]],
		qf, atoms, signs Fact,
	) {
		agree := a.Have(
			"on a member p of P the atom p < 0 holds exactly when σ(p) = −1",
			"∀p:((num → num) → int). list_member(p, P) ⇒ (ordered_ring_formula_atom(F, lt, p, ρ) ⇔ σ(p) = -1)",
			Derive(func(b *Argument) {
				p := b.FixAs[IntegerPolynomial]("p")
				member := b.Assume()
				sign := b.Have(
					"σ gives each member of P its sign, its list along P being the sign vector of P",
					"σ(p) = ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, p))",
					By(
						signs,
						member,
						polynomial_sign_table.SignsDef,
						list.MapAgreesOnMembers.At(
							σ,
							b.TermAs[Fun[IntegerPolynomial, Int]](
								"λq:((num → num) → int). ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q))"),
							P,
							p)))
				b.Show(
					"the sign of a value is −1 exactly when the value is negative",
					Simp(
						Fwd(sign),
						Fwd(ordered_field.OrderedSignDef),
						Fwd(ordered_ring_formula.OrderedRingFormulaAtomDef)),
					CondRewrite(),
					ByArith())
			}))
		a.Show(
			"so the ordered atoms and the sign reading give φ one value",
			Simp(Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef)),
			By(
				qf,
				atoms,
				agree,
				first_order.QuantifierFreeAtomAgreement.At(
					a.TermAs[Set[IntegerPolynomial]]("λq:((num → num) → int). list_member(q, P)"),
					a.TermAs[Set[A]]("F.carrier"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, A], Bool]]("ordered_ring_formula_atom(F, lt)"),
					ρ,
					a.TermAs[Set[Nat]]("𝕌"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, Nat], Bool]](
						"λq:((num → num) → int). λτ:(num → num). σ(q) = -1"),
					a.TermAs[Fun[Nat, Nat]]("λn:num. 0"),
					φ)))
	}),
})}

// SignConditionFormula — every set G of sign vectors of a list E of valid
// polynomials in the variables U is cut out by a valid quantifier-free
// formula in those variables, uniformly over ordered fields: by induction on
// E. The empty list has the one sign vector nil, and a constant formula says
// whether G holds it. In front of a tail, the value x of the head e is
// negative, positive or zero, with sign −1, 1 or 0, x positive exactly when e
// with its coefficients negated is negative; the formula asks which, and
// answers with the tail's formula for the sign vectors G holds behind that
// sign.
var SignConditionFormula = signConditionFormulaThm{family.Add(registry.ProofEntry{
	Name: "SignConditionFormula",
	Key:  "prop_8c049e96f8f3c97d",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀E:list((num → num) → int). ∀G:set(list(int)).",
		Hypotheses: []string{
			"polynomial_list_over(U, E)",
		},
		Conclusion: "∃χ:fo_formula((num → num) → int). " +
			"    polynomial_formula_wf(χ) ∧ " +
			"    fo_qf(χ) ∧ " +
			"    polynomial_formula_fv(χ) ⊆ U ∧ " +
			"    (∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). " +
			"        ordered_field_on(F, lt) ∧ fo_env_ok(F.carrier, U, ρ) ⇒ " +
			"        (ordered_ring_formula_eval(F, lt, ρ, χ) ⇔ polynomial_signs(F, lt, ρ, E) ∈ G))",
	}, func(a *Argument, U *Expr[Set[Nat]], E *Expr[List[IntegerPolynomial]]) {
		type signVectors = Set[List[Int]]
		a.Induct(E)
		a.Base(
			"the empty list has the one sign vector nil, and a constant formula says whether G holds it",
			func(b *Argument) {
				b.FixAs[signVectors]("G")
				b.Assume()
				χ, constant := b.UnpackAs[Formula[IntegerPolynomial]](
					GroupPremises(
						polynomial_formula.ZeroPolynomialValid,
						first_order.ConstantFormula.Inst(TypeBinder.BindA[IntegerPolynomial](), TypeBinder.BindB[A]()).At(
							b.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
							b.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
							b.TermAs[IntegerPolynomial]("fun_zero(int_of_num(0))"),
							b.TermAs[Bool]("nil ∈ G"))),
					"χ")
				b.Take(χ)
				b.Show(
					"the constant formula on the zero polynomial is "+
						"closed, and the sign vector of the empty list is nil",
					By(
						Normalized,
						constant,
						polynomial_sign_table.SignsDef,
						list.ListMapDef,
						set_order.EmptySubset,
						polynomial_formula.FormulaValidDef,
						polynomial_formula.FormulaVarsDef,
						ordered_ring_formula.OrderedRingFormulaEvalDef))
			})
		a.Step(
			"a head e in front of the tail: ask whether its value is negative, "+
				"positive or zero, and answer with the tail's formula behind that sign",
			func(b *Argument, ih Fact) {
				b.StepArgs("e", "E")
				b.FixAs[signVectors]("G")
				over := b.Assume()
				head := b.Have(
					"the head e is a valid polynomial in the variables U",
					"integer_polynomial(e) ∧ integer_polynomial_vars(e) ⊆ U",
					By(over, polynomial_formula.PolynomialListOverDef, list.ListMemberDef))
				tail := b.Have(
					"and the tail lists valid polynomials in the variables U",
					"polynomial_list_over(U, E)",
					By(over, polynomial_formula.PolynomialListOverDef, list.ListMemberDef))
				_, negativeTail := b.UnpackAs[Formula[IntegerPolynomial]](
					GroupPremises(tail, ih.At(b.TermAs[signVectors]("{s:list(int) | cons(-int_of_num(1), s) ∈ G}"))),
					"χ₁")
				_, zeroTail := b.UnpackAs[Formula[IntegerPolynomial]](
					GroupPremises(tail, ih.At(b.TermAs[signVectors]("{s:list(int) | cons(int_of_num(0), s) ∈ G}"))),
					"χ₂")
				_, positiveTail := b.UnpackAs[Formula[IntegerPolynomial]](
					GroupPremises(tail, ih.At(b.TermAs[signVectors]("{s:list(int) | cons(int_of_num(1), s) ∈ G}"))),
					"χ₃")
				negative := b.Conjuncts(
					negativeTail,
					"χ₁ is valid",
					"χ₁ is quantifier-free",
					"χ₁ is in the variables U",
					"χ₁ holds where G holds the sign vector of the tail behind −1")
				zero := b.Conjuncts(
					zeroTail,
					"χ₂ is valid",
					"χ₂ is quantifier-free",
					"χ₂ is in the variables U",
					"χ₂ holds where G holds the sign vector of the tail behind 0")
				positive := b.Conjuncts(
					positiveTail,
					"χ₃ is valid",
					"χ₃ is quantifier-free",
					"χ₃ is in the variables U",
					"χ₃ holds where G holds the sign vector of the tail behind 1")
				b.Take(b.TermAs[Formula[IntegerPolynomial]](
					"fo_and(fo_implies(fo_atom(e), χ₁), " +
						"    fo_implies(fo_not(fo_atom(e)), " +
						"        fo_and(fo_implies(fo_atom(λm:(num → num). -e(m)), χ₃), " +
						"            fo_implies(fo_not(fo_atom(λm:(num → num). -e(m))), χ₂))))"))
				b.Show(
					"the formula asking for the sign of e is valid and quantifier-free "+
						"in the variables U, and tells the sign vectors G holds",
					SplitConj(
						Case(
							"it is built from e, e with its coefficients negated and the three "+
								"tail formulas, all valid and quantifier-free in the variables U",
							Simp(
								Fwd(polynomial_formula.FormulaValidDef),
								Fwd(polynomial_formula.FormulaVarsDef),
								Fwd(first_order.ImpliesDef),
								Fwd(first_order.WellFormedDef),
								Fwd(first_order.QuantifierFreeDef),
								Fwd(first_order.FreeVarsDef)),
							BySets(
								head,
								polynomial_formula.PolynomialNegation.At(b.TermAs[IntegerPolynomial]("e")),
								negative[0],
								negative[1],
								negative[2],
								zero[0],
								zero[1],
								zero[2],
								positive[0],
								positive[1],
								positive[2],
								polynomial_formula.FormulaValidDef,
								polynomial_formula.FormulaVarsDef)),
						Case(
							"in an ordered field the formula holds exactly where G holds the sign vector of cons(e, E)",
							Derive(func(c *Argument) {
								F := c.FixAs[FieldOps[A]]("F")
								lt := c.FixAs[Fun2[A, A, Bool]]("lt")
								ρ := c.FixAs[Fun[Nat, A]]("ρ")
								legality := c.Assume()
								parts := c.Conjuncts(
									legality,
									"F is an ordered field under lt",
									"ρ is legal on U")
								ordered, legal := parts[0], parts[1]
								ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
								x := c.TermAs[A]("integer_polynomial_eval(field_ring(F), ρ, e)")
								legalOnE := c.Have(
									"ρ is legal on the variables of e",
									"fo_env_ok(F.carrier, integer_polynomial_vars(e), ρ)",
									By(
										head,
										legal,
										first_order.EnvOKSubset.At(
											c.TermAs[Set[A]]("F.carrier"),
											c.TermAs[Set[Nat]]("integer_polynomial_vars(e)"),
											U,
											ρ)))
								inCarrier := c.Have(
									"so the value x of e lies in the carrier",
									"integer_polynomial_eval(field_ring(F), ρ, e) ∈ F.carrier",
									By(
										head,
										legalOnE,
										ring,
										polynomial_formula.EvaluationInCarrier.At(
											c.TermAs[module_record.RingOps[A]]("field_ring(F)"), ρ, c.TermAs[IntegerPolynomial]("e"))))
								negation := c.Have(
									"and e with its coefficients negated takes the value −x",
									"integer_polynomial_eval(field_ring(F), ρ, λm:(num → num). -e(m)) = "+
										"F.neg(integer_polynomial_eval(field_ring(F), ρ, e))",
									By(
										head,
										legalOnE,
										ring,
										polynomial_formula.EvaluationNegation.At(
											c.TermAs[module_record.RingOps[A]]("field_ring(F)"), ρ, c.TermAs[IntegerPolynomial]("e"))))
								signs := c.Have(
									"the sign vector of cons(e, E) is the sign of x in front of the sign vector of E",
									"polynomial_signs(F, lt, ρ, cons(e, E)) = "+
										"cons(ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, e)), "+
										"    polynomial_signs(F, lt, ρ, E))",
									Simp(Fwd(polynomial_sign_table.SignsDef), Fwd(list.ListMapDef)),
									Basic())
								behindNegative := c.Have(
									"χ₁ holds exactly where G holds the sign vector of E behind −1",
									"fo_eval(F.carrier, ordered_ring_formula_atom(F, lt), ρ, χ₁) ⇔ "+
										"cons(-int_of_num(1), polynomial_signs(F, lt, ρ, E)) ∈ G",
									By(negative[3], legality, ordered_ring_formula.OrderedRingFormulaEvalDef))
								behindZero := c.Have(
									"χ₂ holds exactly where G holds it behind 0",
									"fo_eval(F.carrier, ordered_ring_formula_atom(F, lt), ρ, χ₂) ⇔ "+
										"cons(int_of_num(0), polynomial_signs(F, lt, ρ, E)) ∈ G",
									By(zero[3], legality, ordered_ring_formula.OrderedRingFormulaEvalDef))
								behindPositive := c.Have(
									"χ₃ holds exactly where G holds it behind 1",
									"fo_eval(F.carrier, ordered_ring_formula_atom(F, lt), ρ, χ₃) ⇔ "+
										"cons(int_of_num(1), polynomial_signs(F, lt, ρ, E)) ∈ G",
									By(positive[3], legality, ordered_ring_formula.OrderedRingFormulaEvalDef))
								xm := c.MemberOf[on.Any](x, inCarrier)
								zm := c.MemberOf[on.Any](c.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
								atomE := ordered_ring_formula.OrderedRingFormulaAtomDef.At(
									F, lt, c.TermAs[IntegerPolynomial]("e"), ρ)
								atomNegated := ordered_ring_formula.OrderedRingFormulaAtomDef.At(
									F, lt, c.TermAs[IntegerPolynomial]("λm:(num → num). -e(m)"), ρ)
								reverses := ordered_field.NegationReversesSign.Read(ordered).At(xm)
								values := ordered_field.SignValues.Read(ordered).At(xm)
								c.Do(Simp(
									Fwd(signs),
									Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef),
									Fwd(first_order.ImpliesSemantics),
									Fwd(first_order.EvalDef)))
								c.Cases(c.Term("lt(integer_polynomial_eval(field_ring(F), ρ, e), F.zero)"))
								c.When(
									"x is negative, with sign −1: the formula answers with χ₁",
									func(d *Argument, below Fact) {
										sign := d.Have(
											"the sign of x is −1",
											"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, e)) = -1",
											By(below, values))
										d.Show(
											"so G holds the sign vector of cons(e, E) exactly where χ₁ holds",
											By(sign, below, behindNegative, atomE))
									})
								c.Otherwise(
									"x is not negative",
									func(d *Argument, notBelow Fact) {
										d.Cases(d.Term("lt(F.zero, integer_polynomial_eval(field_ring(F), ρ, e))"))
										d.When(
											"x is positive, with sign 1, and −x is negative: the formula answers with χ₃",
											func(f *Argument, above Fact) {
												sign := f.Have(
													"the sign of x is 1",
													"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, e)) = 1",
													By(above, values))
												f.Show(
													"so G holds the sign vector of cons(e, E) exactly where χ₃ holds",
													By(sign, notBelow, above, behindPositive, negation, atomE, atomNegated, reverses))
											})
										d.Otherwise(
											"x is zero, with sign 0, and −x is not negative: the formula answers with χ₂",
											func(f *Argument, notAbove Fact) {
												vanishes := f.Have(
													"x is zero, being neither below nor above it",
													"integer_polynomial_eval(field_ring(F), ρ, e) = F.zero",
													By(notBelow, notAbove, ordered_field.Trichotomy.Read(ordered).At(xm, zm)))
												sign := f.Have(
													"so the sign of x is 0",
													"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, e)) = 0",
													By(vanishes, values))
												f.Show(
													"so G holds the sign vector of cons(e, E) exactly where χ₂ holds",
													By(sign, notBelow, notAbove, behindZero, negation, atomE, atomNegated, reverses))
											})
									})
							}))))
			})
	}),
})}

// OneVariableElimination — one existential over a valid quantifier-free
// formula φ is eliminated uniformly over real closed fields, leaving neither
// its name nor any new free name. List the atoms of φ in P, polynomials in
// the parameters and v. Realizable sign control gives parameter polynomials E
// and a rule B, chosen before any field, with the sign vectors P takes along
// v the rows B assigns to the sign vector of E. Since φ reads its truth off
// the signs of its atoms, ∃v. φ holds exactly when a row admitted by φ
// appears, that is when the sign vector of E lies in the set G of sign
// vectors whose rows admit one; a quantifier-free formula in the parameters
// cuts out G.
var OneVariableElimination = oneVariableEliminationThm{family.Add(registry.ProofEntry{
	Name: "OneVariableElimination",
	Key:  "prop_2939c30f5142ad08",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int). ∀v:num.",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
			"fo_qf(φ)",
		},
		Conclusion: "∃ψ:fo_formula((num → num) → int). " +
			"    fo_quantifier_free_equivalent(«realClosed», " +
			"        «carrier», " +
			"        «negative», " +
			"        integer_polynomial, " +
			"        integer_polynomial_vars, " +
			"        fo_exists(v, φ), " +
			"        ψ)",
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], v *Expr[Nat], wf, qf Fact) {
		type polynomials = List[IntegerPolynomial]
		type signVectors = Set[List[Int]]
		P, atomsListed := a.UnpackAs[polynomials](
			GroupPremises(wf, qf, polynomial_formula.AtomList.At(φ)), "P")
		listed := a.Conjuncts(
			atomsListed,
			"P lists valid polynomials in the free variables of φ",
			"P holds every atom of φ")
		parameters := a.TermAs[Set[Nat]]("polynomial_formula_fv(φ) ∖ {v}")
		inFreeVariables := a.Unfolded(listed[0], polynomial_formula.PolynomialListOverDef)
		overAll := a.Have(
			"P lists valid polynomials in the parameters and v",
			"polynomial_list_over((polynomial_formula_fv(φ) ∖ {v}) ∪ {v}, P)",
			Unfold(polynomial_formula.PolynomialListOverDef),
			BySets(inFreeVariables))
		E, _, controlled := a.Unpack2As[polynomials, Fun[List[Int], signVectors]](
			GroupPremises(
				overAll,
				uniform_sign_table.RealizableSignControl.Inst[A]().At(parameters, v, P)),
			"E",
			"B")
		control := a.Conjuncts(
			controlled,
			"E lists valid polynomials in the parameters",
			"in a real closed field the sign vectors P takes "+
				"along v are the rows B assigns to the sign vector of E")
		admitted, admittedDef := a.LetAs[signVectors](
			"G",
			"{s:list(int) | "+
				"    ∃σ:(((num → num) → int) → int). "+
				"        list_map(σ, P) ∈ B(s) ∧ "+
				"        fo_eval(𝕌, λp:((num → num) → int). λτ:(num → num). σ(p) = -1, λn:num. 0, φ)}")
		χ, cutOut := a.UnpackAs[Formula[IntegerPolynomial]](
			GroupPremises(control[0], SignConditionFormula.Inst[A]().At(parameters, E, admitted)),
			"χ")
		formula := a.Conjuncts(
			cutOut,
			"χ is valid",
			"χ is quantifier-free",
			"χ is in the parameters",
			"in an ordered field χ holds exactly where G holds the sign vector of E")
		explicit := a.Have(
			"χ is valid and quantifier-free in the parameters, "+
				"and agrees with ∃v. φ in every real closed field",
			"polynomial_formula_wf(χ) ∧ "+
				"fo_qf(χ) ∧ "+
				"polynomial_formula_fv(χ) ⊆ polynomial_formula_fv(φ) ∖ {v} ∧ "+
				"(∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). "+
				"    real_closed_field(F, lt) ∧ fo_env_ok(F.carrier, polynomial_formula_fv(φ) ∖ {v}, ρ) ⇒ "+
				"    (ordered_ring_formula_eval(F, lt, ρ, fo_exists(v, φ)) ⇔ "+
				"        ordered_ring_formula_eval(F, lt, ρ, χ)))",
			SplitConj(
				Case(
					"χ is valid and quantifier-free in the parameters",
					By(formula[0], formula[1], formula[2])),
				Case(
					"in a real closed field ∃v. φ holds exactly where the sign vector of E lies in G, where χ holds",
					Derive(func(b *Argument) {
						F := b.FixAs[FieldOps[A]]("F")
						lt := b.FixAs[Fun2[A, A, Bool]]("lt")
						b.FixAs[Fun[Nat, A]]("ρ")
						legality := b.Assume()
						parts := b.Conjuncts(
							legality,
							"F is real closed under lt",
							"ρ is legal on the parameters")
						closed, legal := parts[0], parts[1]
						tells := b.Have(
							"χ holds exactly where G holds the sign vector of E, F being an ordered field",
							"ordered_ring_formula_eval(F, lt, ρ, χ) ⇔ polynomial_signs(F, lt, ρ, E) ∈ G",
							By(formula[3], real_closed_field.OrderedFieldOn.Read(closed), legal))
						rows := b.Have(
							"the sign vectors P takes along v are the rows B assigns to the sign vector of E",
							"realizable_polynomial_signs(F, lt, ρ, v, P) = B(polynomial_signs(F, lt, ρ, E))",
							By(control[1], closed, legal))
						along := b.Have(
							"∃v. φ holds at ρ exactly where φ holds at ρ updated at v by a point of the carrier",
							"ordered_ring_formula_eval(F, lt, ρ, fo_exists(v, φ)) ⇔ "+
								"∃x:A. x ∈ F.carrier ∧ ordered_ring_formula_eval(F, lt, fo_update(ρ, v, x), φ)",
							Simp(Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef), Fwd(first_order.EvalDef)),
							Basic())
						b.Do(Simp(Fwd(along), Fwd(tells), Fwd(admittedDef)))
						b.Iff()
						b.Forward(
							"a point x where φ holds gives the sign assignment of the polynomials at ρ updated by x",
							func(c *Argument, holds Fact) {
								_, at := c.UnpackAs[A](holds, "x")
								atX := c.Conjuncts(
									at,
									"x lies in the carrier",
									"φ holds at ρ updated by x")
								updated := c.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")
								σ := c.TermAs[Fun[IntegerPolynomial, Int]](
									"λp:((num → num) → int). " +
										"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), p))")
								assignment := c.Have(
									"the sign assignment at ρ updated by x lists along P "+
										"a row B assigns to the sign vector of E, and admits φ",
									"∃σ:(((num → num) → int) → int). "+
										"    list_map(σ, P) ∈ B(polynomial_signs(F, lt, ρ, E)) ∧ "+
										"    fo_eval(𝕌, λp:((num → num) → int). λτ:(num → num). σ(p) = -1, λn:num. 0, φ)",
									Derive(func(d *Argument) {
										d.Take(σ)
										d.Show(
											"its list along P is the sign vector of P at the update, and φ holds under it",
											SplitConj(
												Case(
													"the sign vector of P at the update is a row realized by x",
													Simp(Rev(rows), Fwd(polynomial_sign_table.RealizableSignsDef)),
													By(atX[0], polynomial_sign_table.SignsDef.At(F, lt, updated, P))),
												Case(
													"φ holds at the update, so under the signs of its atoms there",
													By(
														atX[1],
														qf,
														listed[1],
														polynomial_sign_table.SignsDef.At(F, lt, updated, P),
														SignVectorValue.At(F, lt, updated, P, σ, φ)))))
									}))
								c.Show(
									"so the sign vector of E lies in G",
									By(assignment))
							})
						b.Backward(
							"a sign assignment admitting φ whose list along P is a row realized at some x makes φ hold at x",
							func(c *Argument, admits Fact) {
								σ, assigned := c.UnpackAs[Fun[IntegerPolynomial, Int]](admits, "σ")
								parts := c.Conjuncts(
									assigned,
									"the list of σ along P is a row B assigns to the sign vector of E",
									"φ holds under σ")
								x, realized := c.UnpackAs[A](
									c.Simplified(parts[0], Rev(rows), Fwd(polynomial_sign_table.RealizableSignsDef)),
									"x")
								atX := c.Conjuncts(
									realized,
									"x lies in the carrier",
									"the list of σ along P is the sign vector of P at ρ updated by x")
								c.Take(x)
								c.Show(
									"so φ holds at ρ updated by x",
									By(
										atX[0],
										atX[1],
										parts[1],
										qf,
										listed[1],
										SignVectorValue.At(F, lt, c.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)"), P, σ, φ)))
							})
					}))))
		a.Take(χ)
		a.Show(
			"so χ is a quantifier-free equivalent of ∃v. φ over the real closed pairs",
			first_order.QuantifierFreeEquivalent.Intro(
				Simp(Fwd(pairs.ForallPair), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				Simp(Fwd(first_order.FreeVarsDef)),
				Simp(
					Rev(polynomial_formula.FormulaValidDef),
					Rev(polynomial_formula.FormulaVarsDef),
					Rev(ordered_ring_formula.OrderedRingFormulaEvalDef)),
				By(explicit)))
	}),
})}

// QuantifierElimination — every ordered-ring formula has a uniform
// support-preserving quantifier-free equivalent over real closed fields: the
// models are the pairs of a field and its order, real closed, reading an atom
// as negativity. Over those pairs one existential is eliminated by
// OneVariableElimination at the pair's field and order, so
// first_order.QuantifierEliminationFromOne gives every well-formed formula an
// equivalent, chosen before any model; a quantifier over the pairs is a
// quantifier over a field and an order, which is the claim.
var QuantifierElimination = quantifierEliminationThm{family.Add(registry.ProofEntry{
	Name: "QuantifierElimination",
	Key:  "prop_a366bd1cbe780746",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
		},
		Conclusion: "∃ψ:fo_formula((num → num) → int). " +
			"    fo_quantifier_free_equivalent(«realClosed», " +
			"        «carrier», " +
			"        «negative», " +
			"        integer_polynomial, " +
			"        integer_polynomial_vars, " +
			"        φ, " +
			"        ψ)",
	}, func(a *Argument) {
		type model = Prod[FieldOps[A], Fun2[A, A, Bool]]
		eliminatesOne := a.Have(
			"over the real closed pairs one existential is eliminated, by OneVariableElimination",
			"fo_one_qe(«realClosed», «carrier», «negative», integer_polynomial, integer_polynomial_vars)",
			Unfold(first_order.OneVariableEliminationDef),
			Simp(Rev(polynomial_formula.FormulaValidDef)),
			Cite(OneVariableElimination))
		eliminates := a.Unfolded(
			GroupPremises(
				eliminatesOne,
				first_order.QuantifierEliminationFromOne.At(
					a.TermAs[Set[model]]("«realClosed»"),
					a.TermAs[Fun2[model, A, Bool]]("«carrier»"),
					a.TermAs[Fun3[model, IntegerPolynomial, Fun[Nat, A], Bool]]("«negative»"),
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"))),
			first_order.QuantifierEliminationDef)
		a.Show(
			"every well-formed formula has its equivalent over the real closed pairs",
			By(eliminates, polynomial_formula.FormulaValidDef))
	}),
})}
