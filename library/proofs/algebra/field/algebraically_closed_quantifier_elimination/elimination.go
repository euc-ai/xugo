// elimination.go — the formulas: a quantifier-free formula in the
// parameters cuts out the decided patterns, which eliminates one
// existential, and first_order.QuantifierEliminationFromOne lifts that to
// every quantifier.

package algebraically_closed_quantifier_elimination

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ZeroPatternValue — a quantifier-free formula whose atoms lie in a list P
// takes the value the zero pattern of P gives it: read through any truth
// assignment σ whose list along P is the zero pattern of P, an atom p holding
// exactly when σ(p) does. σ and the atom test have one image list along P,
// so they agree on every member of P (MapAgreesOnMembers), so on every atom
// of φ.
var ZeroPatternValue = zeroPatternValueThm{family.Add(registry.ProofEntry{
	Name: "ZeroPatternValue",
	Key:  "prop_bbaae90853ab009a",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀ρ:(num → A). " +
			"∀P:list((num → num) → int). " +
			"∀σ:(((num → num) → int) → bool). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"fo_qf(φ)",
			"fo_wf(λp:((num → num) → int). list_member(p, P), φ)",
			"polynomial_zero_pattern(F, ρ, P) = list_map(σ, P)",
		},
		Conclusion: "ring_formula_eval(F, ρ, φ) ⇔ " +
			"fo_eval(𝕌, λp:((num → num) → int). λτ:(num → num). σ(p), λn:num. 0, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		ρ *Arrow[Nat, A],
		P *Expr[List[IntegerPolynomial]],
		σ *Arrow[IntegerPolynomial, Bool],
		φ *Expr[Formula[IntegerPolynomial]],
		qf, atoms, pattern Fact,
	) {
		agree := a.Have(
			"on a member p of P the atom p = 0 holds exactly when σ(p) does",
			"∀p:((num → num) → int). list_member(p, P) ⇒ (ring_formula_atom(F, p, ρ) ⇔ σ(p))",
			Derive(func(b *Argument) {
				p := b.FixAs[IntegerPolynomial]("p")
				member := b.Assume()
				b.Show(
					"σ and the atom test have one image list along P, the zero pattern of P",
					By(
						Normalized,
						pattern,
						member,
						zeroPatternDef.At(F, ρ, P),
						list.MapAgreesOnMembers.At(
							σ,
							b.TermAs[Fun[IntegerPolynomial, Bool]]("λq:((num → num) → int). ring_formula_atom(F, q, ρ)"),
							P,
							p)))
			}))
		a.Show(
			"so the ring atoms and the pattern reading give φ one value",
			Simp(Fwd(ring_formula.RingFormulaEvalDef)),
			By(
				qf,
				atoms,
				agree,
				first_order.QuantifierFreeAtomAgreement.At(
					a.TermAs[Set[IntegerPolynomial]]("λq:((num → num) → int). list_member(q, P)"),
					a.TermAs[Set[A]]("F.carrier"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, A], Bool]]("ring_formula_atom(F)"),
					ρ,
					a.TermAs[Set[Nat]]("𝕌"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, Nat], Bool]](
						"λq:((num → num) → int). λτ:(num → num). σ(q)"),
					a.TermAs[Fun[Nat, Nat]]("λn:num. 0"),
					φ)))
	}),
})}

// ZeroConditionFormula — every set G of zero patterns of a list E of valid
// polynomials in the variables U is cut out by a valid quantifier-free formula
// in those variables, at every field and environment: by induction on E. The
// empty list has the one zero pattern nil, and a constant formula says
// whether G holds it. In front of a tail, the head e vanishes or does not; the
// formula asks which, and answers with the tail's formula for the patterns G
// holds behind that answer.
var ZeroConditionFormula = zeroConditionFormulaThm{family.Add(registry.ProofEntry{
	Name: "ZeroConditionFormula",
	Key:  "prop_d6c19751ac8e7c2a",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀E:list((num → num) → int). ∀G:set(list(bool)).",
		Hypotheses: []string{
			"polynomial_list_over(U, E)",
		},
		Conclusion: "∃χ:fo_formula((num → num) → int). " +
			"    polynomial_formula_wf(χ) ∧ " +
			"    fo_qf(χ) ∧ " +
			"    polynomial_formula_fv(χ) ⊆ U ∧ " +
			"    (∀F:field_ops(A). ∀ρ:(num → A). " +
			"        ring_formula_eval(F, ρ, χ) ⇔ polynomial_zero_pattern(F, ρ, E) ∈ G)",
	}, func(a *Argument, U *Expr[Set[Nat]], E *Expr[List[IntegerPolynomial]]) {
		type patterns = Set[List[Bool]]
		a.Induct(E)
		a.Base(
			"the empty list has the one zero pattern nil, and a constant formula says whether G holds it",
			func(b *Argument) {
				b.FixAs[patterns]("G")
				b.Assume()
				χ, constant := b.Unpack(
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
						"closed, and the zero pattern of the empty list is nil",
					By(
						Normalized,
						constant,
						zeroPatternDef,
						list.ListMapDef,
						set_order.EmptySubset,
						polynomial_formula.FormulaValidDef,
						polynomial_formula.FormulaVarsDef,
						ring_formula.RingFormulaEvalDef))
			})
		a.Step(
			"a head e in front of the tail: ask whether e vanishes, "+
				"and answer with the tail's formula behind that answer",
			func(b *Argument, ih Fact) {
				b.StepArgs("e", "E")
				b.FixAs[patterns]("G")
				over := b.Assume()
				head := b.Have(
					"the head e is a valid polynomial in the variables U",
					"integer_polynomial(e) ∧ integer_polynomial_vars(e) ⊆ U",
					By(over, polynomial_formula.PolynomialListOverDef, list.ListMemberDef))
				tail := b.Have(
					"and the tail lists valid polynomials in the variables U",
					"polynomial_list_over(U, E)",
					By(over, polynomial_formula.PolynomialListOverDef, list.ListMemberDef))
				_, zeroTail := b.Unpack(
					GroupPremises(tail, ih.At(b.TermAs[patterns]("{s:list(bool) | cons(⊤, s) ∈ G}"))),
					"χ₁")
				_, nonzeroTail := b.Unpack(
					GroupPremises(tail, ih.At(b.TermAs[patterns]("{s:list(bool) | cons(⊥, s) ∈ G}"))),
					"χ₂")
				zero := b.Conjuncts(
					zeroTail,
					"χ₁ is valid",
					"χ₁ is quantifier-free",
					"χ₁ is in the variables U",
					"χ₁ holds where G holds the zero pattern of the tail behind ⊤")
				nonzero := b.Conjuncts(
					nonzeroTail,
					"χ₂ is valid",
					"χ₂ is quantifier-free",
					"χ₂ is in the variables U",
					"χ₂ holds where G holds the zero pattern of the tail behind ⊥")
				b.Take(b.TermAs[Formula[IntegerPolynomial]](
					"fo_and(fo_implies(fo_atom(e), χ₁), fo_implies(fo_not(fo_atom(e)), χ₂))"))
				b.Show(
					"the formula asking whether e vanishes is valid and "+
						"quantifier-free in the variables U, and tells the patterns G holds",
					SplitConj(
						Case(
							"it is built from e and the two tail formulas, all valid and quantifier-free in the variables U",
							Simp(
								Fwd(polynomial_formula.FormulaValidDef),
								Fwd(polynomial_formula.FormulaVarsDef),
								Fwd(first_order.ImpliesDef),
								Fwd(first_order.WellFormedDef),
								Fwd(first_order.QuantifierFreeDef),
								Fwd(first_order.FreeVarsDef)),
							BySets(
								head,
								zero[0],
								zero[1],
								zero[2],
								nonzero[0],
								nonzero[1],
								nonzero[2],
								polynomial_formula.FormulaValidDef,
								polynomial_formula.FormulaVarsDef)),
						Case(
							"at every field the formula holds exactly where G holds the zero pattern of cons(e, E)",
							Derive(func(c *Argument) {
								c.FixAs[FieldOps[A]]("F")
								c.FixAs[Fun[Nat, A]]("ρ")
								pattern := c.Have(
									"the zero pattern of cons(e, E) is the atom of e in front of the zero pattern of E",
									"polynomial_zero_pattern(F, ρ, cons(e, E)) = "+
										"cons(ring_formula_atom(F, e, ρ), polynomial_zero_pattern(F, ρ, E))",
									Simp(Fwd(zeroPatternDef), Fwd(list.ListMapDef)),
									Basic())
								behindZero := c.Have(
									"χ₁ holds exactly where G holds the zero pattern of E behind ⊤",
									"fo_eval(F.carrier, ring_formula_atom(F), ρ, χ₁) ⇔ cons(⊤, polynomial_zero_pattern(F, ρ, E)) ∈ G",
									By(zero[3], ring_formula.RingFormulaEvalDef))
								behindNonzero := c.Have(
									"χ₂ holds exactly where G holds it behind ⊥",
									"fo_eval(F.carrier, ring_formula_atom(F), ρ, χ₂) ⇔ cons(⊥, polynomial_zero_pattern(F, ρ, E)) ∈ G",
									By(nonzero[3], ring_formula.RingFormulaEvalDef))
								c.Do(Simp(
									Fwd(pattern),
									Fwd(ring_formula.RingFormulaEvalDef),
									Fwd(first_order.ImpliesDef),
									Fwd(first_order.EvalDef)))
								c.Cases(c.Term("ring_formula_atom(F, e, ρ)"))
								c.When(
									"e vanishes: the formula answers with χ₁",
									func(d *Argument, vanishes Fact) {
										d.Show(
											"so G holds the zero pattern of cons(e, E) exactly where χ₁ holds",
											By(Normalized, vanishes, behindZero))
									})
								c.Otherwise(
									"e does not vanish: the formula answers with χ₂",
									func(d *Argument, survives Fact) {
										d.Show(
											"so G holds the zero pattern of cons(e, E) exactly where χ₂ holds",
											By(Normalized, survives, behindNonzero))
									})
							}))))
			})
	}),
})}

// OneVariableElimination — one existential over a valid quantifier-free
// formula φ is eliminated uniformly over algebraically closed fields, leaving
// neither its name nor any new free name. List the atoms of φ in P,
// polynomials in the parameters and v. ParameterizedZeroPatterns gives
// parameter polynomials E and a rule B, chosen before any field, with the zero
// patterns P takes along v the patterns B assigns to the zero pattern of E.
// Since φ reads its truth off the zero pattern of its atoms
// (ZeroPatternValue), ∃v. φ holds exactly when a pattern admitted by φ
// appears, that is when the zero pattern of E lies in the set G of patterns
// whose B admits one; a quantifier-free formula in the parameters cuts out G
// (ZeroConditionFormula).
var OneVariableElimination = oneVariableEliminationThm{family.Add(registry.ProofEntry{
	Name: "OneVariableElimination",
	Key:  "prop_26326d0b7e159820",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int). ∀v:num.",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
			"fo_qf(φ)",
		},
		Conclusion: "∃ψ:fo_formula((num → num) → int). " +
			"    fo_quantifier_free_equivalent(algebraically_closed_field_on, " +
			"        λF:field_ops(A). F.carrier, " +
			"        ring_formula_atom, " +
			"        integer_polynomial, " +
			"        integer_polynomial_vars, " +
			"        fo_exists(v, φ), " +
			"        ψ)",
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], v *Expr[Nat], wf, qf Fact) {
		type polynomials = List[IntegerPolynomial]
		type patterns = Set[List[Bool]]
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
		E, _, controlled := a.Unpack2As[polynomials, Fun[List[Bool], patterns]](
			GroupPremises(overAll, ParameterizedZeroPatterns.Inst[A]().At(parameters, v, P)),
			"E",
			"B")
		control := a.Conjuncts(
			controlled,
			"E lists valid polynomials in the parameters",
			"each B(s) is a finite set of patterns of the length of P",
			"in an algebraically closed field the zero patterns P takes along v are B of the zero pattern of E")
		admitted, admittedDef := a.LetAs[patterns](
			"G",
			"{s:list(bool) | "+
				"    ∃σ:(((num → num) → int) → bool). "+
				"        list_map(σ, P) ∈ B(s) ∧ "+
				"        fo_eval(𝕌, λp:((num → num) → int). λτ:(num → num). σ(p), λn:num. 0, φ)}")
		χ, cutOut := a.Unpack(
			GroupPremises(control[0], ZeroConditionFormula.Inst[A]().At(parameters, E, admitted)),
			"χ")
		formula := a.Conjuncts(
			cutOut,
			"χ is valid",
			"χ is quantifier-free",
			"χ is in the parameters",
			"at every field χ holds exactly where G holds the zero pattern of E")
		explicit := a.Have(
			"χ is valid and quantifier-free in the parameters, and "+
				"agrees with ∃v. φ in every algebraically closed field",
			"polynomial_formula_wf(χ) ∧ "+
				"fo_qf(χ) ∧ "+
				"polynomial_formula_fv(χ) ⊆ polynomial_formula_fv(φ) ∖ {v} ∧ "+
				"(∀F:field_ops(A). ∀ρ:(num → A). "+
				"    algebraically_closed_field_on(F) ∧ "+
				"    fo_env_ok(F.carrier, polynomial_formula_fv(φ) ∖ {v}, ρ) ⇒ "+
				"    (ring_formula_eval(F, ρ, fo_exists(v, φ)) ⇔ ring_formula_eval(F, ρ, χ)))",
			SplitConj(
				Case(
					"χ is valid and quantifier-free in the parameters",
					By(formula[0], formula[1], formula[2])),
				Case(
					"in an algebraically closed field ∃v. φ holds exactly "+
						"where the zero pattern of E lies in G, where χ holds",
					Derive(func(b *Argument) {
						F := b.FixAs[FieldOps[A]]("F")
						b.FixAs[Fun[Nat, A]]("ρ")
						legality := b.Assume()
						tells := b.Have(
							"χ holds exactly where G holds the zero pattern of E",
							"ring_formula_eval(F, ρ, χ) ⇔ polynomial_zero_pattern(F, ρ, E) ∈ G",
							By(formula[3]))
						rows := b.Have(
							"the zero patterns P takes along v are B of the zero pattern of E",
							"{polynomial_zero_pattern(F, fo_update(ρ, v, x), P) | x:A | x ∈ F.carrier} = "+
								"B(polynomial_zero_pattern(F, ρ, E))",
							By(control[2], legality))
						along := b.Have(
							"∃v. φ holds at ρ exactly where φ holds at ρ updated at v by a point of the carrier",
							"ring_formula_eval(F, ρ, fo_exists(v, φ)) ⇔ "+
								"∃x:A. x ∈ F.carrier ∧ ring_formula_eval(F, fo_update(ρ, v, x), φ)",
							Simp(Fwd(ring_formula.RingFormulaEvalDef), Fwd(first_order.EvalDef)),
							Basic())
						b.Do(Simp(Fwd(along), Fwd(tells), Fwd(admittedDef)))
						b.Iff()
						b.Forward(
							"a point x where φ holds gives the truth assignment of the atoms at ρ updated by x",
							func(c *Argument, holds Fact) {
								_, at := c.UnpackAs[A](holds, "x")
								atX := c.Conjuncts(
									at,
									"x lies in the carrier",
									"φ holds at ρ updated by x")
								updated := c.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")
								σ := c.TermAs[Fun[IntegerPolynomial, Bool]](
									"λp:((num → num) → int). ring_formula_atom(F, p, fo_update(ρ, v, x))")
								assignment := c.Have(
									"the truth assignment at ρ updated by x lists along P a "+
										"pattern B assigns to the zero pattern of E, and admits φ",
									"∃σ:(((num → num) → int) → bool). "+
										"    list_map(σ, P) ∈ B(polynomial_zero_pattern(F, ρ, E)) ∧ "+
										"    fo_eval(𝕌, λp:((num → num) → int). λτ:(num → num). σ(p), λn:num. 0, φ)",
									Derive(func(d *Argument) {
										d.Take(σ)
										d.Show(
											"its list along P is the zero pattern of P at the update, and φ holds under it",
											SplitConj(
												Case(
													"the zero pattern of P at the update is a pattern realized by x",
													Simp(Rev(rows)),
													By(atX[0], zeroPatternDef.At(F, updated, P))),
												Case(
													"φ holds at the update, so under the zero pattern of its atoms there",
													By(
														atX[1],
														qf,
														listed[1],
														zeroPatternDef.At(F, updated, P),
														ZeroPatternValue.At(F, updated, P, σ, φ)))))
									}))
								c.Show(
									"so the zero pattern of E lies in G",
									By(assignment))
							})
						b.Backward(
							"a truth assignment admitting φ whose list along P "+
								"is a pattern realized at some x makes φ hold at x",
							func(c *Argument, admits Fact) {
								σ, assigned := c.UnpackAs[Fun[IntegerPolynomial, Bool]](admits, "σ")
								parts := c.Conjuncts(
									assigned,
									"the list of σ along P is a pattern B assigns to the zero pattern of E",
									"φ holds under σ")
								x, realized := c.UnpackAs[A](
									c.Simplified(parts[0], Rev(rows)),
									"x")
								atX := c.Conjuncts(
									realized,
									"x lies in the carrier",
									"the list of σ along P is the zero pattern of P at ρ updated by x")
								c.Take(x)
								c.Show(
									"so φ holds at ρ updated by x",
									By(
										atX[0],
										atX[1],
										parts[1],
										qf,
										listed[1],
										ZeroPatternValue.At(F, c.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)"), P, σ, φ)))
							})
					}))))
		a.Take(χ)
		a.Show(
			"so χ is a quantifier-free equivalent of ∃v. φ over the algebraically closed fields",
			first_order.QuantifierFreeEquivalent.Intro(
				Simp(Fwd(first_order.FreeVarsDef)),
				Simp(
					Rev(polynomial_formula.FormulaValidDef),
					Rev(polynomial_formula.FormulaVarsDef),
					Rev(ring_formula.RingFormulaEvalDef)),
				By(explicit)))
	}),
})}

// QuantifierElimination — every ring formula has a uniform
// support-preserving quantifier-free equivalent over algebraically closed
// fields: the models are the algebraically closed fields themselves, reading
// an atom as vanishing. Over them one existential is eliminated by
// OneVariableElimination, so first_order.QuantifierEliminationFromOne, which
// lifts the elimination of one existential to every formula by induction on
// it, gives every well-formed formula an equivalent, chosen before any field.
var QuantifierElimination = quantifierEliminationThm{family.Add(registry.ProofEntry{
	Name: "QuantifierElimination",
	Key:  "prop_3cc792423cc7b350",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
		},
		Conclusion: "∃ψ:fo_formula((num → num) → int). " +
			"    fo_quantifier_free_equivalent(algebraically_closed_field_on, " +
			"        λF:field_ops(A). F.carrier, " +
			"        ring_formula_atom, " +
			"        integer_polynomial, " +
			"        integer_polynomial_vars, " +
			"        φ, " +
			"        ψ)",
	}, func(a *Argument) {
		eliminatesOne := a.Have(
			"over the algebraically closed fields one existential is eliminated, by OneVariableElimination",
			"fo_one_qe(algebraically_closed_field_on, "+
				"    λF:field_ops(A). F.carrier, "+
				"    ring_formula_atom, "+
				"    integer_polynomial, "+
				"    integer_polynomial_vars)",
			Unfold(first_order.OneVariableEliminationDef),
			Simp(Rev(polynomial_formula.FormulaValidDef)),
			Cite(OneVariableElimination))
		eliminates := a.Unfolded(
			GroupPremises(
				eliminatesOne,
				first_order.QuantifierEliminationFromOne.At(
					a.TermAs[Set[FieldOps[A]]]("algebraically_closed_field_on"),
					a.TermAs[Fun2[FieldOps[A], A, Bool]]("λF:field_ops(A). F.carrier"),
					a.TermAs[Fun3[FieldOps[A], IntegerPolynomial, Fun[Nat, A], Bool]]("ring_formula_atom"),
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"))),
			first_order.QuantifierEliminationDef)
		a.Show(
			"every well-formed formula has its equivalent over the algebraically closed fields",
			By(eliminates, polynomial_formula.FormulaValidDef))
	}),
})}
