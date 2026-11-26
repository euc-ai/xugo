// zero_patterns.go — the parametric decision: whether a system of equations
// and one inequation in v has a solution is decided by the zero pattern of
// finitely many parameter polynomials, and so are the zero patterns a list
// takes along v.

package algebraically_closed_quantifier_elimination

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/listing"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// zeroPatternDef — the zero pattern of a list of integer polynomials at a
// field F and an environment ρ: the list of their atoms' truth values, ⊤ at
// a polynomial that vanishes at ρ and ⊥ at one that does not
// (ring_formula.RingFormulaAtomDef).
var zeroPatternDef = zeroPatternDefThm{family.Define(registry.DefEntry{
	Name:  "zeroPatternDef",
	Const: "polynomial_zero_pattern",
	Type:  "field_ops(A) → (num → A) → list((num → num) → int) → list(bool)",
	Key:   "prop_bdbdb4b49c5c0826",
	Equations: []string{
		"∀F:field_ops(A). ∀ρ:(num → A). ∀P:list((num → num) → int). " +
			"    polynomial_zero_pattern(F, ρ, P) = " +
			"    list_map(λp:((num → num) → int). ring_formula_atom(F, p, ρ), P)",
	},
})}

// zeroPatternDecidesDef — `zero_pattern_decides(E, M, Φ)`: on the models
// M, the zero pattern of the list E decides a property Φ of a field and an
// environment: some set D of patterns has Φ(F, ρ) hold, at every model F, ρ
// of M, exactly when the zero pattern of E at F and ρ lies in D.
var zeroPatternDecidesDef = zeroPatternDecidesDefThm{family.Define(registry.DefEntry{
	Name:  "zeroPatternDecidesDef",
	Key:   "prop_60b42f6bc945d132",
	Const: "zero_pattern_decides",
	Type: "list((num → num) → int) → " +
		"(field_ops(A) → (num → A) → bool) → " +
		"(field_ops(A) → (num → A) → bool) → " +
		"bool",
	Equations: []string{
		"∀E:list((num → num) → int). ∀M Φ:(field_ops(A) → (num → A) → bool). " +
			"    zero_pattern_decides(E, M, Φ) ⇔ " +
			"    ∃D:set(list(bool)). ∀F:field_ops(A). ∀ρ:(num → A). " +
			"        M(F, ρ) ⇒ (Φ(F, ρ) ⇔ polynomial_zero_pattern(F, ρ, E) ∈ D)",
	},
	Deps: []registry.EntryLike{zeroPatternDef},
})}

// decidedByZeroPatternsDef — `decided_by_zero_patterns(U, M, Φ)`: on the
// models M, a property Φ of a field and an environment is decided by the
// zero pattern of some list E of integer polynomials in the variables U.
// The models a decision ranges over are those of «models», or of
// «vanishes»(c) and «survives»(c) when a parameter polynomial c is
// branched on.
var decidedByZeroPatternsDef = decidedByZeroPatternsDefThm{family.Define(registry.DefEntry{
	Name:  "decidedByZeroPatternsDef",
	Key:   "prop_69435aa42294c7a4",
	Const: "decided_by_zero_patterns",
	Type: "set(num) → " +
		"(field_ops(A) → (num → A) → bool) → " +
		"(field_ops(A) → (num → A) → bool) → " +
		"bool",
	Equations: []string{
		"∀U:set(num). ∀M Φ:(field_ops(A) → (num → A) → bool). " +
			"    decided_by_zero_patterns(U, M, Φ) ⇔ " +
			"    ∃E:list((num → num) → int). polynomial_list_over(U, E) ∧ zero_pattern_decides(E, M, Φ)",
	},
	Deps: []registry.EntryLike{zeroPatternDecidesDef},
})}

// ModelSpecialization — at a model of the decision, an algebraically closed
// field F with ρ assigning elements of F to the variables U, F is a field,
// and specialization at ρ is a ring homomorphism from the parameter
// polynomials into F (polynomial_formula.IntegerPolynomialEvalHom), which
// keeps zero.
var ModelSpecialization = modelSpecializationThm{family.Add(registry.ProofEntry{
	Name: "ModelSpecialization",
	Key:  "prop_734d577d82886bd9",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀F:field_ops(A). ∀ρ:(num → A).",
		Hypotheses: []string{
			"«models»(F, ρ)",
		},
		Conclusion: "field_on(F) ∧ " +
			"ring_homomorphism(«parameterRing»(U), " +
			"    field_ring(F), " +
			"    λq:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, q)) ∧ " +
			"integer_polynomial_eval(field_ring(F), ρ, integer_polynomial_ring.zero) = F.zero",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		F *Expr[FieldOps[A]],
		ρ *Arrow[Nat, A],
		closed, environment Fact,
	) {
		fieldOn := algebraic_closure.FieldOn.Read(closed)
		specialization := a.Have(
			"at the ring of F, a field, specialization at ρ is a ring homomorphism",
			"ring_homomorphism(«parameterRing»(U), "+
				"    field_ring(F), "+
				"    λq:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, q))",
			By(
				environment,
				polynomial_formula.IntegerPolynomialEvalHom.Read(field.RingOn.Read(fieldOn)).At(U, ρ)))
		a.Show(
			"F is a field, and the homomorphism keeps zero",
			By(fieldOn, specialization, ring_homomorphism.MapZero.Read(specialization)))
	}),
})}

// NoEquationDecision — with no equation, whether h is nonzero somewhere is
// decided by the zero pattern of finitely many parameter polynomials: E
// lists the coefficients h(0), …, h(n) of h up to its degree n, and D
// holds the patterns with an entry ⊥, those at which some coefficient does
// not vanish. Over an algebraically closed field the specialization of h
// is nonzero somewhere exactly when it is not zero
// (algebraic_closure.NonzeroValue), which is exactly when one of those
// coefficients does not specialize to zero.
var NoEquationDecision = noEquationDecisionThm{family.Add(registry.ProofEntry{
	Name: "NoEquationDecision",
	Key:  "prop_223528c2b94fe124",
	Reading: "E and D are chosen before the field and the environment. The statement needs of the " +
		"field only that it be infinite: over a field of q elements x^q − x vanishes everywhere without " +
		"being zero. The proof takes the closure route, algebraic_closure.NonzeroValue finding a root of " +
		"p·x − 1. With U empty the pattern records which integer constants vanish in the characteristic.",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀h:(num → ((num → num) → int)).",
		Hypotheses: []string{
			"«overParameters»(h)",
		},
		Conclusion: "decided_by_zero_patterns(U, «models», «nonzeroSomewhere»(h))",
	}, func(a *Argument, U *Expr[Set[Nat]], h *Arrow[Nat, IntegerPolynomial], over Fact) {
		vanishes := a.Have(
			"h vanishes past its degree",
			"vec⟨suc(polynomial_degree(integer_polynomial_ring.zero, h))⟩(integer_polynomial_ring.zero, h)",
			By(over, polynomial.DegreeVec))
		n, _ := a.LetAs[Nat]("n", "polynomial_degree(integer_polynomial_ring.zero, h)")
		l, listed := a.ObtainAs[List[Nat]](
			"finitely many indices stand up to n, so some list l lists them",
			"∃l:list(num). set_of_list(l) = {i:num | i ≤ n}",
			By(listing.FiniteIffListable, num_segment.FiniteBelow))
		indices := a.Have(
			"so the members of l are the indices up to n",
			"∀i:num. list_member(i, l) ⇔ i ≤ n",
			BySets(listed, listing.InSetOfList))
		E := a.TermAs[List[IntegerPolynomial]]("list_map(h, l)")
		a.Do(Unfold(decidedByZeroPatternsDef))
		a.Take(E)
		a.Show(
			"E lists the coefficients of h up to n, and D holds the zero patterns with a false entry",
			SplitConj(
				Case(
					"every member of E is a coefficient of h, so a parameter polynomial",
					Unfold(polynomial_formula.PolynomialListOverDef),
					Derive(func(b *Argument) {
						p := b.FixAs[IntegerPolynomial]("p")
						member := b.Assume()
						b.Show(
							"a member of E is h(i) for an index i in l",
							By(
								member,
								over,
								polynomial.PolynomialOverDef,
								list.MemberMap.At(h, p, l),
								polynomial_formula.PolynomialOnVariables.At(U, p)))
					})),
				Case(
					"over an algebraically closed field the pattern of E "+
						"has a false entry exactly when h is nonzero somewhere",
					Unfold(zeroPatternDecidesDef),
					Witness(a.TermAs[Set[List[Bool]]]("{t:list(bool) | list_member(⊥, t)}")),
					Derive(func(b *Argument) {
						F := b.FixAs[FieldOps[A]]("F")
						ρ := b.FixAs[Fun[Nat, A]]("ρ")
						given := b.Conjuncts(
							b.Assume(),
							"F is an algebraically closed field",
							"ρ assigns elements of F to the variables U")
						closed, environment := given[0], given[1]
						opened := b.Conjuncts(
							GroupPremises(closed, environment, ModelSpecialization.At(U, F, ρ)),
							"F is a field",
							"specialization at ρ is a ring homomorphism",
							"that keeps zero")
						fieldOn, keepsZero := opened[0], opened[2]
						specialized := b.Have(
							"h specializes at ρ to a polynomial over F",
							"polynomial_over(F.carrier, «specialized»(field_ring(F), ρ, h))",
							By(
								polynomial_formula.SpecializedPolynomial.Read(field.RingOn.Read(fieldOn)).At(U, ρ, h),
								environment,
								over))
						vanishing := b.Have(
							"specialization keeps zero, so the specialized polynomial vanishes past n too",
							"vec⟨suc(n)⟩(F.zero, «specialized»(field_ring(F), ρ, h))",
							By(
								vanishes,
								At(polynomial.VecMap,
									b.TermAs[Fun[IntegerPolynomial, A]](
										"λq:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, q)"),
									b.TermAs[IntegerPolynomial]("integer_polynomial_ring.zero"),
									b.TermAs[A]("F.zero"),
									b.TermAs[Nat]("suc(n)"),
									h),
								keepsZero))
						specializedH := b.TermAs[Fun[Nat, A]]("«specialized»(field_ring(F), ρ, h)")
						zero := b.TermAs[A]("F.zero")
						carrier := b.TermAs[Set[A]]("F.carrier")
						coefficients := b.Have(
							"the specialized polynomial is nonzero exactly when some "+
								"coefficient h(i), i ≤ n, specializes to a nonzero element",
							"«specialized»(field_ring(F), ρ, h) ≠ vec_zero ⇔ "+
								"∃i:num. i ≤ n ∧ integer_polynomial_eval(field_ring(F), ρ, h(i)) ≠ F.zero",
							Derive(func(c *Argument) {
								c.Iff()
								c.Forward(
									"a nonzero polynomial is nonzero at its degree, which is at most n",
									func(d *Argument, nonzero Fact) {
										d.Show(
											"its degree is such an index",
											Witness(d.TermAs[Nat]("polynomial_degree(«specialized»(field_ring(F), ρ, h))")),
											By(
												nonzero,
												specialized,
												vanishing,
												polynomial.DegreeLeast.At(zero, specializedH, n),
												polynomial.DegreeLeading.At(zero, carrier, specializedH)))
									})
								c.Backward(
									"a nonzero coefficient makes the specialized polynomial nonzero",
									func(d *Argument, some Fact) {
										d.Show(
											"the zero polynomial has every coefficient zero",
											By(some, vec_space.VecZeroDef))
									})
							}))
						test := b.TermAs[Fun[Nat, Bool]]("λi:num. ring_formula_atom(F, h(i), ρ)")
						fused := b.Have(
							"the zero pattern of E tests each coefficient h(i) along l",
							"polynomial_zero_pattern(F, ρ, list_map(h, l)) = "+
								"list_map(λi:num. ring_formula_atom(F, h(i), ρ), l)",
							By(
								zeroPatternDef.At(F, ρ, E),
								list.MapMap.At(
									h,
									b.TermAs[Fun[IntegerPolynomial, Bool]]("λp:((num → num) → int). ring_formula_atom(F, p, ρ)"),
									l)))
						pattern := b.Have(
							"the pattern has a false entry exactly when some "+
								"coefficient h(i), i ≤ n, specializes to a nonzero element",
							"polynomial_zero_pattern(F, ρ, list_map(h, l)) ∈ {t:list(bool) | list_member(⊥, t)} ⇔ "+
								"∃i:num. i ≤ n ∧ integer_polynomial_eval(field_ring(F), ρ, h(i)) ≠ F.zero",
							Derive(func(c *Argument) {
								falseEntry := list.MemberMap.At(test, c.TermAs[Bool]("⊥"), l)
								c.Iff()
								c.Forward(
									"a false entry is the test of a coefficient h(i) with i in l",
									func(d *Argument, member Fact) {
										i, failing := d.ObtainAs[Nat](
											"the false entry tests some h(i) with i in l",
											"∃i:num. list_member(i, l) ∧ ¬ring_formula_atom(F, h(i), ρ)",
											By(member, fused, falseEntry))
										at := d.Conjuncts(
											failing,
											"i is in l",
											"h(i) does not specialize to zero")
										d.Show(
											"so i ≤ n and h(i) specializes to a nonzero element",
											Witness(i),
											By(indices.At(i), at[0], at[1], ring_formula.RingFormulaAtomDef.At(F, h.Apply(i), ρ)))
									})
								c.Backward(
									"a coefficient h(i), i ≤ n, specializing to a nonzero element is a false entry",
									func(d *Argument, some Fact) {
										i, coefficient := d.UnpackAs[Nat](some, "i")
										d.Show(
											"its test is false and i is in l",
											By(
												coefficient,
												indices.At(i),
												fused,
												falseEntry,
												ring_formula.RingFormulaAtomDef.At(F, h.Apply(i), ρ)))
									})
							}))
						b.Show(
							"the specialization of h is nonzero somewhere exactly "+
								"when it is not zero, which the pattern decides",
							By(
								algebraic_closure.NonzeroValue.Read(closed).At(specializedH),
								specialized,
								coefficients,
								pattern))
					})),
			))
	}),
})}

// ZeroPatternAgreement — two zero patterns of one list are equal exactly
// when every member of the list vanishes at both or at neither: by
// induction on the list, the pattern of cons(p, E) being the atom of p in
// front of the pattern of E.
var ZeroPatternAgreement = zeroPatternAgreementThm{family.Add(registry.ProofEntry{
	Name: "ZeroPatternAgreement",
	Key:  "prop_4d45faf9ef87cdb8",
	Build: family.Theorem(
		"∀F₁ F₂:field_ops(A). ∀ρ₁ ρ₂:(num → A). ∀E:list((num → num) → int). "+
			"    polynomial_zero_pattern(F₁, ρ₁, E) = polynomial_zero_pattern(F₂, ρ₂, E) ⇔ "+
			"    ∀p:((num → num) → int). "+
			"        list_member(p, E) ⇒ (ring_formula_atom(F₁, p, ρ₁) ⇔ ring_formula_atom(F₂, p, ρ₂))",
		func(
			a *Argument,
			F1, F2 *Expr[FieldOps[A]],
			ρ1, ρ2 *Arrow[Nat, A],
			E *Expr[List[IntegerPolynomial]],
		) {
			// Both patterns read as the list maps of the atom test, so the
			// induction hypothesis speaks of the maps along the tail.
			a.Do(Simp(Fwd(zeroPatternDef)))
			a.Induct(E)
			a.Base(
				"the empty list has the empty pattern at every model, and no members",
				By(list.ListMapDef, list.ListMemberDef))
			a.Step(
				"the patterns of cons(p, E) agree when the atoms of p agree and the patterns of E do",
				func(b *Argument, ih Fact) {
					b.StepArgs("p", "E")
					b.Show(
						"two cons lists are equal exactly when their heads and their "+
							"tails are, and the members of cons(p, E) are p and those of E",
						Simp(Fwd(list.ListMapDef), Fwd(list.ListMemberDef), Fwd(list.ConsInjective)),
						By(ih))
				})
		}),
})}

// DecisionByCases — a property of the models that zero patterns decide
// where a parameter polynomial c specializes to zero, and decide where it
// does not, is decided by zero patterns: of c followed by the two lists.
// The decision set holds the patterns the models with the property
// realize; two models with one pattern of that list agree on every member
// (ZeroPatternAgreement), so on c and on each list, and so on the
// property.
var DecisionByCases = decisionByCasesThm{family.Add(registry.ProofEntry{
	Name: "DecisionByCases",
	Key:  "prop_b64700e011f706d9",
	Reading: "Φ is any property of a field and an environment; only its values at " +
		"algebraically closed fields with the variables U assigned are read. As in " +
		"NoEquationDecision, E and D are chosen before the field and the environment.",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀c:((num → num) → int). ∀Φ:(field_ops(A) → (num → A) → bool).",
		Hypotheses: []string{
			"c ∈ polynomial_algebra(int_ring, U)",
			"decided_by_zero_patterns(U, «vanishes»(c), Φ)",
			"decided_by_zero_patterns(U, «survives»(c), Φ)",
		},
		Conclusion: "decided_by_zero_patterns(U, «models», Φ)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		c *Expr[IntegerPolynomial],
		Φ *Arrow2[FieldOps[A], Fun[Nat, A], Bool],
		cIn, vanishing, surviving Fact,
	) {
		E1, onZero := a.UnpackAs[List[IntegerPolynomial]](
			a.Unfolded(vanishing, decidedByZeroPatternsDef), "E₁")
		E2, offZero := a.UnpackAs[List[IntegerPolynomial]](
			a.Unfolded(surviving, decidedByZeroPatternsDef), "E₂")
		first := a.Conjuncts(
			onZero,
			"E₁ lists parameter polynomials",
			"whose pattern decides Φ where c specializes to zero")
		second := a.Conjuncts(
			offZero,
			"E₂ lists parameter polynomials",
			"whose pattern decides Φ where c does not")
		_, onZeroDecides := a.Unpack(a.Unfolded(first[1], zeroPatternDecidesDef), "D₁")
		_, offZeroDecides := a.Unpack(a.Unfolded(second[1], zeroPatternDecidesDef), "D₂")
		firstMembers := a.Unfolded(first[0], polynomial_formula.PolynomialListOverDef)
		secondMembers := a.Unfolded(second[0], polynomial_formula.PolynomialListOverDef)
		E := a.TermAs[List[IntegerPolynomial]]("cons(c, list_append(E₁, E₂))")
		a.Do(Unfold(decidedByZeroPatternsDef))
		a.Take(E)
		a.Show(
			"c followed by E₁ and E₂ lists parameter polynomials, "+
				"and D holds the patterns of the models with the property",
			SplitConj(
				Case(
					"c and the members of E₁ and E₂ are parameter polynomials",
					Unfold(polynomial_formula.PolynomialListOverDef),
					By(
						cIn,
						polynomial_formula.PolynomialOnVariables.At(U, c),
						firstMembers,
						secondMembers,
						list.ListMemberDef,
						list.MemberAppend)),
				Case(
					"a model has the property exactly when its pattern is one a model with the property realizes",
					Unfold(zeroPatternDecidesDef),
					Witness(a.TermAs[Set[List[Bool]]](
						"{t:list(bool) | "+
							"    ∃G:field_ops(A). ∃τ:(num → A). "+
							"        algebraically_closed_field_on(G) ∧ "+
							"        fo_env_ok(G.carrier, U, τ) ∧ "+
							"        Φ(G, τ) ∧ "+
							"        t = polynomial_zero_pattern(G, τ, cons(c, list_append(E₁, E₂)))}")),
					Derive(func(b *Argument) {
						F := b.FixAs[FieldOps[A]]("F")
						ρ := b.FixAs[Fun[Nat, A]]("ρ")
						model := b.Assume()
						b.Iff()
						b.Forward(
							"a model with the property realizes its own pattern",
							func(d *Argument, holds Fact) {
								d.Show(
									"F and ρ themselves witness the membership",
									By(holds, model))
							})
						b.Backward(
							"a model with the pattern of one with the property agrees with it on c and on both lists",
							func(d *Argument, realized Fact) {
								G, τ, other := d.Unpack2As[FieldOps[A], Fun[Nat, A]](realized, "G", "τ")
								witness := d.Conjuncts(
									other,
									"G is an algebraically closed field",
									"τ assigns elements of G to U",
									"G and τ have the property",
									"with the pattern of F and ρ")
								agree := d.Have(
									"so every member of the list vanishes at F and ρ exactly when at G and τ",
									Statement{
										Binders:    "∀p:((num → num) → int).",
										Hypotheses: []string{"list_member(p, cons(c, list_append(E₁, E₂)))"},
										Conclusion: "ring_formula_atom(F, p, ρ) ⇔ ring_formula_atom(G, p, τ)",
									},
									By(witness[3], ZeroPatternAgreement.At(F, G, ρ, τ, E)))
								atom := d.Have(
									"c vanishes at both or at neither",
									"ring_formula_atom(F, c, ρ) ⇔ ring_formula_atom(G, c, τ)",
									By(agree, list.ListMemberDef))
								firstPattern := d.Have(
									"the two models have one pattern of E₁",
									"polynomial_zero_pattern(F, ρ, E₁) = polynomial_zero_pattern(G, τ, E₁)",
									By(agree, ZeroPatternAgreement.At(F, G, ρ, τ, E1), list.ListMemberDef, list.MemberAppend))
								secondPattern := d.Have(
									"and one pattern of E₂",
									"polynomial_zero_pattern(F, ρ, E₂) = polynomial_zero_pattern(G, τ, E₂)",
									By(agree, ZeroPatternAgreement.At(F, G, ρ, τ, E2), list.ListMemberDef, list.MemberAppend))
								d.Cases(d.Term("integer_polynomial_eval(field_ring(F), ρ, c) = F.zero"))
								d.When(
									"c specializes to zero at F, so at G, and E₁ decides the property at both",
									func(e *Argument, zero Fact) {
										e.Show(
											"G has the property, and F has G's pattern of E₁",
											By(
												onZeroDecides.At(F, ρ),
												onZeroDecides.At(G, τ),
												zero,
												model,
												witness[0],
												witness[1],
												witness[2],
												atom,
												firstPattern,
												ring_formula.RingFormulaAtomDef.At(F, c, ρ),
												ring_formula.RingFormulaAtomDef.At(G, c, τ)))
									})
								d.Otherwise(
									"c does not specialize to zero at F, so not at G, and E₂ decides the property at both",
									func(e *Argument, nonzero Fact) {
										e.Show(
											"G has the property, and F has G's pattern of E₂",
											By(
												offZeroDecides.At(F, ρ),
												offZeroDecides.At(G, τ),
												nonzero,
												model,
												witness[0],
												witness[1],
												witness[2],
												atom,
												secondPattern,
												ring_formula.RingFormulaAtomDef.At(F, c, ρ),
												ring_formula.RingFormulaAtomDef.At(G, c, τ)))
									})
							})
					}))))
	}),
})}

// DecisionByEquivalence — a property that agrees with a decided one is
// decided: where a property Ψ is decided by zero patterns on the models M,
// and Φ agrees with Ψ on a class N of models inside M, the list and the
// pattern set that decide Ψ on M decide Φ on N.
var DecisionByEquivalence = decisionByEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "DecisionByEquivalence",
	Key:  "prop_e6ee6626aa7edf27",
	Reading: "With N = M the property Φ is equivalent to Ψ at every " +
		"model; with Φ = Ψ a decision on M restricts to the smaller class N.",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀M N Φ Ψ:(field_ops(A) → (num → A) → bool).",
		Hypotheses: []string{
			"decided_by_zero_patterns(U, M, Ψ)",
			"∀F:field_ops(A). ∀ρ:(num → A). N(F, ρ) ⇒ M(F, ρ)",
			"∀F:field_ops(A). ∀ρ:(num → A). N(F, ρ) ⇒ (Φ(F, ρ) ⇔ Ψ(F, ρ))",
		},
		Conclusion: "decided_by_zero_patterns(U, N, Φ)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		M, N, Φ, Ψ *Arrow2[FieldOps[A], Fun[Nat, A], Bool],
		decided, inside, agree Fact,
	) {
		E, decides := a.UnpackAs[List[IntegerPolynomial]](
			a.Unfolded(decided, decidedByZeroPatternsDef), "E")
		decision := a.Conjuncts(
			decides,
			"E lists parameter polynomials",
			"whose pattern decides Ψ on M")
		D, pattern := a.Unpack(a.Unfolded(decision[1], zeroPatternDecidesDef), "D")
		a.Do(Unfold(decidedByZeroPatternsDef))
		a.Take(E)
		a.Show(
			"E lists parameter polynomials, and on N the property Φ is Ψ, which E and D decide on M",
			SplitConj(
				Case(
					"E lists parameter polynomials",
					By(decision[0])),
				Case(
					"on N the property Φ is Ψ, which D decides through the pattern of E",
					Unfold(zeroPatternDecidesDef),
					Witness(D),
					By(pattern, inside, agree))))
	}),
})}

// SingleEquationDecision — whether one equation and one inequation have a
// common solution is decided by the zero pattern of finitely many parameter
// polynomials: by strong induction on the degree n of the equation g,
// branching on whether its leading coefficient specializes to zero
// (DecisionByCases). Where it does, g at degree zero is zero and the system
// is h alone (NoEquationDecision), and at positive degree g specializes as
// its truncation below n (polynomial_formula.SpecializedTruncation), of
// lower degree (polynomial.TruncateBelow), which the induction decides. Where
// it does not, the pseudo-remainder of h to the n by g decides the system
// (algebraic_closure.PseudoRemainderDecision), and NoEquationDecision
// decides the remainder. Each branch carries a decided system to g's by
// DecisionByEquivalence.
var SingleEquationDecision = singleEquationDecisionThm{family.Add(registry.ProofEntry{
	Name: "SingleEquationDecision",
	Key:  "prop_43ec88802148609d",
	Reading: "Algebraic closure is load-bearing beyond infinitude: g = x² + 1 and h " +
		"= 1 with U empty give one zero pattern over the algebraic numbers and over the " +
		"reals, and a common solution only over the first. If g specializes to zero the " +
		"system is h alone; if it specializes to a nonzero constant there is no solution.",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀g h:(num → ((num → num) → int)).",
		Hypotheses: []string{
			"«overParameters»(g)",
			"«overParameters»(h)",
		},
		Conclusion: "decided_by_zero_patterns(U, «models», «solvable»(g))",
		Abbrev: Abbrev{
			{Name: "solvable", Text: "λf:(num → ((num → num) → int)). λF:field_ops(A). λρ:(num → A). ∃x:A. " +
				"    x ∈ F.carrier ∧ «value»(F, ρ, f, x) = F.zero ∧ «value»(F, ρ, h, x) ≠ F.zero"},
		},
	}, func(a *Argument, U *Expr[Set[Nat]], g, h *Arrow[Nat, IntegerPolynomial], gOver, hOver Fact) {
		models := a.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«models»")
		decided := a.TermAs[Set[Nat]](
			"λn:num. ∀f:(num → ((num → num) → int)). " +
				"    «overParameters»(f) ∧ polynomial_degree(integer_polynomial_ring.zero, f) = n ⇒ " +
				"    decided_by_zero_patterns(U, «models», «solvable»(f))")
		a.Show(
			"by strong induction on the degree of g, for every parameter polynomial of that degree",
			ByInduction(nat_order.StrongInduction.At(
				decided, a.TermAs[Nat]("polynomial_degree(integer_polynomial_ring.zero, g)")), gOver,
				Case(
					"a polynomial f of degree n is decided once every polynomial of lower degree is",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						lower := b.Assume()
						f := b.FixAs[Fun[Nat, IntegerPolynomial]]("f")
						given := b.Conjuncts(
							b.Assume(),
							"f is a polynomial over the parameters",
							"of degree n")
						fOver, degree := given[0], given[1]
						leadIn := b.Have(
							"the leading coefficient f(n) is a parameter polynomial",
							"f(n) ∈ polynomial_algebra(int_ring, U)",
							By(fOver, polynomial.PolynomialOverDef))
						vanishes := b.Have(
							"f vanishes past its degree",
							"vec⟨suc(polynomial_degree(integer_polynomial_ring.zero, f))⟩(integer_polynomial_ring.zero, f)",
							By(fOver, polynomial.DegreeVec))
						vanishing := b.Have(
							"where f(n) specializes to zero the system is decided: at degree "+
								"zero it is h alone, beyond it that of the truncation of f below n",
							"decided_by_zero_patterns(U, «vanishes»(f(n)), «solvable»(f))",
							Derive(func(c *Argument) {
								c.Cases(c.Term("n = 0"))
								c.When(
									"at degree zero f specializes to zero altogether, and the system asks only that h not vanish",
									func(d *Argument, zero Fact) {
										sameSystem := d.Have(
											"where f specializes to zero every value of f is zero, and the system is that h not vanish",
											Statement{
												Binders:    "∀F:field_ops(A). ∀ρ:(num → A).",
												Hypotheses: []string{"«vanishes»(f(n), F, ρ)"},
												Conclusion: "«solvable»(f, F, ρ) ⇔ «nonzeroSomewhere»(h, F, ρ)",
											},
											Derive(func(e *Argument) {
												F := e.FixAs[FieldOps[A]]("F")
												ρ := e.FixAs[Fun[Nat, A]]("ρ")
												model := e.Conjuncts(
													e.Assume(),
													"F is an algebraically closed field",
													"ρ assigns elements of F to U",
													"f(n) specializes to zero")
												opened := e.Conjuncts(
													GroupPremises(model[0], model[1], ModelSpecialization.At(U, F, ρ)),
													"F is a field",
													"specialization at ρ is a ring homomorphism",
													"that keeps zero")
												fieldOn, keepsZero := opened[0], opened[2]
												specializedF := e.TermAs[Fun[Nat, A]]("«specialized»(field_ring(F), ρ, f)")
												imageVanishes := e.Have(
													"specialization keeps zero, so the specialization of f vanishes past the degree of f too",
													"vec⟨suc(polynomial_degree(integer_polynomial_ring.zero, f))⟩(F.zero, "+
														"    «specialized»(field_ring(F), ρ, f))",
													By(
														vanishes,
														At(polynomial.VecMap,
															e.TermAs[Fun[IntegerPolynomial, A]](
																"λq:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, q)"),
															e.TermAs[IntegerPolynomial]("integer_polynomial_ring.zero"),
															e.TermAs[A]("F.zero"),
															e.TermAs[Nat]("suc(polynomial_degree(integer_polynomial_ring.zero, f))"),
															f),
														keepsZero))
												bound := e.Have(
													"so its degree is at most that of f",
													"polynomial_degree(F.zero, «specialized»(field_ring(F), ρ, f)) ≤ "+
														"polynomial_degree(integer_polynomial_ring.zero, f)",
													By(imageVanishes, polynomial.DegreeLeast))
												constant := e.Have(
													"which is zero",
													"polynomial_degree(F.zero, «specialized»(field_ring(F), ρ, f)) = 0",
													ByArith(bound, zero, degree))
												nowhere := e.Have(
													"so the specialization of f is its constant coefficient, zero, at every point",
													"∀x:A. x ∈ F.carrier ⇒ «value»(F, ρ, f, x) = F.zero",
													Derive(func(k *Argument) {
														x := k.FixAs[A]("x")
														xIn := k.Assume()
														k.Show(
															"a polynomial of degree zero takes its constant coefficient everywhere",
															By(
																model[1],
																model[2],
																zero,
																constant,
																xIn,
																fOver,
																polynomial_formula.SpecializedPolynomial.Read(field.RingOn.Read(fieldOn)).At(U, ρ, f),
																polynomial_evaluation.DegreeZeroEval.Read(field.RingOn.Read(fieldOn)).AsFact().At(specializedF, x)))
													}))
												e.Show(
													"so the system is that h not vanish somewhere",
													By(nowhere))
											}))
										d.Show(
											"NoEquationDecision decides whether h is nonzero somewhere, "+
												"which is the system where f(0) specializes to zero",
											By(
												DecisionByEquivalence.At(
													U,
													models,
													d.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«vanishes»(f(n))"),
													d.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(f)"),
													d.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«nonzeroSomewhere»(h)")),
												NoEquationDecision.Inst[A]().At(U, h),
												hOver,
												sameSystem))
									})
								c.Otherwise(
									"at positive degree f specializes as its truncation "+
										"below n, of lower degree, which the induction decides",
									func(d *Argument, nonzero Fact) {
										positive := d.Have(
											"n is positive",
											"0 < n",
											ByArith(nonzero))
										zeroIn := d.Have(
											"the zero is a parameter polynomial",
											"integer_polynomial_ring.zero ∈ polynomial_algebra(int_ring, U)",
											By(comm_ring.SubringZero, polynomial_formula.ParameterPolynomialsSubring.At(U)))
										truncation := d.Conjuncts(
											d.Have(
												"the truncation of f below n is a parameter polynomial of degree below n",
												"«overParameters»(λi:num. COND(i < n, f(i), integer_polynomial_ring.zero)) ∧ "+
													"polynomial_degree(integer_polynomial_ring.zero, "+
													"    λi:num. COND(i < n, f(i), integer_polynomial_ring.zero)) < "+
													"n",
												By(fOver, zeroIn, positive, polynomial.TruncateBelow)),
											"the truncation is a parameter polynomial",
											"of degree below n")
										truncated := d.TermAs[Fun[Nat, IntegerPolynomial]](
											"λi:num. COND(i < n, f(i), integer_polynomial_ring.zero)")
										sameSystem := d.Have(
											"where f(n) specializes to zero, f specializes as its truncation",
											Statement{
												Binders:    "∀F:field_ops(A). ∀ρ:(num → A).",
												Hypotheses: []string{"«vanishes»(f(n), F, ρ)"},
												Conclusion: "«solvable»(f, F, ρ) ⇔ " +
													"«solvable»(λi:num. COND(i < n, f(i), integer_polynomial_ring.zero), F, ρ)",
											},
											Derive(func(e *Argument) {
												e.FixAs[FieldOps[A]]("F")
												ρ := e.FixAs[Fun[Nat, A]]("ρ")
												model := e.Conjuncts(
													e.Assume(),
													"F is an algebraically closed field",
													"ρ assigns elements of F to U",
													"f(n) specializes to zero")
												agree := e.Have(
													"f(n) specializing to zero, the truncation of f below its degree n specializes as f",
													"«specialized»(field_ring(F), ρ, λi:num. COND(i < n, f(i), integer_polynomial_ring.zero)) = "+
														"«specialized»(field_ring(F), ρ, f)",
													degree.RwRev(),
													By(
														polynomial_formula.SpecializedTruncation.Read(
															field.RingOn.Read(algebraic_closure.FieldOn.Read(model[0]))).At(
															U, ρ, f),
														model[1],
														fOver,
														model[2]))
												e.Show(
													"so the system of f is that of its truncation",
													agree.RwRev(),
													Basic())
											}))
										d.Show(
											"the induction decides the truncation, whose system is that of f where f(n) specializes to zero",
											By(
												DecisionByEquivalence.At(
													U,
													models,
													d.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«vanishes»(f(n))"),
													d.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(f)"),
													d.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
														"«solvable»(λi:num. COND(i < n, f(i), integer_polynomial_ring.zero))")),
												truncation[0],
												truncation[1],
												lower.At(
													d.TermAs[Nat](
														"polynomial_degree(integer_polynomial_ring.zero, "+
															"    λi:num. COND(i < n, f(i), integer_polynomial_ring.zero))"),
													truncated),
												sameSystem))
									})
							}))
						surviving := b.Have(
							"where f(n) does not specialize to zero the pseudo-remainder of h to the n by f decides the system",
							"decided_by_zero_patterns(U, «survives»(f(n)), «solvable»(f))",
							Derive(func(c *Argument) {
								r, remainder := c.UnpackAs[Fun[Nat, IntegerPolynomial]](
									GroupPremises(
										polynomial_formula.ParameterRingCommutative.At(U),
										fOver,
										hOver,
										algebraic_closure.PseudoRemainderDecision.Inst(
											TypeBinder.BindB[IntegerPolynomial](), TypeBinder.BindA[A]()).At(
											c.TermAs[module_record.RingOps[IntegerPolynomial]]("«parameterRing»(U)"),
											f,
											h)),
									"r")
								parts := c.Conjuncts(
									remainder,
									"r, the pseudo-remainder of h to the degree of f by f, is a parameter polynomial",
									"whose specialization decides the system wherever the leading coefficient of f survives")
								sameSystem := c.Have(
									"where f(n) survives the system is solvable exactly "+
										"when the specialized remainder is nonzero somewhere",
									Statement{
										Binders:    "∀F:field_ops(A). ∀ρ:(num → A).",
										Hypotheses: []string{"«survives»(f(n), F, ρ)"},
										Conclusion: "«solvable»(f, F, ρ) ⇔ «nonzeroSomewhere»(r, F, ρ)",
									},
									Derive(func(d *Argument) {
										F := d.FixAs[FieldOps[A]]("F")
										ρ := d.FixAs[Fun[Nat, A]]("ρ")
										model := d.Conjuncts(
											d.Assume(),
											"F is an algebraically closed field",
											"ρ assigns elements of F to U",
											"f(n) does not specialize to zero")
										opened := d.Conjuncts(
											GroupPremises(model[0], model[1], ModelSpecialization.At(U, F, ρ)),
											"F is a field",
											"specialization at ρ is a ring homomorphism",
											"that keeps zero")
										fieldOn, specialization := opened[0], opened[1]
										survives := d.Have(
											"the coefficient of f at its degree survives",
											"integer_polynomial_eval(field_ring(F), "+
												"    ρ, "+
												"    f(polynomial_degree(integer_polynomial_ring.zero, f))) ≠ "+
												"F.zero",
											By(Normalized, model[2], degree))
										solvable := d.Have(
											"so the specialized system is solvable exactly when the specialized remainder is not zero",
											"«solvable»(f, F, ρ) ⇔ «specialized»(field_ring(F), ρ, r) ≠ vec_zero(F.zero)",
											By(
												model[0],
												survives,
												specialization,
												parts[1].At(
													F,
													d.TermAs[Fun[IntegerPolynomial, A]](
														"λq:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, q)"))))
										d.Show(
											"a polynomial over an algebraically closed field is nonzero somewhere exactly when it is not zero",
											By(
												model[1],
												parts[0],
												solvable,
												polynomial_formula.SpecializedPolynomial.Read(field.RingOn.Read(fieldOn)).At(U, ρ, r),
												algebraic_closure.NonzeroValue.Read(model[0]).At(
													d.TermAs[Fun[Nat, A]]("«specialized»(field_ring(F), ρ, r)"))))
									}))
								c.Show(
									"NoEquationDecision decides whether the specialized remainder "+
										"is nonzero somewhere, which is the system where f(n) survives",
									By(
										DecisionByEquivalence.At(
											U,
											models,
											c.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«survives»(f(n))"),
											c.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(f)"),
											c.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«nonzeroSomewhere»(r)")),
										parts[0],
										NoEquationDecision.Inst[A]().At(U, r),
										sameSystem))
							}))
						b.Show(
							"f(n) in front of the two lists decides the system",
							By(
								DecisionByCases.At(
									U,
									b.TermAs[IntegerPolynomial]("f(n)"),
									b.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(f)")),
								leadIn,
								vanishing,
								surviving))
					}))))
	}),
})}

// PairReduction — a system of k + 2 equations is decided once every
// system of k + 1 equations is: the last two are reduced by the parametric
// Euclidean algorithm. Every pair p, q of parameter polynomials in place of
// g(k), g(k + 1), the degree of q at most that of p, is decided, by strong
// induction on the sum of the two degrees, branching on whether the leading
// coefficient of q specializes to zero (DecisionByCases). Where it does, q
// of degree zero specializes to zero and drops out, leaving k + 1
// equations for the hypothesis, and q of positive degree specializes as its
// truncation below the degree (polynomial_formula.SpecializedTruncation), a
// pair of lower sum. Where it does not, q of degree zero is a nonzero
// constant with no root, and otherwise p is replaced by its pseudo-remainder
// r by q, which vanishes with p at the roots of q and whose coefficients
// vanish from the degree of q on (polynomial_roots.PseudoRemainderRoots), so
// r has degree below q and q, r is a pair of lower sum. Each branch carries
// the decision of the system it reduces to by DecisionByEquivalence, and so
// do the system's own last two equations, taken in the order that puts the
// lower degree second.
var PairReduction = pairReductionThm{family.Add(registry.ProofEntry{
	Name: "PairReduction",
	Key:  "prop_8b1c92e9a80db466",
	Reading: "The conclusion is ParameterizedSystemDecision at k + 2, so it holds outright; " +
		"the hypothesis on k + 1 equations serves the route. It covers every f because the route " +
		"applies it to a truncation or a pseudo-remainder, not to one of the g(j); the inequation " +
		"stays h throughout, so h itself needs no hypothesis. Indices of g past k + 1 are not read.",
	Build: family.Sections(Statement{
		Binders: "∀U:set(num). " +
			"∀k:num. " +
			"∀g:(num → num → ((num → num) → int)). " +
			"∀h:(num → ((num → num) → int)).",
		Hypotheses: []string{
			"∀f:(num → num → ((num → num) → int)). " +
				"    (∀j:num. j < suc(k) ⇒ «overParameters»(f(j))) ⇒ " +
				"    decided_by_zero_patterns(U, «models», «system»(suc(k), f, h))",
			"∀j:num. j < suc(suc(k)) ⇒ «overParameters»(g(j))",
		},
		Conclusion: "decided_by_zero_patterns(U, «models», «system»(suc(suc(k)), g, h))",
		Abbrev: Abbrev{
			{Name: "solvable", Text: "λp:(num → ((num → num) → int)). " +
				"λq:(num → ((num → num) → int)). " +
				"λF:field_ops(A). " +
				"λρ:(num → A). " +
				"∃x:A. " +
				"    x ∈ F.carrier ∧ " +
				"    (∀j:num. j < k ⇒ «value»(F, ρ, g(j), x) = F.zero) ∧ " +
				"    «value»(F, ρ, p, x) = F.zero ∧ " +
				"    «value»(F, ρ, q, x) = F.zero ∧ " +
				"    «value»(F, ρ, h, x) ≠ F.zero"},
			{Name: "decided", Text: "λp:(num → ((num → num) → int)). λq:(num → ((num → num) → int)). " +
				"    decided_by_zero_patterns(U, «models», «solvable»(p, q))"},
			{Name: "truncation", Text: "λq:(num → ((num → num) → int)). λi:num. " +
				"    COND(i < polynomial_degree(integer_polynomial_ring.zero, q), " +
				"        q(i), " +
				"        integer_polynomial_ring.zero)"},
			{Name: "pairsDecided", Text: "λn:num. ∀p q:(num → ((num → num) → int)). " +
				"    «overParameters»(p) ∧ " +
				"    «overParameters»(q) ∧ " +
				"    polynomial_degree(integer_polynomial_ring.zero, q) ≤ " +
				"    polynomial_degree(integer_polynomial_ring.zero, p) ∧ " +
				"    polynomial_degree(integer_polynomial_ring.zero, p) + " +
				"    polynomial_degree(integer_polynomial_ring.zero, q) = " +
				"    n ⇒ " +
				"    «decided»(p, q)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Any pair p, q of parameter polynomials in place of g(k), g(k + 1), q of
		// degree at most that of p, is decided: by strong induction on the sum n
		// of the two degrees.
		reduced := ctx.Lemma(Statement{
			Binders: "∀U:set(num). " +
				"∀k:num. " +
				"∀g:(num → num → ((num → num) → int)). " +
				"∀h:(num → ((num → num) → int)). " +
				"∀n:num.",
			Hypotheses: []string{
				"∀f:(num → num → ((num → num) → int)). " +
					"    (∀j:num. j < suc(k) ⇒ «overParameters»(f(j))) ⇒ " +
					"    decided_by_zero_patterns(U, «models», «system»(suc(k), f, h))",
				"∀j:num. j < suc(suc(k)) ⇒ «overParameters»(g(j))",
			},
			Conclusion: "«pairsDecided»(n)",
		}, func(
			a *Argument,
			U *Expr[Set[Nat]],
			k *Expr[Nat],
			g *Expr[Fun2[Nat, Nat, IntegerPolynomial]],
			h *Arrow[Nat, IntegerPolynomial],
			n *Expr[Nat],
			fewer, gOver Fact,
		) {
			models := a.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«models»")
			zeroIn := a.Have(
				"the zero is a parameter polynomial",
				"integer_polynomial_ring.zero ∈ polynomial_algebra(int_ring, U)",
				By(comm_ring.SubringZero, polynomial_formula.ParameterPolynomialsSubring.At(U)))
			pairs := a.TermAs[Set[Nat]]("«pairsDecided»")
			a.Show(
				"by strong induction on the sum n of the two degrees",
				ByInduction(nat_order.StrongInduction.At(pairs, n),
					Case(
						"a pair whose degrees sum to s is decided once every pair of lower sum is",
						Derive(func(c *Argument) {
							c.FixAs[Nat]("s")
							lower := c.Assume()
							p := c.FixAs[Fun[Nat, IntegerPolynomial]]("p")
							q := c.FixAs[Fun[Nat, IntegerPolynomial]]("q")
							given := c.Conjuncts(
								c.Assume(),
								"p is a parameter polynomial",
								"so is q",
								"q has degree at most that of p",
								"the two degrees sum to s")
							pOver, qOver, ordered, sum := given[0], given[1], given[2], given[3]
							leadIn := c.Have(
								"the leading coefficient of q is a parameter polynomial",
								"q(polynomial_degree(integer_polynomial_ring.zero, q)) ∈ polynomial_algebra(int_ring, U)",
								By(qOver, polynomial.PolynomialOverDef))
							vanishing := c.Have(
								"where the leading coefficient of q specializes to zero the pair is decided",
								"decided_by_zero_patterns(U, "+
									"    «vanishes»(q(polynomial_degree(integer_polynomial_ring.zero, q))), "+
									"    «solvable»(p, q))",
								Derive(func(d *Argument) {
									d.Cases(d.Term("polynomial_degree(integer_polynomial_ring.zero, q) = 0"))
									d.When(
										"q of degree zero specializes to zero altogether and "+
											"drops out, leaving the k + 1 equations g(j), j < k, and p",
										func(e *Argument, constant Fact) {
											listed := e.Have(
												"the k + 1 equations g(j), j < k, and p are parameter polynomials",
												"∀j:num. j < suc(k) ⇒ «overParameters»(COND(j < k, g(j), p))",
												Derive(func(t *Argument) {
													t.FixAs[Nat]("j")
													t.Assume()
													t.Cases(t.Term("j < k"))
													t.When(
														"below k the equation is g(j), one of the system",
														func(u *Argument, below Fact) {
															inRange := u.Have(
																"j lies below k + 2",
																"j < suc(suc(k))",
																ByArith(below))
															equation := u.Have(
																"so g(j) is a parameter polynomial",
																"«overParameters»(g(j))",
																By(gOver, inRange))
															u.Show(
																"and it is the equation at j",
																By(equation, below))
														})
													t.Otherwise(
														"at k the equation is p",
														func(u *Argument, notBelow Fact) {
															u.Show(
																"a parameter polynomial",
																By(pOver, notBelow))
														})
												}))
											replaced := e.TermAs[Fun2[Nat, Nat, IntegerPolynomial]]("λj:num. COND(j < k, g(j), p)")
											sameSystem := e.Have(
												"where q specializes to zero, the pair's system is that of the k + 1 equations",
												Statement{
													Binders:    "∀F:field_ops(A). ∀ρ:(num → A).",
													Hypotheses: []string{"«vanishes»(q(polynomial_degree(integer_polynomial_ring.zero, q)), F, ρ)"},
													Conclusion: "«solvable»(p, q, F, ρ) ⇔ «system»(suc(k), λj:num. COND(j < k, g(j), p), h, F, ρ)",
												},
												Derive(func(m *Argument) {
													F := m.FixAs[FieldOps[A]]("F")
													ρ := m.FixAs[Fun[Nat, A]]("ρ")
													model := m.Conjuncts(
														m.Assume(),
														"F is an algebraically closed field",
														"ρ assigns elements of F to U",
														"the leading coefficient of q specializes to zero")
													opened := m.Conjuncts(
														GroupPremises(model[0], model[1], ModelSpecialization.At(U, F, ρ)),
														"F is a field",
														"specialization at ρ is a ring homomorphism",
														"that keeps zero")
													fieldOn, keepsZero := opened[0], opened[2]
													agree := m.Have(
														"q specializes as its truncation below its degree",
														"«specialized»(field_ring(F), ρ, «truncation»(q)) = «specialized»(field_ring(F), ρ, q)",
														By(
															polynomial_formula.SpecializedTruncation.Read(field.RingOn.Read(fieldOn)).At(U, ρ, q),
															model[1],
															qOver,
															model[2]))
													killed := m.Have(
														"which below degree zero is the zero polynomial",
														"«specialized»(field_ring(F), ρ, q) = vec_zero(F.zero)",
														agree.RwRev(),
														constant.Rw(),
														Funext(),
														m.ForEach(func(i *Expr[Nat]) Action {
															return By(keepsZero, nat_order.LessThanZeroClause, vec_space.VecZeroDef)
														}))
													fieldRing := field.RingOn.Read(fieldOn)
													nowhere := m.Have(
														"so it vanishes everywhere",
														"∀x:A. x ∈ F.carrier ⇒ «value»(F, ρ, q, x) = F.zero",
														By(Normalized, killed, polynomial_evaluation.EvalVecZero.Read(fieldRing)))
													dropped := m.Have(
														"at each point the k + 1 equations hold exactly when the g(j), j < k, and p vanish",
														"∀x:A. "+
															"    (∀j:num. j < suc(k) ⇒ «value»(F, ρ, COND(j < k, g(j), p), x) = F.zero) ⇔ "+
															"    (∀j:num. j < k ⇒ «value»(F, ρ, g(j), x) = F.zero) ∧ «value»(F, ρ, p, x) = F.zero",
														By(nat_order.LessThanSucClause, nat_order.LessThanIrrefl))
													m.Iff()
													m.Forward(
														"a common solution of the pair solves the k + 1 equations",
														func(u *Argument, solution Fact) {
															x, at := u.UnpackAs[A](solution, "x")
															u.Show(
																"at the same point",
																Witness(x),
																By(at, dropped.At(x)))
														})
													m.Backward(
														"a common solution of the k + 1 equations solves the pair, q vanishing everywhere",
														func(u *Argument, solution Fact) {
															x, at := u.UnpackAs[A](solution, "x")
															u.Show(
																"at the same point",
																Witness(x),
																By(at, dropped.At(x), nowhere.At(x)))
														})
												}))
											e.Show(
												"the hypothesis decides the k + 1 equations g(j), j < k, and "+
													"p, the pair's system where q's leading coefficient vanishes",
												By(
													DecisionByEquivalence.At(
														U,
														models,
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
															"«vanishes»(q(polynomial_degree(integer_polynomial_ring.zero, q)))"),
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(p, q)"),
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
															"«system»(suc(k), λj:num. COND(j < k, g(j), p), h)")),
													listed,
													fewer.At(replaced),
													sameSystem))
										})
									d.Otherwise(
										"q of positive degree specializes as its truncation below the degree, a pair of lower sum",
										func(e *Argument, nonconstant Fact) {
											positive := e.Have(
												"q has positive degree",
												"0 < polynomial_degree(integer_polynomial_ring.zero, q)",
												ByArith(nonconstant))
											truncation := e.Conjuncts(
												e.Have(
													"the truncation of q below its degree is a parameter polynomial of lower degree",
													"«overParameters»(«truncation»(q)) ∧ "+
														"polynomial_degree(integer_polynomial_ring.zero, «truncation»(q)) < "+
														"polynomial_degree(integer_polynomial_ring.zero, q)",
													By(qOver, zeroIn, positive, polynomial.TruncateBelow)),
												"the truncation is a parameter polynomial",
												"of degree below q")
											smaller := e.Have(
												"p and the truncation are ordered, and their degrees sum below s",
												"polynomial_degree(integer_polynomial_ring.zero, «truncation»(q)) ≤ "+
													"polynomial_degree(integer_polynomial_ring.zero, p) ∧ "+
													"polynomial_degree(integer_polynomial_ring.zero, p) + "+
													"polynomial_degree(integer_polynomial_ring.zero, «truncation»(q)) < "+
													"s",
												ByArith(truncation[1], ordered, sum))
											sameSystem := e.Have(
												"where the leading coefficient of q specializes to zero, q specializes as its truncation",
												Statement{
													Binders:    "∀F:field_ops(A). ∀ρ:(num → A).",
													Hypotheses: []string{"«vanishes»(q(polynomial_degree(integer_polynomial_ring.zero, q)), F, ρ)"},
													Conclusion: "«solvable»(p, q, F, ρ) ⇔ «solvable»(p, «truncation»(q), F, ρ)",
												},
												Derive(func(m *Argument) {
													m.FixAs[FieldOps[A]]("F")
													ρ := m.FixAs[Fun[Nat, A]]("ρ")
													model := m.Conjuncts(
														m.Assume(),
														"F is an algebraically closed field",
														"ρ assigns elements of F to U",
														"the leading coefficient of q specializes to zero")
													agree := m.Have(
														"so the truncation specializes as q",
														"«specialized»(field_ring(F), ρ, «truncation»(q)) = «specialized»(field_ring(F), ρ, q)",
														By(
															polynomial_formula.SpecializedTruncation.Read(
																field.RingOn.Read(algebraic_closure.FieldOn.Read(model[0]))).At(
																U, ρ, q),
															model[1],
															qOver,
															model[2]))
													m.Show(
														"so the pair's system is that of p and the truncation",
														agree.RwRev(),
														Basic())
												}))
											e.Show(
												"the induction decides p and the truncation of q, the "+
													"pair's system where q's leading coefficient vanishes",
												By(
													DecisionByEquivalence.At(
														U,
														models,
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
															"«vanishes»(q(polynomial_degree(integer_polynomial_ring.zero, q)))"),
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(p, q)"),
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(p, «truncation»(q))")),
													pOver,
													truncation[0],
													smaller,
													lower.At(
														e.TermAs[Nat](
															"polynomial_degree(integer_polynomial_ring.zero, p) + "+
																"polynomial_degree(integer_polynomial_ring.zero, «truncation»(q))"),
														p,
														e.TermAs[Fun[Nat, IntegerPolynomial]]("«truncation»(q)")),
													sameSystem))
										})
								}))
							surviving := c.Have(
								"where the leading coefficient of q survives the pair is decided",
								"decided_by_zero_patterns(U, "+
									"    «survives»(q(polynomial_degree(integer_polynomial_ring.zero, q))), "+
									"    «solvable»(p, q))",
								Derive(func(d *Argument) {
									d.Cases(d.Term("polynomial_degree(integer_polynomial_ring.zero, q) = 0"))
									d.When(
										"q of degree zero specializes to a nonzero constant, which has no root",
										func(e *Argument, constant Fact) {
											noSolution := e.Have(
												"where the constant q survives, the system has no solution",
												Statement{
													Binders:    "∀F:field_ops(A). ∀ρ:(num → A).",
													Hypotheses: []string{"«survives»(q(polynomial_degree(integer_polynomial_ring.zero, q)), F, ρ)"},
													Conclusion: "«solvable»(p, q, F, ρ) ⇔ ⊥",
												},
												Derive(func(m *Argument) {
													m.FixAs[FieldOps[A]]("F")
													ρ := m.FixAs[Fun[Nat, A]]("ρ")
													model := m.Conjuncts(
														m.Assume(),
														"F is an algebraically closed field",
														"ρ assigns elements of F to U",
														"the leading coefficient of q survives")
													fieldRing := field.RingOn.Read(algebraic_closure.FieldOn.Read(model[0]))
													specializedQ := m.TermAs[Fun[Nat, A]]("«specialized»(field_ring(F), ρ, q)")
													keptDegree := m.Have(
														"the specialization of q keeps its degree, the leading coefficient surviving",
														"polynomial_degree(F.zero, «specialized»(field_ring(F), ρ, q)) = "+
															"polynomial_degree(integer_polynomial_ring.zero, q)",
														By(polynomial_formula.SpecializedDegree.Read(fieldRing).At(U, ρ, q), model[1], qOver, model[2]))
													kept := m.Have(
														"which is zero",
														"polynomial_degree(F.zero, «specialized»(field_ring(F), ρ, q)) = 0",
														ByArith(keptDegree, constant))
													nowhere := m.Have(
														"so it takes its nonzero constant coefficient everywhere",
														"∀x:A. x ∈ F.carrier ⇒ «value»(F, ρ, q, x) ≠ F.zero",
														Derive(func(t *Argument) {
															x := t.FixAs[A]("x")
															xIn := t.Assume()
															t.Show(
																"a polynomial of degree zero takes its constant coefficient everywhere",
																By(
																	model[1],
																	model[2],
																	constant,
																	kept,
																	xIn,
																	qOver,
																	polynomial_formula.SpecializedPolynomial.Read(fieldRing).At(U, ρ, q),
																	polynomial_evaluation.DegreeZeroEval.Read(fieldRing).AsFact().At(specializedQ, x)))
														}))
													m.Show(
														"so the system has no solution",
														By(nowhere))
												}))
											never := e.Have(
												"the empty list and no pattern decide the property that never holds",
												"decided_by_zero_patterns(U, «models», λF:field_ops(A). λρ:(num → A). ⊥)",
												Unfold(decidedByZeroPatternsDef),
												Witness(e.TermAs[List[IntegerPolynomial]]("nil")),
												SplitConj(
													Case(
														"the empty list lists parameter polynomials",
														Unfold(polynomial_formula.PolynomialListOverDef),
														By(list.ListMemberDef)),
													Case(
														"and no pattern lies in the empty set",
														Unfold(zeroPatternDecidesDef),
														Witness(e.TermAs[Set[List[Bool]]]("∅")),
														By(set_basic.NotInEmpty))))
											e.Show(
												"a system with no solution is the property that never holds",
												By(
													DecisionByEquivalence.At(
														U,
														models,
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
															"«survives»(q(polynomial_degree(integer_polynomial_ring.zero, q)))"),
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(p, q)"),
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("λF:field_ops(A). λρ:(num → A). ⊥")),
													never,
													noSolution))
										})
									d.Otherwise(
										"q of positive degree: p is replaced by its pseudo-remainder r by q, of degree below q",
										func(e *Argument, nonconstant Fact) {
											r, remainder := e.UnpackAs[Fun[Nat, IntegerPolynomial]](
												GroupPremises(
													polynomial_formula.ParameterRingCommutative.At(U),
													pOver,
													qOver,
													polynomial_roots.PseudoRemainderRoots.Inst(
														TypeBinder.BindB[IntegerPolynomial](), TypeBinder.BindA[A]()).At(
														e.TermAs[module_record.RingOps[IntegerPolynomial]]("«parameterRing»(U)"),
														p,
														q)),
												"r")
											parts := e.Conjuncts(
												remainder,
												"r, the pseudo-remainder of p by q, is a parameter polynomial",
												"vanishing from the degree of q on",
												"which vanishes with p at the roots of q")
											smaller := e.Have(
												"q and r are ordered, and their degrees sum below s",
												"polynomial_degree(integer_polynomial_ring.zero, r) ≤ "+
													"polynomial_degree(integer_polynomial_ring.zero, q) ∧ "+
													"polynomial_degree(integer_polynomial_ring.zero, q) + "+
													"polynomial_degree(integer_polynomial_ring.zero, r) < "+
													"s",
												Derive(func(t *Argument) {
													positive := t.Have(
														"q has positive degree",
														"0 < polynomial_degree(integer_polynomial_ring.zero, q)",
														ByArith(nonconstant))
													zeroDegree := t.Have(
														"the zero polynomial has degree zero",
														"polynomial_degree(integer_polynomial_ring.zero, vec_zero(integer_polynomial_ring.zero)) = 0",
														By(polynomial.DegreeVecZero))
													below := t.Have(
														"so r, vanishing from the positive degree of q on, has degree below q",
														"polynomial_degree(integer_polynomial_ring.zero, r) < "+
															"polynomial_degree(integer_polynomial_ring.zero, q)",
														By(
															positive,
															zeroDegree,
															polynomial.DegreeBelow.At(
																t.TermAs[IntegerPolynomial]("«parameterRing»(U).zero"),
																proof.InhabitFrom(r, parts[1])),
															polynomial_formula.IntegerPolynomialRingOperations))
													t.Show(
														"q has degree at most that of p, and the two degrees sum to s",
														ByArith(below, ordered, sum))
												}))
											sameSystem := e.Have(
												"where the leading coefficient of q survives, p and r vanish together at the roots of q",
												Statement{
													Binders:    "∀F:field_ops(A). ∀ρ:(num → A).",
													Hypotheses: []string{"«survives»(q(polynomial_degree(integer_polynomial_ring.zero, q)), F, ρ)"},
													Conclusion: "«solvable»(p, q, F, ρ) ⇔ «solvable»(q, r, F, ρ)",
												},
												Derive(func(m *Argument) {
													F := m.FixAs[FieldOps[A]]("F")
													ρ := m.FixAs[Fun[Nat, A]]("ρ")
													model := m.Conjuncts(
														m.Assume(),
														"F is an algebraically closed field",
														"ρ assigns elements of F to U",
														"the leading coefficient of q survives")
													opened := m.Conjuncts(
														GroupPremises(model[0], model[1], ModelSpecialization.At(U, F, ρ)),
														"F is a field",
														"specialization at ρ is a ring homomorphism",
														"that keeps zero")
													fieldOn, specialization := opened[0], opened[1]
													agree := m.Have(
														"at a root of the specialization of q, those of p and r vanish together",
														Statement{
															Binders: "∀x:A.",
															Hypotheses: []string{
																"x ∈ F.carrier",
																"«value»(F, ρ, q, x) = F.zero",
															},
															Conclusion: "«value»(F, ρ, p, x) = F.zero ⇔ «value»(F, ρ, r, x) = F.zero",
														},
														By(
															fieldOn,
															specialization,
															model[2],
															parts[2].At(
																F,
																m.TermAs[Fun[IntegerPolynomial, A]](
																	"λu:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, u)"))))
													m.Iff()
													m.Forward(
														"a common solution of p and q is a root of q, where r vanishes with p",
														func(u *Argument, solution Fact) {
															x, at := u.UnpackAs[A](solution, "x")
															u.Show(
																"at the same point",
																Witness(x),
																By(at, agree.At(x)))
														})
													m.Backward(
														"a common solution of q and r is a root of q, where p vanishes with r",
														func(u *Argument, solution Fact) {
															x, at := u.UnpackAs[A](solution, "x")
															u.Show(
																"at the same point",
																Witness(x),
																By(at, agree.At(x)))
														})
												}))
											e.Show(
												"the induction decides the pair q, r, whose system is "+
													"that of p, q where the leading coefficient of q survives",
												By(
													DecisionByEquivalence.At(
														U,
														models,
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
															"«survives»(q(polynomial_degree(integer_polynomial_ring.zero, q)))"),
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(p, q)"),
														e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(q, r)")),
													qOver,
													parts[0],
													smaller,
													lower.At(
														e.TermAs[Nat](
															"polynomial_degree(integer_polynomial_ring.zero, q) + "+
																"polynomial_degree(integer_polynomial_ring.zero, r)"),
														q,
														r),
													sameSystem))
										})
								}))
							c.Show(
								"the leading coefficient of q in front of the two lists decides the pair",
								By(
									DecisionByCases.At(
										U,
										c.TermAs[IntegerPolynomial]("q(polynomial_degree(integer_polynomial_ring.zero, q))"),
										c.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(p, q)")),
									leadIn,
									vanishing,
									surviving))
						}))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			U *Expr[Set[Nat]],
			k *Expr[Nat],
			g *Expr[Fun2[Nat, Nat, IntegerPolynomial]],
			h *Arrow[Nat, IntegerPolynomial],
			fewer, gOver Fact,
		) {
			models := a.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«models»")
			lastIndices := a.Have(
				"k and k + 1 lie below k + 2",
				"k < suc(suc(k)) ∧ suc(k) < suc(suc(k))",
				ByArith())
			members := a.Have(
				"so g(k) and g(k + 1) are parameter polynomials",
				"«overParameters»(g(k)) ∧ «overParameters»(g(suc(k)))",
				By(gOver, lastIndices))
			last := a.Have(
				"the last two equations are decided, in whichever order puts the lower degree second",
				"«decided»(g(k), g(suc(k)))",
				Derive(func(b *Argument) {
					b.Cases(b.Term(
						"polynomial_degree(integer_polynomial_ring.zero, g(suc(k))) ≤ " +
							"polynomial_degree(integer_polynomial_ring.zero, g(k))"))
					b.When(
						"g(k + 1) has degree at most that of g(k)",
						func(c *Argument, ordered Fact) {
							c.Show(
								"the pair g(k), g(k + 1) itself",
								By(
									fewer,
									gOver,
									members,
									ordered,
									At(
										reduced,
										U,
										k,
										g,
										h,
										c.TermAs[Nat](
											"polynomial_degree(integer_polynomial_ring.zero, g(k)) + "+
												"polynomial_degree(integer_polynomial_ring.zero, g(suc(k)))"),
										c.TermAs[Fun[Nat, IntegerPolynomial]]("g(k)"),
										c.TermAs[Fun[Nat, IntegerPolynomial]]("g(suc(k))"))))
						})
					b.Otherwise(
						"g(k) has the lower degree: the pair g(k + 1), g(k) is decided, and has the same common solutions",
						func(c *Argument, reversed Fact) {
							swapped := c.Have(
								"g(k) has degree at most that of g(k + 1)",
								"polynomial_degree(integer_polynomial_ring.zero, g(k)) ≤ "+
									"polynomial_degree(integer_polynomial_ring.zero, g(suc(k)))",
								ByArith(reversed))
							sameSystem := c.Have(
								"the system reads the two equations in either order",
								"∀F:field_ops(A). ∀ρ:(num → A). "+
									"    «solvable»(g(k), g(suc(k)), F, ρ) ⇔ «solvable»(g(suc(k)), g(k), F, ρ)",
								Derive(func(m *Argument) {
									m.FixAs[FieldOps[A]]("F")
									m.FixAs[Fun[Nat, A]]("ρ")
									m.Iff()
									m.Forward(
										"a solution of g(k), g(k + 1) solves g(k + 1), g(k)",
										func(u *Argument, solution Fact) {
											x, at := u.UnpackAs[A](solution, "x")
											u.Show(
												"at the same point",
												Witness(x),
												By(at))
										})
									m.Backward(
										"a solution of g(k + 1), g(k) solves g(k), g(k + 1)",
										func(u *Argument, solution Fact) {
											x, at := u.UnpackAs[A](solution, "x")
											u.Show(
												"at the same point",
												Witness(x),
												By(at))
										})
								}))
							swappedDecided := c.Have(
								"the pair g(k + 1), g(k) is decided",
								"«decided»(g(suc(k)), g(k))",
								By(
									fewer,
									gOver,
									members,
									swapped,
									At(
										reduced,
										U,
										k,
										g,
										h,
										c.TermAs[Nat](
											"polynomial_degree(integer_polynomial_ring.zero, g(suc(k))) + "+
												"polynomial_degree(integer_polynomial_ring.zero, g(k))"),
										c.TermAs[Fun[Nat, IntegerPolynomial]]("g(suc(k))"),
										c.TermAs[Fun[Nat, IntegerPolynomial]]("g(k)"))))
							c.Show(
								"and has the system of g(k), g(k + 1)",
								By(
									DecisionByEquivalence.At(
										U,
										models,
										models,
										c.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(g(k), g(suc(k)))"),
										c.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(g(suc(k)), g(k))")),
									swappedDecided,
									sameSystem))
						})
				}))
			sameSystem := a.Have(
				"the indices below k + 2 are those below k, then k and k + 1",
				"∀F:field_ops(A). ∀ρ:(num → A). "+
					"    «system»(suc(suc(k)), g, h, F, ρ) ⇔ «solvable»(g(k), g(suc(k)), F, ρ)",
				Derive(func(b *Argument) {
					b.FixAs[FieldOps[A]]("F")
					b.FixAs[Fun[Nat, A]]("ρ")
					indices := b.Have(
						"an index below k + 2 is below k, or k, or k + 1",
						"∀j:num. j < suc(suc(k)) ⇔ j < k ∨ j = k ∨ j = suc(k)",
						b.ForEach(func(j *Expr[Nat]) Action { return ByArith() }))
					b.Iff()
					b.Forward(
						"a solution of the k + 2 equations solves those below k and the last two",
						func(u *Argument, solution Fact) {
							x, at := u.UnpackAs[A](solution, "x")
							u.Show(
								"at the same point",
								Witness(x),
								By(at, indices))
						})
					b.Backward(
						"a solution of those below k and the last two solves the k + 2 equations",
						func(u *Argument, solution Fact) {
							x, at := u.UnpackAs[A](solution, "x")
							u.Show(
								"at the same point",
								Witness(x),
								By(at, indices))
						})
				}))
			a.Show(
				"the last pair is decided, and has the system of the k + 2 equations",
				By(
					DecisionByEquivalence.At(
						U,
						models,
						models,
						a.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«system»(suc(suc(k)), g, h)"),
						a.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«solvable»(g(k), g(suc(k)))")),
					last,
					sameSystem))
		})
	}),
})}

// ParameterizedSystemDecision — whether finitely many equations and one
// inequation have a common solution is decided by the zero pattern of
// finitely many parameter polynomials: by induction on the number of
// equations, NoEquationDecision deciding none, SingleEquationDecision one,
// and PairReduction removing one of two or more; with none or one equation
// the system is the decided one read at fewer indices
// (DecisionByEquivalence).
var ParameterizedSystemDecision = parameterizedSystemDecisionThm{family.Add(registry.ProofEntry{
	Name: "ParameterizedSystemDecision",
	Key:  "prop_dd7c0fe680a97e5e",
	Reading: "The g(j) and h are polynomials in v whose coefficients are integer polynomials in the " +
		"parameters U; the field and the parameter environment specialize every coefficient. E and D are " +
		"chosen before the field and the environment; they may depend on the type A, not on F or ρ. With " +
		"k = 0 the system asks only that h take a nonzero value, which over an algebraically closed " +
		"field is a condition on h's coefficients (NoEquationDecision). field_on is load-bearing: a " +
		"specialized nonzero leading coefficient is a unit (polynomial_division.PseudoRemainderDivides).",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀k:num. " +
			"∀g:(num → num → ((num → num) → int)). " +
			"∀h:(num → ((num → num) → int)).",
		Hypotheses: []string{
			"∀j:num. j < k ⇒ «overParameters»(g(j))",
			"«overParameters»(h)",
		},
		Conclusion: "decided_by_zero_patterns(U, «models», «system»(k, g, h))",
	}, func(a *Argument, U *Expr[Set[Nat]], k *Expr[Nat]) {
		models := a.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«models»")
		a.Show(
			"induct on the number of equations, for every system of that many",
			ByInduction(
				peano.Induction.At(
					a.TermAs[Set[Nat]](
						"λn:num. ∀g:(num → num → ((num → num) → int)). ∀h:(num → ((num → num) → int)). "+
							"    (∀j:num. j < n ⇒ «overParameters»(g(j))) ∧ «overParameters»(h) ⇒ "+
							"    decided_by_zero_patterns(U, «models», «system»(n, g, h))"),
					k),
				Case(
					"with no equation the system asks only that h not vanish, which NoEquationDecision decides",
					Derive(func(b *Argument) {
						b.FixAs[Fun2[Nat, Nat, IntegerPolynomial]]("g")
						h := b.FixAs[Fun[Nat, IntegerPolynomial]]("h")
						over := b.Assume()
						b.Show(
							"no index lies below zero, so the system is that h be nonzero somewhere",
							By(
								DecisionByEquivalence.At(
									U,
									models,
									models,
									b.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«system»(0, g, h)"),
									b.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«nonzeroSomewhere»(h)")),
								NoEquationDecision.Inst[A]().At(U, h),
								over,
								nat_order.LessThanZeroClause))
					})),
				Case(
					"if every system of n equations is decided, so is every system of suc(n)",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						fewer := b.Assume()
						g := b.FixAs[Fun2[Nat, Nat, IntegerPolynomial]]("g")
						h := b.FixAs[Fun[Nat, IntegerPolynomial]]("h")
						over := b.Assume()
						b.Cases(b.Term("n = 0"))
						b.When(
							"a single equation g(0), which SingleEquationDecision decides",
							func(c *Argument, zero Fact) {
								single := c.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
									"λF:field_ops(A). λρ:(num → A). ∃x:A. " +
										"    x ∈ F.carrier ∧ «value»(F, ρ, g(0), x) = F.zero ∧ «value»(F, ρ, h, x) ≠ F.zero")
								below := c.Have(
									"the one index below suc(n) is zero",
									"∀j:num. j < suc(n) ⇔ j = 0",
									c.ForEach(func(j *Expr[Nat]) Action { return ByArith(zero) }))
								c.Show(
									"SingleEquationDecision decides the equation g(0) with "+
										"the inequation h, which is the system of suc(n) equations",
									By(
										DecisionByEquivalence.At(
											U,
											models,
											models,
											c.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«system»(suc(n), g, h)"),
											single),
										SingleEquationDecision.Inst[A]().At(U, c.TermAs[Fun[Nat, IntegerPolynomial]]("g(0)"), h),
										over,
										nat_order.ZeroLessThanSuc,
										below))
							})
						b.Otherwise(
							"two or more equations, which PairReduction reduces by one",
							func(c *Argument, nonzero Fact) {
								m, predecessor := c.ObtainAs[Nat](
									"n is the successor of some m",
									"∃m:num. n = suc(m)",
									By(Normalized, nonzero, peano.Cases.At(n)))
								c.Do(predecessor.Rw())
								c.Show(
									"PairReduction lowers suc(suc(m)) equations to suc(m), which the induction decides",
									By(PairReduction.Inst[A]().At(U, m, g, h), fewer, over))
							})
					}))))
	}),
})}

// DecisionByLargerList — a property of the models decided by the zero
// pattern of a list E₁ is decided by the zero pattern of any list E₂
// holding the members of E₁. The decision set holds the patterns of E₂
// the models with the property realize: two models with one pattern of E₂
// agree on its members (ZeroPatternAgreement), so on those of E₁, and so
// have one pattern of E₁, which decides the property.
var DecisionByLargerList = decisionByLargerListThm{family.Add(registry.ProofEntry{
	Name: "DecisionByLargerList",
	Key:  "prop_b2a44fc33d499a0d",
	Build: family.Theorem(Statement{
		Binders: "∀E₁ E₂:list((num → num) → int). ∀M Φ:(field_ops(A) → (num → A) → bool).",
		Hypotheses: []string{
			"∀p:((num → num) → int). list_member(p, E₁) ⇒ list_member(p, E₂)",
			"zero_pattern_decides(E₁, M, Φ)",
		},
		Conclusion: "zero_pattern_decides(E₂, M, Φ)",
	}, func(
		a *Argument,
		E1, E2 *Expr[List[IntegerPolynomial]],
		M, Φ *Arrow2[FieldOps[A], Fun[Nat, A], Bool],
		inside, decided Fact,
	) {
		_, decides := a.Unpack(a.Unfolded(decided, zeroPatternDecidesDef), "D₁")
		a.Do(Unfold(zeroPatternDecidesDef))
		a.Take(a.TermAs[Set[List[Bool]]](
			"{s:list(bool) | " +
				"    ∃G:field_ops(A). ∃τ:(num → A). M(G, τ) ∧ Φ(G, τ) ∧ s = polynomial_zero_pattern(G, τ, E₂)}"))
		a.Show(
			"a model has the property exactly when its pattern of E₂ is one a model with the property realizes",
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				model := b.Assume()
				b.Iff()
				b.Forward(
					"a model with the property realizes its own pattern",
					func(c *Argument, holds Fact) {
						c.Show(
							"F and ρ themselves witness the membership",
							By(holds, model))
					})
				b.Backward(
					"a model with the pattern of E₂ of one with the property has its pattern of E₁ too",
					func(c *Argument, realized Fact) {
						G, τ, other := c.Unpack2As[FieldOps[A], Fun[Nat, A]](realized, "G", "τ")
						witness := c.Conjuncts(
							other,
							"G and τ are a model",
							"with the property",
							"and the pattern of E₂ of F and ρ")
						same := c.Have(
							"the two models agree on the members of E₂, so on those of E₁, and have one pattern of E₁",
							"polynomial_zero_pattern(F, ρ, E₁) = polynomial_zero_pattern(G, τ, E₁)",
							By(
								inside,
								witness[2],
								ZeroPatternAgreement.At(F, G, ρ, τ, E2),
								ZeroPatternAgreement.At(F, G, ρ, τ, E1)))
						c.Show(
							"G has the property, so its pattern of E₁, which is F's, lies in D₁",
							By(Normalized, decides.At(F, ρ), decides.At(G, τ), same, model, witness[0], witness[1]))
					})
			}))
	}),
})}

// ParameterizedZeroPatterns — the zero patterns a list P of polynomials in
// the parameters U and v takes along v are determined, uniformly over
// algebraically closed fields, by the zero pattern of finitely many parameter
// polynomials E. A lemma inducts on P carrying a system beside it, equations
// g(j), j < k, and an inequation h, all polynomials in U and v: for every
// pattern t one list E decides whether the system has a solution x at which P
// has the pattern t. With P empty the pattern is nil, and
// ParameterizedSystemDecision decides the system read through the coefficient
// sequences in v (CoefficientEvaluation). In front of P a head p either
// vanishes, joining the equations, or does not, joining the inequation as a
// factor, specialization being a ring homomorphism and a field having no zero
// divisors; the lists of the two cases, joined, decide both
// (DecisionByLargerList). At no equation and the inequation one, B(s) holds
// the patterns of the length of P whose decision set holds s, finitely many
// (BoolListsOfLengthFinite).
var ParameterizedZeroPatterns = parameterizedZeroPatternsThm{family.Add(registry.ProofEntry{
	Name: "ParameterizedZeroPatterns",
	Key:  "prop_b6fe404019c41421",
	Reading: "E and B are chosen before the field and the environment; they may " +
		"depend on the type A, not on F or ρ. U may be infinite and may contain v: " +
		"the pattern of P along v never reads ρ(v). For an empty input list the " +
		"realized pattern set is the singleton empty list, not the empty set.",
	Build: family.Sections(Statement{
		Binders: "∀U:set(num). ∀v:num. ∀P:list((num → num) → int).",
		Hypotheses: []string{
			"polynomial_list_over(U ∪ {v}, P)",
		},
		Conclusion: "∃E:list((num → num) → int). ∃B:(list(bool) → set(list(bool))). " +
			"    polynomial_list_over(U, E) ∧ " +
			"    (∀s:list(bool). " +
			"        finite(B(s)) ∧ (∀t:list(bool). t ∈ B(s) ⇒ list_length(t) = list_length(P))) ∧ " +
			"    (∀F:field_ops(A). ∀ρ:(num → A). " +
			"        algebraically_closed_field_on(F) ∧ fo_env_ok(F.carrier, U, ρ) ⇒ " +
			"        {polynomial_zero_pattern(F, fo_update(ρ, v, x), P) | x:A | x ∈ F.carrier} = " +
			"        B(polynomial_zero_pattern(F, ρ, E)))",
		Abbrev: Abbrev{
			{Name: "realized", Text: "λk:num. " +
				"λg:(num → ((num → num) → int)). " +
				"λh:((num → num) → int). " +
				"λP:list((num → num) → int). " +
				"λt:list(bool). " +
				"λF:field_ops(A). " +
				"λρ:(num → A). " +
				"∃x:A. " +
				"    x ∈ F.carrier ∧ " +
				"    (∀j:num. j < k ⇒ ring_formula_atom(F, g(j), fo_update(ρ, v, x))) ∧ " +
				"    ¬ring_formula_atom(F, h, fo_update(ρ, v, x)) ∧ " +
				"    polynomial_zero_pattern(F, fo_update(ρ, v, x), P) = t"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		decide := ctx.Lemma(Statement{
			Binders: "∀U:set(num). " +
				"∀v:num. " +
				"∀P:list((num → num) → int). " +
				"∀k:num. " +
				"∀g:(num → ((num → num) → int)). " +
				"∀h:((num → num) → int).",
			Hypotheses: []string{
				"polynomial_list_over(U ∪ {v}, P)",
				"∀j:num. j < k ⇒ g(j) ∈ polynomial_algebra(int_ring, U ∪ {v})",
				"h ∈ polynomial_algebra(int_ring, U ∪ {v})",
			},
			Conclusion: "∃E:list((num → num) → int). " +
				"    polynomial_list_over(U, E) ∧ " +
				"    (∀t:list(bool). zero_pattern_decides(E, «models», «realized»(k, g, h, P, t)))",
		}, func(a *Argument, U *Expr[Set[Nat]], v *Expr[Nat], P *Expr[List[IntegerPolynomial]]) {
			a.Induct(P)
			a.Base(
				"with no polynomial left the pattern is nil, and ParameterizedSystemDecision decides the system",
				func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.FixAs[Fun[Nat, IntegerPolynomial]]("g")
					h := b.FixAs[IntegerPolynomial]("h")
					given := b.Conjuncts(
						b.Assume(),
						"nil lists polynomials in U and v",
						"the g(j), j < k, are polynomials in U and v",
						"and so is h")
					coefficients := b.Have(
						"the coefficients in v of a polynomial in U and v are parameter polynomials",
						Statement{
							Binders:    "∀q:((num → num) → int).",
							Hypotheses: []string{"q ∈ polynomial_algebra(int_ring, U ∪ {v})"},
							Conclusion: "«overParameters»(integer_polynomial_coefficient(v, q))",
						},
						Derive(func(c *Argument) {
							q := c.FixAs[IntegerPolynomial]("q")
							own := c.Conjuncts(
								c.Have(
									"q is an integer polynomial whose variables lie in U and v",
									"integer_polynomial(q) ∧ integer_polynomial_vars(q) ⊆ U ∪ {v}",
									By(c.Assume(), polynomial_formula.PolynomialOnVariables.At(c.TermAs[Set[Nat]]("U ∪ {v}"), q))),
								"q is an integer polynomial",
								"whose variables lie in U and v")
							others := c.Have(
								"so its variables other than v lie in U",
								"integer_polynomial_vars(q) ∖ {v} ⊆ U",
								BySets(own[1]))
							c.Show(
								"its coefficients in v are polynomials on those variables, so parameter polynomials",
								By(
									own[0],
									polynomial_formula.CoefficientsOverParameters.At(v, q),
									polynomial_algebra.PolynomialAlgebraSubset.At(
										c.TermAs[module_record.RingOps[Int]]("int_ring"),
										c.TermAs[Set[Nat]]("integer_polynomial_vars(q) ∖ {v}"),
										U),
									others,
									polynomial.PolynomialOverMono))
						}))
					gOver := b.Have(
						"so the coefficient sequences in v of the g(j) are parameter polynomials",
						"∀j:num. j < k ⇒ «overParameters»(integer_polynomial_coefficient(v, g(j)))",
						By(coefficients, given[1]))
					hOver := b.Have(
						"and so is that of h",
						"«overParameters»(integer_polynomial_coefficient(v, h))",
						By(coefficients, given[2]))
					E, decides := b.UnpackAs[List[IntegerPolynomial]](
						b.Unfolded(
							GroupPremises(
								gOver,
								hOver,
								ParameterizedSystemDecision.Inst[A]().At(
									U,
									k,
									b.TermAs[Fun2[Nat, Nat, IntegerPolynomial]]("λj:num. integer_polynomial_coefficient(v, g(j))"),
									b.TermAs[Fun[Nat, IntegerPolynomial]]("integer_polynomial_coefficient(v, h)"))),
							decidedByZeroPatternsDef),
						"E")
					decision := b.Conjuncts(
						decides,
						"E lists parameter polynomials",
						"whose pattern decides the system of coefficient sequences")
					_, system := b.Unpack(b.Unfolded(decision[1], zeroPatternDecidesDef), "D₀")
					b.Take(E)
					b.Show(
						"E decides the system for the one pattern of nil, which is nil",
						SplitConj(
							Case(
								"E lists parameter polynomials",
								By(decision[0])),
							Case(
								"a pattern t is realized exactly when t is nil and the pattern of E lies in D₀",
								Derive(func(c *Argument) {
									c.FixAs[List[Bool]]("t")
									c.Do(Unfold(zeroPatternDecidesDef))
									c.Take(c.TermAs[Set[List[Bool]]]("{s:list(bool) | t = nil ∧ s ∈ D₀}"))
									F := c.FixAs[FieldOps[A]]("F")
									ρ := c.FixAs[Fun[Nat, A]]("ρ")
									model := c.Conjuncts(
										c.Assume(),
										"F is an algebraically closed field",
										"ρ assigns elements of F to U")
									fieldOn := algebraic_closure.FieldOn.Read(model[0])
									reads := c.Have(
										"a polynomial in U and v vanishes at x along v "+
											"exactly when its specialized coefficient sequence does",
										Statement{
											Binders:    "∀q:((num → num) → int). ∀x:A.",
											Hypotheses: []string{"q ∈ polynomial_algebra(int_ring, U ∪ {v})", "x ∈ F.carrier"},
											Conclusion: "ring_formula_atom(F, q, fo_update(ρ, v, x)) ⇔ " +
												"«value»(F, ρ, integer_polynomial_coefficient(v, q), x) = F.zero",
										},
										Derive(func(e *Argument) {
											q := e.FixAs[IntegerPolynomial]("q")
											x := e.FixAs[A]("x")
											point := e.Conjuncts(
												e.Assume(),
												"q is a polynomial in U and v",
												"x lies in F")
											own := e.Conjuncts(
												e.Have(
													"q is an integer polynomial whose variables lie in U and v",
													"integer_polynomial(q) ∧ integer_polynomial_vars(q) ⊆ U ∪ {v}",
													By(point[0], polynomial_formula.PolynomialOnVariables.At(e.TermAs[Set[Nat]]("U ∪ {v}"), q))),
												"q is an integer polynomial",
												"whose variables lie in U and v")
											legal := e.Have(
												"ρ is legal on the variables of q other than v, which lie in U",
												"fo_env_ok(F.carrier, integer_polynomial_vars(q) ∖ {v}, ρ)",
												BySets(
													own[1],
													model[1],
													first_order.EnvOKSubset.At(
														e.TermAs[Set[A]]("F.carrier"), e.TermAs[Set[Nat]]("integer_polynomial_vars(q) ∖ {v}"), U, ρ)))
											e.Show(
												"evaluating q with v sent to x is evaluating its coefficients at x",
												By(
													own[0],
													point[1],
													legal,
													ring_formula.RingFormulaAtomDef.At(F, q, e.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")),
													polynomial_formula.CoefficientEvaluation.At(
														e.TermAs[module_record.RingOps[A]]("field_ring(F)"), ρ, q, v, x),
													field.RingOn.Read(fieldOn)))
										}))
									along := c.Have(
										"so at a point x the system holds exactly when the system of coefficient sequences does",
										Statement{
											Binders:    "∀x:A.",
											Hypotheses: []string{"x ∈ F.carrier"},
											Conclusion: "(∀j:num. j < k ⇒ ring_formula_atom(F, g(j), fo_update(ρ, v, x))) ∧ " +
												"¬ring_formula_atom(F, h, fo_update(ρ, v, x)) ⇔ " +
												"(∀j:num. j < k ⇒ «value»(F, ρ, integer_polynomial_coefficient(v, g(j)), x) = F.zero) ∧ " +
												"«value»(F, ρ, integer_polynomial_coefficient(v, h), x) ≠ F.zero",
										},
										Derive(func(e *Argument) {
											x := e.FixAs[A]("x")
											xIn := e.Assume()
											each := e.Have(
												"each equation g(j) reads its coefficient sequence",
												Statement{
													Binders: "∀j:num.",
													Hypotheses: []string{
														"j < k",
													},
													Conclusion: "ring_formula_atom(F, g(j), fo_update(ρ, v, x)) ⇔ " +
														"«value»(F, ρ, integer_polynomial_coefficient(v, g(j)), x) = F.zero",
												},
												Derive(func(f *Argument) {
													j := f.FixAs[Nat]("j")
													f.Show(
														"g(j) is a polynomial in U and v",
														By(reads.At(f.TermAs[IntegerPolynomial]("g(j)"), x), given[1].At(j), xIn))
												}))
											inequation := e.Have(
												"and so does the inequation h",
												"ring_formula_atom(F, h, fo_update(ρ, v, x)) ⇔ "+
													"«value»(F, ρ, integer_polynomial_coefficient(v, h), x) = F.zero",
												By(reads.At(h, x), given[2], xIn))
											e.Show(
												"so the two systems hold together",
												By(each, inequation))
										}))
									nilPattern := c.Have(
										"the pattern of nil is nil",
										"∀σ:(num → A). polynomial_zero_pattern(F, σ, nil) = nil",
										By(zeroPatternDef, list.ListMapDef))
									same := c.Have(
										"the system has a solution realizing t exactly when t is "+
											"nil and the system of coefficient sequences has a solution",
										"«realized»(k, g, h, nil⟨A:((num → num) → int)⟩, t, F, ρ) ⇔ "+
											"t = nil⟨A:bool⟩ ∧ "+
											"(∃x:A. "+
											"    x ∈ F.carrier ∧ "+
											"    (∀j:num. j < k ⇒ «value»(F, ρ, integer_polynomial_coefficient(v, g(j)), x) = F.zero) ∧ "+
											"    «value»(F, ρ, integer_polynomial_coefficient(v, h), x) ≠ F.zero)",
										Derive(func(e *Argument) {
											e.Iff()
											e.Forward(
												"a solution x realizing t solves the system of "+
													"coefficient sequences, and t is the pattern nil of nil",
												func(f *Argument, solution Fact) {
													x, at := f.UnpackAs[A](solution, "x")
													f.Show(
														"at the same point",
														By(at, along.At(x), nilPattern.At(f.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)"))))
												})
											e.Backward(
												"for t nil, a solution of the system of coefficient sequences realizes t",
												func(f *Argument, both Fact) {
													parts := f.Conjuncts(
														both,
														"t is nil",
														"the system of coefficient sequences has a solution")
													x, at := f.UnpackAs[A](parts[1], "x")
													f.Show(
														"at the same point",
														Witness(x),
														By(at, parts[0], along.At(x), nilPattern.At(f.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)"))))
												})
										}))
									c.Show(
										"which the pattern of E decides",
										By(same, system.At(F, ρ), model[0], model[1]))
								}))))
				})
			a.Step(
				"a head p in front of P vanishes, joining the equations, "+
					"or does not, joining the inequation as a factor",
				func(b *Argument, ih Fact) {
					b.StepArgs("p", "P")
					k := b.FixAs[Nat]("k")
					g := b.FixAs[Fun[Nat, IntegerPolynomial]]("g")
					h := b.FixAs[IntegerPolynomial]("h")
					p := b.TermAs[IntegerPolynomial]("p")
					given := b.Conjuncts(
						b.Assume(),
						"cons(p, P) lists polynomials in U and v",
						"the g(j), j < k, are polynomials in U and v",
						"and so is h")
					head := b.Have(
						"p is a polynomial in U and v",
						"p ∈ polynomial_algebra(int_ring, U ∪ {v})",
						By(
							given[0],
							polynomial_formula.PolynomialListOverDef,
							list.ListMemberDef,
							polynomial_formula.PolynomialOnVariables.At(b.TermAs[Set[Nat]]("U ∪ {v}"), p)))
					tail := b.Have(
						"and P lists polynomials in U and v",
						"polynomial_list_over(U ∪ {v}, P)",
						By(given[0], polynomial_formula.PolynomialListOverDef, list.ListMemberDef))
					extended := b.Have(
						"the g(j), j < k, and p are polynomials in U and v",
						"∀j:num. j < suc(k) ⇒ COND(j < k, g(j), p) ∈ polynomial_algebra(int_ring, U ∪ {v})",
						b.ForEach(func(j *Expr[Nat]) Action { return By(given[1].At(j), head) }))
					product := b.Have(
						"and so is the product of h and p, the polynomials in U and v forming a subring",
						"polynomial_algebra_mul(int_ring, h, p) ∈ polynomial_algebra(int_ring, U ∪ {v})",
						By(
							given[2],
							head,
							comm_ring.SubringMul.At(
								b.TermAs[module_record.RingOps[IntegerPolynomial]]("integer_polynomial_ring"),
								b.TermAs[Set[IntegerPolynomial]]("polynomial_algebra(int_ring, U ∪ {v})"),
								h,
								p),
							polynomial_formula.ParameterPolynomialsSubring.At(b.TermAs[Set[Nat]]("U ∪ {v}"))))
					E1, inEquations := b.UnpackAs[List[IntegerPolynomial]](
						GroupPremises(
							tail,
							extended,
							given[2],
							ih.At(
								b.TermAs[Nat]("suc(k)"), b.TermAs[Fun[Nat, IntegerPolynomial]]("λj:num. COND(j < k, g(j), p)"), h)),
						"E₁")
					E2, inInequation := b.UnpackAs[List[IntegerPolynomial]](
						GroupPremises(
							tail,
							given[1],
							product,
							ih.At(k, g, b.TermAs[IntegerPolynomial]("polynomial_algebra_mul(int_ring, h, p)"))),
						"E₂")
					first := b.Conjuncts(
						inEquations,
						"E₁ lists parameter polynomials",
						"and decides every pattern of P with p among the equations")
					second := b.Conjuncts(
						inInequation,
						"E₂ lists parameter polynomials",
						"and decides every pattern of P with p a factor of the inequation")
					E := b.TermAs[List[IntegerPolynomial]]("list_append(E₁, E₂)")
					firstInside := b.Have(
						"the members of E₁ are members of E₁ followed by E₂",
						"∀q:((num → num) → int). list_member(q, E₁) ⇒ list_member(q, list_append(E₁, E₂))",
						By(list.MemberAppend))
					secondInside := b.Have(
						"and so are those of E₂",
						"∀q:((num → num) → int). list_member(q, E₂) ⇒ list_member(q, list_append(E₁, E₂))",
						By(list.MemberAppend))
					pattern := b.Have(
						"the pattern of cons(p, P) is the atom of p in front of the pattern of P",
						"∀F:field_ops(A). ∀σ:(num → A). "+
							"    polynomial_zero_pattern(F, σ, cons(p, P)) = "+
							"    cons(ring_formula_atom(F, p, σ), polynomial_zero_pattern(F, σ, P))",
						By(zeroPatternDef, list.ListMapDef))
					dropped := b.Have(
						"the equations g(j), j < k, and p hold exactly when the g(j) and p vanish",
						"∀F:field_ops(A). ∀σ:(num → A). "+
							"    (∀j:num. j < suc(k) ⇒ ring_formula_atom(F, COND(j < k, g(j), p), σ)) ⇔ "+
							"    (∀j:num. j < k ⇒ ring_formula_atom(F, g(j), σ)) ∧ ring_formula_atom(F, p, σ)",
						By(nat_order.LessThanSucClause, nat_order.LessThanIrrefl))
					multiplies := b.Have(
						"in a field h times p vanishes along v exactly when h or p does",
						Statement{
							Binders:    "∀F:field_ops(A). ∀ρ:(num → A). ∀x:A.",
							Hypotheses: []string{"field_on(F)", "fo_env_ok(F.carrier, U, ρ)", "x ∈ F.carrier"},
							Conclusion: "ring_formula_atom(F, polynomial_algebra_mul(int_ring, h, p), fo_update(ρ, v, x)) ⇔ " +
								"ring_formula_atom(F, h, fo_update(ρ, v, x)) ∨ ring_formula_atom(F, p, fo_update(ρ, v, x))",
						},
						Derive(func(c *Argument) {
							F := c.FixAs[FieldOps[A]]("F")
							ρ := c.FixAs[Fun[Nat, A]]("ρ")
							x := c.FixAs[A]("x")
							point := c.Conjuncts(
								c.Assume(),
								"F is a field",
								"ρ assigns elements of F to U",
								"x lies in F")
							updated := c.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")
							legal := c.Have(
								"ρ updated at v by x is legal on U and v",
								"fo_env_ok(F.carrier, U ∪ {v}, fo_update(ρ, v, x))",
								BySets(
									point[1],
									point[2],
									first_order.EnvOKUpdate.At(c.TermAs[Set[A]]("F.carrier"), c.TermAs[Set[Nat]]("U ∪ {v}"), ρ, v, x),
									first_order.EnvOKSubset.At(
										c.TermAs[Set[A]]("F.carrier"), c.TermAs[Set[Nat]]("(U ∪ {v}) ∖ {v}"), U, ρ)))
							specialization := c.Have(
								"specialization there is a ring homomorphism on the polynomials in U and v",
								"ring_homomorphism(«parameterRing»(U ∪ {v}), "+
									"    field_ring(F), "+
									"    λq:((num → num) → int). integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), q))",
								By(
									legal,
									polynomial_formula.IntegerPolynomialEvalHom.Read(field.RingOn.Read(point[0])).At(
										c.TermAs[Set[Nat]]("U ∪ {v}"), updated)))
							c.Show(
								"specialization keeps the product, and a field has no zero divisors",
								By(
									given[2],
									head,
									ring_homomorphism.MapMul.Read(specialization).AsFact().At(h, p),
									ring_homomorphism.MapIn.Read(specialization).AsFact().At(h),
									ring_homomorphism.MapIn.Read(specialization).AsFact().At(p),
									field.MulEqZeroOn.Read(point[0]),
									ring_formula.RingFormulaAtomDef.At(F, h, updated),
									ring_formula.RingFormulaAtomDef.At(F, p, updated),
									ring_formula.RingFormulaAtomDef.At(
										F, c.TermAs[IntegerPolynomial]("polynomial_algebra_mul(int_ring, h, p)"), updated)))
						}))
					firstMembers := b.Unfolded(first[0], polynomial_formula.PolynomialListOverDef)
					secondMembers := b.Unfolded(second[0], polynomial_formula.PolynomialListOverDef)
					b.Take(E)
					b.Show(
						"E₁ followed by E₂ lists parameter polynomials and decides every pattern of cons(p, P)",
						SplitConj(
							Case(
								"the members of E₁ and E₂ are parameter polynomials",
								Unfold(polynomial_formula.PolynomialListOverDef),
								By(firstMembers, secondMembers, list.MemberAppend)),
							Case(
								"a pattern of cons(p, P) is nil, which no point realizes, or a head in front of a pattern of P",
								Derive(func(c *Argument) {
									t := c.FixAs[List[Bool]]("t")
									nonempty := c.Unless(
										c.Term("t = nil"),
										"the pattern of cons(p, P) is a cons, never nil",
										Given(func(d *Argument, empty Fact) {
											d.Do(Unfold(zeroPatternDecidesDef))
											d.Take(d.TermAs[Set[List[Bool]]]("∅"))
											d.Show(
												"so no point realizes t, and no pattern lies in the empty set",
												BySets(empty, pattern, list.NilNotCons.Inst[Bool]()))
										}))
									marked, s, split := c.Obtain2As[Bool, List[Bool]](
										"a list other than nil is a head in front of a tail",
										"∃b:bool. ∃s:list(bool). t = cons(b, s)",
										By(nonempty, list.Cases.At(t)))
									c.Do(split.Rw())
									c.Cases(marked)
									c.When(
										"b marks p zero: p joins the equations, which E₁ decides with the pattern s of P",
										func(e *Argument, zero Fact) {
											D, decides := e.UnpackAs[Set[List[Bool]]](
												e.Unfolded(
													e.Simplified(GroupPremises(
														firstInside,
														first[1].At(s),
														DecisionByLargerList.At(
															E1,
															E,
															e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«models»"),
															e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
																"«realized»(suc(k), λj:num. COND(j < k, g(j), p), h, P, s)")))),
													zeroPatternDecidesDef),
												"D")
											// At every model the pattern cons(b, s) is realized exactly when the larger system has a solution.
											e.Do(Unfold(zeroPatternDecidesDef))
											e.Take(D)
											F := e.FixAs[FieldOps[A]]("F")
											ρ := e.FixAs[Fun[Nat, A]]("ρ")
											model := e.Assume()
											same := e.Have(
												"a point realizes cons(b, s) with the system exactly "+
													"when it solves p and the system and realizes s",
												"«realized»(k, g, h, cons(p, P), cons(b, s), F, ρ) ⇔ "+
													"«realized»(suc(k), λj:num. COND(j < k, g(j), p), h, P, s, F, ρ)",
												Derive(func(m *Argument) {
													m.Iff()
													m.Forward(
														"a point realizing cons(b, s) solves the larger system",
														func(n *Argument, solution Fact) {
															x, at := n.UnpackAs[A](solution, "x")
															parts := n.Conjuncts(
																at,
																"x lies in F",
																"the g(j), j < k, vanish at x",
																"h does not",
																"cons(p, P) has the pattern cons(b, s) at x")
															updated := n.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")
															n.Show(
																"at the same point, p vanishing and P having the pattern s",
																Witness(x),
																By(
																	parts[0],
																	parts[1],
																	parts[2],
																	parts[3],
																	zero,
																	dropped.At(F, updated),
																	pattern.At(F, updated),
																	list.ConsInjective.At(
																		n.TermAs[Bool]("ring_formula_atom(F, p, fo_update(ρ, v, x))"),
																		n.TermAs[List[Bool]]("polynomial_zero_pattern(F, fo_update(ρ, v, x), P)"),
																		marked,
																		s)))
														})
													m.Backward(
														"a solution of the larger system realizes cons(b, s)",
														func(n *Argument, solution Fact) {
															x, at := n.UnpackAs[A](solution, "x")
															parts := n.Conjuncts(
																at,
																"x lies in F",
																"the g(j), j < k, and p vanish at x",
																"h does not",
																"P has the pattern s at x")
															updated := n.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")
															n.Show(
																"at the same point, p vanishing in front of the pattern s",
																Witness(x),
																By(
																	parts[0],
																	parts[1],
																	parts[2],
																	parts[3],
																	zero,
																	dropped.At(F, updated),
																	pattern.At(F, updated),
																	list.ConsInjective.At(
																		n.TermAs[Bool]("ring_formula_atom(F, p, fo_update(ρ, v, x))"),
																		n.TermAs[List[Bool]]("polynomial_zero_pattern(F, fo_update(ρ, v, x), P)"),
																		marked,
																		s)))
														})
												}))
											e.Show(
												"which the pattern of E decides",
												By(same, decides.At(F, ρ), model))
										})
									c.Otherwise(
										"b marks p nonzero: p joins the inequation, which E₂ decides with the pattern s of P",
										func(e *Argument, nonzero Fact) {
											D, decides := e.UnpackAs[Set[List[Bool]]](
												e.Unfolded(
													e.Simplified(GroupPremises(
														secondInside,
														second[1].At(s),
														DecisionByLargerList.At(
															E2,
															E,
															e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]]("«models»"),
															e.TermAs[Fun2[FieldOps[A], Fun[Nat, A], Bool]](
																"«realized»(k, g, polynomial_algebra_mul(int_ring, h, p), P, s)")))),
													zeroPatternDecidesDef),
												"D")
											// At every model the pattern cons(b, s) is realized exactly when the system with the larger inequation has a solution.
											e.Do(Unfold(zeroPatternDecidesDef))
											e.Take(D)
											F := e.FixAs[FieldOps[A]]("F")
											ρ := e.FixAs[Fun[Nat, A]]("ρ")
											model := e.Conjuncts(
												e.Assume(),
												"F is an algebraically closed field",
												"ρ assigns elements of F to U")
											fieldOn := algebraic_closure.FieldOn.Read(model[0])
											same := e.Have(
												"a point realizes cons(b, s) with the system exactly "+
													"when h times p does not vanish there and it realizes s",
												"«realized»(k, g, h, cons(p, P), cons(b, s), F, ρ) ⇔ "+
													"«realized»(k, g, polynomial_algebra_mul(int_ring, h, p), P, s, F, ρ)",
												Derive(func(m *Argument) {
													m.Iff()
													m.Forward(
														"a point realizing cons(b, s) solves the system with the larger inequation",
														func(n *Argument, solution Fact) {
															x, at := n.UnpackAs[A](solution, "x")
															parts := n.Conjuncts(
																at,
																"x lies in F",
																"the g(j), j < k, vanish at x",
																"h does not",
																"cons(p, P) has the pattern cons(b, s) at x")
															updated := n.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")
															n.Show(
																"at the same point, neither h nor p vanishing and P having the pattern s",
																Witness(x),
																By(
																	parts[0],
																	parts[1],
																	parts[2],
																	parts[3],
																	nonzero,
																	fieldOn,
																	model[1],
																	multiplies.At(F, ρ, x),
																	pattern.At(F, updated),
																	list.ConsInjective.At(
																		n.TermAs[Bool]("ring_formula_atom(F, p, fo_update(ρ, v, x))"),
																		n.TermAs[List[Bool]]("polynomial_zero_pattern(F, fo_update(ρ, v, x), P)"),
																		marked,
																		s)))
														})
													m.Backward(
														"a solution of the system with the larger inequation realizes cons(b, s)",
														func(n *Argument, solution Fact) {
															x, at := n.UnpackAs[A](solution, "x")
															parts := n.Conjuncts(
																at,
																"x lies in F",
																"the g(j), j < k, vanish at x",
																"h times p does not",
																"P has the pattern s at x")
															updated := n.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")
															n.Show(
																"at the same point, p not vanishing in front of the pattern s",
																Witness(x),
																By(
																	parts[0],
																	parts[1],
																	parts[2],
																	parts[3],
																	nonzero,
																	fieldOn,
																	model[1],
																	multiplies.At(F, ρ, x),
																	pattern.At(F, updated),
																	list.ConsInjective.At(
																		n.TermAs[Bool]("ring_formula_atom(F, p, fo_update(ρ, v, x))"),
																		n.TermAs[List[Bool]]("polynomial_zero_pattern(F, fo_update(ρ, v, x), P)"),
																		marked,
																		s)))
														})
												}))
											e.Show(
												"which the pattern of E decides",
												By(same, decides.At(F, ρ), model[0], model[1]))
										})
								}))))
				})
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			U *Expr[Set[Nat]],
			v *Expr[Nat],
			P *Expr[List[IntegerPolynomial]],
			over Fact,
		) {
			UV := a.TermAs[Set[Nat]]("U ∪ {v}")
			one := a.TermAs[IntegerPolynomial]("polynomial_algebra_one(int_ring)")
			oneIn := a.Have(
				"one is a polynomial in U and v",
				"polynomial_algebra_one(int_ring) ∈ polynomial_algebra(int_ring, U ∪ {v})",
				By(comm_ring.SubringOne, polynomial_formula.ParameterPolynomialsSubring.At(UV)))
			noIndex := a.Have(
				"the equations below index zero, of which there are none, are polynomials in U and v",
				"∀j:num. j < 0 ⇒ polynomial_algebra_one(int_ring) ∈ polynomial_algebra(int_ring, U ∪ {v})",
				By(oneIn))
			E, decided := a.UnpackAs[List[IntegerPolynomial]](
				GroupPremises(
					over,
					noIndex,
					oneIn,
					At(
						decide,
						U,
						v,
						P,
						a.TermAs[Nat]("0"),
						a.TermAs[Fun[Nat, IntegerPolynomial]]("λj:num. polynomial_algebra_one(int_ring)"),
						one)),
				"E")
			listed := a.Conjuncts(
				decided,
				"E lists parameter polynomials",
				"and decides every pattern of P along v, with no equation and the inequation one")
			_, chosen := a.ObtainAs[Fun[List[Bool], Set[List[Bool]]]](
				"choose a decision set D(t) for each pattern t",
				"∃D:(list(bool) → set(list(bool))). ∀t:list(bool). ∀F:field_ops(A). ∀ρ:(num → A). "+
					"    algebraically_closed_field_on(F) ∧ fo_env_ok(F.carrier, U, ρ) ⇒ "+
					"    («realized»(0, "+
					"            λj:num. polynomial_algebra_one(int_ring), "+
					"            polynomial_algebra_one(int_ring), "+
					"            P, "+
					"            t, "+
					"            F, "+
					"            ρ) ⇔ "+
					"        polynomial_zero_pattern(F, ρ, E) ∈ D(t))",
				By(a.Unfolded(listed[1], zeroPatternDecidesDef)))
			bounded := a.Have(
				"each set of patterns of the length of P admitted at s "+
					"is a set of boolean lists of that length, finitely many",
				"∀s:list(bool). "+
					"    finite({t:list(bool) | list_length(t) = list_length(P) ∧ s ∈ D(t)}) ∧ "+
					"    (∀t:list(bool). "+
					"        t ∈ {t:list(bool) | list_length(t) = list_length(P) ∧ s ∈ D(t)} ⇒ "+
					"        list_length(t) = list_length(P))",
				Derive(func(b *Argument) {
					b.FixAs[List[Bool]]("s")
					within := b.Have(
						"the patterns admitted at s lie among the boolean lists of the length of P",
						"{t:list(bool) | list_length(t) = list_length(P) ∧ s ∈ D(t)} ⊆ "+
							"{t:list(bool) | list_length(t) = list_length(P)}",
						BySets())
					b.Show(
						"a part of a finite set is finite, and its members have the length of P",
						SplitConj(
							Case(
								"the boolean lists of the length of P are finitely many",
								By(
									within,
									list.BoolListsOfLengthFinite.At(b.TermAs[Nat]("list_length(P)")),
									finite_set.FiniteSubset)),
							Case(
								"and each admitted pattern has that length",
								BySets())))
				}))
			realized := a.Have(
				"at an algebraically closed field the patterns P takes along v "+
					"are those of its length whose decision set holds the pattern of E",
				Statement{
					Binders: "∀F:field_ops(A). ∀ρ:(num → A).",
					Hypotheses: []string{
						"algebraically_closed_field_on(F)",
						"fo_env_ok(F.carrier, U, ρ)",
					},
					Conclusion: "{polynomial_zero_pattern(F, fo_update(ρ, v, x), P) | x:A | x ∈ F.carrier} = " +
						"{t:list(bool) | list_length(t) = list_length(P) ∧ polynomial_zero_pattern(F, ρ, E) ∈ D(t)}",
				},
				Derive(func(b *Argument) {
					F := b.FixAs[FieldOps[A]]("F")
					ρ := b.FixAs[Fun[Nat, A]]("ρ")
					model := b.Conjuncts(
						b.Assume(),
						"F is an algebraically closed field",
						"ρ assigns elements of F to U")
					nonzero := b.Have(
						"one vanishes nowhere along v",
						"∀x:A. x ∈ F.carrier ⇒ ¬ring_formula_atom(F, polynomial_algebra_one(int_ring), fo_update(ρ, v, x))",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							updated := c.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")
							legal := c.Have(
								"ρ updated at v by x is legal on U and v",
								"fo_env_ok(F.carrier, U ∪ {v}, fo_update(ρ, v, x))",
								BySets(
									model[1],
									xIn,
									first_order.EnvOKUpdate.At(c.TermAs[Set[A]]("F.carrier"), UV, ρ, v, x),
									first_order.EnvOKSubset.At(
										c.TermAs[Set[A]]("F.carrier"), c.TermAs[Set[Nat]]("(U ∪ {v}) ∖ {v}"), U, ρ)))
							opened := c.Conjuncts(
								GroupPremises(model[0], legal, ModelSpecialization.At(UV, F, updated)),
								"F is a field",
								"specialization there is a ring homomorphism on the polynomials in U and v",
								"that keeps zero")
							c.Show(
								"specialization sends one to one, which is not zero in a field",
								By(
									ring_homomorphism.MapOne.Read(opened[1]),
									field.OneNotZeroOn.Read(opened[0]),
									ring_formula.RingFormulaAtomDef.At(F, one, updated)))
						}))
					lengths := b.Have(
						"every zero pattern of P has the length of P",
						"∀σ:(num → A). list_length(polynomial_zero_pattern(F, σ, P)) = list_length(P)",
						Derive(func(c *Argument) {
							σ := c.FixAs[Fun[Nat, A]]("σ")
							c.Show(
								"a pattern maps the atom test along P",
								By(
									Normalized,
									zeroPatternDef.At(F, σ, P),
									list.LengthMap.At(
										c.TermAs[Fun[IntegerPolynomial, Bool]]("λp:((num → num) → int). ring_formula_atom(F, p, σ)"), P)))
						}))
					members := b.Have(
						"a list is a pattern of P along v exactly when it has the "+
							"length of P and its decision set holds the pattern of E",
						"∀t:list(bool). "+
							"    (∃x:A. x ∈ F.carrier ∧ t = polynomial_zero_pattern(F, fo_update(ρ, v, x), P)) ⇔ "+
							"    list_length(t) = list_length(P) ∧ polynomial_zero_pattern(F, ρ, E) ∈ D(t)",
						Derive(func(c *Argument) {
							t := c.FixAs[List[Bool]]("t")
							c.Iff()
							c.Forward(
								"a pattern realized at x has the length of P and is decided by its own decision set",
								func(e *Argument, realized Fact) {
									x, at := e.UnpackAs[A](realized, "x")
									e.Show(
										"x solves the system of no equation and the inequation one",
										By(
											at,
											nonzero.At(x),
											lengths.At(e.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)")),
											chosen.At(t, F, ρ),
											model[0],
											model[1],
											nat_order.LessThanZeroClause))
								})
							c.Backward(
								"a pattern whose decision set holds the pattern of E is realized at some x",
								func(e *Argument, member Fact) {
									e.Show(
										"the decision set gives a solution of the system, at which the pattern is t",
										By(member, chosen.At(t, F, ρ), model[0], model[1]))
								})
						}))
					b.Show(
						"so the two sets have the same members",
						BySets(members))
				}))
			a.Take(E)
			a.Take(a.TermAs[Fun[List[Bool], Set[List[Bool]]]](
				"λs:list(bool). {t:list(bool) | list_length(t) = list_length(P) ∧ s ∈ D(t)}"))
			a.Show(
				"so E and the rule B admitting at s the patterns of the length of "+
					"P whose decision set holds s are the lists the theorem asks for",
				By(listed[0], bounded, realized))
		})
	}),
})}
