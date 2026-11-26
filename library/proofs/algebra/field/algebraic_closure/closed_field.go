// closed_field.go — an algebraically closed field as a structure, its
// elements algebraic over a subfield closed in their turn, and one variable
// over such a field: roots avoiding a polynomial, nonzero values, and the
// pseudo-remainder deciding a system under every homomorphism into one.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// AlgebraicallyClosedFieldOn — `algebraically_closed_field_on(F)`: a field
// on F.carrier in which every polynomial of positive degree over the carrier
// has a root there. The first conjunct supplies the field laws through
// FieldOn; the second is the root axiom, PositiveDegreeRoot.
var AlgebraicallyClosedFieldOn = algebraicallyClosedFieldOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "AlgebraicallyClosedFieldOn",
	Key:     "prop_1d5aba427f4fc07f",
	Const:   "algebraically_closed_field_on",
	Subject: "F",
	Type:    "field_ops(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    algebraically_closed_field_on(F) ⇔ " +
			"    field_on(F) ∧ " +
			"    (∀p:(num → A). " +
			"        polynomial_over(F.zero, F.carrier, p) ∧ 0 < polynomial_degree(F.zero, p) ⇒ " +
			"        ∃x:A. x ∈ F.carrier ∧ polynomial_eval(F.add, F.zero, F.mul, F.one, p, x) = F.zero)",
	},
})}

// FieldOn — an algebraically closed field is a field: the projection at
// which the field chapter's carrier laws apply.
var FieldOn = fieldOnThm{family.Add(registry.ProofEntry{
	Name:  "FieldOn",
	Key:   "prop_d85f67d29015bf94",
	Build: AlgebraicallyClosedFieldOn.Axiom("field_on(F)"),
})}

// PositiveDegreeRoot — a polynomial of positive degree over the carrier has
// a root in it.
var PositiveDegreeRoot = positiveDegreeRootThm{family.Add(registry.ProofEntry{
	Name: "PositiveDegreeRoot",
	Key:  "prop_549f31d5841f6d10",
	Build: AlgebraicallyClosedFieldOn.Axiom(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"0 < polynomial_degree(p)",
		},
		Conclusion: "∃x:A. x ∈ F.carrier ∧ polynomial_eval(p, x) = F.zero",
	}),
})}

// AlgebraicallyClosedFieldOnIff — an algebraically closed field on its
// carrier is a field that is algebraically closed in the sense of
// algebraically_closed_field: the root axiom is that predicate's definition.
var AlgebraicallyClosedFieldOnIff = algebraicallyClosedFieldOnIffThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicallyClosedFieldOnIff",
	Key:  "prop_f570c2a9929322e9",
	Build: family.Theorem("∀F:field_ops(A). "+
		"    algebraically_closed_field_on(F) ⇔ field_on(F) ∧ algebraically_closed_field(F)",
		func(a *Argument, F *Expr[FieldOps[A]]) {
			a.Show(
				"the root axiom is the definition of algebraically_closed_field",
				Unfold(AlgebraicallyClosedFieldOn),
				Unfold(AlgebraicallyClosedDef))
		}),
})}

// AlgebraicElementsClosed — the elements of an algebraically closed field M algebraic
// over a subfield k are closed in their turn. A polynomial of positive degree over them
// has a root in M, and that root, algebraic over algebraic elements, is algebraic over k.
var AlgebraicElementsClosed = algebraicElementsClosedThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicElementsClosed",
	Key:  "prop_b6c3acc467ba8fb8",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"polynomial_over(algebraic_elements(M, k), p)",
			"0 < polynomial_degree(p)",
		},
		Conclusion: "∃x:A. x ∈ algebraic_elements(M, k) ∧ polynomial_eval(p, x) = M.zero",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		p *Arrow[Nat, A],
		closed, subk, over, positive Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		closure, carrier := a.TermAs[Set[A]]("algebraic_elements(M, k)"), a.TermAs[Set[A]]("M.carrier")
		elements := algebraic_element.AlgebraicElementsDef.At(fieldM, k)
		inField := a.Have(
			"the algebraic elements lie in M, each algebraic over k",
			"algebraic_elements(M, k) ⊆ M.carrier ∧ "+
				"(∀y:A. y ∈ algebraic_elements(M, k) ⇒ algebraic_over(M, k, y))",
			BySets(elements))
		overField := a.Have(
			"p is a polynomial over M",
			"polynomial_over(M.carrier, p)",
			By(over, inField, polynomial.PolynomialOverMono.At(zero, closure, carrier, p)))
		nonzero := a.Have(
			"p is not zero, its degree being positive",
			"p ≠ vec_zero",
			By(
				Normalized,
				positive,
				polynomial.DegreeVecZero.At(zero),
				nat_order.LessThanIrrefl.At(a.TermAs[Nat]("0"))))
		x, root := a.ObtainAs[A](
			"p has a root x in M",
			"∃x:A. x ∈ M.carrier ∧ polynomial_eval(p, x) = M.zero",
			By(closed, overField, positive, AlgebraicallyClosedDef.At(fieldM)))
		parts := a.Conjuncts(
			root,
			"x lies in M",
			"p vanishes at x")
		overElements := a.Have(
			"x is algebraic over the algebraic elements",
			"algebraic_over(M, algebraic_elements(M, k), x)",
			By(over, nonzero, parts[1], algebraic_element.AlgebraicOverDef.At(fieldM, closure, x)))
		a.Take(x)
		a.Show(
			"so x is algebraic over k",
			BySets(
				elements,
				parts[0],
				parts[1],
				a.Have(
					"a tower of algebraic extensions is algebraic",
					"algebraic_over(M, k, x)",
					By(
						M,
						subk,
						inField,
						parts[0],
						overElements,
						algebraic_element.AlgebraicOverTrans.Read(M).AsFact().At(k, closure, x)))))
	}),
})}

// RootsDivideDegreePower — the Nullstellensatz in one variable: over an
// algebraically closed field, a nonzero polynomial whose roots are all roots
// of q divides q to the power of its degree. By induction on the degree, a
// nonzero constant divides one, and a polynomial of positive degree has a
// root a and splits as (x − a)·s₁ with s₁ one degree lower; x − a divides q,
// so the one more factor of q pays for the one more linear factor.
var RootsDivideDegreePower = rootsDivideDegreePowerThm{family.Add(registry.ProofEntry{
	Name: "RootsDivideDegreePower",
	Key:  "prop_33ff2caa92e03602",
	Build: AlgebraicallyClosedFieldOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_over(F.carrier, q)",
			"p ≠ vec_zero",
			"polynomial_roots(F.carrier, p) ⊆ polynomial_roots(F.carrier, q)",
		},
		Conclusion: "polynomial_divides(field_ring(F), p, polynomial_pow(q, polynomial_degree(p)))",
	}, func(
		a *Argument,
		closed AlgebraicallyClosedFieldFact[on.F],
		p, q *Arrow[Nat, A],
		pOver, qOver, nonzero, roots Fact,
	) {
		fieldOn := FieldOn.Read(closed)
		ring := field.RingOn.Read(fieldOn)
		a.Show(
			"induct on the degree, for every polynomial over F whose roots are roots of q",
			ByInduction(
				peano.Induction.At(
					a.TermAs[Set[Nat]](
						"λn:num. ∀s:(num → A). "+
							"    polynomial_over(F.carrier, s) ∧ "+
							"    s ≠ vec_zero ∧ "+
							"    polynomial_degree(s) = n ∧ "+
							"    polynomial_roots(F.carrier, s) ⊆ polynomial_roots(F.carrier, q) ⇒ "+
							"    polynomial_divides(field_ring(F), s, polynomial_pow(q, n))"),
					a.TermAs[Nat]("polynomial_degree(p)")),
				pOver, nonzero, roots,
				Case(
					"a nonzero constant divides one, the zeroth power of q",
					Derive(func(b *Argument) {
						s := b.FixAs[Fun[Nat, A]]("s")
						given := b.Conjuncts(
							b.Assume(),
							"s is a polynomial over F",
							"s is not zero",
							"s has degree zero",
							"every root of s is a root of q")
						inverseIn := b.Have(
							"the inverse of the constant coefficient of s lies in F",
							"F.inv(s(0)) ∈ F.carrier",
							By(field.InvIn.Read(fieldOn), given[0], polynomial.PolynomialOverDef))
						unit := b.Have(
							"scaled by that inverse, s is monic of degree zero, the one polynomial",
							"F.inv(s(0)) • s = basis_vector(0)",
							By(
								Read(polynomial.MonicMultiple, fieldOn).At(s),
								polynomial.MonicDegreeZero.Read(ring).At(b.TermAs[Fun[Nat, A]]("F.inv(s(0)) • s")),
								given[0],
								given[1],
								given[2]))
						inverse := b.MemberOf[on.F](b.TermAs[A]("F.inv(s(0))"), inverseIn)
						b.Show(
							"so s times the constant F.inv(s(0)) is the one polynomial, the zeroth power of q",
							Unfold(polynomial_division.PolynomialDividesDef),
							Witness(b.TermAs[Fun[Nat, A]]("F.inv(s(0)) • basis_vector(0)")),
							By(
								polynomial.PolynomialPowZero.Read(ring).At(q),
								polynomial.PolynomialMulConstant.Read(ring).At(inverse, s),
								module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
								polynomial.BasisVectorOver.Read(ring).At(b.TermAs[Nat]("0")),
								unit,
								given[0]))
					})),
				Case(
					"a root a of s splits off x − a, which divides q, "+
						"and the cofactor divides the power of q one lower",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						ih := b.Assume()
						s := b.FixAs[Fun[Nat, A]]("s")
						given := b.Conjuncts(
							b.Assume(),
							"s is a polynomial over F",
							"s is not zero",
							"s has degree n + 1",
							"every root of s is a root of q")
						positive := b.Have(
							"s has positive degree",
							"0 < polynomial_degree(s)",
							ByArith(given[2]))
						root, rooted := b.ObtainAs[A](
							"F is algebraically closed, so s has a root a in F",
							"∃a:A. a ∈ F.carrier ∧ polynomial_eval(s, a) = F.zero",
							By(PositiveDegreeRoot.Read(closed).At(s), given[0], positive))
						rootFacts := b.Conjuncts(
							rooted,
							"a lies in F",
							"s vanishes at a")
						am := b.MemberOf[on.F](root, rootFacts[0])
						_, split := b.ObtainAs[Fun[Nat, A]](
							"s is x − a times a nonzero s₁ one degree lower, whose roots with a are those of s",
							"∃s₁:(num → A). "+
								"    polynomial_over(F.carrier, s₁) ∧ "+
								"    s₁ ≠ vec_zero ∧ "+
								"    s = polynomial_mul(«linear»(a), s₁) ∧ "+
								"    polynomial_degree(s) = suc(polynomial_degree(s₁)) ∧ "+
								"    polynomial_roots(F.carrier, s) = insert(a, polynomial_roots(F.carrier, s₁))",
							By(
								polynomial_roots.RootFactorization.Read(integral_domain.FieldIntegralDomain.Read(fieldOn)).At(
									s, am),
								given[0],
								given[1],
								rootFacts[1]))
						cofactor := b.Conjuncts(
							split,
							"s₁ is a polynomial over F",
							"s₁ is not zero",
							"s is (x − a)·s₁",
							"the degree of s is one more than that of s₁",
							"the roots of s are a and the roots of s₁")
						degree := b.Have(
							"s₁ has degree n",
							"polynomial_degree(s₁) = n",
							ByArith(given[2], cofactor[3]))
						inherited := b.Conjuncts(
							b.Have(
								"a and every root of s₁ are roots of s, so roots of q",
								"a ∈ polynomial_roots(F.carrier, q) ∧ "+
									"polynomial_roots(F.carrier, s₁) ⊆ polynomial_roots(F.carrier, q)",
								By(cofactor[4], given[3], set_order.InsertSubset)),
							"a is a root of q",
							"every root of s₁ is a root of q")
						lower := b.Have(
							"by induction, s₁ divides q to the power n",
							"polynomial_divides(field_ring(F), s₁, polynomial_pow(q, n))",
							By(ih, cofactor[0], cofactor[1], degree, inherited[1]))
						vanishes := b.Have(
							"q vanishes at a",
							"polynomial_eval(q, a) = F.zero",
							BySets(inherited[0], polynomial_roots.PolynomialRootsDef))
						linear := b.Have(
							"so x − a divides q, by the factor theorem",
							"polynomial_divides(field_ring(F), «linear»(a), q)",
							By(polynomial_roots.FactorTheorem.Read(ring).At(q, am), qOver, vanishes))
						u, qSplit := b.UnpackAs[Fun[Nat, A]](
							b.Unfolded(linear, polynomial_division.PolynomialDividesDef), "u")
						v, powerSplit := b.UnpackAs[Fun[Nat, A]](
							b.Unfolded(lower, polynomial_division.PolynomialDividesDef), "v")
						quotientU := b.Conjuncts(
							qSplit,
							"u is a polynomial over F",
							"q is (x − a)·u")
						quotientV := b.Conjuncts(
							powerSplit,
							"v is a polynomial over F",
							"q to the power n is s₁·v")
						members := b.Have(
							"x, the constant a, u, s₁ and v lie in the ring of polynomials over F",
							"basis_vector(1) ∈ «fieldPolynomials» ∧ "+
								"a • basis_vector(0) ∈ «fieldPolynomials» ∧ "+
								"u ∈ «fieldPolynomials» ∧ "+
								"s₁ ∈ «fieldPolynomials» ∧ "+
								"v ∈ «fieldPolynomials»",
							By(
								rootFacts[0],
								quotientU[0],
								cofactor[0],
								quotientV[0],
								polynomial.BasisVectorOver.Read(ring),
								module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))))
						power := b.Have(
							"q to the power n + 1 is s times u·v",
							"polynomial_pow(q, suc(n)) = polynomial_mul(s, polynomial_mul(u, v))",
							CalcEq(
								Leg(
									b.TermAs[Fun[Nat, A]]("polynomial_mul(q, polynomial_pow(q, n))"),
									"one more factor of q",
									By(polynomial.PolynomialPowSuc.Read(ring).At(n, q))),
								Leg(
									b.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_mul(«linear»(a), u), polynomial_mul(s₁, v))"),
									"q is (x − a)·u and q to the power n is s₁·v",
									By(Normalized, quotientV[1], quotientU[1])),
								Leg(
									b.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_mul(«linear»(a), s₁), polynomial_mul(u, v))"),
									"the four factors regroup in the ring of polynomials over F",
									ByArith(polynomial.PolynomialRingOn.Read(ring), members)),
								FinalLeg(
									"and (x − a)·s₁ is s",
									By(Normalized, cofactor[2]))))
						b.Show(
							"so s divides q to the power n + 1, with quotient u·v",
							Unfold(polynomial_division.PolynomialDividesDef),
							Witness(b.TermAs[Fun[Nat, A]]("polynomial_mul(u, v)")),
							By(power, polynomial.PolynomialMulOver.Read(ring).At(u, v), quotientU[0], quotientV[0]))
					}))))
	}),
})}

// RootAvoidance — a root of p avoiding q exists exactly when p does not
// divide q to the degree of p: at such a root x the power of q would vanish
// with p, forcing q(x) = 0; without one every root of p is a root of q, and
// RootsDivideDegreePower gives the divisibility.
var RootAvoidance = rootAvoidanceThm{family.Add(registry.ProofEntry{
	Name: "RootAvoidance",
	Key:  "prop_910f44094b9bdf33",
	Reading: "Positive degree excludes the zero polynomial. If q is " +
		"zero, both sides are false because every polynomial divides zero.",
	Build: AlgebraicallyClosedFieldOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_over(F.carrier, q)",
			"0 < polynomial_degree(p)",
		},
		Conclusion: "(∃x:A. " +
			"    x ∈ F.carrier ∧ polynomial_eval(p, x) = F.zero ∧ polynomial_eval(q, x) ≠ F.zero) ⇔ " +
			"¬polynomial_divides(field_ring(F), p, polynomial_pow(q, polynomial_degree(p)))",
	}, func(
		a *Argument,
		closed AlgebraicallyClosedFieldFact[on.F],
		p, q *Arrow[Nat, A],
		pOver, qOver, positive Fact,
	) {
		degree := a.TermAs[Nat]("polynomial_degree(p)")
		a.Iff()
		a.Forward(
			"a root of p where q does not vanish rules out the divisibility",
			func(b *Argument, avoiding Fact) {
				x, point := b.UnpackAs[A](avoiding, "x")
				at := b.Conjuncts(
					point,
					"x lies in F",
					"p vanishes at x",
					"q does not vanish at x")
				fieldOn := FieldOn.Read(closed)
				ring := field.RingOn.Read(fieldOn)
				xm := b.MemberOf[on.F](x, at[0])
				divides := b.SupposeNot()
				r, quotient := b.ObtainAs[Fun[Nat, A]](
					"suppose p divides q to the degree of p, with quotient r",
					"∃r:(num → A). "+
						"    polynomial_over(F.carrier, r) ∧ "+
						"    polynomial_pow(q, polynomial_degree(p)) = polynomial_mul(p, r)",
					By(b.Unfolded(divides, polynomial_division.PolynomialDividesDef)))
				quotientR := b.Conjuncts(
					quotient,
					"r is a polynomial over F",
					"q to the degree of p is p·r")
				vanishing := b.Have(
					"at x the power of q is p·r, which vanishes with p, so q(x) to the degree of p is zero",
					"monoid_pow(F.mul, F.one, polynomial_eval(q, x), polynomial_degree(p)) = F.zero",
					By(
						polynomial_evaluation.EvalPow.Read(ring).At(degree, q, xm),
						polynomial_evaluation.EvalMulRoot.Read(ring).At(p, r, xm),
						quotientR[1],
						at[1],
						pOver,
						qOver,
						quotientR[0]))
				value := b.MemberOf[on.F](
					b.TermAs[A]("polynomial_eval(q, x)"),
					GroupPremises(qOver, polynomial_evaluation.EvalIn.Read(ring).At(q, xm)))
				b.Show(
					"but only zero has a vanishing power, and q(x) is not zero",
					By(vanishing, at[2], field.PowEqZeroOn.Read(fieldOn).At(value, degree)))
			})
		a.Backward(
			"if no root of p avoids q, then p divides q to the degree of p",
			func(b *Argument, notDivides Fact) {
				none := b.SupposeNot()
				inclusion := b.Have(
					"every root of p is then a root of q",
					"polynomial_roots(F.carrier, p) ⊆ polynomial_roots(F.carrier, q)",
					Unfold(polynomial_roots.PolynomialRootsDef),
					BySets(none))
				nonzero := b.Have(
					"p is not zero, its degree being positive",
					"p ≠ vec_zero",
					By(positive, polynomial.DegreeVecZero.At(b.TermAs[A]("F.zero")), nat_order.LessThanIrrefl))
				b.Show(
					"and so p divides q to the degree of p, by RootsDivideDegreePower",
					By(notDivides, RootsDivideDegreePower.Read(closed).At(p, q), pOver, qOver, nonzero, inclusion))
			})
	}),
})}

// NonzeroValue — over an algebraically closed field a polynomial takes a
// nonzero value exactly when it is not the zero polynomial: the zero
// polynomial vanishes everywhere, and for a nonzero p the polynomial
// q = p·x − 1 carries the leading coefficient of p one past its degree,
// so it has positive degree and a root a, where p(a)·a = 1 forces
// p(a) ≠ 0.
var NonzeroValue = nonzeroValueThm{family.Add(registry.ProofEntry{
	Name: "NonzeroValue",
	Key:  "prop_b801309dc9948198",
	Build: AlgebraicallyClosedFieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
		},
		Conclusion: "(∃x:A. x ∈ F.carrier ∧ polynomial_eval(p, x) ≠ F.zero) ⇔ p ≠ vec_zero",
	}, func(a *Argument, closed AlgebraicallyClosedFieldFact[on.F], p *Arrow[Nat, A], pOver Fact) {
		fieldOn := FieldOn.Read(closed)
		ring := field.RingOn.Read(fieldOn)
		a.Iff()
		a.Forward(
			"the zero polynomial vanishes at every point of F",
			func(b *Argument, somewhere Fact) {
				b.Show(
					"so a polynomial with a nonzero value is not zero",
					By(Normalized, somewhere, polynomial_evaluation.EvalVecZero.Read(ring)))
			})
		a.Backward(
			"a nonzero p does not vanish at a root of p·x − 1",
			func(b *Argument, nonzero Fact) {
				q, qDef := b.LetAs[Fun[Nat, A]]("q", "polynomial_mul(p, basis_vector(1)) - basis_vector(0)")
				variable := b.TermAs[Fun[Nat, A]]("basis_vector(1)")
				unit := b.TermAs[Fun[Nat, A]]("basis_vector(0)")
				qOver := b.Have(
					"q is a polynomial over F",
					"polynomial_over(F.carrier, q)",
					By(
						qDef,
						pOver,
						comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring)),
						polynomial.PolynomialMulOver.Read(ring).At(p, variable),
						polynomial.BasisVectorOver.Read(ring)))
				coefficients := b.Have(
					"every coefficient of p lies in F",
					"∀i:num. p(i) ∈ F.carrier",
					By(pOver, polynomial.PolynomialOverDef))
				degree := b.TermAs[Nat]("polynomial_degree(p)")
				top := b.Have(
					"one past the degree of p, the coefficient of q is the leading coefficient of p",
					"q(suc(polynomial_degree(p))) = p(polynomial_degree(p))",
					qDef.Rw(),
					Simp(Fwd(vec_space.VecSubDef), Fwd(polynomial.PolynomialMulBasisVector.Read(ring))),
					ByArith(ring, coefficients.At(degree), vec_space.BasisVectorDef))
				zero := b.TermAs[A]("F.zero")
				carrier := b.TermAs[Set[A]]("F.carrier")
				positive := b.Have(
					"that coefficient is not zero, so q does not vanish from index one on: its degree is positive",
					"0 < polynomial_degree(q)",
					ByArith(
						top,
						nonzero,
						pOver,
						qOver,
						polynomial.DegreeVec.At(zero, carrier, q),
						polynomial.DegreeLeading.At(zero, carrier, p),
						At(vec_space.VecDef, zero, b.TermAs[Nat]("suc(polynomial_degree(q))"), q)))
				root, rooted := b.ObtainAs[A](
					"F is algebraically closed, so q has a root a in F",
					"∃a:A. a ∈ F.carrier ∧ polynomial_eval(q, a) = F.zero",
					By(PositiveDegreeRoot.Read(closed).At(q), qOver, positive))
				atRoot := b.Conjuncts(
					rooted,
					"a lies in F",
					"q vanishes at a")
				am := b.MemberOf[on.F](root, atRoot[0])
				value := b.MemberOf[on.F](
					b.TermAs[A]("polynomial_eval(p, a)"),
					GroupPremises(pOver, polynomial_evaluation.EvalIn.Read(ring).At(p, am)))
				evaluated := b.Have(
					"evaluation at a is a ring homomorphism sending x to a, so q takes the value p(a)·a − 1 there",
					"polynomial_eval(q, a) = polynomial_eval(p, a) * a - F.one",
					ByArith(
						ring,
						qDef,
						pOver,
						value,
						polynomial_evaluation.EvalSub.Read(ring).At(
							b.TermAs[Fun[Nat, A]]("polynomial_mul(p, basis_vector(1))"), unit, am),
						polynomial_evaluation.EvalMul.Read(ring).At(p, variable, am),
						polynomial_evaluation.EvalBasisVector.Read(ring).At(b.TermAs[Nat]("0"), am),
						polynomial_evaluation.EvalBasisVector.Read(ring).At(b.TermAs[Nat]("1"), am),
						comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(am),
						polynomial.PolynomialMulOver.Read(ring).At(p, variable),
						polynomial.BasisVectorOver.Read(ring),
						comm_monoid.MonoidPowDef))
				b.Show(
					"so p(a)·a = 1, and p does not vanish at a since one is not zero in F",
					Witness(root),
					ByArith(ring, evaluated, am, atRoot[1], value, field.OneNotZeroOn.Read(fieldOn)))
			})
	}),
})}

// PseudoRemainderDecision — over a commutative ring R, the pseudo-remainder
// r of h^(deg g) by g decides, at every homomorphism σ into an
// algebraically closed field keeping the leading coefficient of g, whether
// σg has a root where σh does not vanish: σ carries the pseudo-division
// cᵏ hⁿ = g·s + r coefficientwise (polynomial_evaluation.CoefficientMapDivision),
// keeps the degree of g, so the image of r stays below it; σc being a unit,
// σg divides (σh)ⁿ exactly when σr is zero
// (polynomial_division.PseudoRemainderDivides), and RootAvoidance turns the
// system into that non-divisibility. A g of degree zero maps to a nonzero
// constant, with no root, and its remainder is zero.
var PseudoRemainderDecision = pseudoRemainderDecisionThm{family.Add(registry.ProofEntry{
	Name: "PseudoRemainderDecision",
	Key:  "prop_80c1073309b5f085",
	Reading: "r is chosen before the field and the homomorphism, from g and h " +
		"alone. The homomorphism is held to keep the leading coefficient of g nonzero; " +
		"where it does not, σg has lower degree and the remainder says nothing.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(B). ∀g h:(num → B).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_over(R.carrier, g)",
			"polynomial_over(R.carrier, h)",
		},
		Conclusion: "∃r:(num → B). " +
			"    polynomial_over(R.carrier, r) ∧ " +
			"    (∀F:field_ops(A). ∀σ:(B → A). " +
			"        algebraically_closed_field_on(F) ∧ " +
			"        ring_homomorphism(R, field_ring(F), σ) ∧ " +
			"        σ(g(polynomial_degree(g))) ≠ F.zero ⇒ " +
			"        ((∃x:A. " +
			"                x ∈ F.carrier ∧ " +
			"                polynomial_eval(λi:num. σ(g(i)), x) = F.zero ∧ " +
			"                polynomial_eval(λi:num. σ(h(i)), x) ≠ F.zero) ⇔ " +
			"            (λi:num. σ(r(i))) ≠ vec_zero(F.zero)))",
		Abbrev: Abbrev{
			{Name: "power", Text: "polynomial_pow(h, polynomial_degree(g))"},
			{Name: "exponent", Text: "suc(polynomial_degree(«power»)) - polynomial_degree(g)"},
		},
	}, func(
		a *Argument,
		_ *Expr[RingOps[B]],
		ring comm_ring.CommRingFact[on.R],
		g, h *Arrow[Nat, B],
		gOver, hOver Fact,
	) {
		degree := a.TermAs[Nat]("polynomial_degree(g)")
		power := a.TermAs[Fun[Nat, B]]("«power»")
		exponent := a.TermAs[Nat]("«exponent»")
		lead := a.TermAs[B]("g(polynomial_degree(g))")
		powerOver := a.Have(
			"the power of h to the degree of g is a polynomial over R",
			"polynomial_over(R.carrier, «power»)",
			By(hOver, polynomial.PolynomialPowOver.Read(ring).At(degree, h)))
		s, r, division := a.Unpack2As[Fun[Nat, B], Fun[Nat, B]](
			GroupPremises(powerOver, gOver, polynomial_division.PseudoDivision.Read(ring).At(power, g)),
			"s", "r")
		parts := a.Conjuncts(
			division,
			"s is a polynomial over R",
			"so is r",
			"r vanishes from the degree of g on",
			"cᵏ hⁿ is g·s + r, c the leading coefficient of g")
		a.Take(r)
		a.Show(
			"r is a polynomial over R whose images decide the system",
			SplitConj(
				Case(
					"r is a polynomial over R",
					By(parts[1])),
				Case(
					"under a homomorphism keeping the leading coefficient of g, "+
						"the system is solvable exactly when the image of r is not zero",
					Derive(func(b *Argument) {
						F := b.FixAs[FieldOps[A]]("F")
						σ := b.FixAs[Fun[B, A]]("σ")
						given := b.Conjuncts(
							b.Assume(),
							"F is an algebraically closed field",
							"σ is a ring homomorphism from R into F",
							"σ keeps the leading coefficient of g nonzero")
						closed, hom, kept := given[0], given[1], given[2]
						fieldOn := FieldOn.Read(closed)
						fieldRing := field.RingOn.Read(fieldOn)
						mapped := polynomial_evaluation.CoefficientMapHomomorphism.Read(hom)
						imageG := b.TermAs[Fun[Nat, A]]("λi:num. σ(g(i))")
						imageH := b.TermAs[Fun[Nat, A]]("λi:num. σ(h(i))")
						imageS := b.TermAs[Fun[Nat, A]]("λi:num. σ(s(i))")
						imageR := b.TermAs[Fun[Nat, A]]("λi:num. σ(r(i))")
						powers := b.Have(
							"applied coefficientwise, σ carries the power of h to the power of its image",
							"(λi:num. σ(«power»(i))) = polynomial_pow(λi:num. σ(h(i)), polynomial_degree(g))",
							Simp(Fwd(polynomial.PolynomialPowDef)),
							By(hOver, ring_homomorphism.RingMapPower.Read(mapped).AsFact().At(degree, h)))
						identity := b.Have(
							"so σ carries the pseudo-division coefficientwise, σ(cᵏ) being σcᵏ",
							"vec_scalar_mul(monoid_pow(F.mul, F.one, σ(g(polynomial_degree(g))), «exponent»), "+
								"    polynomial_pow(λi:num. σ(h(i)), polynomial_degree(g))) = "+
								"vec_add(polynomial_mul(λi:num. σ(g(i)), λi:num. σ(s(i))), λi:num. σ(r(i)))",
							By(
								powers,
								powerOver,
								gOver,
								parts[0],
								parts[1],
								parts[3],
								polynomial.PolynomialOverDef,
								comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(lead, exponent),
								polynomial_evaluation.CoefficientMapDivision.Read(hom).AsFact().At(
									b.TermAs[B]("monoid_pow(R.mul, R.one, g(polynomial_degree(g)), «exponent»)"), power, g, s, r),
								ring_homomorphism.RingMapPower.Read(hom).AsFact().At(exponent, lead)))
						images := b.Have(
							"the images of g, h, s and r are polynomials over F",
							"polynomial_over(F.carrier, λi:num. σ(g(i))) ∧ "+
								"polynomial_over(F.carrier, λi:num. σ(h(i))) ∧ "+
								"polynomial_over(F.carrier, λi:num. σ(s(i))) ∧ "+
								"polynomial_over(F.carrier, λi:num. σ(r(i)))",
							By(
								gOver,
								hOver,
								parts[0],
								parts[1],
								polynomial.PolynomialOverMap,
								ring_homomorphism.MapZero.Read(hom),
								ring_homomorphism.MapIn.Read(hom)))
						zeroF := b.TermAs[A]("F.zero")
						zeroR := b.TermAs[B]("R.zero")
						keeps := b.Have(
							"σ keeps the degree of g, keeping its leading coefficient",
							"polynomial_degree(λi:num. σ(g(i))) = polynomial_degree(g)",
							By(
								kept,
								images,
								gOver,
								polynomial.DegreeExact.At(zeroF, b.TermAs[Set[A]]("F.carrier"), imageG, degree),
								polynomial.DegreeVec.At(zeroR, b.TermAs[Set[B]]("R.carrier"), g),
								At(polynomial.VecMap, σ, zeroR, zeroF, b.TermAs[Nat]("suc(polynomial_degree(g))"), g),
								ring_homomorphism.MapZero.Read(hom)))
						imageVanishes := b.Have(
							"so the image of r vanishes from the degree of the image of g on",
							"vec⟨polynomial_degree(λi:num. σ(g(i)))⟩(λi:num. σ(r(i)))",
							By(
								Normalized,
								keeps,
								parts[2],
								At(polynomial.VecMap, σ, zeroR, zeroF, degree, r),
								ring_homomorphism.MapZero.Read(hom)))
						divisibility := b.Have(
							"σc being a unit, the image of g divides the power "+
								"of the image of h exactly when the image of r is zero",
							"polynomial_divides(field_ring(F), "+
								"    λi:num. σ(g(i)), "+
								"    polynomial_pow(λi:num. σ(h(i)), polynomial_degree(g))) ⇔ "+
								"(λi:num. σ(r(i))) = vec_zero(F.zero)",
							By(
								fieldOn,
								kept,
								identity,
								images,
								gOver,
								imageVanishes,
								polynomial_division.PseudoRemainderDivides.At(
									F,
									b.TermAs[A]("σ(g(polynomial_degree(g)))"),
									exponent,
									b.TermAs[Fun[Nat, A]]("polynomial_pow(λi:num. σ(h(i)), polynomial_degree(g))"),
									imageG,
									imageS,
									imageR),
								ring_homomorphism.MapIn.Read(hom).AsFact().At(lead),
								polynomial.PolynomialOverDef,
								polynomial.PolynomialPowOver.Read(fieldRing).At(degree, imageH)))
						b.Cases(b.Term("polynomial_degree(g) = 0"))
						b.When(
							"g of degree zero maps to the nonzero constant σc, which has no root, and r is then zero",
							func(d *Argument, constant Fact) {
								nowhere := d.Have(
									"the image of g is the nonzero constant σc, so it vanishes nowhere",
									"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(λi:num. σ(g(i)), x) ≠ F.zero",
									Derive(func(e *Argument) {
										x := e.FixAs[A]("x")
										xIn := e.Assume()
										e.Show(
											"its value is its constant coefficient",
											By(
												kept,
												keeps,
												constant,
												images,
												xIn,
												polynomial_evaluation.DegreeZeroEval.Read(fieldRing).AsFact().At(imageG, x)))
									}))
								zeroImage := d.Have(
									"r vanishes from the degree of g on, which is zero, so its image is zero",
									"(λi:num. σ(r(i))) = vec_zero(F.zero)",
									By(keeps, constant, imageVanishes, vec_space.VecDimZero.At(zeroF, imageR)))
								d.Show(
									"so neither side holds",
									By(nowhere, zeroImage))
							})
						b.Otherwise(
							"at positive degree root avoidance turns the system into "+
								"non-divisibility, the nonvanishing of the image of r",
							func(d *Argument, nonconstant Fact) {
								positive := d.Have(
									"the image of g has positive degree",
									"0 < polynomial_degree(λi:num. σ(g(i)))",
									ByArith(nonconstant, keeps))
								d.Show(
									"by root avoidance",
									By(positive, divisibility, keeps, images, RootAvoidance.Read(closed).At(imageG, imageH)))
							})
					}))))
	}),
})}
