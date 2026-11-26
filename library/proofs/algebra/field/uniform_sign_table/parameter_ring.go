// parameter_ring.go — uniform sign tables for every finite family over the
// parameter ring, by induction on the degrees.

package uniform_sign_table

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/parametric_sign_table"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// DropZeroSignCoefficients — dropping the coefficients of sign zero. Let a
// condition C fix the sign s(i, n) of every coefficient g(i, n), n ≤ d, of a
// family of parameter polynomials of degree at most d, and let g' be zero at
// the coefficients of sign zero and agree with g elsewhere. The members of
// g' are parameter polynomials of no larger degree. A member of g' other than
// the zero polynomial has a leading coefficient other than zero, which was
// therefore not dropped: it is the coefficient of g there, of a nonzero sign.
// In a model meeting C, g' specializes as g does, so a uniform table of g'
// gives one of g (parametric_sign_table.SignTableByAgreement); and a member
// of g' that does not specialize to zero is not the zero polynomial, so its
// leading coefficient, of a nonzero sign, does not specialize to zero.
var DropZeroSignCoefficients = dropZeroSignCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "DropZeroSignCoefficients",
	Key:  "prop_fe392f35a49a173",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m d:num. " +
			"∀s:(prod(num, num) → int). " +
			"∀g g':(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"∀i:num. i < m ⇒ «overParameters»(g(i))",
			"∀i:num. i < m ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) ≤ d",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i n:num. " +
				"    «model»(U, C, F, lt, ρ) ∧ i < m ∧ n < suc(d) ⇒ " +
				"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, g(i, n))) = s((i, n))",
			"∀i n:num. " +
				"    (n < suc(d) ∧ s((i, n)) = &0 ⇒ g'(i, n) = integer_polynomial_ring.zero) ∧ " +
				"    (¬(n < suc(d) ∧ s((i, n)) = &0) ⇒ g'(i, n) = g(i, n))",
		},
		Conclusion: "(∀i:num. i < m ⇒ «overParameters»(g'(i))) ∧ " +
			"(∀i:num. " +
			"    i < m ⇒ " +
			"    polynomial_degree(integer_polynomial_ring.zero, g'(i)) ≤ " +
			"    polynomial_degree(integer_polynomial_ring.zero, g(i))) ∧ " +
			"(∀i:num. " +
			"    i < m ∧ g'(i) ≠ vec_zero(integer_polynomial_ring.zero) ⇒ " +
			"    g'(i, polynomial_degree(integer_polynomial_ring.zero, g'(i))) = " +
			"    g(i, polynomial_degree(integer_polynomial_ring.zero, g'(i))) ∧ " +
			"    ¬(s((i, polynomial_degree(integer_polynomial_ring.zero, g'(i)))) = &0)) ∧ " +
			"(∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num. " +
			"    «model»(U, C, F, lt, ρ) ∧ " +
			"    i < m ∧ " +
			"    «specialized»(field_ring(F), ρ, g'(i)) ≠ vec_zero(F.zero) ⇒ " +
			"    integer_polynomial_eval(field_ring(F), " +
			"        ρ, " +
			"        g'(i, polynomial_degree(integer_polynomial_ring.zero, g'(i)))) ≠ " +
			"    F.zero) ∧ " +
			"(parametric_sign_table(U, C, m, g') ⇒ parametric_sign_table(U, C, m, g))",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		m, d *Expr[Nat],
		s *Expr[Fun[Prod[Nat, Nat], Int]],
		g, trimmed *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		over, bounded, signFixed, trimmedCases Fact,
	) {
		operations := a.Have(
			"the integer polynomial ring operates as the polynomial algebra over the integers",
			"integer_polynomial_ring.add = fun_add(int_add) ∧ "+
				"integer_polynomial_ring.zero = fun_zero(int_of_num(0)) ∧ "+
				"integer_polynomial_ring.mul = polynomial_algebra_mul(int_ring) ∧ "+
				"integer_polynomial_ring.one = polynomial_algebra_one(int_ring)",
			Cite(polynomial_formula.IntegerPolynomialRingOperations))
		zeroIn := a.Have(
			"the zero polynomial is a parameter polynomial",
			"integer_polynomial_ring.zero ∈ polynomial_algebra(int_ring, U)",
			By(
				operations,
				comm_ring.ZeroIn.Read(a.Have(
					"the parameter polynomials form a commutative ring",
					"comm_ring_on(«parameterRing»(U))",
					Cite(polynomial_formula.ParameterRingCommutative, U)))))
		coefficients := a.Have(
			"every coefficient of a member is a parameter polynomial",
			"∀i n:num. i < m ⇒ g(i, n) ∈ polynomial_algebra(int_ring, U)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				n := b.FixAs[Nat]("n")
				below := b.Assume()
				b.Show(
					"a coefficient of a parameter polynomial",
					By(polynomial.CoefficientIn.Read(b.Simplified(GroupPremises(below, over.At(i)))).At(n)))
			}))
		trimmedOver := a.Have(
			"dropping the coefficients of sign zero leaves parameter polynomials of no larger degree",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < m",
				},
				Conclusion: "«overParameters»(g'(i)) ∧ " +
					"polynomial_degree(integer_polynomial_ring.zero, g'(i)) ≤ " +
					"polynomial_degree(integer_polynomial_ring.zero, g(i))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				below := b.Assume()
				vanishes := b.Have(
					"g(i) vanishes past its degree",
					"vec⟨suc(polynomial_degree(integer_polynomial_ring.zero, g(i)))⟩(integer_polynomial_ring.zero, "+
						"    g(i))",
					By(below, over, polynomial.DegreeVec))
				trimmedVanishes := b.Have(
					"so does g'(i)",
					"vec⟨suc(polynomial_degree(integer_polynomial_ring.zero, g(i)))⟩(integer_polynomial_ring.zero, "+
						"    g'(i))",
					By(operations, vanishes, trimmedCases, vec_space.VecDef))
				trimmedCoefficients := b.Have(
					"each coefficient of g'(i) is zero or one of g(i)",
					"∀n:num. g'(i, n) ∈ polynomial_algebra(int_ring, U)",
					Derive(func(e *Argument) {
						e.FixAs[Nat]("n")
						e.Cases(e.Term("n < suc(d) ∧ s((i, n)) = &0"))
						e.When(
							"a dropped coefficient is the zero polynomial",
							func(k *Argument, dropped Fact) {
								k.Show(
									"the zero polynomial is a parameter polynomial",
									By(operations, trimmedCases.At(k.TermAs[Nat]("i"), k.TermAs[Nat]("n")), dropped, zeroIn))
							})
						e.Otherwise(
							"a kept coefficient is one of g(i)",
							func(k *Argument, kept Fact) {
								k.Show(
									"a coefficient of a member",
									By(
										trimmedCases.At(k.TermAs[Nat]("i"), k.TermAs[Nat]("n")),
										kept,
										GroupPremises(below, coefficients.At(k.TermAs[Nat]("i"), k.TermAs[Nat]("n")))))
							})
					}))
				b.Show(
					"g'(i) is a parameter polynomial vanishing past the degree of g(i)",
					By(
						operations,
						trimmedVanishes,
						trimmedCoefficients,
						polynomial.PolynomialOverDef.At(
							b.TermAs[IntegerPolynomial]("integer_polynomial_ring.zero"),
							b.TermAs[Set[IntegerPolynomial]]("polynomial_algebra(int_ring, U)"),
							b.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("g'(i)")),
						polynomial.DegreeLeast))
			}))
		withinBound := a.Have(
			"the members of g' have degree at most d",
			"∀i:num. i < m ⇒ polynomial_degree(integer_polynomial_ring.zero, g'(i)) < suc(d)",
			a.ForEach(func(i *Expr[Nat]) Action {
				return ByArith(operations, trimmedOver.At(i), bounded.At(i))
			}))
		leadingNotDropped := a.Have(
			"a member of g' other than the zero polynomial keeps "+
				"the coefficient of g at its degree, of a nonzero sign",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < m",
					"g'(i) ≠ vec_zero(integer_polynomial_ring.zero)",
				},
				Conclusion: "g'(i, polynomial_degree(integer_polynomial_ring.zero, g'(i))) = " +
					"g(i, polynomial_degree(integer_polynomial_ring.zero, g'(i))) ∧ " +
					"¬(s((i, polynomial_degree(integer_polynomial_ring.zero, g'(i)))) = &0)",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				given := b.Conjuncts(
					b.Assume(),
					"i indexes a member",
					"g'(i) is not the zero polynomial")
				leadingCoefficient := b.Have(
					"its leading coefficient is a parameter polynomial other than zero",
					"g'(i, polynomial_degree(integer_polynomial_ring.zero, g'(i))) ≠ integer_polynomial_ring.zero",
					By(
						operations,
						GroupPremises(given[0], trimmedOver.At(i)),
						given[1],
						polynomial.LeadingCoefficientNonzero.At(
							b.TermAs[IntegerPolynomial]("integer_polynomial_ring.zero"),
							b.TermAs[Set[IntegerPolynomial]]("polynomial_algebra(int_ring, U)"),
							b.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("g'(i)"))))
				b.Show(
					"so it was not dropped: it is the coefficient of g(i), and its sign is not zero",
					By(
						operations,
						leadingCoefficient,
						GroupPremises(given[0], withinBound.At(i)),
						trimmedCases.At(i, b.TermAs[Nat]("polynomial_degree(integer_polynomial_ring.zero, g'(i))"))))
			}))
		coefficientValue := a.Have(
			"in a model meeting C, each coefficient of a member specializes into F",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i n:num.",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
					"i < m",
				},
				Conclusion: "integer_polynomial_eval(field_ring(F), ρ, g(i, n)) ∈ F.carrier",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				b.FixAs[Nat]("i")
				b.FixAs[Nat]("n")
				given := b.Assume()
				opened := b.Conjuncts(
					GroupPremises(given, parametric_sign_table.ModelSpecialization.At(U, C, F, lt, ρ)),
					"F is a field",
					"F with lt is an ordered field",
					"ρ gives carrier points to the parameters",
					"specialization at ρ is a ring homomorphism",
					"that keeps zero")
				b.Show(
					"a homomorphism sends a parameter polynomial into F",
					By(
						given,
						coefficients,
						ring_homomorphism.MapIn.Read(opened[3]).AsFact().At(b.TermAs[IntegerPolynomial]("g(i, n)"))))
			}))
		trimmedValues := a.Have(
			"in a model meeting C, each coefficient of g'(i) specializes as that of g(i) does",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i n:num.",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
					"i < m",
				},
				Conclusion: "integer_polynomial_eval(field_ring(F), ρ, g'(i, n)) = " +
					"integer_polynomial_eval(field_ring(F), ρ, g(i, n))",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				i := b.FixAs[Nat]("i")
				n := b.FixAs[Nat]("n")
				given := b.Assume()
				opened := b.Conjuncts(
					GroupPremises(given, parametric_sign_table.ModelSpecialization.At(U, C, F, lt, ρ)),
					"F is a field",
					"F with lt is an ordered field",
					"ρ gives carrier points to the parameters",
					"specialization at ρ is a ring homomorphism",
					"that keeps zero")
				b.Cases(b.Term("n < suc(d) ∧ s((i, n)) = &0"))
				b.When(
					"a coefficient of sign zero is dropped, and specializes to zero",
					func(e *Argument, dropped Fact) {
						parts := e.Conjuncts(
							dropped,
							"n is at most d",
							"s(i, n) is zero")
						e.Show(
							"g(i, n) has sign zero, so it specializes to zero, as the zero polynomial does",
							By(
								trimmedCases.At(i, n),
								dropped,
								operations,
								opened[4],
								parts[1],
								GroupPremises(given, parts[0], signFixed.At(F, lt, ρ, i, n)),
								GroupPremises(given, coefficientValue.At(F, lt, ρ, i, n)),
								ordered_field.SignValues.Read(opened[1]).AsFact().At(
									e.TermAs[A]("integer_polynomial_eval(field_ring(F), ρ, g(i, n))"))))
					})
				b.Otherwise(
					"any other coefficient is kept",
					func(e *Argument, kept Fact) {
						e.Show(
							"g'(i, n) is g(i, n)",
							By(trimmedCases.At(i, n), kept))
					})
			}))
		agreeTrimmed := a.Have(
			"in a model meeting C, g(i) has the signs of g'(i) throughout",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num. ∀x:A.",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
					"i < m",
					"x ∈ F.carrier",
				},
				Conclusion: "ordered_sign(F, lt, «value»(F, ρ, g(i), x)) = " +
					"ordered_sign(F, lt, «value»(F, ρ, g'(i), x))",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				i := b.FixAs[Nat]("i")
				b.FixAs[A]("x")
				given := b.Assume()
				same := b.Have(
					"g'(i) and g(i) specialize to one polynomial",
					"«specialized»(field_ring(F), ρ, g'(i)) = «specialized»(field_ring(F), ρ, g(i))",
					Funext(),
					Derive(func(e *Argument) {
						n := e.FixAs[Nat]("n")
						e.Show(
							"coefficient by coefficient",
							By(GroupPremises(given, trimmedValues.At(F, lt, ρ, i, n))))
					}))
				b.Show(
					"so they take the same values",
					By(same))
			}))
		toTrimmed := a.Have(
			"a uniform table of g' under C gives one of g",
			"parametric_sign_table(U, C, m, g') ⇒ parametric_sign_table(U, C, m, g)",
			Derive(func(b *Argument) {
				table := b.Assume()
				b.Show(
					"g agrees in sign with g', member by member",
					By(
						parametric_sign_table.SignTableByAgreement.At(
							U, C, m, m, trimmed, g, b.TermAs[Fun[Nat, Nat]]("λi:num. i")),
						agreeTrimmed,
						table))
			}))
		leadingStaysNonzero := a.Have(
			"in a model meeting C, a member of g' that does not "+
				"specialize to zero keeps its leading coefficient nonzero",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num.",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
					"i < m",
					"«specialized»(field_ring(F), ρ, g'(i)) ≠ vec_zero(F.zero)",
				},
				Conclusion: "integer_polynomial_eval(field_ring(F), " +
					"    ρ, " +
					"    g'(i, polynomial_degree(integer_polynomial_ring.zero, g'(i)))) ≠ " +
					"F.zero",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				i := b.FixAs[Nat]("i")
				assumed := b.Assume()
				opened := b.Conjuncts(
					GroupPremises(assumed, parametric_sign_table.ModelSpecialization.At(U, C, F, lt, ρ)),
					"F is a field",
					"F with lt is an ordered field",
					"ρ gives carrier points to the parameters",
					"specialization at ρ is a ring homomorphism",
					"that keeps zero")
				degree := b.TermAs[Nat]("polynomial_degree(integer_polynomial_ring.zero, g'(i))")
				formalNonzero := b.Have(
					"g'(i) is not the zero polynomial, which specializes to zero",
					"g'(i) ≠ vec_zero(integer_polynomial_ring.zero)",
					Derive(func(e *Argument) {
						zero := e.SupposeNot()
						specializedZero := e.Have(
							"then g'(i) would specialize to zero",
							"«specialized»(field_ring(F), ρ, g'(i)) = vec_zero(F.zero)",
							Funext(),
							Derive(func(k *Argument) {
								n := k.FixAs[Nat]("n")
								k.Show(
									"each coefficient is the zero polynomial",
									By(
										Normalized,
										zero,
										operations,
										vec_space.VecZeroDef.At(k.TermAs[IntegerPolynomial]("integer_polynomial_ring.zero"), n),
										vec_space.VecZeroDef.At(k.TermAs[A]("F.zero"), n),
										opened[4]))
							}))
						e.Show(
							"against the hypothesis",
							By(specializedZero, assumed))
					}))
				notDropped := b.Conjuncts(
					GroupPremises(assumed, formalNonzero, leadingNotDropped.At(i)),
					"so its leading coefficient is the coefficient of g(i) there",
					"of a nonzero sign")
				fixedSign := b.Have(
					"its degree is one of those at which C fixes the signs",
					"polynomial_degree(integer_polynomial_ring.zero, g'(i)) < suc(d)",
					By(GroupPremises(assumed, withinBound.At(i))))
				b.Show(
					"its sign under C is that nonzero sign, so it does not specialize to zero",
					By(
						operations,
						notDropped[0],
						notDropped[1],
						GroupPremises(assumed, fixedSign, signFixed.At(F, lt, ρ, i, degree)),
						GroupPremises(assumed, coefficientValue.At(F, lt, ρ, i, degree)),
						ordered_field.SignValues.Read(opened[1]).AsFact().At(b.TermAs[A](
							"integer_polynomial_eval(field_ring(F), "+
								"    ρ, "+
								"    g(i, polynomial_degree(integer_polynomial_ring.zero, g'(i))))"))))
			}))
		a.Show(
			"g' is a family of parameter polynomials of no larger degree that "+
				"keep their leading coefficients, and its table gives that of g",
			By(trimmedOver, leadingNotDropped, leadingStaysNonzero, toTrimmed))
	}),
})}

// MoveMemberToFront — moving a member to the front of a family keeps its
// table. For c < m, the exchange π of 0 and c keeps the indices below m and
// undoes itself, so a family g agrees in sign with the moved family
// λi. g(π(i)) read back through π, and a uniform table of the moved family
// gives one of g (parametric_sign_table.SignTableByAgreement).
var MoveMemberToFront = moveMemberToFrontThm{family.Add(registry.ProofEntry{
	Name: "MoveMemberToFront",
	Key:  "prop_dd71f54936e452de",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m c:num. " +
			"∀π:(num → num). " +
			"∀g:(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"c < m",
			"π(0) = c",
			"π(c) = 0",
			"∀i:num. ¬(i = 0) ∧ ¬(i = c) ⇒ π(i) = i",
		},
		Conclusion: "(∀i:num. i < m ⇒ π(i) < m) ∧ " +
			"(parametric_sign_table(U, C, m, λi:num. g(π(i))) ⇒ parametric_sign_table(U, C, m, g))",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		m, c *Expr[Nat],
		π *Arrow[Nat, Nat],
		g *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		cBelow, toC, toZero, fixes Fact,
	) {
		swapFacts := a.Have(
			"π keeps the indices below m and undoes itself",
			"∀i:num. i < m ⇒ π(i) < m ∧ π(π(i)) = i",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				below := b.Assume()
				b.Cases(b.Term("i = 0"))
				b.When(
					"at 0, π goes to c and back",
					func(d *Argument, atZero Fact) {
						d.Show(
							"c lies below m",
							By(atZero, toC, toZero, cBelow))
					})
				b.Otherwise(
					"away from 0",
					func(d *Argument, notZero Fact) {
						d.Cases(d.Term("i = c"))
						d.When(
							"at c, π goes to 0 and back",
							func(e *Argument, atC Fact) {
								e.Show(
									"0 lies below m",
									By(
										atC,
										toC,
										toZero,
										e.Have(
											"0 lies below m",
											"0 < m",
											ByArith(cBelow))))
							})
						d.Otherwise(
							"elsewhere π fixes i",
							func(e *Argument, notC Fact) {
								e.Show(
									"i lies below m",
									By(Normalized, below, GroupPremises(notZero, notC, fixes.At(e.TermAs[Nat]("i")))))
							})
					})
			}))
		agreeBack := a.Have(
			"in a model meeting C, g(i) has the signs of g(π(π(i))), which is g(i)",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num. ∀x:A.",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
					"i < m",
					"x ∈ F.carrier",
				},
				Conclusion: "ordered_sign(F, lt, «value»(F, ρ, g(i), x)) = " +
					"ordered_sign(F, lt, «value»(F, ρ, g(π(π(i))), x))",
			},
			Derive(func(b *Argument) {
				b.FixAs[FieldOps[A]]("F")
				b.FixAs[Fun2[A, A, Bool]]("lt")
				b.FixAs[Fun[Nat, A]]("ρ")
				i := b.FixAs[Nat]("i")
				b.FixAs[A]("x")
				b.Show(
					"π(π(i)) is i",
					By(Normalized, GroupPremises(b.Assume(), swapFacts.At(i))))
			}))
		a.Show(
			"π keeps the indices below m, and a table of the moved family gives one of g",
			SplitConjAll(
				Case(
					"π keeps the indices below m",
					By(swapFacts)),
				Case(
					"a uniform table of the moved family gives one of g",
					Derive(func(b *Argument) {
						table := b.Assume()
						b.Show(
							"g agrees in sign with the moved family read through π",
							By(
								parametric_sign_table.SignTableByAgreement.At(
									U, C, m, m, b.TermAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]]("λi:num. g(π(i))"), g, π),
								swapFacts,
								agreeBack,
								table))
					}))))
	}),
})}

// DerivativeRemainderFamily — the Cohen–Hörmander family over the parameter
// ring. A family g(0), …, g(m) of parameter polynomials of degree at most
// d + 1, whose first member has degree d + 1 and a leading coefficient of
// fixed nonzero sign τ under C, and each of whose members keeps its leading
// coefficient nonzero wherever it does not specialize to zero, extends to the
// family h of g(1), …, g(m), the formal derivative of g(0), and the
// pseudo-remainders of g(0) by each of those m + 1 divisors
// (ordered_field_polynomial.PseudoRemainderSigns). The members of h from the
// derivative on are parameter polynomials of degree at most d, and a uniform
// table of h gives one of g (parametric_sign_table.DerivativeRemainderStep):
// the derivative specializes to the derivative
// (polynomial_formula.SpecializedDerivative), its leading coefficient
// specializes to d + 1 times that of g(0), and at a root of a divisor each
// remainder has the sign of g(0).
var DerivativeRemainderFamily = derivativeRemainderFamilyThm{family.Add(registry.ProofEntry{
	Name: "DerivativeRemainderFamily",
	Key:  "prop_486e405547ce736d",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m d:num. " +
			"∀τ:int. " +
			"∀g:(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"∀i:num. i < suc(m) ⇒ «overParameters»(g(i))",
			"∀i:num. i < suc(m) ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) ≤ suc(d)",
			"polynomial_degree(integer_polynomial_ring.zero, g(0)) = suc(d)",
			"τ ≠ &0",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). " +
				"    «model»(U, C, F, lt, ρ) ⇒ " +
				"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, g(0, suc(d)))) = τ",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num. " +
				"    «model»(U, C, F, lt, ρ) ∧ " +
				"    i < suc(m) ∧ " +
				"    «specialized»(field_ring(F), ρ, g(i)) ≠ vec_zero(F.zero) ⇒ " +
				"    integer_polynomial_eval(field_ring(F), " +
				"        ρ, " +
				"        g(i, polynomial_degree(integer_polynomial_ring.zero, g(i)))) ≠ " +
				"    F.zero",
		},
		Conclusion: "∃h:(num → num → ((num → num) → int)). " +
			"    (∀i:num. i < m ⇒ h(i) = g(suc(i))) ∧ " +
			"    (∀i:num. " +
			"        m ≤ i ∧ i < suc(m) + suc(m) ⇒ " +
			"        «overParameters»(h(i)) ∧ polynomial_degree(integer_polynomial_ring.zero, h(i)) ≤ d) ∧ " +
			"    (parametric_sign_table(U, C, suc(m) + suc(m), h) ⇒ parametric_sign_table(U, C, suc(m), g))",
		Abbrev: Abbrev{
			{Name: "derivative", Text: "polynomial_derivative(integer_polynomial_ring.add, " +
				"    integer_polynomial_ring.zero, " +
				"    integer_polynomial_ring.mul, " +
				"    integer_polynomial_ring.one, " +
				"    g(0))"},
			{Name: "divisor", Text: "λi:num. COND(i < m, g(suc(i)), «derivative»)"},
		},
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		m, d *Expr[Nat],
		τ *Expr[Int],
		g *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		over, bounded, degree, nonzeroSign, leading, kept Fact,
	) {
		first := a.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("g(0)")
		derivative := a.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("«derivative»")
		parameterRing := a.TermAs[module_record.RingOps[IntegerPolynomial]]("«parameterRing»(U)")
		parameters := a.Have(
			"the parameter polynomials form a commutative ring",
			"comm_ring_on(«parameterRing»(U))",
			Cite(polynomial_formula.ParameterRingCommutative, U))
		positive := a.Have(
			"0 lies below m + 1",
			"0 < suc(m)",
			ByArith())
		operations := a.Have(
			"the integer polynomial ring operates as the polynomial algebra over the integers",
			"integer_polynomial_ring.add = fun_add(int_add) ∧ "+
				"integer_polynomial_ring.zero = fun_zero(int_of_num(0)) ∧ "+
				"integer_polynomial_ring.mul = polynomial_algebra_mul(int_ring) ∧ "+
				"integer_polynomial_ring.one = polynomial_algebra_one(int_ring)",
			Cite(polynomial_formula.IntegerPolynomialRingOperations))
		firstOver := a.Have(
			"g(0) is a parameter polynomial",
			"«overParameters»(g(0))",
			By(operations, GroupPremises(positive, over.At(a.TermAs[Nat]("0")))))
		firstCoefficients := polynomial.CoefficientIn.Read(firstOver)
		derivativeOver := a.Have(
			"so is its derivative",
			"«overParameters»(«derivative»)",
			By(firstOver, polynomial.DerivativeOverCarrier.Read(parameters).AsFact().At(first)))
		derivativeVanishes := a.Have(
			"the derivative vanishes from d + 1 on, the degree of g(0)",
			"vec⟨suc(d)⟩(integer_polynomial_ring.zero, «derivative»)",
			By(operations, firstOver, degree, polynomial.DerivativeVec.Read(parameters).AsFact().At(first)))
		derivativeDegree := a.Have(
			"so it has degree at most d",
			"polynomial_degree(integer_polynomial_ring.zero, «derivative») ≤ d",
			By(derivativeVanishes, polynomial.DegreeLeast))
		divisors := a.Have(
			"each divisor, g(i + 1) below m and the derivative from "+
				"m on, is a parameter polynomial of degree at most d + 1",
			"∀i:num. "+
				"    «overParameters»(«divisor»(i)) ∧ "+
				"    polynomial_degree(integer_polynomial_ring.zero, «divisor»(i)) ≤ suc(d)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				b.Cases(b.Term("i < m"))
				b.When(
					"below m the divisor is g(i + 1), a member of the family",
					func(c *Argument, below Fact) {
						next := c.TermAs[Nat]("suc(i)")
						inFamily := c.Have(
							"i + 1 indexes a member",
							"suc(i) < suc(m)",
							ByArith(below))
						c.Show(
							"g(i + 1) is a parameter polynomial of degree at most d + 1",
							By(
								Normalized,
								operations,
								below,
								GroupPremises(inFamily, over.At(next)),
								GroupPremises(inFamily, bounded.At(next))))
					})
				b.Otherwise(
					"at m the divisor is the derivative",
					func(c *Argument, notBelow Fact) {
						atMost := c.Have(
							"the derivative has degree at most d + 1",
							"polynomial_degree(integer_polynomial_ring.zero, «derivative») ≤ suc(d)",
							ByArith(derivativeDegree))
						c.Show(
							"the derivative is a parameter polynomial of degree at most d + 1",
							By(notBelow, derivativeOver, atMost))
					})
			}))
		_, remainderDef := a.LetAs[Fun2[Nat, Fun2[Nat, Fun[Nat, Nat], Int], Bool]](
			"remainderOf",
			"λi:num. λr:(num → ((num → num) → int)). "+
				"    «overParameters»(r) ∧ "+
				"    vec⟨polynomial_degree(integer_polynomial_ring.zero, «divisor»(i))⟩( "+
				"        integer_polynomial_ring.zero, r) ∧ "+
				"    (∀F:field_ops(A). ∀lt:(A → A → bool). ∀σ:(((num → num) → int) → A). ∀x:A. "+
				"        ordered_field_on(F, lt) ∧ "+
				"        ring_homomorphism(«parameterRing»(U), field_ring(F), σ) ∧ "+
				"        σ(«divisor»(i, polynomial_degree(integer_polynomial_ring.zero, «divisor»(i)))) ≠ "+
				"        F.zero ∧ "+
				"        x ∈ F.carrier ∧ "+
				"        polynomial_eval(F.add, F.zero, F.mul, F.one, λj:num. σ(«divisor»(i, j)), x) = F.zero ⇒ "+
				"        ordered_sign(F, lt, polynomial_eval(F.add, F.zero, F.mul, F.one, λj:num. σ(r(j)), x)) = "+
				"        ordered_sign(F, lt, polynomial_eval(F.add, F.zero, F.mul, F.one, λj:num. σ(g(0, j)), x)))")
		remainders := a.Have(
			"for each divisor, g(0) has a pseudo-remainder by it, vanishing from "+
				"the divisor's degree on, with the sign of g(0) at the divisor's roots",
			"∀i:num. ∃r:(num → ((num → num) → int)). remainderOf(i, r)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				divisor := b.Conjuncts(
					divisors.At(i),
					"the divisor is a parameter polynomial",
					"of degree at most d + 1")
				b.Show(
					"pseudo-divide g(0) by the divisor over the parameter ring",
					Simp(Fwd(remainderDef)),
					By(
						operations,
						parameters,
						firstOver,
						divisor[0],
						ordered_field_polynomial.PseudoRemainderSigns.Inst(
							TypeBinder.BindB[IntegerPolynomial](), TypeBinder.BindA[A]()).At(
							parameterRing,
							first,
							b.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("«divisor»(i)"))))
			}))
		_, chosen := a.ObtainAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]](
			"choose the remainders R(0), R(1), …",
			"∃R:(num → num → ((num → num) → int)). ∀i:num. remainderOf(i, R(i))",
			By(remainders))
		h, hDef := a.LetAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]](
			"h",
			"λi:num. COND(i < m, g(suc(i)), COND(i = m, «derivative», R(i - suc(m))))")
		shifted := a.Have(
			"the first m members of h are g(1), …, g(m)",
			"∀i:num. i < m ⇒ h(i) = g(suc(i))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				below := b.Assume()
				b.Show(
					"below m, h(i) is g(i + 1)",
					By(hDef, below))
			}))
		atDerivative := a.Have(
			"h(m) is the derivative of g(0)",
			"h(m) = «derivative»",
			By(
				hDef,
				a.Have(
					"m does not lie below itself",
					"¬(m < m)",
					ByArith())))
		divisorMembers := a.Have(
			"the first m + 1 members of h are the divisors",
			"∀i:num. i < suc(m) ⇒ h(i) = «divisor»(i)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				index := b.Assume()
				b.Cases(b.Term("i < m"))
				b.When(
					"below m both are g(i + 1)",
					func(c *Argument, below Fact) {
						c.Show(
							"h(i) and the divisor are g(i + 1)",
							By(hDef, below))
					})
				b.Otherwise(
					"at m both are the derivative",
					func(c *Argument, notBelow Fact) {
						c.Show(
							"h(m) and the divisor are the derivative",
							By(
								hDef,
								notBelow,
								c.Have(
									"i is m",
									"i = m",
									ByArith(index, notBelow))))
					})
			}))
		remainderMembers := a.Have(
			"the members after them are the remainders",
			"∀i:num. h(suc(m) + i) = R(i)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				b.Show(
					"m + 1 + i lies past m, at offset i",
					By(
						hDef,
						b.Have(
							"m + 1 + i lies past m, at offset i",
							"¬(suc(m) + i < m) ∧ ¬(suc(m) + i = m) ∧ suc(m) + i - suc(m) = i",
							ByArith())))
			}))
		later := a.Have(
			"the members of h from the derivative on are parameter polynomials of degree at most d",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"m ≤ i",
					"i < suc(m) + suc(m)",
				},
				Conclusion: "«overParameters»(h(i)) ∧ polynomial_degree(integer_polynomial_ring.zero, h(i)) ≤ d",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				inRange := b.Assume()
				b.Cases(b.Term("i = m"))
				b.When(
					"h(m) is the derivative",
					func(c *Argument, at Fact) {
						c.Show(
							"the derivative is a parameter polynomial of degree at most d",
							By(at, atDerivative, derivativeOver, derivativeDegree))
					})
				b.Otherwise(
					"past m, h(i) is the remainder R(i − (m + 1))",
					func(c *Argument, past Fact) {
						offset := c.TermAs[Nat]("i - suc(m)")
						within := c.Have(
							"i − (m + 1) indexes a divisor, and i is m + 1 past it",
							"i - suc(m) < suc(m) ∧ i = suc(m) + (i - suc(m))",
							ByArith(inRange, past))
						remainder := c.Conjuncts(
							c.Have(
								"R(i − (m + 1)) is a parameter polynomial, vanishing "+
									"from the degree of its divisor on, which is at most d + 1",
								"«overParameters»(R(i - suc(m))) ∧ "+
									"vec⟨polynomial_degree(integer_polynomial_ring.zero, «divisor»(i - suc(m)))⟩( "+
									"    integer_polynomial_ring.zero, R(i - suc(m))) ∧ "+
									"polynomial_degree(integer_polynomial_ring.zero, «divisor»(i - suc(m))) ≤ suc(d)",
								By(operations, c.Simplified(chosen.At(offset), Fwd(remainderDef)), divisors.At(offset))),
							"R(i − (m + 1)) is a parameter polynomial",
							"vanishing from the degree of its divisor on",
							"which is at most d + 1")
						small := c.Have(
							"so R(i − (m + 1)) vanishes from d + 1 on and has degree at most d",
							"polynomial_degree(integer_polynomial_ring.zero, R(i - suc(m))) ≤ d",
							By(
								remainder[1],
								remainder[2],
								vec_space.VecMono.At(
									c.TermAs[IntegerPolynomial]("integer_polynomial_ring.zero"),
									c.TermAs[Nat]("polynomial_degree(integer_polynomial_ring.zero, «divisor»(i - suc(m)))"),
									c.TermAs[Nat]("suc(d)"),
									c.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("R(i - suc(m))")),
								polynomial.DegreeLeast))
						c.Show(
							"h(i) is the remainder R(i − (m + 1)), a parameter polynomial of degree at most d",
							By(Normalized, within, remainderMembers.At(offset), remainder[0], small))
					})
			}))
		firstLeading := a.Have(
			"in a model meeting C, the leading coefficient of g(0) specializes into F and stays nonzero",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
				},
				Conclusion: "integer_polynomial_eval(field_ring(F), ρ, g(0, suc(d))) ∈ F.carrier ∧ " +
					"integer_polynomial_eval(field_ring(F), ρ, g(0, suc(d))) ≠ F.zero",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				model := b.Assume()
				opened := b.Conjuncts(
					GroupPremises(model, parametric_sign_table.ModelSpecialization.At(U, C, F, lt, ρ)),
					"F is a field",
					"F with lt is an ordered field",
					"ρ gives carrier points to the parameters",
					"specialization at ρ is a ring homomorphism",
					"that keeps zero")
				ordered, specialization := opened[1], opened[3]
				lead := b.TermAs[IntegerPolynomial]("g(0, suc(d))")
				leadIn := b.Have(
					"the leading coefficient of g(0) specializes into F",
					"integer_polynomial_eval(field_ring(F), ρ, g(0, suc(d))) ∈ F.carrier",
					By(
						firstCoefficients.At(b.TermAs[Nat]("suc(d)")),
						ring_homomorphism.MapIn.Read(specialization).AsFact().At(lead)))
				b.Show(
					"of the nonzero sign τ, it is not zero",
					By(
						leadIn,
						GroupPremises(model, leading.At(F, lt, ρ)),
						nonzeroSign,
						ordered_field.SignValues.Read(ordered).AsFact().At(
							b.TermAs[A]("integer_polynomial_eval(field_ring(F), ρ, g(0, suc(d)))"))))
			}))
		stepped := a.Have(
			"a uniform table of h gives one of g",
			"parametric_sign_table(U, C, suc(m) + suc(m), h) ⇒ parametric_sign_table(U, C, suc(m), g)",
			Derive(func(b *Argument) {
				table := b.Assume()
				leadingModels := b.Have(
					"in every model meeting C, the specialization of g(0) "+
						"keeps degree d + 1, its leading coefficient of sign τ",
					Statement{
						Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
						Hypotheses: []string{
							"«model»(U, C, F, lt, ρ)",
						},
						Conclusion: "polynomial_degree(F.zero, «specialized»(field_ring(F), ρ, g(0))) = suc(d) ∧ " +
							"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, g(0, suc(d)))) = τ",
					},
					Derive(func(c *Argument) {
						F := c.FixAs[FieldOps[A]]("F")
						lt := c.FixAs[Fun2[A, A, Bool]]("lt")
						ρ := c.FixAs[Fun[Nat, A]]("ρ")
						model := c.Assume()
						opened := c.Conjuncts(
							GroupPremises(model, parametric_sign_table.ModelSpecialization.At(U, C, F, lt, ρ)),
							"F is a field",
							"F with lt is an ordered field",
							"ρ gives carrier points to the parameters",
							"specialization at ρ is a ring homomorphism",
							"that keeps zero")
						lead := c.Conjuncts(
							GroupPremises(model, firstLeading.At(F, lt, ρ)),
							"the leading coefficient of g(0) specializes into F",
							"to a nonzero element")
						c.Show(
							"a nonzero leading coefficient keeps the degree",
							By(
								operations,
								degree,
								lead[1],
								model,
								firstOver,
								polynomial_formula.SpecializedDegree.Read(field.RingOn.Read(opened[0])).At(U, ρ, first),
								GroupPremises(model, leading.At(F, lt, ρ))))
					}))
				derivativeModels := b.Have(
					"in every model meeting C, h(m) specializes to the derivative of the specialization of g(0)",
					Statement{
						Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
						Hypotheses: []string{
							"«model»(U, C, F, lt, ρ)",
						},
						Conclusion: "«specialized»(field_ring(F), ρ, h(m)) = " +
							"polynomial_derivative(F.add, F.zero, F.mul, F.one, «specialized»(field_ring(F), ρ, g(0)))",
					},
					Derive(func(c *Argument) {
						F := c.FixAs[FieldOps[A]]("F")
						lt := c.FixAs[Fun2[A, A, Bool]]("lt")
						ρ := c.FixAs[Fun[Nat, A]]("ρ")
						opened := c.Conjuncts(
							GroupPremises(c.Assume(), parametric_sign_table.ModelSpecialization.At(U, C, F, lt, ρ)),
							"F is a field",
							"F with lt is an ordered field",
							"ρ gives carrier points to the parameters",
							"specialization at ρ is a ring homomorphism",
							"that keeps zero")
						c.Show(
							"specialization commutes with the derivative",
							By(
								operations,
								atDerivative,
								opened[2],
								firstOver,
								polynomial_formula.SpecializedDerivative.Read(field.RingOn.Read(opened[0])).At(U, ρ, first)))
					}))
				remainderModels := b.Have(
					"in every model meeting C, at a root of a divisor that does "+
						"not specialize to zero, its remainder has the sign of g(0)",
					Statement{
						Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num. ∀x:A.",
						Hypotheses: []string{
							"«model»(U, C, F, lt, ρ)",
							"i < suc(m)",
							"«specialized»(field_ring(F), ρ, h(i)) ≠ vec_zero(F.zero)",
							"x ∈ F.carrier",
							"«value»(F, ρ, h(i), x) = F.zero",
						},
						Conclusion: "ordered_sign(F, lt, «value»(F, ρ, h(suc(m) + i), x)) = " +
							"ordered_sign(F, lt, «value»(F, ρ, g(0), x))",
					},
					Derive(func(c *Argument) {
						F := c.FixAs[FieldOps[A]]("F")
						lt := c.FixAs[Fun2[A, A, Bool]]("lt")
						ρ := c.FixAs[Fun[Nat, A]]("ρ")
						i := c.FixAs[Nat]("i")
						x := c.FixAs[A]("x")
						assumed := c.Assume()
						given := c.Conjuncts(
							assumed,
							"F with lt is a real closed field",
							"ρ gives carrier points to the parameters",
							"C holds at F, lt and ρ",
							"i indexes a divisor",
							"h(i) does not specialize to zero",
							"x lies in F",
							"x is a root of the specialization of h(i)")
						opened := c.Conjuncts(
							GroupPremises(assumed, parametric_sign_table.ModelSpecialization.At(U, C, F, lt, ρ)),
							"F is a field",
							"F with lt is an ordered field",
							"ρ gives carrier points to the parameters",
							"specialization at ρ is a ring homomorphism",
							"that keeps zero")
						lead := c.Conjuncts(
							GroupPremises(assumed, firstLeading.At(F, lt, ρ)),
							"the leading coefficient of g(0) specializes into F",
							"to a nonzero element")
						fieldOn, ordered, specialization := opened[0], opened[1], opened[3]
						leadIn, leadNonzero := lead[0], lead[1]
						isDivisor := GroupPremises(given[3], divisorMembers.At(i))
						leadKept := c.Have(
							"the divisor's leading coefficient does not specialize to zero",
							"integer_polynomial_eval(field_ring(F), "+
								"    ρ, "+
								"    «divisor»(i, polynomial_degree(integer_polynomial_ring.zero, «divisor»(i)))) ≠ "+
								"F.zero",
							Derive(func(e *Argument) {
								e.Cases(e.Term("i < m"))
								e.When(
									"below m the divisor is g(i + 1), which keeps its leading coefficient",
									func(f *Argument, below Fact) {
										next := f.Have(
											"i + 1 indexes a member",
											"suc(i) < suc(m)",
											ByArith(below))
										f.Show(
											"g(i + 1) does not specialize to zero, so its leading coefficient does not",
											By(
												operations,
												below,
												isDivisor,
												given[4],
												GroupPremises(assumed, next, kept.At(F, lt, ρ, f.TermAs[Nat]("suc(i)")))))
									})
								e.Otherwise(
									"at m the divisor is the derivative, whose coefficient at d is d + 1 times the leading one of g(0)",
									func(f *Argument, notBelow Fact) {
										fieldRing := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
										numeral := f.TermAs[A]("monoid_pow(F.add, F.zero, F.one, suc(d))")
										lead := f.TermAs[A]("integer_polynomial_eval(field_ring(F), ρ, g(0, suc(d)))")
										environment := given[1]
										specialized := f.Have(
											"the derivative specializes to the derivative of the specialization of g(0)",
											"«specialized»(field_ring(F), ρ, «derivative») = "+
												"polynomial_derivative(F.add, F.zero, F.mul, F.one, «specialized»(field_ring(F), ρ, g(0)))",
											By(
												operations,
												environment,
												firstOver,
												polynomial_formula.SpecializedDerivative.Read(fieldRing).At(U, ρ, first)))
										atD := f.Have(
											"its coefficient at d specializes to d + 1 times the leading coefficient of g(0)",
											"integer_polynomial_eval(field_ring(F), ρ, «derivative»(d)) = "+
												"F.mul(monoid_pow(F.add, F.zero, F.one, suc(d)), "+
												"    integer_polynomial_eval(field_ring(F), ρ, g(0, suc(d))))",
											By(
												specialized,
												polynomial.PolynomialDerivativeDef.At(
													f.TermAs[Fun2[A, A, A]]("F.add"),
													f.TermAs[A]("F.zero"),
													f.TermAs[Fun2[A, A, A]]("F.mul"),
													f.TermAs[A]("F.one"),
													f.TermAs[Fun[Nat, A]]("«specialized»(field_ring(F), ρ, g(0))"),
													d)))
										numeralPositive := f.Have(
											"d + 1 is positive in F",
											"lt(F.zero, monoid_pow(F.add, F.zero, F.one, suc(d)))",
											By(
												ordered,
												ordered_field.MultipleOfOnePositive.At(F, lt, f.TermAs[Nat]("suc(d)")),
												f.Have(
													"0 < d + 1",
													"0 < suc(d)",
													ByArith())))
										numeralIn := f.Have(
											"and lies in F",
											"monoid_pow(F.add, F.zero, F.one, suc(d)) ∈ F.carrier",
											By(
												comm_ring.OneIn.Read(fieldRing),
												comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(fieldRing)).AsFact().At(
													f.TermAs[A]("F.one"), f.TermAs[Nat]("suc(d)"))))
										numeralNonzero := f.Have(
											"so it is not zero",
											"monoid_pow(F.add, F.zero, F.one, suc(d)) ≠ F.zero",
											By(numeralPositive, numeralIn, ordered_field.Irreflexive.Read(ordered).AsFact().At(numeral)))
										atDNonzero := f.Have(
											"so the coefficient at d does not specialize to zero",
											"integer_polynomial_eval(field_ring(F), ρ, «derivative»(d)) ≠ F.zero",
											By(
												atD,
												numeralNonzero,
												leadNonzero,
												numeralIn,
												leadIn,
												field.MulEqZeroOn.Read(fieldOn).AsFact().At(numeral, lead)))
										coefficient := f.Have(
											"so the coefficient of the derivative at d is not zero",
											"«derivative»(d) ≠ integer_polynomial_ring.zero",
											By(operations, atDNonzero, ring_homomorphism.MapZero.Read(specialization)))
										exact := f.Have(
											"and the derivative, vanishing from d + 1 on, has degree d",
											"polynomial_degree(integer_polynomial_ring.zero, «derivative») = d",
											By(
												operations,
												coefficient,
												derivativeOver,
												derivativeVanishes,
												polynomial.DegreeExact.At(
													f.TermAs[IntegerPolynomial]("integer_polynomial_ring.zero"),
													f.TermAs[Set[IntegerPolynomial]]("polynomial_algebra(int_ring, U)"),
													derivative,
													d)))
										f.Show(
											"the derivative's leading coefficient, its coefficient at d, does not specialize to zero",
											By(notBelow, exact, atDNonzero))
									})
							}))
						sign := c.Conjuncts(
							c.Simplified(chosen.At(i), Fwd(remainderDef)),
							"R(i) is a parameter polynomial",
							"vanishing from the divisor's degree on",
							"with the sign of g(0) at the divisor's roots")[2]
						rootOfDivisor := c.Have(
							"x is a root of the specialization of the divisor",
							"polynomial_eval(F.add, "+
								"    F.zero, "+
								"    F.mul, "+
								"    F.one, "+
								"    λj:num. integer_polynomial_eval(field_ring(F), ρ, «divisor»(i, j)), "+
								"    x) = "+
								"F.zero",
							By(operations, given[6], isDivisor))
						remainderSign := c.Have(
							"so the remainder R(i) has the sign of g(0) at x",
							"ordered_sign(F, lt, «value»(F, ρ, R(i), x)) = ordered_sign(F, lt, «value»(F, ρ, g(0), x))",
							By(
								operations,
								sign.At(
									F,
									lt,
									c.TermAs[Fun[IntegerPolynomial, A]](
										"λq:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, q)"),
									x),
								ordered,
								specialization,
								leadKept,
								given[5],
								rootOfDivisor))
						c.Show(
							"and R(i) is the member of h at m + 1 + i",
							By(remainderSign, remainderMembers.At(i)))
					}))
				b.Show(
					"the Cohen–Hörmander step",
					By(
						operations,
						parametric_sign_table.DerivativeRemainderStep.At(U, C, m, a.TermAs[Nat]("suc(d)"), τ, g, h),
						over,
						shifted,
						b.Have(
							"d + 1 is positive",
							"0 < suc(d)",
							ByArith()),
						leadingModels,
						derivativeModels,
						remainderModels,
						table))
			}))
		a.Take(h)
		a.Show(
			"h is g(1), …, g(m), then members of degree at most d, and its table gives one of g",
			By(shifted, later, stepped))
	}),
})}

// LowerTopDegreeMember — lowering a member of top degree. Let g be a family
// of parameter polynomials of degree at most d + 1 whose members after c
// have lower degree, let g(c) have degree d + 1 and a leading coefficient of
// fixed nonzero sign τ under C, and let each member keep its leading
// coefficient nonzero wherever it does not specialize to zero. Moved to the
// front (MoveMemberToFront), g(c) heads a family k, and h is the
// Cohen–Hörmander family of k (DerivativeRemainderFamily): h holds the other
// members of g, those before c first, then the derivative of g(c) and the
// pseudo-remainders of g(c), of degree at most d. So the members of h of
// degree d + 1 all come before c, and a uniform table of h gives one of g.
var LowerTopDegreeMember = lowerTopDegreeMemberThm{family.Add(registry.ProofEntry{
	Name: "LowerTopDegreeMember",
	Key:  "prop_7f69aca9b973f5d",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m c d:num. " +
			"∀τ:int. " +
			"∀g:(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"c < m",
			"∀i:num. i < m ⇒ «overParameters»(g(i))",
			"∀i:num. i < m ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) ≤ suc(d)",
			"∀i:num. i < m ∧ c < i ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) < suc(d)",
			"polynomial_degree(integer_polynomial_ring.zero, g(c)) = suc(d)",
			"τ ≠ &0",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). " +
				"    «model»(U, C, F, lt, ρ) ⇒ " +
				"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, g(c, suc(d)))) = τ",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num. " +
				"    «model»(U, C, F, lt, ρ) ∧ " +
				"    i < m ∧ " +
				"    «specialized»(field_ring(F), ρ, g(i)) ≠ vec_zero(F.zero) ⇒ " +
				"    integer_polynomial_eval(field_ring(F), " +
				"        ρ, " +
				"        g(i, polynomial_degree(integer_polynomial_ring.zero, g(i)))) ≠ " +
				"    F.zero",
		},
		Conclusion: "∃h:(num → num → ((num → num) → int)). " +
			"    (∀i:num. i < m + m ⇒ «overParameters»(h(i))) ∧ " +
			"    (∀i:num. i < m + m ⇒ polynomial_degree(integer_polynomial_ring.zero, h(i)) ≤ suc(d)) ∧ " +
			"    (∀i:num. " +
			"        i < m + m ∧ c ≤ i ⇒ polynomial_degree(integer_polynomial_ring.zero, h(i)) < suc(d)) ∧ " +
			"    (parametric_sign_table(U, C, m + m, h) ⇒ parametric_sign_table(U, C, m, g))",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		m, c, d *Expr[Nat],
		τ *Expr[Int],
		g *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		cBelow, over, bounded, laterLower, topDegree, nonzeroSign, leading, kept Fact,
	) {
		operations := a.Have(
			"the integer polynomial ring operates as the polynomial algebra over the integers",
			"integer_polynomial_ring.add = fun_add(int_add) ∧ "+
				"integer_polynomial_ring.zero = fun_zero(int_of_num(0)) ∧ "+
				"integer_polynomial_ring.mul = polynomial_algebra_mul(int_ring) ∧ "+
				"integer_polynomial_ring.one = polynomial_algebra_one(int_ring)",
			Cite(polynomial_formula.IntegerPolynomialRingOperations))
		p, mSucc := a.ObtainAs[Nat](
			"m is a successor p + 1, c lying below it",
			"∃p:num. m = suc(p)",
			By(
				Normalized,
				a.Have(
					"m is not 0",
					"¬(m = 0)",
					ByArith(cBelow)),
				peano.Cases.At(m)))
		π, πDef := a.LetAs[Fun[Nat, Nat]]("π", "λi:num. COND(i = 0, c, COND(i = c, 0, i))")
		k, kDef := a.LetAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]]("k", "λi:num. g(π(i))")
		swap := a.Conjuncts(
			a.Have(
				"π sends 0 to c and c to 0, and fixes every other index",
				"π(0) = c ∧ π(c) = 0 ∧ (∀i:num. ¬(i = 0) ∧ ¬(i = c) ⇒ π(i) = i)",
				By(πDef)),
			"π sends 0 to c",
			"π sends c to 0",
			"π fixes every other index")
		moved := a.Conjuncts(
			GroupPremises(
				cBelow,
				swap[0],
				swap[1],
				swap[2],
				MoveMemberToFront.At(U, C, m, c, π, g)),
			"π keeps the indices below m",
			"a uniform table of g read through π gives one of g")
		keeps, toFront := moved[0], moved[1]
		leadSign := a.Have(
			"in a model meeting C, the leading coefficient of k(0) has the sign τ",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
				},
				Conclusion: "ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, k(0, suc(d)))) = τ",
			},
			Derive(func(inModel *Argument) {
				F := inModel.FixAs[FieldOps[A]]("F")
				lt := inModel.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := inModel.FixAs[Fun[Nat, A]]("ρ")
				model := inModel.Assume()
				inModel.Show(
					"k(0) is g(c)",
					By(kDef, swap[0], GroupPremises(model, leading.At(F, lt, ρ))))
			}))
		frontMembers := a.Have(
			"the members of k are those of g, permuted: parameter polynomials of degree at most d + 1",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < suc(p)",
				},
				Conclusion: "«overParameters»(k(i)) ∧ " +
					"polynomial_degree(integer_polynomial_ring.zero, k(i)) ≤ suc(d)",
			},
			Derive(func(member *Argument) {
				member.FixAs[Nat]("i")
				below := member.Assume()
				moved := member.Have(
					"π(i) indexes a member",
					"π(i) < m",
					By(Normalized, mSucc, below, keeps))
				member.Show(
					"k(i) is g(π(i))",
					By(
						Normalized,
						operations,
						kDef,
						GroupPremises(moved, over.At(member.TermAs[Nat]("π(i)"))),
						GroupPremises(moved, bounded.At(member.TermAs[Nat]("π(i)")))))
			}))
		frontLeading := a.Have(
			"in a model meeting C, a member of k that does not "+
				"specialize to zero keeps its leading coefficient nonzero",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num.",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
					"i < suc(p)",
					"«specialized»(field_ring(F), ρ, k(i)) ≠ vec_zero(F.zero)",
				},
				Conclusion: "integer_polynomial_eval(field_ring(F), " +
					"    ρ, " +
					"    k(i, polynomial_degree(integer_polynomial_ring.zero, k(i)))) ≠ " +
					"F.zero",
			},
			Derive(func(member *Argument) {
				F := member.FixAs[FieldOps[A]]("F")
				lt := member.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := member.FixAs[Fun[Nat, A]]("ρ")
				member.FixAs[Nat]("i")
				assumed := member.Assume()
				below := member.Have(
					"i indexes a member of k",
					"i < suc(p)",
					By(assumed))
				moved := member.Have(
					"π(i) indexes a member",
					"π(i) < m",
					By(Normalized, mSucc, below, keeps))
				member.Show(
					"k(i) is g(π(i))",
					By(Normalized, operations, kDef, assumed, moved, kept.At(F, lt, ρ, member.TermAs[Nat]("π(i)"))))
			}))
		reduction := a.Have(
			"the Cohen–Hörmander family of k",
			"∃h:(num → num → ((num → num) → int)). "+
				"    (∀i:num. i < p ⇒ h(i) = k(suc(i))) ∧ "+
				"    (∀i:num. "+
				"        p ≤ i ∧ i < suc(p) + suc(p) ⇒ "+
				"        «overParameters»(h(i)) ∧ polynomial_degree(integer_polynomial_ring.zero, h(i)) ≤ d) ∧ "+
				"    (parametric_sign_table(U, C, suc(p) + suc(p), h) ⇒ parametric_sign_table(U, C, suc(p), k))",
			By(
				operations,
				DerivativeRemainderFamily.At(U, C, p, d, τ, k),
				frontMembers,
				a.Have(
					"k(0) is g(c), of degree d + 1",
					"polynomial_degree(integer_polynomial_ring.zero, k(0)) = suc(d)",
					By(kDef, swap[0], topDegree)),
				nonzeroSign,
				leadSign,
				frontLeading))
		h, reducedFacts := a.UnpackAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]](reduction, "h")
		reducedParts := a.Conjuncts(
			reducedFacts,
			"below p, h(i) is k(i + 1)",
			"from p on, its members are parameter polynomials of degree at most d",
			"a uniform table of h gives one of k")
		reducedMembers := a.Have(
			"every member of h is a parameter polynomial of degree at most d + 1",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < m + m",
				},
				Conclusion: "«overParameters»(h(i)) ∧ " +
					"polynomial_degree(integer_polynomial_ring.zero, h(i)) ≤ suc(d)",
			},
			Derive(func(member *Argument) {
				member.FixAs[Nat]("i")
				below := member.Assume()
				member.Cases(member.Term("i < p"))
				member.When(
					"below p, h(i) is the member k(i + 1)",
					func(shifted *Argument, earlier Fact) {
						next := shifted.TermAs[Nat]("suc(i)")
						shifted.Show(
							"a member of k",
							By(
								Normalized,
								operations,
								GroupPremises(earlier, reducedParts[0].At(shifted.TermAs[Nat]("i"))),
								GroupPremises(shifted.Have(
									"i + 1 indexes a member of k",
									"suc(i) < suc(p)",
									ByArith(earlier)), frontMembers.At(next))))
					})
				member.Otherwise(
					"from p on, of degree at most d",
					func(added *Argument, later Fact) {
						lower := added.Have(
							"h(i) is a parameter polynomial of degree at most d",
							"«overParameters»(h(i)) ∧ polynomial_degree(integer_polynomial_ring.zero, h(i)) ≤ d",
							By(
								operations,
								reducedParts[1],
								added.Have(
									"i lies from p on",
									"p ≤ i ∧ i < suc(p) + suc(p)",
									ByArith(below, later, mSucc))))
						parts := added.Conjuncts(
							lower,
							"h(i) is a parameter polynomial",
							"of degree at most d")
						added.Show(
							"at most d, so at most d + 1",
							By(
								parts[0],
								added.Have(
									"so at most d + 1",
									"polynomial_degree(integer_polynomial_ring.zero, h(i)) ≤ suc(d)",
									ByArith(parts[1]))))
					})
			}))
		reducedBefore := a.Have(
			"the members of h of degree d + 1 come before c",
			"∀i:num. i < m + m ∧ c ≤ i ⇒ polynomial_degree(integer_polynomial_ring.zero, h(i)) < suc(d)",
			Derive(func(member *Argument) {
				member.FixAs[Nat]("i")
				index := member.Conjuncts(
					member.Assume(),
					"i indexes a member of h",
					"at c or later")
				member.Cases(member.Term("i < p"))
				member.When(
					"below p, h(i) is k(i + 1) = g(i + 1), after c",
					func(shifted *Argument, earlier Fact) {
						fixed := shifted.Have(
							"π fixes i + 1, which is neither 0 nor c",
							"k(suc(i)) = g(suc(i))",
							By(
								kDef,
								GroupPremises(shifted.Have(
									"i + 1 is neither 0 nor c",
									"¬(suc(i) = 0) ∧ ¬(suc(i) = c)",
									ByArith(index[1])), swap[2].At(shifted.TermAs[Nat]("suc(i)")))))
						inFamily := shifted.Have(
							"i + 1 indexes a member of g, after c",
							"suc(i) < m ∧ c < suc(i)",
							ByArith(earlier, mSucc, index[1]))
						same := shifted.Have(
							"so h(i) has the degree of g(i + 1)",
							"polynomial_degree(integer_polynomial_ring.zero, h(i)) = "+
								"polynomial_degree(integer_polynomial_ring.zero, g(suc(i)))",
							By(Normalized, reducedParts[0], earlier, fixed))
						shifted.Show(
							"which lies below d + 1",
							ByArith(
								same,
								shifted.Have(
									"g(i + 1), after c, has degree below d + 1",
									"polynomial_degree(integer_polynomial_ring.zero, g(suc(i))) < suc(d)",
									By(inFamily, laterLower))))
					})
				member.Otherwise(
					"from p on, of degree at most d",
					func(added *Argument, later Fact) {
						atMostD := added.Have(
							"h(i) has degree at most d",
							"polynomial_degree(integer_polynomial_ring.zero, h(i)) ≤ d",
							By(
								operations,
								reducedParts[1],
								added.Have(
									"i lies from p on",
									"p ≤ i ∧ i < suc(p) + suc(p)",
									ByArith(index[0], later, mSucc))))
						added.Show(
							"at most d, below d + 1",
							ByArith(atMostD))
					})
			}))
		a.Take(h)
		a.Show(
			"h meets the bounds, its members of degree d + 1 before c, and its table gives one of g",
			SplitConjAll(
				Case(
					"every member of h is a parameter polynomial",
					By(reducedMembers)),
				Case(
					"of degree at most d + 1",
					By(reducedMembers)),
				Case(
					"its members of degree d + 1 come before c",
					By(reducedBefore)),
				Case(
					"a uniform table of h gives one of k, read through π one of g",
					Derive(func(table *Argument) {
						tableH := table.Assume()
						frontTable := table.Have(
							"so k has one",
							"parametric_sign_table(U, C, m, k)",
							By(Normalized, mSucc, reducedParts[2], tableH))
						table.Show(
							"hence g has one",
							By(Normalized, toFront, kDef, frontTable))
					}))))
	}),
})}

// ParameterRingSignTable — every finite family of polynomials over the
// parameter ring has a uniform sign table, under any condition. By induction
// on a bound D on the degrees and, under it, on the number c of leading
// indices whose members may have degree D. A family whose members of degree
// D + 1 all come before c + 1 is first split on the signs of all its
// coefficients (parametric_sign_table.SignTableBySigns), not only on the
// leading one of the member at c: the Cohen–Hörmander step divides by every
// member, and needs each one's leading coefficient nonzero. Under one sign
// assignment the coefficients of sign zero are dropped
// (DropZeroSignCoefficients), after which every member keeps its leading
// coefficient nonzero. If the member at c has lost its top degree, the
// family falls under c; otherwise lowering it (LowerTopDegreeMember) gives a
// family of m + m members, those of degree D + 1 before c. Either way the
// induction hypothesis at c is applied to a new family under the condition
// refined by the sign assignment, so the inner statement quantifies the
// condition, the size and the family after D and c.
var ParameterRingSignTable = parameterRingSignTableThm{family.Add(registry.ProofEntry{
	Name: "ParameterRingSignTable",
	Key:  "prop_e342bc78b3064438",
	Build: family.Sections(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m:num. " +
			"∀g:(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"∀i:num. i < m ⇒ «overParameters»(g(i))",
		},
		Conclusion: "parametric_sign_table(U, C, m, g)",
		Abbrev: Abbrev{
			{Name: "coefficientIndexes", Text: "set_cross({i:num | i < m}, {n:num | n < suc(suc(D))})"},
			{Name: "degrees", Text: "image(λi:num. polynomial_degree(integer_polynomial_ring.zero, g(i)), " +
				"    {i:num | i < m})"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// No index lies below m and at or past a c that is at least m, so any bound
		// holds of the members there.
		noIndexPast := ctx.Lemma(Statement{
			Binders: "∀m c:num. ∀g:(num → num → ((num → num) → int)). ∀D i:num.",
			Hypotheses: []string{
				"i < m",
				"m ≤ c",
				"c ≤ i",
			},
			Conclusion: "polynomial_degree(integer_polynomial_ring.zero, g(i)) < D",
		}, func(
			a *Argument,
			m, c *Expr[Nat],
			g *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
			D, i *Expr[Nat],
			chain Fact,
		) {
			a.Show(
				"i < m, m ≤ c and c ≤ i cannot all hold",
				ByArith(chain))
		})
		// The step of the induction on the degree bound. Suppose that a family of
		// degree at most D whose members of degree D come before a given index has
		// a uniform table, whatever the index and the condition. Then so does a
		// family of degree at most D + 1 whose members of degree D + 1 come before
		// c: by induction on c.
		degreeStep := ctx.Lemma(Statement{
			Binders: "∀U:set(num). " +
				"∀D c:num. " +
				"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
				"∀m:num. " +
				"∀g:(num → num → ((num → num) → int)).",
			Hypotheses: []string{
				"∀b:num. " +
					"∀B:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
					"∀l:num. " +
					"∀k:(num → num → ((num → num) → int)). " +
					"    (∀i:num. i < l ⇒ «overParameters»(k(i))) ∧ " +
					"    (∀i:num. i < l ⇒ polynomial_degree(integer_polynomial_ring.zero, k(i)) ≤ D) ∧ " +
					"    (∀i:num. i < l ∧ b ≤ i ⇒ polynomial_degree(integer_polynomial_ring.zero, k(i)) < D) ⇒ " +
					"    parametric_sign_table(U, B, l, k)",
				"∀i:num. i < m ⇒ «overParameters»(g(i))",
				"∀i:num. i < m ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) ≤ suc(D)",
				"∀i:num. i < m ∧ c ≤ i ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) < suc(D)",
			},
			Conclusion: "parametric_sign_table(U, C, m, g)",
		}, func(topDegree *Argument, U *Expr[Set[Nat]], D *Expr[Nat], lower Fact) {
			operations := topDegree.Have(
				"the integer polynomial ring operates as the polynomial algebra over the integers",
				"integer_polynomial_ring.add = fun_add(int_add) ∧ "+
					"integer_polynomial_ring.zero = fun_zero(int_of_num(0)) ∧ "+
					"integer_polynomial_ring.mul = polynomial_algebra_mul(int_ring) ∧ "+
					"integer_polynomial_ring.one = polynomial_algebra_one(int_ring)",
				Cite(polynomial_formula.IntegerPolynomialRingOperations))
			topDegree.Induct("c")
			topDegree.Base(
				"before 0 no member has degree D + 1: the family has degree at most D",
				func(noneTop *Argument) {
					C := noneTop.FixAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]]("C")
					m := noneTop.FixAs[Nat]("m")
					g := noneTop.FixAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]]("g")
					given := noneTop.Conjuncts(
						noneTop.Assume(),
						"every member is a parameter polynomial",
						"of degree at most D + 1",
						"and in fact below D + 1")
					atMostD := noneTop.Have(
						"every member has degree at most D",
						"∀i:num. i < m ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) ≤ D",
						Derive(func(e *Argument) {
							e.FixAs[Nat]("i")
							below := e.Assume()
							e.Show(
								"below D + 1 is at most D",
								ByArith(e.Have(
									"g(i) has degree below D + 1",
									"polynomial_degree(integer_polynomial_ring.zero, g(i)) < suc(D)",
									By(
										below,
										given[2],
										e.Have(
											"every index lies at 0 or later",
											"0 ≤ i",
											ByArith())))))
						}))
					noneTop.Show(
						"the induction hypothesis at degree D, with every index allowed",
						ByArith(lower.At(m, C, m, g), given[0], atMostD, At(noIndexPast, m, m, g, D)))
				})
			topDegree.Step(
				"before c + 1: split on the coefficient signs, then lower the member at c",
				func(nextTop *Argument, before Fact) {
					C := nextTop.FixAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]]("C")
					m := nextTop.FixAs[Nat]("m")
					g := nextTop.FixAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]]("g")
					given := nextTop.Conjuncts(
						nextTop.Assume(),
						"every member is a parameter polynomial",
						"of degree at most D + 1",
						"those of degree D + 1 coming before c + 1")
					over, bounded, topFirst := given[0], given[1], given[2]
					coefficients := nextTop.Have(
						"every coefficient of a member is a parameter polynomial",
						"∀i n:num. i < m ⇒ g(i, n) ∈ polynomial_algebra(int_ring, U)",
						Derive(func(e *Argument) {
							i := e.FixAs[Nat]("i")
							n := e.FixAs[Nat]("n")
							below := e.Assume()
							e.Show(
								"a coefficient of a parameter polynomial",
								By(polynomial.CoefficientIn.Read(e.Simplified(GroupPremises(below, over.At(i)))).At(n)))
						}))
					cBelow := nextTop.Assuming(
						nextTop.Term("c < m"),
						"c indexes no member: those of degree D + 1 come before c",
						Given(func(indexesNone *Argument, notBelow Fact) {
							beforeC := indexesNone.Have(
								"no member lies at c or later",
								"∀i:num. i < m ∧ c ≤ i ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) < suc(D)",
								ByArith(
									notBelow,
									At(noIndexPast, m, indexesNone.TermAs[Nat]("c"), g, indexesNone.TermAs[Nat]("suc(D)"))))
							indexesNone.Show(
								"the induction hypothesis at c",
								By(before.At(C, m, g), over, bounded, beforeC))
						}))
					finiteCross := nextTop.Have(
						"the coefficients g(i, n), i < m and n ≤ D + 1, are finitely many",
						"finite(«coefficientIndexes»)",
						By(
							finite_set.FiniteProduct,
							num_segment.FiniteBelowStrict.At(m),
							num_segment.FiniteBelowStrict.At(nextTop.TermAs[Nat]("suc(suc(D))"))))
					coefficientsIn := nextTop.Have(
						"and each is a parameter polynomial",
						"∀j:prod(num, num). j ∈ «coefficientIndexes» ⇒ g(fst(j), snd(j)) ∈ polynomial_algebra(int_ring, U)",
						Derive(func(f *Argument) {
							f.FixAs[Prod[Nat, Nat]]("j")
							f.Show(
								"a coefficient of a member",
								By(f.Assume(), set_product.InCrossProjections, coefficients))
						}))
					perSign := nextTop.Have(
						"the step divides by every member, so the split is on every coefficient: "+
							"under each assignment s of their signs, g has a uniform table",
						"∀s:(prod(num, num) → int). "+
							"    parametric_sign_table(U, "+
							"        λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
							"            C(F, lt, ρ) ∧ "+
							"            (∀j:prod(num, num). "+
							"                j ∈ «coefficientIndexes» ⇒ "+
							"                ordered_sign(F, "+
							"                    lt, "+
							"                    integer_polynomial_eval(field_ring(F), ρ, g(fst(j), snd(j)))) = "+
							"                s(j)), "+
							"        m, "+
							"        g)",
						Derive(func(underSigns *Argument) {
							s := underSigns.FixAs[Fun[Prod[Nat, Nat], Int]]("s")
							K, KDef := underSigns.LetAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]](
								"K",
								"λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
									"    C(F, lt, ρ) ∧ "+
									"    (∀j:prod(num, num). "+
									"        j ∈ «coefficientIndexes» ⇒ "+
									"        ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, g(fst(j), snd(j)))) = s(j))")
							signFixed := underSigns.Have(
								"in a model meeting K, each coefficient g(i, n), i < m and n ≤ D + 1, has the sign s(i, n)",
								Statement{
									Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i n:num.",
									Hypotheses: []string{
										"«model»(U, K, F, lt, ρ)",
										"i < m",
										"n < suc(suc(D))",
									},
									Conclusion: "ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, g(i, n))) = s((i, n))",
								},
								Derive(func(inModel *Argument) {
									inModel.FixAs[FieldOps[A]]("F")
									inModel.FixAs[Fun2[A, A, Bool]]("lt")
									inModel.FixAs[Fun[Nat, A]]("ρ")
									i := inModel.FixAs[Nat]("i")
									n := inModel.FixAs[Nat]("n")
									given := inModel.Conjuncts(
										inModel.Assume(),
										"F with lt is a real closed field",
										"ρ gives carrier points to the parameters",
										"K holds at F, lt and ρ",
										"i indexes a member",
										"n is at most D + 1")
									signs := inModel.Conjuncts(
										inModel.Simplified(given[2], Fwd(KDef)),
										"C holds at F, lt and ρ",
										"each coefficient split on has its assigned sign")[1]
									split := inModel.Have(
										"the coefficient g(i, n) is one of those split on",
										"(i, n) ∈ «coefficientIndexes»",
										BySets(
											given[3],
											given[4],
											set_product.InCross.At(
												inModel.TermAs[Set[Nat]]("{j:num | j < m}"),
												inModel.TermAs[Set[Nat]]("{j:num | j < suc(suc(D))}"),
												i,
												n)))
									inModel.Show(
										"so it has its assigned sign",
										By(
											GroupPremises(split, signs.At(inModel.TermAs[Prod[Nat, Nat]]("(i, n)"))),
											pairs.Fst.At(i, n),
											pairs.Snd.At(i, n)))
								}))
							trimmed, trimmedDef := underSigns.LetAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]](
								"g'",
								"λi:num. λn:num. COND(n < suc(suc(D)) ∧ s((i, n)) = &0, integer_polynomial_ring.zero, g(i, n))")
							trimmedCases := underSigns.Have(
								"a coefficient of g' is the zero polynomial where it is dropped and that of g where it is kept",
								"∀i n:num. "+
									"    (n < suc(suc(D)) ∧ s((i, n)) = &0 ⇒ g'(i, n) = integer_polynomial_ring.zero) ∧ "+
									"    (¬(n < suc(suc(D)) ∧ s((i, n)) = &0) ⇒ g'(i, n) = g(i, n))",
								By(trimmedDef))
							dropped := underSigns.Conjuncts(
								GroupPremises(
									over,
									bounded,
									signFixed,
									trimmedCases,
									DropZeroSignCoefficients.At(U, K, m, underSigns.TermAs[Nat]("suc(D)"), s, g, trimmed)),
								"every member of g' is a parameter polynomial",
								"each of no larger degree than the member of g at its index",
								"a member of g' other than the zero polynomial keeps "+
									"the coefficient of g at its degree, of a nonzero sign",
								"in a model meeting K, a member of g' that does not "+
									"specialize to zero keeps its leading coefficient nonzero",
								"a uniform table of g' under K gives one of g")
							trimmedParameters, trimmedDegree, leadingNotDropped, leadingStaysNonzero, toTrimmed :=
								dropped[0], dropped[1], dropped[2], dropped[3], dropped[4]
							trimmedBounded := underSigns.Have(
								"every member of g' has degree at most D + 1",
								"∀i:num. i < m ⇒ polynomial_degree(integer_polynomial_ring.zero, g'(i)) ≤ suc(D)",
								underSigns.ForEach(func(i *Expr[Nat]) Action {
									return ByArith(operations, trimmedDegree.At(i), bounded.At(i))
								}))
							laterLower := underSigns.Have(
								"the members of g' after c have degree below D + 1",
								"∀i:num. i < m ∧ c < i ⇒ polynomial_degree(integer_polynomial_ring.zero, g'(i)) < suc(D)",
								underSigns.ForEach(func(i *Expr[Nat]) Action {
									return ByArith(operations, trimmedDegree.At(i), topFirst.At(i))
								}))
							underSigns.Cases(underSigns.Term("polynomial_degree(integer_polynomial_ring.zero, g'(c)) = suc(D)"))
							underSigns.Otherwise(
								"g'(c) has lost degree D + 1: the members of g' of degree D + 1 come before c",
								func(dropsDegree *Argument, lost Fact) {
									beforeTrimmed := dropsDegree.Have(
										"the members of g' of degree D + 1 come before c",
										"∀i:num. i < m ∧ c ≤ i ⇒ polynomial_degree(integer_polynomial_ring.zero, g'(i)) < suc(D)",
										Derive(func(later *Argument) {
											i := later.FixAs[Nat]("i")
											index := later.Conjuncts(
												later.Assume(),
												"i indexes a member",
												"at c or later")
											later.Cases(later.Term("i = c"))
											later.When(
												"at c the degree is at most D + 1 and not D + 1",
												func(atC *Argument, isC Fact) {
													atC.Show(
														"so below D + 1",
														ByArith(operations, isC, lost, index[0], trimmedBounded.At(i)))
												})
											later.Otherwise(
												"past c, g'(i) is a member after c",
												func(pastC *Argument, notC Fact) {
													pastC.Show(
														"of degree below D + 1",
														ByArith(operations, index[0], index[1], notC, laterLower.At(i)))
												})
										}))
									trimmedTable := dropsDegree.Have(
										"the induction hypothesis at c gives g' a uniform table under K",
										"parametric_sign_table(U, K, m, g')",
										By(before, trimmedParameters, trimmedBounded, beforeTrimmed))
									dropsDegree.Show(
										"hence g has one",
										By(toTrimmed, trimmedTable))
								})
							underSigns.When(
								"g'(c) keeps degree D + 1: lower it through the Cohen–Hörmander family",
								func(keepsDegree *Argument, keptDegree Fact) {
									c := keepsDegree.TermAs[Nat]("c")
									topSplitOn := keepsDegree.Have(
										"the top degree D + 1 is one of the degrees split on",
										"suc(D) < suc(suc(D))",
										ByArith())
									formalNonzero := keepsDegree.Have(
										"of degree D + 1, g'(c) is not the zero polynomial, of degree zero",
										"g'(c) ≠ vec_zero(integer_polynomial_ring.zero)",
										By(
											Normalized,
											keptDegree,
											keepsDegree.Have(
												"the zero polynomial has degree zero",
												"polynomial_degree(integer_polynomial_ring.zero, vec_zero(integer_polynomial_ring.zero)) = 0",
												By(polynomial.DegreeVecZero)),
											keepsDegree.Have(
												"D + 1 is not zero",
												"¬(suc(D) = 0)",
												ByArith())))
									notDroppedAtC := keepsDegree.Conjuncts(
										keepsDegree.Have(
											"so its leading coefficient was not dropped: it is that of g(c), of the nonzero sign s(c, D + 1)",
											"g'(c, suc(D)) = g(c, suc(D)) ∧ ¬(s((c, suc(D))) = &0)",
											By(Normalized, operations, keptDegree, cBelow, formalNonzero, leadingNotDropped.At(c))),
										"the leading coefficient of g'(c) is that of g(c)",
										"the sign s(c, D + 1) is not zero")
									sameLeading, signNonzero := notDroppedAtC[0], notDroppedAtC[1]
									leadSign := keepsDegree.Have(
										"in a model meeting K, the leading coefficient of g'(c) has the sign s(c, D + 1)",
										Statement{
											Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
											Hypotheses: []string{
												"«model»(U, K, F, lt, ρ)",
											},
											Conclusion: "ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, g'(c, suc(D)))) = " +
												"s((c, suc(D)))",
										},
										Derive(func(inModel *Argument) {
											F := inModel.FixAs[FieldOps[A]]("F")
											lt := inModel.FixAs[Fun2[A, A, Bool]]("lt")
											ρ := inModel.FixAs[Fun[Nat, A]]("ρ")
											model := inModel.Assume()
											inModel.Show(
												"g'(c) keeps the leading coefficient of g(c)",
												By(
													Normalized,
													sameLeading,
													GroupPremises(model, cBelow, topSplitOn, signFixed.At(F, lt, ρ, c, inModel.TermAs[Nat]("suc(D)")))))
										}))
									_, lowered := keepsDegree.UnpackAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]](
										GroupPremises(
											cBelow,
											trimmedParameters,
											trimmedBounded,
											laterLower,
											keptDegree,
											signNonzero,
											leadSign,
											leadingStaysNonzero,
											LowerTopDegreeMember.At(
												U, K, m, c, D, keepsDegree.TermAs[Int]("s((c, suc(D)))"), trimmed)),
										"h")
									reduced := keepsDegree.Conjuncts(
										lowered,
										"every member of h is a parameter polynomial",
										"of degree at most D + 1",
										"the members of h of degree D + 1 come before c",
										"a uniform table of h gives one of g'")
									reducedTable := keepsDegree.Have(
										"the induction hypothesis at c gives h a uniform table under K",
										"parametric_sign_table(U, K, m + m, h)",
										By(before, reduced[0], reduced[1], reduced[2]))
									keepsDegree.Show(
										"hence g' and g have one",
										By(toTrimmed, reduced[3], reducedTable))
								})
						}))
					nextTop.Show(
						"split on the signs of the coefficients",
						By(
							finiteCross,
							coefficientsIn,
							perSign,
							parametric_sign_table.SignTableBySigns.At(
								U,
								nextTop.TermAs[Set[Prod[Nat, Nat]]]("«coefficientIndexes»"),
								nextTop.TermAs[Fun2[Prod[Nat, Nat], Fun[Nat, Nat], Int]](
									"λj:prod(num, num). g(fst(j), snd(j))"),
								m,
								g,
								C)))
				})
		})
		return ctx.Theorem(headline, func(a *Argument, U *Expr[Set[Nat]]) {
			operations := a.Have(
				"the integer polynomial ring operates as the polynomial algebra over the integers",
				"integer_polynomial_ring.add = fun_add(int_add) ∧ "+
					"integer_polynomial_ring.zero = fun_zero(int_of_num(0)) ∧ "+
					"integer_polynomial_ring.mul = polynomial_algebra_mul(int_ring) ∧ "+
					"integer_polynomial_ring.one = polynomial_algebra_one(int_ring)",
				Cite(polynomial_formula.IntegerPolynomialRingOperations))
			layered := a.Have(
				"by induction on a degree bound D, then on c: a family of degree at "+
					"most D whose members of degree D come before c has a uniform table",
				Statement{
					Binders: "∀D c:num. " +
						"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
						"∀m:num. " +
						"∀g:(num → num → ((num → num) → int)).",
					Hypotheses: []string{
						"∀i:num. i < m ⇒ «overParameters»(g(i))",
						"∀i:num. i < m ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) ≤ D",
						"∀i:num. i < m ∧ c ≤ i ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) < D",
					},
					Conclusion: "parametric_sign_table(U, C, m, g)",
				},
				Derive(func(onDegree *Argument) {
					onDegree.Induct("D")
					onDegree.Base(
						"at degree zero the family is one of constants",
						func(degreeZero *Argument) {
							degreeZero.FixAs[Nat]("c")
							C := degreeZero.FixAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]]("C")
							m := degreeZero.FixAs[Nat]("m")
							g := degreeZero.FixAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]]("g")
							given := degreeZero.Conjuncts(
								degreeZero.Assume(),
								"every member is a parameter polynomial",
								"of degree zero",
								"none of degree below zero")
							constants := degreeZero.Have(
								"each constant term is a parameter polynomial",
								"∀i:num. i < m ⇒ g(i, 0) ∈ polynomial_algebra(int_ring, U)",
								Derive(func(e *Argument) {
									i := e.FixAs[Nat]("i")
									below := e.Assume()
									e.Show(
										"a coefficient of a parameter polynomial",
										By(polynomial.CoefficientIn.Read(e.Simplified(GroupPremises(below, given[0].At(i)))).At(
											e.TermAs[Nat]("0"))))
								}))
							vanishing := degreeZero.Have(
								"past the constant term every coefficient is zero",
								"∀i n:num. i < m ∧ 0 < n ⇒ g(i, n) = integer_polynomial_ring.zero",
								Derive(func(e *Argument) {
									e.FixAs[Nat]("i")
									e.FixAs[Nat]("n")
									index := e.Conjuncts(
										e.Assume(),
										"i indexes a member",
										"n is positive")
									constant := e.Have(
										"g(i) has degree zero",
										"polynomial_degree(integer_polynomial_ring.zero, g(i)) = 0",
										ByArith(e.Have(
											"g(i) has degree at most zero",
											"polynomial_degree(integer_polynomial_ring.zero, g(i)) ≤ 0",
											By(index[0], given[1]))))
									vanishes := e.Have(
										"so g(i) vanishes from 1 on",
										"vec⟨suc(0)⟩(integer_polynomial_ring.zero, g(i))",
										By(constant, index[0], given[0], polynomial.DegreeVec))
									e.Show(
										"in particular at n",
										By(
											vanishes,
											index[1],
											vec_space.VecDef,
											e.Have(
												"n is at least 1",
												"suc(0) ≤ n",
												ByArith(index[1]))))
								}))
							degreeZero.Show(
								"a family of constants has a uniform table",
								By(operations, constants, vanishing, parametric_sign_table.ConstantFamilySignTable.At(U, C, m, g)))
						})
					onDegree.Step(
						"from degree D to degree D + 1",
						func(nextDegree *Argument, lower Fact) {
							nextDegree.Show(
								"the statement at degree D gives the one at degree D + 1, by induction on c",
								By(lower, At(degreeStep, U, nextDegree.TermAs[Nat]("D"))))
						})
				}))
			C := a.FixAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]]("C")
			m := a.FixAs[Nat]("m")
			g := a.FixAs[Fun3[Nat, Nat, Fun[Nat, Nat], Int]]("g")
			over := a.Assume()
			D, held := a.ObtainAs[Nat](
				"the degrees of the members are finitely many, so some D bounds them",
				"∃D:num. «degrees» ⊆ 0 .. D",
				By(
					num_segment.FiniteIffBounded.At(a.TermAs[Set[Nat]]("«degrees»")),
					finite_set.FiniteImage.At(
						a.TermAs[Fun[Nat, Nat]]("λi:num. polynomial_degree(integer_polynomial_ring.zero, g(i))"),
						a.TermAs[Set[Nat]]("{i:num | i < m}")),
					num_segment.FiniteBelowStrict.At(m)),
				Named("D"))
			degrees := a.Have(
				"so every member's degree lies in 0 .. D: it is at most D",
				"∀i:num. i < m ⇒ polynomial_degree(integer_polynomial_ring.zero, g(i)) ≤ D",
				held.Simp(Fwd(set_image.ImageSubsetIff), Fwd(num_segment.MembershipFromZero)),
				By(held))
			a.Show(
				"the layered statement at the bound D, every index allowed",
				ByArith(layered.At(D, m, C, m, g), over, degrees, At(noIndexPast, m, m, g, D)))
		})
	}),
})}
