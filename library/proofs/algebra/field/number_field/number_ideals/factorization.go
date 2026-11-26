// factorization.go — ideal factorization in the ring of integers of a
// number field: every nonzero ideal is invertible and factors uniquely into
// prime ideals, and a fractional ideal is invertible exactly when it is
// bounded.

package number_ideals

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// NumberRingFactorization — nonzero ideals of a number ring are invertible and
// have unique prime ideal exponents: finite quotients and integral closedness
// supply the hypotheses of the shared maximal ideal factorization theorems.
var NumberRingFactorization = numberRingFactorizationThm{family.Add(registry.ProofEntry{
	Name: "NumberRingFactorization",
	Key:  "prop_95c913e5fde368f8",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀I:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"ring_ideal(«R», I)",
			"I ≠ {L.zero}",
		},
		Conclusion: "invertible_fractional(field_ring(L), «O», I) ∧ " +
			"(∃v:(set(A) → num). " +
			"    «PrimeFactorization»(v) ∧ (∀w:(set(A) → num). «PrimeFactorization»(w) ⇒ v = w))",
		Abbrev: Abbrev{
			{Name: "PrimeFactorization", Text: "λv:(set(A) → num). " +
				"    finite(fun_support(0, v)) ∧ " +
				"    (∀m:set(A). v(m) ≠ 0 ⇒ prime_ideal(«R», m) ∧ m ≠ {L.zero}) ∧ " +
				"    I = ideal_exponent_product(«R», v)"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], I *Expr[Set[A]], given Fact) {
		integers := a.TermAs[Set[A]]("«O»")
		ring := a.TermAs[module_record.RingOps[A]]("«R»")
		subring := a.Have(
			"the algebraic integers form a subring of the number field",
			"subring(field_ring(L), «O»)",
			By(given, integral_closure.IntegralClosureSubring.Read(L)))
		integerRing := a.Have(
			"so the integer ring is commutative",
			"comm_ring_on(«R»)",
			By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(integers)))
		closed := a.Have(
			"the integer ring is integrally closed in the field",
			"integrally_closed_in(«R», L.carrier)",
			By(given, integral_closure.IntegralClosureIntegrallyClosed.Read(L)))
		finiteQuotients := a.Have(
			"every nonzero ideal has finite quotient",
			"∀H:set(A). ring_ideal(«R», H) ∧ H ≠ {L.zero} ⇒ finite(left_cosets(L.add, «O», H))",
			Derive(func(b *Argument) {
				H := b.FixAs[Set[A]]()
				nonzero := b.Assume()
				b.Show(
					"finite index gives the finite quotient",
					By(given, nonzero, ring_of_integers.NonzeroIdealFiniteIndex.Read(L).At(H)))
			}))
		finiteHeights := a.Have(
			"every nonzero ideal has finite height",
			"∀H:set(A). ring_ideal(«R», H) ∧ H ≠ {L.zero} ⇒ finite_ideal_height(«R», H)",
			Derive(func(b *Argument) {
				H := b.FixAs[Set[A]]()
				nonzero := b.Assume()
				b.Show(
					"finite quotient bounds the ideal height",
					By(
						integerRing,
						nonzero,
						finiteQuotients.At(H),
						ideal_factorization.FiniteQuotientIdealHeight.At(ring, H)))
			}))
		maximalInvertible := a.Have(
			"every nonzero maximal ideal is invertible",
			"∀m:set(A). maximal_ideal(«R», m) ∧ m ≠ {L.zero} ⇒ invertible_fractional(field_ring(L), «O», m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]()
				nonzero := b.Assume()
				b.Show(
					"integral closedness and finite quotients give the inverse",
					By(
						subring,
						closed,
						nonzero,
						finiteQuotients,
						ideal_factorization.NonzeroMaximalInvertible.Read(L).At(integers, m)))
			}))
		invertible := a.Have(
			"finite height extends invertibility to the given ideal",
			"invertible_fractional(field_ring(L), «O», I)",
			By(
				subring,
				given,
				finiteHeights,
				maximalInvertible,
				ideal_factorization.NonzeroIdealInvertible.Read(L).At(integers, I)))
		containingNonzero := a.Have(
			"a maximal ideal containing the given nonzero ideal is nonzero",
			"∀m:set(A). maximal_ideal(«R», m) ∧ I ⊆ m ⇒ m ≠ {L.zero}",
			Derive(func(b *Argument) {
				b.FixAs[Set[A]]()
				contains := b.Assume()
				zeroIn := b.Have(
					"the ideal contains zero",
					"L.zero ∈ I",
					By(given, ring_ideal.IdealZero.At(ring, I)))
				b.Show(
					"containment in the zero ideal would make I the zero ideal",
					BySets(zeroIn, given, contains))
			}))
		containingInvertible := a.Have(
			"every maximal ideal above I is invertible",
			"∀m:set(A). maximal_ideal(«R», m) ∧ I ⊆ m ⇒ invertible_fractional(field_ring(L), «O», m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]()
				contains := b.Assume()
				b.Show(
					"apply invertibility to the nonzero maximal ideal",
					By(contains, containingNonzero.At(m), maximalInvertible.At(m)))
			}))
		v, factorization := a.ObtainAs[Fun[Set[A], Nat]](
			"factor I into invertible nonzero maximal ideals",
			"∃v:(set(A) → num). "+
				"    finite(fun_support(0, v)) ∧ "+
				"    (∀m:set(A). "+
				"        v(m) ≠ 0 ⇒ "+
				"        maximal_ideal(«R», m) ∧ m ≠ {L.zero} ∧ invertible_fractional(field_ring(L), «O», m)) ∧ "+
				"    I = ideal_exponent_product(«R», v)",
			By(
				given,
				subring,
				finiteHeights.At(I),
				containingInvertible,
				ideal_factorization.IdealFactorizationExists.Read(L).At(integers, I)),
			Named("v"))
		factors := a.Conjuncts(
			factorization,
			"the factorization has finite support",
			"the supported factors are invertible nonzero maximal ideals",
			"their product is I")
		primeFactors := a.Have(
			"the supported maximal ideals are nonzero prime ideals",
			"∀m:set(A). v(m) ≠ 0 ⇒ prime_ideal(«R», m) ∧ m ≠ {L.zero}",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]()
				active := b.Assume()
				b.Show(
					"a maximal ideal of this commutative ring is prime",
					By(active, factors[1].At(m), ring_ideal.MaximalIsPrime.Read(integerRing).At(m)))
			}))
		primeMaximal := a.Have(
			"a nonzero prime of the integer ring is maximal and invertible",
			Statement{
				Binders: "∀m:set(A).",
				Hypotheses: []string{
					"prime_ideal(«R», m)",
					"m ≠ {L.zero}",
				},
				Conclusion: "maximal_ideal(«R», m) ∧ invertible_fractional(field_ring(L), «O», m)",
			},
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]()
				nonzeroPrime := b.Assume()
				finiteIndex := b.Have(
					"m has finite index, being a nonzero ideal",
					"finite(left_cosets(L.add, «O», m))",
					By(nonzeroPrime, ring_ideal.PrimeIdealIdeal.At(ring, m), finiteQuotients.At(m)))
				maximal := b.Have(
					"a prime of finite index is maximal",
					"maximal_ideal(«R», m)",
					By(integerRing, nonzeroPrime, finiteIndex, quotient_ring.FiniteIndexPrimeMaximal.At(ring, m)))
				b.Show(
					"the nonzero maximal ideal is invertible",
					By(maximal, nonzeroPrime, maximalInvertible.At(m)))
			}))
		a.Show(
			"invertibility and the unique prime ideal factorization",
			SplitConj(
				Case(
					"the nonzero ideal is invertible",
					By(invertible)),
				Case(
					"the maximal factorization gives the required prime factorization",
					Derive(func(b *Argument) {
						b.Take(v)
						b.Show(
							"the finite prime factorization has unique exponents",
							SplitConjAll(
								Case(
									"only finitely many prime exponents are nonzero",
									By(factors[0])),
								Case(
									"the support consists of nonzero prime ideals",
									By(primeFactors)),
								Case(
									"the exponent product recovers I",
									By(factors[2])),
								Case(
									"any other prime factorization has the same exponents",
									Derive(func(c *Argument) {
										w := c.FixAs[Fun[Set[A], Nat]]("w")
										other := c.Assume()
										competitor := c.Conjuncts(
											other,
											"the competing support is finite",
											"its factors are nonzero prime ideals",
											"its product is I")
										maximalFactors := c.Have(
											"the competing primes are invertible maximal ideals",
											"∀m:set(A). w(m) ≠ 0 ⇒ maximal_ideal(«R», m) ∧ invertible_fractional(field_ring(L), «O», m)",
											By(competitor[1], primeMaximal))
										sameProduct := c.Have(
											"both exponent products equal I",
											"ideal_exponent_product(«R», v) = ideal_exponent_product(«R», w)",
											CalcEq(Leg(
												I,
												"the chosen factorization is I",
												By(Normalized, factors[2])), FinalLeg(
												"the competing factorization is I",
												By(competitor[2]))))
										c.Show(
											"uniqueness for invertible maximal factors identifies the exponents",
											By(
												subring,
												factors[0],
												competitor[0],
												factors[1],
												maximalFactors,
												sameProduct,
												ideal_factorization.IdealFactorizationUnique.Read(L).At(integers, v, w)))
									})),
							))
					})),
			))
	}),
})}

// NumberFractionalIdeals — fractional ideals of a number ring are invertible
// exactly when they are bounded: apply the general criterion using invertibility
// of nonzero integral ideals and the number field as the fraction field.
var NumberFractionalIdeals = numberFractionalIdealsThm{family.Add(registry.ProofEntry{
	Name: "NumberFractionalIdeals",
	Key:  "prop_606a63322d745670",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀I:set(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "invertible_fractional(field_ring(L), «O», I) ⇔ " +
			"bounded_fractional(field_ring(L), «O», I)",
	}, func(a *Argument, L field.FieldFact[on.L], I *Expr[Set[A]], numberField Fact) {
		integers := a.TermAs[Set[A]]("«O»")
		invertible := a.Have(
			"every nonzero integral ideal of the number ring is invertible",
			"∀H:set(A). ring_ideal(«R», H) ∧ H ≠ {L.zero} ⇒ invertible_fractional(field_ring(L), «O», H)",
			a.ForEach(func(H *Expr[Set[A]]) Action {
				return By(numberField, NumberRingFactorization.Read(L).At(H))
			}))
		a.Show(
			"the bounded fractional-ideal criterion applies to the integer ring",
			By(
				integral_closure.IntegralClosureSubring.Read(L),
				ring_of_integers.RingOfIntegersFractionField.Read(L),
				numberField,
				invertible,
				ideal_factorization.FractionalIdealInvertibleIffBounded.Read(L).At(integers, I)))
	}),
})}
