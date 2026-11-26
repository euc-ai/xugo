// separable.go — splitting and separability: a field's irreducible factors
// and the roots of a polynomial that splits, and the exact root count of a
// separable one; and the value of the derivative at one of two distinct
// roots, a multiple of their difference.

package separable_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
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
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Splitting and separability
// ---------------------------------------------------------------------------

// SplitsDivisor — a divisor of a polynomial that splits splits:
// each irreducible factor of the divisor also divides the polynomial.
var SplitsDivisor = splitsDivisorThm{family.Add(registry.ProofEntry{
	Name: "SplitsDivisor",
	Key:  "prop_fd53170a578b13f7",
	Reading: "p need not be stated over R.carrier: an irreducible " +
		"factor r with p = r * s, s over R.carrier, already puts p over c.",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_divides(R, p, q)",
			"polynomial_splits(R, q)",
		},
		Conclusion: "polynomial_splits(R, p)",
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], divides, splits Fact) {
		splitting := a.Unfolded(splits, PolynomialSplitsDef)
		a.Do(Simp(Fwd(PolynomialSplitsDef)))
		r := a.FixAs[Fun[Nat, A]]("r")
		factor := a.Assume()
		parts := a.Conjuncts(
			factor,
			"r is irreducible",
			"r divides p")
		irreducible, dividesP := parts[0], parts[1]
		dividesQ := a.Have(
			"r divides q by transitivity through p",
			"polynomial_divides(R, r, q)",
			By(
				irreducible,
				polynomial_division.PolynomialIrreducibleDef.At(a.TermAs[RingOps[A]]("R"), r),
				dividesP,
				divides,
				polynomial_division.DividesTrans.Read(ring).At(r, p, q)))
		a.Show(
			"the irreducible factor r is linear because q splits",
			By(splitting.At(r), irreducible, dividesQ))
	}),
})}

// SplitsRoot — over a field a polynomial of positive degree that splits
// has a root. An irreducible divisor is linear, so its nonzero leading
// coefficient gives a root by field inversion; a root of a factor is a
// root of the product.
var SplitsRoot = splitsRootThm{family.Add(registry.ProofEntry{
	Name: "SplitsRoot",
	Key:  "prop_c476dc60d271a8fa",
	Reading: "Positive degree is load-bearing: a nonzero constant " +
		"splits, having no irreducible factor, and has no root.",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"0 < polynomial_degree(p)",
			"polynomial_splits(field_ring(F), p)",
		},
		Conclusion: "∃a:A. a ∈ F.carrier ∧ polynomial_eval(p, a) = F.zero",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p *Arrow[Nat, A], hypotheses Fact) {
			ring := field.RingOn.Read(fieldOn)
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			zero, carrier := a.TermAs[A]("F.zero"), a.TermAs[Set[A]]("F.carrier")
			zeroth, first := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(F)")
			q, divisor := a.UnpackAs[Fun[Nat, A]](
				GroupPremises(hypotheses, polynomial_division.IrreducibleFactorExists.Read(fieldOn).At(p)), "q")
			divisorParts := a.Conjuncts(
				divisor,
				"q is irreducible",
				"q divides p")
			qOver := a.Have(
				"the irreducible divisor is a polynomial over the field",
				"polynomial_over(F.carrier, q)",
				By(divisor, polynomial_division.PolynomialIrreducibleDef.At(fieldRing, q)))
			coefficients := a.Have(
				"all coefficients of q lie in the field",
				"∀i:num. q(i) ∈ F.carrier",
				By(qOver, polynomial.PolynomialOverDef.At(zero, carrier, q)))
			linearForm := a.Have(
				"splitting makes the irreducible divisor q linear: q(x) is q(0) + q(1) * x, with q(1) nonzero",
				"q(1) ≠ F.zero ∧ ∀x:A. x ∈ F.carrier ⇒ polynomial_eval(q, x) = q(0) + q(1) * x",
				Derive(func(b *Argument) {
					degreeOne := b.Have(
						"splitting makes the irreducible divisor q of degree one",
						"polynomial_degree(q) = 1",
						By(divisor, hypotheses, PolynomialSplitsDef.At(fieldRing, p)))
					qNonzero := b.Have(
						"a polynomial of degree one is not zero",
						"q ≠ vec_zero",
						Derive(func(c *Argument) {
							positive := c.Have(
								"degree one is not degree zero",
								"polynomial_degree(q) ≠ 0",
								ByArith(degreeOne))
							c.Show(
								"the zero polynomial has degree zero",
								By(Normalized, positive, polynomial.DegreeVecZero.At(zero)))
						}))
					firstNonzero := b.Have(
						"q's coefficient at its degree one is nonzero",
						"q(1) ≠ F.zero",
						By(Normalized, qOver, qNonzero, degreeOne, polynomial.DegreeLeading.At(zero, carrier, q)))
					short := b.Have(
						"q vanishes from the index after one on",
						"vec⟨suc(1)⟩(q)",
						By(Normalized, qOver, degreeOne, polynomial.DegreeVec.At(zero, carrier, q)))
					b.Show(
						"q(1) is nonzero, and q, vanishing from two on, takes the value q(0) + q(1) * x",
						By(firstNonzero, qOver, short, polynomial_evaluation.EvalVecTwo.Read(ring)))
				}))
			linearParts := a.Conjuncts(
				linearForm,
				"q's coefficient at one is nonzero",
				"and q(x) is q(0) + q(1) * x at every x of the field")
			leadingNonzero, values := linearParts[0], linearParts[1]
			constant := a.MemberOf[on.F](a.TermAs[A]("q(0)"), coefficients.At(zeroth))
			leading := a.MemberOf[on.F](a.TermAs[A]("q(1)"), coefficients.At(first))
			inverse := field.InvIn.Read(fieldOn).At(leading)
			product := comm_ring.MulIn.Read(ring).At(inverse, constant)
			negative := comm_ring.NegIn.Read(ring).At(product)
			root, rootDef := a.LetAs[A]("root", "-(F.inv(q(1)) * q(0))")
			rootIn := a.Have(
				"the inverse, product and negation defining root stay in the field",
				"root ∈ F.carrier",
				By(rootDef, negative))
			rootMember := a.MemberOf[on.F](root, rootIn)
			qRoot := a.Have(
				"root = −q(1)⁻¹ · q(0) is a root of q",
				"polynomial_eval(q, root) = F.zero",
				Derive(func(b *Argument) {
					cancellation := b.Have(
						"the chosen root cancels the two linear terms",
						"q(0) + q(1) * root = F.zero",
						rootDef.Rw(),
						Simp(
							Fwd(coefficients),
							Fwd(field.InvIn.Read(fieldOn)),
							Fwd(comm_ring.MulIn.Read(ring)),
							Fwd(comm_ring.MulRightNegOn.Read(ring)),
							Fwd(comm_monoid.AssocOn.Read(multiplicative)),
							Fwd(field.MulRightInverseOn.Read(fieldOn)),
							Fwd(leadingNonzero),
							Fwd(comm_monoid.LeftIdentityOn.Read(multiplicative))),
						By(coefficients.At(zeroth), group.RightInverseOn.Read(additive)))
					b.Show(
						"the value of q at root is q(0) + q(1) * root",
						By(rootMember, cancellation, values.At(root)))
				}))
			r, factor := a.UnpackAs[Fun[Nat, A]](
				a.Unfolded(divisorParts[1], polynomial_division.PolynomialDividesDef), "r")
			a.Take(root)
			a.Show(
				"a root of the divisor q is a root of p",
				By(
					Normalized,
					rootIn,
					factor,
					qOver,
					qRoot,
					polynomial_evaluation.EvalMulRoot.Read(ring).At(q, r, rootMember)))
		}),
})}

// SplitsMono — a nonzero polynomial over a subfield that splits over it
// splits over the field.
var SplitsMono = splitsMonoThm{family.Add(registry.ProofEntry{
	Name: "SplitsMono",
	Key:  "prop_97d7ad24e02f8b1d",
	Reading: "p nonzero is load-bearing: the zero polynomial splits over an algebraically closed " +
		"subfield, and over a larger field with an irreducible polynomial of degree two it does not.",
	Deps: []registry.EntryLike{
		PolynomialSplitsDef,
		polynomial_division.IrreducibleFactorExists,
		polynomial_division.IrreducibleDividesProduct,
		polynomial_roots.FactorTheorem,
		polynomial_division.DividesDegree,
		polynomial.DegreeMul,
		integral_domain.FieldIntegralDomain,
		polynomial.PolynomialOverMono,
		field.SubfieldFieldOn,
		field.SubfieldSubset,
	},
	Build: family.Card(field.FieldOn.Statement(Statement{
		Binders: "∀K:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(F, K)",
			"polynomial_over(K, p)",
			"¬(p = vec_zero)",
			"polynomial_splits(restrict_ring(field_ring(F), K), p)",
		},
		Conclusion: "polynomial_splits(field_ring(F), p)",
	}),
		"by induction on the degree, p is a constant times a product of factors x - a with a in "+
			"K (IrreducibleFactorExists over K, each irreducible factor linear, FactorTheorem); an "+
			"irreducible factor over c divides one of the linear factors "+
			"(IrreducibleDividesProduct), so has degree at most F.one (DividesDegree) and exactly one"),
})}

// SplitsMul — over a field a product of polynomials that split splits: an
// irreducible divisor of the product divides one of the two factors
// (polynomial_division.IrreducibleDividesProduct), and so has degree one.
var SplitsMul = splitsMulThm{family.Add(registry.ProofEntry{
	Name: "SplitsMul",
	Key:  "prop_31c1cbf83467eb48",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_over(F.carrier, q)",
			"polynomial_splits(field_ring(F), p)",
			"polynomial_splits(field_ring(F), q)",
		},
		Conclusion: "polynomial_splits(field_ring(F), polynomial_mul(p, q))",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p, q *Arrow[Nat, A], hypotheses Fact) {
			a.Do(Simp(Fwd(PolynomialSplitsDef)))
			r := a.FixAs[Fun[Nat, A]]("r")
			divisor := a.Assume()
			a.Show(
				"an irreducible divisor divides a factor and has degree one",
				By(
					divisor,
					hypotheses,
					polynomial_division.IrreducibleDividesProduct.Read(fieldOn).At(r, p, q),
					PolynomialSplitsDef))
		}),
})}

// SeparableDivisor — a divisor of a separable polynomial is separable:
// the product rule regroups a Bézout identity for the multiple into one
// for the divisor and its derivative.
var SeparableDivisor = separableDivisorThm{family.Add(registry.ProofEntry{
	Name: "SeparableDivisor",
	Key:  "prop_1d9536e1bdd28cf7",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_divides(R, p, q)",
			"polynomial_separable(R, q)",
		},
		Conclusion: "polynomial_separable(R, p)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], hypotheses Fact) {
			R := a.TermAs[RingOps[A]]("R")
			given := a.Conjuncts(
				hypotheses,
				"p is over the carrier",
				"p divides q",
				"q is separable")
			r, factorization := a.UnpackAs[Fun[Nat, A]](
				a.Unfolded(given[1], polynomial_division.PolynomialDividesDef), "r")
			u, v, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(given[2], PolynomialSeparableDef), "u", "v")
			rDerivative := a.Have(
				"the derivative of r is over the carrier",
				"polynomial_over(R.carrier, polynomial_derivative(r))",
				By(factorization, polynomial.DerivativeOverCarrier.Read(ring).At(r)))
			factorCoefficients := a.Have(
				"every coefficient of p and of r lies in the carrier",
				"∀i:num. p(i) ∈ R.carrier ∧ r(i) ∈ R.carrier",
				By(given[0], factorization, polynomial.PolynomialOverDef))
			productRule := a.Have(
				"differentiate the factorization of q",
				"polynomial_derivative(q) = "+
					"polynomial_mul(polynomial_derivative(p), r) + polynomial_mul(p, polynomial_derivative(r))",
				By(factorCoefficients, factorization, polynomial.DerivativeMul.Read(ring).At(p, r)))
			polynomialRing := polynomial.PolynomialRingOn.Read(ring)
			pDerivative := a.Have(
				"the derivative of p is over the carrier",
				"polynomial_over(R.carrier, polynomial_derivative(p))",
				By(hypotheses, polynomial.DerivativeOverCarrier.Read(ring).At(p)))
			_, dpDef := a.LetAs[Fun[Nat, A]]("dp", "polynomial_derivative(p)")
			dr, _ := a.LetAs[Fun[Nat, A]]("dr", "polynomial_derivative(r)")
			U, UDef := a.LetAs[Fun[Nat, A]]("U", "polynomial_mul(u, r) + polynomial_mul(v, dr)")
			V, VDef := a.LetAs[Fun[Nat, A]]("V", "polynomial_mul(v, r)")
			atoms := a.Have(
				"p, r, u, v and the two derivatives belong to the polynomial ring",
				"p ∈ «polynomialRingCarrier» ∧ "+
					"r ∈ «polynomialRingCarrier» ∧ "+
					"u ∈ «polynomialRingCarrier» ∧ "+
					"v ∈ «polynomialRingCarrier» ∧ "+
					"dp ∈ «polynomialRingCarrier» ∧ "+
					"dr ∈ «polynomialRingCarrier»",
				By(hypotheses, bezout, factorization, pDerivative, rDerivative))
			coefficients := a.Have(
				"U and V are polynomials over the carrier",
				"polynomial_over(R.carrier, U) ∧ polynomial_over(R.carrier, V)",
				By(
					UDef,
					VDef,
					bezout,
					factorization,
					rDerivative,
					polynomial.PolynomialMulOver.Read(ring).At(u, r),
					polynomial.PolynomialMulOver.Read(ring).At(v, dr),
					polynomial.PolynomialMulOver.Read(ring).At(v, r),
					comm_ring.AddIn.Read(polynomialRing).AsFact().At(
						a.TermAs[Fun[Nat, A]]("polynomial_mul(u, r)"),
						a.TermAs[Fun[Nat, A]]("polynomial_mul(v, dr)")),
					polynomial.PolynomialRingDef.At(R)))
			identity := a.Have(
				"U and V give a Bézout identity for p and its derivative",
				"polynomial_mul(U, p) + polynomial_mul(V, dp) = basis_vector(0)",
				CalcEq(
					Leg(
						a.TermAs[Fun[Nat, A]](
							"polynomial_mul(u, polynomial_mul(p, r)) + "+
								"polynomial_mul(v, polynomial_mul(dp, r) + polynomial_mul(p, dr))"),
						"distribute and regroup the new coefficients",
						Simp(Fwd(UDef), Fwd(VDef)),
						ByArith(polynomialRing, atoms)),
					Leg(
						a.TermAs[Fun[Nat, A]]("polynomial_mul(u, q) + polynomial_mul(v, polynomial_derivative(q))"),
						"the factorization and product rule recover q and its derivative",
						By(productRule, factorization)),
					FinalLeg(
						"the original Bézout identity is the one polynomial",
						By(bezout))))
			a.Do(Simp(Fwd(PolynomialSeparableDef)))
			a.Take(U)
			a.Take(V)
			a.Show(
				"these coefficients prove p separable",
				By(Normalized, dpDef, identity, coefficients))
		}),
})}

// SeparableMul — a product of coprime separable polynomials is separable:
// each factor is coprime to the product derivative, by the product rule
// and a Bézout identity preserved when a multiple of that factor is added.
var SeparableMul = separableMulThm{family.Add(registry.ProofEntry{
	Name: "SeparableMul",
	Key:  "prop_951e394eac82f756",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_separable(R, p)",
			"polynomial_separable(R, q)",
			"polynomial_coprime(R, p, q)",
		},
		Conclusion: "polynomial_separable(R, polynomial_mul(p, q))",
		Abbrev: Abbrev{
			{Name: "productDerivative", Text: "λp:(num → A). λq:(num → A). " +
				"    polynomial_derivative(polynomial_mul(p, q))"},
			{Name: "derivativeTerm", Text: "λp:(num → A). λq:(num → A). " +
				"    polynomial_mul(polynomial_derivative(p), q)"},
			{Name: "derivativeSum", Text: "λp:(num → A). λq:(num → A). " +
				"    «derivativeTerm»(p, q) + polynomial_mul(p, polynomial_derivative(q))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		factorDerivative := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀p q:(num → A).",
			Hypotheses: []string{
				"polynomial_over(R.carrier, p)",
				"polynomial_over(R.carrier, q)",
				"polynomial_separable(R, p)",
				"polynomial_coprime(R, p, q)",
			},
			Conclusion: "polynomial_coprime(R, p, «productDerivative»(p, q))",
		}, func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], hypotheses Fact) {
			R := a.TermAs[RingOps[A]]("R")
			dp, dq :=
				a.TermAs[Fun[Nat, A]]("polynomial_derivative(p)"), a.TermAs[Fun[Nat, A]]("polynomial_derivative(q)")
			derivatives := a.Have(
				"both derivatives are polynomials over the carrier",
				"polynomial_over(R.carrier, polynomial_derivative(p)) ∧ "+
					"polynomial_over(R.carrier, polynomial_derivative(q))",
				By(
					hypotheses,
					polynomial.DerivativeOverCarrier.Read(ring).At(p),
					polynomial.DerivativeOverCarrier.Read(ring).At(q)))
			reversed := a.Have(
				"the derivative and the other factor are each coprime to p",
				"polynomial_coprime(R, polynomial_derivative(p), p) ∧ polynomial_coprime(R, q, p)",
				By(
					hypotheses,
					derivatives,
					SeparableCoprime.At(R, p),
					polynomial_division.CoprimeSymm.Read(ring).At(p, dp),
					polynomial_division.CoprimeSymm.Read(ring).At(p, q)))
			product := a.Have(
				"the product of the derivative and the other factor is over the carrier and coprime to p",
				"polynomial_over(R.carrier, «derivativeTerm»(p, q)) ∧ "+
					"polynomial_coprime(R, «derivativeTerm»(p, q), p)",
				By(
					hypotheses,
					reversed,
					derivatives,
					polynomial.PolynomialMulOver.Read(ring).At(dp, q),
					polynomial_division.CoprimeMul.Read(ring).At(dp, q, p)))
			crossTerm := a.TermAs[Fun[Nat, A]]("«derivativeTerm»(p, q)")
			coprime := a.Have(
				"p is coprime to the first term of the product rule",
				"polynomial_coprime(R, p, «derivativeTerm»(p, q))",
				By(hypotheses, product, polynomial_division.CoprimeSymm.Read(ring).At(crossTerm, p)))
			sum := a.Have(
				"adding the second product-rule term preserves coprimality with p",
				"polynomial_coprime(R, p, «derivativeSum»(p, q))",
				By(
					hypotheses,
					derivatives,
					product,
					coprime,
					polynomial_division.CoprimeAddMultiple.Read(ring).At(p, crossTerm, dq)))
			productRule := a.Have(
				"the derivative of the product is the sum of its two product-rule terms",
				"«productDerivative»(p, q) = «derivativeSum»(p, q)",
				By(hypotheses, polynomial.PolynomialOverDef, polynomial.DerivativeMul.Read(ring).At(p, q)))
			a.Show(
				"p is coprime to the product derivative",
				By(productRule, sum))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p, q *Arrow[Nat, A],
			hypotheses Fact,
		) {
			R := a.TermAs[RingOps[A]]("R")
			pCoprime := a.Have(
				"the first factor is coprime to the product derivative",
				"polynomial_coprime(R, p, «productDerivative»(p, q))",
				By(ring, hypotheses, At(factorDerivative, R, p, q)))
			qCoprimeReversed := a.Have(
				"the second factor, separable and coprime to the first, "+
					"is coprime to the derivative of the reversed product",
				"polynomial_coprime(R, q, «productDerivative»(q, p))",
				By(
					ring,
					hypotheses,
					polynomial_division.CoprimeSymm.Read(ring).At(p, q),
					At(factorDerivative, R, q, p)))
			qCoprime := a.Have(
				"reversing the factors preserves their product, so the "+
					"second factor is coprime to the same product derivative",
				"polynomial_coprime(R, q, «productDerivative»(p, q))",
				By(
					hypotheses,
					polynomial.PolynomialOverDef,
					polynomial.PolynomialMulComm.Read(ring).At(q, p),
					qCoprimeReversed))
			derivative := a.Have(
				"the product derivative is a polynomial over the carrier",
				"polynomial_over(R.carrier, «productDerivative»(p, q))",
				By(
					hypotheses,
					polynomial.PolynomialMulOver.Read(ring).At(p, q),
					polynomial.DerivativeOverCarrier.Read(ring).At(a.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)"))))
			coprime := a.Have(
				"the product is coprime to its derivative",
				"polynomial_coprime(R, polynomial_mul(p, q), «productDerivative»(p, q))",
				By(
					hypotheses,
					pCoprime,
					qCoprime,
					derivative,
					polynomial_division.CoprimeMul.Read(ring).At(
						p, q, a.TermAs[Fun[Nat, A]]("«productDerivative»(p, q)"))))
			a.Show(
				"a product coprime to its derivative is separable",
				By(coprime, SeparableCoprime.At(R, a.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)"))))
		})
	}),
})}

// SeparableMono — a polynomial separable over a subset of the ring's
// carrier is separable over the ring: separability is coprimality with the
// derivative, the restriction keeps R's operations and so the derivative,
// and coprimality passes to the larger carrier.
var SeparableMono = separableMonoThm{family.Add(registry.ProofEntry{
	Name: "SeparableMono",
	Key:  "prop_21b66cb7cbbe3efa",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀K:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"K ⊆ R.carrier",
			"polynomial_separable(restrict_ring(R, K), p)",
		},
		Conclusion: "polynomial_separable(R, p)",
	},
		func(a *Argument, R *Expr[RingOps[A]], K *Expr[Set[A]], p *Arrow[Nat, A], hypotheses Fact) {
			derivative := a.TermAs[Fun[Nat, A]]("polynomial_derivative(p)")
			a.Show(
				"coprime to its derivative over K, p is coprime to it over R, hence separable over R",
				By(
					hypotheses,
					SeparableCoprime.At(a.TermAs[RingOps[A]]("restrict_ring(R, K)"), p),
					polynomial_division.CoprimeMono.At(R, K, p, derivative),
					SeparableCoprime.At(R, p)))
		}),
})}

// SeparableCoefficientMap — moving coefficients along a ring homomorphism f
// keeps a polynomial separable: the identity u p + v p′ = 1 that witnesses
// separability maps coefficient by coefficient to (fu)(fp) + (fv)(fp)′ = 1,
// the coefficient map being a homomorphism of polynomial rings
// (CoefficientMapHomomorphism) that commutes with the derivative
// (CoefficientMapDerivative).
var SeparableCoefficientMap = separableCoefficientMapThm{family.Add(registry.ProofEntry{
	Name: "SeparableCoefficientMap",
	Key:  "prop_806cfe5564051da5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀p:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"polynomial_over(R.carrier, p)",
			"polynomial_separable(R, p)",
		},
		Conclusion: "polynomial_separable(S, λi:num. f(p(i)))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		f *Arrow[A, B],
		p *Arrow[Nat, A],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		pOver, isSeparable Fact,
	) {
		source := ring_homomorphism.Source.Read(hom)
		u, v, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
			a.Unfolded(isSeparable, PolynomialSeparableDef), "u", "v")
		d, dDef := a.LetAs[Fun[Nat, A]]("d", "polynomial_derivative(p)")
		U, UDef := a.LetAs[Fun[Nat, A]]("U", "polynomial_mul(u, p)")
		V, VDef := a.LetAs[Fun[Nat, A]]("V", "polynomial_mul(v, d)")
		_, CDef := a.LetAs[Fun[Fun[Nat, A], Fun[Nat, B]]]("C", "λq:(num → A). λi:num. f(q(i))")
		rCarrier := a.TermAs[Set[A]]("R.carrier")
		coefficientMap := polynomial_evaluation.CoefficientMapHomomorphism.Read(hom)
		dOver := a.Have(
			"the derivative of p is a polynomial over R",
			"polynomial_over(R.carrier, d)",
			By(
				Normalized,
				dDef,
				pOver,
				comm_ring.CarrierSubring.Read(source),
				polynomial.DerivativeOver.Read(source).At(rCarrier, p)))
		productsOver := a.Have(
			"both products are polynomials over R",
			"polynomial_over(R.carrier, U) ∧ polynomial_over(R.carrier, V)",
			By(
				Normalized,
				UDef,
				VDef,
				bezout,
				dOver,
				pOver,
				polynomial.PolynomialMulOver.Read(source).At(u, p),
				polynomial.PolynomialMulOver.Read(source).At(v, d)))
		witnessesOver := a.Have(
			"the two witnesses map to polynomials over S",
			"polynomial_over(S.carrier, C(u)) ∧ polynomial_over(S.carrier, C(v))",
			CDef.Rw(),
			By(
				bezout,
				ring_homomorphism.MapIn.Read(coefficientMap).AsFact().At(u),
				ring_homomorphism.MapIn.Read(coefficientMap).AsFact().At(v)))
		mappedDerivative := a.Have(
			"the derivative maps to the derivative of the image of p",
			"C(d) = polynomial_derivative(C(p))",
			CDef.Rw(),
			dDef.Rw(),
			By(pOver, polynomial_evaluation.CoefficientMapDerivative.Read(hom).At(p)))
		mappedProducts := a.Have(
			"the two products map to the products of the images",
			"C(U) = polynomial_mul(C(u), C(p)) ∧ C(V) = polynomial_mul(C(v), C(d))",
			CDef.Rw(),
			UDef.Rw(),
			VDef.Rw(),
			By(
				bezout,
				pOver,
				dOver,
				ring_homomorphism.MapMul.Read(coefficientMap).AsFact().At(u, p),
				ring_homomorphism.MapMul.Read(coefficientMap).AsFact().At(v, d)))
		mappedSumUnit := a.Have(
			"the sum and the unit polynomial are preserved",
			"C(vec_add(U, V)) = vec_add(C(U), C(V)) ∧ "+
				"C(basis_vector(R.zero, R.one, 0)) = basis_vector(S.zero, S.one, 0)",
			CDef.Rw(),
			By(
				productsOver,
				ring_homomorphism.MapAdd.Read(coefficientMap).AsFact().At(U, V),
				ring_homomorphism.MapOne.Read(coefficientMap)))
		mappedBezout := a.Have(
			"the images of u and v satisfy the separability identity over S",
			"vec_add(polynomial_mul(C(u), C(p)), polynomial_mul(C(v), polynomial_derivative(C(p)))) = "+
				"basis_vector(S.zero, S.one, 0)",
			By(mappedDerivative, mappedProducts, mappedSumUnit, bezout))
		separableImage := a.Have(
			"the images of u and v witness the separability of the image of p",
			"polynomial_separable(S, C(p))",
			Simp(Fwd(PolynomialSeparableDef)),
			Witness(a.TermAs[Fun[Nat, B]]("C(u)")),
			Witness(a.TermAs[Fun[Nat, B]]("C(v)")),
			By(witnessesOver, mappedBezout))
		a.Show(
			"the image of p is separable over S",
			By(separableImage))
	}),
})}

// SeparableIffDerivative — an irreducible polynomial over a field is
// separable exactly when its derivative is nonzero: a zero derivative
// would make p divide one, while a nonzero derivative has degree below p.
var SeparableIffDerivative = separableIffDerivativeThm{family.Add(registry.ProofEntry{
	Name: "SeparableIffDerivative",
	Key:  "prop_64fafcb400bb05fe",
	Reading: "Irreducibility is load-bearing both ways: for ⇐, (x - a)² (x - b) with " +
		"a ≠ b has the derivative (x - a)(3x - a - 2b), nonzero in every characteristic, " +
		"and is not separable; for ⇒, a nonzero constant is separable with derivative zero.",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_irreducible(field_ring(F), p)",
		},
		Conclusion: "polynomial_separable(field_ring(F), p) ⇔ ¬(polynomial_derivative(p) = vec_zero)",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p *Arrow[Nat, A], irreducible Fact) {
			parts := a.Conjuncts(
				a.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
				"p is over the field",
				"p has positive degree",
				"every factorization of p has a factor of degree zero")
			over, positive := parts[0], parts[1]
			ring := field.RingOn.Read(fieldOn)
			zero, one := a.TermAs[A]("F.zero"), a.TermAs[A]("F.one")
			indexZero := a.TermAs[Nat]("0")
			onePolynomial := a.TermAs[Fun[Nat, A]]("basis_vector(0)")
			derivative := a.TermAs[Fun[Nat, A]]("polynomial_derivative(p)")
			a.Iff()
			a.Forward(
				"separability forces a nonzero derivative",
				func(b *Argument, separable Fact) {
					derivativeZero := b.SupposeNot()
					u, _, bezout := b.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
						b.Unfolded(separable, PolynomialSeparableDef), "u", "v")
					atoms := b.Have(
						"p and its Bézout coefficients lie in the polynomial ring",
						"p ∈ «fieldPolynomials» ∧ u ∈ «fieldPolynomials» ∧ v ∈ «fieldPolynomials»",
						By(over, bezout))
					dividesOne := b.Have(
						"a zero derivative makes p divide the one polynomial",
						"polynomial_divides(field_ring(F), p, basis_vector(0))",
						Simp(Fwd(polynomial_division.PolynomialDividesDef)),
						Witness(u),
						ByArith(polynomial.PolynomialRingOn.Read(ring), atoms, bezout, derivativeZero))
					oneNonzero := b.Have(
						"the one polynomial has a nonzero constant coefficient",
						"basis_vector(0) ≠ vec_zero",
						By(
							Normalized,
							field.OneNotZeroOn.Read(fieldOn),
							vec_space.BasisVectorDef.At(zero, one, indexZero, indexZero),
							vec_space.VecZeroDef.At(zero, indexZero)))
					b.Show(
						"a positive-degree polynomial cannot divide the nonzero polynomial of degree zero",
						ByArith(
							field.OneNotZeroOn.Read(fieldOn),
							positive,
							over,
							oneNonzero,
							dividesOne,
							polynomial_division.DividesDegree.Read(fieldOn).At(p, onePolynomial),
							polynomial.DegreeBasisVector.Read(ring).At(indexZero)))
				})
			a.Backward(
				"a nonzero derivative is too small to have p as a divisor",
				func(b *Argument, nonzero Fact) {
					bounded := b.Have(
						"the derivative vanishes from the degree of p on",
						"vec⟨polynomial_degree(p)⟩(polynomial_derivative(p))",
						By(over, polynomial.DerivativeVec.Read(ring).At(p)))
					notDivides := b.Have(
						"a nonzero derivative has degree strictly below p, so p cannot divide it",
						"¬polynomial_divides(field_ring(F), p, polynomial_derivative(p))",
						ByArith(
							polynomial.DegreeBelow.At(zero, proof.InhabitFrom(derivative, bounded)),
							over,
							nonzero,
							polynomial_division.DividesDegree.Read(fieldOn).At(p, derivative)))
					b.Show(
						"the Bézout identity for p and its derivative gives separability",
						Simp(Fwd(PolynomialSeparableDef)),
						By(
							irreducible,
							over,
							notDivides,
							polynomial.DerivativeOverCarrier.Read(ring).At(p),
							polynomial_division.IrreducibleCoprime.Read(fieldOn).At(p, derivative)))
				})
		}),
})}

// CharZeroIrreducibleSeparable — in characteristic zero an irreducible
// polynomial over a subfield is separable. Its degree n is positive, so the
// derivative's coefficient at n - 1 is n times the leading coefficient, a
// product of two nonzero members of L, and over K read as a field an
// irreducible polynomial with a nonzero derivative is separable.
var CharZeroIrreducibleSeparable = charZeroIrreducibleSeparableThm{family.Add(registry.ProofEntry{
	Name: "CharZeroIrreducibleSeparable",
	Key:  "prop_84ba8cae842df4e9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"subfield(L, K)",
			"polynomial_irreducible(restrict_ring(field_ring(L), K), p)",
		},
		Conclusion: "polynomial_separable(restrict_ring(field_ring(L), K), p)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			p *Arrow[Nat, A],
			characteristic, subK, irreducible Fact,
		) {
			fieldK := a.Have(
				"K with the operations of L is a field",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			parts := a.Conjuncts(
				a.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
				"p is over K",
				"p has positive degree",
				"every factorization of p has a factor of degree zero")
			over, positive := parts[0], parts[1]
			ring := field.RingOn.Read(L)
			zero := a.TermAs[A]("L.zero")
			one := a.MemberOf[on.L](a.TermAs[A]("L.one"), comm_ring.OneIn.Read(ring))
			leading := a.Have(
				"positive degree rules out the zero polynomial, so the leading coefficient of p is nonzero",
				"p(polynomial_degree(p)) ≠ L.zero",
				By(
					positive,
					over,
					polynomial.DegreeVecZero.At(zero),
					nat_order.LessThanIrrefl,
					polynomial.DegreeLeading.At(zero, K, p)))
			m, degree := a.ObtainAs[Nat](
				"the positive degree is a successor",
				"∃m:num. polynomial_degree(p) = suc(m)",
				By(positive, peano.Cases.At(a.TermAs[Nat]("polynomial_degree(p)")), nat_order.LessThanIrrefl))
			n := a.TermAs[Nat]("suc(m)")
			multiple := a.Have(
				"in characteristic zero the sum of suc(m) copies of one is nonzero",
				"monoid_pow(L.add, L.zero, L.one, suc(m)) ≠ L.zero",
				By(a.Unfolded(characteristic, comm_ring.CharacteristicZeroDef).At(n), positive, degree))
			multipleIn := comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).At(one, n)
			leadingInL := a.Have(
				"the coefficients of p lie in K, which lies in L",
				"p(suc(m)) ∈ L.carrier",
				By(
					subK,
					over,
					field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), K),
					polynomial.PolynomialOverDef.At(zero, K, p),
					set_basic.SubsetDef))
			coefficientIn := a.MemberOf[on.L](p.Apply(n), leadingInL)
			coefficient := a.Have(
				"the derivative at m is that multiple of the leading coefficient, and L has no zero divisors",
				"polynomial_derivative(p, m) ≠ L.zero",
				By(
					multiple,
					leading,
					degree,
					polynomial.PolynomialDerivativeDef.At(
						a.TermAs[Op[A]]("L.add"), zero, a.TermAs[Op[A]]("L.mul"), one, p, m),
					field.MulEqZeroOn.Read(L).At(multipleIn, coefficientIn)))
			irreducibleOverK := a.Simplified(irreducible, Fwd(field.RestrictFieldRing))
			a.Show(
				"the derivative is not the zero polynomial, so p is separable over the field K",
				Simp(Fwd(field.RestrictFieldRing)),
				By(
					irreducibleOverK,
					coefficient,
					vec_space.VecZeroDef.At(zero, m),
					SeparableIffDerivative.Read(fieldK).At(p)))
		}),
})}

// SeparableRootSimple — a root of a separable polynomial is simple: the
// derivative does not vanish there, since p is coprime to its derivative
// and coprime polynomials share no root.
var SeparableRootSimple = separableRootSimpleThm{family.Add(registry.ProofEntry{
	Name: "SeparableRootSimple",
	Key:  "prop_c21b6f538789ca4a",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_separable(field_ring(F), p)",
			"x ∈ F.carrier",
			"polynomial_eval(p, x) = F.zero",
		},
		Conclusion: "polynomial_eval(polynomial_derivative(p), x) ≠ F.zero",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p *Arrow[Nat, A], x *Member[A, on.F], given Fact) {
			fieldRing := a.TermAs[RingOps[A]]("field_ring(F)")
			dp := a.TermAs[Fun[Nat, A]]("polynomial_derivative(p)")
			a.Show(
				"p is coprime to its derivative, which is over the field, so the two share no root",
				By(
					given,
					polynomial.DerivativeOverCarrier.Read(field.RingOn.Read(fieldOn)).At(p),
					SeparableCoprime.At(fieldRing, p),
					polynomial_roots.CoprimeNoCommonRoot.Read(fieldOn).At(p, dp, x)))
		}),
})}

// SeparableNonzero — over a field a separable polynomial is nonzero: zero
// is a root of the zero polynomial and of its derivative, the zero
// polynomial again, while a root of a separable polynomial is simple
// (SeparableRootSimple).
var SeparableNonzero = separableNonzeroThm{family.Add(registry.ProofEntry{
	Name: "SeparableNonzero",
	Key:  "prop_638831759c74b078",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_separable(field_ring(F), p)",
		},
		Conclusion: "p ≠ vec_zero",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p *Arrow[Nat, A], given Fact) {
			ring := field.RingOn.Read(fieldOn)
			zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
			a.Show(
				"the zero polynomial and its derivative both vanish at zero, contradicting separability",
				By(
					Normalized,
					given,
					SeparableRootSimple.Read(fieldOn).At(p, zero),
					polynomial.DerivativeVecZero.Read(ring),
					polynomial_evaluation.EvalVecZero.Read(ring).At(zero)))
		}),
})}

// SeparableFactorsShareNoRoot — the two factors of a separable product
// share no root in the field: at a common root both terms of the product
// rule vanish, so the product would be a separable polynomial whose
// derivative vanishes at its root (SeparableRootSimple).
var SeparableFactorsShareNoRoot = separableFactorsShareNoRootThm{family.Add(registry.ProofEntry{
	Name: "SeparableFactorsShareNoRoot",
	Key:  "prop_657bee9271a6ebea",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀g q:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, g)",
			"polynomial_over(F.carrier, q)",
			"polynomial_separable(field_ring(F), polynomial_mul(g, q))",
			"x ∈ F.carrier",
			"polynomial_eval(g, x) = F.zero",
		},
		Conclusion: "polynomial_eval(q, x) ≠ F.zero",
	},
		func(
			a *Argument,
			fieldOn field.FieldFact[on.F],
			g, q *Arrow[Nat, A],
			x *Member[A, on.F],
			given Fact,
		) {
			ring := field.RingOn.Read(fieldOn)
			denial := a.SupposeNot()
			dg, dq :=
				a.TermAs[Fun[Nat, A]]("polynomial_derivative(g)"), a.TermAs[Fun[Nat, A]]("polynomial_derivative(q)")
			left, right :=
				a.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_derivative(g), q)"),
				a.TermAs[Fun[Nat, A]]("polynomial_mul(g, polynomial_derivative(q))")
			derivativesOver := a.Have(
				"both derivatives are polynomials over the field",
				"polynomial_over(F.carrier, polynomial_derivative(g)) ∧ "+
					"polynomial_over(F.carrier, polynomial_derivative(q))",
				By(
					given,
					polynomial.DerivativeOverCarrier.Read(ring).At(g),
					polynomial.DerivativeOverCarrier.Read(ring).At(q)))
			productValues := a.Have(
				"if q also vanished, both summands in the product rule would vanish",
				"polynomial_eval(polynomial_mul(polynomial_derivative(g), q), x) = F.zero ∧ "+
					"polynomial_eval(polynomial_mul(g, polynomial_derivative(q)), x) = F.zero",
				By(
					denial,
					given,
					x,
					derivativesOver,
					polynomial_evaluation.EvalMulRoot.Read(ring).At(q, dg, x),
					polynomial_evaluation.EvalMulRoot.Read(ring).At(g, dq, x)))
			productsOver := a.Have(
				"the summands in the product rule are polynomials over the field",
				"polynomial_over(F.carrier, polynomial_mul(polynomial_derivative(g), q)) ∧ "+
					"polynomial_over(F.carrier, polynomial_mul(g, polynomial_derivative(q)))",
				By(
					given,
					derivativesOver,
					polynomial.PolynomialMulOver.Read(ring).At(dg, q),
					polynomial.PolynomialMulOver.Read(ring).At(g, dq)))
			coefficients := a.Have(
				"every coefficient of g and of q lies in the field",
				"∀i:num. g(i) ∈ F.carrier ∧ q(i) ∈ F.carrier",
				By(given, polynomial.PolynomialOverDef))
			derivativeValue := a.Have(
				"the derivative of the product would vanish at x",
				"polynomial_eval(polynomial_derivative(polynomial_mul(g, q)), x) = F.zero",
				By(
					comm_ring.ZeroIn.Read(ring),
					productValues,
					given,
					x,
					productsOver,
					coefficients,
					polynomial.DerivativeMul.Read(ring).At(g, q),
					polynomial_evaluation.EvalAdd.Read(ring).At(left, right, x),
					comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(
						a.TermAs[A]("F.zero"))))
			a.Show(
				"a root of a separable polynomial cannot also annihilate its derivative",
				By(
					derivativeValue,
					given,
					x,
					polynomial.PolynomialMulOver.Read(ring).At(g, q),
					polynomial_evaluation.EvalMulRoot.Read(ring).At(g, q, x),
					SeparableRootSimple.Read(fieldOn).At(a.TermAs[Fun[Nat, A]]("polynomial_mul(g, q)"), x)))
		}),
})}

// SeparableSplitsRoots — a separable polynomial that splits has as many
// roots as its degree: strong induction on the degree. A constant has no
// roots; otherwise remove a root, count the quotient's roots, and
// separability keeps the removed root out of them.
var SeparableSplitsRoots = separableSplitsRootsThm{family.Add(registry.ProofEntry{
	Name: "SeparableSplitsRoots",
	Key:  "prop_3cc5dec5ffe5b229",
	Reading: "Separability is load-bearing: (x - a)² splits and has one root against " +
		"degree two. polynomial_over(F.carrier, p) is needed, the operations being free " +
		"off F.carrier; that p is nonzero follows from separability over a field.",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_separable(field_ring(F), p)",
			"polynomial_splits(field_ring(F), p)",
		},
		Conclusion: "has_size(polynomial_roots(F.carrier, p), polynomial_degree(p))",
	},
		func(arg *Argument, fieldOn field.FieldFact[on.F], p *Arrow[Nat, A], given Fact) {
			ring := field.RingOn.Read(fieldOn)
			count := arg.TermAs[Fun[Nat, Bool]](
				"λn:num. ∀f:(num → A). " +
					"    polynomial_over(F.carrier, f) ∧ " +
					"    polynomial_separable(field_ring(F), f) ∧ " +
					"    polynomial_splits(field_ring(F), f) ∧ " +
					"    polynomial_degree(f) = n ⇒ " +
					"    has_size(polynomial_roots(F.carrier, f), n)")
			arg.Show(
				"strong induction on the degree counts the roots of "+
					"every separable polynomial that splits, p among them",
				ByInduction(At(nat_order.StrongInduction, count, arg.TermAs[Nat]("polynomial_degree(p)")), given,
					Case(
						"granted the count below degree n, a separable polynomial of degree n that splits has n roots",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							smaller := b.Assume()
							f := b.FixAs[Fun[Nat, A]]("f")
							parts := b.Conjuncts(
								b.Assume(),
								"f is over the field",
								"f is separable",
								"f splits",
								"f has degree n")
							fOver, fSeparable, fSplits, degree := parts[0], parts[1], parts[2], parts[3]
							nonzero := b.Have(
								"separability forces f to be nonzero",
								"f ≠ vec_zero",
								By(fOver, fSeparable, SeparableNonzero.Read(fieldOn).At(f)))
							degreeNonzero := b.Unless(
								b.Term("polynomial_degree(f) = 0"),
								"degree zero is the constant case",
								Given(func(c *Argument, degreeZero Fact) {
									c.Show(
										"n is the degree of f; the nonzero constant has no roots, and the empty set has size zero",
										degree.RwRev(),
										By(
											fieldOn,
											nonzero,
											degreeZero,
											fOver,
											polynomial_roots.DegreeZeroNoRoots.Read(ring).At(f),
											cardinality.HasSizeZero.At(c.TermAs[Set[A]]("polynomial_roots(F.carrier, f)"))))
								}))
							positiveDegree := b.Have(
								"the degree is positive",
								"0 < polynomial_degree(f)",
								ByArith(degreeNonzero))
							a, aRoot := b.UnpackAs[A](
								GroupPremises(parts[0], parts[2], positiveDegree, SplitsRoot.Read(fieldOn).At(f)), "a")
							aIn := b.Have(
								"the root lies in the field",
								"a ∈ F.carrier",
								By(aRoot))
							aMember := b.MemberOf[on.F](a, aIn)
							q, factor := b.UnpackAs[Fun[Nat, A]](
								GroupPremises(
									parts[0],
									nonzero,
									aRoot,
									polynomial_roots.RootFactorization.Read(integral_domain.FieldIntegralDomain.Read(fieldOn)).At(
										f, aMember)),
								"q")
							linear := b.Conjuncts(
								polynomial_roots.LinearFactor.Read(ring).At(aMember),
								"the removed factor x - a is a polynomial over the field",
								"it is monic",
								"it has degree at most one",
								"its value at each point y of the field is y - a",
								"it vanishes at a",
								"and its degree is one when one is not zero")
							gOver, gRoot := linear[0], linear[4]
							g := b.TermAs[Fun[Nat, A]]("«linear»(a)")
							factorCoefficients := b.Have(
								"every coefficient of x - a and of the quotient lies in the field",
								"∀i:num. «linear»(a, i) ∈ F.carrier ∧ q(i) ∈ F.carrier",
								By(factor, gOver, polynomial.PolynomialOverDef))
							qDivides := b.Have(
								"the quotient divides f",
								"polynomial_divides(field_ring(F), q, f)",
								Simp(Fwd(polynomial_division.PolynomialDividesDef)),
								Witness(g),
								By(factor, gOver, factorCoefficients, polynomial.PolynomialMulComm.Read(ring).At(g, q)))
							quotient := b.Have(
								"the quotient remains separable and splitting",
								"polynomial_separable(field_ring(F), q) ∧ polynomial_splits(field_ring(F), q)",
								By(
									factor,
									fSeparable,
									fSplits,
									qDivides,
									SeparableDivisor.Read(ring).At(q, f),
									SplitsDivisor.Read(ring).At(q, f)))
							quotientSmaller := b.Have(
								"the quotient's degree lies below n",
								"polynomial_degree(q) < n",
								ByArith(degree, factor))
							qCount := b.Have(
								"the hypothesis below n counts the quotient roots",
								"has_size(polynomial_roots(F.carrier, q), polynomial_degree(q))",
								By(smaller.At(b.TermAs[Nat]("polynomial_degree(q)"), q), quotientSmaller, quotient, factor))
							qAtRoot := b.Have(
								"separability keeps a out of the quotient roots",
								"polynomial_eval(q, a) ≠ F.zero",
								By(factor, fSeparable, gOver, gRoot, SeparableFactorsShareNoRoot.Read(fieldOn).At(g, q, aMember)))
							newRoot := b.Have(
								"a is a new root when inserted into the quotient root set",
								"a ∉ polynomial_roots(F.carrier, q)",
								Simp(Fwd(polynomial_roots.PolynomialRootsDef)),
								BySets(Normalized, qAtRoot))
							insertion := b.Have(
								"the root set is obtained by adjoining one new point",
								"∃b:A. ∃t:set(A). "+
									"    has_size(t, polynomial_degree(q)) ∧ b ∉ t ∧ polynomial_roots(F.carrier, f) = insert(b, t)",
								Witness(a),
								Witness(b.TermAs[Set[A]]("polynomial_roots(F.carrier, q)")),
								By(newRoot, qCount, factor))
							successorCount := b.Have(
								"adjoining the new root increments the exact size",
								"has_size(polynomial_roots(F.carrier, f), suc(polynomial_degree(q)))",
								Simp(Fwd(cardinality.HasSizeClauses)),
								By(insertion))
							b.Show(
								"n is the degree of f, and the size increment is the degree increment",
								degree.RwRev(),
								By(successorCount, factor))
						}))))
		}),
})}

// DistinctLinearProduct — the product of the linear factors X − a over a
// finite subset S of a field is over the field, separable and split, has
// root set exactly S, and is coprime to X − a at every point of the field
// off S: induction on S, a new root multiplying the product by a linear
// factor coprime to it.
var DistinctLinearProduct = distinctLinearProductThm{family.Add(registry.ProofEntry{
	Name: "DistinctLinearProduct",
	Key:  "prop_df3e6bb70b617c27",
	Build: family.Sections(Statement{
		Binders: "∀F:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"finite(S)",
			"S ⊆ F.carrier",
		},
		Conclusion: "polynomial_over(F.carrier, «product»(F, S)) ∧ " +
			"polynomial_separable(field_ring(F), «product»(F, S)) ∧ " +
			"polynomial_splits(field_ring(F), «product»(F, S)) ∧ " +
			"polynomial_roots(F.carrier, «product»(F, S)) = S ∧ " +
			"(∀a:A. a ∈ F.carrier ∧ a ∉ S ⇒ polynomial_coprime(field_ring(F), «product»(F, S), «line»(F, a)))",
		Abbrev: Abbrev{
			{Name: "line", Text: "λF:field_ops(A). λa:A. " +
				"    vec_sub(F.sub, " +
				"        basis_vector(F.zero, F.one, 1), " +
				"        vec_scalar_mul(F.mul, a, basis_vector(F.zero, F.one, 0)))"},
			{Name: "product", Text: "λF:field_ops(A). λS:set(A). " +
				"    module_sum(polynomial_mul(F.add, F.zero, F.mul), " +
				"        basis_vector(F.zero, F.one, 0), " +
				"        S, " +
				"        λa:A. «line»(F, a))"},
			{Name: "polynomials", Text: "λF:field_ops(A). " +
				"    {p:(num → A) | polynomial_over(F.zero, F.carrier, p)}"},
			{Name: "scaledLine", Text: "λF:field_ops(A). λc:A. λa:A. vec_scalar_mul(F.mul, c, «line»(F, a))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		linearDerivative := ctx.Lemma(Statement{
			Binders:    "∀F:field_on(A). ∀a:A.",
			Hypotheses: []string{"a ∈ F.carrier"},
			Conclusion: "polynomial_derivative(«line»(F, a)) = basis_vector(0)",
		}, func(b *Argument, F field.FieldFact[on.F], a *Member[A, on.F]) {
			b.Do(Funext())
			b.FixAs[Nat]("n")
			b.Do(Simp(
				Fwd(polynomial.PolynomialDerivativeDef),
				Fwd(vec_space.VecSubDef),
				Fwd(vec_space.VecScalarMulDef),
				Fwd(vec_space.BasisVectorDef)))
			b.Cases(b.TermAs[Bool]("n = 0"))
			b.When(
				"the constant coefficient of the derivative is one",
				func(c *Argument, zero Fact) {
					c.Show(
						"the first coefficient differentiates to one",
						zero.Subst(),
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						ByArith(F, a))
				})
			b.Otherwise(
				"higher coefficients differentiate to zero",
				func(c *Argument, nonzero Fact) {
					c.Show(
						"there are no higher coefficients",
						ByArith(F, nonzero, a))
				})
		})
		oneCoprime := ctx.Lemma(Statement{
			Binders:    "∀F:field_on(A). ∀p:(num → A).",
			Hypotheses: []string{"polynomial_over(F.carrier, p)"},
			Conclusion: "polynomial_coprime(field_ring(F), basis_vector(0), p)",
		}, func(b *Argument, F field.FieldFact[on.F], p *Arrow[Nat, A], over Fact) {
			ring := field.RingOn.Read(F)
			inRing := b.Have(
				"p lies in the polynomial ring",
				"p ∈ «polynomials»(F)",
				By(over))
			identity := b.Have(
				"one times one plus zero times p is one",
				"vec_add(F.add, "+
					"    polynomial_mul(basis_vector(0), basis_vector(0)), "+
					"    polynomial_mul(vec_zero(F.zero), p)) = "+
					"basis_vector(0)",
				ByArith(polynomial.PolynomialRingOn.Read(ring), inRing))
			b.Do(Simp(Fwd(polynomial_division.PolynomialCoprimeDef)))
			b.Take(b.TermAs[Fun[Nat, A]]("basis_vector(F.zero, F.one, 0)"))
			b.Take(b.TermAs[Fun[Nat, A]]("vec_zero(F.zero)"))
			b.Show(
				"one and zero are Bézout coefficients",
				By(
					identity,
					polynomial.BasisVectorOver.Read(ring).At(b.TermAs[Nat]("0")),
					polynomial.VecZeroOver.Read(ring)))
		})
		linearSeparable := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀a:A.", Hypotheses: []string{"a ∈ F.carrier"},
			Conclusion: "polynomial_separable(field_ring(F), «line»(F, a))",
		}, func(b *Argument, F field.FieldFact[on.F], a *Member[A, on.F]) {
			ring, f := field.RingOn.Read(F), b.TermAs[Fun[Nat, A]]("«line»(F, a)")
			Ft, one := b.TermAs[FieldOps[A]]("F"), b.TermAs[Fun[Nat, A]]("basis_vector(F.zero, F.one, 0)")
			derivative := b.Have(
				"the derivative of the linear factor is one",
				"polynomial_derivative(«line»(F, a)) = basis_vector(0)",
				By(F, a, At(linearDerivative, Ft, a)))
			coprime := b.Have(
				"the linear factor, a polynomial over F, is coprime to one",
				"polynomial_coprime(field_ring(F), «line»(F, a), basis_vector(0))",
				By(
					a,
					polynomial_roots.LinearFactor.Read(ring).At(a),
					At(oneCoprime, Ft, f),
					polynomial.BasisVectorOver.Read(ring).At(b.TermAs[Nat]("0")),
					polynomial_division.CoprimeSymm.Read(ring).At(one, f)))
			b.Show(
				"the Bézout definitions give separability",
				By(derivative, coprime, PolynomialSeparableDef, polynomial_division.PolynomialCoprimeDef))
		})
		distinctLinearCoprime := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀a b:A.", Hypotheses: []string{"a ∈ F.carrier", "b ∈ F.carrier", "a ≠ b"},
			Conclusion: "polynomial_coprime(field_ring(F), «line»(F, a), «line»(F, b))",
		}, func(d *Argument, F field.FieldFact[on.F], a, b *Member[A, on.F], distinct Fact) {
			ring := field.RingOn.Read(F)
			c, cDef := d.LetAs[A]("c", "F.inv(b - a)")
			delta := comm_ring.SubIn.Read(ring).At(b, a)
			nonzero := d.Have(
				"the difference of the two roots is nonzero",
				"b - a ≠ F.zero",
				ByArith(F, a, b, distinct))
			cIn := d.Have(
				"the inverse difference lies in F",
				"c ∈ F.carrier",
				By(Normalized, cDef, a, b, distinct, delta, field.InvIn.Read(F).At(delta)))
			inverse := d.Have(
				"the inverse difference cancels the difference",
				"c * (b - a) = F.one",
				By(Normalized, nonzero, cDef, a, b, distinct, delta, field.MulLeftInverseOn.Read(F).At(delta)))
			identity := d.Have(
				"opposite scalar multiples of the factors add to one",
				"vec_add(F.add, «scaledLine»(F, c, a), «scaledLine»(F, -c, b)) = basis_vector(0)",
				Derive(func(e *Argument) {
					e.Do(Funext())
					e.FixAs[Nat]("n")
					e.Do(Simp(
						Fwd(vec_space.VecAddDef),
						Fwd(vec_space.VecSubDef),
						Fwd(vec_space.VecScalarMulDef),
						Fwd(vec_space.BasisVectorDef)))
					e.Cases(e.TermAs[Bool]("n = 0"))
					e.When(
						"the constant terms give the inverse difference identity",
						func(f *Argument, zero Fact) {
							f.Show(
								"the constant coefficient is one",
								zero.Subst(),
								ByArith(F, inverse, zero, cIn, a, b, distinct))
						})
					e.Otherwise(
						"the remaining coefficients cancel",
						func(f *Argument, nonzeroIndex Fact) {
							f.Cases(f.TermAs[Bool]("n = 1"))
							f.When(
								"the leading coefficients are opposite",
								func(g *Argument, one Fact) {
									g.Show(
										"the linear coefficient is zero",
										one.Subst(),
										ByArith(F, nonzeroIndex, inverse, one, cIn, a, b, distinct))
								})
							f.Otherwise(
								"all higher coefficients vanish",
								func(g *Argument, notOne Fact) {
									g.Show(
										"the higher coefficient is zero",
										ByArith(F, nonzeroIndex, notOne, inverse, cIn, a, b, distinct))
								})
						})
				}))
			U, uDef := d.LetAs[Fun[Nat, A]]("U", "vec_scalar_mul(F.mul, c, basis_vector(0))")
			V, vDef := d.LetAs[Fun[Nat, A]]("V", "vec_scalar_mul(F.mul, -c, basis_vector(0))")
			lines := d.Have(
				"both linear factors are over F",
				"polynomial_over(F.carrier, «line»(F, a)) ∧ polynomial_over(F.carrier, «line»(F, b))",
				By(
					a,
					b,
					distinct,
					polynomial_roots.LinearFactor.Read(ring).At(a),
					polynomial_roots.LinearFactor.Read(ring).At(b)))
			cMember := d.MemberOf[on.F](c, cIn)
			negative := comm_ring.NegIn.Read(ring).At(cMember)
			coefficients := d.Have(
				"the Bézout coefficients and their scalar products are over F",
				"polynomial_over(F.carrier, U) ∧ "+
					"polynomial_over(F.carrier, V) ∧ "+
					"polynomial_over(F.carrier, «scaledLine»(F, c, a)) ∧ "+
					"polynomial_over(F.carrier, «scaledLine»(F, -c, b))",
				By(
					Normalized,
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
					uDef,
					vDef,
					cIn,
					lines,
					polynomial.BasisVectorOver.Read(ring).At(d.TermAs[Nat]("0")),
					negative))
			fa, fb := d.TermAs[Fun[Nat, A]]("«line»(F, a)"), d.TermAs[Fun[Nat, A]]("«line»(F, b)")
			products := d.Have(
				"multiplication by a constant polynomial is scalar multiplication",
				"polynomial_mul(«line»(F, a), U) = «scaledLine»(F, c, a) ∧ "+
					"polynomial_mul(«line»(F, b), V) = «scaledLine»(F, -c, b)",
				By(
					uDef,
					vDef,
					cIn,
					lines,
					negative,
					polynomial.PolynomialMulConstant.Read(ring).At(cMember, fa),
					polynomial.PolynomialMulConstant.Read(ring).At(negative, fb)))
			atoms := d.Have(
				"the terms of the identity lie in the polynomial ring",
				"U ∈ «polynomials»(F) ∧ "+
					"V ∈ «polynomials»(F) ∧ "+
					"«line»(F, a) ∈ «polynomials»(F) ∧ "+
					"«line»(F, b) ∈ «polynomials»(F) ∧ "+
					"«scaledLine»(F, c, a) ∈ «polynomials»(F) ∧ "+
					"«scaledLine»(F, -c, b) ∈ «polynomials»(F)",
				By(coefficients, lines))
			monoid := comm_ring.MulMonoidOn.Read(polynomial.PolynomialRingOn.Read(ring))
			bezout := d.Have(
				"commutativity turns the scalar identity into a Bézout identity",
				"vec_add(F.add, polynomial_mul(U, «line»(F, a)), polynomial_mul(V, «line»(F, b))) = "+
					"basis_vector(0)",
				By(
					identity,
					products,
					atoms,
					comm_monoid.CommOn.Read(monoid).AsFact().At(U, fa),
					comm_monoid.CommOn.Read(monoid).AsFact().At(V, fb)))
			d.Do(Simp(Fwd(polynomial_division.PolynomialCoprimeDef)))
			d.Take(U)
			d.Take(V)
			d.Show(
				"the two constants witness coprimality",
				By(bezout, coefficients))
		})
		lowDegreeSplits := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀p:(num → A).",
			Hypotheses: []string{
				"polynomial_over(F.carrier, p)",
				"polynomial_separable(field_ring(F), p)",
				"polynomial_degree(p) ≤ 1",
			},
			Conclusion: "polynomial_splits(field_ring(F), p)",
		}, func(b *Argument, F field.FieldFact[on.F], p *Arrow[Nat, A], hypotheses Fact) {
			b.Do(Simp(Fwd(PolynomialSplitsDef)))
			q := b.FixAs[Fun[Nat, A]]("q")
			divides := b.Assume()
			irreducible := b.Have(
				"an irreducible divisor is over F and has positive degree",
				"polynomial_over(F.carrier, q) ∧ 0 < polynomial_degree(q)",
				By(divides, polynomial_division.PolynomialIrreducibleDef))
			bound := b.Have(
				"a separable polynomial is nonzero, so a divisor has no larger degree",
				"polynomial_degree(q) ≤ polynomial_degree(p)",
				By(
					hypotheses,
					SeparableNonzero.Read(F).At(p),
					divides,
					irreducible,
					polynomial_division.DividesDegree.Read(F).At(q, p)))
			b.Show(
				"every irreducible divisor has degree one",
				ByArith(bound, hypotheses, irreducible))
		})
		oneSeparable := ctx.Lemma("∀F:field_on(A). polynomial_separable(field_ring(F), basis_vector(0))",
			func(b *Argument, F field.FieldFact[on.F]) {
				ring := field.RingOn.Read(F)
				one := b.TermAs[Fun[Nat, A]]("basis_vector(F.zero, F.one, 0)")
				b.Show(
					"one is coprime to its derivative, which is over F",
					By(
						Normalized,
						F,
						polynomial.BasisVectorOver.Read(ring).At(b.TermAs[Nat]("0")),
						polynomial.DerivativeOverCarrier.Read(ring).At(one),
						At(
							oneCoprime,
							b.TermAs[FieldOps[A]]("F"),
							b.TermAs[Fun[Nat, A]]("polynomial_derivative(basis_vector(0))")),
						PolynomialSeparableDef,
						polynomial_division.PolynomialCoprimeDef))
			})
		evalProductZero := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀p q:(num → A). ∀x:A.",
			Hypotheses: []string{
				"polynomial_over(F.carrier, p)",
				"polynomial_over(F.carrier, q)",
				"x ∈ F.carrier",
			},
			Conclusion: "polynomial_eval(polynomial_mul(p, q), x) = F.zero ⇔ " +
				"polynomial_eval(p, x) = F.zero ∨ polynomial_eval(q, x) = F.zero",
		}, func(b *Argument, F field.FieldFact[on.F], p, q *Arrow[Nat, A], x *Expr[A], hypotheses Fact) {
			ring := field.RingOn.Read(F)
			b.Show(
				"evaluation preserves products and a field has no zero divisors",
				By(
					hypotheses,
					polynomial_evaluation.EvalIn.Read(ring).AsFact().At(p, x),
					polynomial_evaluation.EvalIn.Read(ring).AsFact().At(q, x),
					polynomial_evaluation.EvalMul.Read(ring).AsFact().At(p, q, x),
					field.MulEqZeroOn.Read(F).AsFact().At(
						b.TermAs[A]("polynomial_eval(p, x)"), b.TermAs[A]("polynomial_eval(q, x)"))))
		})
		oneFacts := ctx.Lemma("∀F:field_on(A). "+
			"    polynomial_over(F.carrier, basis_vector(0)) ∧ "+
			"    polynomial_separable(field_ring(F), basis_vector(0)) ∧ "+
			"    polynomial_splits(field_ring(F), basis_vector(0)) ∧ "+
			"    polynomial_roots(F.carrier, basis_vector(0)) = ∅",
			func(b *Argument, F field.FieldFact[on.F]) {
				Ft, one := b.TermAs[FieldOps[A]]("F"), b.TermAs[Fun[Nat, A]]("basis_vector(F.zero, F.one, 0)")
				ring := field.RingOn.Read(F)
				overSeparable := b.Have(
					"one is over F and separable",
					"polynomial_over(F.carrier, basis_vector(0)) ∧ "+
						"polynomial_separable(field_ring(F), basis_vector(0))",
					By(polynomial.BasisVectorOver.Read(ring).At(b.TermAs[Nat]("0")), At(oneSeparable, Ft)))
				degree := b.Have(
					"one has degree zero",
					"polynomial_degree(basis_vector(0)) = 0",
					By(field.OneNotZeroOn.Read(F), polynomial.DegreeBasisVector.Read(ring).At(b.TermAs[Nat]("0"))))
				bound := b.Have(
					"its degree is at most one",
					"polynomial_degree(basis_vector(0)) ≤ 1",
					ByArith(degree))
				splits := b.Have(
					"one splits",
					"polynomial_splits(field_ring(F), basis_vector(0))",
					By(F, bound, overSeparable, At(lowDegreeSplits, Ft, one)))
				b.Show(
					"the empty product has no roots",
					By(
						degree,
						splits,
						overSeparable,
						SeparableNonzero.Read(F).At(one),
						polynomial_roots.DegreeZeroNoRoots.Read(ring).At(one)))
			})
		linearFacts := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀a:A.", Hypotheses: []string{"a ∈ F.carrier"},
			Conclusion: "polynomial_over(F.carrier, «line»(F, a)) ∧ " +
				"polynomial_separable(field_ring(F), «line»(F, a)) ∧ " +
				"polynomial_splits(field_ring(F), «line»(F, a)) ∧ " +
				"polynomial_roots(F.carrier, «line»(F, a)) = {a}",
		}, func(b *Argument, F field.FieldFact[on.F], a *Member[A, on.F]) {
			Ft, line := b.TermAs[FieldOps[A]]("F"), b.TermAs[Fun[Nat, A]]("«line»(F, a)")
			properties := b.Have(
				"a linear factor is over F, has degree at most one, and evaluates by subtraction",
				"polynomial_over(F.carrier, «line»(F, a)) ∧ "+
					"polynomial_degree(«line»(F, a)) ≤ 1 ∧ "+
					"(∀y:A. y ∈ F.carrier ⇒ polynomial_eval(«line»(F, a), y) = y - a)",
				By(a, polynomial_roots.LinearFactor.Read(field.RingOn.Read(F)).At(a)))
			separable := b.Have(
				"the linear factor is separable",
				"polynomial_separable(field_ring(F), «line»(F, a))",
				By(F, a, At(linearSeparable, Ft, a)))
			subtractZero := b.Have(
				"subtraction vanishes exactly at a",
				"∀y:A. y ∈ F.carrier ⇒ (y - a = F.zero ⇔ y = a)",
				Derive(func(c *Argument) {
					c.FixAs[A]("y")
					yIn := c.Assume()
					c.Iff()
					c.Forward(
						"zero difference identifies the point",
						func(d *Argument, zero Fact) {
							d.Show(
								"the point equals a",
								ByArith(F, zero, a, yIn))
						})
					c.Backward(
						"a has zero difference from itself",
						func(d *Argument, equal Fact) {
							d.Show(
								"the difference vanishes",
								ByArith(F, equal, a, yIn))
						})
				}))
			roots := b.Have(
				"the root set of the linear factor is the singleton",
				"polynomial_roots(F.carrier, «line»(F, a)) = {a}",
				BySets(subtractZero, a, properties, polynomial_roots.PolynomialRootsDef))
			b.Show(
				"the linear factor has all four required properties",
				By(F, roots, separable, properties, At(lowDegreeSplits, Ft, line)))
		})
		return ctx.Theorem(headline, func(
			b *Argument,
			F field.FieldFact[on.F],
			S *Expr[Set[A]],
			hypotheses Fact,
		) {
			Ft := b.TermAs[FieldOps[A]]("F")
			ring := field.RingOn.Read(F)
			elements := b.Have(
				"every element of S lies in F",
				"∀a:A. a ∈ S ⇒ a ∈ F.carrier",
				BySets(hypotheses))
			b.Show(
				"induction on a finite set of distinct roots",
				ByInduction(finite_set.FiniteInductFreshOn, F, elements, hypotheses,
					Case(
						"the empty product is one",
						Simp(Fwd(module.ModuleSumEmpty)),
						By(polynomial_roots.LinearFactor.Read(ring), At(oneFacts, Ft), At(oneCoprime, Ft))),
					Case(
						"adjoining a new root multiplies by a coprime linear factor",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							t := c.FixAs[Set[A]]("t")
							induction := c.Assume()
							p, pDef := c.LetAs[Fun[Nat, A]]("p", "«product»(F, t)")
							f, fDef := c.LetAs[Fun[Nat, A]]("f", "«line»(F, x)")
							factor := c.Have(
								"the new linear factor is separable and splits with root x",
								"polynomial_over(F.carrier, f) ∧ "+
									"polynomial_separable(field_ring(F), f) ∧ "+
									"polynomial_splits(field_ring(F), f) ∧ "+
									"polynomial_roots(F.carrier, f) = {x}",
								By(Normalized, F, fDef, induction, At(linearFacts, Ft, x)))
							coprime := c.Have(
								"the old product is coprime to the new factor",
								"polynomial_coprime(field_ring(F), p, f)",
								By(Normalized, fDef, induction))
							reversed := c.Have(
								"the new factor is coprime to the old product",
								"polynomial_coprime(field_ring(F), f, p)",
								By(induction, factor, coprime, polynomial_division.CoprimeSymm.Read(ring).At(p, f)))
							_, rDef := c.LetAs[Fun[Nat, A]]("r", "polynomial_mul(f, p)")
							properties := c.Have(
								"the enlarged product is over F, separable, and split",
								"polynomial_over(F.carrier, r) ∧ "+
									"polynomial_separable(field_ring(F), r) ∧ "+
									"polynomial_splits(field_ring(F), r)",
								By(
									Normalized,
									rDef,
									induction,
									factor,
									reversed,
									polynomial.PolynomialMulOver.Read(ring).At(f, p),
									SeparableMul.Read(ring).At(f, p),
									SplitsMul.Read(F).At(f, p)))
							factorData := c.Have(
								"the factors have root sets singleton x and t",
								"polynomial_over(F.carrier, f) ∧ "+
									"polynomial_over(F.carrier, p) ∧ "+
									"polynomial_roots(F.carrier, f) = {x} ∧ "+
									"polynomial_roots(F.carrier, p) = t",
								By(induction, factor))
							roots := c.Have(
								"the enlarged product has exactly the enlarged root set",
								"polynomial_roots(F.carrier, r) = insert(x, t)",
								Derive(func(d *Argument) {
									d.Do(Simp(Fwd(set_basic.Extension)))
									y := d.FixAs[A]("y")
									d.Do(factorData.Simp(Fwd(polynomial_roots.PolynomialRootsDef)))
									d.Show(
										"a product vanishes exactly where either factor vanishes",
										Simp(Fwd(rDef), Fwd(polynomial_roots.PolynomialRootsDef)),
										BySets(F, factorData, At(evalProductZero, Ft, f, p, y)))
								}))
							factorsIn := c.Have(
								"all factors indexed by t lie in the polynomial ring",
								"∀y:A. y ∈ t ⇒ «line»(F, y) ∈ «polynomials»(F)",
								By(polynomial_roots.LinearFactor.Read(ring), induction))
							insertion := c.Have(
								"the finite product over the insertion is the enlarged product",
								"«product»(F, insert(x, t)) = r",
								BySets(
									Normalized,
									factorsIn,
									fDef,
									pDef,
									rDef,
									induction,
									factor,
									module.ModuleSumInsertMonoid.Read(
										comm_ring.MulMonoidOn.Read(polynomial.PolynomialRingOn.Read(ring))).At(
										t, x, c.TermAs[Fun[A, Fun[Nat, A]]]("λa:A. «line»(F, a)"))))
							outside := c.Have(
								"a linear factor outside the enlarged root set remains coprime",
								"∀a:A. a ∈ F.carrier ∧ a ∉ insert(x, t) ⇒ polynomial_coprime(field_ring(F), r, «line»(F, a))",
								Derive(func(d *Argument) {
									z := d.FixAs[A]("a")
									guard := d.Assume()
									fresh := d.Have(
										"the outside point differs from x and is outside t",
										"a ∉ t ∧ x ≠ a",
										BySets(guard))
									pair := d.Have(
										"each factor is coprime to the outside linear factor",
										"polynomial_coprime(field_ring(F), p, «line»(F, a)) ∧ "+
											"polynomial_coprime(field_ring(F), f, «line»(F, a))",
										By(F, fDef, fresh, guard, induction, At(distinctLinearCoprime, Ft, x, z)))
									line := d.TermAs[Fun[Nat, A]]("«line»(F, a)")
									d.Show(
										"coprimality is preserved by multiplication",
										By(
											rDef,
											guard,
											factorData,
											pair,
											polynomial_roots.LinearFactor.Read(ring).AsFact().At(z),
											polynomial_division.CoprimeMul.Read(ring).At(f, p, line)))
								}))
							c.Show(
								"the insertion has all inductive properties",
								By(Normalized, outside, roots, insertion, properties))
						}))))
		})
	}),
})}

// SeparableCoprime — a polynomial is separable exactly when it is coprime
// to its derivative: both sides unfold to one statement, a combination of
// p and its derivative by polynomials over the carrier equal to one.
var SeparableCoprime = separableCoprimeThm{family.Add(registry.ProofEntry{
	Name: "SeparableCoprime",
	Key:  "prop_dfe431bfa783edc9",
	Build: family.Theorem("∀R:ring_ops(A). ∀p:(num → A). "+
		"    polynomial_separable(R, p) ⇔ "+
		"    polynomial_coprime(R, p, polynomial_derivative(R.add, R.zero, R.mul, R.one, p))",
		func(a *Argument, _ *Expr[RingOps[A]], p *Arrow[Nat, A]) {
			a.Show(
				"both sides unfold to the same Bézout combination",
				Simp(Fwd(PolynomialSeparableDef), Fwd(polynomial_division.PolynomialCoprimeDef)),
				Basic())
		}),
})}

// ---------------------------------------------------------------------------
// The derivative at two roots
// ---------------------------------------------------------------------------

// DerivativeAtRootFactors — at two distinct roots a and b of a nonzero polynomial
// p over a domain, the value of the derivative of p at a is a multiple of a - b in
// the domain: p = (X - a) q with q(b) = 0, so q = (X - b) r, and differentiating
// the first product at its root gives q(a) = (a - b) r(a).
var DerivativeAtRootFactors = derivativeAtRootFactorsThm{family.Add(registry.ProofEntry{
	Name: "DerivativeAtRootFactors",
	Key:  "prop_62b6a3f31f1fd962",
	Build: family.Sections(Statement{
		Binders: "∀R:integral_domain_on(A). ∀p:(num → A). ∀a b:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"p ≠ vec_zero",
			"a ∈ R.carrier",
			"b ∈ R.carrier",
			"a ≠ b",
			"polynomial_eval(p, a) = R.zero",
			"polynomial_eval(p, b) = R.zero",
		},
		Conclusion: "∃c:A. c ∈ R.carrier ∧ polynomial_eval(polynomial_derivative(p), a) = (a - b) * c",
	}, func(ctx *Script, headline string) *GoalStackNode {
		linearDerivative := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A). ∀a:A.",
			Hypotheses: []string{"a ∈ R.carrier"},
			Conclusion: "polynomial_derivative(«linear»(a)) = basis_vector(0)",
		}, func(b *Argument, R comm_ring.CommRingFact[on.R], a *Member[A, on.R]) {
			b.Do(Funext())
			b.FixAs[Nat]("n")
			b.Do(Simp(
				Fwd(polynomial.PolynomialDerivativeDef),
				Fwd(vec_space.VecSubDef),
				Fwd(vec_space.VecScalarMulDef),
				Fwd(vec_space.BasisVectorDef)))
			b.Cases(b.TermAs[Bool]("n = 0"))
			b.When(
				"the constant coefficient of the derivative is one",
				func(c *Argument, zero Fact) {
					c.Show(
						"the first coefficient differentiates to one",
						zero.Subst(),
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						ByArith(R, a))
				})
			b.Otherwise(
				"higher coefficients differentiate to zero",
				func(c *Argument, nonzero Fact) {
					c.Show(
						"there are no higher coefficients",
						ByArith(R, nonzero, a))
				})
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			domain integral_domain.IntegralDomainFact[on.R],
			p *Arrow[Nat, A],
			a, b *Expr[A],
			pOver, pNonzero, aIn, bIn, distinct, aRoot, bRoot Fact,
		) {
			ring := integral_domain.Ring.Read(domain)
			am, bm := arg.MemberOf[on.R](a, aIn), arg.MemberOf[on.R](b, bIn)
			q, reduced := arg.UnpackAs[Fun[Nat, A]](
				GroupPremises(pOver, pNonzero, aRoot, polynomial_roots.RootFactorization.Read(domain).At(p, am)),
				"q")
			qParts := arg.Conjuncts(
				reduced,
				"q is over R",
				"q is nonzero",
				"p is the linear factor at a times q",
				"the degree drops by one",
				"a is inserted into the roots of q")
			qOver, pFactored := qParts[0], qParts[2]
			line := arg.Conjuncts(
				polynomial_roots.LinearFactor.Read(ring).At(am),
				"f is over R",
				"f is monic",
				"f has degree at most one",
				"f evaluates to the difference",
				"f vanishes at a",
				"f has degree one in a nontrivial ring")
			f, fDef := arg.LetAs[Fun[Nat, A]]("f", "«linear»(a)")
			fOver, fValue, fVanishes := line[0], line[3], line[4]
			qVanishesAtB := arg.Have(
				"q vanishes at b, since b - a is not zero",
				"polynomial_eval(q, b) = R.zero",
				Derive(func(c *Argument) {
					product := c.Have(
						"the value of p at b is (b - a) q(b)",
						"(b - a) * polynomial_eval(q, b) = R.zero",
						By(
							fOver,
							qOver,
							bm,
							bRoot,
							fDef,
							pFactored,
							fValue.At(b),
							polynomial_evaluation.EvalMul.Read(ring).At(f, q, bm)))
					difference := c.Have(
						"b - a is not zero",
						"b - a ≠ R.zero",
						Derive(func(d *Argument) {
							vanishing := d.SupposeNot()
							d.Show(
								"then a and b would be equal",
								ByArith(ring, aIn, bIn, vanishing, distinct))
						}))
					c.Show(
						"the domain has no zero divisors",
						By(
							product,
							difference,
							comm_ring.SubIn.Read(ring).At(bm, am),
							polynomial_evaluation.EvalIn.Read(ring).At(q, bm),
							qOver,
							integral_domain.NoZeroDivisors.Read(domain).AsFact().At(
								c.TermAs[A]("b - a"), c.TermAs[A]("polynomial_eval(q, b)"))))
				}))
			r, reducedAgain := arg.UnpackAs[Fun[Nat, A]](
				GroupPremises(
					qParts[0], qParts[1], qVanishesAtB, polynomial_roots.RootFactorization.Read(domain).At(q, bm)),
				"r")
			rParts := arg.Conjuncts(
				reducedAgain,
				"r is over R",
				"r is nonzero",
				"q is the linear factor at b times r",
				"the degree drops by one",
				"b is inserted into the roots of r")
			rOver, qFactored := rParts[0], rParts[2]
			lineB := arg.Conjuncts(
				polynomial_roots.LinearFactor.Read(ring).At(bm),
				"g is over R",
				"g is monic",
				"g has degree at most one",
				"g evaluates to the difference",
				"g vanishes at b",
				"g has degree one in a nontrivial ring")
			g, _ := arg.LetAs[Fun[Nat, A]]("g", "«linear»(b)")
			qAtA := arg.Have(
				"the value of q at a is (a - b) r(a)",
				"polynomial_eval(q, a) = (a - b) * polynomial_eval(r, a)",
				By(
					lineB[0],
					rOver,
					am,
					qFactored,
					lineB[3].At(a),
					polynomial_evaluation.EvalMul.Read(ring).At(g, r, am)))
			coefficients := arg.Have(
				"the coefficients of f and q lie in R",
				"∀i:num. f(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
				By(fOver, qOver, polynomial.PolynomialOverDef))
			coefficientsInR := arg.Have(
				"the coefficients of q lie in R",
				"∀i:num. q(i) ∈ R.carrier",
				By(coefficients))
			fDerivative := arg.Have(
				"the derivative of f is one",
				"polynomial_derivative(f) = basis_vector(0)",
				By(Normalized, ring, aIn, fDef, At(linearDerivative, arg.TermAs[RingOps[A]]("R"), a)))
			derivative := arg.Have(
				"the derivative of p is q + f q′",
				"polynomial_derivative(p) = q + polynomial_mul(f, polynomial_derivative(q))",
				pFactored.Rw(),
				GroupPremises(coefficients, polynomial.DerivativeMul.Read(ring).AsFact().At(f, q)).Rw(),
				fDerivative.Rw(),
				GroupPremises(coefficientsInR, polynomial.PolynomialOneMul.Read(ring).AsFact().At(q)).Rw(),
				Basic())
			qDerivativeOver := arg.Have(
				"the derivative of q is a polynomial over R",
				"polynomial_over(R.carrier, polynomial_derivative(q))",
				By(qOver, polynomial.DerivativeOverCarrier.Read(ring).AsFact().At(q)))
			productOverR := arg.Have(
				"so is f q′",
				"polynomial_over(R.carrier, polynomial_mul(f, polynomial_derivative(q)))",
				By(
					fOver,
					qDerivativeOver,
					polynomial.PolynomialMulOver.Read(ring).AsFact().At(
						f, arg.TermAs[Fun[Nat, A]]("polynomial_derivative(q)"))))
			factorRoot := arg.Have(
				"f q′ vanishes at a",
				"polynomial_eval(polynomial_mul(f, polynomial_derivative(q)), a) = R.zero",
				By(
					fOver,
					qDerivativeOver,
					am,
					fVanishes,
					polynomial_evaluation.EvalMulRoot.Read(ring).At(
						f, arg.TermAs[Fun[Nat, A]]("polynomial_derivative(q)"), am)))
			value := arg.Have(
				"the value of the derivative of p at a is q(a)",
				"polynomial_eval(polynomial_derivative(p), a) = polynomial_eval(q, a)",
				derivative.Rw(),
				GroupPremises(
					qOver,
					productOverR,
					aIn,
					polynomial_evaluation.EvalAdd.Read(ring).AsFact().At(
						q, arg.TermAs[Fun[Nat, A]]("polynomial_mul(f, polynomial_derivative(q))"), a)).Rw(),
				factorRoot.Rw(),
				ByArith(ring, qOver, polynomial_evaluation.EvalIn.Read(ring).At(q, am)))
			arg.Take(arg.TermAs[A]("polynomial_eval(r, a)"))
			arg.Show(
				"the value of r at a is the cofactor",
				By(rOver, polynomial_evaluation.EvalIn.Read(ring).At(r, am), value, qAtA))
		})
	}),
})}
