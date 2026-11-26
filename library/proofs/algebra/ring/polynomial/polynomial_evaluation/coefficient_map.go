// coefficient_map.go — moving the coefficients of a polynomial along a ring
// homomorphism is a homomorphism of polynomial rings, which carries a scalar
// multiple c • p to f(c) times the image of p, the derivative of p to the
// derivative of the image, and a division identity
// c • p = g q + r to the same identity between the images; evaluating at a
// point of the target after it is a homomorphism out of the polynomials
// over the source.

package polynomial_evaluation

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// CoefficientMapHomomorphism — a ring homomorphism f from R to S moves
// polynomials over R to polynomials over S coefficient by coefficient, and that
// map is a homomorphism of polynomial rings: sums and the unit polynomial are
// read at each coefficient, and f passes through the finite convolution sum that
// spells a coefficient of a product.
var CoefficientMapHomomorphism = coefficientMapHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "CoefficientMapHomomorphism",
	Key:  "prop_9fcc81d9fe0ffb7",
	Build: family.Sections(Statement{
		Binders:    "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{"ring_homomorphism(R, S, f)"},
		Conclusion: "ring_homomorphism(polynomial_ring(R), " +
			"    polynomial_ring(S), " +
			"    λp:(num → A). λi:num. f(p(i)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		product := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀f:(A → B). ∀p q:(num → A).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"polynomial_over(R.carrier, p)",
				"polynomial_over(R.carrier, q)",
			},
			Conclusion: "(λn:num. f(polynomial_mul(p, q, n))) = " +
				"polynomial_mul(λi:num. f(p(i)), λi:num. f(q(i)))",
		}, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			S comm_ring.CommRingFact[on.S],
			f *Arrow[A, B],
			p, q *Arrow[Nat, A],
			hom, pOver, qOver Fact,
		) {
			a.Do(Funext())
			n := a.FixAs[Nat]("n")
			a.Do(Simp(Fwd(polynomial.PolynomialMulDef)))
			additive := a.Have(
				"zero and carrier sums are preserved",
				"f(R.zero) = S.zero ∧ (∀u v:A. u ∈ R.carrier ∧ v ∈ R.carrier ⇒ f(R.add(u, v)) = S.add(f(u), f(v)))",
				By(
					hom,
					ring_homomorphism.MapZero.Read(hom),
					ring_homomorphism.RingHomomorphism.At(a.TermAs[RingOps[A]]("R"), a.TermAs[RingOps[B]]("S"), f)))
			coefficients := a.Have(
				"each convolution term belongs to the carrier and its product is preserved",
				"∀i:num. "+
					"    p(i) ∈ R.carrier ∧ "+
					"    q(n - i) ∈ R.carrier ∧ "+
					"    R.mul(p(i), q(n - i)) ∈ R.carrier ∧ "+
					"    f(R.mul(p(i), q(n - i))) = S.mul(f(p(i)), f(q(n - i)))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"apply multiplicativity to the two coefficients",
						By(
							pOver,
							qOver,
							polynomial.PolynomialOverDef.At(b.TermAs[A]("R.zero"), b.TermAs[Set[A]]("R.carrier"), p),
							polynomial.PolynomialOverDef.At(b.TermAs[A]("R.zero"), b.TermAs[Set[A]]("R.carrier"), q),
							comm_ring.MulIn.Read(R).AsFact().At(p.Apply(i), q.Apply(b.TermAs[Nat]("n - i"))),
							ring_homomorphism.MapMul.Read(hom).AsFact().At(p.Apply(i), q.Apply(b.TermAs[Nat]("n - i")))))
				}))
			addS, zeroS := a.TermAs[Fun[B, Fun[B, B]]]("S.add"), a.TermAs[B]("S.zero")
			upToN := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			terms := a.TermAs[Fun[Nat, A]]("λi:num. R.mul(p(i), q(n - i))")
			mappedTerms := a.TermAs[Fun[Nat, B]]("λi:num. f(R.mul(p(i), q(n - i)))")
			productTerms := a.TermAs[Fun[Nat, B]]("λi:num. S.mul(f(p(i)), f(q(n - i)))")
			mappedSum := a.Have(
				"the homomorphism passes through the finite convolution sum",
				"f(module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. R.mul(p(i), q(n - i)))) = "+
					"module_sum(S.add, S.zero, {i:num | i ≤ n}, λi:num. f(R.mul(p(i), q(n - i))))",
				By(
					coefficients,
					additive,
					num_segment.FiniteBelow.At(n),
					module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(R)).At(
						addS, zeroS, f, upToN, terms)))
			a.Show(
				"the image convolution is the target product",
				By(
					mappedSum,
					coefficients,
					module.ModuleSumCongruence.At(addS, zeroS, upToN, mappedTerms, productTerms)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[RingOps[B]],
			f *Arrow[A, B],
			hom Fact,
		) {
			zero, zeroS := a.TermAs[A]("R.zero"), a.TermAs[B]("S.zero")
			carrier, carrierS := a.TermAs[Set[A]]("R.carrier"), a.TermAs[Set[B]]("S.carrier")
			C, CDef := a.LetAs[Fun[Fun[Nat, A], Fun[Nat, B]]]("C", "λp:(num → A). λi:num. f(p(i))")
			keepsUnits := a.Have(
				"f keeps zero and one",
				"f(R.zero) = S.zero ∧ f(R.one) = S.one",
				By(ring_homomorphism.MapOne.Read(hom), ring_homomorphism.MapZero.Read(hom)))
			mapPolynomials := a.Have(
				"coefficient transport sends polynomials over R to polynomials over S",
				"∀p:(num → A). polynomial_over(R.carrier, p) ⇒ polynomial_over(S.carrier, C(p))",
				Derive(func(b *Argument) {
					p := b.FixAs[Fun[Nat, A]]("p")
					pOver := b.Assume()
					b.Show(
						"each coefficient f(p(i)) lies in S, and f keeps zero",
						By(
							Normalized,
							CDef,
							pOver,
							keepsUnits,
							ring_homomorphism.MapIn.Read(hom),
							polynomial.PolynomialOverMap.At(f, zero, zeroS, carrier, carrierS, p)))
				}))
			mapSums := a.Have(
				"coefficient transport preserves polynomial addition",
				Statement{
					Binders: "∀p r:(num → A).",
					Hypotheses: []string{
						"polynomial_over(R.carrier, p)",
						"polynomial_over(R.carrier, r)",
					},
					Conclusion: "C(vec_add(p, r)) = vec_add(C(p), C(r))",
				},
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(CDef), Fwd(vec_space.VecAddDef)))
					p := b.FixAs[Fun[Nat, A]]("p")
					r := b.FixAs[Fun[Nat, A]]("r")
					over := b.Assume()
					b.Do(Funext())
					b.FixAs[Nat]("i")
					b.Do(By(
						over,
						polynomial.PolynomialOverDef.At(zero, carrier, p),
						polynomial.PolynomialOverDef.At(zero, carrier, r),
						At(ring_homomorphism.MapAdd.Read(hom), b.TermAs[A]("p(i)"), b.TermAs[A]("r(i)"))))
				}))
			mapProducts := a.Have(
				"coefficient transport preserves polynomial multiplication",
				Statement{
					Binders: "∀p r:(num → A).",
					Hypotheses: []string{
						"polynomial_over(R.carrier, p)",
						"polynomial_over(R.carrier, r)",
					},
					Conclusion: "C(polynomial_mul(p, r)) = polynomial_mul(C(p), C(r))",
				},
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(CDef)))
					p := b.FixAs[Fun[Nat, A]]("p")
					r := b.FixAs[Fun[Nat, A]]("r")
					over := b.Assume()
					b.Show(
						"the coefficients of a product are moved by the convolution lemma",
						By(
							over,
							hom,
							ring_homomorphism.Source.Read(hom),
							ring_homomorphism.Target.Read(hom),
							At(product, R, S, f, p, r)))
				}))
			mapUnitPolynomial := a.Have(
				"coefficient transport preserves the unit polynomial",
				"C(basis_vector(R.zero, R.one, 0)) = basis_vector(S.zero, S.one, 0)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(CDef), Fwd(vec_space.BasisVectorDef)))
					b.Do(By(keepsUnits))
				}))
			a.Show(
				"C keeps polynomials and preserves sums, products and one",
				By(
					mapSums,
					mapProducts,
					mapPolynomials,
					mapUnitPolynomial,
					polynomial.PolynomialRingOn.Read(ring_homomorphism.Source.Read(hom)),
					polynomial.PolynomialRingOn.Read(ring_homomorphism.Target.Read(hom)),
					ring_homomorphism.RingHomomorphism.At(
						a.TermAs[RingOps[Fun[Nat, A]]]("polynomial_ring(R)"),
						a.TermAs[RingOps[Fun[Nat, B]]]("polynomial_ring(S)"),
						C)))
		})
	}),
})}

// CoefficientMapScalar — moving coefficients along a ring homomorphism f
// carries a scalar multiple c • p to f(c) times the image of p: at each index
// f is multiplicative at c and the coefficient of p.
var CoefficientMapScalar = coefficientMapScalarThm{family.Add(registry.ProofEntry{
	Name: "CoefficientMapScalar",
	Key:  "prop_c62b61f9f58b6a91",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀c:A. ∀p:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"c ∈ R.carrier",
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "(λi:num. f((c • p)(i))) = f(c) • (λi:num. f(p(i)))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		f *Arrow[A, B],
		c *Expr[A],
		p *Arrow[Nat, A],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		cIn, pOver Fact,
	) {
		a.Do(Funext())
		i := a.FixAs[Nat]("i")
		a.Show(
			"at each index, f of a product is the product of the images",
			Simp(Fwd(vec_space.VecScalarMulDef)),
			By(
				cIn,
				pOver,
				polynomial.PolynomialOverDef,
				ring_homomorphism.MapMul.Read(hom).AsFact().At(c, p.Apply(i))))
	}),
})}

// CoefficientMapDerivative — moving coefficients along a ring homomorphism f
// commutes with the formal derivative: the j-th coefficient of the derivative
// is the numeral j + 1 times p(j + 1), and f keeps the numeral and the
// product.
var CoefficientMapDerivative = coefficientMapDerivativeThm{family.Add(registry.ProofEntry{
	Name: "CoefficientMapDerivative",
	Key:  "prop_5d7b8d5ec59e84b3",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀p:(num → A).",
		Hypotheses: []string{"ring_homomorphism(R, S, f)", "polynomial_over(R.carrier, p)"},
		Conclusion: "(λi:num. f(polynomial_derivative(p, i))) = polynomial_derivative(λi:num. f(p(i)))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		f *Arrow[A, B],
		p *Arrow[Nat, A],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		over Fact,
	) {
		source := ring_homomorphism.Source.Read(hom)
		target := ring_homomorphism.Target.Read(hom)
		a.Do(Funext())
		a.FixAs[Nat]("j")
		a.Show(
			"the numeral j + 1 and the coefficient p(j + 1) are both preserved",
			Simp(Fwd(polynomial.PolynomialDerivativeDef)),
			By(
				Normalized,
				source,
				target,
				over,
				hom,
				comm_ring.OneIn.Read(source),
				polynomial.PolynomialOverDef.At(a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier"), p),
				comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(source)).AsFact().At(
					a.TermAs[A]("R.one"), a.TermAs[Nat]("suc(j)")),
				ring_homomorphism.MapMul.Read(hom).AsFact().At(
					a.TermAs[A]("monoid_pow(R.add, R.zero, R.one, suc(j))"), p.Apply(a.TermAs[Nat]("suc(j)"))),
				ring_homomorphism.RingMapNumeral.Read(hom).At(a.TermAs[Nat]("suc(j)"))))
	}),
})}

// CoefficientMapDivision — moving coefficients along a ring homomorphism f
// carries a division c • p = g q + r to f(c) • fp = (fg)(fq) + fr, where fp
// is p with f applied to every coefficient: the coefficient map is a
// homomorphism of polynomial rings (CoefficientMapHomomorphism) and carries
// c • p to f(c) • fp (CoefficientMapScalar).
var CoefficientMapDivision = coefficientMapDivisionThm{family.Add(registry.ProofEntry{
	Name: "CoefficientMapDivision",
	Key:  "prop_33f75e003dd1e44a",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀c:A. ∀p g q r:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"c ∈ R.carrier",
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, g)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, r)",
			"c • p = polynomial_mul(g, q) + r",
		},
		Conclusion: "f(c) • (λi:num. f(p(i))) = " +
			"polynomial_mul(λi:num. f(g(i)), λi:num. f(q(i))) + (λi:num. f(r(i)))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		f *Arrow[A, B],
		c *Expr[A],
		p, g, q, r *Arrow[Nat, A],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		cIn, pOver, gOver, qOver, rOver, divided Fact,
	) {
		mapped := CoefficientMapHomomorphism.Read(hom)
		a.Show(
			"the image of c • p is f(c) • fp, and the image of g q + r is (fg)(fq) + fr",
			By(
				hom,
				pOver,
				gOver,
				qOver,
				rOver,
				divided,
				CoefficientMapScalar.Read(hom).At(a.MemberOf[on.R](c, cIn), p),
				ring_homomorphism.MapAdd.Read(mapped).AsFact().At(a.TermAs[Fun[Nat, A]]("polynomial_mul(g, q)"), r),
				ring_homomorphism.MapMul.Read(mapped).AsFact().At(g, q),
				polynomial.PolynomialMulOver.Read(ring_homomorphism.Source.Read(hom)).At(g, q)))
	}),
})}

// TransportedEvaluationHomomorphism — moving coefficients along a ring
// homomorphism f from R to S and evaluating at a point w of S is a homomorphism
// from the polynomials over R to S, the composite of two homomorphisms.
var TransportedEvaluationHomomorphism = transportedEvaluationHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "TransportedEvaluationHomomorphism",
	Key:  "prop_445b8b96f2cd2be6",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀w:B.",
		Hypotheses: []string{"ring_homomorphism(R, S, f)", "w ∈ S.carrier"},
		Conclusion: "ring_homomorphism(polynomial_ring(R), " +
			"    S, " +
			"    λp:(num → A). polynomial_eval(λi:num. f(p(i)), w))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		f *Arrow[A, B],
		w *Expr[B],
		hom, wIn Fact,
	) {
		target := ring_homomorphism.Target.Read(hom)
		transport := a.Have(
			"moving coefficients is a homomorphism of polynomial rings",
			"ring_homomorphism(polynomial_ring(R), polynomial_ring(S), λp:(num → A). λi:num. f(p(i)))",
			By(hom, At(CoefficientMapHomomorphism, R, S, f)))
		evaluation := a.Have(
			"evaluation at w is a homomorphism",
			"ring_homomorphism(polynomial_ring(S), S, λq:(num → B). polynomial_eval(q, w))",
			By(wIn, EvalHomomorphism.Read(target).At(a.MemberOf[on.Any](w, wIn))))
		a.Show(
			"the composite of the two",
			By(
				Normalized,
				transport,
				evaluation,
				ring_homomorphism.RingHomCompose.At(
					a.TermAs[RingOps[Fun[Nat, A]]]("polynomial_ring(R)"),
					a.TermAs[RingOps[Fun[Nat, B]]]("polynomial_ring(S)"),
					S,
					a.TermAs[Fun[Fun[Nat, A], Fun[Nat, B]]]("λp:(num → A). λi:num. f(p(i))"),
					a.TermAs[Fun[Fun[Nat, B], B]]("λq:(num → B). polynomial_eval(q, w)"))))
	}),
})}
