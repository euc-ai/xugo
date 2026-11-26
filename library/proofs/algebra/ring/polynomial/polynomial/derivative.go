// derivative.go — the formal derivative: it is additive and takes
// differences to differences, takes the zero polynomial and the constants
// to zero, obeys the product rule, keeps polynomials over a subring,
// vanishes from the degree on and lets a scalar out; and the power rule,
// by which over an integral domain a power of zero derivative, its
// exponent not zero in the ring, has a base of zero derivative.

package polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// DerivativeAdd — the derivative of a sum is the sum of the derivatives,
// for any two sequences with every term in c: each coefficient is the
// numeral times a sum of two coefficients, all members of the ring, and
// the product distributes.
var DerivativeAdd = derivativeAddThm{family.Add(registry.ProofEntry{
	Name: "DerivativeAdd",
	Key:  "prop_4cd7fbf8252e7c8d",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_derivative(p + q) = polynomial_derivative(p) + polynomial_derivative(q)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], given Fact) {
			arg.Show(
				"the two sequences agree at every index",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					members := b.Have(
						"the numeral at suc(i) and the coefficients of p and q there lie in R.carrier",
						"«numeral»(suc(i)) ∈ R.carrier ∧ p(suc(i)) ∈ R.carrier ∧ q(suc(i)) ∈ R.carrier",
						By(
							comm_ring.OneIn.Read(ring),
							given,
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(
								b.TermAs[A]("R.one"), b.TermAs[Nat]("suc(i)"))))
					b.Show(
						"the numeral distributes over the two coefficients",
						Simp(Fwd(PolynomialDerivativeDef), Fwd(vec_space.VecAddDef)),
						ByArith(ring, members))
				}))
		}),
})}

// DerivativeVecZero — the derivative of the zero polynomial is the zero
// polynomial: each of its coefficients is a numeral, a member of c, times
// a zero coefficient.
var DerivativeVecZero = derivativeVecZeroThm{family.Add(registry.ProofEntry{
	Name: "DerivativeVecZero",
	Key:  "prop_97ad180b5a66094a",
	Build: comm_ring.CommRingOn.Law(Statement{
		Conclusion: "polynomial_derivative(vec_zero) = vec_zero",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			zero, one := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")
			a.Show(
				"every derivative coefficient of the zero polynomial is zero",
				Funext(),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					successor := b.TermAs[Nat]("suc(i)")
					b.Show(
						"the coefficient formula multiplies a numeral, a member of c, by zero",
						By(
							comm_ring.OneIn.Read(ring),
							PolynomialDerivativeDef.At(
								b.TermAs[Op[A]]("R.add"),
								zero,
								b.TermAs[Op[A]]("R.mul"),
								one,
								b.TermAs[Fun[Nat, A]]("vec_zero"),
								i),
							vec_space.VecZeroDef.At(zero, successor),
							vec_space.VecZeroDef.At(zero, i),
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(one, successor),
							comm_ring.MulRightZeroOn.Read(ring).AsFact().At(b.TermAs[A]("«numeral»(suc(i))"))))
				}))
		}),
})}

// DerivativeSub — the derivative of a difference is the difference of
// the derivatives, for any two sequences with every term in c: each
// coefficient is the numeral times a difference of two coefficients, all
// members of the ring, and the product distributes.
var DerivativeSub = derivativeSubThm{family.Add(registry.ProofEntry{
	Name: "DerivativeSub",
	Key:  "prop_5117385b8ed2ca2d",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_derivative(p - q) = polynomial_derivative(p) - polynomial_derivative(q)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], given Fact) {
			arg.Show(
				"the two sequences agree at every index",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					members := b.Have(
						"the numeral at suc(i) and the coefficients of p and q there lie in R.carrier",
						"«numeral»(suc(i)) ∈ R.carrier ∧ p(suc(i)) ∈ R.carrier ∧ q(suc(i)) ∈ R.carrier",
						By(
							comm_ring.OneIn.Read(ring),
							given,
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(
								b.TermAs[A]("R.one"), b.TermAs[Nat]("suc(i)"))))
					b.Show(
						"the numeral distributes over the difference of the two coefficients",
						Simp(Fwd(PolynomialDerivativeDef), Fwd(vec_space.VecSubDef)),
						ByArith(ring, members))
				}))
		}),
})}

// DerivativeConstant — the derivative of a constant polynomial is zero:
// each of its coefficients is a numeral times a coefficient of the
// constant past index zero, which is a times zero.
var DerivativeConstant = derivativeConstantThm{family.Add(registry.ProofEntry{
	Name: "DerivativeConstant",
	Key:  "prop_bd1ac515c7ae57fa",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a:A.",
		Hypotheses: []string{
			"a ∈ R.carrier",
		},
		Conclusion: "polynomial_derivative(a • basis_vector(0)) = vec_zero",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], a *Expr[A], aIn Fact) {
			arg.Show(
				"every derivative coefficient of the constant is zero",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					numeral := b.Have(
						"the numeral at suc(i) lies in R.carrier",
						"«numeral»(suc(i)) ∈ R.carrier",
						By(
							comm_ring.OneIn.Read(ring),
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(
								b.TermAs[A]("R.one"), b.TermAs[Nat]("suc(i)"))))
					b.Show(
						"past index zero the constant's coefficient is a times zero, and the numeral times zero is zero",
						Simp(
							Fwd(PolynomialDerivativeDef),
							Fwd(vec_space.VecScalarMulDef),
							Fwd(vec_space.BasisVectorDef),
							Fwd(vec_space.VecZeroDef)),
						ByArith(ring, aIn, numeral))
				}))
		}),
})}

// DerivativeMul — the product rule, for any two sequences with every
// term in c: split the weight suc(n) of each convolution term as
// i + (suc(n) − i); the left-weighted sum, past its zero first term and
// shifted down, is the coefficient of p′q, and the right-weighted sum,
// past its zero last term, that of pq′.
var DerivativeMul = derivativeMulThm{family.Add(registry.ProofEntry{
	Name: "DerivativeMul",
	Key:  "prop_e0521322b5132fe3",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p q:(num → A).",
		Hypotheses: []string{
			"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_derivative(polynomial_mul(p, q)) = " +
			"polynomial_mul(polynomial_derivative(p), q) + polynomial_mul(p, polynomial_derivative(q))",
		Abbrev: Abbrev{
			{Name: "upTo", Text: "λn:num. {i:num | i ≤ n}"},
			{Name: "convolutionTerm", Text: "λn:num. λi:num. p(i) * q(suc(n) - i)"},
			{Name: "leftWeighted", Text: "λn:num. λi:num. «numeral»(i) * «convolutionTerm»(n, i)"},
			{Name: "rightWeighted", Text: "λn:num. λi:num. «numeral»(suc(n) - i) * «convolutionTerm»(n, i)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		shift := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀n:num. ∀F:(num → A).",
			Hypotheses: []string{
				"∀i:num. F(i) ∈ R.carrier",
				"F(0) = R.zero",
			},
			Conclusion: "module_sum(R.add, R.zero, «upTo»(suc(n)), F) = " +
				"module_sum(R.add, R.zero, «upTo»(n), λi:num. F(suc(i)))",
		}, func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			n *Expr[Nat],
			F *Arrow[Nat, A],
			values, zero Fact,
		) {
			regular := module.RegularModuleOn.Read(ring)
			forward := a.Have(
				"successor sends the shorter prefix into the longer one",
				"∀i:num. i ≤ n ⇒ suc(i) ≤ suc(n)",
				ByArith())
			predecessor := a.Have(
				"every nonzero index in the longer prefix has its predecessor in the shorter one",
				"∀i:num. i ≤ suc(n) ∧ i ≠ 0 ⇒ i - 1 ≤ n ∧ suc(i - 1) = i",
				ByArith())
			subset := a.Have(
				"the successor image lies in the longer prefix",
				"image(suc, «upTo»(n)) ⊆ «upTo»(suc(n))",
				BySets(forward))
			injective := a.Have(
				"successor is injective on the shorter prefix",
				"injective_on(«upTo»(n), suc)",
				ByArith(functions.InjectiveOnDef))
			covers := a.Have(
				"the successor image contains every bounded nonzero index",
				"∀i:num. i ≤ suc(n) ∧ i ≠ 0 ⇒ i ∈ image(suc, «upTo»(n))",
				BySets(predecessor))
			outside := a.Have(
				"the only discarded index is zero, where F vanishes",
				"∀i:num. i ∈ «upTo»(suc(n)) ∧ i ∉ image(suc, «upTo»(n)) ⇒ F(i) = R.zero",
				BySets(covers, zero))
			a.Show(
				"restrict to the successor image, then reindex it by the shorter prefix",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, image(suc, «upTo»(n)), F)"),
						"discard the zero term",
						By(
							subset,
							outside,
							values,
							num_segment.FiniteBelow.At(a.TermAs[Nat]("suc(n)")),
							module.ModuleSumSupport.Read(regular).At(
								a.TermAs[Set[Nat]]("«upTo»(suc(n))"), a.TermAs[Set[Nat]]("image(suc, «upTo»(n))"), F))),
					FinalLeg(
						"reindex along the injective successor map",
						By(
							injective,
							values,
							num_segment.FiniteBelow.At(n),
							module.ModuleSumImage.Read(regular).At(
								a.TermAs[Set[Nat]]("«upTo»(n)"), a.TermAs[Fun[Nat, Nat]]("suc"), F)))))
		})
		removeLast := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀n:num. ∀F:(num → A).",
			Hypotheses: []string{
				"∀i:num. F(i) ∈ R.carrier",
				"F(suc(n)) = R.zero",
			},
			Conclusion: "module_sum(R.add, R.zero, «upTo»(suc(n)), F) = " +
				"module_sum(R.add, R.zero, «upTo»(n), F)",
		}, func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			n *Expr[Nat],
			F *Arrow[Nat, A],
			values, zero Fact,
		) {
			subset := a.Have(
				"the shorter prefix lies in the longer one",
				"«upTo»(n) ⊆ «upTo»(suc(n))",
				ByArith(set_basic.SubsetDef))
			endpoint := a.Have(
				"an index discarded from the longer prefix is its last index",
				"∀i:num. i ≤ suc(n) ∧ ¬(i ≤ n) ⇒ i = suc(n)",
				ByArith())
			outside := a.Have(
				"F vanishes at the discarded index",
				"∀i:num. i ∈ «upTo»(suc(n)) ∧ i ∉ «upTo»(n) ⇒ F(i) = R.zero",
				By(Normalized, endpoint, zero))
			a.Show(
				"discard the zero last term",
				By(
					subset,
					outside,
					values,
					num_segment.FiniteBelow.At(a.TermAs[Nat]("suc(n)")),
					module.ModuleSumSupport.Read(module.RegularModuleOn.Read(ring)).At(
						a.TermAs[Set[Nat]]("«upTo»(suc(n))"), a.TermAs[Set[Nat]]("«upTo»(n)"), F)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p, q *Arrow[Nat, A],
			coefficients Fact,
		) {
			additive := comm_ring.AddMonoidOn.Read(ring)
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			regular := module.RegularModuleOn.Read(ring)
			one := a.MemberOf[on.R](a.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			numerals := a.Have(
				"all natural-number weights lie in the ring",
				"∀i:num. «numeral»(i) ∈ R.carrier",
				a.ForEach(func(i *Expr[Nat]) Action { return By(comm_monoid.PowIn.Read(additive).At(one, i)) }))
			products := a.Have(
				"every product of coefficients lies in the ring",
				"∀i j:num. p(i) * q(j) ∈ R.carrier",
				By(coefficients, comm_ring.MulIn.Read(ring)))
			weighted := a.Have(
				"a numeral times any product of coefficients lies in the ring",
				"∀i j k:num. «numeral»(i) * (p(j) * q(k)) ∈ R.carrier",
				By(coefficients, numerals, comm_ring.MulIn.Read(ring)))
			zeroWeight := a.Have(
				"the zero index has weight zero",
				"«numeral»(0) = R.zero",
				By(comm_monoid.MonoidPowDef))
			a.Do(Funext())
			n := a.FixAs[Nat]("n")
			termSplit := a.Have(
				"the weight suc(n) of each convolution term splits as i + (suc(n) − i)",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i ≤ suc(n)",
					},
					Conclusion: "«numeral»(suc(n)) * «convolutionTerm»(n, i) = " +
						"«leftWeighted»(n, i) + «rightWeighted»(n, i)",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					below := b.Assume()
					remaining := b.TermAs[Nat]("suc(n) - i")
					indexSplit := b.Have(
						"the two convolution indices add to the derivative index",
						"i + (suc(n) - i) = suc(n)",
						ByArith(below))
					weightSplit := b.Have(
						"so the derivative weight is the sum of the two index weights",
						"«numeral»(suc(n)) = «numeral»(i) + «numeral»(suc(n) - i)",
						By(
							comm_ring.OneIn.Read(ring),
							indexSplit,
							comm_monoid.PowAddOn.Read(additive).AsFact().At(b.TermAs[A]("R.one"), i, remaining)))
					b.Show(
						"right distributivity splits the weighted term",
						By(
							weightSplit,
							numerals.At(i),
							numerals.At(remaining),
							products.At(i, remaining),
							comm_ring.RightDistribOn.Read(ring).AsFact().At(
								b.TermAs[A]("«numeral»(i)"),
								b.TermAs[A]("«numeral»(suc(n) - i)"),
								b.TermAs[A]("«convolutionTerm»(n, i)"))))
				}))
			leftClaim := a.Have(
				"the left-weighted sum is the coefficient at n of p′q",
				"module_sum(R.add, R.zero, «upTo»(suc(n)), «leftWeighted»(n)) = "+
					"polynomial_mul(polynomial_derivative(p), q, n)",
				Derive(func(b *Argument) {
					firstZero := b.Have(
						"the first left-weighted term vanishes",
						"«leftWeighted»(n, 0) = R.zero",
						Simp(Fwd(zeroWeight)),
						By(products, comm_ring.MulLeftZeroOn.Read(ring)))
					shiftIndex := b.Have(
						"successor subtraction shifts both indices down once",
						"∀i:num. suc(n) - suc(i) = n - i",
						ByArith())
					leftTerm := b.Have(
						"a shifted left-weighted term is a term of the convolution of p′ and q",
						"∀i:num. «leftWeighted»(n, suc(i)) = polynomial_derivative(p, i) * q(n - i)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							successor := c.TermAs[Nat]("suc(i)")
							c.Show(
								"associate the numeral with the coefficient of p",
								shiftIndex.At(i).Rw(),
								Simp(Fwd(PolynomialDerivativeDef)),
								By(
									comm_monoid.AssocOn.Read(multiplicative),
									numerals.At(successor),
									coefficients.At(successor),
									coefficients.At(c.TermAs[Nat]("n - i"))))
						}))
					b.Show(
						"drop the zero first term and shift, then read the convolution term by term",
						CalcEq(
							Leg(
								b.TermAs[A]("module_sum(R.add, R.zero, «upTo»(n), λi:num. «leftWeighted»(n, suc(i)))"),
								"shift the left-weighted sum past its zero first term",
								By(weighted, firstZero, Read(shift, ring).At(n, b.TermAs[Fun[Nat, A]]("«leftWeighted»(n)")))),
							FinalLeg(
								"the shifted sum is the coefficient of the convolution of p′ and q",
								Simp(Fwd(PolynomialMulDef)),
								By(leftTerm, module.ModuleSumCongruence))))
				}))
			rightClaim := a.Have(
				"the right-weighted sum is the coefficient at n of pq′",
				"module_sum(R.add, R.zero, «upTo»(suc(n)), «rightWeighted»(n)) = "+
					"polynomial_mul(p, polynomial_derivative(q), n)",
				Derive(func(b *Argument) {
					lastIndex := b.Have(
						"the second index at the last term is zero",
						"suc(n) - suc(n) = 0",
						ByArith())
					lastZero := b.Have(
						"the last right-weighted term vanishes",
						"«rightWeighted»(n, suc(n)) = R.zero",
						Simp(Fwd(lastIndex), Fwd(zeroWeight)),
						By(products, comm_ring.MulLeftZeroOn.Read(ring)))
					raiseIndex := b.Have(
						"before the last index, the second index is a successor",
						"∀i:num. i ≤ n ⇒ suc(n) - i = suc(n - i)",
						ByArith())
					rightTerm := b.Have(
						"a right-weighted term is a term of the convolution of p and q′",
						"∀i:num. i ≤ n ⇒ «rightWeighted»(n, i) = p(i) * polynomial_derivative(q, n - i)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							c.Assume()
							c.Show(
								"commute the numeral past the coefficient of p",
								Simp(Fwd(raiseIndex), Fwd(PolynomialDerivativeDef)),
								By(
									comm_monoid.LeftCommOn.Read(multiplicative),
									numerals.At(c.TermAs[Nat]("suc(n - i)")),
									coefficients.At(i),
									coefficients.At(c.TermAs[Nat]("suc(n - i)"))))
						}))
					b.Show(
						"drop the zero last term, then read the convolution term by term",
						CalcEq(
							Leg(
								b.TermAs[A]("module_sum(R.add, R.zero, «upTo»(n), «rightWeighted»(n))"),
								"restrict the right-weighted sum past its zero last term",
								By(weighted, lastZero, Read(removeLast, ring).At(n, b.TermAs[Fun[Nat, A]]("«rightWeighted»(n)")))),
							FinalLeg(
								"the restricted sum is the coefficient of the convolution of p and q′",
								Simp(Fwd(PolynomialMulDef)),
								By(rightTerm, module.ModuleSumCongruence))))
				}))
			a.Show(
				"the derivative coefficient is the weighted sum split in two, and the two claims read the halves",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, «upTo»(suc(n)), λi:num. «numeral»(suc(n)) * «convolutionTerm»(n, i))"),
						"open the derivative and convolution coefficients, and move the weight suc(n) into the finite sum",
						Simp(Fwd(PolynomialDerivativeDef), Fwd(PolynomialMulDef)),
						By(
							products,
							numerals,
							num_segment.FiniteBelow.At(a.TermAs[Nat]("suc(n)")),
							module.ModuleSumSmul.Read(regular).AsFact().At(
								a.TermAs[Set[Nat]]("«upTo»(suc(n))"),
								a.TermAs[A]("«numeral»(suc(n))"),
								a.TermAs[Fun[Nat, A]]("«convolutionTerm»(n)")))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, «upTo»(suc(n)), λi:num. «leftWeighted»(n, i) + «rightWeighted»(n, i))"),
						"split each weight as i + (suc(n) − i)",
						By(termSplit, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, «upTo»(suc(n)), «leftWeighted»(n)) + "+
								"module_sum(R.add, R.zero, «upTo»(suc(n)), «rightWeighted»(n))"),
						"sum the two weighted families separately",
						By(
							weighted,
							num_segment.FiniteBelow.At(a.TermAs[Nat]("suc(n)")),
							module.ModuleSumAdd.Read(regular).At(
								a.TermAs[Set[Nat]]("«upTo»(suc(n))"),
								a.TermAs[Fun[Nat, A]]("«leftWeighted»(n)"),
								a.TermAs[Fun[Nat, A]]("«rightWeighted»(n)")))),
					FinalLeg(
						"the two claims give the coefficients at n of p′q and pq′, whose sum is the coefficient of the sum",
						Simp(Fwd(leftClaim), Fwd(rightClaim), Fwd(vec_space.VecAddDef)),
						Basic())))
		})
	}),
})}

// DerivativeOver — differentiation preserves polynomials over a subring:
// natural numerals lie in the subring, and a coefficient past the
// support bound is a ring element times zero.
var DerivativeOver = derivativeOverThm{family.Add(registry.ProofEntry{
	Name: "DerivativeOver",
	Key:  "prop_14862096ff8a6a0b",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀K:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"subring(R, K)",
			"polynomial_over(K, p)",
		},
		Conclusion: "polynomial_over(K, polynomial_derivative(p))",
	}, func(
		a *Argument,
		ring comm_ring.CommRingFact[on.R],
		K *Expr[Set[A]],
		p *Arrow[Nat, A],
		sub, poly Fact,
	) {
		zero := a.TermAs[A]("R.zero")
		numerals := a.Have(
			"each natural numeral lies in K",
			"∀m:num. «numeral»(m) ∈ K",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				b.Induct(m)
				b.Base(
					"the zero numeral is the zero of the subring",
					Simp(Fwd(comm_monoid.MonoidPowDef)),
					By(comm_ring.SubringZero.Read(sub)))
				b.Step(
					"the next numeral adds the subring one to the preceding numeral",
					func(c *Argument, ih Fact) {
						c.Show(
							"the subring one plus the preceding numeral, a member of K, lies in K",
							Simp(Fwd(comm_monoid.MonoidPowDef)),
							By(comm_ring.SubringOne.Read(sub), comm_ring.SubringAdd.Read(sub), ih))
					})
			}))
		over := a.Conjuncts(
			a.Unfolded(poly, PolynomialOverDef),
			"p vanishes from some index on",
			"every coefficient of p lies in K")
		n, bounded := a.UnpackAs[Nat](over[0], "n")
		coefficients := over[1]
		derivativeCoefficients := a.Have(
			"a derivative coefficient is a product of two members of K",
			"∀i:num. polynomial_derivative(p, i) ∈ K",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				next := b.TermAs[Nat]("suc(i)")
				b.Show(
					"the numeral multiplies the next coefficient of p",
					Simp(Fwd(PolynomialDerivativeDef)),
					By(comm_ring.SubringMul.Read(sub), coefficients.At(next), numerals.At(next)))
			}))
		tail := a.Unfolded(bounded, vec_space.VecDef)
		derivativeBounded := a.Have(
			"the derivative also vanishes from n on",
			"vec⟨n⟩(polynomial_derivative(p))",
			Simp(Fwd(vec_space.VecDef)),
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				past := b.Assume()
				next := b.TermAs[Nat]("suc(i)")
				coefficientZero := b.Have(
					"the successor index is also past n, so the next coefficient of p is zero",
					"p(suc(i)) = R.zero",
					By(tail.At(next), past, nat_order.LessEqSucClause.At(n, i)))
				numeralIn := b.Have(
					"the numeral in K belongs to the ambient ring carrier",
					"«numeral»(suc(i)) ∈ R.carrier",
					By(comm_ring.SubringSubset.Read(sub), numerals.At(next), set_basic.SubsetDef))
				b.Show(
					"the derivative coefficient is a ring element times zero",
					Simp(Fwd(PolynomialDerivativeDef)),
					coefficientZero.Rw(),
					By(comm_ring.MulRightZeroOn.Read(ring), numeralIn))
			}))
		a.Show(
			"finite support and coefficients in K give a polynomial over K",
			By(
				derivativeCoefficients,
				derivativeBounded,
				PolynomialOverDef.At(zero, K, a.TermAs[Fun[Nat, A]]("polynomial_derivative(p)"))))
	}),
})}

// DerivativeOverCarrier — the derivative of a polynomial over c is over c:
// DerivativeOver at the carrier, a subring of itself.
var DerivativeOverCarrier = derivativeOverCarrierThm{family.Add(registry.ProofEntry{
	Name: "DerivativeOverCarrier",
	Key:  "prop_3190ba5c50afdbb2",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_over(R.carrier, polynomial_derivative(p))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], over Fact) {
			a.Show(
				"the carrier is a subring of itself",
				By(
					comm_ring.CarrierSubring.Read(ring),
					over,
					DerivativeOver.Read(ring).At(a.TermAs[Set[A]]("R.carrier"), p)))
		}),
})}

// DerivativeVec — the derivative vanishes from the degree on: its
// coefficient at i uses p at suc(i), beyond p's last nonzero coefficient.
var DerivativeVec = derivativeVecThm{family.Add(registry.ProofEntry{
	Name: "DerivativeVec",
	Key:  "prop_951c66d46a9c2696",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "vec⟨polynomial_degree(p)⟩(polynomial_derivative(p))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], over Fact) {
			zero, one := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")
			bounded := a.Have(
				"p vanishes past its degree",
				"vec⟨suc(polynomial_degree(p))⟩(p)",
				By(over, DegreeVec.At(zero, a.TermAs[Set[A]]("R.carrier"), p)))
			tail := a.Unfolded(bounded, vec_space.VecDef)
			a.Show(
				"each derivative coefficient at or beyond the degree is zero",
				Simp(Fwd(vec_space.VecDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					past := b.Assume()
					next := b.TermAs[Nat]("suc(i)")
					nextPast := b.Have(
						"the next index is beyond the last possible nonzero coefficient of p",
						"suc(polynomial_degree(p)) ≤ suc(i)",
						ByArith(past))
					b.Show(
						"the derivative coefficient is a carrier numeral times a zero coefficient",
						By(
							comm_ring.OneIn.Read(ring),
							nextPast,
							tail.At(next),
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(one, next),
							PolynomialDerivativeDef.At(b.TermAs[Op[A]]("R.add"), zero, b.TermAs[Op[A]]("R.mul"), one, p, i),
							comm_ring.MulRightZeroOn.Read(ring).AsFact().At(b.TermAs[A]("«numeral»(suc(i))"))))
				}))
		}),
})}

// DerivativeScalar — a scalar comes out of the derivative of a sequence
// with every term in c: each coefficient is a product of the numeral,
// the scalar and a coefficient of p, all members of the ring, and the
// product regroups.
var DerivativeScalar = derivativeScalarThm{family.Add(registry.ProofEntry{
	Name: "DerivativeScalar",
	Key:  "prop_f56b63822142cca0",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a:A. ∀p:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"∀i:num. p(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_derivative(a • p) = a • polynomial_derivative(p)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], a *Expr[A], p *Arrow[Nat, A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a lies in R.carrier",
				"every coefficient of p lies in R.carrier")
			aIn, pIn := parts[0], parts[1]
			arg.Show(
				"the two sequences agree at every index",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					members := b.Have(
						"the numeral at suc(i) and the coefficient of p there lie in R.carrier",
						"«numeral»(suc(i)) ∈ R.carrier ∧ p(suc(i)) ∈ R.carrier",
						By(
							comm_ring.OneIn.Read(ring),
							pIn,
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(
								b.TermAs[A]("R.one"), b.TermAs[Nat]("suc(i)"))))
					b.Show(
						"the numeral, a and p(suc(i)) regroup in the ring",
						Simp(Fwd(PolynomialDerivativeDef), Fwd(vec_space.VecScalarMulDef)),
						ByArith(ring, aIn, members))
				}))
		}),
})}

// DerivativePow — the power rule: the derivative of the (n + 1)-th power
// is n + 1 times the n-th power times the derivative. By induction on n,
// the product rule taking p^(n+2) = p · p^(n+1) to one copy of
// p^(n+1) · p′ more than the induction hypothesis gives.
var DerivativePow = derivativePowThm{family.Add(registry.ProofEntry{
	Name: "DerivativePow",
	Key:  "prop_51128dda227d4fd1",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_derivative(polynomial_pow(p, suc(n))) = " +
			"«numeral»(suc(n)) • polynomial_mul(polynomial_pow(p, n), polynomial_derivative(p))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], n *Expr[Nat], p *Arrow[Nat, A], over Fact) {
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			derivative := a.TermAs[Fun[Nat, A]]("polynomial_derivative(p)")
			additive := comm_ring.AddMonoidOn.Read(ring)
			one := a.MemberOf[on.R](a.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			coefficients := a.Have(
				"every coefficient of p and of its derivative lies in R.carrier",
				"∀i:num. p(i) ∈ R.carrier ∧ polynomial_derivative(p, i) ∈ R.carrier",
				By(
					over,
					DerivativeOverCarrier.Read(ring).At(p),
					PolynomialOverDef.At(zero, c, p),
					PolynomialOverDef.At(zero, c, derivative)))
			powers := a.Have(
				"so does every coefficient of every power of p",
				"∀m i:num. polynomial_pow(p, m, i) ∈ R.carrier",
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]("m")
					b.Show(
						"a power of p is a polynomial over R.carrier",
						By(
							over,
							PolynomialPowOver.Read(ring).At(m, p),
							PolynomialOverDef.At(zero, c, b.TermAs[Fun[Nat, A]]("polynomial_pow(p, m)"))))
				}))
			products := a.Have(
				"and every coefficient of a power of p times the derivative",
				"∀m i:num. polynomial_mul(polynomial_pow(p, m), polynomial_derivative(p), i) ∈ R.carrier",
				By(powers, coefficients, SeriesMulIn.Read(ring)))
			a.Induct(n)
			a.Base(
				"at 0 both sides are the derivative of p",
				CalcEq(
					Leg(
						derivative,
						"the first power of p is p times the one polynomial, which is p",
						By(
							powers,
							coefficients,
							PolynomialPowSuc.Read(ring).At(a.TermAs[Nat]("0"), p),
							PolynomialPowZero.Read(ring).At(p),
							PolynomialMulComm.Read(ring).At(p, a.TermAs[Fun[Nat, A]]("polynomial_pow(p, 0)")),
							PolynomialOneMul.Read(ring).At(p))),
					FinalLeg(
						"the numeral 1 is R.one, which scales nothing, and the one polynomial times p′ is p′",
						By(
							coefficients,
							comm_monoid.MonoidPowDef,
							comm_monoid.RightIdentityOn.Read(additive).At(one),
							PolynomialPowZero.Read(ring).At(p),
							PolynomialOneMul.Read(ring).At(derivative),
							vec_space.SmulOneOn.Read(ring).At(derivative)))))
			a.Step(
				"one more factor of p contributes one more copy of p^(n+1) · p′",
				func(b *Argument, ih Fact) {
					next := b.TermAs[Nat]("suc(n)")
					power, nextPower :=
						b.TermAs[Fun[Nat, A]]("polynomial_pow(p, n)"), b.TermAs[Fun[Nat, A]]("polynomial_pow(p, suc(n))")
					product := b.TermAs[Fun[Nat, A]](
						"polynomial_mul(polynomial_pow(p, suc(n)), polynomial_derivative(p))")
					multiple := comm_monoid.PowIn.Read(additive).At(one, next)
					b.Show(
						"the derivative of p^(n+2) is n + 2 times p^(n+1) · p′",
						CalcEq(
							Leg(
								b.TermAs[Fun[Nat, A]](
									"polynomial_mul(polynomial_derivative(p), polynomial_pow(p, suc(n))) + "+
										"polynomial_mul(p, polynomial_derivative(polynomial_pow(p, suc(n))))"),
								"the product rule, p^(n+2) being p times p^(n+1)",
								By(
									powers,
									coefficients,
									PolynomialPowSuc.Read(ring).At(next, p),
									DerivativeMul.Read(ring).At(p, nextPower))),
							Leg(
								b.TermAs[Fun[Nat, A]](
									"polynomial_mul(polynomial_derivative(p), polynomial_pow(p, suc(n))) + "+
										"«numeral»(suc(n)) • "+
										"polynomial_mul(p, polynomial_mul(polynomial_pow(p, n), polynomial_derivative(p)))"),
								"the induction hypothesis, the scalar n + 1 then passing out of the product with p",
								ih.Rw(),
								By(
									products,
									coefficients,
									PolynomialMulScalar.Read(ring).At(
										multiple,
										p,
										b.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_pow(p, n), polynomial_derivative(p))")))),
							Leg(
								b.TermAs[Fun[Nat, A]](
									"polynomial_mul(polynomial_pow(p, suc(n)), polynomial_derivative(p)) + "+
										"«numeral»(suc(n)) • polynomial_mul(polynomial_pow(p, suc(n)), polynomial_derivative(p))"),
								"commute the first product, and regroup p · (p^n · p′) as p^(n+1) · p′",
								By(
									powers,
									coefficients,
									PolynomialMulComm.Read(ring).At(derivative, nextPower),
									PolynomialMulAssoc.Read(ring).At(p, power, derivative),
									PolynomialPowSuc.Read(ring).At(n, p))),
							FinalLeg(
								"R.one, which scales nothing, and the numeral n + 1 add up to the numeral n + 2",
								By(
									products,
									comm_monoid.MonoidPowDef,
									vec_space.SmulOneOn.Read(ring).At(product),
									vec_space.SmulAddRightOn.Read(ring).At(one, multiple, product)))))
				})
		}),
})}

// PowDerivativeZero — over an integral domain, for an exponent that is
// not zero in the ring, a power of zero derivative has a base of zero
// derivative.
var PowDerivativeZero = powDerivativeZeroThm{family.Add(registry.ProofEntry{
	Name: "PowDerivativeZero",
	Reading: "Both hypotheses are load-bearing. In characteristic ℓ the derivative of " +
		"t^ℓ is R.zero while that of t is R.one; over ℤ/4, (1 + 2t)² = 1 has derivative " +
		"R.zero while 1 + 2t has derivative 2, the exponent 2 not being R.zero there.",
	Key: "prop_c81938feb29d35ad",
	Deps: []registry.EntryLike{
		DerivativePow,
		PolynomialPowDef,
		comm_monoid.MonoidPowDef,
		PolynomialPowOver,
		PolynomialDomain,
		integral_domain.NoZeroDivisors,
		integral_domain.OneNotZero,
	},
	Build: family.Card(integral_domain.IntegralDomainOn.Statement(Statement{
		Binders: "∀n:num. ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"¬(monoid_pow(R.add, R.zero, R.one, n) = R.zero)",
			"polynomial_derivative(polynomial_pow(p, n)) = vec_zero",
		},
		Conclusion: "polynomial_derivative(p) = vec_zero",
	}),
		"n is not 0, the numeral at 0 being R.zero (MonoidPowDef); at n = suc(m) the power rule "+
			"(DerivativePow) makes the numeral times polynomial_mul(polynomial_pow(p, m), "+
			"polynomial_derivative(p)) R.zero, so the product is R.zero, the numeral being a nonzero "+
			"element of a domain (NoZeroDivisors at each coefficient); then polynomial_pow(p, m) or "+
			"the derivative is R.zero (PolynomialDomain), and polynomial_pow(p, m) is R.zero only "+
			"for p = vec_zero and m > 0 (OneNotZero), whose derivative is R.zero"),
})}
