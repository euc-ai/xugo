// parameters.go — integral primitive elements and Galois closures over a separating parameter.

package separating_parameter

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// IntegralPrimitiveElement — a finite separable extension K of the rational
// function field k(t), t transcendental over k, has a primitive element z
// whose minimal polynomial over k(t) is monic of degree [K : k(t)], separable,
// and has its coefficients in the polynomial ring k[t]. The powers of t are
// distinct, so k(t) is infinite and the primitive element theorem gives a
// generator of K; scaling it by a common denominator of its minimal
// polynomial makes the coefficients polynomials in t.
var IntegralPrimitiveElement = integralPrimitiveElementThm{family.Add(registry.ProofEntry{
	Name: "IntegralPrimitiveElement",
	Key:  "prop_fa84b00ef729b5ae",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"t ∈ K",
			"¬algebraic_over(M, k, t)",
			"finite_extension(M, field_adjoin(M, k, {t}), K)",
			"∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {t}), x)",
		},
		Conclusion: "∃z:A. " +
			"    z ∈ K ∧ " +
			"    field_adjoin(M, field_adjoin(M, k, {t}), {z}) = K ∧ " +
			"    polynomial_over(polynomial_image(field_ring(M), k, t), " +
			"        minimal_polynomial(M, field_adjoin(M, k, {t}), z)) ∧ " +
			"    polynomial_monic(minimal_polynomial(M, field_adjoin(M, k, {t}), z)) ∧ " +
			"    polynomial_degree(minimal_polynomial(M, field_adjoin(M, k, {t}), z)) = " +
			"    extension_degree(M, field_adjoin(M, k, {t}), K) ∧ " +
			"    polynomial_separable(restrict_ring(field_ring(M), field_adjoin(M, k, {t})), " +
			"        minimal_polynomial(M, field_adjoin(M, k, {t}), z))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		// When c·p has its coefficients in S and p is monic of degree n, the
		// scaled polynomial with coefficients c^(n - i)·p(i) is monic of degree
		// n with its coefficients in S.
		scaledPolynomial := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀S:set(A). ∀c:A. ∀n:num. ∀p:(num → A).",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"c ∈ S",
				"polynomial_over(L.carrier, p)",
				"p(n) = L.one",
				"∀i:num. c * p(i) ∈ S",
			},
			Conclusion: "polynomial_over(S, " +
				"    λi:num. COND(i ≤ n, monoid_pow(L.mul, L.one, c, n - i) * p(i), L.zero)) ∧ " +
				"polynomial_monic(λi:num. COND(i ≤ n, monoid_pow(L.mul, L.one, c, n - i) * p(i), L.zero)) ∧ " +
				"polynomial_degree(λi:num. COND(i ≤ n, monoid_pow(L.mul, L.one, c, n - i) * p(i), L.zero)) = n",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			S *Expr[Set[A]],
			c *Expr[A],
			n *Expr[Nat],
			p *Arrow[Nat, A],
			subring, cInS, coefficients, leading, scaledIn Fact,
		) {
			ring := field.RingOn.Read(L)
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			fieldRing := a.TermAs[comm_ring.RingOps[A]]("field_ring(L)")
			q, qDef := a.LetAs[Fun[Nat, A]](
				"q", "λi:num. COND(i ≤ n, monoid_pow(L.mul, L.one, c, n - i) * p(i), L.zero)")
			restricted := a.Have(
				"S is a commutative ring under the operations of L",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subring, comm_ring.SubringRingOn.Read(ring).At(S)))
			top := a.Have(
				"n is the top index, where c^(n - n) = c⁰",
				"n ≤ n ∧ n - n = 0",
				ByArith())
			qLeading := a.Have(
				"the coefficient of q at n is c⁰·p(n) = 1",
				"q(n) = L.one",
				Simp(Fwd(qDef), Fwd(top), Fwd(leading), Fwd(comm_monoid.MonoidPowDef)),
				ByArith(L))
			qSupport := a.Have(
				"q vanishes from n + 1 on",
				"vec⟨suc(n)⟩(q)",
				Simp(Fwd(vec_space.VecDef)),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					beyond := b.Assume()
					past := b.Have(
						"i lies past n",
						"¬(i ≤ n)",
						ByArith(beyond))
					b.Show(
						"past n the coefficient of q is zero",
						By(past, qDef))
				}))
			pBoth := a.Have(
				"each coefficient of p lies in L, and c times it lies in S",
				"∀i:num. p(i) ∈ L.carrier ∧ c * p(i) ∈ S",
				By(coefficients, scaledIn, polynomial.PolynomialOverDef))
			cInL := a.Have(
				"c lies in L",
				"c ∈ L.carrier",
				BySets(subring, cInS, comm_ring.SubringSubset.At(fieldRing, S)))
			cm := a.MemberOf[on.L](c, cInL)
			qInS := a.Have(
				"every coefficient of q lies in S",
				"∀i:num. q(i) ∈ S",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Cases(b.TermAs[Bool]("i = n"))
					b.When(
						"the coefficient at n is one",
						func(d *Argument, atTop Fact) {
							d.Show(
								"one lies in the subring S",
								By(qLeading, atTop, subring, comm_ring.SubringOne.At(fieldRing, S)))
						})
					b.Otherwise(
						"away from n the coefficient is integral or zero",
						func(d *Argument, notTop Fact) {
							d.Cases(d.TermAs[Bool]("i < n"))
							d.When(
								"below n one factor c makes c·p(i) integral",
								func(e *Argument, below Fact) {
									split := e.Have(
										"i ≤ n and n - i = (n - i - 1) + 1",
										"i ≤ n ∧ n - i - 1 + 1 = n - i",
										ByArith(below))
									peel := e.Have(
										"c^(n - i) = c^(n - i - 1)·c",
										"monoid_pow(L.mul, L.one, c, n - i) = monoid_pow(L.mul, L.one, c, n - i - 1) * c",
										By(
											split,
											comm_monoid.PowAddOn.Read(multiplicative).At(cm, e.TermAs[Nat]("n - i - 1"), e.TermAs[Nat]("1")),
											comm_monoid.PowOneOn.Read(multiplicative).At(cm)))
									regroup := e.Have(
										"q(i) = c^(n - i - 1)·(c·p(i))",
										"q(i) = monoid_pow(L.mul, L.one, c, n - i - 1) * (c * p(i))",
										By(
											pBoth.At(i),
											peel,
											qDef,
											cInL,
											split,
											comm_monoid.PowIn.Read(multiplicative).At(cm, e.TermAs[Nat]("n - i - 1")),
											comm_monoid.AssocOn.Read(multiplicative).AsFact().At(
												e.TermAs[A]("monoid_pow(L.mul, L.one, c, n - i - 1)"), c, e.TermAs[A]("p(i)"))))
									power := e.Have(
										"c^(n - i - 1) lies in S",
										"monoid_pow(L.mul, L.one, c, n - i - 1) ∈ S",
										By(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(restricted)).At(
											proof.MemberOf(c, cInS), e.TermAs[Nat]("n - i - 1"))))
									e.Show(
										"a product of two points of S lies in S",
										By(
											pBoth.At(i),
											regroup,
											power,
											subring,
											comm_ring.SubringMul.At(
												fieldRing, S, e.TermAs[A]("monoid_pow(L.mul, L.one, c, n - i - 1)"), e.TermAs[A]("c * p(i)"))))
								})
							d.Otherwise(
								"above n the coefficient is zero, which S contains",
								func(e *Argument, notBelow Fact) {
									past := e.Have(
										"i lies past n",
										"¬(i ≤ n)",
										ByArith(notBelow, notTop))
									e.Show(
										"zero lies in the subring S",
										By(past, qDef, subring, comm_ring.SubringZero.At(fieldRing, S)))
								})
						})
				}))
			qOver := a.Have(
				"q is a polynomial over S",
				"polynomial_over(S, q)",
				By(Normalized, qInS, qSupport, polynomial.PolynomialOverDef))
			degree := a.Have(
				"q has degree exactly n, vanishing past n and not at n",
				"polynomial_degree(q) = n",
				By(qSupport, qLeading, field.OneNotZeroOn.Read(L), polynomial.DegreeExact.Read(qOver).At(n)))
			a.Show(
				"q is monic of degree n over S",
				By(
					Normalized,
					degree,
					qLeading,
					qOver,
					polynomial.PolynomialMonicDef.At(a.TermAs[A]("L.zero"), a.TermAs[A]("L.one"), q)))
		})

		// Over a field, a monic polynomial that divides a monic polynomial of
		// the same degree equals it.
		monicDivisorEqual := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀p q:(num → A).",
			Hypotheses: []string{
				"polynomial_over(F.carrier, p)",
				"polynomial_monic(p)",
				"polynomial_over(F.carrier, q)",
				"polynomial_monic(q)",
				"polynomial_divides(field_ring(F), p, q)",
				"polynomial_degree(p) = polynomial_degree(q)",
			},
			Conclusion: "p = q",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			p, q *Arrow[Nat, A],
			pOver, pMonic, qOver, qMonic, divides, sameDegree Fact,
		) {
			ring := field.RingOn.Read(F)
			domain := integral_domain.FieldIntegralDomain.Read(F)
			r, quotient := a.UnpackAs[Fun[Nat, A]](
				a.Unfolded(divides, polynomial_division.PolynomialDividesDef), "r")
			nonzero := a.Have(
				"monic polynomials are nonzero",
				"p ≠ vec_zero ∧ q ≠ vec_zero",
				By(
					pMonic,
					qMonic,
					polynomial.MonicNonzero.Read(domain).At(p),
					polynomial.MonicNonzero.Read(domain).At(q)))
			rNonzero := a.Have(
				"the quotient r is nonzero, since q is",
				"r ≠ vec_zero",
				By(
					Normalized,
					nonzero,
					quotient,
					pOver,
					comm_ring.MulRightZeroOn.Read(polynomial.PolynomialRingOn.Read(ring)).AsFact().At(p)))
			degrees := a.Have(
				"degrees add under multiplication",
				"polynomial_degree(q) = polynomial_degree(p) + polynomial_degree(r)",
				By(rNonzero, nonzero, quotient, pOver, polynomial.DegreeMul.Read(domain).At(p, r)))
			constant := a.Have(
				"so r has degree zero",
				"polynomial_degree(r) = 0",
				ByArith(sameDegree, degrees))
			rConstant := a.Have(
				"a polynomial of degree zero is its constant term",
				"r = vec_scalar_mul(r(0), basis_vector(0))",
				By(constant, quotient, polynomial.DegreeZeroConstant.Read(ring).At(r)))
			coefficients := a.Have(
				"the coefficients of p and r lie in F",
				"∀i:num. p(i) ∈ F.carrier ∧ r(i) ∈ F.carrier",
				By(quotient, pOver, polynomial.PolynomialOverDef))
			leading := a.Have(
				"p and q have leading coefficient one",
				"p(polynomial_degree(p)) = F.one ∧ q(polynomial_degree(q)) = F.one",
				By(
					pMonic,
					qMonic,
					polynomial.PolynomialMonicDef.At(a.TermAs[A]("F.zero"), a.TermAs[A]("F.one"), p),
					polynomial.PolynomialMonicDef.At(a.TermAs[A]("F.zero"), a.TermAs[A]("F.one"), q)))
			unit := a.Have(
				"comparing leading coefficients, r(0) = 1",
				"r(0) = F.one",
				By(
					coefficients.At(a.TermAs[Nat]("0")),
					degrees,
					constant,
					leading,
					quotient,
					pOver,
					polynomial.LeadingCoefficientMul.Read(ring).At(p, r),
					comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(a.TermAs[A]("r(0)"))))
			a.Show(
				"q = p·1 = p",
				By(
					coefficients,
					unit,
					rConstant,
					quotient,
					pOver,
					polynomial.PolynomialMulConstant.Read(ring).At(
						a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring)), p),
					vec_space.SmulOneOn.Read(ring).At(p)))
		})

		// Scaling a generator by a nonzero element of the base field does not
		// change the field it generates.
		scaledGenerator := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀B:set(A). ∀c a:A.",
			Hypotheses: []string{
				"subfield(L, B)",
				"c ∈ B",
				"c ≠ L.zero",
				"a ∈ L.carrier",
			},
			Conclusion: "field_adjoin(L, B, {c * a}) = field_adjoin(L, B, {a})",
		}, func(
			arg *Argument,
			L field.FieldFact[on.L],
			B *Expr[Set[A]],
			c, a *Expr[A],
			BField, cInB, cNonzero, aInL Fact,
		) {
			l := arg.TermAs[FieldOps[A]]("L")
			E, EDef := arg.LetAs[Set[A]]("E", "field_adjoin(L, B, {a})")
			D, DDef := arg.LetAs[Set[A]]("D", "field_adjoin(L, B, {c * a})")
			cInL := arg.Have(
				"c lies in L",
				"c ∈ L.carrier",
				BySets(BField, cInB, field.SubfieldSubset.At(l, B)))
			am := arg.MemberOf[on.L](a, aInL)
			product := comm_ring.MulIn.Read(field.RingOn.Read(L)).At(arg.MemberOf[on.L](c, cInL), am)
			generated := arg.Have(
				"E = B(a) and D = B(c·a) are subfields over B containing their generators",
				"subfield(L, E) ∧ B ⊆ E ∧ a ∈ E ∧ subfield(L, D) ∧ B ⊆ D ∧ c * a ∈ D",
				By(
					Normalized,
					DDef,
					EDef,
					BField,
					algebraic_element.AdjoinElementSubfield.Read(L).At(B, am),
					algebraic_element.AdjoinElementSubfield.Read(L).At(B, product)))
			scalars := arg.Have(
				"c lies in E, and its inverse in D",
				"c ∈ E ∧ L.inv(c) ∈ D",
				BySets(BField, cInB, generated, field.SubfieldInv.At(l, B, c)))
			productInE := arg.Have(
				"c·a lies in E",
				"c * a ∈ E",
				By(scalars, generated, field.SubfieldMul.At(l, E, c, a)))
			productSingleton := arg.Have(
				"so {c·a} ⊆ E",
				"{c * a} ⊆ E",
				BySets(productInE))
			DInE := arg.Have(
				"D ⊆ E",
				"D ⊆ E",
				BySets(
					DDef,
					productSingleton,
					generated,
					algebraic_element.AdjoinLeast.Read(L).At(B, arg.TermAs[Set[A]]("{c * a}"), E)))
			recover := arg.Have(
				"c⁻¹·(c·a) = a",
				"L.inv(c) * (c * a) = a",
				ByArith(cInL, cNonzero, aInL, Scaled(a, field.MulLeftInverseOn.Read(L).AsFact().At(c))))
			aInD := arg.Have(
				"a lies in D",
				"a ∈ D",
				By(
					Normalized,
					recover,
					scalars,
					generated,
					field.SubfieldMul.At(l, D, arg.TermAs[A]("L.inv(c)"), arg.TermAs[A]("c * a"))))
			aSingleton := arg.Have(
				"so {a} ⊆ D",
				"{a} ⊆ D",
				BySets(aInD))
			EInD := arg.Have(
				"E ⊆ D",
				"E ⊆ D",
				BySets(
					EDef,
					aSingleton,
					generated,
					algebraic_element.AdjoinLeast.Read(L).At(B, arg.TermAs[Set[A]]("{a}"), D)))
			arg.Show(
				"so D = E",
				BySets(DInE, EInD))
		})

		// If c clears the denominators of the minimal polynomial of a over B,
		// the minimal polynomial of c·a has its coefficients in S: it is the
		// scaled polynomial, which it divides and matches in degree.
		scaledMinimalPolynomial := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀B S:set(A). ∀c a:A.",
			Hypotheses: []string{
				"subfield(L, B)",
				"subring(field_ring(L), S)",
				"S ⊆ B",
				"c ∈ S",
				"c ≠ L.zero",
				"a ∈ L.carrier",
				"algebraic_over(L, B, a)",
				"∀i:num. c * minimal_polynomial(L, B, a, i) ∈ S",
			},
			Conclusion: "polynomial_over(S, minimal_polynomial(L, B, c * a))",
		}, func(
			arg *Argument,
			L field.FieldFact[on.L],
			B, S *Expr[Set[A]],
			c, a *Expr[A],
			BField, subring, SInB, cInS, cNonzero, aInL, algebraic, scaledIn Fact,
		) {
			l := arg.TermAs[FieldOps[A]]("L")
			ring := field.RingOn.Read(L)
			zero := arg.TermAs[A]("L.zero")
			p, pDef := arg.LetAs[Fun[Nat, A]]("p", "minimal_polynomial(L, B, a)")
			n, nDef := arg.LetAs[Nat]("n", "polynomial_degree(p)")
			z, zDef := arg.LetAs[A]("z", "c * a")
			q, qDef := arg.LetAs[Fun[Nat, A]](
				"q", "λi:num. COND(i ≤ n, monoid_pow(L.mul, L.one, c, n - i) * p(i), L.zero)")
			g, gDef := arg.LetAs[Fun[Nat, A]]("g", "minimal_polynomial(L, B, z)")
			am := arg.MemberOf[on.L](a, aInL)
			pSpec := arg.Have(
				"p is a monic polynomial over B with root a",
				"polynomial_over(B, p) ∧ polynomial_monic(p) ∧ polynomial_eval(p, a) = L.zero",
				By(Normalized, pDef, BField, algebraic, algebraic_element.MinimalPolynomialSpec.Read(L).At(B, am)))
			cIn := arg.Have(
				"c lies in B and in L",
				"c ∈ B ∧ c ∈ L.carrier",
				BySets(cInS, SInB, BField, field.SubfieldSubset.At(l, B)))
			cParts := arg.Conjuncts(
				cIn,
				"c lies in B",
				"c lies in L")
			cm := arg.MemberOf[on.L](c, cParts[1])
			zInL := arg.Have(
				"z lies in L",
				"z ∈ L.carrier",
				By(Normalized, zDef, comm_ring.MulIn.Read(ring).At(cm, am)))
			zm := arg.MemberOf[on.L](z, zInL)
			pShape := arg.Have(
				"p is a polynomial over L of degree n with p(n) = 1",
				"polynomial_over(L.carrier, p) ∧ polynomial_degree(p) ≤ n ∧ p(n) = L.one",
				By(
					Normalized,
					nDef,
					BField,
					pSpec,
					field.SubfieldSubset.At(l, B),
					polynomial.PolynomialOverMono.At(zero, B, arg.TermAs[Set[A]]("L.carrier"), p),
					nat_order.LessEqRefl.At(n),
					polynomial.PolynomialMonicDef.At(zero, arg.TermAs[A]("L.one"), p)))
			qShape := arg.Have(
				"the scaled polynomial q is monic of degree n over S",
				"polynomial_over(S, q) ∧ polynomial_monic(q) ∧ polynomial_degree(q) = n",
				qDef.Rw(),
				By(L, subring, cInS, scaledIn, pShape, At(scaledPolynomial, l, S, c, n, p)))
			qValue := arg.Have(
				"q(z) = c^n·p(a), q being p rescaled by c at weight one and z = c·a",
				"polynomial_eval(q, z) = monoid_pow(L.mul, L.one, c, n) * polynomial_eval(p, a)",
				qDef.Rw(),
				zDef.Rw(),
				By(
					pShape,
					polynomial_evaluation.EvalRescaled.Read(ring).At(p, n, arg.TermAs[Nat]("1"), cm, am),
					nat_arith.OneMul,
					comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(cm)))
			qRoot := arg.Have(
				"so z is a root of q",
				"polynomial_eval(q, z) = L.zero",
				By(
					qValue,
					pSpec,
					comm_ring.MulRightZeroOn.Read(ring).At(
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(cm, n))))
			qNonzero := arg.Have(
				"q is a nonzero polynomial over B",
				"polynomial_over(B, q) ∧ q ≠ vec_zero",
				By(
					SInB,
					qShape,
					polynomial.PolynomialOverMono.At(zero, S, B, q),
					polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(L)).At(q)))
			zAlgebraic := arg.Have(
				"q witnesses that z is algebraic over B",
				"algebraic_over(L, B, z)",
				Simp(Fwd(algebraic_element.AlgebraicOverDef)),
				Witness(q),
				By(qRoot, qNonzero))
			gDivides := arg.Have(
				"g is a monic polynomial over B dividing q",
				"polynomial_over(B, g) ∧ "+
					"polynomial_monic(g) ∧ "+
					"polynomial_divides(restrict_ring(field_ring(L), B), g, q)",
				By(
					Normalized,
					qRoot,
					gDef,
					BField,
					qNonzero,
					zAlgebraic,
					algebraic_element.MinimalPolynomialSpec.Read(L).At(B, zm),
					algebraic_element.MinimalPolynomialDivides.Read(L).At(B, zm, q)))
			sameField := arg.Have(
				"z generates the same field over B as a",
				"field_adjoin(L, B, {z}) = field_adjoin(L, B, {a})",
				zDef.Rw(),
				By(L, cIn, BField, cNonzero, aInL, At(scaledGenerator, l, B, c, a)))
			gDegree := arg.Have(
				"g has degree n, the degree of that common field over B",
				"polynomial_degree(g) = n",
				By(
					Normalized,
					sameField,
					gDef,
					pDef,
					nDef,
					BField,
					algebraic,
					zAlgebraic,
					algebraic_element.AdjoinDegree.Read(L).At(B, am),
					algebraic_element.AdjoinDegree.Read(L).At(B, zm)))
			restrictedField := arg.Have(
				"B is a field under the operations of L",
				"field_on(restrict_field(L, B))",
				By(BField, field.SubfieldFieldOn.Read(L).At(B)))
			restricted := arg.Have(
				"the ring of the restricted field is the restricted ring",
				"restrict_ring(field_ring(L), B) = field_ring(restrict_field(L, B))",
				Cite(field.RestrictFieldRing))
			dividesOverB := arg.Have(
				"g divides q in the polynomial ring of the field B",
				"polynomial_divides(field_ring(restrict_field(L, B)), g, q)",
				Simp(Rev(restricted)),
				By(gDivides))
			sameDegree := arg.Have(
				"g and q have the same degree",
				"polynomial_degree(g) = polynomial_degree(q)",
				By(Normalized, gDegree, qShape))
			equal := arg.Have(
				"a monic divisor of the same degree is the polynomial itself",
				"g = q",
				By(
					restrictedField,
					sameDegree,
					gDivides,
					qShape,
					qNonzero,
					dividesOverB,
					At(monicDivisorEqual, arg.TermAs[FieldOps[A]]("restrict_field(L, B)"), g, q)))
			arg.Show(
				"so the minimal polynomial of c·a has its coefficients in S",
				By(Normalized, equal, qShape))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			t *Expr[A],
			kField, KField, kInK, tInK, transcendental, finite, separable Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			B, BDef := a.LetAs[Set[A]]("B", "field_adjoin(M, k, {t})")
			S, SDef := a.LetAs[Set[A]]("S", "polynomial_image(field_ring(M), k, t)")
			rationalFunctions := a.Have(
				"B = k(t) is a subfield between k and K containing t",
				"subfield(M, B) ∧ k ⊆ B ∧ t ∈ B ∧ B ⊆ K",
				Simp(Fwd(BDef)),
				By(kField, KField, kInK, tInK, algebraic_element.AdjoinElementBetween.Read(M).At(k, K, t)))
			tInM := a.Have(
				"t lies in M",
				"t ∈ M.carrier",
				BySets(KField, tInK, field.SubfieldSubset.At(m, K)))
			tm := a.MemberOf[on.M](t, tInM)
			polynomials := a.Have(
				"the polynomial ring S = k[t] is a subring of M inside k(t)",
				"subring(field_ring(M), S) ∧ S ⊆ B",
				By(Normalized, BDef, SDef, kField, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
			fractions := a.Have(
				"k(t) is the fraction field of k[t]",
				"fraction_field_carrier(restrict_ring(field_ring(M), B), S)",
				By(
					Normalized,
					BDef,
					SDef,
					kField,
					integral_element.RationalFunctionsFractionField.Read(M).At(k, tm)))
			infiniteB := a.Have(
				"t being transcendental over k, k(t) is infinite",
				"infinite(B)",
				By(
					rationalFunctions,
					kField,
					transcendental,
					algebraic_element.TranscendentalSubfieldInfinite.Read(M).At(k, B, t)))
			θ, primitive := a.ObtainAs[A](
				"K has a primitive element θ over k(t)",
				"∃θ:A. θ ∈ K ∧ field_adjoin(M, B, {θ}) = K",
				By(
					rationalFunctions,
					KField,
					infiniteB,
					finite,
					separable,
					algebraic_closure.PrimitiveElement.Read(M).At(B, K)))
			θParts := a.Conjuncts(
				primitive,
				"θ lies in K",
				"θ generates K over k(t)")
			θAlgebraic := a.Have(
				"θ lies in M and is algebraic over k(t)",
				"θ ∈ M.carrier ∧ algebraic_over(M, B, θ)",
				BySets(
					separable.At(θ),
					θParts[0],
					KField,
					field.SubfieldSubset.At(m, K),
					galois_correspondence.SeparableOverDef.At(m, B, θ)))
			θIn := a.Conjuncts(
				θAlgebraic,
				"θ lies in M",
				"θ is algebraic over k(t)")
			θm := a.MemberOf[on.M](θ, θIn[0])
			θPolynomial := a.Have(
				"the minimal polynomial of θ is a polynomial over k(t)",
				"polynomial_over(B, minimal_polynomial(M, B, θ))",
				By(θAlgebraic, rationalFunctions, algebraic_element.MinimalPolynomialSpec.Read(M).At(B, θm)))
			c, denominator := a.ObtainAs[A](
				"a common denominator c ∈ k[t] of its coefficients",
				"∃c:A. c ∈ S ∧ c ≠ M.zero ∧ (∀i:num. c * minimal_polynomial(M, B, θ, i) ∈ S)",
				By(
					fractions,
					rationalFunctions,
					polynomials,
					θPolynomial,
					integral_element.PolynomialCommonDenominator.Read(M).At(
						B, S, a.TermAs[Fun[Nat, A]]("minimal_polynomial(M, B, θ)"))))
			w, wDef := a.LetAs[A]("w", "c * θ")
			_, gDef := a.LetAs[Fun[Nat, A]]("g", "minimal_polynomial(M, B, w)")
			cIn := a.Have(
				"c lies in k(t) and in K",
				"c ∈ B ∧ c ∈ K",
				BySets(denominator, rationalFunctions, polynomials))
			wInK := a.Have(
				"w = c·θ lies in K",
				"w ∈ K",
				By(Normalized, wDef, θParts[0], KField, cIn, field.SubfieldMul.At(m, K, c, θ)))
			wSeparable := a.Have(
				"w lies in M, is algebraic over k(t), and has a separable minimal polynomial g",
				"w ∈ M.carrier ∧ "+
					"algebraic_over(M, B, w) ∧ "+
					"polynomial_separable(restrict_ring(field_ring(M), B), g)",
				BySets(
					separable.At(w),
					wInK,
					KField,
					gDef,
					field.SubfieldSubset.At(m, K),
					galois_correspondence.SeparableOverDef.At(m, B, w)))
			wParts := a.Conjuncts(
				wSeparable,
				"w lies in M",
				"w is algebraic over k(t)",
				"g is separable over k(t)")
			wm := a.MemberOf[on.M](w, wParts[0])
			integral := a.Have(
				"g has its coefficients in k[t]",
				"polynomial_over(S, g)",
				gDef.Rw(),
				wDef.Rw(),
				By(
					M,
					θAlgebraic,
					denominator,
					rationalFunctions,
					polynomials,
					At(scaledMinimalPolynomial, m, B, S, c, θ)))
			generates := a.Have(
				"w generates K over k(t), as θ does",
				"field_adjoin(M, B, {w}) = K",
				wDef.Rw(),
				By(M, θParts[1], θAlgebraic, cIn, denominator, rationalFunctions, At(scaledGenerator, m, B, c, θ)))
			monic := a.Have(
				"g is monic of degree [K : k(t)]",
				"polynomial_monic(g) ∧ polynomial_degree(g) = extension_degree(M, B, K)",
				By(
					Normalized,
					generates,
					gDef,
					wSeparable,
					rationalFunctions,
					algebraic_element.MinimalPolynomialSpec.Read(M).At(B, wm),
					algebraic_element.AdjoinDegree.Read(M).At(B, wm)))
			a.Take(w)
			a.Show(
				"w is the required integral primitive element",
				Simp(Rev(gDef)),
				By(wInK, generates, integral, wSeparable, monic))
		})
	}),
})}

// FiniteGaloisClosureExists — a finite separable extension K of k(t), t
// transcendental over k, inside an algebraically closed field M lies in a
// Galois extension E of k(t) over which the minimal polynomial of every
// element of K splits, and K is the fixed field of the automorphisms of E
// fixing K. k(t), holding the transcendental t, is infinite, so K has a
// primitive element z over it, separable; E is the field k(t) generates
// with the roots of the minimal polynomial of z: the root field of one
// separable polynomial, it is Galois, hence normal, and the Galois
// correspondence recovers K, which lies between k(t) and E.
var FiniteGaloisClosureExists = finiteGaloisClosureExistsThm{family.Add(registry.ProofEntry{
	Name: "FiniteGaloisClosureExists",
	Key:  "prop_c4a4ac9ee38e5ffa",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"t ∈ K",
			"¬algebraic_over(M, k, t)",
			"finite_extension(M, field_adjoin(M, k, {t}), K)",
			"∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {t}), x)",
		},
		Conclusion: "∃L:set(A). " +
			"    subfield(M, L) ∧ " +
			"    K ⊆ L ∧ " +
			"    galois_over(M, field_adjoin(M, k, {t}), L) ∧ " +
			"    (∀x:A. " +
			"        x ∈ K ⇒ " +
			"        polynomial_splits(restrict_ring(field_ring(M), L), " +
			"            minimal_polynomial(M, field_adjoin(M, k, {t}), x))) ∧ " +
			"    fixed_field(L, field_automorphisms(M, K, L)) = K",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, K *Expr[Set[A]],
		t *Expr[A],
		closed, kField, KField, kInK, tInK, transcendental, finite, separable Fact,
	) {
		m := a.TermAs[FieldOps[A]]("M")
		B, baseDef := a.LetAs[Set[A]]("B", "field_adjoin(M, k, {t})")
		base := a.Have(
			"k(t) is a subfield between k and K",
			"subfield(M, B) ∧ k ⊆ B ∧ t ∈ B ∧ B ⊆ K",
			Simp(Fwd(baseDef)),
			By(kField, KField, kInK, tInK, algebraic_element.AdjoinElementBetween.Read(M).At(k, K, t)))
		infiniteBase := a.Have(
			"t being transcendental over k, k(t) is infinite",
			"infinite(B)",
			By(
				base,
				kField,
				transcendental,
				algebraic_element.TranscendentalSubfieldInfinite.Read(M).At(k, B, t)))
		z, primitive := a.ObtainAs[A](
			"K has a primitive element z over k(t)",
			"∃z:A. z ∈ K ∧ field_adjoin(M, B, {z}) = K",
			By(
				base,
				KField,
				infiniteBase,
				finite,
				separable,
				algebraic_closure.PrimitiveElement.Read(M).At(B, K)))
		p, polynomialDef := a.LetAs[Fun[Nat, A]]("p", "minimal_polynomial(M, B, z)")
		R, rootsDef := a.LetAs[Set[A]]("R", "{x:A | x ∈ M.carrier ∧ polynomial_eval(p, x) = M.zero}")
		E, extensionDef := a.LetAs[Set[A]]("E", "field_adjoin(M, B, R)")
		baseInM := a.Have(
			"k(t) lies in M",
			"B ⊆ M.carrier",
			By(base, field.SubfieldSubset.At(m, B)))
		zInM := a.Have(
			"the primitive element lies in M",
			"z ∈ M.carrier",
			BySets(primitive, KField, field.SubfieldSubset.At(m, K)))
		zm := a.MemberOf[on.M](z, zInM)
		algebraic := a.Have(
			"z is separable over k(t): algebraic, with a separable minimal polynomial p",
			"algebraic_over(M, B, z) ∧ polynomial_separable(restrict_ring(field_ring(M), B), p)",
			By(
				Normalized,
				polynomialDef,
				primitive,
				separable.At(z),
				galois_correspondence.SeparableOverDef.At(m, B, z)))
		polynomial := a.Have(
			"the generator has a nonconstant minimal polynomial over k(t)",
			"polynomial_over(B, p) ∧ 0 < polynomial_degree(p) ∧ polynomial_eval(p, z) = M.zero",
			By(
				Normalized,
				base,
				algebraic,
				polynomialDef,
				algebraic_element.MinimalPolynomialSpec.Read(M).At(B, zm),
				algebraic_element.MinimalPolynomialPositive.Read(M).At(B, zm)))
		roots := a.Have(
			"the full root set lies in the ambient field and contains z",
			"R ⊆ M.carrier ∧ z ∈ R",
			BySets(rootsDef, zInM, polynomial))
		rootField := a.Have(
			"the root field contains k(t) and every root",
			"subfield(M, E) ∧ B ⊆ E ∧ R ⊆ E",
			By(
				Normalized,
				base,
				baseInM,
				roots,
				extensionDef,
				algebraic_element.AdjoinSubfield.Read(M).At(B, R)))
		generator := a.Have(
			"the generator singleton lies in the root field",
			"{z} ⊆ E",
			BySets(roots, rootField))
		containsK := a.Have(
			"the root field contains K because z generates K",
			"K ⊆ E",
			By(
				Normalized,
				primitive,
				rootField,
				generator,
				algebraic_element.AdjoinLeast.Read(M).At(B, a.TermAs[Set[A]]("{z}"), E)))
		galois := a.Have(
			"the root field is Galois over k(t)",
			"galois_over(M, B, E)",
			Derive(func(b *Argument) {
				singletonRoots := b.Have(
					"the roots of p are the roots of the singleton polynomial family",
					"R = {x:A | x ∈ M.carrier ∧ (∃q:(num → A). q ∈ {p} ∧ polynomial_eval(q, x) = M.zero)}",
					BySets(rootsDef))
				singletonFamily := b.Have(
					"the singleton family consists of nonconstant separable polynomials over k(t)",
					"finite({p}) ∧ "+
						"(∀q:(num → A). "+
						"    q ∈ {p} ⇒ "+
						"    polynomial_over(B, q) ∧ "+
						"    0 < polynomial_degree(q) ∧ "+
						"    polynomial_separable(restrict_ring(field_ring(M), B), q))",
					By(Normalized, algebraic, polynomial, finite_set.FiniteSing.At(p), set_basic.InSing))
				b.Do(Simp(Fwd(extensionDef), Fwd(singletonRoots)))
				b.Show(
					"apply the Galois theorem for finite separable root fields",
					By(
						closed,
						M,
						singletonFamily,
						base,
						algebraic_closure.ClosedFieldSplits.Read(M),
						galois_correspondence.SeparableRootFieldGalois.Read(M).At(B, b.TermAs[Set[Fun[Nat, A]]]("{p}"))))
			}))
		normal := a.Have(
			"the Galois root field is normal over k(t)",
			"normal_over(M, B, E)",
			By(galois, galois_correspondence.GaloisOverDef.At(m, B, E)))
		fixed := a.Have(
			"the automorphisms fixing K have fixed field K",
			"fixed_field(E, field_automorphisms(M, K, E)) = K",
			By(
				galois,
				base,
				rootField,
				KField,
				containsK,
				galois_correspondence.CorrespondenceFixed.Read(M).At(B, K, E)))
		algebraicElements := a.Have(
			"every element of K is algebraic over k(t)",
			"∀x:A. x ∈ K ⇒ algebraic_over(M, B, x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inK := b.Assume()
				b.Show(
					"separability includes algebraicity",
					By(separable.At(x), inK, galois_correspondence.SeparableOverDef.At(m, B, x)))
			}))
		splits := a.Have(
			"normality splits the minimal polynomial of every element of K",
			"∀x:A. x ∈ K ⇒ polynomial_splits(restrict_ring(field_ring(M), E), minimal_polynomial(M, B, x))",
			By(
				normal,
				base,
				rootField,
				containsK,
				algebraicElements,
				galois_correspondence.NormalIffMinimalPolynomial.Read(M).At(B, E),
				set_basic.SubsetDef))
		a.Take(E)
		a.Show(
			"the root field has all the required closure and fixed-field properties",
			By(rootField, containsK, galois, splits, fixed))
	}),
})}
