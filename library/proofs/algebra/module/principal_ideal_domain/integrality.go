package principal_ideal_domain

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// IntegralPolynomialModule — adjoining an integral element to a coefficient
// subring gives a finite module containing one and preserved by that element:
// finitely many short powers span it, and the ring S[x] contains x, so
// multiplication by x preserves it.
var IntegralPolynomialModule = integralPolynomialModuleThm{family.Add(registry.ProofEntry{
	Name: "IntegralPolynomialModule",
	Key:  "prop_a97a3bf9a4c8348b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
			"integral_over(restrict_ring(field_ring(L), S), x)",
		},
		Conclusion: "submodule(restrict_ring(field_ring(L), S), " +
			"    regular_module(field_ring(L)), " +
			"    polynomial_image(field_ring(L), S, x)) ∧ " +
			"module_finitely_generated(restrict_ring(field_ring(L), S), " +
			"    restrict_module(regular_module(field_ring(L)), polynomial_image(field_ring(L), S, x))) ∧ " +
			"L.one ∈ polynomial_image(field_ring(L), S, x) ∧ " +
			"image(L.mul(x), polynomial_image(field_ring(L), S, x)) ⊆ polynomial_image(field_ring(L), S, x)",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], x *Expr[A], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a subring of the field",
			"x lies in the field",
			"x is integral over S")
		subringS, xIn, integral := parts[0], parts[1], parts[2]
		xm := a.MemberOf[on.L](x, xIn)
		fieldRing := field.RingOn.Read(L)
		fieldModule := a.Have(
			"the field is a module over S",
			"module_on(restrict_ring(field_ring(L), S), regular_module(field_ring(L)))",
			By(subringS, fractional_ideal.FieldModuleOn.Read(L).At(S)))
		p, relation := a.ObtainAs[Fun[Nat, A]](
			"choose a monic relation for x",
			"∃p:(num → A). "+
				"    polynomial_over(S, p) ∧ "+
				"    polynomial_monic(p) ∧ "+
				"    0 < polynomial_degree(p) ∧ "+
				"    polynomial_eval(p, x) = L.zero",
			By(integral, integral_element.IntegralOverDef))
		spans := a.Have(
			"the short powers span S[x]",
			"polynomial_image(field_ring(L), S, x) = "+
				"module_span(restrict_ring(field_ring(L), S), "+
				"    regular_module(field_ring(L)), "+
				"    {monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)})",
			By(subringS, xIn, relation, integral_element.IntegralPowerSpan.Read(L).At(S, xm, p)))
		powersIn := a.Have(
			"the power generators lie in the field",
			"{monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)} ⊆ L.carrier",
			BySets(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(fieldRing)), xIn))
		sub := a.Have(
			"S[x] is a submodule of the field",
			"submodule(restrict_ring(field_ring(L), S), "+
				"    regular_module(field_ring(L)), "+
				"    polynomial_image(field_ring(L), S, x))",
			spans.Rw(),
			By(submodule.SpanSubmodule.Read(fieldModule), powersIn))
		holdsOne := a.Have(
			"the zeroth power puts one in S[x]",
			"L.one ∈ polynomial_image(field_ring(L), S, x)",
			spans.Rw(),
			BySets(relation, comm_monoid.MonoidPowDef, submodule.SubsetSpan))
		powers := a.TermAs[Set[A]]("{monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)}")
		polynomialModule := a.TermAs[Set[A]]("polynomial_image(field_ring(L), S, x)")
		finitePowers := a.Have(
			"there are finitely many short powers",
			"finite({monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)})",
			Derive(func(b *Argument) {
				asImage := b.Have(
					"the short powers are the image of their finite initial segment",
					"{monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)} = "+
						"image(λi:num. monoid_pow(L.mul, L.one, x, i), {i:num | i < polynomial_degree(p)})",
					BySets())
				b.Show(
					"a finite image is finite",
					asImage.Rw(),
					By(num_segment.FiniteBelowStrict, finite_set.FiniteImage))
			}))
		generatorsIn := a.Have(
			"the short powers lie in the polynomial module",
			"{monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)} ⊆ "+
				"polynomial_image(field_ring(L), S, x)",
			spans.Rw(),
			By(submodule.SubsetSpan))
		spansRestriction := a.Have(
			"the short powers also span the restricted polynomial module",
			"module_span(restrict_ring(field_ring(L), S), "+
				"    restrict_module(regular_module(field_ring(L)), polynomial_image(field_ring(L), S, x)), "+
				"    {monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)}) = "+
				"polynomial_image(field_ring(L), S, x)",
			By(
				spans,
				generatorsIn,
				sub,
				linear_independence.SpanRestrict.Read(fieldModule).At(polynomialModule, powers)))
		finite := a.Have(
			"the finite short-power set generates the polynomial module",
			"module_finitely_generated(restrict_ring(field_ring(L), S), "+
				"    restrict_module(regular_module(field_ring(L)), polynomial_image(field_ring(L), S, x)))",
			Simp(Fwd(FinitelyGeneratedDef)),
			Witness(powers),
			By(finitePowers, spansRestriction, generatorsIn))
		subringSx := a.Conjuncts(
			GroupPremises(parts[0], algebraic_element.PolynomialImageSubring.Read(L).At(S, xm)),
			"S[x] is a subring of the field",
			"S lies in S[x]",
			"x lies in S[x]")
		ringSx, xInSx := subringSx[0], subringSx[2]
		stable := a.Have(
			"multiplication by x preserves S[x]",
			"image(L.mul(x), polynomial_image(field_ring(L), S, x)) ⊆ polynomial_image(field_ring(L), S, x)",
			BySets(xInSx, comm_ring.SubringMul.Read(ringSx)))
		a.Show(
			"S[x] is a finite module holding one and preserved by x",
			By(sub, finite, holdsOne, stable))
	}),
})}

// IntegralFiniteModuleCriterion — an element is integral over a subring
// precisely when its polynomial values form a finitely generated module over that
// subring. A monic relation bounds the powers needed to span; conversely,
// a common degree bound for polynomial representatives of the generators
// produces a monic relation.
var IntegralFiniteModuleCriterion = integralFiniteModuleCriterionThm{family.Add(registry.ProofEntry{
	Name: "IntegralFiniteModuleCriterion",
	Key:  "prop_df0bf60cf9f19c8a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(L), S), x) ⇔ " +
			"module_finitely_generated(restrict_ring(field_ring(L), S), " +
			"    restrict_module(regular_module(field_ring(L)), polynomial_image(field_ring(L), S, x)))",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], x *Expr[A], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a subring of L",
			"x lies in L")
		xIn := parts[1]
		inside := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(parts[0])))
		subring := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(parts[0], comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		a.Iff()
		a.Forward(
			"the polynomial values of an integral element form a finite module",
			func(b *Argument, integral Fact) {
				b.Show(
					"S[x] is finitely generated over S",
					By(integral, h, IntegralPolynomialModule.Read(L).At(S, b.MemberOf[on.L](x, xIn))))
			})
		a.Backward(
			"finite generation bounds the polynomial representatives",
			func(b *Argument, finiteModule Fact) {
				E, generators := b.UnpackAs[Set[A]](b.Unfolded(finiteModule, FinitelyGeneratedDef), "E")
				image := b.Have(
					"polynomial values are the image of evaluation",
					"polynomial_image(field_ring(L), S, x) = "+
						"image(λp:(num → A). polynomial_eval(p, x), {p:(num → A) | polynomial_over(S, p)})",
					Unfold(algebraic_element.PolynomialImageDef),
					BySets())
				_, representatives := b.ObtainAs[Set[Fun[Nat, A]]](
					"choose finitely many polynomial representatives of the generators",
					"∃P:set(num → A). "+
						"    finite(P) ∧ "+
						"    P ⊆ {p:(num → A) | polynomial_over(S, p)} ∧ "+
						"    E ⊆ image(λp:(num → A). polynomial_eval(p, x), P)",
					By(
						image,
						generators,
						finite_set.FiniteSubsetImageImp.At(
							b.TermAs[Fun[Fun[Nat, A], A]]("λp:(num → A). polynomial_eval(p, x)"),
							b.TermAs[Set[Fun[Nat, A]]]("{p:(num → A) | polynomial_over(S, p)}"),
							E)),
					Named("P"))
				degreesFinite := b.Have(
					"the representative degrees form a finite set",
					"finite(image(λp:(num → A). polynomial_degree(p), P))",
					By(representatives, finite_set.FiniteImage))
				_, degreeBound := b.ObtainAs[Nat](
					"bound all representative degrees",
					"∃n:num. image(λp:(num → A). polynomial_degree(p), P) ⊆ 0 .. n",
					By(degreesFinite, num_segment.FiniteIffBounded),
					Named("n"))
				boundedDegrees := b.Have(
					"each representative has degree at most n",
					"∀p:(num → A). p ∈ P ⇒ polynomial_degree(p) ≤ n",
					BySets(degreeBound, num_segment.IntervalDef))
				N, nDef := b.LetAs[Nat]("N", "suc(n)")
				polynomials := b.Have(
					"all representatives have coefficients in S",
					"∀p:(num → A). p ∈ P ⇒ polynomial_over(S, p)",
					BySets(representatives))
				boundedLengths := b.Have(
					"their coefficient supports fit below N",
					"∀p:(num → A). p ∈ P ⇒ suc(polynomial_degree(p)) ≤ N",
					ByArith(boundedDegrees, nDef))
				bounded := b.Have(
					"each representative vanishes from N onward",
					"∀p:(num → A). p ∈ P ⇒ vec⟨N⟩(p)",
					Derive(func(c *Argument) {
						t := c.FixAs[Fun[Nat, A]]("t")
						member := c.Assume()
						c.Show(
							"enlarge its degree support to the common bound",
							By(
								boundedLengths.At(t),
								polynomials.At(t),
								member,
								polynomial.DegreeVec.At(c.TermAs[A]("L.zero"), S, t),
								vec_space.VecMono.At(c.TermAs[A]("L.zero"), c.TermAs[Nat]("suc(polynomial_degree(t))"), N, t)))
					}))
				wDef := b.Let(
					"W", b.TermAs[Set[A]]("{polynomial_eval(p, x) | p:(num → A) | polynomial_over(S, p) ∧ vec⟨N⟩(p)}"))
				values := b.Have(
					"membership in W is evaluation of a bounded polynomial",
					"∀y:A. y ∈ W ⇔ ∃p:(num → A). polynomial_over(S, p) ∧ vec⟨N⟩(p) ∧ y = polynomial_eval(p, x)",
					BySets(wDef))
				space := b.Have(
					"L is an S-module",
					"module_on(restrict_ring(field_ring(L), S), regular_module(field_ring(L)))",
					By(module.RegularModuleOverSubring.Read(field.RingOn.Read(L)), h))
				ring := b.Have(
					"L supplies its ambient ring",
					"comm_ring_on(field_ring(L))",
					By(field.RingOn.Read(L)))
				overL := b.Have(
					"coefficients in S are coefficients in L",
					"∀p:(num → A). polynomial_over(S, p) ⇒ polynomial_over(L.carrier, p)",
					By(inside, polynomial.PolynomialOverMono))
				valuesIn := b.Have(
					"bounded evaluations lie in L",
					"W ⊆ L.carrier",
					BySets(polynomial_evaluation.EvalIn.Read(ring), values, overL, h))
				zero := b.Have(
					"zero belongs to W",
					"L.zero ∈ W",
					By(
						polynomial.VecZeroOver.Read(subring),
						values,
						polynomial_evaluation.EvalVecZero.Read(ring).At(proof.MemberOf(x, xIn)),
						vec_space.VecZero.At(b.TermAs[A]("L.zero"), N)))
				sums := b.Have(
					"polynomial addition preserves coefficients in S",
					"∀f g:(num → A). polynomial_over(S, f) ∧ polynomial_over(S, g) ⇒ polynomial_over(S, f + g)",
					BySets(comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(subring))))
				multiples := b.Have(
					"scalar multiplication preserves coefficients in S",
					"∀c:A. ∀f:(num → A). c ∈ S ∧ polynomial_over(S, f) ⇒ polynomial_over(S, c • f)",
					BySets(module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(subring))))
				evalSum := b.Have(
					"evaluation preserves addition",
					Statement{
						Binders: "∀f g:(num → A).",
						Hypotheses: []string{
							"polynomial_over(S, f)",
							"polynomial_over(S, g)",
						},
						Conclusion: "polynomial_eval(f + g, x) = polynomial_eval(f, x) + polynomial_eval(g, x)",
					},
					By(polynomial_evaluation.EvalAdd.Read(ring), overL, h))
				evalMultiple := b.Have(
					"evaluation preserves scalar multiplication",
					Statement{
						Binders: "∀c:A. ∀f:(num → A).",
						Hypotheses: []string{
							"c ∈ S",
							"polynomial_over(S, f)",
						},
						Conclusion: "polynomial_eval(c • f, x) = c * polynomial_eval(f, x)",
					},
					BySets(polynomial_evaluation.EvalScalar.Read(ring), overL, inside, h))
				addClosed := b.Have(
					"W is closed under addition",
					"∀u v:A. u ∈ W ∧ v ∈ W ⇒ u + v ∈ W",
					By(values, sums, evalSum, At(vec_space.VecAddOn.Read(subring), N)))
				smulClosed := b.Have(
					"W is closed under S-scalar multiplication",
					"∀c u:A. c ∈ S ∧ u ∈ W ⇒ c * u ∈ W",
					By(values, multiples, evalMultiple, At(vec_space.VecSmulOn.Read(subring), N)))
				boundedSubmodule := b.Have(
					"bounded polynomial values form an S-submodule",
					"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), W)",
					By(submodule.SubmoduleCriterion.Read(space), valuesIn, zero, addClosed, smulClosed))
				generatorsBounded := b.Have(
					"W contains every chosen generator",
					"E ⊆ W",
					BySets(values, bounded, representatives))
				ambientSpan := b.Have(
					"the generators span the same set in L",
					"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), E) = "+
						"polynomial_image(field_ring(L), S, x)",
					By(
						linear_independence.SpanningRestrict.Read(space),
						generators,
						integral_element.PolynomialImageSubmodule.Read(L),
						h))
				allBounded := b.Have(
					"every polynomial value belongs to W",
					"polynomial_image(field_ring(L), S, x) ⊆ W",
					By(generatorsBounded, boundedSubmodule, ambientSpan, submodule.SpanLeast))
				powerIn := b.Have(
					"the Nth power is a polynomial value",
					"monoid_pow(L.mul, L.one, x, N) ∈ polynomial_image(field_ring(L), S, x)",
					BySets(
						image,
						polynomial.BasisVectorOver.Read(subring).At(N),
						polynomial_evaluation.EvalBasisVector.Read(ring).At(N, proof.MemberOf(x, xIn))))
				_, lower := b.ObtainAs[Fun[Nat, A]](
					"represent the Nth power by a polynomial supported below N",
					"∃q:(num → A). "+
						"    polynomial_over(S, q) ∧ vec⟨N⟩(q) ∧ monoid_pow(L.mul, L.one, x, N) = polynomial_eval(q, x)",
					BySets(values, allBounded, powerIn),
					Named("q"))
				r, rDef := b.LetAs[Fun[Nat, A]]("r", "basis_vector(N) - q")
				relationOver := b.Have(
					"subtract the lower polynomial from the Nth monomial",
					"polynomial_over(S, r)",
					BySets(
						comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(subring)),
						rDef,
						lower,
						polynomial.BasisVectorOver.Read(subring).At(N)))
				qAtN := b.Have(
					"the lower polynomial has zero coefficient at N",
					"q(N) = L.zero",
					ByArith(lower, vec_space.VecDef))
				leading := b.Have(
					"the constructed polynomial has coefficient one at N",
					"r(N) = L.one",
					rDef.Rw(),
					Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.BasisVectorDef)),
					qAtN.Rw(),
					ByArith(ring))
				relationBounded := b.Have(
					"the constructed polynomial vanishes above N",
					"vec⟨suc(N)⟩(r)",
					Simp(Fwd(vec_space.VecDef)),
					Derive(func(c *Argument) {
						c.FixAs[Nat]("i")
						above := c.Assume()
						qZero := c.Have(
							"the lower polynomial vanishes at this index",
							"q(i) = L.zero",
							ByArith(above, lower, vec_space.VecDef.At(c.TermAs[A]("L.zero"), c.VecAt[A](N, "q"))))
						c.Show(
							"both monomial and lower polynomial vanish",
							rDef.Rw(),
							Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.BasisVectorDef)),
							qZero.Rw(),
							ByArith(ring, above))
					}))
				degreeGe := b.Have(
					"its nonzero coefficient at N forces degree at least N",
					"N < suc(polynomial_degree(r))",
					By(
						field.OneNotZeroOn.Read(L),
						leading,
						relationOver,
						polynomial.DegreeVec.At(b.TermAs[A]("L.zero"), S, r),
						vec_space.VecDef.At(
							b.TermAs[A]("L.zero"), b.VecAt[A](b.TermAs[Nat]("suc(polynomial_degree(r))"), "r")),
						nat_order.NotLessEq.At(b.TermAs[Nat]("suc(polynomial_degree(r))"), N)))
				degree := b.Have(
					"and, vanishing above N, it has degree at most N: the degree is exactly N",
					"polynomial_degree(r) = N",
					ByArith(relationBounded, polynomial.DegreeLeast.At(b.TermAs[A]("L.zero"), r, N), degreeGe))
				monic := b.Have(
					"the constructed polynomial is monic",
					"polynomial_monic(r)",
					By(Normalized, degree, leading, polynomial.PolynomialMonicDef))
				members := b.Have(
					"the three polynomials lie in the ring of polynomials over S",
					"r ∈ polynomial_ring(restrict_ring(field_ring(L), S)).carrier ∧ "+
						"q ∈ polynomial_ring(restrict_ring(field_ring(L), S)).carrier ∧ "+
						"basis_vector(N) ∈ polynomial_ring(restrict_ring(field_ring(L), S)).carrier",
					BySets(relationOver, lower, polynomial.BasisVectorOver.Read(subring).At(N)))
				cancelPolynomials := b.Have(
					"adding back the lower polynomial leaves the Nth monomial",
					"r + q = basis_vector(N)",
					Derive(func(c *Argument) {
						carrier := c.Unfolded(members, polynomial.PolynomialRingDef)
						c.Show(
							"cancel the subtraction in the polynomial ring",
							ByArith(polynomial.PolynomialRingOn.Read(subring), carrier, rDef))
					}))
				evaluationSum := b.Have(
					"the evaluations satisfy the same cancellation",
					"polynomial_eval(r, x) + polynomial_eval(q, x) = polynomial_eval(q, x)",
					By(
						cancelPolynomials,
						evalSum,
						relationOver,
						lower,
						h,
						polynomial_evaluation.EvalBasisVector.Read(ring).At(N, proof.MemberOf(x, xIn))))
				evaluationsIn := b.Have(
					"both evaluations lie in L",
					"polynomial_eval(r, x) ∈ L.carrier ∧ polynomial_eval(q, x) ∈ L.carrier",
					By(polynomial_evaluation.EvalIn.Read(ring), relationOver, lower, overL, h))
				root := b.Have(
					"the constructed polynomial vanishes at x",
					"polynomial_eval(r, x) = L.zero",
					ByArith(ring, evaluationSum, evaluationsIn))
				positive := b.Have(
					"its degree is positive",
					"0 < polynomial_degree(r)",
					ByArith(degree, nDef))
				b.Do(Unfold(integral_element.IntegralOverDef))
				b.Take(r)
				b.Show(
					"this positive-degree monic relation witnesses integrality",
					By(relationOver, monic, positive, root))
			})
	}),
})}

// StableModuleIntegral — an element of a field stabilizing a finitely
// generated submodule containing one is integral over the subring of scalars:
// a finite generating set spans that submodule inside the field, one is a
// nonzero member of it, and the finitely spanned criterion applies.
var StableModuleIntegral = stableModuleIntegralThm{family.Add(registry.ProofEntry{
	Name: "StableModuleIntegral",
	Key:  "prop_7c6c121a9f5fad41",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x:A. ∀M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), M)",
			"module_finitely_generated(restrict_ring(field_ring(L), S), " +
				"    restrict_module(regular_module(field_ring(L)), M))",
			"L.one ∈ M",
			"image(L.mul(x), M) ⊆ M",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(L), S), x)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		x *Expr[A],
		M *Expr[Set[A]],
		h Fact,
	) {
		parts := a.Conjuncts(
			h,
			"S is a subring of L",
			"x lies in L",
			"M is an S-submodule",
			"M is finitely generated",
			"M contains one",
			"multiplication by x preserves M")
		subS, xIn, subM, finiteM, one, stable := parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
		space := a.Have(
			"L is an S-module",
			"module_on(restrict_ring(field_ring(L), S), regular_module(field_ring(L)))",
			By(subS, module.RegularModuleOverSubring.Read(field.RingOn.Read(L)).At(S)))
		E, given := a.UnpackAs[Set[A]](a.Unfolded(finiteM, FinitelyGeneratedDef), "E")
		generators := a.Conjuncts(
			given,
			"E is finite",
			"E lies in M",
			"E spans M inside M")
		spanned := a.Have(
			"lying in M, E spans M inside L as well",
			"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), E) = M",
			By(subM, generators[1], generators[2], linear_independence.SpanningRestrict.Read(space).At(M, E)))
		inField := a.Have(
			"so E lies in L",
			"E ⊆ L.carrier",
			BySets(generators[1], submodule.SubmoduleSubset.Read(subM)))
		nonzero := a.Have(
			"M holds one, which is not zero",
			"∃v:A. v ∈ M ∧ v ≠ L.zero",
			By(one, field.OneNotZeroOn.Read(L)))
		a.Show(
			"M is spanned by finitely many members of L and stable under x",
			By(
				subS,
				generators[0],
				inField,
				spanned,
				stable,
				nonzero,
				integral_element.FinitelySpannedIntegral.Read(L).At(S, M, E, a.MemberOf[on.L](x, xIn))))
	}),
})}

// FiniteSubringIntegral — every element of a subring N of a field, finite as a
// module over a subring S inside it, is integral over S: N is a finitely
// generated module holding one, and multiplying by the element keeps it.
var FiniteSubringIntegral = finiteSubringIntegralThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubringIntegral",
	Key:  "prop_9f9959c93407ebf9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N:set(A). ∀z:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subring(field_ring(L), N)",
			"S ⊆ N",
			"module_finitely_generated(restrict_ring(field_ring(L), S), " +
				"    restrict_module(regular_module(field_ring(L)), N))",
			"z ∈ N",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(L), S), z)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			S, N *Expr[Set[A]],
			z *Expr[A],
			subS, subN, SInN, finite, zIn Fact,
		) {
			l := a.TermAs[FieldOps[A]]("L")
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			product := a.TermAs[Fun[A, A]]("L.mul(z)")
			zInField := a.Have(
				"z lies in the field",
				"z ∈ L.carrier",
				By(subN, zIn, comm_ring.SubringSubset.At(ring, N), set_basic.SubsetDef))
			zm := a.MemberOf[on.L](z, zInField)
			stable := a.Have(
				"multiplying by z keeps N",
				"image(L.mul(z), N) ⊆ N",
				By(subN, zIn, set_image.ImageSubsetIff.At(product, N, N), At(comm_ring.SubringMul, ring, N)))
			a.Show(
				"N is a finite module holding one and stable under z",
				By(
					subS,
					subN,
					finite,
					zm,
					stable,
					SInN,
					comm_ring.SubringOne.At(ring, N),
					ConstantSubringSubmodule.At(l, S, N),
					StableModuleIntegral.Read(L).At(S, zm, N)))
		}),
})}

// IntegralTowerOverPrincipal — integrality climbs a finite tower: x integral
// over B, finite over the subring S, lies in the subring B[x], finite over B
// and so over S.
var IntegralTowerOverPrincipal = integralTowerOverPrincipalThm{family.Add(registry.ProofEntry{
	Name: "IntegralTowerOverPrincipal",
	Key:  "prop_ab1da8feff9ef775",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "Bx", Text: "polynomial_image(field_ring(L), B, x)"},
		},
		Binders: "∀L:field_on(A). ∀S B:set(A). ∀x:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"S ⊆ B",
			"module_finitely_generated(restrict_ring(field_ring(L), S), " +
				"    restrict_module(regular_module(field_ring(L)), B))",
			"x ∈ L.carrier",
			"integral_over(restrict_ring(field_ring(L), B), x)",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(L), S), x)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			S, B *Expr[Set[A]],
			x *Expr[A],
			subS, subB, SInB, finiteB, xIn, integralX Fact,
		) {
			l := a.TermAs[FieldOps[A]]("L")
			Bx := a.TermAs[Set[A]]("«Bx»")
			xm := a.MemberOf[on.L](x, xIn)
			top := a.Conjuncts(
				GroupPremises(subB, algebraic_element.PolynomialImageSubring.Read(L).At(B, xm)),
				"B[x] is a subring",
				"B[x] holds B",
				"B[x] holds x")
			subBx, BInBx, xInBx := top[0], top[1], top[2]
			polynomialsOverB := a.Conjuncts(
				GroupPremises(subB, integralX, IntegralPolynomialModule.Read(L).At(B, xm)),
				"B[x] is a submodule over B",
				"B[x] is finite over B",
				"B[x] holds one",
				"x keeps B[x]")
			tower := a.Conjuncts(
				GroupPremises(
					L,
					SInB,
					subS,
					subB,
					finiteB,
					polynomialsOverB[0],
					polynomialsOverB[1],
					FiniteModuleTower.At(l, S, B, Bx)),
				"B[x] is a submodule over S",
				"B[x] is finite over S")
			SInBx := a.Have(
				"B[x] holds S",
				"S ⊆ «Bx»",
				BySets(SInB, BInBx))
			a.Show(
				"x lies in a subring finite over S",
				By(L, subS, subBx, SInBx, tower[1], xInBx, FiniteSubringIntegral.At(l, S, Bx, x)))
		}),
})}

// ConstantSubringSubmodule — a subring T of the field holding l is a submodule
// over l: T is a submodule over itself, and the scalars of l are scalars of T.
var ConstantSubringSubmodule = constantSubringSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "ConstantSubringSubmodule",
	Key:  "prop_a9da51febd9ccdde",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀l T:set(A).",
		Hypotheses: []string{
			"subring(field_ring(M), T)",
			"l ⊆ T",
		},
		Conclusion: "submodule(restrict_ring(field_ring(M), l), regular_module(field_ring(M)), T)",
	},
		func(a *Argument, M field.FieldFact[on.M], l, T *Expr[Set[A]], subring, lInT Fact) {
			overT := a.Have(
				"T is a submodule of the field over itself",
				"submodule(restrict_ring(field_ring(M), T), regular_module(field_ring(M)), T)",
				By(subring, fractional_ideal.SubringSubmodule.Read(M).At(T)))
			a.Show(
				"and the scalars of l are scalars of T",
				By(
					lInT,
					submodule.SubmoduleRestrictScalars.Read(overT).At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), l)"))))
		}),
})}
