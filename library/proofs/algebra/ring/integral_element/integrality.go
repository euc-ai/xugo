// integrality.go — the polynomial values S[x] over a subring S, for x a root
// of a monic polynomial p over S: they form an S-submodule of the field, each
// is the value of a polynomial over S vanishing from the degree of p on, so
// the powers of x below that degree span them, and a basis when p is the
// minimal polynomial.

package integral_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// PolynomialImageSubmodule — polynomial values over a subring form a
// submodule of the ambient field: S[x] is a subring of L holding S, so a
// submodule of L over its own scalars, and restricting those scalars to S
// keeps a submodule.
var PolynomialImageSubmodule = polynomialImageSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "PolynomialImageSubmodule",
	Key:  "prop_1cc824853308ce99",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
		},
		Conclusion: "submodule(restrict_ring(field_ring(L), S), " +
			"    regular_module(field_ring(L)), " +
			"    polynomial_image(field_ring(L), S, x))",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], x *Expr[A], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a subring of L",
			"x lies in L")
		xIn := parts[1]
		Sx := a.TermAs[Set[A]]("polynomial_image(field_ring(L), S, x)")
		subring := a.Conjuncts(
			GroupPremises(
				parts[0], algebraic_element.PolynomialImageSubring.Read(L).At(S, a.MemberOf[on.L](x, xIn))),
			"S[x] is a subring of L",
			"S lies in S[x]",
			"x lies in S[x]")
		selfModule := a.Have(
			"a subring of L, S[x] is a submodule of L over its own scalars",
			"submodule(restrict_ring(field_ring(L), polynomial_image(field_ring(L), S, x)), "+
				"    regular_module(field_ring(L)), "+
				"    polynomial_image(field_ring(L), S, x))",
			By(subring[0], fractional_ideal.SubringSubmodule.Read(L).At(Sx)))
		a.Show(
			"restricting the scalars to S, which lies in S[x], keeps a submodule",
			By(
				subring[1],
				submodule.SubmoduleRestrictScalars.Read(selfModule).At(
					a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)"))))
	}),
})}

// IntegralShortRepresentative — when x is a root of a monic polynomial p over a
// subring S, every member y of S[x] is the value at x of a polynomial over S
// vanishing from the degree of p on. Write y = f(x) and divide f by p: the
// multiple of p vanishes at x, so y is the value of the remainder.
var IntegralShortRepresentative = integralShortRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "IntegralShortRepresentative",
	Key:  "prop_143da0c3a7f78cfb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x y:A. ∀p:(num → A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
			"polynomial_over(S, p)",
			"polynomial_monic(p)",
			"polynomial_eval(p, x) = L.zero",
			"y ∈ polynomial_image(field_ring(L), S, x)",
		},
		Conclusion: "∃r:(num → A). " +
			"    polynomial_over(S, r) ∧ vec⟨polynomial_degree(p)⟩(r) ∧ y = polynomial_eval(r, x)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		x, y *Expr[A],
		p *Arrow[Nat, A],
		subS, xIn, pOver, monic, root, yIn Fact,
	) {
		ring := field.RingOn.Read(L)
		xM := a.MemberOf[on.L](x, xIn)
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(subS, comm_ring.SubringRingOn.Read(ring).At(S)))
		values := a.Have(
			"a member of S[x] is the value at x of a polynomial over S",
			"∀v:A. "+
				"    v ∈ polynomial_image(field_ring(L), S, x) ⇔ "+
				"    ∃f:(num → A). polynomial_over(S, f) ∧ v = polynomial_eval(f, x)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTacMembership())
		f, represented := a.ObtainAs[Fun[Nat, A]](
			"y is the value at x of a polynomial f over S",
			"∃f:(num → A). polynomial_over(S, f) ∧ y = polynomial_eval(f, x)",
			By(values.At(y), yIn))
		q, u, divided := a.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
			"divide f by the monic polynomial p",
			"∃q u:(num → A). "+
				"    polynomial_over(S, q) ∧ "+
				"    polynomial_over(S, u) ∧ "+
				"    vec⟨polynomial_degree(p)⟩(u) ∧ "+
				"    f = polynomial_mul(p, q) + u",
			By(represented, pOver, monic, polynomial_division.MonicDivisionExists.Read(ringS).At(f, p)))
		division := a.Conjuncts(
			divided,
			"q is over S",
			"u is over S",
			"u vanishes from the degree of p on",
			"f = p q + u")
		qOver, uOver, uPast, decomposition := division[0], division[1], division[2], division[3]
		inside := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subS)))
		ambient := a.Have(
			"p, q and u are polynomials over L",
			"polynomial_over(L.carrier, p) ∧ polynomial_over(L.carrier, q) ∧ polynomial_over(L.carrier, u)",
			By(inside, pOver, qOver, uOver, polynomial.PolynomialOverMono))
		product := a.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)")
		productOver := a.Have(
			"so is their product p q",
			"polynomial_over(L.carrier, polynomial_mul(p, q))",
			By(ambient, polynomial.PolynomialMulOver.Read(ring).At(p, q)))
		productZero := a.Have(
			"a multiple of p vanishes at x",
			"polynomial_eval(polynomial_mul(p, q), x) = L.zero",
			By(ambient, root, polynomial_evaluation.EvalMulRoot.Read(ring).At(p, q, xM)))
		evalSum := a.Have(
			"evaluation adds the values of p q and u",
			"polynomial_eval(polynomial_mul(p, q) + u, x) = "+
				"polynomial_eval(polynomial_mul(p, q), x) + polynomial_eval(u, x)",
			By(productOver, ambient, polynomial_evaluation.EvalAdd.Read(ring).At(product, u, xM)))
		remainderIn := a.Have(
			"the value of u lies in L",
			"polynomial_eval(u, x) ∈ L.carrier",
			By(ambient, polynomial_evaluation.EvalIn.Read(ring).At(u, xM)))
		removeZero := a.Have(
			"zero adds nothing to that value",
			"L.zero + polynomial_eval(u, x) = polynomial_eval(u, x)",
			ByArith(ring, remainderIn))
		sameValue := a.Have(
			"f and its remainder u have the same value at x",
			"polynomial_eval(f, x) = polynomial_eval(u, x)",
			CalcEq(
				Leg(
					a.TermAs[A]("polynomial_eval(polynomial_mul(p, q) + u, x)"),
					"use the division identity",
					decomposition.Rw(),
					Basic()),
				Leg(
					a.TermAs[A]("polynomial_eval(polynomial_mul(p, q), x) + polynomial_eval(u, x)"),
					"evaluation adds",
					By(evalSum)),
				Leg(
					a.TermAs[A]("L.zero + polynomial_eval(u, x)"),
					"the multiple of p vanishes",
					productZero.Rw(),
					Basic()),
				FinalLeg(
					"zero adds nothing",
					By(removeZero)),
			))
		a.Take(u)
		a.Show(
			"u is over S, vanishes from the degree of p on, and has the value y of f at x",
			By(Normalized, represented, uOver, uPast, sameValue))
	}),
})}

// IntegralPowerSpan — a monic relation makes the short powers span S[x].
// Every member of S[x] is the value of a polynomial vanishing from the degree
// of the relation on (IntegralShortRepresentative), an S-combination of the
// short powers. Conversely, polynomial values form an S-submodule containing
// every generating power.
var IntegralPowerSpan = integralPowerSpanThm{family.Add(registry.ProofEntry{
	Name: "IntegralPowerSpan",
	Key:  "prop_5afdcc8a8520e73c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x:A. ∀p:(num → A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
			"polynomial_over(S, p)",
			"polynomial_monic(p)",
			"polynomial_eval(p, x) = L.zero",
		},
		Conclusion: "polynomial_image(field_ring(L), S, x) = " +
			"module_span(restrict_ring(field_ring(L), S), " +
			"    regular_module(field_ring(L)), " +
			"    {monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)})",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		x *Expr[A],
		p *Arrow[Nat, A],
		h Fact,
	) {
		parts := a.Conjuncts(
			h,
			"S is a subring of L",
			"x lies in L",
			"p is over S",
			"p is monic",
			"p vanishes at x")
		subring, xIn, pOver, monic, root := parts[0], parts[1], parts[2], parts[3], parts[4]
		ring := field.RingOn.Read(L)
		inside := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subring)))
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(subring, comm_ring.SubringRingOn.Read(ring).At(S)))
		xM := a.MemberOf[on.L](x, xIn)
		shortPowers, powersDefined := a.LetAs[Set[A]](
			"B", "{monoid_pow(L.mul, L.one, x, i) | i:num | i < polynomial_degree(p)}")
		span, spanDefined := a.LetAs[Set[A]](
			"V", "module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), B)")
		scalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		image := a.TermAs[Set[A]]("polynomial_image(field_ring(L), S, x)")
		degree := a.TermAs[Nat]("polynomial_degree(p)")
		values := a.Have(
			"membership is representation by a polynomial value",
			"∀y:A. "+
				"    y ∈ polynomial_image(field_ring(L), S, x) ⇔ "+
				"    ∃f:(num → A). polynomial_over(S, f) ∧ y = polynomial_eval(f, x)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTacMembership())
		space := a.Have(
			"L is a module over S",
			"module_on(restrict_ring(field_ring(L), S), regular_module(field_ring(L)))",
			By(module.RegularModuleOverSubring.Read(ring), subring))
		powersInL := a.Have(
			"all powers of x lie in L",
			"∀i:num. monoid_pow(L.mul, L.one, x, i) ∈ L.carrier",
			By(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)), xIn))
		powersInside := a.Have(
			"the short powers lie in L",
			"B ⊆ L.carrier",
			BySets(powersDefined, powersInL))
		spanSubmodule := a.Have(
			"their span is an S-submodule of L",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), V)",
			By(Normalized, submodule.SpanSubmodule.Read(space).At(shortPowers), powersInside, spanDefined))
		powersInSpan := a.Have(
			"the span contains each short power",
			"∀i:num. i < polynomial_degree(p) ⇒ monoid_pow(L.mul, L.one, x, i) ∈ V",
			BySets(powersDefined, spanDefined, submodule.SubsetSpan.At(scalars, vectors, shortPowers)))

		// The reverse inclusion uses only closure of polynomial values under S.
		imageSubmodule := a.Have(
			"polynomial values form an S-submodule",
			"submodule(restrict_ring(field_ring(L), S), "+
				"    regular_module(field_ring(L)), "+
				"    polynomial_image(field_ring(L), S, x))",
			By(subring, PolynomialImageSubmodule.Read(L).At(S, xM)))
		powerValues := a.Have(
			"each power is the value of a basis-vector polynomial",
			"∀i:num. "+
				"    polynomial_over(S, basis_vector(i)) ∧ "+
				"    polynomial_eval(basis_vector(i), x) = monoid_pow(L.mul, L.one, x, i)",
			By(polynomial.BasisVectorOver.Read(ringS), polynomial_evaluation.EvalBasisVector.Read(ring), xIn))
		powersInImage := a.Have(
			"polynomial values contain every power",
			"∀i:num. monoid_pow(L.mul, L.one, x, i) ∈ polynomial_image(field_ring(L), S, x)",
			By(values, powerValues))
		shortPowersInImage := a.Have(
			"in particular they contain the short powers",
			"B ⊆ polynomial_image(field_ring(L), S, x)",
			BySets(powersDefined, powersInImage))
		spanInImage := a.Have(
			"and therefore contain their span",
			"V ⊆ polynomial_image(field_ring(L), S, x)",
			By(
				Normalized,
				spanDefined,
				shortPowersInImage,
				imageSubmodule,
				submodule.SpanLeast.At(scalars, vectors, shortPowers, image)))
		overL := a.Have(
			"a polynomial over S is one over L",
			"∀f:(num → A). polynomial_over(S, f) ⇒ polynomial_over(L.carrier, f)",
			By(inside, polynomial.PolynomialOverMono))

		// A short remainder evaluates to a finite sum of scalar multiples of B.
		shortValues := a.Have(
			"every short polynomial has its value in the span",
			"∀r:(num → A). polynomial_over(S, r) ∧ vec⟨polynomial_degree(p)⟩(r) ⇒ polynomial_eval(r, x) ∈ V",
			Derive(func(b *Argument) {
				r := b.FixAs[Fun[Nat, A]]("r")
				given := b.Assume()
				short := b.Conjuncts(
					given,
					"r is over S",
					"r vanishes from p's degree on")
				rOver, rPast := short[0], short[1]
				rOverL := b.Have(
					"r is a polynomial over L",
					"polynomial_over(L.carrier, r)",
					By(rOver, overL.At(r)))
				value := b.Have(
					"its value is the sum of its terms below p's degree",
					"polynomial_eval(r, x) = "+
						"module_sum(L.add, "+
						"    L.zero, "+
						"    {i:num | i < polynomial_degree(p)}, "+
						"    λi:num. r(i) * monoid_pow(L.mul, L.one, x, i))",
					By(rOverL, polynomial_evaluation.EvalBelow.Read(ring).At(proof.InhabitFrom(r, rPast), xM)))
				coefficients := b.Have(
					"each coefficient belongs to S",
					"∀i:num. r(i) ∈ S",
					By(rOver, polynomial.PolynomialOverDef))
				terms := b.Have(
					"each term is an S-multiple of a short power",
					"∀i:num. i ∈ {j:num | j < polynomial_degree(p)} ⇒ r(i) * monoid_pow(L.mul, L.one, x, i) ∈ V",
					BySets(submodule.SubmoduleSmul.Read(spanSubmodule), coefficients, powersInSpan))
				below := b.TermAs[Set[Nat]]("{i:num | i < polynomial_degree(p)}")
				summand := b.TermAs[Fun[Nat, A]]("λi:num. r(i) * monoid_pow(L.mul, L.one, x, i)")
				b.Show(
					"the submodule contains their finite sum",
					By(
						value,
						terms,
						spanSubmodule,
						num_segment.FiniteBelowStrict.At(degree),
						submodule.SubmoduleModuleSum.Read(space).At(span, below, summand)))
			}))
		imageInSpan := a.Have(
			"every polynomial value is the value of a short polynomial, so lies in the span",
			"polynomial_image(field_ring(L), S, x) ⊆ V",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				yIn := b.Assume()
				r, short := b.ObtainAs[Fun[Nat, A]](
					"y is the value at x of a polynomial r over S vanishing from the degree of p on",
					"∃r:(num → A). polynomial_over(S, r) ∧ vec⟨polynomial_degree(p)⟩(r) ∧ y = polynomial_eval(r, x)",
					By(subring, pOver, monic, root, yIn, IntegralShortRepresentative.Read(L).At(S, xM, y, p)),
					Named("r"))
				b.Show(
					"and the value of a short polynomial lies in the span",
					By(Normalized, short, shortValues.At(r)))
			}))
		a.Show(
			"the polynomial values equal the span of the short powers",
			By(imageInSpan, spanInImage, set_order.SubsetAntisym))
	}),
})}

// MonicSubringPowerBasis — a minimal polynomial over a subring gives the short
// power basis of its polynomial image. Monic division supplies spanning; the
// power basis of K(y) over K supplies independence and the number of distinct
// powers.
var MonicSubringPowerBasis = monicSubringPowerBasisThm{family.Add(registry.ProofEntry{
	Name: "MonicSubringPowerBasis",
	Key:  "prop_3c752c78aba9000a",
	Reading: "The minimal polynomial must have coefficients in S: in Q(√2), " +
		"K=Q, S=Z and y=1/√2 have μ=T²−1/2; without that hypothesis the powers " +
		"{1,y} do not span S[y], since y²=1/2 is not an integer combination of them.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"polynomial_over(S, minimal_polynomial(L, K, y))",
		},
		Conclusion: "module_on(restrict_ring(field_ring(L), S), " +
			"    restrict_module(regular_module(field_ring(L)), polynomial_image(field_ring(L), S, y))) ∧ " +
			"module_basis(restrict_ring(field_ring(L), S), " +
			"    restrict_module(regular_module(field_ring(L)), polynomial_image(field_ring(L), S, y)), " +
			"    {monoid_pow(L.mul, L.one, y, i) | " +
			"        i:num | " +
			"        i < polynomial_degree(minimal_polynomial(L, K, y))}) ∧ " +
			"has_size({monoid_pow(L.mul, L.one, y, i) | " +
			"        i:num | " +
			"        i < polynomial_degree(minimal_polynomial(L, K, y))}, " +
			"    polynomial_degree(minimal_polynomial(L, K, y)))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, S *Expr[Set[A]], y *Expr[A], h Fact) {
			parts := a.Conjuncts(
				h,
				"K is a subfield of L",
				"y lies in L",
				"y is algebraic over K",
				"S lies in K",
				"S is a subring of L",
				"the minimal polynomial has coefficients in S")
			subK, yIn, algebraic, scalarsInside, subS, polynomialOverS :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			yM := a.MemberOf[on.L](y, yIn)
			B, powersDefined := a.LetAs[Set[A]](
				"B",
				"{monoid_pow(L.mul, L.one, y, i) | i:num | i < polynomial_degree(minimal_polynomial(L, K, y))}")
			N, imageDefined := a.LetAs[Set[A]]("N", "polynomial_image(field_ring(L), S, y)")
			scalarsS := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
			scalarsK := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), K)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			minpoly := a.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, y)")
			adjoin := a.TermAs[Set[A]]("field_adjoin(L, K, {y})")
			ambientModule := a.Have(
				"L is a module over the subring S",
				"module_on(restrict_ring(field_ring(L), S), regular_module(field_ring(L)))",
				By(module.RegularModuleOverSubring.Read(field.RingOn.Read(L)), subS))
			imageSubmodule := a.Have(
				"polynomial values form an S-submodule of L",
				"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), N)",
				By(Normalized, imageDefined, yIn, subS, PolynomialImageSubmodule.Read(L).At(S, yM)))
			powers := a.Conjuncts(
				a.Have(
					"the short powers, a K-basis of K(y), are K-linearly independent in L and have the required size",
					"module_independent(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), B) ∧ "+
						"has_size(B, polynomial_degree(minimal_polynomial(L, K, y)))",
					By(
						powersDefined,
						subK,
						algebraic,
						algebraic_element.AdjoinPowerBasis.Read(L).At(K, yM),
						algebraic_element.AdjoinElementSubfield.Read(L).At(K, yM),
						field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), adjoin),
						linear_independence.ModuleBasisDef.At(
							scalarsK,
							a.TermAs[module_record.ModuleOps[A, A]](
								"restrict_module(regular_module(field_ring(L)), field_adjoin(L, K, {y}))"),
							B),
						linear_independence.IndependentRestrict.At(scalarsK, vectors, adjoin, B))),
				"the short powers are K-linearly independent in L",
				"there are as many of them as the degree")
			independentOverK, size := powers[0], powers[1]
			independentOverS := a.Have(
				"a relation with coefficients in S is a relation with coefficients in K",
				"module_independent(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), B)",
				By(
					Normalized,
					scalarsInside,
					independentOverK,
					linear_independence.ModuleIndependentDef.At(scalarsK, vectors, B),
					linear_independence.ModuleIndependentDef.At(scalarsS, vectors, B),
					set_basic.SubsetDef.At(S, K)))
			spanning := a.Have(
				"the monic minimal relation reduces every polynomial value to the short power span",
				"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), B) = N",
				By(
					powersDefined,
					imageDefined,
					yIn,
					subK,
					subS,
					algebraic,
					polynomialOverS,
					algebraic_element.MinimalPolynomialSpec.Read(L).At(K, yM),
					IntegralPowerSpan.Read(L).At(S, yM, minpoly)))
			basis := a.Have(
				"independence and spanning give the basis on the restricted carrier",
				"module_basis(restrict_ring(field_ring(L), S), "+
					"    restrict_module(regular_module(field_ring(L)), N), "+
					"    B)",
				By(
					spanning,
					independentOverS,
					imageSubmodule,
					linear_independence.BasisRestrict.Read(ambientModule).At(N, B)))
			a.Show(
				"the polynomial image is free over S on the short powers",
				By(size, submodule.SubmoduleModuleOn.Read(ambientModule), imageSubmodule, basis))
		}),
})}
