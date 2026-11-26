// regularity.go — the regularity of a quadratic fibre: over a polynomial
// ring k[t] inside a field, the ideal (p(t), w − r(t)) of a fibre of
// w² = F(t) is invertible wherever 2w and F′(t) span the ring, and with it
// every maximal ideal of k[t] + k[t]·w (QuadraticChartMaximalInvertible);
// and the Weierstrass cubic X³ + aX + b, the F of chart zero, as a
// polynomial over k (WeierstrassCubicPolynomial).

package closed_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// QuadraticFibreIdealInvertible — the Jacobian criterion for a quadratic
// fibre: when 2w and F′(t) span S, the ideal m = (p(t), w − r(t)) of S is
// invertible. Write P = p(t), R = r(t) and w² − R² = h · P with h in k[t],
// and let I be the ideal of S spanned by P, w − R, w + R and h. It holds
// 2w = (w + R) + (w − R). With h = q(t), transcendence lifts w² = F(t) to
// the identity F = r·r + p·q of polynomials, whose derivative at t is
// r′(t)·((w + R) − (w − R)) + p′(t)·h + q′(t)·P; so I holds F′(t) as well,
// and with 2w all of S. RelationIdealInvertible at P ≠ 0 and the relation
// (w − R)·(w + R) = P·h then makes m invertible.
var QuadraticFibreIdealInvertible = quadraticFibreIdealInvertibleThm{family.Add(registry.ProofEntry{
	Name: "QuadraticFibreIdealInvertible",
	Key:  "prop_2de7065962fba886",
	Reading: "No basis, maximality or irreducibility is asked: the two generators of " +
		"m and the Jacobian pair are the whole input. Nor is 2 ≠ 0: 2w enters as (w + R) " +
		"+ (w − R), never inverted, and in characteristic 2 the pair spans S through " +
		"F′(t) alone. p ≠ 0 is load-bearing, making P a unit of L by transcendence.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S:set(A). ∀t w:A. ∀F p r:(num → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"subring(field_ring(L), S)",
			"polynomial_image(field_ring(L), k, t) ⊆ S",
			"w ∈ S",
			"polynomial_over(k, F)",
			"w * w = polynomial_eval(F, t)",
			"ideal_span(restrict_ring(field_ring(L), S), " +
				"    {w + w, polynomial_eval(polynomial_derivative(F), t)}) = " +
				"S",
			"polynomial_over(k, p)",
			"p ≠ vec_zero",
			"polynomial_over(k, r)",
			"w * w - polynomial_eval(r, t) * polynomial_eval(r, t) ∈ " +
				"ideal_span(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t)), " +
				"    {polynomial_eval(p, t)})",
		},
		Conclusion: "invertible_fractional(field_ring(L), " +
			"    S, " +
			"    ideal_span(restrict_ring(field_ring(L), S), " +
			"        {polynomial_eval(p, t), w - polynomial_eval(r, t)}))",
		Abbrev: Abbrev{
			{Name: "kt", Text: "polynomial_image(field_ring(L), k, t)"},
			{Name: "I", Text: "ideal_span(restrict_ring(field_ring(L), S), " +
				"    {polynomial_eval(p, t), w - polynomial_eval(r, t), w + polynomial_eval(r, t), h})"},
			{Name: "derivativeAt", Text: "λf:(num → A). polynomial_eval(polynomial_derivative(f), t)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, S *Expr[Set[A]],
		t, w *Expr[A],
		F, p, r *Arrow[Nat, A],
		hypotheses Fact,
	) {
		given := a.Conjuncts(
			hypotheses,
			"k is a subfield of L",
			"t lies in L",
			"t is transcendental over k",
			"S is a subring of L",
			"S holds k[t]",
			"w lies in S",
			"F is a polynomial over k",
			"w² is the value of F at t",
			"2w and F′(t) span S",
			"p is a polynomial over k",
			"p is not the zero polynomial",
			"r is a polynomial over k",
			"w² − r(t)² lies in the ideal of k[t] that p(t) generates")
		kSubfield, tInL, transcendental, subring, imageInS, wInS :=
			given[0], given[1], given[2], given[3], given[4], given[5]
		fOver, wSquare, jacobian, pOver, pNonzero, rOver, fibre :=
			given[6], given[7], given[8], given[9], given[10], given[11], given[12]
		ringL := field.RingOn.Read(L)
		tm := a.MemberOf[on.L](t, tInL)
		P, R := a.TermAs[A]("polynomial_eval(p, t)"), a.TermAs[A]("polynomial_eval(r, t)")
		plus, minus := a.TermAs[A]("w + polynomial_eval(r, t)"), a.TermAs[A]("w - polynomial_eval(r, t)")
		kt := a.TermAs[Set[A]]("«kt»")
		ringOfS := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")

		// k[t], the cofactor h with w² − r(t)² = h · p(t), and h = q(t).
		values := a.Have(
			"k[t] is the set of values at t of the polynomials over k",
			"∀z:A. z ∈ «kt» ⇔ ∃f:(num → A). polynomial_over(k, f) ∧ z = polynomial_eval(f, t)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTacMembership())
		ktRing := a.Have(
			"k[t] is a ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), «kt»))",
			By(
				kSubfield,
				algebraic_element.PolynomialImageRing.Read(L).At(k, tm),
				comm_ring.SubringRingOn.Read(ringL).At(kt)))
		valuesInImage := a.Have(
			"p(t) and r(t) lie in k[t]",
			"polynomial_eval(p, t) ∈ «kt» ∧ polynomial_eval(r, t) ∈ «kt»",
			By(pOver, rOver, values.At(P), values.At(R)))
		h, cofactor := a.ObtainAs[A](
			"w² − r(t)² is h · p(t) for some h in k[t]",
			"∃h:A. "+
				"    h ∈ «kt» ∧ w * w - polynomial_eval(r, t) * polynomial_eval(r, t) = h * polynomial_eval(p, t)",
			BySets(fibre, valuesInImage, ring_ideal.PrincipalIdealMultiples.Read(ktRing).AsFact().At(P)))
		cofactorParts := a.Conjuncts(
			cofactor,
			"h lies in k[t]",
			"w² − r(t)² = h · p(t)")
		hInImage, relation := cofactorParts[0], cofactorParts[1]
		q, cofactorPolynomial := a.ObtainAs[Fun[Nat, A]](
			"h is the value at t of a polynomial q over k",
			"∃q:(num → A). polynomial_over(k, q) ∧ h = polynomial_eval(q, t)",
			By(hInImage, values.At(h)))
		qParts := a.Conjuncts(
			cofactorPolynomial,
			"q is a polynomial over k",
			"h = q(t)")
		qOver, hValue := qParts[0], qParts[1]

		// The elements in play lie in S and in L.
		sInL := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subring)))
		ringS := a.Have(
			"S is a ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(subring, comm_ring.SubringRingOn.Read(ringL).At(S)))
		inS := a.Have(
			"p(t), r(t) and h lie in S, as k[t] does",
			"polynomial_eval(p, t) ∈ S ∧ polynomial_eval(r, t) ∈ S ∧ h ∈ S",
			BySets(imageInS, valuesInImage, hInImage))
		inL := a.Have(
			"they and w lie in L, as S does",
			"polynomial_eval(p, t) ∈ L.carrier ∧ "+
				"polynomial_eval(r, t) ∈ L.carrier ∧ "+
				"h ∈ L.carrier ∧ "+
				"w ∈ L.carrier",
			BySets(sInL, inS, wInS))
		conjugatesInS := a.Have(
			"w + r(t) and w − r(t) lie in S",
			"w + polynomial_eval(r, t) ∈ S ∧ w - polynomial_eval(r, t) ∈ S",
			By(
				wInS,
				inS,
				comm_ring.AddIn.Read(ringS).AsFact().At(w, R),
				comm_ring.SubIn.Read(ringS).AsFact().At(w, R)))

		// The polynomial identity F = r·r + p·q and the value of its derivative at t.
		kRing := a.Have(
			"k is a ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), k))",
			By(kSubfield, field.SubfieldCommRing.Read(L).At(k)))
		kInL := a.Have(
			"k lies in L",
			"k ⊆ L.carrier",
			By(kSubfield, field.SubfieldSubset))
		products := a.Have(
			"r·r and p·q are polynomials over k, taking the values r(t)² and p(t)·h at t",
			"polynomial_over(k, polynomial_mul(r, r)) ∧ "+
				"polynomial_over(k, polynomial_mul(p, q)) ∧ "+
				"polynomial_eval(polynomial_mul(r, r), t) = polynomial_eval(r, t) * polynomial_eval(r, t) ∧ "+
				"polynomial_eval(polynomial_mul(p, q), t) = polynomial_eval(p, t) * h",
			By(
				hValue,
				tInL,
				kSubfield,
				pOver,
				qOver,
				rOver,
				polynomial_evaluation.PolynomialProductData.Read(L).At(k, r, r),
				polynomial_evaluation.PolynomialProductData.Read(L).At(k, p, q)))
		productParts := a.Conjuncts(
			products,
			"r·r is a polynomial over k",
			"p·q is a polynomial over k",
			"r·r takes the value r(t)² at t",
			"p·q takes the value p(t)·h at t")
		sum := a.TermAs[Fun[Nat, A]]("polynomial_mul(r, r) + polynomial_mul(p, q)")
		sumOver := a.Have(
			"r·r + p·q is a polynomial over k",
			"polynomial_over(k, polynomial_mul(r, r) + polynomial_mul(p, q))",
			BySets(
				productParts[0],
				productParts[1],
				comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(kRing))))
		productsOverL := a.Have(
			"r·r and p·q are polynomials over L",
			"polynomial_over(L.carrier, polynomial_mul(r, r)) ∧ "+
				"polynomial_over(L.carrier, polynomial_mul(p, q))",
			By(kInL, productParts[0], productParts[1], polynomial.PolynomialOverMono))
		agree := a.Have(
			"F and r·r + p·q take one value at t, w² = r(t)² + p(t)·h",
			"polynomial_eval(F, t) = polynomial_eval(polynomial_mul(r, r) + polynomial_mul(p, q), t)",
			Simp(
				Fwd(polynomial_evaluation.EvalAdd.Read(ringL)),
				Fwd(productsOverL),
				Fwd(productParts[2]),
				Fwd(productParts[3])),
			ByArith(L, wSquare, relation, inL))
		identity := a.Have(
			"so F = r·r + p·q, evaluation at the transcendental t being one-to-one",
			"F = polynomial_mul(r, r) + polynomial_mul(p, q)",
			By(
				kSubfield,
				transcendental,
				fOver,
				sumOver,
				agree,
				algebraic_element.EvalInjectiveTranscendental.Read(L).At(k, tm, F, sum)))
		coefficients := a.Have(
			"the coefficients of r, p and q lie in k",
			"∀i:num. r(i) ∈ k ∧ p(i) ∈ k ∧ q(i) ∈ k",
			By(pOver, qOver, rOver, polynomial.PolynomialOverDef))
		additive := a.Have(
			"the sum rule splits the derivative of r·r + p·q, the coefficients of both products lying in k",
			"polynomial_derivative(polynomial_mul(r, r) + polynomial_mul(p, q)) = "+
				"polynomial_derivative(polynomial_mul(r, r)) + polynomial_derivative(polynomial_mul(p, q))",
			By(
				productParts[0],
				productParts[1],
				polynomial.PolynomialOverDef,
				polynomial.DerivativeAdd.Read(kRing).At(
					a.TermAs[Fun[Nat, A]]("polynomial_mul(r, r)"), a.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)"))))
		derivative := a.Have(
			"and the product rule differentiates each product",
			"polynomial_derivative(F) = "+
				"polynomial_mul(polynomial_derivative(r), r) + "+
				"polynomial_mul(r, polynomial_derivative(r)) + "+
				"(polynomial_mul(polynomial_derivative(p), q) + polynomial_mul(p, polynomial_derivative(q)))",
			identity.Rw(),
			additive.Rw(),
			By(
				coefficients,
				polynomial.DerivativeMul.Read(kRing).At(r, r),
				polynomial.DerivativeMul.Read(kRing).At(p, q)))
		derivativesOver := a.Have(
			"r′, p′ and q′ are polynomials over k",
			"polynomial_over(k, polynomial_derivative(r)) ∧ "+
				"polynomial_over(k, polynomial_derivative(p)) ∧ "+
				"polynomial_over(k, polynomial_derivative(q))",
			By(
				kSubfield,
				field.SubfieldSubring.Read(L).At(k),
				pOver,
				qOver,
				rOver,
				polynomial.DerivativeOver.Read(ringL)))
		termValues := a.Have(
			"the four products of the derivative are polynomials over k, multiplicative at t",
			"polynomial_over(k, polynomial_mul(polynomial_derivative(r), r)) ∧ "+
				"polynomial_over(k, polynomial_mul(r, polynomial_derivative(r))) ∧ "+
				"polynomial_over(k, polynomial_mul(polynomial_derivative(p), q)) ∧ "+
				"polynomial_over(k, polynomial_mul(p, polynomial_derivative(q))) ∧ "+
				"polynomial_eval(polynomial_mul(polynomial_derivative(r), r), t) = "+
				"«derivativeAt»(r) * polynomial_eval(r, t) ∧ "+
				"polynomial_eval(polynomial_mul(r, polynomial_derivative(r)), t) = "+
				"polynomial_eval(r, t) * «derivativeAt»(r) ∧ "+
				"polynomial_eval(polynomial_mul(polynomial_derivative(p), q), t) = «derivativeAt»(p) * h ∧ "+
				"polynomial_eval(polynomial_mul(p, polynomial_derivative(q)), t) = "+
				"polynomial_eval(p, t) * «derivativeAt»(q)",
			By(
				hValue,
				tInL,
				kSubfield,
				derivativesOver,
				pOver,
				qOver,
				rOver,
				polynomial_evaluation.PolynomialProductData.Read(L).At(
					k, a.TermAs[Fun[Nat, A]]("polynomial_derivative(r)"), r),
				polynomial_evaluation.PolynomialProductData.Read(L).At(
					k, r, a.TermAs[Fun[Nat, A]]("polynomial_derivative(r)")),
				polynomial_evaluation.PolynomialProductData.Read(L).At(
					k, a.TermAs[Fun[Nat, A]]("polynomial_derivative(p)"), q),
				polynomial_evaluation.PolynomialProductData.Read(L).At(
					k, p, a.TermAs[Fun[Nat, A]]("polynomial_derivative(q)"))))
		termsOverL := a.Have(
			"so are those products and their sums over L",
			"polynomial_over(L.carrier, polynomial_mul(polynomial_derivative(r), r)) ∧ "+
				"polynomial_over(L.carrier, polynomial_mul(r, polynomial_derivative(r))) ∧ "+
				"polynomial_over(L.carrier, polynomial_mul(polynomial_derivative(p), q)) ∧ "+
				"polynomial_over(L.carrier, polynomial_mul(p, polynomial_derivative(q))) ∧ "+
				"polynomial_over(L.carrier, "+
				"    polynomial_mul(polynomial_derivative(r), r) + "+
				"    polynomial_mul(r, polynomial_derivative(r))) ∧ "+
				"polynomial_over(L.carrier, "+
				"    polynomial_mul(polynomial_derivative(p), q) + polynomial_mul(p, polynomial_derivative(q)))",
			BySets(
				kInL,
				termValues,
				polynomial.PolynomialOverMono,
				comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ringL))))
		derivativeValue := a.Have(
			"evaluation at t is additive, so F′(t) = r′(t)·r(t) + r(t)·r′(t) + (p′(t)·h + p(t)·q′(t))",
			"«derivativeAt»(F) = "+
				"«derivativeAt»(r) * polynomial_eval(r, t) + "+
				"polynomial_eval(r, t) * «derivativeAt»(r) + "+
				"(«derivativeAt»(p) * h + polynomial_eval(p, t) * «derivativeAt»(q))",
			derivative.Rw(),
			Simp(Fwd(polynomial_evaluation.EvalAdd.Read(ringL)), Fwd(termsOverL)),
			By(termValues))
		derivativesInS := a.Have(
			"r′(t), p′(t) and q′(t) lie in k[t], so in S",
			"«derivativeAt»(r) ∈ S ∧ «derivativeAt»(p) ∈ S ∧ «derivativeAt»(q) ∈ S",
			BySets(
				imageInS,
				derivativesOver,
				values.At(a.TermAs[A]("«derivativeAt»(r)")),
				values.At(a.TermAs[A]("«derivativeAt»(p)")),
				values.At(a.TermAs[A]("«derivativeAt»(q)"))))
		derivativesInL := a.Have(
			"so in L",
			"«derivativeAt»(r) ∈ L.carrier ∧ «derivativeAt»(p) ∈ L.carrier ∧ «derivativeAt»(q) ∈ L.carrier",
			BySets(sInL, derivativesInS))
		combination := a.Have(
			"F′(t) = r′(t)·(w + r(t)) − r′(t)·(w − r(t)) + (p′(t)·h + q′(t)·p(t))",
			"«derivativeAt»(F) = "+
				"«derivativeAt»(r) * (w + polynomial_eval(r, t)) + "+
				"-«derivativeAt»(r) * (w - polynomial_eval(r, t)) + "+
				"(«derivativeAt»(p) * h + «derivativeAt»(q) * polynomial_eval(p, t))",
			derivativeValue.Rw(),
			ByArith(L, derivativesInL, inL))

		// The ideal I spanned by p(t), w − r(t), w + r(t) and h holds 2w and F′(t), so it is S.
		generators := a.TermAs[Set[A]](
			"{polynomial_eval(p, t), w - polynomial_eval(r, t), w + polynomial_eval(r, t), h}")
		spanned := a.TermAs[Set[A]]("«I»")
		spannedIdeal := a.Have(
			"p(t), w − r(t), w + r(t) and h lie in S, so they span an ideal I of S",
			"ring_ideal(restrict_ring(field_ring(L), S), «I»)",
			BySets(inS, conjugatesInS, ring_ideal.SpanIdeal.Read(ringS).AsFact().At(generators)))
		generatorsInSpan := a.Have(
			"I holds the elements that span it",
			"polynomial_eval(p, t) ∈ «I» ∧ "+
				"w - polynomial_eval(r, t) ∈ «I» ∧ "+
				"w + polynomial_eval(r, t) ∈ «I» ∧ "+
				"h ∈ «I»",
			BySets(ring_ideal.SpanContains.At(ringOfS, generators)))
		twiceW := a.Have(
			"(w + r(t)) + (w − r(t)) = 2w",
			"w + polynomial_eval(r, t) + (w - polynomial_eval(r, t)) = w + w",
			ByArith(L, inL))
		twiceInSpan := a.Have(
			"so 2w lies in I",
			"w + w ∈ «I»",
			By(twiceW, spannedIdeal, generatorsInSpan, ring_ideal.IdealAdd.At(ringOfS, spanned, plus, minus)))
		rPrime, pPrime, qPrime :=
			a.TermAs[A]("«derivativeAt»(r)"), a.TermAs[A]("«derivativeAt»(p)"), a.TermAs[A]("«derivativeAt»(q)")
		negRPrime := a.TermAs[A]("-«derivativeAt»(r)")
		plusTerm, minusTerm :=
			a.TermAs[A]("«derivativeAt»(r) * (w + polynomial_eval(r, t))"),
			a.TermAs[A]("-«derivativeAt»(r) * (w - polynomial_eval(r, t))")
		hTerm, pTerm :=
			a.TermAs[A]("«derivativeAt»(p) * h"), a.TermAs[A]("«derivativeAt»(q) * polynomial_eval(p, t)")
		conjugateTerms := a.TermAs[A](
			"«derivativeAt»(r) * (w + polynomial_eval(r, t)) + " +
				"-«derivativeAt»(r) * (w - polynomial_eval(r, t))")
		cofactorTerms := a.TermAs[A]("«derivativeAt»(p) * h + «derivativeAt»(q) * polynomial_eval(p, t)")
		derivativeInSpan := a.Have(
			"F′(t), an S-combination of w ± r(t), h and p(t), lies in I",
			"«derivativeAt»(F) ∈ «I»",
			combination.Rw(),
			By(
				spannedIdeal,
				generatorsInSpan,
				derivativesInS,
				comm_ring.NegIn.Read(ringS).AsFact().At(rPrime),
				ring_ideal.IdealMul.At(ringOfS, spanned, rPrime, plus),
				ring_ideal.IdealMul.At(ringOfS, spanned, negRPrime, minus),
				ring_ideal.IdealMul.At(ringOfS, spanned, pPrime, h),
				ring_ideal.IdealMul.At(ringOfS, spanned, qPrime, P),
				ring_ideal.IdealAdd.At(ringOfS, spanned, plusTerm, minusTerm),
				ring_ideal.IdealAdd.At(ringOfS, spanned, hTerm, pTerm),
				ring_ideal.IdealAdd.At(ringOfS, spanned, conjugateTerms, cofactorTerms)))
		pairInSpan := a.Have(
			"2w and F′(t) lie in I",
			"{w + w, «derivativeAt»(F)} ⊆ «I»",
			BySets(twiceInSpan, derivativeInSpan))
		wholeInSpan := a.Have(
			"so I holds S, the ideal they span",
			"S ⊆ «I»",
			By(
				jacobian,
				spannedIdeal,
				pairInSpan,
				ring_ideal.SpanLeast.At(ringOfS, a.TermAs[Set[A]]("{w + w, «derivativeAt»(F)}"), spanned)))
		spansS := a.Have(
			"an ideal of S holding S, I is S",
			"«I» = S",
			BySets(wholeInSpan, spannedIdeal, ring_ideal.IdealSubset.At(ringOfS, spanned)))

		// The relation (w − r(t))·(w + r(t)) = p(t)·h at the nonzero p(t) makes m invertible.
		pValueNonzero := a.Have(
			"p(t) is not zero, t being transcendental and p not zero",
			"polynomial_eval(p, t) ≠ L.zero",
			By(
				pNonzero,
				transcendental,
				pOver,
				algebraic_element.AlgebraicOverDef.At(a.TermAs[FieldOps[A]]("L"), k, t)))
		relationAtPoint := a.Have(
			"w² − r(t)² = h·p(t) factors as (w − r(t))·(w + r(t)) = p(t)·h",
			"(w - polynomial_eval(r, t)) * (w + polynomial_eval(r, t)) = polynomial_eval(p, t) * h",
			ByArith(L, inL, relation))
		a.Show(
			"p(t) is nonzero and the four elements satisfy the relation and span S, so m is invertible",
			By(
				subring,
				inS,
				conjugatesInS,
				pValueNonzero,
				relationAtPoint,
				spansS,
				invertible_fractional_ideal.RelationIdealInvertible.Read(L).At(S, P, minus, plus, h)))
	}),
})}

// QuadraticChartMaximalInvertible — every maximal ideal m of a quadratic
// ring S = k[t] + k[t]·w inside a field is invertible, when t is
// transcendental over k, w² = F(t) for a polynomial F over k, and 2w and
// F′(t) span S. m meets k[t] in p(t)·k[t] for an irreducible p, and the
// classification above p leaves two kinds: m = (p(t), w − r(t)) for a
// square root r of w² modulo p, which the quadratic-fibre lemma inverts,
// or the inert m = p(t)·S, the ideal of the nonzero member p(t) of S,
// which PrincipalIdealInvertible inverts.
var QuadraticChartMaximalInvertible = quadraticChartMaximalInvertibleThm{family.Add(registry.ProofEntry{
	Name: "QuadraticChartMaximalInvertible",
	Key:  "prop_45cfa4a455b14d53",
	Reading: "The Jacobian pair is load-bearing for the first kind: it is what " +
		"inverts (p(t), w − r(t)). The inert p(t)·S is principal and needs only p(t) ≠ " +
		"0, which transcendence of t gives for the nonzero p. Monicity of p is not asked.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S:set(A). ∀t w:A. ∀F:(num → A). ∀m:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"w ∈ L.carrier",
			"polynomial_over(k, F)",
			"w * w = polynomial_eval(F, t)",
			"S = {c + d * w:A | c:A, d:A | c ∈ «polynomials» ∧ d ∈ «polynomials»}",
			"ideal_span(«ringS», {w + w, polynomial_eval(polynomial_derivative(F), t)}) = S",
			"maximal_ideal(«ringS», m)",
			"polynomial_irreducible(restrict_ring(field_ring(L), k), p)",
			"m ∩ «polynomials» = «pIdeal»",
		},
		Conclusion: "invertible_fractional(field_ring(L), S, m)",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
			{Name: "pIdeal", Text: "ideal_span(restrict_ring(field_ring(L), «polynomials»), " +
				"    {polynomial_eval(p, t)})"},
			{Name: "ringS", Text: "restrict_ring(field_ring(L), S)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, S *Expr[Set[A]],
		t, w *Expr[A],
		F *Arrow[Nat, A],
		m *Expr[Set[A]],
		p *Arrow[Nat, A],
		kSubfield, tInL, transcendental, wInL, fOver, wSquare, chart, jacobian, maximal, irreducible, contraction Fact,
	) {
		tm, wm := a.MemberOf[on.L](t, tInL), a.MemberOf[on.L](w, wInL)
		kt := a.Conjuncts(
			GroupPremises(kSubfield, algebraic_element.PolynomialImageRing.Read(L).At(k, tm)),
			"k[t] is a subring of L",
			"holding k",
			"and t",
			"inside k(t)")

		// S = k[t] + k[t]·w is a subring of L holding k[t] and w, as w² = F(t) lies in k[t].
		square := a.Have(
			"w² = F(t) lies in k[t]",
			"w * w ∈ «polynomials»",
			wSquare.Rw(),
			Unfold(algebraic_element.PolynomialImageDef),
			BySets(fOver))
		ringS := a.Have(
			"S is a subring of L holding k[t] and w",
			"subring(field_ring(L), S) ∧ «polynomials» ⊆ S ∧ w ∈ S",
			chart.Rw(),
			By(
				kt[0],
				square,
				fractional_ideal.RingOneAndElement.Read(L).At(a.TermAs[Set[A]]("«polynomials»"), wm)))

		// p is a polynomial over k of positive degree, so not the zero polynomial.
		irreducibility := a.Conjuncts(
			a.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
			"p is a polynomial over k",
			"of positive degree",
			"with no factorization into two of positive degree")
		pOver := irreducibility[0]
		pNonzero := a.Have(
			"p is not the zero polynomial, whose degree is zero",
			"p ≠ vec_zero",
			By(irreducibility[1], polynomial.DegreeVecZero.At(a.TermAs[A]("L.zero")), nat_order.LessThanIrrefl))

		a.Show(
			"above p, m is of the first kind or inert, and either kind is invertible",
			GroupPremises(
				kSubfield,
				square,
				chart,
				maximal,
				irreducible,
				contraction,
				QuadraticMaximalIdealClassification.Read(L).At(k, S, tm, wm, m, p)).SplitDisj(
				LeftHolds(
					"first kind: m = (p(t), w − r(t)) with w² ≡ r(t)² "+
						"modulo p(t), invertible by the quadratic-fibre lemma",
					Given(func(branch *Argument, firstKind Fact) {
						r, root := branch.UnpackAs[Fun[Nat, A]](firstKind, "r")
						rFacts := branch.Conjuncts(
							root,
							"r is a polynomial over k",
							"of degree below that of p",
							"with w² ≡ r(t)² modulo p(t)",
							"m = (p(t), w − r(t))")
						branch.Show(
							"(p(t), w − r(t)) is invertible, 2w and F′(t) spanning S",
							rFacts[3].Rw(),
							By(
								kSubfield,
								transcendental,
								ringS,
								fOver,
								wSquare,
								jacobian,
								pOver,
								pNonzero,
								rFacts[0],
								rFacts[2],
								QuadraticFibreIdealInvertible.Read(L).At(k, S, tm, w, F, p, r)))
					})),
				RightHolds(
					"inert: m = p(t)·S, and p(t) is a nonzero member of S",
					Given(func(branch *Argument, inert Fact) {
						principal := branch.Conjuncts(
							inert,
							"m = (p(t))",
							"w² is no square modulo p(t)")[0]
						value := branch.TermAs[A]("polynomial_eval(p, t)")
						valueIn := branch.Have(
							"p(t) lies in k[t], so in S",
							"polynomial_eval(p, t) ∈ S",
							BySets(ringS, pOver, algebraic_element.PolynomialImageDef))
						valueNonzero := branch.Have(
							"p(t) is not zero: p is not, and t is transcendental over k",
							"polynomial_eval(p, t) ≠ L.zero",
							By(transcendental, pOver, pNonzero, algebraic_element.AlgebraicOverDef))
						branch.Show(
							"a nonzero principal ideal is invertible",
							principal.Rw(),
							By(ringS, valueIn, valueNonzero, PrincipalIdealInvertible.Read(L).At(S, value)))
					}))))
	}),
})}

// WeierstrassCubicPolynomial — the Weierstrass cubic as a polynomial over
// k: C = X³ + aX + b has its coefficients in k, takes the value y² at x,
// and its derivative takes the value 3x² + a there. Coefficient by
// coefficient, C′(n) = (n + 1)·C(n + 1) is 3 at n = 2, a at n = 0 and
// zero elsewhere, so C′ = 3X² + a.
var WeierstrassCubicPolynomial = weierstrassCubicPolynomialThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassCubicPolynomial",
	Key:  "prop_36ec4d1bf9371a56",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{"weierstrass(L, k, x, y, a, b)"},
		Conclusion: "polynomial_over(k, «cubic») ∧ " +
			"y * y = polynomial_eval(«cubic», x) ∧ " +
			"polynomial_eval(polynomial_derivative(«cubic»), x) = " +
			"monoid_pow(L.add, L.zero, L.one, 3) * (x * x) + a",
		Abbrev: Abbrev{
			{Name: "cubic", Text: "basis_vector(3) + a • basis_vector(1) + b • basis_vector(0)"},
		},
	}, func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
		kSubfield, aInK, bInK :=
			elliptic_curve.WeierstrassSubfield.Read(datum),
			elliptic_curve.WeierstrassCoefficientA.Read(datum),
			elliptic_curve.WeierstrassCoefficientB.Read(datum)
		xInL, yInL :=
			elliptic_curve.WeierstrassXInField.Read(datum).AsFact(),
			elliptic_curve.WeierstrassYInField.Read(datum).AsFact()
		ring := field.RingOn.Read(L)
		fieldK := arg.Have(
			"k is a field in its own right",
			"field_on(restrict_field(L, k))",
			By(kSubfield, field.SubfieldFieldOn.Read(L).At(k)))
		ringK := field.RingOn.Read(fieldK)
		cubicOver := arg.Have(
			"C is a polynomial over k, a and b lying in k",
			"polynomial_over(k, «cubic»)",
			BySets(
				aInK,
				bInK,
				polynomial.BasisVectorOver.Read(ringK),
				module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ringK)),
				comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ringK))))
		coefficients := arg.Have(
			"x, y, a, b and 3 lie in L",
			"x ∈ L.carrier ∧ "+
				"y ∈ L.carrier ∧ "+
				"a ∈ L.carrier ∧ "+
				"b ∈ L.carrier ∧ "+
				"monoid_pow(L.add, L.zero, L.one, 3) ∈ L.carrier",
			BySets(
				xInL,
				yInL,
				kSubfield,
				field.SubfieldSubset,
				aInK,
				bInK,
				comm_ring.OneIn.Read(ring),
				comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))))
		termsOverL := arg.Have(
			"the terms of C and of 3X² + a are polynomials over L",
			"polynomial_over(L.carrier, basis_vector(3)) ∧ "+
				"polynomial_over(L.carrier, basis_vector(2)) ∧ "+
				"polynomial_over(L.carrier, basis_vector(1)) ∧ "+
				"polynomial_over(L.carrier, basis_vector(0)) ∧ "+
				"polynomial_over(L.carrier, a • basis_vector(1)) ∧ "+
				"polynomial_over(L.carrier, b • basis_vector(0)) ∧ "+
				"polynomial_over(L.carrier, a • basis_vector(0)) ∧ "+
				"polynomial_over(L.carrier, monoid_pow(L.add, L.zero, L.one, 3) • basis_vector(2)) ∧ "+
				"polynomial_over(L.carrier, basis_vector(3) + a • basis_vector(1))",
			BySets(
				coefficients,
				polynomial.BasisVectorOver.Read(ring),
				module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
				comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ring))))
		value := arg.Have(
			"C takes the value x³ + ax + b = y² at x",
			"y * y = polynomial_eval(«cubic», x)",
			Simp(
				Fwd(polynomial_evaluation.EvalAdd.Read(ring)),
				Fwd(polynomial_evaluation.EvalScalar.Read(ring)),
				Fwd(polynomial_evaluation.EvalBasisVector.Read(ring)),
				Fwd(termsOverL)),
			ByArith(L, elliptic_curve.WeierstrassEquation.Read(datum), coefficients))
		derivative := arg.Have(
			"C′ = 3X² + a, coefficient by coefficient",
			"polynomial_derivative(«cubic») = "+
				"monoid_pow(L.add, L.zero, L.one, 3) • basis_vector(2) + a • basis_vector(0)",
			Funext(),
			Derive(func(c *Argument) {
				c.FixAs[Nat]("n")
				c.Do(Simp(
					Fwd(polynomial.PolynomialDerivativeDef),
					Fwd(vec_space.VecAddDef),
					Fwd(vec_space.VecScalarMulDef),
					Fwd(vec_space.BasisVectorDef)))
				c.Cases(c.TermAs[Bool]("n = 2"))
				c.When(
					"at n = 2 only X³ contributes, with the factor 2 + 1 = 3",
					func(d *Argument, two Fact) {
						successor := d.Have(
							"the factor is 3",
							"suc(2) = 3",
							ByArith())
						d.Show(
							"(2 + 1)·1 = 3",
							ByArith(Normalized, L, two, successor, coefficients))
					})
				c.Otherwise(
					"for n ≠ 2 the X³ term is gone, and n = 0 decides the aX term",
					func(d *Argument, notTwo Fact) {
						d.Cases(d.TermAs[Bool]("n = 0"))
						d.When(
							"at n = 0 only aX contributes, with the factor 0 + 1 = 1",
							func(e *Argument, zero Fact) {
								successor := e.Have(
									"the factor is 1",
									"suc(0) = 1",
									ByArith())
								e.Show(
									"1·a = a",
									ByArith(Normalized, L, zero, successor, coefficients))
							})
						d.Otherwise(
							"elsewhere no term of C contributes",
							func(e *Argument, notZero Fact) {
								off := e.Have(
									"n + 1 is neither 3 nor 1",
									"suc(n) ≠ 3 ∧ suc(n) ≠ 1",
									ByArith(notZero, notTwo))
								e.Show(
									"both sides are zero",
									ByArith(Normalized, L, notZero, notTwo, off, coefficients))
							})
					})
			}))
		slope := arg.Have(
			"so C′ takes the value 3x² + a at x",
			"polynomial_eval(polynomial_derivative(«cubic»), x) = "+
				"monoid_pow(L.add, L.zero, L.one, 3) * (x * x) + a",
			derivative.Rw(),
			Simp(
				Fwd(polynomial_evaluation.EvalAdd.Read(ring)),
				Fwd(polynomial_evaluation.EvalScalar.Read(ring)),
				Fwd(polynomial_evaluation.EvalBasisVector.Read(ring)),
				Fwd(termsOverL)),
			ByArith(L, coefficients))
		arg.Show(
			"C is a polynomial over k with C(x) = y² and C′(x) = 3x² + a",
			By(cubicOver, value, slope))
	}),
})}
