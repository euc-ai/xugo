// factor_coefficients.go — the coefficients of a monic factor read from its
// roots: over a closed field a monic polynomial lies over every subring that
// holds its roots, and a monic factor of a nonzero polynomial over a subfield
// k has its coefficients algebraic over k.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// MonicCoefficientsFromRoots — over an algebraically closed field, a monic
// polynomial whose roots lie in a subring Ω has its coefficients in Ω. By
// induction on the degree: a monic polynomial of positive degree has a root
// r, in Ω; its linear factor there splits off, leaving a monic factor of
// lower degree whose roots are among those of the polynomial, and the product
// of two polynomials over the ring Ω is over Ω.
var MonicCoefficientsFromRoots = monicCoefficientsFromRootsThm{family.Add(registry.ProofEntry{
	Name: "MonicCoefficientsFromRoots",
	Key:  "prop_7fa150e4ae7425ac",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀Ω:set(A). ∀h:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subring(field_ring(M), Ω)",
			"polynomial_over(M.carrier, h)",
			"polynomial_monic(h)",
			"polynomial_roots(M.carrier, h) ⊆ Ω",
		},
		Conclusion: "polynomial_over(Ω, h)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		Ω *Expr[Set[A]],
		h *Arrow[Nat, A],
		closed, ΩSubring, hOver, hMonic, hRoots Fact,
	) {
		fieldValue := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		one := a.TermAs[A]("M.one")
		carrier := a.TermAs[Set[A]]("M.carrier")
		ring := field.RingOn.Read(M)
		domain := integral_domain.FieldIntegralDomain.Read(M)
		ΩRing := a.Have(
			"Ω is a ring under M's operations",
			"comm_ring_on(restrict_ring(field_ring(M), Ω))",
			By(ΩSubring, comm_ring.SubringRingOn.Read(ring)))

		factors := a.Have(
			"every monic polynomial over M with its roots in Ω is over Ω, by induction on its degree",
			Statement{
				Binders: "∀n:num. ∀p:(num → A).",
				Hypotheses: []string{
					"polynomial_over(M.carrier, p)",
					"polynomial_monic(p)",
					"polynomial_roots(M.carrier, p) ⊆ Ω",
					"polynomial_degree(p) = n",
				},
				Conclusion: "polynomial_over(Ω, p)",
			},
			Derive(func(b *Argument) {
				b.Induct("n")
				b.Base(
					"a monic polynomial of degree zero is the one polynomial, over every ring",
					func(c *Argument) {
						p := c.FixAs[Fun[Nat, A]]("p")
						c.Show(
							"it is over the ring Ω",
							By(
								Normalized,
								c.Assume(),
								polynomial.MonicDegreeZero.Read(ring).At(p),
								polynomial.BasisVectorOver.Read(ΩRing).At(c.TermAs[Nat]("0"))))
					})
				b.Step(
					"a root of p in the closed field splits off a linear factor over Ω",
					func(c *Argument, smaller Fact) {
						p := c.FixAs[Fun[Nat, A]]("p")
						data := c.Conjuncts(
							c.Assume(),
							"p is a polynomial over M",
							"p is monic",
							"the roots of p lie in Ω",
							"p has degree n + 1")
						pOver, pMonic, pRoots, pDegree := data[0], data[1], data[2], data[3]
						r, root := c.ObtainAs[A](
							"p has positive degree, so a root in the closed field",
							"∃r:A. r ∈ M.carrier ∧ polynomial_eval(p, r) = M.zero",
							ByArith(closed, pOver, pDegree, AlgebraicallyClosedDef.At(fieldValue)))
						rootParts := c.Conjuncts(
							root,
							"r lies in M",
							"p vanishes at r")
						pVanishes := rootParts[1]
						rMember := c.MemberOf[on.M](r, rootParts[0])

						l, linearDef := c.LetAs[Fun[Nat, A]]("l", "«linear»(r)")
						linear := c.Conjuncts(
							c.Simplified(polynomial_roots.LinearFactor.Read(ring).At(rMember), Rev(linearDef)),
							"the linear factor at r is a polynomial over M",
							"the linear factor is monic",
							"the linear factor has degree at most one",
							"the linear factor takes the value y - r at each point y of M",
							"the linear factor vanishes at r",
							"the linear factor has degree one when one is not zero")
						lOver, lMonic, lNontrivial := linear[0], linear[1], linear[5]

						q, quotient := c.ObtainAs[Fun[Nat, A]](
							"p, monic and so nonzero, is the linear factor at its root "+
								"times a nonzero q one degree lower, with the roots of q",
							"∃q:(num → A). "+
								"    polynomial_over(M.carrier, q) ∧ "+
								"    q ≠ vec_zero ∧ "+
								"    p = polynomial_mul(l, q) ∧ "+
								"    polynomial_degree(p) = suc(polynomial_degree(q)) ∧ "+
								"    polynomial_roots(M.carrier, p) = insert(r, polynomial_roots(M.carrier, q))",
							By(
								linearDef,
								pOver,
								pMonic,
								pVanishes,
								polynomial.MonicNonzero.Read(domain).At(p),
								polynomial_roots.RootFactorization.Read(domain).At(p, rMember)))
						quotientParts := c.Conjuncts(
							quotient,
							"q is a polynomial over M",
							"q is not zero",
							"p is the linear factor times q",
							"p is one degree above q",
							"the roots of p are r and the roots of q")
						qOver, product, degreeStep, roots :=
							quotientParts[0], quotientParts[2], quotientParts[3], quotientParts[4]
						rootsIn := c.Have(
							"so r and the roots of q lie in Ω",
							"r ∈ Ω ∧ polynomial_roots(M.carrier, q) ⊆ Ω",
							BySets(roots, pRoots))

						degrees := c.Have(
							"one is not zero in a field, so the linear factor has degree one and the degrees add to that of p",
							"polynomial_degree(l) + polynomial_degree(q) = polynomial_degree(p)",
							ByArith(field.OneNotZeroOn.Read(M), lNontrivial, degreeStep))
						leading := c.Have(
							"the leading coefficients of the two factors multiply at that degree",
							"polynomial_mul(l, q, polynomial_degree(p)) = l(polynomial_degree(l)) * q(polynomial_degree(q))",
							By(degrees, lOver, qOver, polynomial.LeadingCoefficientMul.Read(ring).At(l, q)))
						unit := c.Have(
							"p and the linear factor being monic, one times the leading coefficient of q is one",
							"M.one * q(polynomial_degree(q)) = M.one",
							By(
								Normalized,
								leading,
								product,
								lMonic,
								pMonic,
								polynomial.PolynomialMonicDef.At(zero, one, p),
								polynomial.PolynomialMonicDef.At(zero, one, l)))
						qMonic := c.Have(
							"so q is monic",
							"polynomial_monic(q)",
							ByArith(
								M,
								unit,
								qOver,
								polynomial.PolynomialMonicDef.At(zero, one, q),
								polynomial.PolynomialOverDef.At(zero, carrier, q)))
						qInΩ := c.Have(
							"q, monic of degree n with its roots in Ω, is over Ω",
							"polynomial_over(Ω, q)",
							ByArith(qOver, qMonic, rootsIn, pDegree, degreeStep, smaller.At(q)))
						lInΩ := c.Have(
							"r lies in Ω, so the linear factor is over Ω",
							"polynomial_over(Ω, l)",
							By(Normalized, linearDef, rootsIn, polynomial_roots.LinearFactor.Read(ΩRing).AsFact().At(r)))
						c.Show(
							"the product of two polynomials over the ring Ω is over Ω",
							By(Normalized, product, lInΩ, qInΩ, polynomial.PolynomialMulOver.Read(ΩRing).AsFact().At(l, q)))
					})
			}))
		a.Show(
			"h is such a polynomial, of its own degree",
			By(factors.At(a.TermAs[Nat]("polynomial_degree(h)"), h), hOver, hMonic, hRoots))
	}),
})}

// MonicFactorCoefficientsInClosed — over an algebraically closed field, a
// monic factor of a nonzero polynomial over a subfield has its coefficients
// algebraic over the subfield. A root of the factor is a root of the
// polynomial, and so algebraic over k; the elements algebraic over k are a
// subfield, which then holds the coefficients (MonicCoefficientsFromRoots).
var MonicFactorCoefficientsInClosed = monicFactorCoefficientsInClosedThm{family.Add(registry.ProofEntry{
	Name: "MonicFactorCoefficientsInClosed",
	Key:  "prop_5bac6b1775c14770",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀g h:(num → A). ∀i:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"polynomial_over(k, g)",
			"g ≠ vec_zero",
			"polynomial_over(M.carrier, h)",
			"polynomial_monic(h)",
			"polynomial_divides(field_ring(M), h, g)",
		},
		Conclusion: "algebraic_over(M, k, h(i))",
	}, func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], g, h *Arrow[Nat, A], i *Expr[Nat],
		closed, kSubfield, gOver, gNonzero, hOver, hMonic, hDivides Fact) {
		fieldValue := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		ring := field.RingOn.Read(M)
		Ω, ΩDef := a.LetAs[Set[A]]("Ω", "algebraic_elements(M, k)")
		elements := algebraic_element.AlgebraicElementsDef.At(fieldValue, k)
		ΩSubring := a.Have(
			"the elements of M algebraic over k are a subfield, so a subring",
			"subring(field_ring(M), Ω)",
			By(
				Normalized,
				ΩDef,
				kSubfield,
				algebraic_element.AlgebraicElementsSubfield.Read(M).At(k),
				field.SubfieldSubring.Read(M)))

		w, cofactor := a.UnpackAs[Fun[Nat, A]](
			a.Unfolded(hDivides, polynomial_division.PolynomialDividesDef), "w")
		rootsAlgebraic := a.Have(
			"a root of h is a root of g, nonzero over k, and so algebraic over k",
			"∀r:A. r ∈ M.carrier ∧ polynomial_eval(h, r) = M.zero ⇒ r ∈ Ω",
			Derive(func(b *Argument) {
				r := b.FixAs[A]("r")
				root := b.Conjuncts(
					b.Assume(),
					"r lies in M",
					"h vanishes at r")
				rIn, hVanishes := root[0], root[1]
				gVanishes := b.Have(
					"a root of the factor h is a root of g",
					"polynomial_eval(g, r) = M.zero",
					By(
						Normalized,
						cofactor,
						hOver,
						hVanishes,
						polynomial_evaluation.EvalMulRoot.Read(ring).At(h, w, b.MemberOf[on.M](r, rIn))))
				rAlgebraic := b.Have(
					"g, nonzero over k, makes r algebraic over k",
					"algebraic_over(M, k, r)",
					By(gVanishes, gOver, gNonzero, algebraic_element.AlgebraicOverDef.At(fieldValue, k, r)))
				b.Show(
					"so r lies in Ω",
					ΩDef.Rw(),
					BySets(elements, rIn, rAlgebraic))
			}))
		roots := a.Have(
			"so the roots of h lie in Ω",
			"polynomial_roots(M.carrier, h) ⊆ Ω",
			Simp(Fwd(polynomial_roots.PolynomialRootsDef)),
			BySets(rootsAlgebraic))
		hCoefficient := a.Have(
			"h, monic over the closed field M with its roots in the subring Ω, has the coefficient h(i) in Ω",
			"h(i) ∈ Ω",
			By(
				M,
				closed,
				ΩSubring,
				hOver,
				hMonic,
				roots,
				MonicCoefficientsFromRoots.At(fieldValue, Ω, h),
				polynomial.PolynomialOverDef.At(zero, Ω, h)))
		a.Show(
			"and the elements of Ω are algebraic over k",
			ΩDef.Rw(),
			BySets(elements, hCoefficient))
	}),
})}

// MonicFactorCoefficientsAlgebraic — a monic factor over a field of a
// nonzero polynomial over a subfield k has its coefficients algebraic over
// k. The field embeds in an algebraically closed field G extending its
// transported copy, a ring homomorphism keeping the polynomials, the leading
// coefficient and the factorization, so the images of the coefficients are
// algebraic over the image of k (MonicFactorCoefficientsInClosed). Algebraicity
// passes from G to the transported copy (FieldExtendsEval) and from the copy
// to the field (AlgebraicOverTransport). The embedding step is a lemma of its
// own because it ranges over a second type B, the closure's host.
var MonicFactorCoefficientsAlgebraic = monicFactorCoefficientsAlgebraicThm{family.Add(registry.ProofEntry{
	Name: "MonicFactorCoefficientsAlgebraic",
	Key:  "prop_812b0de041bd4a40",
	Reading: "g ≠ vec_zero is load-bearing: every polynomial over M divides the zero polynomial, so " +
		"a factor of it says nothing. So is monic: a factor scaled by a point of M transcendental over " +
		"k is still a factor, its coefficients scaled with it. M need not be algebraic over k or closed.",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀g h:(num → A). ∀i:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"polynomial_over(k, g)",
			"g ≠ vec_zero",
			"polynomial_over(M.carrier, h)",
			"polynomial_monic(h)",
			"polynomial_divides(field_ring(M), h, g)",
		},
		Conclusion: "algebraic_over(M, k, h(i))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		intoClosed := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀g h:(num → A). ∀i:num.",
			Hypotheses: []string{
				"injective_on(F.carrier, ι)",
				"algebraically_closed_field(G)",
				"field_extends(transport_field(ι, F), G)",
				"subfield(F, k)",
				"polynomial_over(F.zero, k, g)",
				"g ≠ vec_zero(F.zero)",
				"polynomial_over(F.zero, F.carrier, h)",
				"polynomial_monic(F.zero, F.one, h)",
				"polynomial_divides(field_ring(F), h, g)",
			},
			Conclusion: "algebraic_over(F, k, h(i))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k *Expr[Set[A]],
			g, h *Arrow[Nat, A],
			i *Expr[Nat],
			injective, closed, extension, kSubfield, gOver, gNonzero, hOver, hMonic, hDivides Fact,
		) {
			source := a.TermAs[FieldOps[A]]("F")
			target := a.TermAs[FieldOps[B]]("G")
			carrier := a.TermAs[Set[A]]("F.carrier")
			sourceZero := a.TermAs[A]("F.zero")
			coefficient := a.TermAs[A]("h(i)")
			targetZero := a.TermAs[B]("G.zero")
			targetCarrier := a.TermAs[Set[B]]("G.carrier")
			carrierImage := a.TermAs[Set[B]]("image(ι, F.carrier)")
			kImage := a.TermAs[Set[B]]("image(ι, k)")
			gMapped := a.TermAs[Fun[Nat, B]]("λj:num. ι(g(j))")
			hMapped := a.TermAs[Fun[Nat, B]]("λj:num. ι(h(j))")
			T, copyDef := a.LetAs[FieldOps[B]]("T", "transport_field(ι, F)")

			copyField := a.Have(
				"the transported copy of F is a field",
				"field_on(T)",
				copyDef.Rw(),
				By(F, injective, ring_transport.TransportFieldOn.At(ι, source)))
			copyHom := a.Have(
				"ι is a ring homomorphism onto the copy",
				"ring_homomorphism(field_ring(F), field_ring(T), ι)",
				copyDef.Rw(),
				By(F, injective, ring_transport.TransportFieldHomomorphism.At(ι, source)))
			inclusion := a.TermAs[Fun[B, B]]("λy:B. y")
			inclusionHom := a.Have(
				"G includes the copy as a ring homomorphism",
				"ring_homomorphism(field_ring(T), field_ring(G), λy:B. y)",
				By(G, copyField, extension, FieldExtendsHomomorphism.At(T, target)))
			hom := a.Have(
				"so ι is a ring homomorphism into G",
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				By(
					copyHom,
					inclusionHom,
					ring_homomorphism.RingHomCompose.At(
						a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
						a.TermAs[module_record.RingOps[B]]("field_ring(T)"),
						a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
						ι,
						inclusion)))
			copyCarrier := a.Have(
				"the copy's carrier is the image of F's",
				"T.carrier = image(ι, F.carrier)",
				Simp(Fwd(copyDef), Fwd(ring_transport.TransportFieldDef)),
				Basic())
			imageInG := a.Have(
				"the image of F lies in G",
				"image(ι, F.carrier) ⊆ G.carrier",
				Simp(Rev(copyCarrier)),
				By(extension, fieldExtendsDef.At(T, target)))

			gLaws := algebraic_element.FieldEmbeddingPolynomials.At(source, target, ι, k, g)
			gImage := a.Have(
				"g maps to a polynomial over the image of k",
				"polynomial_over(G.zero, image(ι, k), λj:num. ι(g(j)))",
				By(F, G, hom, kSubfield, gOver, gLaws))
			gImageNonzero := a.Have(
				"and its image is not zero",
				"(λj:num. ι(g(j))) ≠ vec_zero(G.zero)",
				By(F, G, hom, kSubfield, gOver, gNonzero, gLaws))
			hImage := a.Have(
				"h maps to a monic polynomial over G",
				"polynomial_over(G.zero, G.carrier, λj:num. ι(h(j))) ∧ "+
					"polynomial_monic(G.zero, G.one, λj:num. ι(h(j)))",
				By(
					F,
					G,
					hom,
					hOver,
					hMonic,
					imageInG,
					set_order.SubsetRefl.At(carrier),
					algebraic_element.FieldEmbeddingMonic.At(source, target, ι, carrier, h),
					polynomial.PolynomialOverMono.At(targetZero, carrierImage, targetCarrier, hMapped)))
			imageDivides := a.Have(
				"the image of h divides the image of g",
				"polynomial_divides(field_ring(G), λj:num. ι(h(j)), λj:num. ι(g(j)))",
				By(F, G, hom, hOver, hDivides, algebraic_element.FieldEmbeddingDivides.At(source, target, ι, g, h)))
			kImageSubfield := a.Have(
				"ι carries the subfield k to a subfield of G",
				"subfield(G, image(ι, k))",
				By(F, G, hom, kSubfield, algebraic_element.FieldEmbeddingSubfieldsAdjoin.At(source, target, ι)))

			algebraicInG := a.Have(
				"in the closed field G the image of each coefficient is algebraic over the image of k",
				"algebraic_over(G, image(ι, k), ι(h(i)))",
				By(
					G,
					closed,
					kImageSubfield,
					gImage,
					gImageNonzero,
					hImage,
					imageDivides,
					MonicFactorCoefficientsInClosed.At(target, kImage, gMapped, hMapped, i)))

			kInCarrier := a.Have(
				"k lies in F",
				"k ⊆ F.carrier",
				By(kSubfield, field.SubfieldSubset.At(source, k)))
			coefficientIn := a.Have(
				"h(i) lies in F",
				"h(i) ∈ F.carrier",
				By(hOver, polynomial.PolynomialOverDef.At(sourceZero, carrier, h)))
			kImageInCopy := a.Have(
				"the image of k lies in the copy",
				"image(ι, k) ⊆ T.carrier",
				Simp(Fwd(copyCarrier)),
				By(kInCarrier, set_image.ImageSubset.At(ι, k, carrier)))
			coefficientInCopy := a.Have(
				"the image of h(i) lies in the copy",
				"ι(h(i)) ∈ T.carrier",
				Simp(Fwd(copyCarrier)),
				By(coefficientIn, set_image.FunInImage.At(ι, carrier, coefficient)))
			algebraicInCopy := a.Have(
				"the extension G evaluates the polynomials over the copy as the copy does",
				"algebraic_over(T, image(ι, k), ι(h(i)))",
				By(
					extension,
					kImageInCopy,
					coefficientInCopy,
					algebraicInG,
					FieldExtendsEval.Read(copyField).AsFact().At(target, kImage, a.TermAs[B]("ι(h(i))"))))
			a.Show(
				"transport along ι brings algebraicity back to F",
				By(
					Normalized,
					copyDef,
					algebraicInCopy,
					injective,
					kInCarrier,
					coefficientIn,
					F,
					AlgebraicOverTransport.At(ι, source, k, coefficient)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			g, h *Arrow[Nat, A],
			i *Expr[Nat],
			given Fact,
		) {
			C, closure := a.UnpackAs[FieldOps[_ClosureHost]](AlgebraicClosureInHost.Read(M), "C")
			a.Show(
				"M embeds in its algebraic closure, a closed field extending its transported copy",
				By(
					M,
					closure,
					given,
					At(
						intoClosed,
						a.TermAs[FieldOps[A]]("M"),
						C,
						a.TermAs[Fun[A, _ClosureHost]]("«closureEmbedding»"),
						k,
						g,
						h,
						i),
					ClosureEmbeddingInjective.At(a.TermAs[Set[A]]("M.carrier"))))
		})
	}),
})}
