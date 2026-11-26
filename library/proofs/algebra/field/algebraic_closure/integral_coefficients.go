// integral_coefficients.go — the coefficients of a monic factor read over a
// subring: a field embedding carries integrality to its image and reflects
// it, a monic factor of a monic polynomial over a subring S has its
// coefficients integral over S (Kronecker), and the minimal polynomial of an
// element integral over a ring has its coefficients in the ring when the ring
// is integrally closed in the field of the coefficients.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldEmbeddingIntegral — a field embedding carries integrality over a set
// to integrality over its image: a monic equation p of x over S maps,
// coefficient by coefficient, to a monic polynomial over image(ι, S)
// (algebraic_element.FieldEmbeddingMonic) of the same degree, vanishing at
// ι(x) since ι sends zero to zero.
var FieldEmbeddingIntegral = fieldEmbeddingIntegralThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingIntegral",
	Key:  "prop_1fe1988fbb7ee05f",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀S:set(A). ∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"S ⊆ F.carrier",
			"x ∈ F.carrier",
			"integral_over(restrict_ring(field_ring(F), S), x)",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(G), image(ι, S)), ι(x))",
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G field.FieldFact[on.G],
		ι *Arrow[A, B],
		S *Expr[Set[A]],
		x *Member[A, on.F],
		hom, sInCarrier, integral Fact,
	) {
		sourceRecord := a.TermAs[FieldOps[A]]("F")
		targetRecord := a.TermAs[FieldOps[B]]("G")
		carrier := a.TermAs[Set[A]]("F.carrier")
		sourceZero := a.TermAs[A]("F.zero")
		p, equation := a.UnpackAs[Fun[Nat, A]](a.Unfolded(integral, integral_element.IntegralOverDef), "p")
		parts := a.Conjuncts(
			equation,
			"p is a polynomial over S",
			"p is monic",
			"p has positive degree",
			"p vanishes at x")
		pOver, pMonic, pPositive, pVanishes := parts[0], parts[1], parts[2], parts[3]

		imageMonic := a.Have(
			"ι carries p to a monic polynomial over the image of S",
			"polynomial_over(image(ι, S), λi:num. ι(p(i))) ∧ polynomial_monic(λi:num. ι(p(i)))",
			By(
				F,
				G,
				hom,
				sInCarrier,
				pOver,
				pMonic,
				algebraic_element.FieldEmbeddingMonic.At(sourceRecord, targetRecord, ι, S, p)))
		laws := a.Have(
			"ι keeps the degree of p and carries its value at x to the value of the image at ι(x)",
			"polynomial_degree(λi:num. ι(p(i))) = polynomial_degree(p) ∧ "+
				"polynomial_eval(λi:num. ι(p(i)), ι(x)) = ι(polynomial_eval(p, x))",
			By(
				F,
				G,
				x,
				hom,
				sInCarrier,
				pOver,
				polynomial.PolynomialOverMono.At(sourceZero, S, carrier, p),
				field.CarrierSubfield.Read(F),
				algebraic_element.FieldEmbeddingPolynomials.At(sourceRecord, targetRecord, ι, carrier, p)))
		a.Show(
			"ι sends the value zero to zero, so the image is a monic equation of ι(x) over image(ι, S)",
			By(
				imageMonic,
				pPositive,
				pVanishes,
				laws,
				ring_homomorphism.MapZero.Read(hom),
				integral_element.IntegralOverDef.At(
					a.TermAs[module_record.RingOps[B]]("restrict_ring(field_ring(G), image(ι, S))"),
					a.TermAs[B]("ι(x)"))))
	}),
})}

// FieldEmbeddingReflectsIntegral — a field embedding reflects integrality.
// On its image an embedding ι is an isomorphism, so its inverse is an
// embedding of the image field into F. Integrality of ι(x) over image(ι, S)
// holds in the image field, whose operations are G's, and the inverse
// carries it back to x over S (FieldEmbeddingIntegral).
var FieldEmbeddingReflectsIntegral = fieldEmbeddingReflectsIntegralThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingReflectsIntegral",
	Key:  "prop_241d2fc82a7c7e9",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀S:set(A). ∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"S ⊆ F.carrier",
			"x ∈ F.carrier",
			"integral_over(restrict_ring(field_ring(G), image(ι, S)), ι(x))",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(F), S), x)",
		Abbrev: Abbrev{
			{Name: "imageField", Text: "restrict_field(G, image(ι, F.carrier))"},
		},
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G field.FieldFact[on.G],
		ι *Arrow[A, B],
		S *Expr[Set[A]],
		x *Member[A, on.F],
		hom, sInCarrier, integral Fact,
	) {
		sourceRecord := a.TermAs[FieldOps[A]]("F")
		targetRecord := a.TermAs[FieldOps[B]]("G")
		imageRecord := a.TermAs[FieldOps[B]]("«imageField»")
		sourceRing := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		targetRing := a.TermAs[module_record.RingOps[B]]("field_ring(G)")
		imageRing := a.TermAs[module_record.RingOps[B]]("field_ring(«imageField»)")
		sourceCarrier := a.TermAs[Set[A]]("F.carrier")
		imageCarrier := a.TermAs[Set[B]]("image(ι, F.carrier)")
		imageS := a.TermAs[Set[B]]("image(ι, S)")
		imageX := a.TermAs[B]("ι(x)")
		back := a.TermAs[Fun[B, A]]("inverse_on(F.carrier, ι)")

		injective := a.Have(
			"a homomorphism of fields is one-to-one",
			"injective_on(F.carrier, ι)",
			By(G, hom, ring_homomorphism.FieldHomomorphismInjective.Read(F).At(targetRecord, ι)))
		imageSubfield := a.Have(
			"the image of F is a subfield of G",
			"subfield(G, image(ι, F.carrier))",
			By(G, hom, ring_homomorphism.ImageSubfield.Read(F).At(targetRecord, ι)))
		imageFieldOn := a.Have(
			"so it is a field under the operations of G",
			"field_on(«imageField»)",
			By(imageSubfield, field.SubfieldFieldOn.Read(G).At(imageCarrier)))
		toImage := a.Have(
			"ι is a homomorphism of F into the image field",
			"ring_homomorphism(field_ring(F), field_ring(«imageField»), ι)",
			By(
				hom,
				imageSubfield,
				field.SubfieldSubring.Read(G).At(imageCarrier),
				set_image.FunInImage,
				ring_homomorphism.RingHomCorestrict.At(sourceRing, targetRing, ι, imageCarrier),
				field.RestrictFieldRing.At(targetRecord, imageCarrier)))
		isomorphism := a.Have(
			"one-to-one and onto, it is an isomorphism",
			"ring_isomorphism(field_ring(F), field_ring(«imageField»), ι)",
			By(toImage, injective, ring_homomorphism.RingIsomorphismDef.At(sourceRing, imageRing, ι)))
		backHom := a.Have(
			"so its inverse is a homomorphism of the image field into F",
			"ring_homomorphism(field_ring(«imageField»), field_ring(F), inverse_on(F.carrier, ι))",
			By(
				isomorphism,
				ring_homomorphism.IsomorphismInverse.At(sourceRing, imageRing, ι),
				ring_homomorphism.RingIsomorphismDef.At(imageRing, sourceRing, back)))

		inImage := a.Have(
			"the image field has G's operations, so ι(x) is integral over image(ι, S) there too",
			"integral_over(restrict_ring(field_ring(«imageField»), image(ι, S)), ι(x))",
			Simp(Rev(field.RestrictFieldRing), Fwd(module_record.RestrictRingTwice)),
			By(integral))
		pushed := a.Have(
			"the inverse embedding carries that integrality to F",
			"integral_over(restrict_ring(field_ring(F), image(inverse_on(F.carrier, ι), image(ι, S))), "+
				"    inverse_on(F.carrier, ι, ι(x)))",
			By(
				F,
				imageFieldOn,
				backHom,
				inImage,
				x,
				sInCarrier,
				set_image.ImageSubset.At(ι, S, sourceCarrier),
				set_image.FunInImage.At(ι, sourceCarrier, x),
				FieldEmbeddingIntegral.At(imageRecord, sourceRecord, back, imageS, imageX)))
		leftInverse := a.Have(
			"the inverse undoes ι on F",
			"∀y:A. y ∈ F.carrier ⇒ inverse_on(F.carrier, ι, ι(y)) = y",
			By(injective, functions.InverseOnLeft))
		scalarsReturn := a.Have(
			"so it returns image(ι, S) to S",
			"image(inverse_on(F.carrier, ι), image(ι, S)) = S",
			BySets(leftInverse, sInCarrier))
		a.Show(
			"and ι(x) to x",
			By(Normalized, pushed, scalarsReturn, leftInverse.At(x), x))
	}),
})}

// MonicFactorCoefficientsIntegralInClosed — over an algebraically closed
// field, a monic factor of a monic polynomial over a subring S has its
// coefficients integral over S. A root of the factor is a root of the
// polynomial, and so integral over S; the elements integral over S are a
// subring, which then holds the coefficients (MonicCoefficientsFromRoots).
var MonicFactorCoefficientsIntegralInClosed = monicFactorCoefficientsIntegralInClosedThm{family.Add(registry.ProofEntry{
	Name: "MonicFactorCoefficientsIntegralInClosed",
	Key:  "prop_27d8156f16e77bf",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀S:set(A). ∀g h:(num → A). ∀i:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subring(field_ring(M), S)",
			"polynomial_over(S, g)",
			"polynomial_monic(g)",
			"polynomial_over(M.carrier, h)",
			"polynomial_monic(h)",
			"polynomial_divides(field_ring(M), h, g)",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(M), S), h(i))",
	}, func(a *Argument, M field.FieldFact[on.M], S *Expr[Set[A]], g, h *Arrow[Nat, A], i *Expr[Nat],
		closed, sSubring, gOver, gMonic, hOver, hMonic, hDivides Fact) {
		fieldValue := a.TermAs[FieldOps[A]]("M")
		coefficients := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		scalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), S)")
		zero := a.TermAs[A]("M.zero")
		one := a.TermAs[A]("M.one")
		carrier := a.TermAs[Set[A]]("M.carrier")
		ring := field.RingOn.Read(M)
		Ω, ΩDef := a.LetAs[Set[A]]("Ω", "integral_closure(restrict_ring(field_ring(M), S), M.carrier)")
		elements := integral_element.IntegralClosureDef.At(scalars, carrier)
		ΩSubring := a.Have(
			"the elements of M integral over S are a subring",
			"subring(field_ring(M), Ω)",
			By(Normalized, ΩDef, sSubring, integral_element.IntegralElementsSubring.Read(M).At(S)))

		w, cofactor := a.UnpackAs[Fun[Nat, A]](
			a.Unfolded(hDivides, polynomial_division.PolynomialDividesDef), "w")
		rootsIntegral := a.Have(
			"a root of h is a root of the monic g over S, and so integral over S",
			"∀r:A. r ∈ M.carrier ∧ polynomial_eval(h, r) = M.zero ⇒ r ∈ Ω",
			Derive(func(b *Argument) {
				r := b.FixAs[A]("r")
				root := b.Conjuncts(
					b.Assume(),
					"r lies in M",
					"h vanishes at r")
				rIn, hVanishes := root[0], root[1]
				rMember := b.MemberOf[on.M](r, rIn)
				gVanishes := b.Have(
					"a root of the factor h is a root of g",
					"polynomial_eval(g, r) = M.zero",
					By(
						Normalized,
						cofactor,
						hOver,
						hVanishes,
						polynomial_evaluation.EvalMulRoot.Read(ring).At(h, w, rMember)))
				// The degree of g is not assumed positive: a root of g rules
				// out the constant one, all a monic g of degree zero can be.
				gPositive := b.Have(
					"g, monic and vanishing at r, is not the constant one, so it has positive degree",
					"0 < polynomial_degree(g)",
					By(
						gVanishes,
						rMember,
						gMonic,
						sSubring,
						gOver,
						comm_ring.SubringSubset.At(coefficients, S),
						polynomial.PolynomialOverMono.At(zero, S, carrier, g),
						field.OneNotZeroOn.Read(M),
						polynomial.PolynomialMonicDef.At(zero, one, g),
						polynomial_evaluation.DegreeZeroEval.Read(ring).At(g, rMember),
						nat_order.PosIffNonzero.At(b.TermAs[Nat]("polynomial_degree(g)"))))
				rIntegral := b.Have(
					"g, a monic polynomial over S of positive degree, makes r integral over S",
					"integral_over(restrict_ring(field_ring(M), S), r)",
					By(gVanishes, gOver, gMonic, gPositive, integral_element.IntegralOverDef.At(scalars, r)))
				b.Show(
					"so r lies in Ω",
					ΩDef.Rw(),
					BySets(elements, rIn, rIntegral))
			}))
		roots := a.Have(
			"so the roots of h lie in Ω",
			"polynomial_roots(M.carrier, h) ⊆ Ω",
			Simp(Fwd(polynomial_roots.PolynomialRootsDef)),
			BySets(rootsIntegral))
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
			"and the elements of Ω are integral over S",
			ΩDef.Rw(),
			BySets(elements, hCoefficient))
	}),
})}

// MonicFactorCoefficientsIntegral — a monic factor over a field of a monic
// polynomial over a subring S has its coefficients integral over S
// (Kronecker). M embeds in its algebraic closure C, and an embedding keeps
// the monic polynomials and the factorization, so in the closed field C the
// images of the coefficients are integral over the image of S
// (MonicFactorCoefficientsIntegralInClosed). The embedding reflects
// integrality (FieldEmbeddingReflectsIntegral). The embedding step is a lemma
// of its own because it ranges over a second type B, the closure's host.
var MonicFactorCoefficientsIntegral = monicFactorCoefficientsIntegralThm{family.Add(registry.ProofEntry{
	Name: "MonicFactorCoefficientsIntegral",
	Key:  "prop_fae0a67d306de789",
	Reading: "Both monic hypotheses are load-bearing, over ℤ in ℚ: (X − 1)/2 divides " +
		"X² − 1, its cofactor 2(X + 1), and the monic X − 1/2 divides 2X − 1; 1/2 is " +
		"integral over ℤ in neither case. M need not be closed or algebraic over S.",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀S:set(A). ∀g h:(num → A). ∀i:num.",
		Hypotheses: []string{
			"subring(field_ring(M), S)",
			"polynomial_over(S, g)",
			"polynomial_monic(g)",
			"polynomial_over(M.carrier, h)",
			"polynomial_monic(h)",
			"polynomial_divides(field_ring(M), h, g)",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(M), S), h(i))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		intoClosed := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀S:set(A). ∀g h:(num → A). ∀i:num.",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"algebraically_closed_field(G)",
				"subring(field_ring(F), S)",
				"polynomial_over(S, g)",
				"polynomial_monic(g)",
				"polynomial_over(F.carrier, h)",
				"polynomial_monic(h)",
				"polynomial_divides(field_ring(F), h, g)",
			},
			Conclusion: "integral_over(restrict_ring(field_ring(F), S), h(i))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			S *Expr[Set[A]],
			g, h *Arrow[Nat, A],
			i *Expr[Nat],
			hom, closed, sSubring, gOver, gMonic, hOver, hMonic, hDivides Fact,
		) {
			source := a.TermAs[FieldOps[A]]("F")
			target := a.TermAs[FieldOps[B]]("G")
			sourceRing := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
			targetRing := a.TermAs[module_record.RingOps[B]]("field_ring(G)")
			carrier := a.TermAs[Set[A]]("F.carrier")
			sourceZero := a.TermAs[A]("F.zero")
			targetZero := a.TermAs[B]("G.zero")
			targetCarrier := a.TermAs[Set[B]]("G.carrier")
			imageS := a.TermAs[Set[B]]("image(ι, S)")
			gMapped := a.TermAs[Fun[Nat, B]]("λj:num. ι(g(j))")
			hMapped := a.TermAs[Fun[Nat, B]]("λj:num. ι(h(j))")

			sInCarrier := a.Have(
				"S lies in F",
				"S ⊆ F.carrier",
				By(sSubring, comm_ring.SubringSubset.At(sourceRing, S)))
			gImage := a.Have(
				"g maps to a monic polynomial over the image of S",
				"polynomial_over(image(ι, S), λj:num. ι(g(j))) ∧ polynomial_monic(λj:num. ι(g(j)))",
				By(
					F,
					G,
					hom,
					sInCarrier,
					gOver,
					gMonic,
					algebraic_element.FieldEmbeddingMonic.At(source, target, ι, S, g)))
			hImage := a.Have(
				"h maps to a monic polynomial over G",
				"polynomial_over(G.carrier, λj:num. ι(h(j))) ∧ polynomial_monic(λj:num. ι(h(j)))",
				By(
					F,
					G,
					hom,
					hOver,
					hMonic,
					ring_homomorphism.MapZero.Read(hom),
					ring_homomorphism.MapIn.Read(hom),
					polynomial.PolynomialOverMap.At(ι, sourceZero, targetZero, carrier, targetCarrier, h),
					set_order.SubsetRefl.At(carrier),
					algebraic_element.FieldEmbeddingMonic.At(source, target, ι, carrier, h)))
			imageDivides := a.Have(
				"the image of h divides the image of g",
				"polynomial_divides(field_ring(G), λj:num. ι(h(j)), λj:num. ι(g(j)))",
				By(F, G, hom, hOver, hDivides, algebraic_element.FieldEmbeddingDivides.At(source, target, ι, g, h)))
			sImageSubring := a.Have(
				"ι carries the subring S to a subring of G",
				"subring(field_ring(G), image(ι, S))",
				By(
					hom,
					sSubring,
					ring_homomorphism.RingHomRestrictSource.At(sourceRing, targetRing, ι, S),
					ring_homomorphism.ImageSubring.At(
						a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(F), S)"), targetRing, ι)))

			integralInG := a.Have(
				"in the closed field G the image of each coefficient is integral over the image of S",
				"integral_over(restrict_ring(field_ring(G), image(ι, S)), ι(h(i)))",
				By(
					G,
					closed,
					sImageSubring,
					gImage,
					hImage,
					imageDivides,
					MonicFactorCoefficientsIntegralInClosed.At(target, imageS, gMapped, hMapped, i)))
			a.Show(
				"the embedding reflects integrality back to F",
				By(
					F,
					G,
					hom,
					sInCarrier,
					hOver,
					polynomial.PolynomialOverDef.At(sourceZero, carrier, h),
					integralInG,
					FieldEmbeddingReflectsIntegral.At(source, target, ι, S, a.TermAs[A]("h(i)"))))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			S *Expr[Set[A]],
			g, h *Arrow[Nat, A],
			i *Expr[Nat],
			given Fact,
		) {
			baseRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			embedding := a.TermAs[Fun[A, _ClosureHost]]("«closureEmbedding»")
			imageCarrier := a.TermAs[Set[_ClosureHost]]("image(«closureEmbedding», M.carrier)")
			C, closure := a.UnpackAs[FieldOps[_ClosureHost]](AlgebraicClosureFieldOn.Read(M), "C")
			parts := a.Conjuncts(
				closure,
				"C is a field",
				"C is algebraically closed",
				"the image of M is a subfield of C",
				"the embedding is an isomorphism onto it",
				"C is algebraic over it")
			CField, closed, imageSubfield, isomorphism := parts[0], parts[1], parts[2], parts[3]
			closureRing := a.TermAs[module_record.RingOps[_ClosureHost]]("field_ring(C)")
			imageRing := a.TermAs[module_record.RingOps[_ClosureHost]](
				"restrict_ring(field_ring(C), image(«closureEmbedding», M.carrier))")
			hom := a.Have(
				"the embedding is a ring homomorphism into C",
				"ring_homomorphism(field_ring(M), field_ring(C), «closureEmbedding»)",
				By(
					isomorphism,
					imageSubfield,
					field.RingOn.Read(CField),
					field.SubfieldSubset.At(C, imageCarrier),
					ring_homomorphism.RingIsomorphismDef.At(baseRing, imageRing, embedding),
					ring_homomorphism.RingHomExtendTarget.At(baseRing, closureRing, embedding, imageCarrier)))
			a.Show(
				"M embeds in its algebraic closure C, a closed field",
				By(
					M,
					CField,
					closed,
					hom,
					given,
					At(intoClosed, a.TermAs[FieldOps[A]]("M"), C, embedding, S, g, h, i)))
		})
	}),
})}

// MinimalPolynomialOverClosed — an element integral over a ring R that is
// integrally closed in a field F containing it has its minimal polynomial
// over F with coefficients in R. A monic equation f of x over R lies over F,
// so x is algebraic over F and its minimal polynomial p divides f. p is a
// monic factor of the monic f over R, so each coefficient of p is integral
// over R (MonicFactorCoefficientsIntegral); it lies in F, in which R is
// integrally closed.
var MinimalPolynomialOverClosed = minimalPolynomialOverClosedThm{family.Add(registry.ProofEntry{
	Name: "MinimalPolynomialOverClosed",
	Reading: "Closedness of R in F is load-bearing: for R = ℤ[2i] in F = ℚ(i) and x = " +
		"i, the minimal polynomial X − i has −i ∉ R. F need not be the fraction field of R.",
	Key: "prop_f622a13976a8ea2d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀R F:set(A). ∀x:A.",
		Hypotheses: []string{
			"subring(field_ring(L), R)",
			"subfield(L, F)",
			"R ⊆ F",
			"integrally_closed_in(restrict_ring(field_ring(L), R), F)",
			"x ∈ L.carrier",
			"integral_over(restrict_ring(field_ring(L), R), x)",
		},
		Conclusion: "polynomial_over(R, minimal_polynomial(L, F, x))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		R, F *Expr[Set[A]],
		x *Member[A, on.L],
		rSubring, fSubfield, rInF, closedIn, integral Fact,
	) {
		fieldValue := a.TermAs[FieldOps[A]]("L")
		coefficients := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
		scalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), R)")
		zero := a.TermAs[A]("L.zero")
		carrier := a.TermAs[Set[A]]("L.carrier")
		fInL := a.Have(
			"F lies in L",
			"F ⊆ L.carrier",
			By(fSubfield, field.SubfieldSubset.At(fieldValue, F)))
		f, equation := a.UnpackAs[Fun[Nat, A]](a.Unfolded(integral, integral_element.IntegralOverDef), "f")
		parts := a.Conjuncts(
			equation,
			"f is a polynomial over R",
			"f is monic",
			"f has positive degree",
			"f vanishes at x")
		fOver, fMonic, fVanishes := parts[0], parts[1], parts[3]
		fOverF := a.Have(
			"R lies in F, so f is a polynomial over F",
			"polynomial_over(F, f)",
			By(rInF, fOver, polynomial.PolynomialOverMono.At(zero, R, F, f)))
		algebraic := a.Have(
			"f, monic and so nonzero, makes x algebraic over F",
			"algebraic_over(L, F, x)",
			By(
				fOverF,
				fMonic,
				fVanishes,
				polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(L)).At(f),
				algebraic_element.AlgebraicOverDef.At(fieldValue, F, x)))

		p, pDef := a.LetAs[Fun[Nat, A]]("p", "minimal_polynomial(L, F, x)")
		spec := a.Have(
			"p is a monic polynomial over F",
			"polynomial_over(F, p) ∧ polynomial_monic(p)",
			By(
				Normalized,
				pDef,
				fSubfield,
				algebraic,
				algebraic_element.MinimalPolynomialSpec.Read(L).At(F, x)))
		divides := a.Have(
			"p divides f, which vanishes at x, over F and so over L",
			"polynomial_divides(field_ring(L), p, f)",
			By(
				Normalized,
				pDef,
				fSubfield,
				algebraic,
				fOverF,
				fVanishes,
				fInL,
				algebraic_element.MinimalPolynomialDivides.Read(L).At(F, x, f),
				polynomial_division.DividesMono.At(coefficients, F, p, f)))
		inR := a.Have(
			"every coefficient of p is integral over R and lies in F, so in R",
			"∀i:num. p(i) ∈ R",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				integralCoefficient := b.Have(
					"p, a monic factor of the monic f over R, has p(i) integral over R",
					"integral_over(restrict_ring(field_ring(L), R), p(i))",
					By(
						rSubring,
						fOver,
						fMonic,
						fInL,
						spec,
						polynomial.PolynomialOverMono.At(zero, F, carrier, p),
						divides,
						MonicFactorCoefficientsIntegral.Read(L).At(R, f, p, i)))
				b.Show(
					"p(i) lies in F, in which R is integrally closed",
					By(
						integralCoefficient,
						closedIn,
						spec,
						integral_element.IntegrallyClosedDef.At(scalars, F),
						polynomial.PolynomialOverDef.At(zero, F, p)))
			}))
		a.Show(
			"p has finite support, being over F, and its coefficients in R",
			By(
				spec,
				inR,
				polynomial.PolynomialOverDef.At(zero, R, p),
				polynomial.PolynomialOverDef.At(zero, F, p)))
	}),
})}
