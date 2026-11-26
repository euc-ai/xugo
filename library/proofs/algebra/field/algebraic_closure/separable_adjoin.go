// separable_adjoin.go — a simple extension by a separable element is a
// separable extension. Inside an algebraically closed field the element's
// minimal polynomial has a root field that is Galois, so separable; any
// field embeds in its algebraic closure, and an embedding carries
// separability both ways.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldEmbeddingReflectsSeparable — a field embedding reflects
// separability, the mirror of galois_correspondence.FieldEmbeddingSeparable.
// On its image an embedding ι is an isomorphism, so its inverse is an
// embedding of the image field into F. Separability of ι(x) passes from G
// to the image field, the same separable polynomial annihilating ι(x)
// there, and the inverse carries it to F, where it says x is separable.
var FieldEmbeddingReflectsSeparable = fieldEmbeddingReflectsSeparableThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingReflectsSeparable",
	Key:  "prop_ba5358162c93699f",
	Reading: "x is not assumed algebraic over k: that comes with the separability " +
		"of ι(x), whose minimal polynomial pulls back to an annihilator of x. x ∈ " +
		"F.carrier is load-bearing: off the carrier, ι(x) says nothing about x.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"subfield(F, k)",
			"x ∈ F.carrier",
			"separable_over(G, image(ι, k), ι(x))",
		},
		Conclusion: "separable_over(F, k, x)",
		Abbrev: Abbrev{
			{Name: "imageField", Text: "restrict_field(G, image(ι, F.carrier))"},
		},
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G field.FieldFact[on.G],
		ι *Arrow[A, B],
		k *Expr[Set[A]],
		x *Member[A, on.F],
		hom, subfieldK, separable Fact,
	) {
		sourceRecord := a.TermAs[FieldOps[A]]("F")
		targetRecord := a.TermAs[FieldOps[B]]("G")
		imageRecord := a.TermAs[FieldOps[B]]("«imageField»")
		sourceRing := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		targetRing := a.TermAs[module_record.RingOps[B]]("field_ring(G)")
		imageRing := a.TermAs[module_record.RingOps[B]]("field_ring(«imageField»)")
		sourceCarrier := a.TermAs[Set[A]]("F.carrier")
		imageCarrier := a.TermAs[Set[B]]("image(ι, F.carrier)")
		imageK := a.TermAs[Set[B]]("image(ι, k)")
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
		imageKSubfield := a.Have(
			"image(ι, k) is a subfield of the image field",
			"subfield(«imageField», image(ι, k))",
			By(
				F,
				imageFieldOn,
				toImage,
				subfieldK,
				algebraic_element.FieldEmbeddingSubfieldsAdjoin.At(sourceRecord, imageRecord, ι)))

		m, mDef := a.LetAs[Fun[Nat, B]]("m", "minimal_polynomial(G, image(ι, k), ι(x))")
		data := a.Have(
			"in G, ι(x) is algebraic over image(ι, k) and m is separable",
			"algebraic_over(G, image(ι, k), ι(x)) ∧ "+
				"polynomial_separable(restrict_ring(field_ring(G), image(ι, k)), m)",
			By(
				Normalized,
				mDef,
				separable,
				galois_correspondence.SeparableOverDef.At(targetRecord, imageK, imageX)))
		base := a.Have(
			"image(ι, k) is a subfield of G, and ι(x) lies in G",
			"subfield(G, image(ι, k)) ∧ ι(x) ∈ G.carrier",
			By(
				F,
				G,
				x,
				subfieldK,
				hom,
				algebraic_element.FieldEmbeddingSubfieldsAdjoin.At(sourceRecord, targetRecord, ι),
				ring_homomorphism.MapIn.Read(hom)))
		annihilator := a.Have(
			"m is a polynomial over image(ι, k) vanishing at ι(x)",
			"polynomial_over(image(ι, k), m) ∧ polynomial_eval(m, ι(x)) = G.zero",
			By(
				Normalized,
				mDef,
				base,
				data,
				algebraic_element.MinimalPolynomialSpec.Read(G).AsFact().At(imageK, imageX)))
		inImage := a.Have(
			"so m makes ι(x) separable inside the image field",
			"separable_over(«imageField», image(ι, k), ι(x))",
			By(
				imageKSubfield,
				data,
				annihilator,
				field.RestrictFieldRing.At(targetRecord, imageCarrier),
				module_record.RestrictRingTwice.At(targetRing, imageCarrier, imageK),
				x,
				set_image.FunInImage.At(ι, sourceCarrier, x),
				galois_correspondence.SeparableAnnihilator.Read(imageFieldOn).AsFact().At(imageK, m, imageX)))
		pushed := a.Have(
			"the inverse embedding carries that separability to F",
			"separable_over(F, image(inverse_on(F.carrier, ι), image(ι, k)), inverse_on(F.carrier, ι, ι(x)))",
			By(
				F,
				imageFieldOn,
				backHom,
				imageKSubfield,
				inImage,
				x,
				set_image.FunInImage.At(ι, sourceCarrier, x),
				galois_correspondence.FieldEmbeddingSeparable.At(imageRecord, sourceRecord, back, imageK, imageX)))
		leftInverse := a.Have(
			"the inverse undoes ι on F",
			"∀y:A. y ∈ F.carrier ⇒ inverse_on(F.carrier, ι, ι(y)) = y",
			By(injective, functions.InverseOnLeft))
		scalarsReturn := a.Have(
			"so it returns image(ι, k) to k",
			"image(inverse_on(F.carrier, ι), image(ι, k)) = k",
			BySets(leftInverse, subfieldK, field.SubfieldSubset.At(sourceRecord, k)))
		a.Show(
			"and ι(x) to x",
			By(Normalized, pushed, scalarsReturn, leftInverse.At(x), x))
	}),
})}

// SeparableAdjoinSeparable — a simple extension by a separable element is
// a separable extension, in any ambient field: L embeds in its algebraic
// closure M, the image of F(z) there is the field the image of F generates
// with the image of z, and inside the closed field M every element of that
// field is separable. Separability of the image of x pulls back to x.
var SeparableAdjoinSeparable = separableAdjoinSeparableThm{family.Add(registry.ProofEntry{
	Name: "SeparableAdjoinSeparable",
	Key:  "prop_ca6bdf19860a209",
	Reading: "L is any field holding F and z: neither closed nor normal over F, so the " +
		"minimal polynomial of z need not split in L. The closure of L supplies the splitting.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀F:set(A). ∀z x:A.",
		Hypotheses: []string{
			"subfield(L, F)",
			"z ∈ L.carrier",
			"separable_over(L, F, z)",
			"x ∈ field_adjoin(L, F, {z})",
		},
		Conclusion: "separable_over(L, F, x)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Over a closed field the minimal polynomial p of z splits, so the
		// roots of p generate a field Galois over F, and F(z) lies in it.
		closedCase := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀F:set(A). ∀z x:A.",
			Hypotheses: []string{
				"algebraically_closed_field(L)",
				"subfield(L, F)",
				"z ∈ L.carrier",
				"separable_over(L, F, z)",
				"x ∈ field_adjoin(L, F, {z})",
			},
			Conclusion: "separable_over(L, F, x)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			F *Expr[Set[A]],
			z, x *Expr[A],
			closed, subfieldF, zIn, separable, xIn Fact,
		) {
			fieldRecord := a.TermAs[FieldOps[A]]("L")
			zMember := a.MemberOf[on.L](z, zIn)
			p, pDef := a.LetAs[Fun[Nat, A]]("p", "minimal_polynomial(L, F, z)")
			singleton := a.TermAs[Set[Fun[Nat, A]]]("{p}")
			data := a.Have(
				"z is algebraic over F and p is separable",
				"algebraic_over(L, F, z) ∧ polynomial_separable(restrict_ring(field_ring(L), F), p)",
				By(Normalized, pDef, separable, galois_correspondence.SeparableOverDef.At(fieldRecord, F, z)))
			annihilator := a.Have(
				"p is a polynomial over F vanishing at z",
				"polynomial_over(F, p) ∧ polynomial_eval(p, z) = L.zero",
				By(
					Normalized,
					pDef,
					zMember,
					subfieldF,
					data,
					algebraic_element.MinimalPolynomialSpec.Read(L).At(F, zMember)))
			polynomials := a.Have(
				"p, the one polynomial of {p}, is over F, separable and split in the closed field",
				Statement{
					Binders:    "∀q:(num → A).",
					Hypotheses: []string{"q ∈ {p}"},
					Conclusion: "polynomial_over(F, q) ∧ " +
						"polynomial_separable(restrict_ring(field_ring(L), F), q) ∧ " +
						"polynomial_splits(field_ring(L), q)",
				},
				BySets(data, annihilator, closed, ClosedFieldSplits.Read(L).At(p)))
			S, SDef := a.LetAs[Set[A]](
				"S", "{y:A | y ∈ L.carrier ∧ (∃q:(num → A). q ∈ {p} ∧ polynomial_eval(q, y) = L.zero)}")
			R, RDef := a.LetAs[Set[A]]("R", "field_adjoin(L, F, S)")
			galois := a.Have(
				"the root field theorem takes a finite family of polynomials, "+
					"here {p}: the roots of p generate a field R Galois over F",
				"galois_over(L, F, R)",
				By(
					RDef,
					SDef,
					subfieldF,
					polynomials,
					finite_set.FiniteSing.At(p),
					galois_correspondence.SeparableRootFieldGalois.Read(L).At(F, singleton)))
			roots := a.Have(
				"the roots lie in L, and z is one of them",
				"S ⊆ L.carrier ∧ z ∈ S",
				BySets(SDef, zIn, annihilator))
			generated := a.Have(
				"R is a subfield holding F and the root z",
				"subfield(L, R) ∧ F ⊆ R ∧ z ∈ R",
				BySets(
					RDef,
					subfieldF,
					roots,
					field.SubfieldSubset.At(fieldRecord, F),
					algebraic_element.AdjoinSubfield.Read(L).At(F, S)))
			inside := a.Have(
				"so F(z) lies in R",
				"field_adjoin(L, F, {z}) ⊆ R",
				By(subfieldF, generated, algebraic_element.AdjoinElementBetween.Read(L).At(F, R, z)))
			parts := a.Conjuncts(
				a.Unfolded(galois, galois_correspondence.GaloisOverDef),
				"R is finite over F",
				"R is normal over F",
				"every element of R is separable over F")
			a.Show(
				"x lies in R, so it is separable over F",
				By(parts[2].At(x), xIn, inside, set_basic.SubsetDef))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			F *Expr[Set[A]],
			z, x *Expr[A],
			subfieldF, zIn, separable, xIn Fact,
		) {
			fieldRecord := a.TermAs[FieldOps[A]]("L")
			baseRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			embedding := a.TermAs[Fun[A, _ClosureHost]]("«closureEmbedding»")
			imageCarrier := a.TermAs[Set[_ClosureHost]]("image(«closureEmbedding», L.carrier)")
			imageF := a.TermAs[Set[_ClosureHost]]("image(«closureEmbedding», F)")
			imageZ := a.TermAs[_ClosureHost]("«closureEmbedding»(z)")
			imageX := a.TermAs[_ClosureHost]("«closureEmbedding»(x)")
			zMember := a.MemberOf[on.L](z, zIn)
			M, closure := a.UnpackAs[FieldOps[_ClosureHost]](AlgebraicClosureFieldOn.Read(L), "M")
			parts := a.Conjuncts(
				closure,
				"M is a field",
				"M is algebraically closed",
				"the image of L is a subfield of M",
				"the embedding is an isomorphism onto it",
				"M is algebraic over it")
			MField, closed, imageSubfield, isomorphism := parts[0], parts[1], parts[2], parts[3]
			MRing := a.TermAs[module_record.RingOps[_ClosureHost]]("field_ring(M)")
			imageRing := a.TermAs[module_record.RingOps[_ClosureHost]](
				"restrict_ring(field_ring(M), image(«closureEmbedding», L.carrier))")
			hom := a.Have(
				"the embedding is a ring homomorphism into M",
				"ring_homomorphism(field_ring(L), field_ring(M), «closureEmbedding»)",
				By(
					isomorphism,
					imageSubfield,
					field.RingOn.Read(MField),
					field.SubfieldSubset.At(M, imageCarrier),
					ring_homomorphism.RingIsomorphismDef.At(baseRing, imageRing, embedding),
					ring_homomorphism.RingHomExtendTarget.At(baseRing, MRing, embedding, imageCarrier)))
			pushed := a.Have(
				"the image of z is separable over the image of F",
				"separable_over(M, image(«closureEmbedding», F), «closureEmbedding»(z))",
				By(
					L,
					MField,
					hom,
					subfieldF,
					zIn,
					separable,
					galois_correspondence.FieldEmbeddingSeparable.At(fieldRecord, M, embedding, F, z)))
			adjoinImage := a.Have(
				"the embedding carries F(z) to the field the images generate",
				"image(«closureEmbedding», field_adjoin(L, F, {z})) = "+
					"field_adjoin(M, image(«closureEmbedding», F), image(«closureEmbedding», {z}))",
				By(
					L,
					MField,
					hom,
					subfieldF,
					zIn,
					field.SubfieldSubset,
					set_order.SingSubset,
					algebraic_element.FieldEmbeddingSubfieldsAdjoin.At(fieldRecord, M, embedding)))
			xImage := a.Have(
				"the image of x lies in the field generated by the image of z",
				"«closureEmbedding»(x) ∈ field_adjoin(M, image(«closureEmbedding», F), {«closureEmbedding»(z)})",
				By(
					xIn,
					adjoinImage,
					// {z} reads as insert(z, ∅), so ImageClauses at the witness ∅ gives the image of {z}.
					set_image.ImageClauses.At(embedding, z, a.TermAs[Set[A]]("∅")),
					set_image.FunInImage.At(embedding, a.TermAs[Set[A]]("field_adjoin(L, F, {z})"), x)))
			imageData := a.Have(
				"the image of F is a subfield of M, and the image of z lies in M",
				"subfield(M, image(«closureEmbedding», F)) ∧ «closureEmbedding»(z) ∈ M.carrier",
				By(
					L,
					MField,
					hom,
					subfieldF,
					zIn,
					algebraic_element.FieldEmbeddingSubfieldsAdjoin.At(fieldRecord, M, embedding),
					ring_homomorphism.MapIn.Read(hom)))
			imageSeparable := a.Have(
				"inside the closed field M the image of x is separable",
				"separable_over(M, image(«closureEmbedding», F), «closureEmbedding»(x))",
				By(MField, closed, imageData, pushed, xImage, At(closedCase, M, imageF, imageZ, imageX)))
			xInL := a.Have(
				"x lies in L, F(z) being a subfield of L",
				"x ∈ L.carrier",
				BySets(
					xIn,
					subfieldF,
					zMember,
					algebraic_element.AdjoinElementSubfield.Read(L).At(F, zMember),
					field.SubfieldSubset.At(fieldRecord, a.TermAs[Set[A]]("field_adjoin(L, F, {z})"))))
			a.Show(
				"the embedding reflects separability",
				By(
					L,
					MField,
					hom,
					subfieldF,
					xInL,
					imageSeparable,
					FieldEmbeddingReflectsSeparable.At(fieldRecord, M, embedding, F, x)))
		})
	}),
})}
