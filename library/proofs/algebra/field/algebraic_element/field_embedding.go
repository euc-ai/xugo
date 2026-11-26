// field_embedding.go — a field embedding, a ring homomorphism ι of a field
// F into a field G: it is one-to-one, and carries subfields, generated
// fields, finite extensions with their degrees, and polynomials over a
// subfield with their degree, products, values, derivatives and
// irreducibility to their images.

package algebraic_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldEmbeddingPreimageSubfield — under a field embedding, the preimage of a
// subfield of the target is a subfield of the source: the embedding keeps
// zero, one, sums, negatives, products and inverses, so each closure
// condition of the target subfield pulls back to its preimage.
var FieldEmbeddingPreimageSubfield = fieldEmbeddingPreimageSubfieldThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingPreimageSubfield",
	Key:  "prop_74a6c280e35f2c13",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀H:set(B).",
		Hypotheses: []string{"ring_homomorphism(field_ring(F), field_ring(G), ι)", "subfield(G, H)"},
		Conclusion: "subfield(F, preimage_on(F.carrier, ι, H))",
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G field.FieldFact[on.G],
		ι *Arrow[A, B],
		H *Expr[Set[B]],
		hom, targetField Fact,
	) {
		g := a.TermAs[FieldOps[B]]("G")
		_, preimageDef := a.LetAs[Set[A]]("S", "preimage_on(F.carrier, ι, H)")
		SDef := a.Simplified(preimageDef, Fwd(functions.PreimageOnDef))
		add := ring_homomorphism.MapAdd.Read(hom).AsFact()
		mul := ring_homomorphism.MapMul.Read(hom).AsFact()
		neg := ring_homomorphism.MapNeg.Read(hom).AsFact()
		inverse := a.Have(
			"inverses are preserved",
			"∀u:A. u ∈ F.carrier ⇒ ι(F.inv(u)) = G.inv(ι(u))",
			Derive(func(b *Argument) {
				u := b.FixAs[A]("u")
				uF := b.MemberOf[on.F](u, b.Assume())
				b.Show(
					"ι keeps zero, one and products between the two fields",
					By(
						G,
						field.MapInv.Read(F).At(g, ι, uF),
						ring_homomorphism.MapIn.Read(hom),
						ring_homomorphism.MapMul.Read(hom),
						ring_homomorphism.MapZero.Read(hom),
						ring_homomorphism.MapOne.Read(hom)))
			}))
		source := a.Simplified(field.CarrierSubfield.Read(F), Fwd(field.SubfieldDef))
		closedSource := a.Conjuncts(
			source,
			"source carrier inclusion",
			"source zero",
			"source one",
			"source addition closure",
			"source negation closure",
			"source multiplication closure",
			"source inverse closure")
		target := a.Simplified(targetField, Fwd(field.SubfieldDef))
		closedTarget := a.Conjuncts(
			target,
			"target carrier inclusion",
			"target zero",
			"target one",
			"target addition closure",
			"target negation closure",
			"target multiplication closure",
			"target inverse closure")
		a.Show(
			"the preimage is a subfield",
			Simp(Fwd(field.SubfieldDef)),
			SplitConjAll(
				Case(
					"the preimage lies in the source carrier",
					BySets(SDef)),
				Case(
					"the preimage contains source zero",
					BySets(SDef, closedSource[1], closedTarget[1], ring_homomorphism.MapZero.Read(hom))),
				Case(
					"the preimage contains source one",
					BySets(SDef, closedSource[2], closedTarget[2], ring_homomorphism.MapOne.Read(hom))),
				Case(
					"the preimage is closed under addition",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						v := b.FixAs[A]("v")
						inPreimage := b.Assume()
						b.Show(
							"the sum and its image lie in the two fields",
							BySets(
								SDef,
								inPreimage,
								closedSource[3].At(u, v),
								closedTarget[3].At(b.TermAs[B]("ι(u)"), b.TermAs[B]("ι(v)")),
								add.At(u, v)))
					})),
				Case(
					"the preimage is closed under negation",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						inPreimage := b.Assume()
						b.Show(
							"the negative and its image lie in the two fields",
							BySets(SDef, inPreimage, closedSource[4].At(u), closedTarget[4].At(b.TermAs[B]("ι(u)")), neg.At(u)))
					})),
				Case(
					"the preimage is closed under multiplication",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						v := b.FixAs[A]("v")
						inPreimage := b.Assume()
						b.Show(
							"the product and its image lie in the two fields",
							BySets(
								SDef,
								inPreimage,
								closedSource[5].At(u, v),
								closedTarget[5].At(b.TermAs[B]("ι(u)"), b.TermAs[B]("ι(v)")),
								mul.At(u, v)))
					})),
				Case(
					"the preimage is closed under inversion",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						inPreimage := b.Assume()
						b.Show(
							"the inverse and its image lie in the two fields",
							BySets(
								SDef,
								inPreimage,
								closedSource[6].At(u),
								closedTarget[6].At(b.TermAs[B]("ι(u)")),
								inverse.At(u)))
					})),
			))
	}),
})}

// FieldEmbeddingSubfieldsAdjoin — a field embedding is one-to-one and
// carries subfields and generated fields to their images. The image of a
// subfield is closed under the operations the embedding keeps; and the
// field the image generators generate holds the image of the generated
// field because its preimage is a subfield holding the generators.
var FieldEmbeddingSubfieldsAdjoin = fieldEmbeddingSubfieldsAdjoinThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingSubfieldsAdjoin",
	Key:  "prop_2db5f369ab691d0c",
	Build: family.Sections(Statement{
		Binders:    "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B).",
		Hypotheses: []string{"ring_homomorphism(field_ring(F), field_ring(G), ι)"},
		Conclusion: "injective_on(F.carrier, ι) ∧ " +
			"(∀S:set(A). subfield(F, S) ⇒ subfield(G, image(ι, S))) ∧ " +
			"(∀K E:set(A). " +
			"    K ⊆ F.carrier ∧ E ⊆ F.carrier ⇒ " +
			"    image(ι, field_adjoin(F, K, E)) = field_adjoin(G, image(ι, K), image(ι, E)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		inverses := ctx.Lemma(Statement{
			Binders:    "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀x:A.",
			Hypotheses: []string{"ring_homomorphism(field_ring(F), field_ring(G), ι)", "x ∈ F.carrier"},
			Conclusion: "ι(F.inv(x)) = G.inv(ι(x))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			x *Member[A, on.F],
			hom Fact,
		) {
			a.Show(
				"ι keeps zero, one and products between the two fields",
				By(
					G,
					field.MapInv.Read(F).At(a.TermAs[FieldOps[B]]("G"), ι, x),
					ring_homomorphism.MapIn.Read(hom),
					ring_homomorphism.MapMul.Read(hom),
					ring_homomorphism.MapZero.Read(hom),
					ring_homomorphism.MapOne.Read(hom)))
		})

		imageSubfield := ctx.Lemma(Statement{
			Binders:    "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀S:set(A).",
			Hypotheses: []string{"ring_homomorphism(field_ring(F), field_ring(G), ι)", "subfield(F, S)"},
			Conclusion: "subfield(G, image(ι, S))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			S *Expr[Set[A]],
			hom, sourceField Fact,
		) {
			f := a.TermAs[FieldOps[A]]("F")
			g := a.TermAs[FieldOps[B]]("G")
			mapsInto := ring_homomorphism.MapIn.Read(hom).AsFact()
			add := ring_homomorphism.MapAdd.Read(hom).AsFact()
			mul := ring_homomorphism.MapMul.Read(hom).AsFact()
			neg := ring_homomorphism.MapNeg.Read(hom).AsFact()
			inverse := a.Have(
				"inverses are preserved",
				"∀u:A. u ∈ F.carrier ⇒ ι(F.inv(u)) = G.inv(ι(u))",
				By(F, G, hom, At(inverses, f, g, ι)))
			source := a.Simplified(sourceField, Fwd(field.SubfieldDef))
			closed := a.Conjuncts(
				source,
				"source carrier inclusion",
				"source zero",
				"source one",
				"source addition closure",
				"source negation closure",
				"source multiplication closure",
				"source inverse closure")
			a.Show(
				"the image is a subfield",
				Simp(Fwd(field.SubfieldDef)),
				SplitConjAll(
					Case(
						"the image lies in the target carrier",
						BySets(mapsInto, closed[0])),
					Case(
						"the image contains target zero",
						By(
							Normalized,
							closed[1],
							ring_homomorphism.MapZero.Read(hom),
							set_image.FunInImage.At(ι, S, a.TermAs[A]("F.zero")))),
					Case(
						"the image contains target one",
						By(
							Normalized,
							closed[2],
							ring_homomorphism.MapOne.Read(hom),
							set_image.FunInImage.At(ι, S, a.TermAs[A]("F.one")))),
					Case(
						"the image is closed under addition",
						Derive(func(b *Argument) {
							u := b.FixAs[B]("u")
							v := b.FixAs[B]("v")
							inImage := b.Assume()
							x, y, preimages := b.Obtain2As[A, A](
								"choose source preimages",
								"∃x y:A. x ∈ S ∧ y ∈ S ∧ u = ι(x) ∧ v = ι(y)",
								By(Normalized, inImage, set_basic.InImage.At(ι, S, u), set_basic.InImage.At(ι, S, v)),
								Named("x", "y"))
							inSource := b.Have(
								"the preimages belong to the source carrier",
								"x ∈ F.carrier ∧ y ∈ F.carrier",
								By(preimages, closed[0], set_basic.SubsetDef.At(S, b.TermAs[Set[A]]("F.carrier"))))
							mappedSum := b.Have(
								"the target sum is the image of the source sum",
								"G.add(u, v) = ι(F.add(x, y))",
								By(Normalized, preimages, add.At(x, y), inSource))
							b.Show(
								"the sum belongs to the image",
								By(
									Normalized,
									preimages,
									closed[3].At(x, y),
									mappedSum,
									set_image.FunInImage.At(ι, S, b.TermAs[A]("F.add(x, y)"))))
						})),
					Case(
						"the image is closed under negation",
						Derive(func(b *Argument) {
							u := b.FixAs[B]("u")
							inImage := b.Assume()
							x, preimage := b.ObtainAs[A](
								"choose a source preimage",
								"∃x:A. u = ι(x) ∧ x ∈ S",
								By(inImage, set_basic.InImage.At(ι, S, u)),
								Named("x"))
							inSource := b.Have(
								"the preimage belongs to the source carrier",
								"x ∈ F.carrier",
								By(preimage, closed[0], set_basic.SubsetDef.At(S, b.TermAs[Set[A]]("F.carrier"))))
							mappedNeg := b.Have(
								"the target negative is the image of the source negative",
								"G.neg(u) = ι(F.neg(x))",
								By(Normalized, preimage, neg.At(x), inSource))
							b.Show(
								"the negative belongs to the image",
								By(
									Normalized,
									preimage,
									closed[4].At(x),
									mappedNeg,
									set_image.FunInImage.At(ι, S, b.TermAs[A]("F.neg(x)"))))
						})),
					Case(
						"the image is closed under multiplication",
						Derive(func(b *Argument) {
							u := b.FixAs[B]("u")
							v := b.FixAs[B]("v")
							inImage := b.Assume()
							x, y, preimages := b.Obtain2As[A, A](
								"choose source preimages",
								"∃x y:A. x ∈ S ∧ y ∈ S ∧ u = ι(x) ∧ v = ι(y)",
								By(Normalized, inImage, set_basic.InImage.At(ι, S, u), set_basic.InImage.At(ι, S, v)),
								Named("x", "y"))
							inSource := b.Have(
								"the preimages belong to the source carrier",
								"x ∈ F.carrier ∧ y ∈ F.carrier",
								By(preimages, closed[0], set_basic.SubsetDef.At(S, b.TermAs[Set[A]]("F.carrier"))))
							mappedProduct := b.Have(
								"the target product is the image of the source product",
								"G.mul(u, v) = ι(F.mul(x, y))",
								By(Normalized, preimages, mul.At(x, y), inSource))
							b.Show(
								"the product belongs to the image",
								By(
									Normalized,
									preimages,
									closed[5].At(x, y),
									mappedProduct,
									set_image.FunInImage.At(ι, S, b.TermAs[A]("F.mul(x, y)"))))
						})),
					Case(
						"the image is closed under inversion",
						Derive(func(b *Argument) {
							u := b.FixAs[B]("u")
							inImage := b.Assume()
							x, preimage := b.ObtainAs[A](
								"choose a source preimage",
								"∃x:A. u = ι(x) ∧ x ∈ S",
								By(inImage, set_basic.InImage.At(ι, S, u)),
								Named("x"))
							inSource := b.Have(
								"the preimage belongs to the source carrier",
								"x ∈ F.carrier",
								By(preimage, closed[0], set_basic.SubsetDef.At(S, b.TermAs[Set[A]]("F.carrier"))))
							mappedInverse := b.Have(
								"the target inverse is the image of the source inverse",
								"G.inv(u) = ι(F.inv(x))",
								By(Normalized, preimage, inverse.At(x), inSource))
							b.Show(
								"the inverse belongs to the image",
								By(
									Normalized,
									preimage,
									closed[6].At(x),
									mappedInverse,
									set_image.FunInImage.At(ι, S, b.TermAs[A]("F.inv(x)"))))
						})),
				))
		})

		adjoinImage := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀K E:set(A).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"K ⊆ F.carrier", "E ⊆ F.carrier",
			},
			Conclusion: "image(ι, field_adjoin(F, K, E)) = field_adjoin(G, image(ι, K), image(ι, E))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			K, E *Expr[Set[A]],
			hom, baseInside, generatorsInside Fact,
		) {
			joined, joinedDef := a.LetAs[Set[A]]("joined", "field_adjoin(F, K, E)")
			hostJoin, hostJoinDef := a.LetAs[Set[B]]("hostJoin", "field_adjoin(G, image(ι, K), image(ι, E))")
			pullback, pullbackDef := a.LetAs[Set[A]]("pullback", "preimage_on(F.carrier, ι, hostJoin)")
			f := a.TermAs[FieldOps[A]]("F")
			g := a.TermAs[FieldOps[B]]("G")
			imageK := a.TermAs[Set[B]]("image(ι, K)")
			imageE := a.TermAs[Set[B]]("image(ι, E)")
			imageJoined := a.TermAs[Set[B]]("image(ι, joined)")
			joinedProps := a.Have(
				"the source generated field contains its generators",
				"subfield(F, joined) ∧ K ⊆ joined ∧ E ⊆ joined",
				By(Normalized, F, baseInside, generatorsInside, joinedDef, AdjoinSubfield.Read(F).At(K, E)))
			imageJoinedField := a.Have(
				"its image is a target subfield",
				"subfield(G, image(ι, joined))",
				By(F, G, hom, joinedProps, At(imageSubfield, f, g, ι, joined)))
			imageGenerators := a.Have(
				"the image field contains the image generators",
				"image(ι, K) ⊆ image(ι, joined) ∧ image(ι, E) ⊆ image(ι, joined)",
				By(joinedProps, set_image.ImageSubset.At(ι, K, joined), set_image.ImageSubset.At(ι, E, joined)))
			hostInsideImage := a.Have(
				"the target generated field is contained in the source image",
				"hostJoin ⊆ image(ι, joined)",
				By(
					Normalized,
					G,
					hostJoinDef,
					imageJoinedField,
					imageGenerators,
					AdjoinLeast.Read(G).At(imageK, imageE, imageJoined)))
			generatorsInTarget := a.Have(
				"both image generators lie in the target carrier",
				"image(ι, K) ⊆ G.carrier ∧ image(ι, E) ⊆ G.carrier",
				BySets(baseInside, generatorsInside, ring_homomorphism.MapIn.Read(hom)))
			hostProps := a.Have(
				"the target generated field contains the image generators",
				"subfield(G, hostJoin) ∧ image(ι, K) ⊆ hostJoin ∧ image(ι, E) ⊆ hostJoin",
				By(Normalized, G, hostJoinDef, generatorsInTarget, AdjoinSubfield.Read(G).At(imageK, imageE)))
			pullbackField := a.Have(
				"its preimage is a source subfield",
				"subfield(F, pullback)",
				By(
					Normalized,
					G,
					pullbackDef,
					hostProps,
					hom,
					FieldEmbeddingPreimageSubfield.Read(F).At(g, ι, hostJoin)))
			pullbackSet := a.Simplified(pullbackDef, Fwd(functions.PreimageOnDef))
			generatorsInPreimage := a.Have(
				"the preimage contains the source generators",
				"K ⊆ pullback ∧ E ⊆ pullback",
				BySets(pullbackSet, baseInside, generatorsInside, hostProps))
			joinedInsidePreimage := a.Have(
				"the source generated field lies in the preimage",
				"joined ⊆ pullback",
				By(
					Normalized,
					F,
					joinedDef,
					pullbackField,
					generatorsInPreimage,
					AdjoinLeast.Read(F).At(K, E, pullback)))
			imageInsideHost := a.Have(
				"the image of the source generated field lies in the target generated field",
				"image(ι, joined) ⊆ hostJoin",
				BySets(joinedInsidePreimage, pullbackSet))
			a.Show(
				"the two generated fields agree",
				BySets(hostInsideImage, imageInsideHost))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			hom Fact,
		) {
			f := a.TermAs[FieldOps[A]]("F")
			g := a.TermAs[FieldOps[B]]("G")
			a.Show(
				"the embedding is one-to-one and transports subfields and adjoining",
				SplitConjAll(
					Case(
						"the embedding is one-to-one, as every homomorphism of fields is",
						By(G, hom, ring_homomorphism.FieldHomomorphismInjective.Read(F).At(g, ι))),
					Case(
						"subfields map to subfields",
						Derive(func(b *Argument) {
							S := b.FixAs[Set[A]]("S")
							sourceField := b.Assume()
							b.Show(
								"the image is a target subfield",
								By(F, G, hom, sourceField, At(imageSubfield, f, g, ι, S)))
						})),
					Case(
						"adjoining commutes with the embedding",
						Derive(func(b *Argument) {
							K := b.FixAs[Set[A]]("K")
							E := b.FixAs[Set[A]]("E")
							inside := b.Assume()
							b.Show(
								"the generated fields have the same image",
								By(F, G, hom, inside, At(adjoinImage, f, g, ι, K, E)))
						})),
				))
		})
	}),
})}

// FieldEmbeddingFiniteDegree — a field embedding preserves finite
// extension degrees. Images and preimages carry scalar submodules to
// submodules, hence preserve spans; fresh-element induction then
// preserves finite independent sets and finite bases.
var FieldEmbeddingFiniteDegree = fieldEmbeddingFiniteDegreeThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingFiniteDegree",
	Key:  "prop_fbf7bc1dbf55355d",
	Build: family.Sections(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k K:set(A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"subfield(F, k)", "subfield(F, K)", "k ⊆ K", "finite_extension(F, k, K)",
		},
		Conclusion: "finite_extension(G, image(ι, k), image(ι, K)) ∧ " +
			"extension_degree(G, image(ι, k), image(ι, K)) = extension_degree(F, k, K)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		ambientModule := ctx.Lemma(Statement{
			Binders:    "∀M:field_on(A). ∀k:set(A).",
			Hypotheses: []string{"subfield(M, k)"},
			Conclusion: "module_on(restrict_ring(field_ring(M), k), regular_module(field_ring(M)))",
		}, func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], scalarField Fact) {
			a.Show(
				"restrict scalars to the subfield",
				By(
					scalarField,
					field.SubfieldSubring.Read(M).At(k),
					module.RegularModuleOverSubring.Read(field.RingOn.Read(M)).At(k)))
		})
		subfieldModule := ctx.Lemma(Statement{
			Binders:    "∀M:field_on(A). ∀k l:set(A).",
			Hypotheses: []string{"subfield(M, k)", "subfield(M, l)", "k ⊆ l"},
			Conclusion: "submodule(restrict_ring(field_ring(M), k), regular_module(field_ring(M)), l)",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l *Expr[Set[A]],
			baseField, upperField, nested Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			r := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)")
			v := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
			vl := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(regular_module(field_ring(M)), l)")
			modules := a.Have(
				"the inclusion has two modules over k",
				"module_on(restrict_ring(field_ring(M), k), restrict_module(regular_module(field_ring(M)), l)) ∧ "+
					"module_on(restrict_ring(field_ring(M), k), regular_module(field_ring(M))) ∧ "+
					"l ⊆ M.carrier",
				By(
					M,
					baseField,
					upperField,
					nested,
					field_extension.ExtensionModuleOn.Read(M).At(k, l),
					field_extension.SubfieldScalars.Read(M).At(k),
					field.SubfieldSubset.At(m, l)))
			inclusion := a.Have(
				"the inclusion is linear",
				"module_homomorphism(restrict_ring(field_ring(M), k), "+
					"    restrict_module(regular_module(field_ring(M)), l), "+
					"    regular_module(field_ring(M)), "+
					"    λx:A. x)",
				By(
					modules,
					module_homomorphism.ModuleHomomorphismDef.At(r, vl, v, a.TermAs[Fun[A, A]]("λx:A. x")),
					set_basic.SubsetDef.At(l, a.TermAs[Set[A]]("M.carrier"))))
			image := a.Have(
				"the inclusion has image l",
				"image(λx:A. x, l) = l",
				BySets())
			a.Show(
				"l is a submodule of the ambient field",
				By(Normalized, module_homomorphism.ImageSubmodule.Read(inclusion), image))
		})
		imageSubmodule := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k U:set(A).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"subfield(F, k)", "submodule(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), U)",
			},
			Conclusion: "submodule(restrict_ring(field_ring(G), image(ι, k)), " +
				"    regular_module(field_ring(G)), " +
				"    image(ι, U))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k, U *Expr[Set[A]],
			hom, scalarField, sourceModule Fact,
		) {
			f := a.TermAs[FieldOps[A]]("F")
			g := a.TermAs[FieldOps[B]]("G")
			add := ring_homomorphism.MapAdd.Read(hom).AsFact()
			mul := ring_homomorphism.MapMul.Read(hom).AsFact()
			uInside := a.Simplified(submodule.SubmoduleSubset.Read(sourceModule))
			uZero := a.Simplified(submodule.SubmoduleZero.Read(sourceModule))
			uAdd := a.Simplified(submodule.SubmoduleAdd.Read(sourceModule))
			uSmul := a.Simplified(submodule.SubmoduleSmul.Read(sourceModule))
			imageScalars := a.Have(
				"the image scalars form a subfield",
				"subfield(G, image(ι, k))",
				By(F, G, hom, scalarField, FieldEmbeddingSubfieldsAdjoin.At(f, g, ι)))
			targetModule := a.Have(
				"the target field is a module over the image scalars",
				"module_on(restrict_ring(field_ring(G), image(ι, k)), regular_module(field_ring(G)))",
				By(G, imageScalars, At(ambientModule, g, a.TermAs[Set[B]]("image(ι, k)"))))
			imageInside := a.Have(
				"the image submodule lies in the target carrier",
				"image(ι, U) ⊆ G.carrier",
				BySets(ring_homomorphism.MapIn.Read(hom), uInside))
			imageZero := a.Have(
				"the image contains target zero",
				"G.zero ∈ image(ι, U)",
				By(
					Normalized,
					uZero,
					ring_homomorphism.MapZero.Read(hom),
					set_image.FunInImage.At(ι, U, a.TermAs[A]("F.zero"))))
			imageAdd := a.Have(
				"the image is closed under sums",
				"∀u v:B. u ∈ image(ι, U) ∧ v ∈ image(ι, U) ⇒ G.add(u, v) ∈ image(ι, U)",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					v := b.FixAs[B]("v")
					inImage := b.Assume()
					x, y, preimages := b.Obtain2As[A, A](
						"choose source preimages",
						"∃x y:A. x ∈ U ∧ y ∈ U ∧ u = ι(x) ∧ v = ι(y)",
						By(Normalized, inImage, set_basic.InImage.At(ι, U, u), set_basic.InImage.At(ι, U, v)),
						Named("x", "y"))
					ambient := b.Have(
						"the preimages belong to the source carrier",
						"x ∈ F.carrier ∧ y ∈ F.carrier",
						BySets(preimages, uInside))
					mapped := b.Have(
						"the target sum is the image of the source sum",
						"G.add(u, v) = ι(F.add(x, y))",
						By(Normalized, preimages, add.At(x, y), ambient))
					b.Show(
						"the sum belongs to the image",
						By(
							Normalized,
							preimages,
							uAdd.At(x, y),
							mapped,
							set_image.FunInImage.At(ι, U, b.TermAs[A]("F.add(x, y)"))))
				}))
			imageSmul := a.Have(
				"the image is closed under image scalars",
				"∀c u:B. c ∈ image(ι, k) ∧ u ∈ image(ι, U) ⇒ G.mul(c, u) ∈ image(ι, U)",
				Derive(func(b *Argument) {
					c := b.FixAs[B]("c")
					u := b.FixAs[B]("u")
					inImage := b.Assume()
					x, y, preimages := b.Obtain2As[A, A](
						"choose scalar and vector preimages",
						"∃x y:A. x ∈ k ∧ y ∈ U ∧ c = ι(x) ∧ u = ι(y)",
						By(Normalized, inImage, set_basic.InImage.At(ι, k, c), set_basic.InImage.At(ι, U, u)),
						Named("x", "y"))
					ambient := b.Have(
						"the preimages belong to the source carrier",
						"x ∈ F.carrier ∧ y ∈ F.carrier",
						BySets(preimages, scalarField, field.SubfieldSubset.At(f, k), uInside))
					mapped := b.Have(
						"the target product is the image of the source product",
						"G.mul(c, u) = ι(F.mul(x, y))",
						By(Normalized, preimages, mul.At(x, y), ambient))
					b.Show(
						"the scalar product belongs to the image",
						By(
							Normalized,
							preimages,
							uSmul.At(x, y),
							mapped,
							set_image.FunInImage.At(ι, U, b.TermAs[A]("F.mul(x, y)"))))
				}))
			a.Show(
				"the image satisfies the submodule criterion",
				By(
					imageInside,
					imageZero,
					imageAdd,
					imageSmul,
					submodule.SubmoduleCriterion.Read(targetModule).At(a.TermAs[Set[B]]("image(ι, U)"))))
		})
		preimageSubmodule := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀H:set(B).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"subfield(F, k)",
				"submodule(restrict_ring(field_ring(G), image(ι, k)), regular_module(field_ring(G)), H)",
			},
			Conclusion: "submodule(restrict_ring(field_ring(F), k), " +
				"    regular_module(field_ring(F)), " +
				"    {x:A | x ∈ F.carrier ∧ ι(x) ∈ H})",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k *Expr[Set[A]],
			H *Expr[Set[B]],
			hom, scalarField, targetSubmodule Fact,
		) {
			pullback, pullbackDef := a.LetAs[Set[A]]("pullback", "{x:A | x ∈ F.carrier ∧ ι(x) ∈ H}")
			f := a.TermAs[FieldOps[A]]("F")
			add := ring_homomorphism.MapAdd.Read(hom).AsFact()
			mul := ring_homomorphism.MapMul.Read(hom).AsFact()
			sourceModule := a.Have(
				"the source field is a module over k",
				"module_on(restrict_ring(field_ring(F), k), regular_module(field_ring(F)))",
				By(F, scalarField, At(ambientModule, f, k)))
			sourceCarrier := a.Simplified(submodule.CarrierSubmodule.Read(sourceModule))
			sourceZero := a.Simplified(submodule.SubmoduleZero.Read(sourceCarrier))
			sourceAdd := a.Simplified(submodule.SubmoduleAdd.Read(sourceCarrier))
			sourceSmul := a.Simplified(submodule.SubmoduleSmul.Read(sourceCarrier))
			targetZero := a.Simplified(submodule.SubmoduleZero.Read(targetSubmodule))
			targetAdd := a.Simplified(submodule.SubmoduleAdd.Read(targetSubmodule))
			targetSmul := a.Simplified(submodule.SubmoduleSmul.Read(targetSubmodule))
			inside := a.Have(
				"the preimage lies in the source carrier",
				"pullback ⊆ F.carrier",
				BySets(pullbackDef))
			zero := a.Have(
				"the preimage contains source zero",
				"F.zero ∈ pullback",
				BySets(pullbackDef, sourceZero, targetZero, ring_homomorphism.MapZero.Read(hom)))
			sums := a.Have(
				"the preimage is closed under sums",
				"∀u v:A. u ∈ pullback ∧ v ∈ pullback ⇒ F.add(u, v) ∈ pullback",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					v := b.FixAs[A]("v")
					inPreimage := b.Assume()
					b.Show(
						"the sum and its image lie in the two submodules",
						BySets(
							pullbackDef,
							inPreimage,
							sourceAdd.At(u, v),
							targetAdd.At(b.TermAs[B]("ι(u)"), b.TermAs[B]("ι(v)")),
							add.At(u, v)))
				}))
			smul := a.Have(
				"the preimage is closed under scalar products",
				"∀c u:A. c ∈ k ∧ u ∈ pullback ⇒ F.mul(c, u) ∈ pullback",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[A]("u")
					inPreimage := b.Assume()
					b.Show(
						"the scalar product and its image lie in the two submodules",
						BySets(
							pullbackDef,
							inPreimage,
							scalarField,
							field.SubfieldSubset.At(f, k),
							sourceSmul.At(c, u),
							targetSmul.At(b.TermAs[B]("ι(c)"), b.TermAs[B]("ι(u)")),
							mul.At(c, u)))
				}))
			a.Show(
				"the preimage satisfies the submodule criterion",
				By(inside, zero, sums, smul, submodule.SubmoduleCriterion.Read(sourceModule).At(pullback)))
		})
		spanImage := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k S:set(A).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"subfield(F, k)", "S ⊆ F.carrier",
			},
			Conclusion: "image(ι, " +
				"    module_span(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), S)) = " +
				"module_span(restrict_ring(field_ring(G), image(ι, k)), " +
				"    regular_module(field_ring(G)), " +
				"    image(ι, S))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k, S *Expr[Set[A]],
			hom, scalarField, generatorsInside Fact,
		) {
			P, pDef := a.LetAs[Set[A]](
				"P", "module_span(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), S)")
			Q, qDef := a.LetAs[Set[B]](
				"Q",
				"module_span(restrict_ring(field_ring(G), image(ι, k)), "+
					"    regular_module(field_ring(G)), "+
					"    image(ι, S))")
			pullback, pullbackDef := a.LetAs[Set[A]]("pullback", "{x:A | x ∈ F.carrier ∧ ι(x) ∈ Q}")
			f := a.TermAs[FieldOps[A]]("F")
			g := a.TermAs[FieldOps[B]]("G")
			fr := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(F), k)")
			fv := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(F))")
			gr := a.TermAs[module_record.RingOps[B]]("restrict_ring(field_ring(G), image(ι, k))")
			gv := a.TermAs[module_record.ModuleOps[B, B]]("regular_module(field_ring(G))")
			imageScalars := a.Have(
				"the image scalars form a subfield",
				"subfield(G, image(ι, k))",
				By(F, G, hom, scalarField, FieldEmbeddingSubfieldsAdjoin.At(f, g, ι)))
			sourceModule := a.Have(
				"the source field is a module over k",
				"module_on(restrict_ring(field_ring(F), k), regular_module(field_ring(F)))",
				By(F, scalarField, At(ambientModule, f, k)))
			targetModule := a.Have(
				"the target field is a module over the image scalars",
				"module_on(restrict_ring(field_ring(G), image(ι, k)), regular_module(field_ring(G)))",
				By(G, imageScalars, At(ambientModule, g, a.TermAs[Set[B]]("image(ι, k)"))))
			pModule := a.Have(
				"the source span is a submodule",
				"submodule(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), P)",
				By(Normalized, sourceModule, generatorsInside, pDef, submodule.SpanSubmodule.At(fr, fv, S)))
			imageP := a.Have(
				"its image is a target submodule",
				"submodule(restrict_ring(field_ring(G), image(ι, k)), regular_module(field_ring(G)), image(ι, P))",
				By(F, G, hom, scalarField, pModule, At(imageSubmodule, f, g, ι, k, P)))
			sInP := a.Have(
				"the source generators lie in their span",
				"S ⊆ P",
				By(Normalized, pDef, submodule.SubsetSpan.At(fr, fv, S)))
			qInImageP := a.Have(
				"the source image, a submodule holding the image generators, holds the target span",
				"Q ⊆ image(ι, P)",
				By(
					Normalized,
					qDef,
					imageP,
					sInP,
					set_image.ImageSubset.At(ι, S, P),
					submodule.SpanLeast.At(gr, gv, a.TermAs[Set[B]]("image(ι, S)"), a.TermAs[Set[B]]("image(ι, P)"))))
			imageS := a.Have(
				"the image generators lie in the target carrier",
				"image(ι, S) ⊆ G.carrier",
				BySets(generatorsInside, ring_homomorphism.MapIn.Read(hom)))
			qModule := a.Have(
				"the target span is a submodule",
				"submodule(restrict_ring(field_ring(G), image(ι, k)), regular_module(field_ring(G)), Q)",
				By(
					Normalized,
					targetModule,
					qDef,
					imageS,
					submodule.SpanSubmodule.At(gr, gv, a.TermAs[Set[B]]("image(ι, S)"))))
			backModule := a.Have(
				"its preimage is a source submodule",
				"submodule(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), pullback)",
				By(F, G, hom, scalarField, qModule, pullbackDef, At(preimageSubmodule, f, g, ι, k, Q)))
			imageSInQ := a.Have(
				"the target span contains the image generators",
				"image(ι, S) ⊆ Q",
				By(Normalized, qDef, submodule.SubsetSpan.At(gr, gv, a.TermAs[Set[B]]("image(ι, S)"))))
			sInBack := a.Have(
				"the preimage contains the source generators",
				"S ⊆ pullback",
				BySets(generatorsInside, imageSInQ, pullbackDef))
			pInBack := a.Have(
				"the source span lies in the preimage",
				"P ⊆ pullback",
				By(Normalized, pDef, backModule, sInBack, submodule.SpanLeast.At(fr, fv, S, pullback)))
			imagePInQ := a.Have(
				"the source image lies in the target span",
				"image(ι, P) ⊆ Q",
				BySets(pInBack, pullbackDef))
			a.Show(
				"the spans correspond under the embedding",
				BySets(qInImageP, imagePInQ))
		})
		independentInsert := ctx.Lemma(Statement{
			Binders:    "∀M:field_on(A). ∀k S:set(A). ∀v:A.",
			Hypotheses: []string{"subfield(M, k)", "S ⊆ M.carrier", "v ∈ M.carrier", "v ∉ S"},
			Conclusion: "module_independent(restrict_ring(field_ring(M), k), " +
				"    regular_module(field_ring(M)), " +
				"    insert(v, S)) ⇔ " +
				"module_independent(restrict_ring(field_ring(M), k), regular_module(field_ring(M)), S) ∧ " +
				"v ∉ module_span(restrict_ring(field_ring(M), k), regular_module(field_ring(M)), S)",
		}, func(
			a *Argument,
			M field.FieldFact[on.M],
			k, S *Expr[Set[A]],
			v *Member[A, on.M],
			scalarField, inside, fresh Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			vectors := a.Have(
				"the ambient field is a module over k",
				"module_on(restrict_ring(field_ring(M), k), regular_module(field_ring(M)))",
				By(M, scalarField, At(ambientModule, m, k)))
			a.Show(
				"inserting a fresh vector preserves independence exactly outside the span",
				By(
					scalarField,
					inside,
					v,
					fresh,
					field.SubfieldRingSubfield.Read(M).At(k, k),
					linear_independence.IndependentInsertIff.Read(vectors).AsFact().At(
						a.TermAs[Fun[A, A]]("M.inv"), S, v)))
		})
		finiteIndependent := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k E:set(A).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"subfield(F, k)",
				"finite(E)",
				"E ⊆ F.carrier",
				"module_independent(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), E)",
			},
			Conclusion: "module_independent(restrict_ring(field_ring(G), image(ι, k)), " +
				"    regular_module(field_ring(G)), " +
				"    image(ι, E))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k, E *Expr[Set[A]],
			hom, scalarField, finiteE, eInside, independentE Fact,
		) {
			P, pDef := a.LetAs[Set[Set[A]]](
				"P",
				"λS:set(A). "+
					"    S ⊆ F.carrier ∧ "+
					"    module_independent(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), S) ⇒ "+
					"    module_independent(restrict_ring(field_ring(G), image(ι, k)), "+
					"        regular_module(field_ring(G)), "+
					"        image(ι, S))")
			f := a.TermAs[FieldOps[A]]("F")
			g := a.TermAs[FieldOps[B]]("G")
			fr := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(F), k)")
			fv := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(F))")
			gr := a.TermAs[module_record.RingOps[B]]("restrict_ring(field_ring(G), image(ι, k))")
			gv := a.TermAs[module_record.ModuleOps[B, B]]("regular_module(field_ring(G))")
			injective := a.Have(
				"the embedding is one-to-one",
				"injective_on(F.carrier, ι)",
				By(F, G, hom, FieldEmbeddingSubfieldsAdjoin.At(f, g, ι)))
			imageScalars := a.Have(
				"the image scalars form a subfield",
				"subfield(G, image(ι, k))",
				By(F, G, hom, scalarField, FieldEmbeddingSubfieldsAdjoin.At(f, g, ι)))
			empty := a.Have(
				"the empty set has independent image",
				"P(∅)",
				By(
					Normalized,
					pDef,
					linear_independence.IndependentEmpty.At(gr, gv),
					At(set_image.ImageClauses, ι)))
			step := a.Have(
				"a fresh independent vector has independent image",
				"∀x:A. ∀S:set(A). P(S) ∧ x ∉ S ∧ finite(S) ⇒ P(insert(x, S))",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					S := b.FixAs[Set[A]]("S")
					ih := b.Conjuncts(
						b.Assume(),
						"the image of S is independent when S is",
						"x lies outside S",
						"S is finite")
					hypothesis, outside := ih[0], ih[1]
					b.Do(Simp(Fwd(pDef)))
					inserted := b.Assume()
					bounds := b.Have(
						"the fresh vector and the old set lie in the source carrier",
						"S ⊆ F.carrier ∧ x ∈ F.carrier",
						BySets(inserted))
					sourceParts := b.Have(
						"the old set is independent and the fresh vector lies outside its span",
						"module_independent(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), S) ∧ "+
							"x ∉ module_span(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), S)",
						By(F, scalarField, inserted, outside, bounds, At(independentInsert, f, k, S, x)))
					induction := b.Simplified(hypothesis, Fwd(pDef))
					targetIndependent := b.Have(
						"the old image set is independent",
						"module_independent(restrict_ring(field_ring(G), image(ι, k)), "+
							"    regular_module(field_ring(G)), "+
							"    image(ι, S))",
						By(induction, bounds, sourceParts))
					spans := b.Have(
						"the old spans correspond under the embedding",
						"image(ι, module_span(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), S)) = "+
							"module_span(restrict_ring(field_ring(G), image(ι, k)), "+
							"    regular_module(field_ring(G)), "+
							"    image(ι, S))",
						By(F, G, hom, scalarField, bounds, At(spanImage, f, g, ι, k, S)))
					sourceModule := b.Have(
						"the source field is a module over k",
						"module_on(restrict_ring(field_ring(F), k), regular_module(field_ring(F)))",
						By(F, scalarField, At(ambientModule, f, k)))
					spanSubmodule := b.Have(
						"the old source span is a submodule",
						"submodule(restrict_ring(field_ring(F), k), "+
							"    regular_module(field_ring(F)), "+
							"    module_span(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), S))",
						By(sourceModule, bounds, submodule.SpanSubmodule.At(fr, fv, S)))
					spanInside := b.Simplified(submodule.SubmoduleSubset.Read(spanSubmodule))
					outsideSpan := b.Have(
						"the fresh image lies outside the old image span",
						"ι(x) ∉ "+
							"module_span(restrict_ring(field_ring(G), image(ι, k)), "+
							"    regular_module(field_ring(G)), "+
							"    image(ι, S))",
						BySets(
							injective,
							spans,
							bounds,
							spanInside,
							sourceParts,
							functions.InjectiveOnDef.At(b.TermAs[Set[A]]("F.carrier"), ι)))
					fresh := b.Have(
						"the fresh image is absent from the old image set",
						"ι(x) ∉ image(ι, S)",
						BySets(injective, bounds, outside, functions.InjectiveOnDef.At(b.TermAs[Set[A]]("F.carrier"), ι)))
					targetBounds := b.Have(
						"the image set and fresh image lie in the target carrier",
						"image(ι, S) ⊆ G.carrier ∧ ι(x) ∈ G.carrier",
						BySets(ring_homomorphism.MapIn.Read(hom), bounds))
					targetInserted := b.Have(
						"inserting the fresh image preserves independence",
						"module_independent(restrict_ring(field_ring(G), image(ι, k)), "+
							"    regular_module(field_ring(G)), "+
							"    insert(ι(x), image(ι, S)))",
						By(
							G,
							imageScalars,
							targetBounds,
							fresh,
							outsideSpan,
							targetIndependent,
							At(
								independentInsert,
								g,
								b.TermAs[Set[B]]("image(ι, k)"),
								b.TermAs[Set[B]]("image(ι, S)"),
								b.TermAs[B]("ι(x)"))))
					b.Show(
						"the image of the enlarged set is independent",
						By(Normalized, targetInserted, set_image.ImageClauses.At(ι, x, S)))
				}))
			allFinite := a.Have(
				"fresh-element induction applies to E",
				"P(E)",
				By(empty, step, finiteE, finite_set.FiniteInductFresh.At(P, E)))
			a.Show(
				"the finite independent set has independent image",
				By(Normalized, allFinite, pDef, eInside, independentE))
		})
		finiteBasis := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k K E:set(A).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"subfield(F, k)", "subfield(F, K)", "k ⊆ K", "finite(E)",
				"module_basis(restrict_ring(field_ring(F), k), " +
					"    restrict_module(regular_module(field_ring(F)), K), " +
					"    E)",
			},
			Conclusion: "finite(image(ι, E)) ∧ " +
				"module_basis(restrict_ring(field_ring(G), image(ι, k)), " +
				"    restrict_module(regular_module(field_ring(G)), image(ι, K)), " +
				"    image(ι, E)) ∧ " +
				"card(image(ι, E)) = card(E)",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k, K, E *Expr[Set[A]],
			hom, scalarField, upperField, nested, finiteE, basisE Fact,
		) {
			f := a.TermAs[FieldOps[A]]("F")
			g := a.TermAs[FieldOps[B]]("G")
			fr := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(F), k)")
			vk := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(regular_module(field_ring(F)), K)")
			sourceModule := a.Have(
				"the source field is a module over k",
				"module_on(restrict_ring(field_ring(F), k), regular_module(field_ring(F)))",
				By(F, scalarField, At(ambientModule, f, k)))
			upperModule := a.Have(
				"the upper subfield is a source submodule",
				"submodule(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), K)",
				By(F, scalarField, upperField, nested, At(subfieldModule, f, k, K)))
			sourceBasis := a.Have(
				"the basis is independent and spans K in the ambient module",
				"module_independent(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), E) ∧ "+
					"module_span(restrict_ring(field_ring(F), k), regular_module(field_ring(F)), E) = K",
				By(upperModule, basisE, linear_independence.BasisRestrict.Read(sourceModule).At(K, E)))
			eInF := a.Have(
				"the basis lies in the source carrier",
				"E ⊆ F.carrier",
				BySets(
					basisE,
					linear_independence.BasisInCarrier.At(fr, vk, E),
					upperField,
					field.SubfieldSubset.At(f, K)))
			targetIndependent := a.Have(
				"the image basis is independent",
				"module_independent(restrict_ring(field_ring(G), image(ι, k)), "+
					"    regular_module(field_ring(G)), "+
					"    image(ι, E))",
				By(F, G, hom, scalarField, finiteE, sourceBasis, eInF, At(finiteIndependent, f, g, ι, k, E)))
			targetSpan := a.Have(
				"the image basis spans the image upper field",
				"module_span(restrict_ring(field_ring(G), image(ι, k)), "+
					"    regular_module(field_ring(G)), "+
					"    image(ι, E)) = "+
					"image(ι, K)",
				By(F, G, hom, scalarField, sourceBasis, eInF, At(spanImage, f, g, ι, k, E)))
			imageScalars := a.Have(
				"the image scalars form a subfield",
				"subfield(G, image(ι, k))",
				By(F, G, hom, scalarField, FieldEmbeddingSubfieldsAdjoin.At(f, g, ι)))
			targetModule := a.Have(
				"the target field is a module over the image scalars",
				"module_on(restrict_ring(field_ring(G), image(ι, k)), regular_module(field_ring(G)))",
				By(G, imageScalars, At(ambientModule, g, a.TermAs[Set[B]]("image(ι, k)"))))
			imageUpperModule := a.Have(
				"the image upper field is a target submodule",
				"submodule(restrict_ring(field_ring(G), image(ι, k)), regular_module(field_ring(G)), image(ι, K))",
				By(F, G, hom, scalarField, upperModule, At(imageSubmodule, f, g, ι, k, K)))
			targetBasis := a.Have(
				"the image is a basis of the image upper field",
				"module_basis(restrict_ring(field_ring(G), image(ι, k)), "+
					"    restrict_module(regular_module(field_ring(G)), image(ι, K)), "+
					"    image(ι, E))",
				By(
					imageUpperModule,
					targetIndependent,
					targetSpan,
					linear_independence.BasisRestrict.Read(targetModule).At(
						a.TermAs[Set[B]]("image(ι, K)"), a.TermAs[Set[B]]("image(ι, E)"))))
			injective := a.Have(
				"the embedding is one-to-one",
				"injective_on(F.carrier, ι)",
				By(F, G, hom, FieldEmbeddingSubfieldsAdjoin.At(f, g, ι)))
			injE := a.Have(
				"the embedding is one-to-one on the basis",
				"injective_on(E, ι)",
				BySets(
					injective,
					eInF,
					functions.InjectiveOnDef.At(a.TermAs[Set[A]]("F.carrier"), ι),
					functions.InjectiveOnDef.At(E, ι)))
			size := a.Have(
				"the basis cardinality is preserved",
				"card(image(ι, E)) = card(E)",
				By(finiteE, injE, cardinality.CardImageInj.At(ι, E)))
			a.Show(
				"the image is a finite basis of the same size",
				By(finiteE, finite_set.FiniteImage.At(ι, E), targetBasis, size))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k, K *Expr[Set[A]],
			hom, scalarField, upperField, nested, finiteExtension Fact,
		) {
			f := a.TermAs[FieldOps[A]]("F")
			g := a.TermAs[FieldOps[B]]("G")
			fr := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(F), k)")
			vk := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(regular_module(field_ring(F)), K)")
			E, basis := a.ObtainAs[Set[A]](
				"choose a finite basis of the extension",
				"∃E:set(A). "+
					"    finite(E) ∧ "+
					"    module_basis(restrict_ring(field_ring(F), k), "+
					"        restrict_module(regular_module(field_ring(F)), K), "+
					"        E)",
				By(
					finiteExtension,
					field_extension.FiniteExtensionDef.At(f, k, K),
					module_dimension.FiniteDimensionalDef.At(fr, vk)),
				Named("E"))
			imageBasis := a.Have(
				"its image is a finite basis of the same size",
				"finite(image(ι, E)) ∧ "+
					"module_basis(restrict_ring(field_ring(G), image(ι, k)), "+
					"    restrict_module(regular_module(field_ring(G)), image(ι, K)), "+
					"    image(ι, E)) ∧ "+
					"card(image(ι, E)) = card(E)",
				By(F, G, hom, scalarField, upperField, nested, basis, At(finiteBasis, f, g, ι, k, K, E)))
			sourceDegree := a.Have(
				"the source degree is the source basis cardinality",
				"extension_degree(F, k, K) = card(E)",
				By(scalarField, upperField, nested, basis, field_extension.BasisDegree.Read(F).At(k, K, E)))
			imageFields := a.Have(
				"both image fields are subfields of the target",
				"subfield(G, image(ι, k)) ∧ subfield(G, image(ι, K))",
				By(F, G, hom, scalarField, upperField, FieldEmbeddingSubfieldsAdjoin.At(f, g, ι)))
			targetDegree := a.Have(
				"the target extension is finite with the image basis cardinality",
				"finite_extension(G, image(ι, k), image(ι, K)) ∧ "+
					"extension_degree(G, image(ι, k), image(ι, K)) = card(image(ι, E))",
				By(
					imageFields,
					nested,
					set_image.ImageSubset.At(ι, k, K),
					imageBasis,
					field_extension.BasisDegree.Read(G).At(
						a.TermAs[Set[B]]("image(ι, k)"), a.TermAs[Set[B]]("image(ι, K)"), a.TermAs[Set[B]]("image(ι, E)"))))
			a.Show(
				"the extension remains finite and its degree is preserved",
				By(imageBasis, sourceDegree, targetDegree))
		})
	}),
})}

// FieldEmbeddingPolynomials — a field embedding carries polynomial
// coefficients over a subfield to the image subfield, preserving degree,
// products, evaluation and derivatives. Finite support bounds the degree
// and one-to-one-ness keeps it.
var FieldEmbeddingPolynomials = fieldEmbeddingPolynomialsThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingPolynomials",
	Key:  "prop_5205434170c72588",
	Build: family.Sections(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"subfield(F, k)",
			"polynomial_over(k, p)",
		},
		Conclusion: "polynomial_over(image(ι, k), λi:num. ι(p(i))) ∧ " +
			"polynomial_degree(λi:num. ι(p(i))) = polynomial_degree(p) ∧ " +
			"((λi:num. ι(p(i))) = vec_zero(G.zero) ⇔ p = vec_zero(F.zero)) ∧ " +
			"(∀q:(num → A). " +
			"    polynomial_over(k, q) ⇒ " +
			"    (λi:num. ι(polynomial_mul(p, q, i))) = polynomial_mul(λi:num. ι(p(i)), λi:num. ι(q(i)))) ∧ " +
			"(∀x:A. x ∈ F.carrier ⇒ ι(polynomial_eval(p, x)) = polynomial_eval(λi:num. ι(p(i)), ι(x))) ∧ " +
			"(λi:num. ι(polynomial_derivative(p, i))) = polynomial_derivative(λi:num. ι(p(i)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		supportDegree := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀ι:(A → B). ∀k:set(A). ∀p:(num → A).",
			Hypotheses: []string{"ring_homomorphism(R, S, ι)", "k ⊆ R.carrier", "polynomial_over(k, p)"},
			Conclusion: "polynomial_over(image(ι, k), λi:num. ι(p(i))) ∧ " +
				"(injective_on(R.carrier, ι) ⇒ polynomial_degree(λi:num. ι(p(i))) = polynomial_degree(p))",
		}, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			S comm_ring.CommRingFact[on.S],
			ι *Arrow[A, B],
			k *Expr[Set[A]],
			p *Arrow[Nat, A],
			hom, inside, over Fact,
		) {
			q, qDef := a.LetAs[Fun[Nat, B]]("q", "λi:num. ι(p(i))")
			zero := a.Have(
				"zero is preserved",
				"ι(R.zero) = S.zero",
				By(ring_homomorphism.MapZero.Read(hom)))
			coefficients := a.Have(
				"the image coefficients belong to the image subring",
				"∀i:num. p(i) ∈ k ∧ p(i) ∈ R.carrier ∧ q(i) ∈ image(ι, k)",
				BySets(qDef, inside, over, polynomial.PolynomialOverDef.At(a.TermAs[A]("R.zero"), k, p)))
			forward := a.Have(
				"mapping coefficients preserves every support bound",
				"∀n:num. vec⟨n⟩(p) ⇒ vec⟨n⟩(q)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					bound := b.Assume()
					b.Show(
						"coefficients beyond the bound map to zero",
						By(
							zero,
							qDef,
							bound,
							vec_space.VecDef.At(b.TermAs[A]("R.zero"), b.VecAt[A](n, "p")),
							vec_space.VecDef.At(b.TermAs[B]("S.zero"), b.VecAt[B](n, "q"))))
				}))
			mappedOver := a.Have(
				"the mapped polynomial has finite support and the required coefficients",
				"polynomial_over(image(ι, k), q)",
				By(
					Normalized,
					forward,
					coefficients,
					over,
					polynomial.PolynomialOverDef.At(a.TermAs[A]("R.zero"), k, p),
					polynomial.PolynomialOverDef.At(a.TermAs[B]("S.zero"), a.TermAs[Set[B]]("image(ι, k)"), q)))
			degree := a.Have(
				"injectivity preserves the least support bound",
				"injective_on(R.carrier, ι) ⇒ polynomial_degree(q) = polynomial_degree(p)",
				Derive(func(b *Argument) {
					injective := b.Assume()
					backward := b.Have(
						"a mapped zero coefficient was already zero",
						"∀n:num. vec⟨n⟩(q) ⇒ vec⟨n⟩(p)",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							bound := c.Assume()
							c.Show(
								"injectivity reflects vanishing beyond the bound",
								By(
									coefficients,
									zero,
									qDef,
									injective,
									bound,
									comm_ring.ZeroIn.Read(R),
									vec_space.VecDef.At(c.TermAs[B]("S.zero"), c.VecAt[B](n, "q")),
									vec_space.VecDef.At(c.TermAs[A]("R.zero"), c.VecAt[A](n, "p")),
									functions.InjectiveOnDef.At(c.TermAs[Set[A]]("R.carrier"), ι)))
						}))
					bounds := b.Have(
						"the two degrees bound each other",
						"polynomial_degree(q) ≤ polynomial_degree(p) ∧ polynomial_degree(p) ≤ polynomial_degree(q)",
						By(
							forward.At(b.TermAs[Nat]("suc(polynomial_degree(p))")),
							backward.At(b.TermAs[Nat]("suc(polynomial_degree(q))")),
							over,
							mappedOver,
							polynomial.DegreeVec.At(b.TermAs[A]("R.zero"), k, p),
							polynomial.DegreeVec.At(b.TermAs[B]("S.zero"), b.TermAs[Set[B]]("image(ι, k)"), q),
							polynomial.DegreeLeast.At(b.TermAs[B]("S.zero"), q, b.TermAs[Nat]("polynomial_degree(p)")),
							polynomial.DegreeLeast.At(b.TermAs[A]("R.zero"), p, b.TermAs[Nat]("polynomial_degree(q)"))))
					b.Show(
						"the degrees agree",
						ByArith(bounds))
				}))
			a.Show(
				"support and degree give the coefficient image statement",
				By(degree, mappedOver))
		})

		zeroPolynomial := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀ι:(A → B). ∀p:(num → A).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, ι)",
				"injective_on(R.carrier, ι)",
				"polynomial_over(R.carrier, p)",
			},
			Conclusion: "(λi:num. ι(p(i))) = vec_zero(S.zero) ⇔ p = vec_zero(R.zero)",
		}, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			S comm_ring.CommRingFact[on.S],
			ι *Arrow[A, B],
			p *Arrow[Nat, A],
			hom, injective, over Fact,
		) {
			a.Show(
				"injectivity reflects the zero polynomial",
				By(
					Broadcast,
					Normalized,
					injective,
					over,
					ring_homomorphism.MapZero.Read(hom),
					comm_ring.ZeroIn.Read(R),
					polynomial.PolynomialOverDef.At(a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier"), p),
					functions.InjectiveOnDef.At(a.TermAs[Set[A]]("R.carrier"), ι),
					vec_space.VecZeroDef.Inst[A]().At(a.TermAs[A]("R.zero")),
					vec_space.VecZeroDef.Inst[B]().At(a.TermAs[B]("S.zero"))))
		})

		return ctx.Theorem(headline,
			func(
				a *Argument,
				F field.FieldFact[on.F],
				G field.FieldFact[on.G],
				ι *Arrow[A, B],
				k *Expr[Set[A]],
				p *Arrow[Nat, A],
				hom, sourceField, pOver Fact,
			) {
				fRecord := a.TermAs[FieldOps[A]]("F")
				gRecord := a.TermAs[FieldOps[B]]("G")
				fRing := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
				gRing := a.TermAs[module_record.RingOps[B]]("field_ring(G)")
				imageK := a.TermAs[Set[B]]("image(ι, k)")
				targetField := a.Have(
					"the scalar subfield maps to a target subfield",
					"subfield(G, image(ι, k))",
					By(F, G, hom, sourceField, FieldEmbeddingSubfieldsAdjoin.At(fRecord, gRecord, ι)))
				injective := a.Have(
					"the embedding is one-to-one",
					"injective_on(F.carrier, ι)",
					By(F, G, hom, FieldEmbeddingSubfieldsAdjoin.At(fRecord, gRecord, ι)))
				subrings := a.Have(
					"the scalar fields are subrings of the ambient rings",
					"k ⊆ F.carrier ∧ subring(field_ring(F), k) ∧ subring(field_ring(G), image(ι, k))",
					By(
						sourceField,
						targetField,
						field.SubfieldSubset.At(fRecord, k),
						field.SubfieldSubring.Read(F).At(k),
						field.SubfieldSubring.Read(G).At(imageK)))
				ambientOver := a.Have(
					"the source coefficients belong to the ambient field",
					"polynomial_over(F.carrier, p)",
					By(
						subrings,
						pOver,
						polynomial.PolynomialOverMono.At(a.TermAs[A]("F.zero"), k, a.TermAs[Set[A]]("F.carrier"), p)))
				mappedSupport := a.Have(
					"mapping coefficients preserves the coefficient field and degree",
					"polynomial_over(image(ι, k), λi:num. ι(p(i))) ∧ "+
						"polynomial_degree(λi:num. ι(p(i))) = polynomial_degree(p)",
					By(
						subrings,
						pOver,
						hom,
						injective,
						field.RingOn.Read(F),
						field.RingOn.Read(G),
						At(supportDegree, fRing, gRing, ι, k, p)))
				zeroDerivative := a.Have(
					"zero and the formal derivative are preserved",
					"((λi:num. ι(p(i))) = vec_zero(G.zero) ⇔ p = vec_zero(F.zero)) ∧ "+
						"(λi:num. ι(polynomial_derivative(p, i))) = polynomial_derivative(λi:num. ι(p(i)))",
					By(
						hom,
						injective,
						ambientOver,
						field.RingOn.Read(F),
						field.RingOn.Read(G),
						At(zeroPolynomial, fRing, gRing, ι, p),
						polynomial_evaluation.CoefficientMapDerivative.At(fRing, gRing, ι, p)))
				products := a.Have(
					"the coefficient map preserves multiplication by every polynomial over k",
					Statement{Binders: "∀q:(num → A).", Hypotheses: []string{"polynomial_over(k, q)"},
						Conclusion: "(λi:num. ι(polynomial_mul(p, q, i))) = " +
							"polynomial_mul(λi:num. ι(p(i)), λi:num. ι(q(i)))"},
					Derive(func(b *Argument) {
						q := b.FixAs[Fun[Nat, A]]("q")
						qOver := b.Assume()
						coefficients := b.Have(
							"the coefficients of p and of q lie in the source field",
							"∀n:num. p(n) ∈ F.carrier ∧ q(n) ∈ F.carrier",
							By(
								subrings,
								qOver,
								ambientOver,
								polynomial.PolynomialOverMono.At(b.TermAs[A]("F.zero"), k, b.TermAs[Set[A]]("F.carrier"), q),
								polynomial.PolynomialOverDef))
						b.Show(
							"the convolution formula is preserved",
							By(
								hom,
								coefficients,
								field.RingOn.Read(F),
								field.RingOn.Read(G),
								polynomial.ConvolutionRingMap.At(fRing, gRing, ι, p, q)))
					}))
				evaluation := a.Have(
					"evaluation commutes with the embedding at every source point",
					"∀x:A. x ∈ F.carrier ⇒ ι(polynomial_eval(p, x)) = polynomial_eval(λi:num. ι(p(i)), ι(x))",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						inSource := b.Assume()
						b.Show(
							"apply evaluation along the ambient homomorphism",
							By(
								inSource,
								hom,
								ambientOver,
								polynomial_evaluation.EvalAlongHomomorphism.At(fRing, gRing, ι, p, x)))
					}))
				a.Show(
					"the coefficient embedding preserves all the stated polynomial data",
					By(mappedSupport, zeroDerivative, products, evaluation))
			})
	}),
})}

// FieldEmbeddingIrreducible — an embedding carries an irreducible polynomial
// over a subfield to an irreducible polynomial over its image: pull a proposed
// factorization back through the isomorphism of the two scalar fields.
var FieldEmbeddingIrreducible = fieldEmbeddingIrreducibleThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingIrreducible",
	Key:  "prop_a0b953c204886b39",
	Build: family.Sections(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"subfield(F, k)",
			"polynomial_irreducible(«sourceScalars», p)",
		},
		Conclusion: "polynomial_irreducible(«imageScalars», «mapped»)",
		Abbrev: Abbrev{
			{Name: "sourceScalars", Text: "restrict_ring(field_ring(F), k)"},
			{Name: "imageScalars", Text: "restrict_ring(field_ring(G), image(ι, k))"},
			{Name: "imageField", Text: "restrict_field(G, image(ι, k))"},
			{Name: "sourceRestrictionRing", Text: "field_ring(restrict_field(F, k))"},
			{Name: "mapped", Text: "λj:num. ι(p(j))"},
			{Name: "pullback", Text: "λq:(num → B). λj:num. inverse_on(k, ι, q(j))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		inverse := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k:set(A).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"subfield(F, k)",
			},
			Conclusion: "field_on(restrict_field(F, k)) ∧ " +
				"field_on(«imageField») ∧ " +
				"ring_homomorphism(field_ring(«imageField»), «sourceRestrictionRing», inverse_on(k, ι)) ∧ " +
				"injective_on(k, ι)",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k *Expr[Set[A]],
			hom, sub Fact,
		) {
			fRecord := a.TermAs[FieldOps[A]]("F")
			gRecord := a.TermAs[FieldOps[B]]("G")
			imageK := a.TermAs[Set[B]]("image(ι, k)")
			sourceRing := a.TermAs[RingOps[A]]("«sourceScalars»")
			imageRing := a.TermAs[RingOps[B]]("«imageScalars»")
			gRing := a.TermAs[RingOps[B]]("field_ring(G)")
			back := a.TermAs[Fun[B, A]]("inverse_on(k, ι)")
			restricted := a.Have(
				"the embedding restricts to the source subfield",
				"ring_homomorphism(«sourceScalars», field_ring(G), ι)",
				By(F, hom, sub, field.SubfieldSubring.Read(F).At(k), ring_homomorphism.RingHomRestrictSource))
			image := a.Have(
				"the restriction is injective and its image is a subfield",
				"subfield(G, image(ι, k)) ∧ injective_on(k, ι)",
				By(F, G, sub, restricted, ring_homomorphism.SubfieldHomomorphismEmbedding))
			parts := a.Conjuncts(
				image,
				"the image is a subfield",
				"the map is injective on k")
			isomorphism := a.Have(
				"the source subfield is isomorphic to its image",
				"ring_isomorphism(«sourceScalars», «imageScalars», ι)",
				Derive(func(b *Argument) {
					b.Do(Unfold(ring_homomorphism.RingIsomorphismDef))
					b.Show(
						"the restricted map has exactly the image carrier",
						BySets(
							G,
							parts[1],
							parts[0],
							restricted,
							field.SubfieldSubring.Read(G).At(imageK),
							ring_homomorphism.RingHomCorestrict.At(sourceRing, gRing, ι, imageK),
							set_image.FunInImage))
				}))
			a.Show(
				"the inverse is a homomorphism of the restricted fields",
				By(
					F,
					G,
					sub,
					image,
					isomorphism,
					field.SubfieldFieldOn.Read(F).At(k),
					field.SubfieldFieldOn.Read(G).At(imageK),
					ring_homomorphism.IsomorphismInverse.At(sourceRing, imageRing, ι),
					ring_homomorphism.RingIsomorphismDef.At(imageRing, sourceRing, back),
					field.RestrictFieldRing.At(fRecord, k),
					field.RestrictFieldRing.At(gRecord, imageK)))
		})

		pullPolynomials := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀q:(num → B).",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
				"subfield(F, k)",
				"polynomial_over(image(ι, k), q)",
			},
			Conclusion: "polynomial_over(k, «pullback»(q)) ∧ " +
				"polynomial_degree(«pullback»(q)) = polynomial_degree(q) ∧ " +
				"(∀r:(num → B). " +
				"    polynomial_over(image(ι, k), r) ⇒ " +
				"    «pullback»(polynomial_mul(q, r)) = polynomial_mul(«pullback»(q), «pullback»(r)))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			k *Expr[Set[A]],
			q *Arrow[Nat, B],
			hom, sub, over Fact,
		) {
			fRecord := a.TermAs[FieldOps[A]]("F")
			gRecord := a.TermAs[FieldOps[B]]("G")
			imageK := a.TermAs[Set[B]]("image(ι, k)")
			back := a.TermAs[Fun[B, A]]("inverse_on(k, ι)")
			inverseFields := a.Have(
				"the inverse embedding joins the two scalar fields",
				"field_on(restrict_field(F, k)) ∧ "+
					"field_on(«imageField») ∧ "+
					"ring_homomorphism(field_ring(«imageField»), «sourceRestrictionRing», inverse_on(k, ι)) ∧ "+
					"injective_on(k, ι)",
				By(F, G, hom, sub, At(inverse, fRecord, gRecord, ι, k)))
			// The inverse and coefficient laws are read at every point, here and in the
			// theorem below, so they are cited at a partial tuple, which the typed At
			// (full tuple only) cannot spell.
			scalarImage := a.Have(
				"the inverse maps the image scalar field onto k",
				"image(inverse_on(k, ι), image(ι, k)) = k",
				BySets(
					inverseFields,
					At(functions.InverseOnIn.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()), k, ι),
					At(functions.InverseOnLeft.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()), k, ι)))
			a.Show(
				"coefficient pullback preserves products and degree",
				By(
					scalarImage,
					inverseFields,
					over,
					field.CarrierSubfield.At(a.TermAs[FieldOps[B]]("«imageField»")),
					FieldEmbeddingPolynomials.At(
						a.TermAs[FieldOps[B]]("«imageField»"),
						a.TermAs[FieldOps[A]]("restrict_field(F, k)"), back, imageK, q),
					field.RestrictFieldDef))
		})

		return ctx.Theorem(headline,
			func(
				a *Argument,
				F field.FieldFact[on.F],
				G field.FieldFact[on.G],
				ι *Arrow[A, B],
				k *Expr[Set[A]],
				p *Arrow[Nat, A],
				hom, sub, irreducible Fact,
			) {
				fRecord := a.TermAs[FieldOps[A]]("F")
				gRecord := a.TermAs[FieldOps[B]]("G")
				parts := a.Conjuncts(
					a.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
					"p is a polynomial over k",
					"p has positive degree",
					"every factorization of p has a constant factor")
				over, positive, sourceFactors := parts[0], parts[1], parts[2]
				cancel := a.Have(
					"pulling back the embedded polynomial recovers p",
					"«pullback»(«mapped») = p",
					By(
						F,
						G,
						hom,
						sub,
						over,
						At(inverse, fRecord, gRecord, ι, k),
						At(polynomial.CoefficientIn.Inst[A](), a.TermAs[A]("F.zero"), k, p),
						At(functions.InverseOnLeft.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()), k, ι)))
				imageFactors := a.Have(
					"each image factorization has a constant factor",
					Statement{
						Binders: "∀q r:(num → B).",
						Hypotheses: []string{
							"polynomial_over(image(ι, k), q)",
							"polynomial_over(image(ι, k), r)",
							"«mapped» = polynomial_mul(q, r)",
						},
						Conclusion: "polynomial_degree(q) = 0 ∨ polynomial_degree(r) = 0",
					},
					Derive(func(b *Argument) {
						q := b.FixAs[Fun[Nat, B]]("q")
						r := b.FixAs[Fun[Nat, B]]("r")
						factorization := b.Assume()
						pulledFactors := b.Have(
							"the pulled factors multiply to p with the same degrees",
							"polynomial_over(k, «pullback»(q)) ∧ "+
								"polynomial_over(k, «pullback»(r)) ∧ "+
								"polynomial_degree(«pullback»(q)) = polynomial_degree(q) ∧ "+
								"polynomial_degree(«pullback»(r)) = polynomial_degree(r) ∧ "+
								"p = polynomial_mul(«pullback»(q), «pullback»(r))",
							By(
								cancel,
								F,
								G,
								hom,
								sub,
								factorization,
								At(pullPolynomials, fRecord, gRecord, ι, k, q),
								At(pullPolynomials, fRecord, gRecord, ι, k, r)))
						b.Show(
							"irreducibility of p forces an original factor to be constant",
							By(sourceFactors, pulledFactors))
					}))
				support := a.Have(
					"the image polynomial is over the image field and has positive degree",
					"polynomial_over(image(ι, k), «mapped») ∧ 0 < polynomial_degree(«mapped»)",
					By(
						Normalized,
						F,
						G,
						positive,
						sub,
						over,
						hom,
						FieldEmbeddingPolynomials.At(fRecord, gRecord, ι, k, p)))
				a.Show(
					"the coefficient image is irreducible over the image scalar field",
					By(
						imageFactors,
						support,
						polynomial_division.PolynomialIrreducibleDef.At(
							a.TermAs[RingOps[B]]("«imageScalars»"), a.TermAs[Fun[Nat, B]]("«mapped»"))))
			})
	}),
})}

// FieldEmbeddingMonic — a field embedding carries a monic polynomial over a
// set S of F to a monic polynomial over the image of S: ι sends zero to zero
// and the coefficients into image(ι, S), keeps the degree, and sends the
// leading one to one.
var FieldEmbeddingMonic = fieldEmbeddingMonicThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingMonic",
	Key:  "prop_5dfa448ab0afcf24",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀S:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"S ⊆ F.carrier",
			"polynomial_over(S, p)",
			"polynomial_monic(p)",
		},
		Conclusion: "polynomial_over(image(ι, S), λi:num. ι(p(i))) ∧ polynomial_monic(λi:num. ι(p(i)))",
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G field.FieldFact[on.G],
		ι *Arrow[A, B],
		S *Expr[Set[A]],
		p *Arrow[Nat, A],
		hom, sInCarrier, pOver, pMonic Fact,
	) {
		source := a.TermAs[FieldOps[A]]("F")
		target := a.TermAs[FieldOps[B]]("G")
		carrier := a.TermAs[Set[A]]("F.carrier")
		sourceZero := a.TermAs[A]("F.zero")
		sourceOne := a.TermAs[A]("F.one")
		targetZero := a.TermAs[B]("G.zero")
		targetOne := a.TermAs[B]("G.one")
		mapped := a.TermAs[Fun[Nat, B]]("λi:num. ι(p(i))")
		imageOver := a.Have(
			"ι sends zero to zero and the coefficients of p into the image of S",
			"polynomial_over(image(ι, S), λi:num. ι(p(i)))",
			By(
				pOver,
				ring_homomorphism.MapZero.Read(hom),
				set_image.FunInImage,
				polynomial.PolynomialOverMap.At(ι, sourceZero, targetZero, S, a.TermAs[Set[B]]("image(ι, S)"), p)))
		a.Show(
			"ι keeps the degree of p and sends its leading one to one",
			By(
				F,
				G,
				hom,
				sInCarrier,
				pOver,
				pMonic,
				imageOver,
				polynomial.PolynomialOverMono.At(sourceZero, S, carrier, p),
				field.CarrierSubfield.Read(F),
				FieldEmbeddingPolynomials.At(source, target, ι, carrier, p),
				polynomial.PolynomialMonicDef.At(targetZero, targetOne, mapped),
				polynomial.PolynomialMonicDef.At(sourceZero, sourceOne, p),
				ring_homomorphism.MapOne.Read(hom)))
	}),
})}

// FieldEmbeddingDivides — a field embedding carries a factor h of g over F
// to a factor of the image of g over G: the cofactor maps to a polynomial
// over G, and ι carries the product of h and the cofactor to the product of
// their images.
var FieldEmbeddingDivides = fieldEmbeddingDividesThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingDivides",
	Key:  "prop_2e9566e40582218e",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀g h:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"polynomial_over(F.carrier, h)",
			"polynomial_divides(field_ring(F), h, g)",
		},
		Conclusion: "polynomial_divides(field_ring(G), λi:num. ι(h(i)), λi:num. ι(g(i)))",
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G field.FieldFact[on.G],
		ι *Arrow[A, B],
		g, h *Arrow[Nat, A],
		hom, hOver, hDivides Fact,
	) {
		source := a.TermAs[FieldOps[A]]("F")
		target := a.TermAs[FieldOps[B]]("G")
		carrier := a.TermAs[Set[A]]("F.carrier")
		sourceZero := a.TermAs[A]("F.zero")
		targetZero := a.TermAs[B]("G.zero")
		w, cofactor := a.UnpackAs[Fun[Nat, A]](
			a.Unfolded(hDivides, polynomial_division.PolynomialDividesDef), "w")
		cofactorParts := a.Conjuncts(
			cofactor,
			"the cofactor is a polynomial over F",
			"g is h times the cofactor")
		wOver, product := cofactorParts[0], cofactorParts[1]
		wImage := a.Have(
			"the cofactor maps to a polynomial over G",
			"polynomial_over(G.carrier, λi:num. ι(w(i)))",
			By(
				wOver,
				ring_homomorphism.MapZero.Read(hom),
				ring_homomorphism.MapIn.Read(hom),
				polynomial.PolynomialOverMap.At(
					ι, sourceZero, targetZero, carrier, a.TermAs[Set[B]]("G.carrier"), w)))
		productImage := a.Have(
			"ι carries the product to the product of the images",
			"(λi:num. ι(g(i))) = polynomial_mul(λi:num. ι(h(i)), λi:num. ι(w(i)))",
			Simp(Fwd(product)),
			By(
				F,
				G,
				hom,
				field.CarrierSubfield.Read(F),
				hOver,
				wOver,
				FieldEmbeddingPolynomials.At(source, target, ι, carrier, h)))
		a.Show(
			"so the image of h divides the image of g",
			By(
				wImage,
				productImage,
				polynomial_division.PolynomialDividesDef.At(
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					a.TermAs[Fun[Nat, B]]("λi:num. ι(h(i))"),
					a.TermAs[Fun[Nat, B]]("λi:num. ι(g(i))"))))
	}),
})}

// TransportOddDegreeRootsIsomorphism — odd-degree roots are carried along a
// ring isomorphism onto any field: an odd-degree polynomial over G, its
// coefficients carried back along the inverse, is one over F of the same
// degree, and the isomorphism carries its root in F to a root of the first.
var TransportOddDegreeRootsIsomorphism = transportOddDegreeRootsIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "TransportOddDegreeRootsIsomorphism",
	Key:  "prop_de6d8a8c92b4edec",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B).",
		Hypotheses: []string{
			"ring_isomorphism(field_ring(F), field_ring(G), ι)",
			"odd_degree_roots(F)",
		},
		Conclusion: "odd_degree_roots(G)",
		Abbrev: Abbrev{
			{Name: "pullCoefficients", Text: "λc:set(A). λj:(A → B). λr:(num → B). λn:num. " +
				"    inverse_on(c, j, r(n))"},
		},
	}, func(
		a *Argument,
		fieldF field.FieldFact[on.F],
		fieldG field.FieldFact[on.G],
		ι *Arrow[A, B],
		iso, odd Fact,
	) {
		F := a.TermAs[FieldOps[A]]("F")
		G := a.TermAs[FieldOps[B]]("G")
		oddRoots := a.Unfolded(odd, polynomial_evaluation.OddDegreeRootsDef)
		fCarrier := a.TermAs[Set[A]]("F.carrier")
		gCarrier := a.TermAs[Set[B]]("G.carrier")
		back := a.TermAs[Fun[B, A]]("inverse_on(F.carrier, ι)")
		ringF := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		ringG := a.TermAs[module_record.RingOps[B]]("field_ring(G)")
		reverse := a.Have(
			"the inverse is a ring isomorphism",
			"ring_isomorphism(field_ring(G), field_ring(F), inverse_on(F.carrier, ι))",
			By(iso, ring_homomorphism.IsomorphismInverse.At(ringF, ringG, ι)))
		forwardParts := a.Conjuncts(
			a.Unfolded(iso, ring_homomorphism.RingIsomorphismDef),
			"the embedding is a homomorphism",
			"the embedding is injective",
			"the embedding covers the target")
		reverseParts := a.Conjuncts(
			a.Unfolded(reverse, ring_homomorphism.RingIsomorphismDef),
			"the inverse is a homomorphism",
			"the inverse is injective",
			"the inverse covers the source")
		hom, onto := forwardParts[0], forwardParts[2]
		inverseHom, inverseOnto := reverseParts[0], reverseParts[2]
		a.Do(Unfold(polynomial_evaluation.OddDegreeRootsDef))
		p := a.FixAs[Fun[Nat, B]]("p")
		polynomialOdd := a.Assume()
		pulled := a.TermAs[Fun[Nat, A]]("«pullCoefficients»(F.carrier, ι, p)")
		pullback := a.Have(
			"carried back along the inverse, the polynomial keeps its degree",
			"polynomial_over(F.carrier, «pullCoefficients»(F.carrier, ι, p)) ∧ "+
				"polynomial_degree(«pullCoefficients»(F.carrier, ι, p)) = polynomial_degree(p)",
			By(
				Normalized,
				fieldF,
				fieldG,
				inverseHom,
				inverseOnto,
				polynomialOdd,
				field.CarrierSubfield.Read(fieldG),
				FieldEmbeddingPolynomials.At(G, F, back, gCarrier, p)))
		x, root := a.ObtainAs[A](
			"the carried-back odd polynomial has a root in F",
			"∃x:A. x ∈ F.carrier ∧ polynomial_eval(«pullCoefficients»(F.carrier, ι, p), x) = F.zero",
			By(oddRoots.At(pulled), pullback, polynomialOdd))
		roundTrip := a.Have(
			"every coefficient returns under the two maps",
			"(λn:num. ι(inverse_on(F.carrier, ι, p(n)))) = p",
			Derive(func(c *Argument) {
				c.Do(Funext())
				c.Show(
					"the inverse law applies to each coefficient",
					By(
						Normalized,
						onto,
						polynomialOdd,
						At(functions.InverseOnRight, fCarrier, ι),
						At(polynomial.CoefficientIn, c.TermAs[B]("G.zero"), gCarrier, p)))
			}))
		a.Take(ι.Apply(x))
		a.Show(
			"evaluation commutes with the isomorphism",
			By(
				fieldF,
				fieldG,
				hom,
				roundTrip,
				root,
				pullback,
				field.CarrierSubfield.Read(fieldF),
				FieldEmbeddingPolynomials.At(F, G, ι, fCarrier, pulled),
				ring_homomorphism.MapZero.Read(hom),
				ring_homomorphism.MapIn.Read(hom)))
	}),
})}
