// lrs_morphism.go — maps of locally ringed spaces and their induced maps on germs.

package locally_ringed_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// StalkMapHomomorphism — both stalks are rings (StalkRing), and the
// stalk map is checked on germs. The germ of t over an open V ∋ f(x)
// goes to the germ of ψ(V, t) over the preimage of V, an open
// neighbourhood of x (presheaf.StalkMapGerm), so the image of a germ lies
// in the stalk at x. Two germs are germs of s and t over one open W
// (presheaf.GermInduction2): the germ of s + t goes to the germ of
// ψ(W, s + t) = ψ(W, s) + ψ(W, t), which over the preimage of W is the
// sum of the images of the two germs; products likewise. The one of a
// stalk is the germ of one over the whole space, and ψ keeps one.
var StalkMapHomomorphism = stalkMapHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "StalkMapHomomorphism",
	Key:  "prop_99be2dd05a4963de",
	Build: family.Theorem(Statement{
		Binders: "∀X:sheaf_of_rings(A, B). " +
			"∀Y:sheaf_of_rings(C, D). " +
			"∀f:(A → C). " +
			"∀ψ:(set(C) → D → B). " +
			"∀x:A.",
		Hypotheses: []string{
			"continuous_map(X.T, Y.T, f)",
			"∀V:set(C). V ∈ Y.T ⇒ ring_homomorphism(Y(V), X(preimage_on(⋃X.T, f, V)), ψ(V))",
			"∀V W:set(C). ∀t:D. " +
				"    V ∈ Y.T ∧ W ∈ Y.T ∧ W ⊆ V ∧ t ∈ Y(V).carrier ⇒ " +
				"    X.res(preimage_on(⋃X.T, f, V), preimage_on(⋃X.T, f, W), ψ(V, t)) = ψ(W, Y.res(V, W, t))",
			"x ∈ ⋃X.T",
		},
		Conclusion: "ring_homomorphism(stalk_ring(Y.T, Y, Y.res, f(x)), " +
			"    stalk_ring(X.T, X, X.res, x), " +
			"    stalk_map(X.T, λU:set(A). X(U).carrier, X.res, f, ψ, x))",
	},
		func(
			a *Argument,
			X SheafOfRingsFact[on.T],
			Y Fact,
			f *Arrow[A, C],
			ψ *Arrow2[Set[C], D, B],
			morphism Fact,
			x *Expr[A],
			inSpace Fact,
		) {
			parts := a.Conjuncts(
				morphism,
				"f is continuous",
				"each ψ(V) is a ring homomorphism from the sections "+
					"of Y over V to those of X over the preimage of V",
				"ψ commutes with restriction")
			continuity, homs, natural := parts[0], parts[1], parts[2]
			ringX, ringY := SheafPresheafOfRings.Read(X), SheafPresheafOfRings.Read(Y)
			presheafX, presheafY := Presheaf.Read(ringX), Presheaf.Read(ringY)
			pointInY := a.Have(
				"f(x) is a point of the space of Y",
				"f(x) ∈ ⋃Y.T",
				By(continuous.MapsInto.Read(continuity), inSpace))
			sections := a.Have(
				"ψ carries a section of Y over an open V to a section of X over the preimage of V",
				"∀V:set(C). ∀t:D. V ∈ Y.T ∧ t ∈ Y(V).carrier ⇒ ψ(V, t) ∈ X(preimage_on(⋃X.T, f, V)).carrier",
				Derive(func(b *Argument) {
					b.FixAs[Set[C]]("V")
					b.FixAs[D]("t")
					section := b.Assume()
					hom := b.Have(
						"ψ(V) is a ring homomorphism",
						"ring_homomorphism(Y(V), X(preimage_on(⋃X.T, f, V)), ψ(V))",
						By(homs, section))
					b.Show(
						"which carries Y(V) into the sections over the preimage of V",
						By(ring_homomorphism.MapIn.Read(hom), section))
				}))
			neighbourhood := a.Have(
				"the preimage of an open V ∋ f(x) is an open neighbourhood of x",
				"∀V:set(C). V ∈ Y.T ∧ f(x) ∈ V ⇒ preimage_on(⋃X.T, f, V) ∈ X.T ∧ x ∈ preimage_on(⋃X.T, f, V)",
				Derive(func(b *Argument) {
					b.FixAs[Set[C]]("V")
					contains := b.Assume()
					open := b.Have(
						"the preimage is open, f being continuous",
						"preimage_on(⋃X.T, f, V) ∈ X.T",
						By(continuous.PreimageOpen.Read(continuity), contains))
					b.Show(
						"and holds x, as f(x) ∈ V",
						BySets(open, inSpace, contains))
				}))
			germImage := a.Have(
				"the stalk map sends the germ of t over V to the germ of ψ(V, t) over the preimage of V",
				Statement{
					Binders: "∀V:set(C). ∀t:D.",
					Hypotheses: []string{
						"V ∈ Y.T",
						"f(x) ∈ V",
						"t ∈ Y(V).carrier",
					},
					Conclusion: "stalk_map(X.T, " +
						"    λU:set(A). X(U).carrier, " +
						"    X.res, " +
						"    f, " +
						"    ψ, " +
						"    x, " +
						"    sheaf_germ(Y.T, λU:set(C). Y(U).carrier, Y.res, f(x), V, t)) = " +
						"sheaf_germ(X.T, λU:set(A). X(U).carrier, X.res, x, preimage_on(⋃X.T, f, V), ψ(V, t))",
				},
				By(presheaf.StalkMapGerm.Read(presheafX), presheafY, continuity, sections, natural, inSpace))

			stalkRingY := a.Have(
				"the stalk of Y at f(x) is a ring",
				"comm_ring_on(stalk_ring(Y.T, Y, Y.res, f(x)))",
				By(StalkRing.Read(ringY), pointInY))
			stalkRingX := a.Have(
				"the stalk of X at x is a ring",
				"comm_ring_on(stalk_ring(X.T, X, X.res, x))",
				By(StalkRing.Read(ringX), inSpace))

			topologyY, sectionsY :=
				a.TermAs[Set[Set[C]]]("Y.T"), a.TermAs[Fun[Set[C], Set[D]]]("λU:set(C). Y(U).carrier")
			restrictY, fx := a.TermAs[Fun3[Set[C], Set[C], D, D]]("Y.res"), f.Apply(x)
			into := a.Have(
				"the stalk map carries the stalk of Y at f(x) into the stalk of X at x",
				Statement{
					Binders: "∀g:set(prod(set(C), D)).",
					Hypotheses: []string{
						"g ∈ stalk(Y.T, λU:set(C). Y(U).carrier, Y.res, f(x))",
					},
					Conclusion: "stalk_map(X.T, λU:set(A). X(U).carrier, X.res, f, ψ, x, g) ∈ " +
						"stalk(X.T, λU:set(A). X(U).carrier, X.res, x)",
				},
				ByInduction(presheaf.GermInduction,
					Case(
						"the germ of s over W goes to the germ of ψ(W, s) over the preimage of W, a neighbourhood of x",
						Derive(func(b *Argument) {
							W := b.FixAs[Set[C]]("W")
							s := b.FixAs[D]("s")
							member := b.Assume()
							preimage := b.TermAs[Set[A]]("preimage_on(⋃X.T, f, W)")
							b.Show(
								"a germ at x of a section over an open neighbourhood of x lies in the stalk",
								By(
									presheaf.GermInStalk.Read(presheafX).AsFact().At(x, preimage, ψ.Apply(W, s)),
									germImage.At(W, s),
									neighbourhood.At(W),
									sections.At(W, s),
									member))
						}))))

			sums := a.Have(
				"the stalk map keeps sums",
				Statement{
					Binders: "∀g h:set(prod(set(C), D)).",
					Hypotheses: []string{
						"g ∈ stalk(Y.T, λU:set(C). Y(U).carrier, Y.res, f(x))",
						"h ∈ stalk(Y.T, λU:set(C). Y(U).carrier, Y.res, f(x))",
					},
					Conclusion: "stalk_map(X.T, " +
						"    λU:set(A). X(U).carrier, " +
						"    X.res, " +
						"    f, " +
						"    ψ, " +
						"    x, " +
						"    stalk_add(Y.T, Y, Y.res, f(x), g, h)) = " +
						"stalk_add(X.T, " +
						"    X, " +
						"    X.res, " +
						"    x, " +
						"    stalk_map(X.T, λU:set(A). X(U).carrier, X.res, f, ψ, x, g), " +
						"    stalk_map(X.T, λU:set(A). X(U).carrier, X.res, f, ψ, x, h))",
				},
				ByInduction(At(presheaf.GermInduction2, topologyY, sectionsY, restrictY, fx), presheafY,
					Case(
						"over one open W ∋ f(x), the germ of a sum goes to the sum of the images",
						Derive(func(b *Argument) {
							W := b.FixAs[Set[C]]("W")
							s, t := b.FixAs[D]("s"), b.FixAs[D]("t")
							members := b.Assume()
							hom := b.Have(
								"ψ(W) is a ring homomorphism",
								"ring_homomorphism(Y(W), X(preimage_on(⋃X.T, f, W)), ψ(W))",
								By(homs, members))
							sum := b.Have(
								"the sum of s and t is a section over W",
								"Y(W).add(s, t) ∈ Y(W).carrier",
								By(comm_ring.AddIn.Read(ring_homomorphism.Source.Read(hom)), members))
							b.Show(
								"both sides are the germ over the preimage of W of the sum of ψ(W, s) and ψ(W, t)",
								CalcEq(
									Leg(
										b.TermAs[Set[Prod[Set[A], B]]](
											"stalk_map(X.T, "+
												"    (λU:set(A). X(U).carrier), "+
												"    X.res, "+
												"    f, "+
												"    ψ, "+
												"    x, "+
												"    sheaf_germ(Y.T, (λU:set(C). Y(U).carrier), Y.res, f(x), W, Y(W).add(s, t)))"),
										"the sum of the germs of s and t is the germ of their sum",
										By(GermAdd.Read(ringY).AsFact().At(fx, W, s, t), members)),
									Leg(
										b.TermAs[Set[Prod[Set[A], B]]](
											"sheaf_germ(X.T, "+
												"    (λU:set(A). X(U).carrier), "+
												"    X.res, "+
												"    x, "+
												"    preimage_on(⋃X.T, f, W), "+
												"    ψ(W, Y(W).add(s, t)))"),
										"which goes to the germ of its image under ψ(W)",
										By(germImage.At(W, b.TermAs[D]("Y(W).add(s, t)")), members, sum)),
									Leg(
										b.TermAs[Set[Prod[Set[A], B]]](
											"sheaf_germ(X.T, "+
												"    (λU:set(A). X(U).carrier), "+
												"    X.res, "+
												"    x, "+
												"    preimage_on(⋃X.T, f, W), "+
												"    X(preimage_on(⋃X.T, f, W)).add(ψ(W, s), ψ(W, t)))"),
										"ψ(W) keeps the sum",
										By(ring_homomorphism.MapAdd.Read(hom).AsFact().At(s, t), members)),
									Leg(
										b.TermAs[Set[Prod[Set[A], B]]](
											"stalk_add(X.T, "+
												"    X, "+
												"    X.res, "+
												"    x, "+
												"    sheaf_germ(X.T, (λU:set(A). X(U).carrier), X.res, x, preimage_on(⋃X.T, f, W), ψ(W, s)), "+
												"    sheaf_germ(X.T, (λU:set(A). X(U).carrier), X.res, x, preimage_on(⋃X.T, f, W), ψ(W, t)))"),
										"over the preimage of W the germ of a sum is the sum of the germs",
										By(GermAdd.Read(ringX), neighbourhood.At(W), sections.At(W, s), sections.At(W, t), members)),
									FinalLeg(
										"each of those germs is the image of the germ of s or of t",
										By(germImage.At(W, s), germImage.At(W, t), members)),
								))
						}))))

			products := a.Have(
				"the stalk map keeps products",
				Statement{
					Binders: "∀g h:set(prod(set(C), D)).",
					Hypotheses: []string{
						"g ∈ stalk(Y.T, λU:set(C). Y(U).carrier, Y.res, f(x))",
						"h ∈ stalk(Y.T, λU:set(C). Y(U).carrier, Y.res, f(x))",
					},
					Conclusion: "stalk_map(X.T, " +
						"    λU:set(A). X(U).carrier, " +
						"    X.res, " +
						"    f, " +
						"    ψ, " +
						"    x, " +
						"    stalk_mul(Y.T, Y, Y.res, f(x), g, h)) = " +
						"stalk_mul(X.T, " +
						"    X, " +
						"    X.res, " +
						"    x, " +
						"    stalk_map(X.T, λU:set(A). X(U).carrier, X.res, f, ψ, x, g), " +
						"    stalk_map(X.T, λU:set(A). X(U).carrier, X.res, f, ψ, x, h))",
				},
				ByInduction(At(presheaf.GermInduction2, topologyY, sectionsY, restrictY, fx), presheafY,
					Case(
						"over one open W ∋ f(x), the germ of a product goes to the product of the images",
						Derive(func(b *Argument) {
							W := b.FixAs[Set[C]]("W")
							s, t := b.FixAs[D]("s"), b.FixAs[D]("t")
							members := b.Assume()
							hom := b.Have(
								"ψ(W) is a ring homomorphism",
								"ring_homomorphism(Y(W), X(preimage_on(⋃X.T, f, W)), ψ(W))",
								By(homs, members))
							product := b.Have(
								"the product of s and t is a section over W",
								"Y(W).mul(s, t) ∈ Y(W).carrier",
								By(comm_ring.MulIn.Read(ring_homomorphism.Source.Read(hom)), members))
							b.Show(
								"both sides are the germ over the preimage of W of the product of ψ(W, s) and ψ(W, t)",
								CalcEq(
									Leg(
										b.TermAs[Set[Prod[Set[A], B]]](
											"stalk_map(X.T, "+
												"    (λU:set(A). X(U).carrier), "+
												"    X.res, "+
												"    f, "+
												"    ψ, "+
												"    x, "+
												"    sheaf_germ(Y.T, (λU:set(C). Y(U).carrier), Y.res, f(x), W, Y(W).mul(s, t)))"),
										"the product of the germs of s and t is the germ of their product",
										By(GermMul.Read(ringY).AsFact().At(fx, W, s, t), members)),
									Leg(
										b.TermAs[Set[Prod[Set[A], B]]](
											"sheaf_germ(X.T, "+
												"    (λU:set(A). X(U).carrier), "+
												"    X.res, "+
												"    x, "+
												"    preimage_on(⋃X.T, f, W), "+
												"    ψ(W, Y(W).mul(s, t)))"),
										"which goes to the germ of its image under ψ(W)",
										By(germImage.At(W, b.TermAs[D]("Y(W).mul(s, t)")), members, product)),
									Leg(
										b.TermAs[Set[Prod[Set[A], B]]](
											"sheaf_germ(X.T, "+
												"    (λU:set(A). X(U).carrier), "+
												"    X.res, "+
												"    x, "+
												"    preimage_on(⋃X.T, f, W), "+
												"    X(preimage_on(⋃X.T, f, W)).mul(ψ(W, s), ψ(W, t)))"),
										"ψ(W) keeps the product",
										By(ring_homomorphism.MapMul.Read(hom).AsFact().At(s, t), members)),
									Leg(
										b.TermAs[Set[Prod[Set[A], B]]](
											"stalk_mul(X.T, "+
												"    X, "+
												"    X.res, "+
												"    x, "+
												"    sheaf_germ(X.T, (λU:set(A). X(U).carrier), X.res, x, preimage_on(⋃X.T, f, W), ψ(W, s)), "+
												"    sheaf_germ(X.T, (λU:set(A). X(U).carrier), X.res, x, preimage_on(⋃X.T, f, W), ψ(W, t)))"),
										"over the preimage of W the germ of a product is the product of the germs",
										By(GermMul.Read(ringX), neighbourhood.At(W), sections.At(W, s), sections.At(W, t), members)),
									FinalLeg(
										"each of those germs is the image of the germ of s or of t",
										By(germImage.At(W, s), germImage.At(W, t), members)),
								))
						}))))

			whole := a.Have(
				"the space of Y is open",
				"⋃Y.T ∈ Y.T",
				By(topological_space.SpaceOpen.Read(presheaf.Topology.Read(presheafY))))
			homWhole := a.Have(
				"ψ over the whole space is a ring homomorphism",
				"ring_homomorphism(Y(⋃Y.T), X(preimage_on(⋃X.T, f, ⋃Y.T)), ψ(⋃Y.T))",
				By(homs, whole))
			oneIn := a.Have(
				"one over the whole space is a section",
				"Y(⋃Y.T).one ∈ Y(⋃Y.T).carrier",
				By(comm_ring.OneIn.Read(ring_homomorphism.Source.Read(homWhole))))
			space := a.TermAs[Set[C]]("⋃Y.T")
			one := a.Have(
				"the stalk map keeps one",
				"stalk_map(X.T, (λU:set(A). X(U).carrier), X.res, f, ψ, x, stalk_one(Y.T, Y, Y.res, f(x))) = "+
					"stalk_one(X.T, X, X.res, x)",
				CalcEq(
					Leg(
						a.TermAs[Set[Prod[Set[A], B]]](
							"stalk_map(X.T, "+
								"    (λU:set(A). X(U).carrier), "+
								"    X.res, "+
								"    f, "+
								"    ψ, "+
								"    x, "+
								"    sheaf_germ(Y.T, (λU:set(C). Y(U).carrier), Y.res, f(x), ⋃Y.T, Y(⋃Y.T).one))"),
						"the one of the stalk of Y is the germ of one over the whole space",
						By(GermOne.Read(ringY).AsFact().At(fx, space), whole, pointInY)),
					Leg(
						a.TermAs[Set[Prod[Set[A], B]]](
							"sheaf_germ(X.T, "+
								"    (λU:set(A). X(U).carrier), "+
								"    X.res, "+
								"    x, "+
								"    preimage_on(⋃X.T, f, ⋃Y.T), "+
								"    ψ(⋃Y.T, Y(⋃Y.T).one))"),
						"which goes to the germ of its image under ψ",
						By(germImage.At(space, a.TermAs[D]("Y(⋃Y.T).one")), whole, pointInY, oneIn)),
					Leg(
						a.TermAs[Set[Prod[Set[A], B]]](
							"sheaf_germ(X.T, "+
								"    (λU:set(A). X(U).carrier), "+
								"    X.res, "+
								"    x, "+
								"    preimage_on(⋃X.T, f, ⋃Y.T), "+
								"    X(preimage_on(⋃X.T, f, ⋃Y.T)).one)"),
						"ψ keeps one",
						By(ring_homomorphism.MapOne.Read(homWhole))),
					FinalLeg(
						"and over the preimage of the whole space, a neighbourhood "+
							"of x, the germ of one is the one of the stalk of X",
						By(GermOne.Read(ringX), neighbourhood.At(space), whole, pointInY))))

			a.Show(
				"so the stalk map is a ring homomorphism: both stalks are rings, "+
					"it carries one into the other, and it keeps sums, products and one",
				Unfold(ring_homomorphism.RingHomomorphism),
				By(stalkRingY, stalkRingX, into, sums, products, one))
		}),
})}

// LrsMorphism — a continuous map with contravariant section homomorphisms,
// compatible with restrictions and local on each stalk.
var LrsMorphism = lrsMorphismThm{family.DefineStructure(registry.DefEntry{
	Name: "LrsMorphism", Const: "lrs_morphism", Subject: "f",
	Key: "prop_c891deeedb86bd8b",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"set(set(C)) → " +
		"(set(C) → ring_ops(D)) → " +
		"(set(C) → set(C) → D → D) → " +
		"(A → C) → " +
		"(set(C) → D → B) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → ring_ops(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀T':set(set(C)). " +
			"∀F':(set(C) → ring_ops(D)). " +
			"∀res':(set(C) → set(C) → D → D). " +
			"∀f:(A → C). " +
			"∀ψ:(set(C) → D → B). " +
			"    lrs_morphism(T, F, res, T', F', res', f, ψ) ⇔ " +
			"    (locally_ringed_space(T, F, res)) ∧ " +
			"    (locally_ringed_space(T', F', res')) ∧ " +
			"    (continuous_map(T, T', f)) ∧ " +
			"    (∀V:set(C). V ∈ T' ⇒ ring_homomorphism(F'(V), F(preimage_on(⋃T, f, V)), ψ(V))) ∧ " +
			"    (∀V W:set(C). ∀t:D. " +
			"        V ∈ T' ∧ W ∈ T' ∧ W ⊆ V ∧ t ∈ F'(V).carrier ⇒ " +
			"        res(preimage_on(⋃T, f, V), preimage_on(⋃T, f, W), ψ(V, t)) = ψ(W, res'(V, W, t))) ∧ " +
			"    (∀x:A. ∀g:set(prod(set(C), D)). " +
			"        x ∈ ⋃T ∧ " +
			"        g ∈ stalk(T', (λU:set(C). F'(U).carrier), res', f(x)) ∧ " +
			"        ¬ring_unit(stalk_ring(T', F', res', f(x)), g) ⇒ " +
			"        ¬ring_unit(stalk_ring(T, F, res, x), " +
			"            stalk_map(T, (λU:set(A). F(U).carrier), res, f, ψ, x, g)))",
	},
	Deps: []registry.EntryLike{LocallyRingedSpace},
})}

// MorphismSource — a defining condition of a locally ringed space morphism.
var MorphismSource = morphismSourceThm{family.Add(registry.ProofEntry{
	Name:  "MorphismSource",
	Key:   "prop_55fda97c3c0ed29d",
	Build: LrsMorphism.Axiom("locally_ringed_space(T, F, res)")})}

// MorphismTarget — a defining condition of a locally ringed space morphism.
var MorphismTarget = morphismTargetThm{family.Add(registry.ProofEntry{
	Name:  "MorphismTarget",
	Key:   "prop_3996cf1e950c84ba",
	Build: LrsMorphism.Axiom("locally_ringed_space(T', F', res')")})}

// MorphismContinuous — a defining condition of a locally ringed space morphism.
var MorphismContinuous = morphismContinuousThm{family.Add(registry.ProofEntry{
	Name:  "MorphismContinuous",
	Key:   "prop_35bc37ee6cece9e4",
	Build: LrsMorphism.Axiom("continuous_map(T, T', f)")})}

// MorphismSections — a defining condition of a locally ringed space morphism.
var MorphismSections = morphismSectionsThm{family.Add(registry.ProofEntry{
	Name: "MorphismSections",
	Key:  "prop_a06ca75571009134",
	Build: LrsMorphism.Axiom(Statement{
		Binders: "∀V:set(C).",
		Hypotheses: []string{
			"V ∈ T'",
		},
		Conclusion: "ring_homomorphism(F'(V), F(preimage_on(⋃T, f, V)), ψ(V))",
	})})}

// MorphismRestrict — a defining condition of a locally ringed space morphism.
var MorphismRestrict = morphismRestrictThm{family.Add(registry.ProofEntry{
	Name: "MorphismRestrict",
	Key:  "prop_c7b096a1375fabd5",
	Build: LrsMorphism.Axiom(Statement{
		Binders: "∀V W:set(C). ∀t:D.",
		Hypotheses: []string{
			"V ∈ T'",
			"W ∈ T'",
			"W ⊆ V",
			"t ∈ F'(V).carrier",
		},
		Conclusion: "res(preimage_on(⋃T, f, V), preimage_on(⋃T, f, W), ψ(V, t)) = ψ(W, res'(V, W, t))",
	})})}

// MorphismLocal — a defining condition of a locally ringed space morphism.
var MorphismLocal = morphismLocalThm{family.Add(registry.ProofEntry{
	Name: "MorphismLocal",
	Key:  "prop_9846dd792c362e3",
	Build: LrsMorphism.Axiom(Statement{
		Binders: "∀x:A. ∀g:set(prod(set(C), D)).",
		Hypotheses: []string{
			"x ∈ ⋃T",
			"g ∈ stalk(T', λU:set(C). F'(U).carrier, res', f(x))",
			"¬ring_unit(stalk_ring(T', F', res', f(x)), g)",
		},
		Conclusion: "¬ring_unit(stalk_ring(T, F, res, x), " +
			"    stalk_map(T, λU:set(A). F(U).carrier, res, f, ψ, x, g))",
	})})}

// MorphismCompose — Carrier-restricted preimages compose because f maps source points into the middle space.
var MorphismCompose = morphismComposeThm{family.Add(registry.ProofEntry{
	Name: "MorphismCompose",
	Key:  "prop_575e0df408bb1dc6",
	Deps: []registry.EntryLike{
		MorphismSource,
		MorphismTarget,
		MorphismContinuous,
		MorphismSections,
		MorphismRestrict,
		MorphismLocal,
		presheaf.StalkMapGerm,
		StalkMapHomomorphism,
		LrsMorphism,
	},
	Build: family.Card(
		"∀X:locally_ringed_space(A, B). "+
			"∀Y:locally_ringed_space(C, D). "+
			"∀Z:locally_ringed_space(E, F). "+
			"∀f:lrs_morphism(X, Y). "+
			"∀g:lrs_morphism(Y, Z). "+
			"    lrs_morphism(X, Z, λx:A. g(f(x)), λW:set(E). λt:F. f.ψ(preimage_on(⋃Y.T, g, W), g.ψ(W, t)))",
		"Carrier-restricted preimages compose because f maps source points into the middle space. "+
			"Compose section homomorphisms and their restriction identities. StalkMapGerm identifies the "+
			"composite stalk map with the composite on germs, and the two locality implications compose."),
})}

// IsomorphismMorphism — Use the homeomorphism and the section isomorphisms for continuity, section maps and naturality.
var IsomorphismMorphism = isomorphismMorphismThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismMorphism",
	Key:  "prop_d58d65da5c733c7d",
	Reading: "The endpoint hypotheses are necessary: lrs_isomorphism " +
		"alone does not assert that either endpoint is a locally ringed space.",
	Deps: []registry.EntryLike{
		LrsIsomorphismDef,
		presheaf.StalkMapGerm,
		StalkMapHomomorphism,
		LrsMorphism,
		ring_homomorphism.RingIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀X:locally_ringed_space(A, B). " +
			"∀Y:locally_ringed_space(C, D). " +
			"∀f:(A → C). " +
			"∀ψ:(set(C) → D → B).",
		Hypotheses: []string{
			"lrs_isomorphism(X.T, X, X.res, Y.T, Y, Y.res, f, ψ)",
		},
		Conclusion: "lrs_morphism(X, Y, f, ψ)",
	},
		"Use the homeomorphism and the section isomorphisms for continuity, section maps and "+
			"naturality. Transport representatives through the inverse homeomorphism and inverse section "+
			"maps to obtain inverse stalk homomorphisms; a ring isomorphism reflects units, giving locality."),
})}

// MorphismInverseIsomorphism — over an open V of Y, with P its preimage
// under f (open, f being continuous), the points of Y that g carries into
// P are exactly those of V: V lies among the points of Y, g carries these
// into the points of X, and f undoes g on them. So g.ψ(P) is a ring
// homomorphism from X(P) back to Y(V); read at P, the third equation says
// that f.ψ(V) undoes it, the fourth that it undoes f.ψ(V), and f.ψ(V),
// having a two-sided inverse, is a bijective ring homomorphism from Y(V)
// onto X(P). The point maps, continuous and inverse on the two spaces,
// make f a homeomorphism, and the restriction law is the one f has as a
// morphism. The section isomorphisms come before the homeomorphism:
// once homeomorphic_map(X.T, Y.T, f) is a fact, f is the subject of two
// structures and the text no longer reads its field f.ψ.
var MorphismInverseIsomorphism = morphismInverseIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "MorphismInverseIsomorphism",
	Key:  "prop_199e7c93212ec6e8",
	Reading: "Inverse equations are restricted to space points and valid " +
		"sections; values of the total maps outside these carriers are not constrained.",
	Build: family.Theorem(Statement{
		Binders: "∀X:locally_ringed_space(A, B). " +
			"∀Y:locally_ringed_space(C, D). " +
			"∀f:lrs_morphism(X, Y). " +
			"∀g:lrs_morphism(Y, X).",
		Hypotheses: []string{
			"∀x:A. x ∈ ⋃X.T ⇒ g(f(x)) = x",
			"∀y:C. y ∈ ⋃Y.T ⇒ f(g(y)) = y",
			"∀U:set(A). ∀s:B. U ∈ X.T ∧ s ∈ X(U).carrier ⇒ f.ψ(preimage_on(⋃Y.T, g, U), g.ψ(U, s)) = s",
			"∀V:set(C). ∀t:D. V ∈ Y.T ∧ t ∈ Y(V).carrier ⇒ g.ψ(preimage_on(⋃X.T, f, V), f.ψ(V, t)) = t",
		},
		Conclusion: "lrs_isomorphism(X.T, X, X.res, Y.T, Y, Y.res, f, f.ψ)",
	},
		func(a *Argument, X LocallyRingedSpaceFact[on.T], _ Fact, f, g Fact, inverses Fact) {
			equations := a.Conjuncts(
				inverses,
				"g undoes f on the points of X",
				"f undoes g on the points of Y",
				"f.ψ undoes g.ψ on the sections over the opens of X",
				"g.ψ undoes f.ψ on the sections over the opens of Y")
			pointsBack, pointsForth, sectionsBack, sectionsForth :=
				equations[0], equations[1], equations[2], equations[3]
			isomorphisms := a.Have(
				"over every open V of Y, f.ψ(V) is a ring isomorphism onto the sections over the preimage of V",
				"∀V:set(C). V ∈ Y.T ⇒ ring_isomorphism(Y(V), X(preimage_on(⋃X.T, f, V)), f.ψ(V))",
				Derive(func(b *Argument) {
					b.FixAs[Set[C]]("V")
					vOpen := b.Assume()
					preimage := b.TermAs[Set[A]]("preimage_on(⋃X.T, f, V)")
					preimageOpen := b.Have(
						"the preimage P of V is open in X",
						"preimage_on(⋃X.T, f, V) ∈ X.T",
						By(continuous.PreimageOpen.Read(MorphismContinuous.Read(f)), vOpen))
					backToV := b.Have(
						"the points of Y that g carries into P are those of V",
						"preimage_on(⋃Y.T, g, preimage_on(⋃X.T, f, V)) = V",
						BySets(vOpen, pointsForth, continuous.MapsInto.Read(MorphismContinuous.Read(g))))
					forward := b.Have(
						"f.ψ(V) is a ring homomorphism from Y(V) to X(P)",
						"ring_homomorphism(Y(V), X(preimage_on(⋃X.T, f, V)), f.ψ(V))",
						By(MorphismSections.Read(f), vOpen))
					backward := b.Have(
						"g.ψ(P) is a ring homomorphism from X(P) to the sections "+
							"of Y over the points g carries into P, which are those of V",
						"ring_homomorphism(X(preimage_on(⋃X.T, f, V)), Y(V), g.ψ(preimage_on(⋃X.T, f, V)))",
						By(Normalized, MorphismSections.Read(g).AsFact().At(preimage), backToV, preimageOpen))
					undoes := b.Have(
						"read at P, the third equation says that f.ψ(V) undoes g.ψ(P) on X(P)",
						"∀s:B. s ∈ X(preimage_on(⋃X.T, f, V)).carrier ⇒ f.ψ(V, g.ψ(preimage_on(⋃X.T, f, V), s)) = s",
						b.ForEach(func(s *Expr[B]) Action {
							return By(sectionsBack.At(preimage, s), backToV, preimageOpen)
						}))
					bijection := b.Conjuncts(
						b.Have(
							"so g.ψ(P) is a two-sided inverse, and f.ψ(V) a bijection from Y(V) onto X(P)",
							"injective_on(Y(V).carrier, f.ψ(V)) ∧ "+
								"image(f.ψ(V), Y(V).carrier) = X(preimage_on(⋃X.T, f, V)).carrier",
							By(
								functions.TwoSidedInverseBijection.At(
									b.TermAs[Set[D]]("Y(V).carrier"),
									b.TermAs[Set[B]]("X(preimage_on(⋃X.T, f, V)).carrier"),
									b.TermAs[Fun[D, B]]("f.ψ(V)"),
									b.TermAs[Fun[B, D]]("g.ψ(preimage_on(⋃X.T, f, V))")),
								sectionsForth,
								vOpen,
								undoes,
								ring_homomorphism.MapIn.Read(forward),
								ring_homomorphism.MapIn.Read(backward))),
						"f.ψ(V) is one-to-one on Y(V)",
						"and carries Y(V) onto X(P)")
					b.Show(
						"so f.ψ(V), a ring homomorphism and a bijection from Y(V) onto X(P), is a ring isomorphism",
						Unfold(ring_homomorphism.RingIsomorphismDef),
						By(forward, bijection[0], bijection[1]))
				}))
			homeomorphism := a.Have(
				"f is a homeomorphism, with g a continuous inverse on the points",
				"homeomorphic_map(X.T, Y.T, f)",
				Unfold(continuous.HomeomorphicMap),
				SplitConj(
					Case(
						"f is continuous",
						By(MorphismContinuous.Read(f))),
					Case(
						"g is continuous and inverse to f on the points of the two spaces",
						Witness(a.TermAs[Fun[C, A]]("g")),
						By(MorphismContinuous.Read(g), pointsBack, pointsForth)),
				))
			a.Show(
				"an isomorphism is the homeomorphism and the section "+
					"isomorphisms above, and the restriction law f has as a morphism",
				Unfold(LrsIsomorphismDef),
				By(homeomorphism, isomorphisms, MorphismRestrict.Read(f)))
		}),
})}
