// constant_normal.go — what carries normality through a constant extension.
// The composite K(l) is Galois over K, and a basis of l dual for the sum of
// conjugates recovers the coordinates of an element as sums of its conjugates'
// multiples, integral when the element is integral over a subring inside K;
// and the chart of a ring S between k and K is generated over S by a k-basis
// of l.

package constant_galois

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_pairing"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantCompositeData — where the field l of q^r constants sits: over k, of
// finite degree, and inside the composite K(l), which is a subfield over K.
var ConstantCompositeData = constantCompositeDataThm{family.Add(registry.ProofEntry{
	Name: "ConstantCompositeData",
	Key:  "prop_41fe5acf8e2e2e02",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "composite", Text: "constant_composite(M, K, «constants»)"},
		},
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
			"0 < r",
		},
		Conclusion: "subfield(M, k) ∧ " +
			"subfield(M, K) ∧ " +
			"k ⊆ K ∧ " +
			"(∀x:A. x ∈ K ∧ algebraic_over(M, k, x) ⇒ x ∈ k) ∧ " +
			"subfield(M, «constants») ∧ " +
			"k ⊆ «constants» ∧ " +
			"finite(«constants») ∧ " +
			"finite_extension(M, k, «constants») ∧ " +
			"subfield(M, «composite») ∧ " +
			"K ⊆ «composite» ∧ " +
			"«constants» ⊆ «composite»",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			r *Expr[Nat],
			closed, regular, finiteK, positive Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			l := a.TermAs[Set[A]]("«constants»")
			regularData := a.Conjuncts(
				a.Unfolded(regular, function_field.RegularFunctionFieldDef),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"k is perfect",
				"K is finitely generated over k",
				"K has a parameter over k",
				"k is algebraically closed in K")
			constants := a.Conjuncts(
				GroupPremises(
					closed, regularData[0], finiteK, positive, finite_field.FiniteConstantsSubfield.Read(M).At(k, r)),
				"l is a subfield",
				"l holds k",
				"l has q^r points")
			extension := a.Conjuncts(
				GroupPremises(
					M,
					closed,
					regularData[0],
					finiteK,
					positive,
					finite_field.FiniteConstantsAutomorphisms.At(m, k, r)),
				"l is finite over k",
				"of degree r",
				"with r automorphisms over k")
			a.Show(
				"l is a finite field finite over k, and the composite holds K and l",
				By(
					M,
					regularData[0],
					regularData[1],
					regularData[2],
					regularData[6],
					constants[0],
					constants[1],
					extension[0],
					cardinality.HasSizeDef.At(l, a.TermAs[Nat]("card(k) ^ r")),
					constants[2],
					constant_composite.ConstantCompositeSubfield.At(m, K, l)))
		}),
})}

// ConstantCompositeGalois — the composite K(l) of K with the field l of q^r
// constants is Galois over K. l is Galois over k, so its elements are
// separable over k and over K; their minimal polynomials over K divide
// X^(q^r) − X, so the roots of these polynomials are exactly l, and
// the field they generate over K is Galois.
var ConstantCompositeGalois = constantCompositeGaloisThm{family.Add(registry.ProofEntry{
	Name: "ConstantCompositeGalois",
	Key:  "prop_37f8e94237ec1292",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "minimal", Text: "image(minimal_polynomial(M, K), «constants»)"},
			{Name: "roots", Text: "{x:A | " +
				"    x ∈ M.carrier ∧ (∃p:(num → A). p ∈ «minimal» ∧ polynomial_eval(p, x) = M.zero)}"},
			{Name: "Q", Text: "basis_vector(card(k) ^ r) - basis_vector(1)"},
		},
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
			"0 < r",
		},
		Conclusion: "galois_over(M, K, constant_composite(M, K, «constants»))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			r *Expr[Nat],
			closed, regular, finiteK, positive Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			ring := field.RingOn.Read(M)
			l := a.TermAs[Set[A]]("«constants»")
			minimal := a.TermAs[Set[Fun[Nat, A]]]("«minimal»")
			polynomialQ := a.TermAs[Fun[Nat, A]]("«Q»")
			data := a.Conjuncts(
				GroupPremises(M, closed, regular, finiteK, positive, ConstantCompositeData.At(m, K, k, r)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"k is closed in K",
				"l is a subfield",
				"l holds k",
				"l is finite",
				"l is finite over k",
				"the composite is a subfield",
				"it holds K",
				"it holds l")
			kSubfield, KSubfield, kInK, lSubfield, kInL, finiteL :=
				data[0], data[1], data[2], data[4], data[5], data[6]
			galoisL := a.Have(
				"l is Galois over k: as many automorphisms as its degree",
				"galois_over(M, k, «constants»)",
				By(
					kSubfield,
					lSubfield,
					kInL,
					data[7],
					closed,
					finiteK,
					positive,
					finite_field.FiniteConstantsAutomorphisms.At(m, k, r),
					cardinality.HasSizeDef.At(
						a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, k, «constants»)"), r),
					galois_correspondence.GaloisIffCard.Read(M).At(k, l)))
			minimalData := a.Have(
				"each point of l is separable over k, hence over K, and a root of its minimal polynomial",
				Statement{
					Binders:    "∀b:A.",
					Hypotheses: []string{"b ∈ «constants»"},
					Conclusion: "b ∈ M.carrier ∧ " +
						"algebraic_over(M, K, b) ∧ " +
						"polynomial_over(K, minimal_polynomial(M, K, b)) ∧ " +
						"polynomial_separable(restrict_ring(field_ring(M), K), minimal_polynomial(M, K, b)) ∧ " +
						"polynomial_eval(minimal_polynomial(M, K, b), b) = M.zero",
				},
				Derive(func(b *Argument) {
					point := b.FixAs[A]("b")
					inL := b.Assume()
					inM := b.Have(
						"b lies in M",
						"b ∈ M.carrier",
						BySets(inL, lSubfield, field.SubfieldSubset.At(m, l)))
					pointM := b.MemberOf[on.M](point, inM)
					overK := b.Have(
						"separability climbs from k to K",
						"separable_over(M, K, b)",
						By(
							kSubfield,
							KSubfield,
							kInK,
							galoisL,
							inL,
							pointM,
							galois_correspondence.GaloisOverDef.At(m, k, l),
							galois_correspondence.SeparableTower.Read(M).At(k, K, pointM)))
					opened := b.Conjuncts(
						b.Unfolded(overK, galois_correspondence.SeparableOverDef),
						"b is algebraic over K",
						"its minimal polynomial is separable over K")
					b.Show(
						"the minimal polynomial is over K and vanishes at b",
						By(
							KSubfield,
							pointM,
							opened[0],
							opened[1],
							algebraic_element.MinimalPolynomialSpec.Read(M).At(K, pointM)))
				}))
			minimalMap := a.TermAs[Fun[A, Fun[Nat, A]]]("minimal_polynomial(M, K)")
			inMinimal := a.Have(
				"a member of the set is over K, separable over K, and splits in M",
				Statement{
					Binders:    "∀p:(num → A).",
					Hypotheses: []string{"p ∈ «minimal»"},
					Conclusion: "polynomial_over(K, p) ∧ " +
						"polynomial_separable(restrict_ring(field_ring(M), K), p) ∧ " +
						"polynomial_splits(field_ring(M), p)",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Fun[Nat, A]]("p")
					inP := b.Assume()
					point, chosen := b.ObtainAs[A](
						"p is the minimal polynomial of a point of l",
						"∃c:A. p = minimal_polynomial(M, K, c) ∧ c ∈ «constants»",
						By(inP, set_basic.InImage.At(minimalMap, l, p)))
					b.Show(
						"its data, and M is closed",
						By(closed, chosen, minimalData.At(point), algebraic_closure.ClosedFieldSplits.Read(M).At(p)))
				}))
			rootData := a.Conjuncts(
				GroupPremises(
					data[1], M, finite_field.FiniteConstantsRootPolynomial.At(m, K, a.TermAs[Nat]("card(k)"), r)),
				"X^(q^r) − X is a polynomial over K",
				"its roots in M are l")
			overQ, rootsQ := rootData[0], rootData[1]
			pointwise := a.Have(
				"the roots are exactly the points of l",
				"∀x:A. x ∈ «roots» ⇔ x ∈ «constants»",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.Iff()
					b.Forward(
						"a root divides into X^(q^r) − X, so it is one of its roots",
						func(c *Argument, inRoots Fact) {
							opened := c.Conjuncts(
								c.Have(
									"x is a point of M and a root of a member of the set",
									"x ∈ M.carrier ∧ (∃p:(num → A). p ∈ «minimal» ∧ polynomial_eval(p, x) = M.zero)",
									BySets(inRoots)),
								"x lies in M",
								"x is a root of a member")
							xIn := opened[0]
							p, member := c.UnpackAs[Fun[Nat, A]](opened[1], "p")
							memberParts := c.Conjuncts(
								member,
								"p is in the set",
								"p vanishes at x")
							point, chosen := c.ObtainAs[A](
								"p is the minimal polynomial of a point of l",
								"∃d:A. p = minimal_polynomial(M, K, d) ∧ d ∈ «constants»",
								By(memberParts[0], set_basic.InImage.At(minimalMap, l, p)))
							parts := c.Conjuncts(
								chosen,
								"p is minimal at d",
								"d lies in l")
							dInL := parts[1]
							dataAtD := c.Conjuncts(
								GroupPremises(parts[1], minimalData.At(point)),
								"d lies in M",
								"d is algebraic over K",
								"its minimal polynomial is over K",
								"and separable",
								"and vanishes at d")
							divides := c.Have(
								"X^(q^r) − X vanishes at d, so the minimal polynomial divides it",
								"polynomial_divides(restrict_ring(field_ring(M), K), minimal_polynomial(M, K, d), «Q»)",
								By(
									M,
									KSubfield,
									dInL,
									dataAtD[0],
									dataAtD[1],
									overQ,
									rootsQ.At(point),
									algebraic_element.MinimalPolynomialDivides.At(m, K, point, polynomialQ)))
							cofactor, factors := c.UnpackAs[Fun[Nat, A]](
								c.Unfolded(divides, polynomial_division.PolynomialDividesDef), "s")
							factorParts := c.Conjuncts(
								factors,
								"the cofactor is over K",
								"X^(q^r) − X is the product")
							minimalAtD := c.TermAs[Fun[Nat, A]]("minimal_polynomial(M, K, d)")
							carrier := c.TermAs[Set[A]]("M.carrier")
							zero := c.TermAs[A]("M.zero")
							minimalRoot := c.Have(
								"the minimal polynomial of d vanishes at x",
								"polynomial_eval(minimal_polynomial(M, K, d), x) = M.zero",
								parts[0].RwRev(),
								By(memberParts[1]))
							vanishes := c.Have(
								"X^(q^r) − X is a multiple of p, so it vanishes at x",
								"polynomial_eval(«Q», x) = M.zero",
								factorParts[1].Rw(),
								By(
									xIn,
									minimalRoot,
									dataAtD[2],
									factorParts[0],
									field.SubfieldSubset.At(m, K),
									KSubfield,
									polynomial.PolynomialOverMono.At(zero, K, carrier, minimalAtD),
									polynomial.PolynomialOverMono.At(zero, K, carrier, cofactor),
									polynomial_evaluation.EvalMulRoot.Read(ring).AsFact().At(minimalAtD, cofactor, x)))
							c.Show(
								"the roots of X^(q^r) − X in M are l",
								By(xIn, vanishes, rootsQ.At(x)))
						})
					b.Backward(
						"a point of l is a root of its own minimal polynomial",
						func(c *Argument, inL Fact) {
							dataAtX := c.Conjuncts(
								GroupPremises(inL, minimalData.At(x)),
								"x lies in M",
								"x is algebraic over K",
								"its minimal polynomial is over K",
								"and separable",
								"and vanishes at x")
							c.Show(
								"the minimal polynomial of x lies in the set",
								BySets(inL, dataAtX[0], dataAtX[4]))
						})
				}))
			rootField := a.Have(
				"the roots generate a Galois extension of K",
				"galois_over(M, K, field_adjoin(M, K, «roots»))",
				By(
					KSubfield,
					finite_set.FiniteImage.At(minimalMap, l),
					finiteL,
					inMinimal,
					galois_correspondence.SeparableRootFieldGalois.Read(M).At(K, minimal)))
			sameSet := a.Have(
				"the roots are l",
				"«roots» = «constants»",
				By(pointwise, set_basic.Extension.At(a.TermAs[Set[A]]("«roots»"), l)))
			a.Do(rootField.Simp(Fwd(sameSet)))
			a.Show(
				"the composite is the field of the roots",
				Unfold(constant_composite.ConstantCompositeDef))
		}),
})}

// ConstantTraceForm — the sum of the conjugates over K, read on the field l of
// constants, is a k-linear form on l: an automorphism fixing K sends a root of
// X^(q^r) − X to a root, so it keeps l; the sum lies in l and in K, and a point
// of K algebraic over k lies in k.
var ConstantTraceForm = constantTraceFormThm{family.Add(registry.ProofEntry{
	Name: "ConstantTraceForm",
	Key:  "prop_8fc8a74b3f56ab75",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "composite", Text: "constant_composite(M, K, «constants»)"},
			{Name: "group", Text: "field_automorphisms(M, K, «composite»)"},
			{Name: "trace", Text: "λb:A. " +
				"    module_sum(M.add, M.zero, «group», λg:permutation(A). permutation_map(g, b))"},
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "Q", Text: "basis_vector(card(k) ^ r) - basis_vector(1)"},
		},
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
			"0 < r",
		},
		Conclusion: "finite(«group») ∧ " +
			"galois_over(M, K, «composite») ∧ " +
			"module_homomorphism(«scalars»(K), " +
			"    «vectors»(«composite»), " +
			"    regular_module(«scalars»(K)), " +
			"    «trace») ∧ " +
			"module_homomorphism(«scalars»(k), «vectors»(«constants»), regular_module(«scalars»(k)), «trace»)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			r *Expr[Nat],
			closed, regular, finiteK, positive Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			l := a.TermAs[Set[A]]("«constants»")
			composite := a.TermAs[Set[A]]("«composite»")
			G := a.TermAs[Set[symmetric_group.Permutation[A]]]("«group»")
			trace := a.TermAs[Fun[A, A]]("«trace»")
			polynomialQ := a.TermAs[Fun[Nat, A]]("«Q»")
			kScalars := a.TermAs[module_record.RingOps[A]]("«scalars»(k)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(«constants»)")
			target := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(«scalars»(k))")
			data := a.Conjuncts(
				GroupPremises(M, closed, regular, finiteK, positive, ConstantCompositeData.At(m, K, k, r)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"k is closed in K",
				"l is a subfield",
				"l holds k",
				"l is finite",
				"l is finite over k",
				"the composite is a subfield",
				"it holds K",
				"it holds l")
			kSubfield, KSubfield, kInK, closedInK := data[0], data[1], data[2], data[3]
			lSubfield, kInL, finiteL := data[4], data[5], data[7]
			compositeSubfield, KInC, lInC := data[8], data[9], data[10]
			galois := a.Have(
				"the composite is Galois over K",
				"galois_over(M, K, «composite»)",
				By(M, closed, regular, finiteK, positive, ConstantCompositeGalois.At(m, K, k, r)))
			form := a.Conjuncts(
				GroupPremises(
					data[1], data[8], M, data[9], galois, galois_correspondence.GaloisTraceLinear.At(m, K, composite)),
				"the group is finite",
				"the sum of the conjugates is K-linear")
			finiteG, linear := form[0], form[1]
			lModule := a.Have(
				"l is a module over itself and over k",
				"module_on(«scalars»(«constants»), «vectors»(«constants»)) ∧ "+
					"module_on(«scalars»(k), «vectors»(«constants»))",
				By(
					M,
					lSubfield,
					kSubfield,
					kInL,
					set_order.SubsetRefl.At(l),
					field_extension.ExtensionModuleOn.Read(M).At(l, l),
					field_extension.ExtensionModuleOn.Read(M).At(k, l)))
			moduleOverL := a.Conjuncts(
				lModule,
				"l over itself",
				"l over k")
			baseRing := a.Have(
				"k is a ring under the operations of M",
				"comm_ring_on(«scalars»(k))",
				By(kSubfield, field.SubfieldCommRing.Read(M).At(k)))
			rootData := a.Conjuncts(
				GroupPremises(
					M, data[1], finite_field.FiniteConstantsRootPolynomial.At(m, K, a.TermAs[Nat]("card(k)"), r)),
				"X^(q^r) − X is a polynomial over K",
				"its roots in M are l")
			overQ, rootsQ := rootData[0], rootData[1]
			conjugates := a.Have(
				"an automorphism fixing K keeps l, the roots of a polynomial over K",
				"∀g:permutation(A). ∀b:A. g ∈ «group» ∧ b ∈ «constants» ⇒ permutation_map(g, b) ∈ «constants»",
				Derive(func(c *Argument) {
					g := c.FixAs[symmetric_group.Permutation[A]]("g")
					b := c.FixAs[A]("b")
					members := c.Assume()
					inside := c.Have(
						"b lies in the composite and in M",
						"b ∈ «composite» ∧ b ∈ M.carrier",
						BySets(members, lInC, lSubfield, field.SubfieldSubset.At(m, l)))
					linearG := c.Have(
						"g is linear over K",
						"module_homomorphism(«scalars»(K), "+
							"    «vectors»(«composite»), "+
							"    «vectors»(«composite»), "+
							"    permutation_map(g))",
						By(
							M,
							KSubfield,
							compositeSubfield,
							KInC,
							members,
							field_automorphism.AutomorphismLinear.At(m, K, composite, g)))
					image := c.Have(
						"its image lies in M",
						"permutation_map(g, b) ∈ M.carrier",
						BySets(
							inside,
							module_homomorphism.HomIn.Read(linearG),
							compositeSubfield,
							field.SubfieldSubset.At(m, composite)))
					root := c.Have(
						"and is a root of X^(q^r) − X, as b is",
						"polynomial_eval(«Q», permutation_map(g, b)) = M.zero",
						By(
							M,
							compositeSubfield,
							KInC,
							members,
							overQ,
							inside,
							rootsQ.At(b),
							field_automorphism.AutomorphismPermutesRoots.At(m, K, composite, polynomialQ, g, b)))
					c.Show(
						"the roots of X^(q^r) − X in M are l",
						By(image, root, rootsQ.At(c.TermAs[A]("permutation_map(g, b)"))))
				}))
			inConstants := a.Have(
				"the sum of the conjugates of a point of l lies in k",
				"∀b:A. b ∈ «constants» ⇒ «trace»(b) ∈ k",
				Derive(func(c *Argument) {
					c.FixAs[A]("b")
					inL := c.Assume()
					value := c.TermAs[A]("«trace»(b)")
					evaluate := c.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). permutation_map(g, b)")
					sumIn := c.Have(
						"the sum lies in l",
						"«trace»(b) ∈ «constants»",
						By(finiteG, inL, conjugates, module.ModuleSumIn.Read(moduleOverL[0]).AsFact().At(G, evaluate)))
					inComposite := c.Have(
						"b lies in the composite",
						"b ∈ «composite»",
						BySets(inL, lInC))
					inFunctionField := c.Have(
						"and in K",
						"«trace»(b) ∈ K",
						By(inComposite, module_homomorphism.HomIn.Read(linear)))
					c.Show(
						"a point of K algebraic over k lies in k",
						By(
							M,
							kSubfield,
							lSubfield,
							kInL,
							finiteL,
							sumIn,
							inFunctionField,
							algebraic_element.FiniteExtensionAlgebraic.At(m, k, l, value),
							closedInK.At(value)))
				}))
			adds := a.Have(
				"the form adds on l",
				"∀u v:A. u ∈ «constants» ∧ v ∈ «constants» ⇒ «trace»(u + v) = «trace»(u) + «trace»(v)",
				Derive(func(c *Argument) {
					c.FixAs[A]("u")
					c.FixAs[A]("v")
					members := c.Assume()
					inComposite := c.Have(
						"l lies in the composite",
						"u ∈ «composite» ∧ v ∈ «composite»",
						BySets(members, lInC))
					c.Show(
						"it adds on the composite",
						By(inComposite, module_homomorphism.HomAdd.Read(linear)))
				}))
			scales := a.Have(
				"and takes scalars of k out",
				"∀c u:A. c ∈ k ∧ u ∈ «constants» ⇒ «trace»(c * u) = c * «trace»(u)",
				Derive(func(c *Argument) {
					c.FixAs[A]("c")
					c.FixAs[A]("u")
					members := c.Assume()
					inComposite := c.Have(
						"c lies in K and u in the composite",
						"c ∈ K ∧ u ∈ «composite»",
						BySets(members, kInK, lInC))
					c.Show(
						"k lies in K, and it is K-linear on the composite",
						By(inComposite, module_homomorphism.HomSmul.Read(linear)))
				}))
			a.Show(
				"a finite group, a Galois extension, and a K-linear form restricting to a k-linear form on l",
				By(
					finiteG,
					galois,
					linear,
					moduleOverL[1],
					module.RegularModuleOn.Read(baseRing),
					inConstants,
					adds,
					scales,
					module_homomorphism.ModuleHomomorphismDef.At(kScalars, lVectors, target, trace)))
		}),
})}

// ConstantTraceDual — the sum of the conjugates reads the K-coordinates of the
// composite. Its pairing (u, v) ↦ T(u * v) on l is k-bilinear, and left
// nondegenerate: T is nonzero somewhere (Dedekind), so at some f in the basis E,
// which spans the composite over K, and a nonzero u pairs with u⁻¹ * f to T(f).
// So E has a dual family d in l, and y ↦ T(d(e) * y) and the coordinate at e
// are two K-linear forms on the composite agreeing on E.
var ConstantTraceDual = constantTraceDualThm{family.Add(registry.ProofEntry{
	Name: "ConstantTraceDual",
	Key:  "prop_d9a9d8eadfc4dcfb",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "composite", Text: "constant_composite(M, K, «constants»)"},
			{Name: "group", Text: "field_automorphisms(M, K, «composite»)"},
			{Name: "trace", Text: "λb:A. " +
				"    module_sum(M.add, M.zero, «group», λg:permutation(A). permutation_map(g, b))"},
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "coordinate", Text: "λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(«composite»), E, x, e)"},
			{Name: "pairing", Text: "λu:A. λv:A. «trace»(u * v)"},
			{Name: "kernel", Text: "group_kernel(M.zero, «composite», «trace»)"},
		},
		Binders: "∀M:field_on(A). ∀K k E:set(A). ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
			"0 < r",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(«constants»), E)",
		},
		Conclusion: "∃d:(A → A). " +
			"    (∀e:A. e ∈ E ⇒ d(e) ∈ «constants») ∧ " +
			"    (∀e x:A. e ∈ E ∧ x ∈ «composite» ⇒ «trace»(d(e) * x) = «coordinate»(x, e))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, E *Expr[Set[A]],
			r *Expr[Nat],
			closed, regular, finiteK, positive, finiteE, basis Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			l := a.TermAs[Set[A]]("«constants»")
			composite := a.TermAs[Set[A]]("«composite»")
			trace := a.TermAs[Fun[A, A]]("«trace»")
			kScalars := a.TermAs[module_record.RingOps[A]]("«scalars»(k)")
			KScalars := a.TermAs[module_record.RingOps[A]]("«scalars»(K)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(«constants»)")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(«composite»)")
			kTarget := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(«scalars»(k))")
			KTarget := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(«scalars»(K))")
			kernel := a.TermAs[Set[A]]("«kernel»")
			pairing := a.TermAs[Fun2[A, A, A]]("«pairing»")
			data := a.Conjuncts(
				GroupPremises(M, closed, regular, finiteK, positive, ConstantCompositeData.At(m, K, k, r)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"k is closed in K",
				"l is a subfield",
				"l holds k",
				"l is finite",
				"l is finite over k",
				"the composite is a subfield",
				"it holds K",
				"it holds l")
			kSubfield, KSubfield, lSubfield, kInL := data[0], data[1], data[4], data[5]
			compositeSubfield, KInC, lInC := data[8], data[9], data[10]
			basisData := a.Conjuncts(
				a.Have(
					"E lies in l and stays a basis of the composite over K",
					"E ⊆ «constants» ∧ "+
						"module_on(«scalars»(K), «vectors»(«composite»)) ∧ "+
						"module_basis(«scalars»(K), «vectors»(«composite»), E)",
					By(
						M,
						regular,
						lSubfield,
						kInL,
						finiteE,
						basis,
						constant_composite.ConstantExtensionData.At(m, K, k, l, E))),
				"E lies in l",
				"the composite is a module over K",
				"with basis E")
			EInL, compositeModule, compositeBasis := basisData[0], basisData[1], basisData[2]
			form := a.Conjuncts(
				GroupPremises(M, closed, regular, finiteK, positive, ConstantTraceForm.At(m, K, k, r)),
				"the group is finite",
				"the composite is Galois over K",
				"the sum of the conjugates is K-linear",
				"and a k-linear form on l")
			linear, formOnL := form[2], form[3]
			spans := a.Conjuncts(
				a.Unfolded(compositeBasis, linear_independence.ModuleBasisDef),
				"E is independent over K",
				"E spans the composite over K")[1]
			inComposite := a.Have(
				"l and E lie in the composite",
				"E ⊆ «composite»",
				BySets(EInL, lInC))
			_, nonzero := a.UnpackAs[A](
				GroupPremises(
					data[1], data[8], M, data[9], form[0], field_automorphism.GaloisTraceNonzero.At(m, K, composite)),
				"b")
			f, onBasis := a.ObtainAs[A](
				"the form does not vanish on all of E, which spans the composite",
				"∃f:A. f ∈ E ∧ «trace»(f) ≠ M.zero",
				Derive(func(c *Argument) {
					none := c.SupposeNot()
					kernelPoints := c.Have(
						"the kernel is the set of zeros of the form",
						"«kernel» = {y:A | y ∈ «composite» ∧ «trace»(y) = M.zero}",
						By(group_homomorphism.GroupKernelDef.At(c.TermAs[A]("M.zero"), composite, trace)))
					vanishes := c.Have(
						"then every member of E lies in the kernel",
						"E ⊆ «kernel»",
						BySets(none, inComposite, kernelPoints))
					kernelSubmodule := c.Have(
						"the kernel is a submodule",
						"submodule(«scalars»(K), «vectors»(«composite»), «kernel»)",
						By(linear, module_homomorphism.KernelSubmodule.At(KScalars, compositeVectors, KTarget, trace)))
					inKernel := c.Have(
						"so it holds the span of E",
						"module_span(«scalars»(K), «vectors»(«composite»), E) ⊆ «kernel»",
						By(kernelSubmodule, vanishes, submodule.SpanLeast.At(KScalars, compositeVectors, E, kernel)))
					c.Show(
						"and b would be a zero of the form",
						BySets(nonzero, spans, inKernel, kernelPoints))
				}))
			onBasisParts := a.Conjuncts(
				onBasis,
				"f lies in E",
				"the form is nonzero at f")
			fInL := a.Have(
				"f lies in l",
				"f ∈ «constants»",
				BySets(onBasisParts[0], EInL))
			leftSlices := a.Have(
				"multiplying by a point of l and summing the conjugates is a k-linear form",
				Statement{
					Binders:    "∀u:A.",
					Hypotheses: []string{"u ∈ «constants»"},
					Conclusion: "module_homomorphism(«scalars»(k), " +
						"    «vectors»(«constants»), " +
						"    regular_module(«scalars»(k)), " +
						"    λv:A. «trace»(u * v))",
				},
				Derive(func(c *Argument) {
					u := c.FixAs[A]("u")
					inL := c.Assume()
					c.Show(
						"a linear form twisted by a point",
						By(
							M,
							kSubfield,
							lSubfield,
							kInL,
							formOnL,
							inL,
							field_extension.ProductFormLinear.At(m, k, l, trace, u)))
				}))
			inField := a.Have(
				"l lies in M",
				"«constants» ⊆ M.carrier",
				By(lSubfield, field.SubfieldSubset.At(m, l)))
			rightSlices := a.Have(
				"the pairing is symmetric, so its other slices are linear forms too",
				Statement{
					Binders:    "∀v:A.",
					Hypotheses: []string{"v ∈ «constants»"},
					Conclusion: "module_homomorphism(«scalars»(k), " +
						"    «vectors»(«constants»), " +
						"    regular_module(«scalars»(k)), " +
						"    λu:A. «trace»(u * v))",
				},
				Derive(func(c *Argument) {
					v := c.FixAs[A]("v")
					inL := c.Assume()
					left := c.TermAs[Fun[A, A]]("λu:A. «trace»(v * u)")
					right := c.TermAs[Fun[A, A]]("λu:A. «trace»(u * v)")
					swap := c.Have(
						"the two slices agree on l",
						"∀u:A. u ∈ «constants» ⇒ «trace»(u * v) = «trace»(v * u)",
						Derive(func(d *Argument) {
							d.FixAs[A]("u")
							members := d.Have(
								"both factors lie in M",
								"u ∈ M.carrier ∧ v ∈ M.carrier",
								BySets(d.Assume(), inL, inField))
							commute := d.Have(
								"the product commutes",
								"u * v = v * u",
								ByArith(M, members))
							d.Show(
								"the same product",
								commute.Rw(),
								Basic())
						}))
					c.Show(
						"a map agreeing with a linear form on l is one",
						By(
							leftSlices.At(v),
							inL,
							swap,
							module_homomorphism.HomCongruence.At(kScalars, lVectors, kTarget, left, right)))
				}))
			bilinear := a.Have(
				"the pairing is bilinear over k",
				"bilinear_pairing(«scalars»(k), «vectors»(«constants»), «pairing»)",
				By(leftSlices, rightSlices, linear_pairing.BilinearPairingDef.At(kScalars, lVectors, pairing)))
			nondegenerate := a.Have(
				"a nonzero point of l pairs with its inverse times f to the nonzero value at f",
				"pairing_nondegenerate(«scalars»(k), «vectors»(«constants»), «pairing»)",
				Derive(func(c *Argument) {
					c.Do(Simp(Fwd(linear_pairing.PairingNondegenerateDef)))
					u := c.FixAs[A]("u")
					guards := c.Conjuncts(
						c.Assume(),
						"u lies in l",
						"u is not zero")
					uIn, uNonzero := guards[0], guards[1]
					inverse := c.TermAs[A]("M.inv(u)")
					members := c.Have(
						"u, its inverse and f lie in l",
						"M.inv(u) ∈ «constants» ∧ "+
							"M.inv(u) * f ∈ «constants» ∧ "+
							"u ∈ M.carrier ∧ "+
							"M.inv(u) ∈ M.carrier ∧ "+
							"f ∈ M.carrier",
						BySets(
							uIn,
							fInL,
							inField,
							lSubfield,
							field.SubfieldInv.At(m, l, u),
							field.SubfieldMul.At(m, l, inverse, f)))
					rightInverse := c.Have(
						"u times its inverse is one",
						"u * M.inv(u) = M.one",
						By(M, members, uNonzero, field.MulRightInverseOn.Read(M).AsFact().At(u)))
					cancels := c.Have(
						"u cancels its inverse",
						"u * (M.inv(u) * f) = f",
						ByArith(M, members, Scaled(f, rightInverse)))
					c.Take(c.TermAs[A]("M.inv(u) * f"))
					c.Show(
						"the pairing at that point is the value at f",
						cancels.Rw(),
						By(members, onBasisParts[1]))
				}))
			kField := a.Have(
				"k is a field under the operations of M",
				"field_on(restrict_field(M, k))",
				By(M, kSubfield, field.SubfieldFieldOn.Read(M).At(k)))
			ringEquation := a.Have(
				"its ring is the restriction of M's",
				"«scalars»(k) = field_ring(restrict_field(M, k))",
				By(field.RestrictFieldRing.At(m, k)))
			pairingData := a.Have(
				"the pairing's data, read over the field k",
				"module_on(field_ring(restrict_field(M, k)), «vectors»(«constants»)) ∧ "+
					"bilinear_pairing(field_ring(restrict_field(M, k)), «vectors»(«constants»), «pairing») ∧ "+
					"pairing_nondegenerate(field_ring(restrict_field(M, k)), «vectors»(«constants»), «pairing») ∧ "+
					"module_basis(field_ring(restrict_field(M, k)), «vectors»(«constants»), E)",
				ringEquation.RwRev(),
				By(formOnL, module_homomorphism.HomSource.Read(formOnL), bilinear, nondegenerate, basis))
			d, dual := a.UnpackAs[Fun[A, A]](
				GroupPremises(
					finiteE,
					kField,
					pairingData,
					linear_pairing.NondegeneratePairingDualBasis.At(
						a.TermAs[FieldOps[A]]("restrict_field(M, k)"), lVectors, pairing, E)),
				"d")
			dualParts := a.Conjuncts(
				dual,
				"d lands in l",
				"d is dual to E under the pairing",
				"the image of d is a basis",
				"every element of l expands in it",
				"and d is the only such family")
			inL, dualToE := dualParts[0], dualParts[1]
			coordinates := a.Have(
				"the sum of the conjugates of d(e) * x is the coordinate of x at e",
				"∀e x:A. e ∈ E ∧ x ∈ «composite» ⇒ «trace»(d(e) * x) = «coordinate»(x, e)",
				Derive(func(c *Argument) {
					e := c.FixAs[A]("e")
					x := c.FixAs[A]("x")
					members := c.Assume()
					de := c.TermAs[A]("d(e)")
					twisted := c.TermAs[Fun[A, A]]("λy:A. «trace»(d(e) * y)")
					coordinate := c.TermAs[Fun[A, A]]("λy:A. «coordinate»(y, e)")
					dInComposite := c.Have(
						"d(e) lies in the composite",
						"d(e) ∈ «composite»",
						BySets(members, inL.At(e), lInC))
					twistedLinear := c.Have(
						"y ↦ T(d(e) * y) is K-linear",
						"module_homomorphism(«scalars»(K), "+
							"    «vectors»(«composite»), "+
							"    regular_module(«scalars»(K)), "+
							"    λy:A. «trace»(d(e) * y))",
						By(
							M,
							KSubfield,
							compositeSubfield,
							KInC,
							linear,
							dInComposite,
							field_extension.ProductFormLinear.At(m, K, composite, trace, de)))
					coordinateLinear := c.Have(
						"the coordinate at e is K-linear",
						"module_homomorphism(«scalars»(K), "+
							"    «vectors»(«composite»), "+
							"    regular_module(«scalars»(K)), "+
							"    λy:A. «coordinate»(y, e))",
						By(
							compositeModule,
							finiteE,
							compositeBasis,
							members,
							module_dimension.BasisCoordinateLinear.At(KScalars, compositeVectors, E, e)))
					agree := c.Have(
						"they agree on E",
						"∀g:A. g ∈ E ⇒ «trace»(d(e) * g) = «coordinate»(g, e)",
						Derive(func(h *Argument) {
							g := h.FixAs[A]("g")
							gIn := h.Assume()
							delta := h.Have(
								"a basis vector has a Kronecker coordinate",
								"module_basis_coordinates(«scalars»(K), «vectors»(«composite»), E, g) = "+
									"λy:A. COND(y = g, M.one, M.zero)",
								By(
									compositeModule,
									finiteE,
									compositeBasis,
									gIn,
									module_dimension.BasisCoordinateDelta.At(KScalars, compositeVectors, E, g)))
							h.Show(
								"both are the delta of e and g",
								delta.Rw(),
								By(members, gIn, dualToE.At(e, g)))
						}))
					c.Show(
						"two linear forms agreeing on a spanning set agree",
						By(
							twistedLinear,
							coordinateLinear,
							inComposite,
							agree,
							members,
							spans,
							linear_independence.HomAgreeOnSpan.At(
								KScalars, compositeVectors, KTarget, twisted, coordinate, E, x)))
				}))
			a.Take(d)
			a.Show(
				"the dual family",
				By(inL, coordinates))
		}),
})}
