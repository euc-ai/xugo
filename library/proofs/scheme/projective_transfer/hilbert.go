// hilbert.go — two stories: carrying the coefficients of polynomials along
// ι, an isomorphism of the polynomials over k onto those over ι(k) that keeps
// the forms of each degree; and the Hilbert function and genus of a set of
// equations, which carrying it along ι keeps.

package projective_transfer

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CarriedPolynomials — ι is an isomorphism of k onto ι(k), so «carried» is an
// isomorphism of the polynomials over k onto the polynomials over ι(k), and
// it takes the forms of each degree onto the forms of that degree. ι is one
// to one on k (SubfieldHomomorphismEmbedding); «carried» is
// polynomial_algebra.PolynomialAlgebraMapIsomorphism along it; a coefficient
// of a polynomial over k vanishes exactly where its carried coefficient does,
// so a polynomial over k is a form of degree d exactly when its carried
// polynomial is, and every form over ι(k), a polynomial over ι(k), is carried
// from a polynomial over k.
var CarriedPolynomials = carriedPolynomialsThm{family.Add(registry.ProofEntry{
	Name: "CarriedPolynomials",
	Key:  "prop_a7e4f7982052d1ad",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀N:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀n:num.",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"subfield(M, k)",
		},
		Conclusion: "ring_isomorphism(«hilbertCoefficients», «carriedCoefficients», ι) ∧ " +
			"ring_isomorphism(«polynomials», «carriedPolynomials», «carried») ∧ " +
			"(∀d:num. image(«carried», «forms»(d)) = «carriedForms»(d))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		N field.FieldFact[on.N],
		ι *Arrow[A, B],
		k *Expr[Set[A]],
		n *Expr[Nat],
		hom, subK Fact,
	) {
		type polynomial = Fun[Fun[Nat, Nat], A]
		type carriedPolynomial = Fun[Fun[Nat, Nat], B]
		fieldN := a.TermAs[FieldOps[B]]("N")
		ringM := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		ringN := a.TermAs[module_record.RingOps[B]]("field_ring(N)")
		kRing := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		carriedKRing := a.TermAs[module_record.RingOps[B]]("«carriedCoefficients»")
		carriedK := a.TermAs[Set[B]]("image(ι, k)")
		variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		polynomialsOverK := a.TermAs[Set[polynomial]](
			"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})")
		carried := a.TermAs[Fun[polynomial, carriedPolynomial]]("«carried»")
		onK := a.Have(
			"ι is a ring homomorphism on k",
			"ring_homomorphism(«hilbertCoefficients», field_ring(N), ι)",
			By(
				hom,
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.RingHomRestrictSource.At(ringM, ringN, ι, k)))
		embedding := a.Conjuncts(
			GroupPremises(
				N, subK, onK, ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(fieldN, k, ι)),
			"ι(k) is a subfield of N",
			"ι is one to one on k")
		coefficients := a.Have(
			"so ι is an isomorphism of k onto ι(k)",
			"ring_isomorphism(«hilbertCoefficients», «carriedCoefficients», ι)",
			By(
				onK,
				embedding[0],
				embedding[1],
				field.SubfieldSubring.Read(N).At(carriedK),
				ring_homomorphism.RingHomCorestrict.At(kRing, ringN, ι, carriedK),
				ring_homomorphism.RingIsomorphismDef.At(kRing, carriedKRing, ι),
				set_image.FunInImage))
		isomorphism := a.Have(
			"and «carried» is an isomorphism of the polynomials over k onto those over ι(k)",
			"ring_isomorphism(«polynomials», «carriedPolynomials», «carried»)",
			By(
				coefficients,
				polynomial_algebra.PolynomialAlgebraMapIsomorphism.At(kRing, carriedKRing, ι, variables)))
		carriedIso := a.Conjuncts(
			a.Unfolded(isomorphism, ring_homomorphism.RingIsomorphismDef),
			"«carried» is a ring homomorphism",
			"one to one on the polynomials over k",
			"onto the polynomials over ι(k)")
		vanishing := a.Have(
			"a coefficient of a polynomial over k vanishes exactly "+
				"where its carried coefficient does, ι being one to one on k",
			Statement{
				Binders: "∀P:((num → num) → A). ∀m:(num → num).",
				Hypotheses: []string{
					"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
				},
				Conclusion: "ι(P(m)) = N.zero ⇔ P(m) = M.zero",
			},
			Derive(func(b *Argument) {
				P := b.FixAs[polynomial]("P")
				b.FixAs[Fun[Nat, Nat]]("m")
				member := b.Assume()
				b.Show(
					"P(m) lies in k, where ι sends only zero to zero",
					By(
						member,
						embedding[1],
						polynomial_algebra.PolynomialAlgebraMember.At(kRing, variables, P),
						ring_homomorphism.ZeroIffImageZero.Read(onK).AsFact().At(b.TermAs[A]("P(m)"))))
			}))
		forms := a.Have(
			"so «carried» takes the forms of degree d over k onto those over ι(k)",
			"∀d:num. image(«carried», «forms»(d)) = «carriedForms»(d)",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				homogeneous := b.Have(
					"a polynomial over k is a form of degree d exactly when its carried polynomial is",
					Statement{
						Binders: "∀P:((num → num) → A).",
						Hypotheses: []string{
							"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
						},
						Conclusion: "homogeneous_polynomial(«carriedCoefficients», n, d, «carried»(P)) ⇔ " +
							"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					},
					Derive(func(c *Argument) {
						P := c.FixAs[polynomial]("P")
						member := c.Assume()
						c.Show(
							"a coefficient of P vanishes exactly where its carried "+
								"coefficient does, and «carried»(P) is a polynomial over ι(k)",
							By(
								vanishing,
								member,
								carriedIso[2],
								set_image.FunInImage.At(carried, polynomialsOverK, P),
								homogeneous_polynomial.HomogeneousPolynomialDef.At(
									carriedKRing, n, d, c.TermAs[carriedPolynomial]("«carried»(P)")),
								homogeneous_polynomial.HomogeneousPolynomialDef.At(kRing, n, d, P)))
					}))
				into := b.Have(
					"a carried form of degree d is a form of degree d",
					"image(«carried», «forms»(d)) ⊆ «carriedForms»(d)",
					BySets(homogeneous, homogeneous_polynomial.FormPolynomial))
				onto := b.Have(
					"and every form of degree d over ι(k) is carried from one over k",
					"«carriedForms»(d) ⊆ image(«carried», «forms»(d))",
					Simp(Fwd(set_basic.SubsetDef)),
					Derive(func(c *Argument) {
						Q := c.FixAs[carriedPolynomial]("Q")
						form := c.Assume()
						_, preimage := c.ObtainAs[polynomial](
							"a form over ι(k) is a polynomial over ι(k), so carried from a polynomial over k",
							"∃P:((num → num) → A). "+
								"    P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ Q = «carried»(P)",
							By(
								form,
								carriedIso[2],
								homogeneous_polynomial.FormPolynomial.At(carriedKRing, n, d, Q),
								set_basic.InImage.At(carried, polynomialsOverK, Q)))
						c.Show(
							"and that polynomial is a form of degree d, as its carried polynomial is",
							By(
								homogeneous,
								form,
								preimage,
								set_basic.InImage.At(carried, c.TermAs[Set[polynomial]]("«forms»(d)"), Q)))
					}))
				b.Show(
					"the two inclusions give the equation",
					By(into, onto, set_order.SubsetAntisym))
			}))
		a.Show(
			"ι is an isomorphism on k, «carried» one on the polynomials, keeping the forms of each degree",
			By(coefficients, isomorphism, forms))
	}),
})}

// CarriedIdealFormsDimension — the forms of degree d in the ideal E spans
// over k and the forms of degree d in the ideal the carried equations span
// over ι(k) have one dimension. «carried» takes the first layer one to one
// onto the second: it keeps forms of each degree and takes the ideal E spans
// to the ideal of the carried equations (CarriedPolynomials,
// ring_homomorphism.IdealSpanImage), both within the polynomials over k where
// it is one to one (ImageInterInjOn). On the polynomials over k it is
// additive and carries c·u to ι(c)·«carried»(u): a linear isomorphism over k
// onto the second layer read over k through ι. So the second layer, read so,
// has the first's dimension (IsomorphicDim), which is its dimension over ι(k)
// (module_dimension.ScalarRestrictionDim).
var CarriedIdealFormsDimension = carriedIdealFormsDimensionThm{family.Add(registry.ProofEntry{
	Name: "CarriedIdealFormsDimension",
	Key:  "prop_d43303b9efdc1863",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀N:field_on(B). " +
			"∀ι:(A → B). " +
			"∀k:set(A). " +
			"∀n d:num. " +
			"∀E:set((num → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"subfield(M, k)",
			"E ⊆ «polynomials».carrier",
		},
		Conclusion: "module_dim(«carriedCoefficients», «carriedIdealForms») = " +
			"module_dim(«hilbertCoefficients», «idealForms»)",
		Abbrev: Abbrev{
			{Name: "formSpace", Text: "mk_module(fun_add(M.add), " +
				"    fun_zero(M.zero), " +
				"    fun_neg(M.neg), " +
				"    λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"    «forms»(d))"},
			{Name: "idealForms", Text: "restrict_module(«formSpace», " +
				"    «forms»(d) ∩ ideal_span(«polynomials», E))"},
			{Name: "carriedFormSpace", Text: "mk_module(fun_add(N.add), " +
				"    fun_zero(N.zero), " +
				"    fun_neg(N.neg), " +
				"    λb:B. λQ:((num → num) → B). λm:(num → num). b * Q(m), " +
				"    «carriedForms»(d))"},
			{Name: "carriedIdealForms", Text: "restrict_module(«carriedFormSpace», " +
				"    «carriedForms»(d) ∩ ideal_span(«carriedPolynomials», image(«carried», E)))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		N field.FieldFact[on.N],
		ι *Arrow[A, B],
		k *Expr[Set[A]],
		n, d *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		hom, subK, equationsOverK Fact,
	) {
		type polynomial = Fun[Fun[Nat, Nat], A]
		type carriedPolynomial = Fun[Fun[Nat, Nat], B]
		fieldN := a.TermAs[FieldOps[B]]("N")
		ringN := a.TermAs[module_record.RingOps[B]]("field_ring(N)")
		kRing := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		polynomialsOverK := a.TermAs[Set[polynomial]](
			"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})")
		carried := a.TermAs[Fun[polynomial, carriedPolynomial]]("«carried»")
		first := a.TermAs[module_record.ModuleOps[A, polynomial]]("«idealForms»")
		second := a.TermAs[module_record.ModuleOps[B, carriedPolynomial]]("«carriedIdealForms»")
		secondOverK := a.TermAs[module_record.ModuleOps[A, carriedPolynomial]](
			"scalar_restriction(ι, «carriedIdealForms»)")
		onK := a.Have(
			"ι is a ring homomorphism on k",
			"ring_homomorphism(«hilbertCoefficients», field_ring(N), ι)",
			By(
				hom,
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.RingHomRestrictSource.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(M)"), ringN, ι, k)))
		embedding := a.Conjuncts(
			GroupPremises(
				N, subK, onK, ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(fieldN, k, ι)),
			"ι(k) is a subfield of N",
			"ι is one to one on k")
		transfer := a.Conjuncts(
			GroupPremises(M, N, hom, subK, CarriedPolynomials.At(a.TermAs[FieldOps[A]]("M"), fieldN, ι, k, n)),
			"ι is an isomorphism of k onto ι(k)",
			"«carried» is an isomorphism of the polynomials over k onto those over ι(k)",
			"taking the forms of each degree onto the forms of that degree")
		carriedIso := a.Conjuncts(
			a.Unfolded(transfer[1], ring_homomorphism.RingIsomorphismDef),
			"«carried» is a ring homomorphism",
			"one to one on the polynomials over k",
			"onto the polynomials over ι(k)")
		carriedHom, oneToOne := carriedIso[0], carriedIso[1]
		polynomialsRing := a.Have(
			"the polynomials over k are a commutative ring",
			"comm_ring_on(«polynomials»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k), polynomial_algebra.PolynomialAlgebraCommRingOn))
		idealIsIdeal := a.Have(
			"E spans an ideal of the polynomials over k",
			"ring_ideal(«polynomials», ideal_span(«polynomials», E))",
			By(equationsOverK, ring_ideal.SpanIdeal.Read(polynomialsRing)))
		firstModule := a.Have(
			"the first layer is a space over k",
			"module_on(«hilbertCoefficients», «idealForms»)",
			Derive(func(b *Argument) {
				firstSpace := b.Have(
					"the forms of degree d over k are a space over k, the first layer a subspace",
					"module_on(«hilbertCoefficients», «formSpace») ∧ "+
						"submodule(«hilbertCoefficients», «formSpace», «forms»(d) ∩ ideal_span(«polynomials», E))",
					By(subK, idealIsIdeal, projective_curve.FormsSubspace.Read(M).At(k, n, d)))
				b.Show(
					"a subspace is a space",
					By(firstSpace, submodule.SubmoduleModuleOn))
			}))
		secondOverKModule := a.Have(
			"the second layer is a space over ι(k), and so over k acting through ι",
			"module_on(«hilbertCoefficients», scalar_restriction(ι, «carriedIdealForms»))",
			Derive(func(b *Argument) {
				carriedK := b.TermAs[Set[B]]("image(ι, k)")
				carriedPolynomialsRing := b.Have(
					"the polynomials over ι(k) are a commutative ring",
					"comm_ring_on(«carriedPolynomials»)",
					By(
						embedding[0],
						field.SubfieldCommRing.Read(N).At(carriedK),
						polynomial_algebra.PolynomialAlgebraCommRingOn))
				carriedEquations := b.Have(
					"the carried equations are polynomials over ι(k)",
					"image(«carried», E) ⊆ «carriedPolynomials».carrier",
					By(
						equationsOverK,
						ring_homomorphism.MapIn.Read(carriedHom),
						set_image.ImageSubsetIff,
						set_basic.SubsetDef))
				secondSpace := b.Have(
					"the forms of degree d over ι(k) are a space over ι(k), the second layer a subspace",
					"module_on(«carriedCoefficients», «carriedFormSpace») ∧ "+
						"submodule(«carriedCoefficients», "+
						"    «carriedFormSpace», "+
						"    «carriedForms»(d) ∩ ideal_span(«carriedPolynomials», image(«carried», E)))",
					By(
						embedding[0],
						carriedEquations,
						projective_curve.FormsSubspace.Read(N).At(carriedK, n, d),
						ring_ideal.SpanIdeal.Read(carriedPolynomialsRing)))
				secondModule := b.Have(
					"so the second layer is a space over ι(k)",
					"module_on(«carriedCoefficients», «carriedIdealForms»)",
					By(secondSpace, submodule.SubmoduleModuleOn))
				coefficientsHom := b.Conjuncts(
					b.Unfolded(transfer[0], ring_homomorphism.RingIsomorphismDef),
					"ι is a ring homomorphism of k to ι(k)",
					"one to one on k",
					"onto ι(k)")[0]
				b.Show(
					"read over k acting through ι, a ring homomorphism of k to ι(k)",
					By(
						coefficientsHom,
						secondModule,
						hom_module.RestrictScalarsModuleOn.At(
							kRing, b.TermAs[module_record.RingOps[B]]("«carriedCoefficients»"), ι, second)))
			}))
		layerImage := a.Have(
			"«carried» takes the first layer onto the second",
			"image(«carried», «forms»(d) ∩ ideal_span(«polynomials», E)) = "+
				"«carriedForms»(d) ∩ ideal_span(«carriedPolynomials», image(«carried», E))",
			Derive(func(b *Argument) {
				polynomials := b.TermAs[module_record.RingOps[polynomial]]("«polynomials»")
				idealK := b.TermAs[Set[polynomial]]("ideal_span(«polynomials», E)")
				idealImage := b.Have(
					"it takes the ideal E spans to the ideal the carried equations span",
					"image(«carried», ideal_span(«polynomials», E)) = "+
						"ideal_span(«carriedPolynomials», image(«carried», E))",
					By(
						transfer[1],
						equationsOverK,
						ring_homomorphism.IdealSpanImage.At(
							polynomials,
							b.TermAs[module_record.RingOps[carriedPolynomial]]("«carriedPolynomials»"),
							carried,
							E)))
				formsInside := b.Have(
					"the forms of degree d are polynomials over k",
					"«forms»(d) ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					BySets(homogeneous_polynomial.FormPolynomial))
				idealInside := b.Have(
					"and so are the members of the ideal",
					"ideal_span(«polynomials», E) ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(idealIsIdeal, ring_ideal.IdealSubset.At(polynomials, idealK)))
				b.Show(
					"it takes the forms of degree d onto the forms of degree d, "+
						"one to one on the polynomials over k, which hold both sets",
					By(
						oneToOne,
						formsInside,
						idealInside,
						transfer[2],
						idealImage,
						set_image.ImageInterInjOn.At(
							carried, b.TermAs[Set[polynomial]]("«forms»(d)"), idealK, polynomialsOverK)))
			}))
		isomorphism := a.Have(
			"«carried» is linear over k acting through ι, so a linear "+
				"isomorphism of the first layer onto the second read over k",
			"module_isomorphism(«hilbertCoefficients», "+
				"    «idealForms», "+
				"    scalar_restriction(ι, «carriedIdealForms»), "+
				"    «carried»)",
			Derive(func(b *Argument) {
				layer := b.TermAs[Set[polynomial]]("«forms»(d) ∩ ideal_span(«polynomials», E)")
				layerInside := b.Have(
					"the first layer lies among the polynomials over k",
					"«forms»(d) ∩ ideal_span(«polynomials», E) ⊆ "+
						"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					BySets(homogeneous_polynomial.FormPolynomial))
				additive := b.Have(
					"«carried» is additive on the polynomials over k, a ring homomorphism",
					Statement{
						Binders: "∀u v:((num → num) → A).",
						Hypotheses: []string{
							"u ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
							"v ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
						},
						Conclusion: "«carried»(fun_add(M.add, u, v)) = fun_add(N.add, «carried»(u), «carried»(v))",
					},
					Derive(func(c *Argument) {
						u := c.FixAs[polynomial]("u")
						v := c.FixAs[polynomial]("v")
						members := c.Assume()
						c.Show(
							"«carried»(u + v) = «carried»(u) + «carried»(v)",
							By(members, ring_homomorphism.MapAdd.Read(carriedHom).AsFact().At(u, v)))
					}))
				scaling := b.Have(
					"and takes c·u to ι(c)·«carried»(u) for c in k",
					Statement{
						Binders: "∀c:A. ∀u:((num → num) → A).",
						Hypotheses: []string{
							"c ∈ k",
							"u ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
						},
						Conclusion: "«carried»(λm:(num → num). c * u(m)) = (λm:(num → num). ι(c) * «carried»(u, m))",
					},
					Derive(func(c *Argument) {
						scalar := c.FixAs[A]("c")
						u := c.FixAs[polynomial]("u")
						given := c.Assume()
						c.Do(Funext())
						c.FixAs[Fun[Nat, Nat]]("m")
						c.Show(
							"ι(c·u(m)) = ι(c)·ι(u(m)), c and u(m) lying in k",
							By(
								given,
								polynomial_algebra.PolynomialAlgebraMember.At(kRing, c.TermAs[Set[Nat]]("{i:num | i ≤ n}"), u),
								ring_homomorphism.MapMul.Read(onK).AsFact().At(scalar, c.TermAs[A]("u(m)"))))
					}))
				mapsInto := b.Have(
					"«carried» takes the first layer into the second",
					Statement{
						Binders: "∀u:((num → num) → A).",
						Hypotheses: []string{
							"u ∈ «forms»(d) ∩ ideal_span(«polynomials», E)",
						},
						Conclusion: "«carried»(u) ∈ " +
							"«carriedForms»(d) ∩ ideal_span(«carriedPolynomials», image(«carried», E))",
					},
					By(layerImage, set_image.FunInImage))
				linear := b.Have(
					"so «carried» is linear over k from the first layer to the second read through ι",
					"module_homomorphism(«hilbertCoefficients», "+
						"    «idealForms», "+
						"    scalar_restriction(ι, «carriedIdealForms»), "+
						"    «carried»)",
					Simp(Fwd(module_homomorphism.ModuleHomomorphismDef), Fwd(module_record.ScalarRestrictionDef)),
					By(
						firstModule,
						secondOverKModule,
						module_record.ScalarRestrictionDef.At(ι, second),
						mapsInto,
						layerInside,
						set_basic.SubsetDef.At(layer, polynomialsOverK),
						additive,
						scaling))
				oneToOneOnLayer := b.Have(
					"and one to one on the first layer, which lies among the polynomials over k",
					"injective_on(«forms»(d) ∩ ideal_span(«polynomials», E), «carried»)",
					By(oneToOne, layerInside, functions.InjectiveOnSubset.At(carried, layer, polynomialsOverK)))
				b.Show(
					"a linear map one to one on the first layer and onto the second",
					By(
						linear,
						oneToOneOnLayer,
						layerImage,
						module_homomorphism.ModuleIsomorphismDef.At(kRing, first, secondOverK, carried),
						module_record.ScalarRestrictionDef.At(ι, second)))
			}))
		readOverK := a.Have(
			"so the second layer read over k has the first's dimension",
			"module_dim(«hilbertCoefficients», scalar_restriction(ι, «carriedIdealForms»)) = "+
				"module_dim(«hilbertCoefficients», «idealForms»)",
			Derive(func(b *Argument) {
				finite := b.Have(
					"the first layer is finite-dimensional",
					"finite_dimensional(«hilbertCoefficients», «idealForms»)",
					By(subK, equationsOverK, projective_curve.HilbertFunctionCodimension.Read(M).At(k, n, d, E)))
				kField := b.Have(
					"k is a field",
					"ring_subfield(«hilbertCoefficients», M.inv, k)",
					By(subK, field.SubfieldRingSubfield.Read(M).At(k, k)))
				b.Show(
					"over the field k, a space isomorphic to a finite-dimensional one has its dimension",
					By(
						isomorphism,
						kField,
						finite,
						firstModule,
						secondOverKModule,
						module_dimension.IsomorphicDim.At(kRing, first, b.TermAs[Fun[A, A]]("M.inv"), secondOverK),
						module_homomorphism.ModuleIsomorphicDef.At(kRing, first, secondOverK)))
			}))
		a.Show(
			"which is its dimension over ι(k), the image of k under the one-to-one ι",
			By(onK, embedding[1], readOverK, module_dimension.ScalarRestrictionDim.At(kRing, ringN, ι, second)))
	}),
})}

// CarriedHilbertFunction — carried along ι, a set of equations over k keeps
// its Hilbert function at every degree, and so its genus. At degree d each
// Hilbert function is binomial(d + n, n) less the dimension of its ideal's
// forms of degree d (projective_curve.HilbertFunctionCodimension, over k and
// over ι(k), a subfield of N), and those two dimensions agree
// (CarriedIdealFormsDimension). The genus reads only the Hilbert function.
var CarriedHilbertFunction = carriedHilbertFunctionThm{family.Add(registry.ProofEntry{
	Name: "CarriedHilbertFunction",
	Key:  "prop_9f6690940e641ba",
	Reading: "E ⊆ «polynomials».carrier is load-bearing: a set reaching outside the polynomials over " +
		"k is held by no ideal of them, so the ideal it spans is the whole type and its Hilbert function " +
		"zero, while «carried», unconstrained off them, may carry it among the polynomials over ι(k).",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀N:field_on(B). " +
			"∀ι:(A → B). " +
			"∀k:set(A). " +
			"∀n:num. " +
			"∀E:set((num → num) → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"subfield(M, k)",
			"E ⊆ «polynomials».carrier",
		},
		Conclusion: "(∀d:num. " +
			"    projective_hilbert_function(field_ring(N), image(ι, k), n, image(«carried», E), d) = " +
			"    projective_hilbert_function(field_ring(M), k, n, E, d)) ∧ " +
			"projective_equation_genus(field_ring(N), image(ι, k), n, image(«carried», E)) = " +
			"projective_equation_genus(field_ring(M), k, n, E)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		N field.FieldFact[on.N],
		ι *Arrow[A, B],
		k *Expr[Set[A]],
		n *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		hom, subK, equationsOverK Fact,
	) {
		type carriedPolynomial = Fun[Fun[Nat, Nat], B]
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldN := a.TermAs[FieldOps[B]]("N")
		ringM := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		ringN := a.TermAs[module_record.RingOps[B]]("field_ring(N)")
		carriedK := a.TermAs[Set[B]]("image(ι, k)")
		carriedE := a.TermAs[Set[carriedPolynomial]]("image(«carried», E)")
		onK := a.Have(
			"ι is a ring homomorphism on k",
			"ring_homomorphism(«hilbertCoefficients», field_ring(N), ι)",
			By(
				hom,
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.RingHomRestrictSource.At(ringM, ringN, ι, k)))
		embedding := a.Conjuncts(
			GroupPremises(
				N, subK, onK, ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(fieldN, k, ι)),
			"ι(k) is a subfield of N",
			"ι is one to one on k")
		transfer := a.Conjuncts(
			GroupPremises(M, N, hom, subK, CarriedPolynomials.At(fieldM, fieldN, ι, k, n)),
			"ι is an isomorphism of k onto ι(k)",
			"«carried» is an isomorphism of the polynomials over k onto those over ι(k)",
			"taking the forms of each degree onto the forms of that degree")
		carriedHom := a.Conjuncts(
			a.Unfolded(transfer[1], ring_homomorphism.RingIsomorphismDef),
			"so «carried» is a ring homomorphism",
			"one to one on the polynomials over k",
			"onto the polynomials over ι(k)")[0]
		carriedEquations := a.Have(
			"the carried equations are polynomials over ι(k)",
			"image(«carried», E) ⊆ «carriedPolynomials».carrier",
			By(
				equationsOverK,
				ring_homomorphism.MapIn.Read(carriedHom),
				set_image.ImageSubsetIff,
				set_basic.SubsetDef))
		hilbert := a.Have(
			"at each degree d both are binomial(d + n, n) less the dimension "+
				"of the ideal's forms of degree d, and those dimensions agree",
			"∀d:num. "+
				"    projective_hilbert_function(field_ring(N), image(ι, k), n, image(«carried», E), d) = "+
				"    projective_hilbert_function(field_ring(M), k, n, E, d)",
			a.ForEach(func(d *Expr[Nat]) Action {
				return ByArith(
					M,
					N,
					hom,
					subK,
					equationsOverK,
					embedding[0],
					carriedEquations,
					projective_curve.HilbertFunctionCodimension.Read(M).At(k, n, d, E),
					projective_curve.HilbertFunctionCodimension.Read(N).At(carriedK, n, d, carriedE),
					CarriedIdealFormsDimension.At(fieldM, fieldN, ι, k, n, d, E))
			}))
		a.Show(
			"the genus reads only the Hilbert function, so the two genera are one",
			Simp(Fwd(projective_curve.ProjectiveGenusDef), Fwd(hilbert)),
			Refl())
	}),
})}
