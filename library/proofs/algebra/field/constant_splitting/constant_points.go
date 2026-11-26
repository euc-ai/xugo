// constant_points.go — the points of a chart under a constant extension. A
// point of a ring S between k and K with values in a field T holding l extends
// to the chart of S over l along the coordinates of a k-basis of l, and
// restriction to S undoes the extension. So the chart over l has the points of
// S over k, as many of them, and two maps from the chart agreeing on l and on S
// agree. Inverting f in S and taking the chart is inverting f in the chart of S.

package constant_splitting

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantPointExtension — a point φ of S extends to the chart of S over l:
// send x to the sum σ(x) of φ(c)·e over a k-basis E of l, c the coordinate of x
// at e. σ is additive, a factor s from S comes out of it as φ(s), and it fixes
// l, so on S it is φ. Multiplicativity is one reduction: if σ respects the
// product of y with each e in E, it respects the product of y with anything,
// the other factor expanded over E. The hypothesis holds at y in l, which gives
// the product with l, in particular with E, and so the hypothesis at every y.
var ConstantPointExtension = constantPointExtensionThm{family.Add(registry.ProofEntry{
	Name: "ConstantPointExtension",
	Key:  "prop_cf081e3b02b6c0fc",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), l, S)"},
			{Name: "coordinate", Text: "λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(constant_composite(M, K, l)), E, x, e)"},
			{Name: "sum", Text: "λx:A. module_sum(M.add, M.zero, E, λe:A. φ(«coordinate»(x, e)) * e)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E S T:set(A). ∀φ:(A → A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"S ⊆ K",
			"subfield(M, T)",
			"l ⊆ T",
			"φ ∈ algebra_points(«scalars»(S), «scalars»(T), k, λx:A. x)",
		},
		Conclusion: "(λx:A. COND(x ∈ «chart», «sum»(x), M.zero)) ∈ " +
			"algebra_points(«scalars»(«chart»), «scalars»(T), l, λx:A. x) ∧ " +
			"(∀x:A. x ∈ S ⇒ «sum»(x) = φ(x))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E, S, T *Expr[Set[A]],
			φ *Arrow[A, A],
			regular, lSubfield, kInL, finiteBasis, basis, SSubring, kInS, SInK, TSubfield, lInT, point Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			fieldVectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			KScalars := a.TermAs[RingOps[A]]("«scalars»(K)")
			chartScalars := a.TermAs[RingOps[A]]("«scalars»(«chart»)")
			TScalars := a.TermAs[RingOps[A]]("«scalars»(T)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"«vectors»(constant_composite(M, K, l))")
			chart := a.TermAs[Set[A]]("«chart»")
			add := a.TermAs[Fun2[A, A, A]]("M.add")
			zero := a.TermAs[A]("M.zero")
			one := a.TermAs[A]("M.one")
			identity := a.TermAs[Fun[A, A]]("λx:A. x")
			ring := field.RingOn.Read(M)
			regularModule := module.RegularModuleOn.Read(ring)
			finiteExtension := a.Have(
				"the basis makes l finite over k",
				"finite_extension(M, k, l)",
				By(
					finiteBasis,
					basis,
					field_extension.FiniteExtensionDef.At(fieldM, k, l),
					module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					constant_composite.ConstantExtensionData.At(fieldM, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"the composite is a subfield",
				"it holds K",
				"it holds l",
				"E lies in l",
				"the composite is a K-module",
				"E is a K-basis of the composite")
			KSubfield, lInComposite, EInL, compositeModule, compositeBasis :=
				data[1], data[5], data[6], data[7], data[8]
			chartData := a.Conjuncts(
				a.Have(
					"the chart is a ring holding l and S",
					"subring(field_ring(M), «chart») ∧ l ⊆ «chart» ∧ S ⊆ «chart»",
					By(
						M,
						regular,
						lSubfield,
						kInL,
						finiteExtension,
						SSubring,
						SInK,
						kInS,
						constant_field_extension.ConstantChartRing.At(fieldM, K, k, l, S))),
				"the chart is a subring",
				"it holds l",
				"it holds S")
			chartSubring, lInChart, SInChart := chartData[0], chartData[1], chartData[2]
			chartRing := a.Conjuncts(
				a.Have(
					"so it is a ring in the field",
					"«chart» ⊆ M.carrier ∧ comm_ring_on(«scalars»(«chart»))",
					By(chartSubring, comm_ring.SubringRingOn.Read(ring).At(chart))),
				"the chart lies in the field",
				"the chart is a ring")
			chartInField, chartIsRing := chartRing[0], chartRing[1]
			subspace := a.Have(
				"S is a k-subspace of K",
				"submodule(«scalars»(k), «vectors»(K), S)",
				By(M, SSubring, kInS, SInK, constant_field_extension.ConstantRingSubspace.At(fieldM, K, k, S)))
			coordinates := a.Have(
				"a member of the chart lies in the composite, with its coordinates in S",
				"∀x:A. x ∈ «chart» ⇒ x ∈ constant_composite(M, K, l) ∧ (∀e:A. e ∈ E ⇒ «coordinate»(x, e) ∈ S)",
				a.ForEach(func(x *Expr[A]) Action {
					return By(
						M,
						regular,
						lSubfield,
						kInL,
						finiteBasis,
						basis,
						subspace,
						constant_field_extension.ConstantChartCoordinates.At(fieldM, K, k, l, E, S, x))
				}))
			pointData := a.Conjuncts(
				a.Have(
					"φ is a ring map fixing k",
					"ring_homomorphism(«scalars»(S), «scalars»(T), φ) ∧ (∀x:A. x ∈ k ⇒ φ(x) = x)",
					By(
						point,
						algebra_points.AlgebraPointsMember.At(
							a.TermAs[RingOps[A]]("«scalars»(S)"), TScalars, k, identity, φ))),
				"φ is a ring map",
				"φ fixes k")
			ringMap, fixesK := pointData[0], pointData[1]
			targetRing := ring_homomorphism.Target.Read(ringMap)
			TInField := a.Have(
				"T lies in the field",
				"T ⊆ M.carrier",
				By(TSubfield, field.SubfieldSubset.At(fieldM, T)))
			summands := a.Have(
				"the coordinates and the summands lie in the field, the summands in T",
				Statement{
					Binders:    "∀x e:A.",
					Hypotheses: []string{"x ∈ «chart»", "e ∈ E"},
					Conclusion: "«coordinate»(x, e) ∈ S ∧ " +
						"«coordinate»(x, e) ∈ M.carrier ∧ " +
						"φ(«coordinate»(x, e)) ∈ M.carrier ∧ " +
						"e ∈ M.carrier ∧ " +
						"φ(«coordinate»(x, e)) * e ∈ T ∧ " +
						"φ(«coordinate»(x, e)) * e ∈ M.carrier",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					e := b.FixAs[A]("e")
					assumed := b.Conjuncts(
						b.Assume(),
						"x lies in the chart",
						"e lies in E")
					xIn, eIn := assumed[0], assumed[1]
					inS := b.Have(
						"the coordinate lies in S",
						"«coordinate»(x, e) ∈ S",
						By(coordinates.At(x), xIn, eIn))
					inT := b.Have(
						"φ of it and e lie in T",
						"φ(«coordinate»(x, e)) ∈ T ∧ e ∈ T",
						BySets(inS, eIn, EInL, lInT, ring_homomorphism.MapIn.Read(ringMap)))
					b.Show(
						"T is a ring in the field, and S lies in the chart",
						BySets(
							inS,
							inT,
							SInChart,
							chartInField,
							TInField,
							comm_ring.MulIn.Read(targetRing).AsFact().At(b.TermAs[A]("φ(«coordinate»(x, e))"), e)))
				}))
			expansion := a.Have(
				"a member of the composite is the sum of its coordinates times E",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ constant_composite(M, K, l)"},
					Conclusion: "module_sum(M.add, M.zero, E, λe:A. «coordinate»(x, e) * e) = x",
				},
				a.ForEach(func(x *Expr[A]) Action {
					return By(
						compositeModule,
						finiteBasis,
						compositeBasis,
						module_dimension.BasisCoordinatesSpec.At(KScalars, compositeVectors, E, x))
				}))
			σ, σDef := a.LetAs[Fun[A, A]]("σ", "«sum»")
			value := a.Have(
				"σ(x) is the sum at x",
				"∀x:A. σ(x) = «sum»(x)",
				σDef.Rw(),
				TrivialNormalized())
			inT := a.Have(
				"the sum lands in T",
				"∀x:A. x ∈ «chart» ⇒ σ(x) ∈ T ∧ σ(x) ∈ M.carrier",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					terms := b.Have(
						"its terms lie in T",
						"∀e:A. e ∈ E ⇒ φ(«coordinate»(x, e)) * e ∈ T",
						b.ForEach(func(e *Expr[A]) Action {
							return By(summands.At(x, e), xIn)
						}))
					inTarget := b.Have(
						"so does the sum, a sum in the additive monoid of T",
						"σ(x) ∈ T",
						value.At(x).Rw(),
						By(
							terms,
							finiteBasis,
							module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(targetRing)).AsFact().At(
								E, b.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(x, e)) * e"))))
					b.Show(
						"and T lies in the field",
						BySets(inTarget, TInField))
				}))
			additive := a.Have(
				"σ is additive on the chart: coordinates add, and φ is additive",
				"∀x y:A. x ∈ «chart» ∧ y ∈ «chart» ⇒ σ(x + y) = σ(x) + σ(y)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					assumed := b.Conjuncts(
						b.Assume(),
						"x lies in the chart",
						"y lies in the chart")
					xIn, yIn := assumed[0], assumed[1]
					summandsAdd := b.Have(
						"summand by summand",
						Statement{
							Binders:    "∀e:A.",
							Hypotheses: []string{"e ∈ E"},
							Conclusion: "φ(«coordinate»(x, e)) * e ∈ M.carrier ∧ " +
								"φ(«coordinate»(y, e)) * e ∈ M.carrier ∧ " +
								"φ(«coordinate»(x + y, e)) * e = φ(«coordinate»(x, e)) * e + φ(«coordinate»(y, e)) * e",
						},
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							termsX := c.Have(
								"the terms of x",
								"«coordinate»(x, e) ∈ S ∧ "+
									"φ(«coordinate»(x, e)) ∈ M.carrier ∧ "+
									"e ∈ M.carrier ∧ "+
									"φ(«coordinate»(x, e)) * e ∈ M.carrier",
								By(summands.At(x, e), xIn, eIn))
							termsY := c.Have(
								"the terms of y",
								"«coordinate»(y, e) ∈ S ∧ "+
									"φ(«coordinate»(y, e)) ∈ M.carrier ∧ "+
									"φ(«coordinate»(y, e)) * e ∈ M.carrier",
								By(summands.At(y, e), yIn, eIn))
							inComposite := c.Have(
								"x and y lie in the composite",
								"x ∈ constant_composite(M, K, l) ∧ y ∈ constant_composite(M, K, l)",
								By(coordinates.At(x), coordinates.At(y), xIn, yIn))
							coordinateAdd := c.Have(
								"the coordinate of a sum is the sum of the coordinates",
								"«coordinate»(x + y, e) = «coordinate»(x, e) + «coordinate»(y, e)",
								By(
									finiteBasis,
									compositeModule,
									compositeBasis,
									inComposite,
									module_dimension.BasisCoordinatesAdd.At(KScalars, compositeVectors, E, x, y)))
							mapAdd := c.Have(
								"φ is additive on S",
								"φ(«coordinate»(x, e) + «coordinate»(y, e)) = φ(«coordinate»(x, e)) + φ(«coordinate»(y, e))",
								By(
									termsX,
									termsY,
									ring_homomorphism.MapAdd.Read(ringMap).AsFact().At(
										c.TermAs[A]("«coordinate»(x, e)"), c.TermAs[A]("«coordinate»(y, e)"))))
							distributed := c.Have(
								"the product distributes",
								"φ(«coordinate»(x + y, e)) * e = φ(«coordinate»(x, e)) * e + φ(«coordinate»(y, e)) * e",
								coordinateAdd.Rw(),
								mapAdd.Rw(),
								ByArith(M, termsX, termsY))
							c.Show(
								"the memberships and the distribution",
								By(termsX, termsY, distributed))
						}))
					b.Show(
						"sum the summands",
						value.At(b.TermAs[A]("x + y")).Rw(),
						value.At(x).Rw(),
						value.At(y).Rw(),
						By(
							regularModule,
							finiteBasis,
							summandsAdd,
							module.ModuleSumCongruence.At(
								add,
								zero,
								E,
								b.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(x + y, e)) * e"),
								b.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(x, e)) * e + φ(«coordinate»(y, e)) * e")),
							module.ModuleSumAdd.At(
								fieldRing,
								fieldVectors,
								E,
								b.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(x, e)) * e"),
								b.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(y, e)) * e"))))
				}))
			scaled := a.Have(
				"a factor s from S comes out of σ as φ(s): it comes out of each coordinate",
				"∀s x:A. s ∈ S ∧ x ∈ «chart» ⇒ σ(s * x) = φ(s) * σ(x)",
				Derive(func(b *Argument) {
					s := b.FixAs[A]("s")
					x := b.FixAs[A]("x")
					assumed := b.Conjuncts(
						b.Assume(),
						"s lies in S",
						"x lies in the chart")
					sIn, xIn := assumed[0], assumed[1]
					members := b.Have(
						"x lies in the composite, s in K, both in the field, and φ(s) in the field",
						"x ∈ constant_composite(M, K, l) ∧ s ∈ K ∧ s ∈ M.carrier ∧ x ∈ M.carrier ∧ φ(s) ∈ M.carrier",
						BySets(
							coordinates.At(x),
							xIn,
							sIn,
							SInK,
							SInChart,
							chartInField,
							TInField,
							ring_homomorphism.MapIn.Read(ringMap).AsFact().At(s)))
					summandsScale := b.Have(
						"summand by summand",
						Statement{
							Binders:    "∀e:A.",
							Hypotheses: []string{"e ∈ E"},
							Conclusion: "φ(«coordinate»(x, e)) * e ∈ M.carrier ∧ " +
								"φ(«coordinate»(s * x, e)) * e = φ(s) * (φ(«coordinate»(x, e)) * e)",
						},
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							terms := c.Have(
								"the terms of x",
								"«coordinate»(x, e) ∈ S ∧ "+
									"φ(«coordinate»(x, e)) ∈ M.carrier ∧ "+
									"e ∈ M.carrier ∧ "+
									"φ(«coordinate»(x, e)) * e ∈ M.carrier",
								By(summands.At(x, e), xIn, eIn))
							swapped := c.Have(
								"the product commutes",
								"s * x = x * s",
								ByArith(M, members))
							coordinateScale := c.Have(
								"s comes out of the coordinate",
								"«coordinate»(x * s, e) = «coordinate»(x, e) * s",
								By(
									M,
									regular,
									lSubfield,
									kInL,
									finiteBasis,
									basis,
									members,
									eIn,
									constant_composite.ConstantCoordinateProduct.At(fieldM, K, k, l, E, x, s, e)))
							mapMul := c.Have(
								"φ is multiplicative on S",
								"φ(«coordinate»(x, e) * s) = φ(«coordinate»(x, e)) * φ(s)",
								By(
									terms,
									sIn,
									ring_homomorphism.MapMul.Read(ringMap).AsFact().At(c.TermAs[A]("«coordinate»(x, e)"), s)))
							regrouped := c.Have(
								"the factors regroup",
								"φ(«coordinate»(s * x, e)) * e = φ(s) * (φ(«coordinate»(x, e)) * e)",
								swapped.Rw(),
								coordinateScale.Rw(),
								mapMul.Rw(),
								ByArith(M, terms, members))
							c.Show(
								"the membership and the regrouping",
								By(terms, regrouped))
						}))
					b.Show(
						"take φ(s) out of the sum",
						value.At(b.TermAs[A]("s * x")).Rw(),
						value.At(x).Rw(),
						By(
							regularModule,
							finiteBasis,
							members,
							summandsScale,
							module.ModuleSumCongruence.At(
								add,
								zero,
								E,
								b.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(s * x, e)) * e"),
								b.TermAs[Fun[A, A]]("λe:A. φ(s) * (φ(«coordinate»(x, e)) * e)")),
							module.ModuleSumSmul.At(
								fieldRing,
								fieldVectors,
								E,
								b.TermAs[A]("φ(s)"),
								b.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(x, e)) * e"))))
				}))
			fixed := a.Have(
				"σ fixes l: the coordinates of an element of l lie in k, which φ fixes",
				"∀b:A. b ∈ l ⇒ σ(b) = b",
				Derive(func(c *Argument) {
					b := c.FixAs[A]("b")
					bIn := c.Assume()
					summandsFixed := c.Have(
						"summand by summand",
						"∀e:A. e ∈ E ⇒ φ(«coordinate»(b, e)) * e = «coordinate»(b, e) * e",
						Derive(func(d *Argument) {
							e := d.FixAs[A]("e")
							eIn := d.Assume()
							inK := d.Have(
								"the coordinate lies in k",
								"«coordinate»(b, e) ∈ k",
								By(
									M,
									regular,
									lSubfield,
									kInL,
									finiteBasis,
									basis,
									bIn,
									KSubfield,
									eIn,
									field.SubfieldOne.At(fieldM, K),
									constant_composite.ConstantCoordinateScale.At(fieldM, K, k, l, E, b, one, e)))
							d.Show(
								"φ fixes it",
								By(inK, fixesK.At(d.TermAs[A]("«coordinate»(b, e)"))))
						}))
					inComposite := c.Have(
						"b lies in the composite",
						"b ∈ constant_composite(M, K, l)",
						BySets(bIn, lInComposite))
					c.Show(
						"and b is the sum of its coordinates times E",
						value.At(b).Rw(),
						By(
							summandsFixed,
							inComposite,
							expansion.At(b),
							module.ModuleSumCongruence.At(
								add,
								zero,
								E,
								c.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(b, e)) * e"),
								c.TermAs[Fun[A, A]]("λe:A. «coordinate»(b, e) * e"))))
				}))
			oneIn := a.Have(
				"one lies in l and the chart, zero in l",
				"M.one ∈ l ∧ M.one ∈ «chart» ∧ M.zero ∈ l",
				BySets(field.SubfieldOne.At(fieldM, l), field.SubfieldZero.At(fieldM, l), lSubfield, lInChart))
			onS := a.Have(
				"on S, σ is φ: a member of S is itself times one",
				"∀s:A. s ∈ S ⇒ σ(s) = φ(s)",
				Derive(func(b *Argument) {
					s := b.FixAs[A]("s")
					sIn := b.Assume()
					members := b.Have(
						"s and φ(s) lie in the field",
						"s ∈ M.carrier ∧ φ(s) ∈ M.carrier",
						BySets(sIn, SInChart, chartInField, TInField, ring_homomorphism.MapIn.Read(ringMap).AsFact().At(s)))
					units := b.Have(
						"one is a unit for both",
						"s * M.one = s ∧ φ(s) * M.one = φ(s)",
						ByArith(M, members))
					b.Show(
						"scale one by s",
						By(sIn, oneIn, units, scaled.At(s, one), fixed.At(one)))
				}))
			finiteSums := a.Have(
				"σ commutes with sums over E of members of the chart",
				Statement{
					Binders:    "∀F:(A → A).",
					Hypotheses: []string{"∀e:A. e ∈ E ⇒ F(e) ∈ «chart»"},
					Conclusion: "σ(module_sum(M.add, M.zero, E, F)) = module_sum(M.add, M.zero, E, λe:A. σ(F(e)))",
				},
				Derive(func(b *Argument) {
					F := b.FixAs[Fun[A, A]]("F")
					membersF := b.Assume()
					b.Show(
						"σ is a homomorphism of the additive monoid of the chart",
						By(
							oneIn,
							additive,
							finiteBasis,
							membersF,
							fixed.At(zero),
							module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(chartIsRing)).At(
								add, zero, σ, E, F)))
				}))
			reduction := a.Have(
				"if σ respects the product of y with each e of E, it respects the product of y with every x",
				Statement{
					Binders:    "∀y:A.",
					Hypotheses: []string{"y ∈ «chart»", "∀e:A. e ∈ E ⇒ σ(e * y) = e * σ(y)"},
					Conclusion: "∀x:A. x ∈ «chart» ⇒ σ(x * y) = σ(x) * σ(y)",
				},
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					hypotheses := b.Conjuncts(
						b.Assume(),
						"y lies in the chart",
						"σ respects the products with E")
					yIn, onBasis := hypotheses[0], hypotheses[1]
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					members := b.Have(
						"x, y, σ(x) and σ(y) lie in the field, and x in the composite",
						"x ∈ constant_composite(M, K, l) ∧ "+
							"x ∈ M.carrier ∧ "+
							"y ∈ M.carrier ∧ "+
							"σ(x) ∈ M.carrier ∧ "+
							"σ(y) ∈ M.carrier",
						BySets(xIn, yIn, chartInField, coordinates.At(x), inT.At(x), inT.At(y)))
					commuted := b.Have(
						"the two products commute",
						"x * y = y * x ∧ σ(x) * σ(y) = σ(y) * σ(x)",
						ByArith(M, members))
					regroupTerms := b.Have(
						"each term of the expansion of x, times y, regroups",
						Statement{
							Binders:    "∀e:A.",
							Hypotheses: []string{"e ∈ E"},
							Conclusion: "«coordinate»(x, e) * e ∈ M.carrier ∧ " +
								"φ(«coordinate»(x, e)) * e ∈ M.carrier ∧ " +
								"y * («coordinate»(x, e) * e) = «coordinate»(x, e) * (e * y)",
						},
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							terms := c.Have(
								"the factors lie in the field",
								"«coordinate»(x, e) ∈ M.carrier ∧ e ∈ M.carrier ∧ φ(«coordinate»(x, e)) * e ∈ M.carrier",
								By(summands.At(x, e), xIn, eIn))
							product := c.Have(
								"so does their product",
								"«coordinate»(x, e) * e ∈ M.carrier",
								By(terms, comm_ring.MulIn.Read(ring).AsFact().At(c.TermAs[A]("«coordinate»(x, e)"), e)))
							regrouped := c.Have(
								"the factors regroup",
								"y * («coordinate»(x, e) * e) = «coordinate»(x, e) * (e * y)",
								ByArith(M, terms, members))
							c.Show(
								"the memberships and the regrouping",
								By(terms, product, regrouped))
						}))
					expanded := b.Have(
						"x times y is the sum of the coordinates of x times e times y",
						"x * y = module_sum(M.add, M.zero, E, λe:A. «coordinate»(x, e) * (e * y))",
						By(
							regularModule,
							finiteBasis,
							members,
							commuted,
							regroupTerms,
							expansion.At(x),
							module.ModuleSumSmul.At(
								fieldRing,
								fieldVectors,
								E,
								y,
								b.TermAs[Fun[A, A]]("λe:A. «coordinate»(x, e) * e")),
							module.ModuleSumCongruence.At(
								add,
								zero,
								E,
								b.TermAs[Fun[A, A]]("λe:A. y * («coordinate»(x, e) * e)"),
								b.TermAs[Fun[A, A]]("λe:A. «coordinate»(x, e) * (e * y)"))))
					termsOfProduct := b.Have(
						"each term lies in the chart, and σ of it is σ(y) times a summand of σ(x)",
						Statement{
							Binders:    "∀e:A.",
							Hypotheses: []string{"e ∈ E"},
							Conclusion: "«coordinate»(x, e) * (e * y) ∈ «chart» ∧ " +
								"σ(«coordinate»(x, e) * (e * y)) = σ(y) * (φ(«coordinate»(x, e)) * e)",
						},
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							coordinate := c.TermAs[A]("«coordinate»(x, e)")
							ey := c.TermAs[A]("e * y")
							terms := c.Have(
								"the factors lie in S and the field",
								"«coordinate»(x, e) ∈ S ∧ φ(«coordinate»(x, e)) ∈ M.carrier ∧ e ∈ M.carrier",
								By(summands.At(x, e), xIn, eIn))
							inChart := c.Have(
								"the coordinate and e lie in the chart",
								"«coordinate»(x, e) ∈ «chart» ∧ e ∈ «chart»",
								BySets(terms, eIn, SInChart, EInL, lInChart))
							eyIn := c.Have(
								"so does e times y",
								"e * y ∈ «chart»",
								By(inChart, yIn, comm_ring.MulIn.Read(chartIsRing).AsFact().At(e, y)))
							product := c.Have(
								"and so does the term",
								"«coordinate»(x, e) * (e * y) ∈ «chart»",
								By(inChart, eyIn, comm_ring.MulIn.Read(chartIsRing).AsFact().At(coordinate, ey)))
							extracted := c.Have(
								"the coordinate comes out as its φ, and e by hypothesis",
								"σ(«coordinate»(x, e) * (e * y)) = φ(«coordinate»(x, e)) * (e * σ(y))",
								By(terms, eyIn, eIn, scaled.At(coordinate, ey), onBasis.At(e)))
							regrouped := c.Have(
								"the factors regroup",
								"φ(«coordinate»(x, e)) * (e * σ(y)) = σ(y) * (φ(«coordinate»(x, e)) * e)",
								ByArith(M, terms, members))
							c.Show(
								"the membership, and the two steps chained",
								By(product, extracted, regrouped))
						}))
					summed := b.Have(
						"σ of the product is the sum of σ of the terms",
						"σ(x * y) = module_sum(M.add, M.zero, E, λe:A. σ(«coordinate»(x, e) * (e * y)))",
						expanded.Rw(),
						By(termsOfProduct, finiteSums.At(b.TermAs[Fun[A, A]]("λe:A. «coordinate»(x, e) * (e * y)"))))
					congruent := b.Have(
						"term by term",
						"module_sum(M.add, M.zero, E, λe:A. σ(«coordinate»(x, e) * (e * y))) = "+
							"module_sum(M.add, M.zero, E, λe:A. σ(y) * (φ(«coordinate»(x, e)) * e))",
						By(
							termsOfProduct,
							module.ModuleSumCongruence.At(
								add,
								zero,
								E,
								b.TermAs[Fun[A, A]]("λe:A. σ(«coordinate»(x, e) * (e * y))"),
								b.TermAs[Fun[A, A]]("λe:A. σ(y) * (φ(«coordinate»(x, e)) * e)"))))
					pulled := b.Have(
						"and σ(y) comes out of the sum, leaving σ(x)",
						"σ(y) * σ(x) = module_sum(M.add, M.zero, E, λe:A. σ(y) * (φ(«coordinate»(x, e)) * e))",
						value.At(x).Rw(),
						By(
							regularModule,
							finiteBasis,
							members,
							regroupTerms,
							module.ModuleSumSmul.At(
								fieldRing,
								fieldVectors,
								E,
								b.TermAs[A]("σ(y)"),
								b.TermAs[Fun[A, A]]("λe:A. φ(«coordinate»(x, e)) * e"))))
					b.Show(
						"chain the three, and commute",
						By(commuted, summed, congruent, pulled))
				}))
			withConstants := a.Have(
				"σ respects the product with l: the hypothesis of the reduction holds at b in l, σ fixing l",
				"∀b x:A. b ∈ l ∧ x ∈ «chart» ⇒ σ(x * b) = σ(x) * b",
				Derive(func(c *Argument) {
					b := c.FixAs[A]("b")
					c.FixAs[A]("x")
					assumed := c.Conjuncts(
						c.Assume(),
						"b lies in l",
						"x lies in the chart")
					bIn, xIn := assumed[0], assumed[1]
					onBasis := c.Have(
						"e times b lies in l",
						"∀e:A. e ∈ E ⇒ σ(e * b) = e * σ(b)",
						Derive(func(d *Argument) {
							e := d.FixAs[A]("e")
							eIn := d.Assume()
							inL := d.Have(
								"e lies in l, and so does the product",
								"e ∈ l ∧ e * b ∈ l",
								BySets(eIn, EInL, bIn, lSubfield, field.SubfieldMul.At(fieldM, l, e, b)))
							d.Show(
								"σ fixes both",
								By(Normalized, bIn, inL, fixed.At(b), fixed.At(d.TermAs[A]("e * b"))))
						}))
					inChart := c.Have(
						"b lies in the chart",
						"b ∈ «chart»",
						BySets(bIn, lInChart))
					c.Show(
						"the reduction at b",
						By(bIn, inChart, onBasis, xIn, fixed.At(b), reduction.At(b)))
				}))
			multiplicative := a.Have(
				"so σ is multiplicative: the hypothesis of the reduction holds at every y",
				"∀x y:A. x ∈ «chart» ∧ y ∈ «chart» ⇒ σ(x * y) = σ(x) * σ(y)",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					assumed := b.Conjuncts(
						b.Assume(),
						"x lies in the chart",
						"y lies in the chart")
					xIn, yIn := assumed[0], assumed[1]
					onBasis := b.Have(
						"each e of E lies in l",
						"∀e:A. e ∈ E ⇒ σ(e * y) = e * σ(y)",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							members := c.Have(
								"e lies in l, and e, y and σ(y) in the field",
								"e ∈ l ∧ e ∈ M.carrier ∧ y ∈ M.carrier ∧ σ(y) ∈ M.carrier",
								BySets(eIn, EInL, yIn, lInChart, chartInField, inT.At(y)))
							commuted := c.Have(
								"the products commute",
								"e * y = y * e ∧ σ(y) * e = e * σ(y)",
								ByArith(M, members))
							c.Show(
								"read the product with l",
								By(commuted, members, yIn, withConstants.At(e, y)))
						}))
					b.Show(
						"the reduction at y",
						By(xIn, yIn, onBasis, reduction.At(y)))
				}))
			extension := a.TermAs[Fun[A, A]]("λx:A. COND(x ∈ «chart», σ(x), M.zero)")
			ringMapAbove := a.Have(
				"σ is a ring map from the chart to T",
				"ring_homomorphism(«scalars»(«chart»), «scalars»(T), σ)",
				By(
					chartIsRing,
					targetRing,
					inT,
					additive,
					multiplicative,
					oneIn,
					fixed.At(one),
					ring_homomorphism.RingHomomorphism.At(chartScalars, TScalars, σ)))
			extensionMap := a.Have(
				"and so is the extension, which is σ on the chart",
				"ring_homomorphism(«scalars»(«chart»), «scalars»(T), λx:A. COND(x ∈ «chart», σ(x), M.zero))",
				By(ringMapAbove, ring_homomorphism.RingHomCongruence.At(chartScalars, TScalars, σ, extension)))
			fixesL := a.Have(
				"the extension fixes l",
				"∀x:A. x ∈ l ⇒ COND(x ∈ «chart», σ(x), M.zero) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					inChart := b.Have(
						"x lies in the chart",
						"x ∈ «chart»",
						BySets(xIn, lInChart))
					b.Show(
						"where the extension is σ, which fixes x",
						By(inChart, xIn, fixed.At(x)))
				}))
			offChart := a.Have(
				"and vanishes off the chart",
				"∀x:A. x ∉ «chart» ⇒ COND(x ∈ «chart», σ(x), M.zero) = M.zero",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					off := b.Assume()
					b.Show(
						"its other branch",
						By(off))
				}))
			isPoint := a.Have(
				"so the extension is a point of the chart",
				"(λx:A. COND(x ∈ «chart», σ(x), M.zero)) ∈ "+
					"algebra_points(«scalars»(«chart»), «scalars»(T), l, λx:A. x)",
				By(
					extensionMap,
					fixesL,
					offChart,
					algebra_points.AlgebraPointsMember.At(chartScalars, TScalars, l, identity, extension)))
			a.Show(
				"the extension is a point of the chart, and on S it is φ",
				By(isPoint, onS))
		}),
})}

// ConstantChartGenerated — a subring of the chart of S over l holding l and S is
// the chart: it is a subring of the field, so a submodule over l, and the chart
// is the least submodule over l holding S.
var ConstantChartGenerated = constantChartGeneratedThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartGenerated",
	Key:  "prop_1a58b710c5c3b58",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "constant_chart(field_ring(M), l, S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), «chart»)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S D:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"subring(«scalars», D)",
			"l ⊆ D",
			"S ⊆ D",
		},
		Conclusion: "«chart» ⊆ D",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, D *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subringS, SInK, kInS, subringD, lInD, SInD Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			chart := a.TermAs[Set[A]]("«chart»")
			chartSubring := a.Have(
				"the chart is a subring of the field",
				"subring(field_ring(M), «chart»)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					SInK,
					kInS,
					constant_field_extension.ConstantChartRing.At(ops, K, k, l, S)))
			inField := a.Have(
				"so D is a subring of the field",
				"subring(field_ring(M), D)",
				BySets(
					chartSubring,
					subringD,
					comm_ring.SubringDef.At(fieldRing, D),
					comm_ring.SubringDef.At(a.TermAs[RingOps[A]]("«scalars»"), D),
					comm_ring.SubringDef.At(fieldRing, chart)))
			a.Show(
				"a submodule over l holding S, it holds the chart",
				By(
					SInD,
					M,
					inField,
					lInD,
					principal_ideal_domain.ConstantSubringSubmodule.At(ops, l, D),
					constant_field_extension.ConstantChartLeast.At(fieldRing, l, S, D)))
		}),
})}

// ConstantChartMapsAgree — two ring maps from the chart of S over l that agree
// on l and on S agree on the chart: where they agree is a subring holding both.
var ConstantChartMapsAgree = constantChartMapsAgreeThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartMapsAgree",
	Key:  "prop_f50de0ba31b62d3f",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "constant_chart(field_ring(M), l, S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), «chart»)"},
			{Name: "agreement", Text: "{y:A | y ∈ «chart» ∧ f(y) = g(y)}"},
		},
		Binders: "∀M:field_on(A). ∀K k l S:set(A). ∀T:ring_ops(B). ∀f g:(A → B). ∀x:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"ring_homomorphism(«scalars», T, f)",
			"ring_homomorphism(«scalars», T, g)",
			"∀c:A. c ∈ l ⇒ f(c) = g(c)",
			"∀c:A. c ∈ S ⇒ f(c) = g(c)",
			"x ∈ «chart»",
		},
		Conclusion: "f(x) = g(x)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S *Expr[Set[A]],
			T *Expr[RingOps[B]],
			f, g *Arrow[A, B],
			x *Expr[A],
			regular, lSubfield, kInL, finiteExtension, subringS, SInK, kInS, fMap, gMap, onL, onS, xIn Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			holdsBoth := a.Have(
				"the chart holds l and S",
				"l ⊆ «chart» ∧ S ⊆ «chart»",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					SInK,
					kInS,
					constant_field_extension.ConstantChartRing.At(ops, K, k, l, S)))
			equalizer := a.Have(
				"the elements of the chart where they agree form a subring",
				"subring(«scalars», «agreement»)",
				By(
					fMap,
					gMap,
					ring_homomorphism.RingMapEqualizerSubring.At(a.TermAs[RingOps[A]]("«scalars»"), T, f, g)))
			holds := a.Have(
				"which holds l and S",
				"l ⊆ «agreement» ∧ S ⊆ «agreement»",
				BySets(holdsBoth, onL, onS))
			cover := a.Have(
				"so it is the whole chart",
				"«chart» ⊆ «agreement»",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					SInK,
					kInS,
					equalizer,
					holds,
					ConstantChartGenerated.At(ops, K, k, l, S, a.TermAs[Set[A]]("«agreement»"))))
			a.Show(
				"x lies in the chart",
				BySets(cover, xIn))
		}),
})}

// ConstantChartPoints — restriction to S is a bijection from the points of the
// chart of S over l onto the points of S over k. The chart is the least ring
// holding l and S, so two points agreeing on S are equal; a point of the chart
// restricts to a point of S since k lies in l; and every point of S is the
// restriction of its extension along a k-basis of l.
var ConstantChartPoints = constantChartPointsThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartPoints",
	Key:  "prop_30c5c806a338cfe",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), l, S)"},
			{Name: "above", Text: "algebra_points(«scalars»(«chart»), «scalars»(T), l, λx:A. x)"},
			{Name: "below", Text: "algebra_points(«scalars»(S), «scalars»(T), k, λx:A. x)"},
			{Name: "restriction", Text: "λψ:A → A. λx:A. COND(x ∈ S, ψ(x), M.zero)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S T:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"S ⊆ K",
			"subfield(M, T)",
			"l ⊆ T",
		},
		Conclusion: "injective_on(«above», «restriction») ∧ image(«restriction», «above») = «below»",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, T *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, SSubring, kInS, SInK, TSubfield, lInT Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			SScalars := a.TermAs[RingOps[A]]("«scalars»(S)")
			TScalars := a.TermAs[RingOps[A]]("«scalars»(T)")
			chartScalars := a.TermAs[RingOps[A]]("«scalars»(«chart»)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			chart := a.TermAs[Set[A]]("«chart»")
			identity := a.TermAs[Fun[A, A]]("λx:A. x")
			above := a.TermAs[Set[Fun[A, A]]]("«above»")
			below := a.TermAs[Set[Fun[A, A]]]("«below»")
			ring := field.RingOn.Read(M)
			E, basisData := a.ObtainAs[Set[A]](
				"take a finite k-basis of l",
				"∃E:set(A). finite(E) ∧ module_basis(«scalars»(k), «vectors»(l), E)",
				By(
					finiteExtension,
					field_extension.FiniteExtensionDef.At(fieldM, k, l),
					module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
			basisParts := a.Conjuncts(
				basisData,
				"E is finite",
				"E is a k-basis of l")
			chartData := a.Conjuncts(
				a.Have(
					"the chart is a ring holding l and S",
					"subring(field_ring(M), «chart») ∧ l ⊆ «chart» ∧ S ⊆ «chart»",
					By(
						M,
						regular,
						lSubfield,
						kInL,
						finiteExtension,
						SSubring,
						SInK,
						kInS,
						constant_field_extension.ConstantChartRing.At(fieldM, K, k, l, S))),
				"the chart is a subring",
				"it holds l",
				"it holds S")
			chartSubring, SInChart := chartData[0], chartData[2]
			chartRing := a.Conjuncts(
				a.Have(
					"it is a ring in the field",
					"«chart» ⊆ M.carrier ∧ comm_ring_on(«scalars»(«chart»))",
					By(chartSubring, comm_ring.SubringRingOn.Read(ring).At(chart))),
				"the chart lies in the field",
				"the chart is a ring")
			chartIsRing := chartRing[1]
			pointsAbove := a.Have(
				"a point of the chart is a ring map fixing l and zero off the chart",
				"∀ψ:(A → A). "+
					"    ψ ∈ «above» ⇔ "+
					"    ring_homomorphism(«scalars»(«chart»), «scalars»(T), ψ) ∧ "+
					"    (∀x:A. x ∈ l ⇒ ψ(x) = x) ∧ "+
					"    (∀x:A. x ∉ «chart» ⇒ ψ(x) = M.zero)",
				a.ForEach(func(ψ *Expr[Fun[A, A]]) Action {
					return By(algebra_points.AlgebraPointsMember.At(chartScalars, TScalars, l, identity, ψ))
				}))
			pointsBelow := a.Have(
				"a point of S is a ring map fixing k and zero off S",
				"∀ψ:(A → A). "+
					"    ψ ∈ «below» ⇔ "+
					"    ring_homomorphism(«scalars»(S), «scalars»(T), ψ) ∧ "+
					"    (∀x:A. x ∈ k ⇒ ψ(x) = x) ∧ "+
					"    (∀x:A. x ∉ S ⇒ ψ(x) = M.zero)",
				a.ForEach(func(ψ *Expr[Fun[A, A]]) Action {
					return By(algebra_points.AlgebraPointsMember.At(SScalars, TScalars, k, identity, ψ))
				}))
			agreement := a.Have(
				"two points of the chart with one restriction are equal",
				"∀ψ χ:(A → A). ψ ∈ «above» ∧ χ ∈ «above» ∧ «restriction»(ψ) = «restriction»(χ) ⇒ ψ = χ",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, A]]("ψ")
					χ := b.FixAs[Fun[A, A]]("χ")
					assumed := b.Conjuncts(
						b.Assume(),
						"ψ is a point",
						"χ is a point",
						"they restrict alike")
					ψPoint, χPoint, alike := assumed[0], assumed[1], assumed[2]
					onS := b.Have(
						"they agree on S",
						"∀x:A. x ∈ S ⇒ ψ(x) = χ(x)",
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							inS := c.Assume()
							c.Show(
								"on S each is its restriction",
								By(alike, inS))
						}))
					data := b.Have(
						"both are ring maps, equal on l and zero off the chart",
						"ring_homomorphism(«scalars»(«chart»), «scalars»(T), ψ) ∧ "+
							"ring_homomorphism(«scalars»(«chart»), «scalars»(T), χ) ∧ "+
							"(∀x:A. x ∈ l ⇒ ψ(x) = χ(x)) ∧ "+
							"(∀x:A. x ∉ «chart» ⇒ ψ(x) = M.zero ∧ χ(x) = M.zero)",
						BySets(pointsAbove.At(ψ), pointsAbove.At(χ), ψPoint, χPoint))
					onChart := b.Have(
						"two ring maps from the chart agreeing on l and on S agree on the chart",
						"∀x:A. x ∈ «chart» ⇒ ψ(x) = χ(x)",
						b.ForEach(func(x *Expr[A]) Action {
							return By(
								M,
								regular,
								lSubfield,
								kInL,
								finiteExtension,
								SSubring,
								SInK,
								kInS,
								data,
								onS,
								ConstantChartMapsAgree.At(fieldM, K, k, l, S, TScalars, ψ, χ, x))
						}))
					b.Do(Funext())
					b.Show(
						"they agree on the chart and vanish off it",
						BySets(onChart, data))
				}))
			injective := a.Have(
				"so restriction is injective",
				"injective_on(«above», «restriction»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				By(agreement))
			SSource := a.Have(
				"S is a ring in the field",
				"S ⊆ M.carrier ∧ comm_ring_on(«scalars»(S))",
				By(SSubring, comm_ring.SubringRingOn.Read(ring).At(S)))
			restrictedRing := a.Have(
				"the ring on S reads the same inside the chart",
				"restrict_ring(«scalars»(«chart»), S) = «scalars»(S)",
				By(module_record.RestrictRingTwice.At(fieldRing, chart, S)))
			SInChartRing := a.Have(
				"so S is a subring of the chart",
				"subring(«scalars»(«chart»), S)",
				By(SInChart, SSource, restrictedRing, comm_ring.SubringRingOn.Read(chartIsRing).AsFact().At(S)))
			restricted := a.Have(
				"the restriction of a point of the chart is a point of S",
				"∀ψ:(A → A). ψ ∈ «above» ⇒ «restriction»(ψ) ∈ «below»",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, A]]("ψ")
					point := b.Assume()
					restriction := b.TermAs[Fun[A, A]]("«restriction»(ψ)")
					data := b.Have(
						"ψ is a ring map fixing l",
						"ring_homomorphism(«scalars»(«chart»), «scalars»(T), ψ) ∧ (∀x:A. x ∈ l ⇒ ψ(x) = x)",
						By(pointsAbove.At(ψ), point))
					onS := b.Have(
						"so a ring map on S",
						"ring_homomorphism(«scalars»(S), «scalars»(T), ψ)",
						By(
							data,
							SInChartRing,
							restrictedRing,
							ring_homomorphism.RingHomRestrictSource.At(chartScalars, TScalars, ψ, S)))
					restrictedMap := b.Have(
						"and so is its restriction, the same map on S",
						"ring_homomorphism(«scalars»(S), «scalars»(T), «restriction»(ψ))",
						By(onS, ring_homomorphism.RingHomCongruence.At(SScalars, TScalars, ψ, restriction)))
					b.Show(
						"it fixes k, which lies in l, and vanishes off S",
						BySets(pointsBelow.At(restriction), restrictedMap, data, kInS, kInL))
				}))
			extended := a.Have(
				"every point of S is the restriction of its extension along E",
				"∀φ:(A → A). φ ∈ «below» ⇒ ∃ψ:(A → A). ψ ∈ «above» ∧ «restriction»(ψ) = φ",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]("φ")
					point := b.Assume()
					Φ, ΦDef := b.LetAs[Fun[A, A]](
						"Φ",
						"λx:A. "+
							"    COND(x ∈ «chart», "+
							"        module_sum(M.add, "+
							"            M.zero, "+
							"            E, "+
							"            λe:A. "+
							"                φ(module_basis_coordinates(«scalars»(K), "+
							"                        «vectors»(constant_composite(M, K, l)), "+
							"                        E, "+
							"                        x, "+
							"                        e)) * "+
							"                e), "+
							"        M.zero)")
					extension := b.Conjuncts(
						GroupPremises(
							M,
							regular,
							lSubfield,
							kInL,
							SSubring,
							kInS,
							SInK,
							TSubfield,
							lInT,
							point,
							basisParts[0],
							basisParts[1],
							ConstantPointExtension.At(fieldM, K, k, l, E, S, T, φ)),
						"the extension is a point of the chart",
						"on S it is φ")
					offS := b.Have(
						"φ vanishes off S",
						"∀x:A. x ∉ S ⇒ φ(x) = M.zero",
						By(pointsBelow.At(φ), point))
					restrictsToφ := b.Have(
						"the extension restricts to φ",
						"«restriction»(Φ) = φ",
						Funext(),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							c.Cases(c.Term("x ∈ S"))
							c.When(
								"on S it is φ",
								func(d *Argument, inS Fact) {
									inChart := d.Have(
										"x lies in the chart",
										"x ∈ «chart»",
										BySets(inS, SInChart))
									d.Show(
										"the chart's branch at x",
										By(inS, inChart, ΦDef, extension[1].At(x)))
								})
							c.Otherwise(
								"off S both vanish",
								func(d *Argument, off Fact) {
									d.Show(
										"φ vanishes there",
										By(off, offS.At(x)))
								})
						}))
					b.Show(
						"take the extension",
						Witness(Φ),
						By(ΦDef, extension[0], restrictsToφ))
				}))
			into := a.Have(
				"the image lies in the points of S",
				"image(«restriction», «above») ⊆ «below»",
				By(
					restricted,
					set_image.ImageSubsetIff.At(a.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»"), above, below)))
			onto := a.Have(
				"and holds them",
				"«below» ⊆ image(«restriction», «above»)",
				BySets(extended))
			a.Show(
				"restriction is a bijection",
				By(
					injective,
					into,
					onto,
					set_order.SubsetAntisym.At(a.TermAs[Set[Fun[A, A]]]("image(«restriction», «above»)"), below)))
		}),
})}

// ConstantChartPointCount — the chart of a ring S over l has as many points over
// l as S has over k: for k ⊆ S ⊆ K a subring with finitely many points in a
// subfield T holding l, restriction to S is a bijection from the points of its
// chart onto those of S (ConstantChartPoints), so the chart has finitely many,
// and as many.
var ConstantChartPointCount = constantChartPointCountThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartPointCount",
	Key:  "prop_feac656444961232",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k l S T:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"S ⊆ K",
			"subfield(M, T)",
			"l ⊆ T",
			"finite(«below»)",
		},
		Conclusion: "finite(«above») ∧ card(«above») = card(«below»)",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), l, S)"},
			{Name: "above", Text: "algebra_points(«scalars»(«chart»), «scalars»(T), l, λx:A. x)"},
			{Name: "below", Text: "algebra_points(«scalars»(S), «scalars»(T), k, λx:A. x)"},
			{Name: "restriction", Text: "λψ:A → A. λx:A. COND(x ∈ S, ψ(x), M.zero)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, T *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subringS, kInS, SInK, TSubfield, lInT, finiteBelow Fact,
		) {
			above := a.TermAs[Set[Fun[A, A]]]("«above»")
			restriction := a.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
			bijection := a.Conjuncts(
				GroupPremises(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					kInS,
					SInK,
					TSubfield,
					lInT,
					ConstantChartPoints.Read(M).At(K, k, l, S, T)),
				"restriction to S is injective on the points of the chart",
				"and takes them onto the points of S")
			a.Show(
				"an injective image is finite with its source, and has its size",
				By(
					bijection[0],
					bijection[1],
					finiteBelow,
					finite_set.FiniteImageInjEq.At(restriction, above),
					cardinality.CardImageInj.At(restriction, above)))
		}),
})}
