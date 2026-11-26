// constant_extension.go — the linear algebra of a constant extension. A
// k-basis E of a finite extension l of the constants stays a basis of the
// composite K' = K(l) over a regular function field K, because the tensor
// product l ⊗_k K is K' and a k-basis of l separates the terms of a tensor.
// Multiplying a k-subspace S of K by l gives the chart S', the direct sum of
// the lines S·e: everything about charts is read off the E-coordinates. The
// chart of a subring is a subring holding l, and charting commutes with
// adjoining an element.

package constant_field_extension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantChartSubmodule — the chart of a subset of the field is a submodule
// over l holding the subset.
var ConstantChartSubmodule = constantChartSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartSubmodule",
	Key:  "prop_c6b42b64533cf35f",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "lScalars", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "regular", Text: "regular_module(field_ring(M))"},
		},
		Binders: "∀M:field_on(A). ∀l S:set(A).",
		Hypotheses: []string{
			"subfield(M, l)",
			"S ⊆ M.carrier",
		},
		Conclusion: "module_on(«lScalars», «regular») ∧ " +
			"submodule(«lScalars», «regular», constant_chart(field_ring(M), l, S)) ∧ " +
			"S ⊆ constant_chart(field_ring(M), l, S)",
	},
		func(a *Argument, M field.FieldFact[on.M], l, S *Expr[Set[A]], lSubfield, SInField Fact) {
			m := a.TermAs[FieldOps[A]]("M")
			lScalars := a.TermAs[RingOps[A]]("«lScalars»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«regular»")
			a.Show(
				"a span over a subfield of the field",
				Unfold(ConstantChartDef),
				By(
					M,
					lSubfield,
					SInField,
					field_extension.SubfieldScalars.At(m, l),
					submodule.SpanSubmodule.At(lScalars, regular, S),
					submodule.SubsetSpan.At(lScalars, regular, S)))
		}),
})}

// ConstantChartLeast — the chart of T lies in every submodule over l holding
// T: it is their meet.
var ConstantChartLeast = constantChartLeastThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartLeast",
	Key:  "prop_b3bee58a9422886c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀l T N:set(A).",
		Hypotheses: []string{
			"submodule(restrict_ring(R, l), regular_module(R), N)",
			"T ⊆ N",
		},
		Conclusion: "constant_chart(R, l, T) ⊆ N",
	},
		func(a *Argument, R *Expr[RingOps[A]], l, T, N *Expr[Set[A]], submoduleN, TInN Fact) {
			a.Show(
				"the chart is the span over l",
				Unfold(ConstantChartDef),
				By(
					submoduleN,
					TInN,
					submodule.SpanLeast.At(
						a.TermAs[RingOps[A]]("restrict_ring(R, l)"),
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(R)"),
						T,
						N)))
		}),
})}

// ConstantChartCombination — a combination of elements of l with
// coefficients in S lies in the chart of S.
var ConstantChartCombination = constantChartCombinationThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartCombination",
	Key:  "prop_f9415a77552d3888",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "lScalars", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "regular", Text: "regular_module(field_ring(M))"},
		},
		Binders: "∀M:field_on(A). ∀l S E:set(A). ∀c:(A → A).",
		Hypotheses: []string{
			"subfield(M, l)",
			"S ⊆ M.carrier",
			"finite(E)",
			"E ⊆ l",
			"∀e:A. e ∈ E ⇒ c(e) ∈ S",
		},
		Conclusion: "module_sum(M.add, M.zero, E, λe:A. c(e) * e) ∈ constant_chart(field_ring(M), l, S)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			l, S, E *Expr[Set[A]],
			c *Arrow[A, A],
			lSubfield, SInField, finiteE, EInL, coefficients Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			lScalars := a.TermAs[RingOps[A]]("«lScalars»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«regular»")
			chart := a.TermAs[Set[A]]("constant_chart(field_ring(M), l, S)")
			chartData := a.Conjuncts(
				GroupPremises(M, lSubfield, SInField, ConstantChartSubmodule.At(m, l, S)),
				"the field is a module over l",
				"the chart is a submodule",
				"the chart holds S")
			lModule, chartSubmodule, SInChart := chartData[0], chartData[1], chartData[2]
			terms := a.Have(
				"each c(e) * e lies in the chart",
				"∀e:A. e ∈ E ⇒ c(e) * e ∈ constant_chart(field_ring(M), l, S)",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					inE := b.Assume()
					members := b.Have(
						"e is a scalar, and c(e) lies in the chart, both in the field",
						"e ∈ l ∧ c(e) ∈ constant_chart(field_ring(M), l, S) ∧ e ∈ M.carrier ∧ c(e) ∈ M.carrier",
						BySets(inE, EInL, coefficients.At(e), SInField, SInChart, lSubfield, field.SubfieldSubset.At(m, l)))
					swap := b.Have(
						"the product commutes",
						"c(e) * e = e * c(e)",
						ByArith(M, members))
					b.Show(
						"the chart is closed under scalars from l",
						swap.Rw(),
						By(
							members,
							chartSubmodule,
							submodule.SubmoduleSmul.At(lScalars, regular, chart, e, b.TermAs[A]("c(e)"))))
				}))
			a.Show(
				"the chart is closed under finite sums",
				By(
					finiteE,
					terms,
					chartSubmodule,
					lModule,
					submodule.SubmoduleModuleSum.At(
						lScalars, regular, chart, E, a.TermAs[Fun[A, A]]("λe:A. c(e) * e"))))
		}),
})}

// ConstantChartCoordinates — the coordinate lemma: an element of the
// composite lies in the chart of S exactly when its coordinates in the basis
// E lie in S. A member of the chart is an l-combination of S, and the
// coordinate of a·y is the coordinate of a, in k, times y, in S.
var ConstantChartCoordinates = constantChartCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartCoordinates",
	Key:  "prop_75f36f4cdb4bb2ba",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "coordinate", Text: "λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(constant_composite(M, K, l)), E, x, e)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E S:set(A). ∀x:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
			"submodule(«scalars»(k), «vectors»(K), S)",
		},
		Conclusion: "x ∈ constant_chart(field_ring(M), l, S) ⇔ " +
			"x ∈ constant_composite(M, K, l) ∧ (∀e:A. e ∈ E ⇒ «coordinate»(x, e) ∈ S)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E, S *Expr[Set[A]],
			x *Expr[A],
			regular, lSubfield, kInL, finiteBasis, basis, subspace Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			lScalars := a.TermAs[RingOps[A]]("«scalars»(l)")
			KScalars := a.TermAs[RingOps[A]]("«scalars»(K)")
			KVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
			composite := a.TermAs[Set[A]]("constant_composite(M, K, l)")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"«vectors»(constant_composite(M, K, l))")
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					constant_composite.ConstantExtensionData.At(m, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			kSubfield, KSubfield, kInK, compositeSubfield, KInC, lInC, EInL, compositeModule, compositeBasis :=
				data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7], data[8]
			KModule := a.Have(
				"K is a module over k",
				"module_on(«scalars»(k), «vectors»(K))",
				By(M, kSubfield, KSubfield, kInK, field_extension.ExtensionModuleOn.At(m, k, K)))
			SInK := a.Have(
				"S lies in K",
				"S ⊆ K",
				By(subspace, submodule.SubmoduleSubset.At(kScalars, KVectors, S)))
			SInField := a.Have(
				"so S lies in the field",
				"S ⊆ M.carrier",
				BySets(SInK, KSubfield, field.SubfieldSubset.At(m, K)))
			lModule := a.Conjuncts(
				GroupPremises(M, lSubfield, SInField, ConstantChartSubmodule.At(m, l, S)),
				"the field is a module over l",
				"the chart is a submodule",
				"the chart holds S")[0]
			a.Iff()
			a.Forward(
				"a member of the chart is an l-combination of S",
				func(b *Argument, inChart Fact) {
					T, _, expansion := b.Obtain2As[Set[A], Fun[A, A]](
						"write x as a finite combination of S over l",
						"∃T:set(A). ∃g:(A → A). "+
							"    finite(T) ∧ "+
							"    T ⊆ S ∧ "+
							"    (∀y:A. y ∈ T ⇒ g(y) ∈ l) ∧ "+
							"    x = module_sum(M.add, M.zero, T, λy:A. g(y) * y)",
						By(
							b.Unfolded(inChart, ConstantChartDef),
							lModule,
							SInField,
							linear_independence.SpanMembership.At(lScalars, ambient, S, x)))
					parts := b.Conjuncts(
						expansion,
						"T is finite",
						"T lies in S",
						"the scalars lie in l",
						"x is the combination")
					finiteT, TInS, scalarsInL, xSum := parts[0], parts[1], parts[2], parts[3]
					term := b.TermAs[Fun[A, A]]("λy:A. g(y) * y")
					factors := b.Have(
						"each term is a product of l and S, inside K'",
						Statement{
							Binders: "∀y:A.",
							Hypotheses: []string{
								"y ∈ T",
							},
							Conclusion: "g(y) ∈ l ∧ " +
								"y ∈ K ∧ " +
								"g(y) ∈ constant_composite(M, K, l) ∧ " +
								"y ∈ constant_composite(M, K, l)",
						},
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							inT := c.Assume()
							c.Show(
								"T lies in S, which lies in K, and the scalars lie in l",
								BySets(inT, TInS, SInK, KInC, lInC, scalarsInL.At(y)))
						}))
					termsInComposite := b.Have(
						"each term lies in K'",
						"∀y:A. y ∈ T ⇒ g(y) * y ∈ constant_composite(M, K, l)",
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							inT := c.Assume()
							c.Show(
								"K' is closed under products",
								By(
									inT,
									factors.At(y),
									compositeSubfield,
									field.SubfieldMul.At(m, composite, c.TermAs[A]("g(y)"), y)))
						}))
					xInComposite := b.Have(
						"so x lies in K'",
						"x ∈ constant_composite(M, K, l)",
						By(
							Normalized,
							xSum,
							compositeModule,
							finiteT,
							termsInComposite,
							module.ModuleSumIn.At(KScalars, compositeVectors, T, term)))
					coordinatesInS := b.Have(
						"each coordinate of x is a sum of coordinates in S",
						"∀e:A. e ∈ E ⇒ «coordinate»(x, e) ∈ S",
						Derive(func(d *Argument) {
							e := d.FixAs[A]("e")
							inE := d.Assume()
							coordinate := d.TermAs[Fun[A, A]]("λv:A. «coordinate»(v, e)")
							linear := d.Have(
								"the coordinate at e is K-linear",
								"module_homomorphism(«scalars»(K), "+
									"    «vectors»(constant_composite(M, K, l)), "+
									"    regular_module(«scalars»(K)), "+
									"    λv:A. «coordinate»(v, e))",
								By(
									compositeModule,
									finiteBasis,
									compositeBasis,
									inE,
									module_dimension.BasisCoordinateLinear.At(KScalars, compositeVectors, E, e)))
							termCoordinates := d.Have(
								"the coordinate of each term lies in S",
								"∀y:A. y ∈ T ⇒ «coordinate»(g(y) * y, e) ∈ S",
								Derive(func(f *Argument) {
									y := f.FixAs[A]("y")
									inT := f.Assume()
									inS := f.Have(
										"y lies in S",
										"y ∈ S",
										BySets(inT, TInS))
									scalar := f.TermAs[A]("g(y)")
									memberships := f.Conjuncts(
										GroupPremises(inT, factors.At(y)),
										"g(y) lies in l",
										"y lies in K",
										"g(y) lies in K'",
										"y lies in K'")
									scaled := f.Conjuncts(
										GroupPremises(
											memberships[0],
											M,
											regular,
											lSubfield,
											kInL,
											finiteBasis,
											basis,
											memberships[1],
											inE,
											constant_composite.ConstantCoordinateScale.At(m, K, k, l, E, scalar, y, e)),
										"its coordinate lies in k",
										"y moves out of the coordinate")
									f.Show(
										"a k-multiple of y lies in S",
										scaled[1].Rw(),
										By(
											scaled[0],
											inS,
											memberships[0],
											subspace,
											submodule.SubmoduleSmul.At(kScalars, KVectors, S, f.TermAs[A]("«coordinate»(g(y), e)"), y)))
								}))
							summed := d.Have(
								"the coordinate of x is the sum of the coordinates of the terms",
								"«coordinate»(x, e) = module_sum(M.add, M.zero, T, λy:A. «coordinate»(g(y) * y, e))",
								By(
									xSum,
									finiteT,
									linear,
									termsInComposite,
									module_homomorphism.HomSum.At(
										KScalars,
										compositeVectors,
										d.TermAs[module_record.ModuleOps[A, A]]("regular_module(«scalars»(K))"),
										coordinate,
										T,
										term)))
							d.Show(
								"S is closed under finite sums",
								summed.Rw(),
								By(
									finiteT,
									termCoordinates,
									subspace,
									KModule,
									submodule.SubmoduleModuleSum.At(
										kScalars, KVectors, S, T, d.TermAs[Fun[A, A]]("λy:A. «coordinate»(g(y) * y, e)"))))
						}))
					b.Show(
						"x lies in K' with its coordinates in S",
						By(xInComposite, coordinatesInS))
				})
			a.Backward(
				"an element of K' is the combination of E with its coordinates",
				func(b *Argument, membership Fact) {
					parts := b.Conjuncts(
						membership,
						"x lies in K'",
						"its coordinates lie in S")
					coordinates := parts[1]
					expansion := b.Conjuncts(
						GroupPremises(
							data[7],
							finiteBasis,
							data[8],
							parts[0],
							module_dimension.BasisCoordinatesSpec.At(KScalars, compositeVectors, E, x)),
						"the coordinates are scalars",
						"they vanish off E",
						"x is their combination")[2]
					combination := b.Have(
						"the combination of E with the coordinates of x lies in the chart",
						"module_sum(M.add, M.zero, E, λe:A. «coordinate»(x, e) * e) ∈ constant_chart(field_ring(M), l, S)",
						By(
							M,
							lSubfield,
							SInField,
							finiteBasis,
							EInL,
							coordinates,
							ConstantChartCombination.At(m, l, S, E, b.TermAs[Fun[A, A]]("λe:A. «coordinate»(x, e)"))))
					b.Show(
						"a combination of E with coefficients in S lies in the chart",
						By(Normalized, expansion, combination))
				})
		}),
})}

// ConstantChartMembers — the chart of S is the direct sum of the lines S·e:
// its members are the combinations of E with coefficients in S.
var ConstantChartMembers = constantChartMembersThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartMembers",
	Key:  "prop_743529d48a9e3acc",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "coordinate", Text: "λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(constant_composite(M, K, l)), E, x, e)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E S:set(A). ∀x:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
			"submodule(«scalars»(k), «vectors»(K), S)",
		},
		Conclusion: "x ∈ constant_chart(field_ring(M), l, S) ⇔ " +
			"∃c:(A → A). (∀e:A. e ∈ E ⇒ c(e) ∈ S) ∧ x = module_sum(M.add, M.zero, E, λe:A. c(e) * e)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E, S *Expr[Set[A]],
			x *Expr[A],
			regular, lSubfield, kInL, finiteBasis, basis, subspace Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			KScalars := a.TermAs[RingOps[A]]("«scalars»(K)")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			KVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"«vectors»(constant_composite(M, K, l))")
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					constant_composite.ConstantExtensionData.At(m, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			KSubfield, EInL, compositeModule, compositeBasis := data[1], data[6], data[7], data[8]
			coordinates := ConstantChartCoordinates.At(m, K, k, l, E, S, x)
			SInField := a.Have(
				"S lies in the field",
				"S ⊆ M.carrier",
				BySets(
					subspace,
					KSubfield,
					submodule.SubmoduleSubset.At(kScalars, KVectors, S),
					field.SubfieldSubset.At(m, K)))
			a.Iff()
			a.Forward(
				"take the coordinates of x",
				func(b *Argument, inChart Fact) {
					membership := b.Conjuncts(
						b.Have(
							"x lies in K' with its coordinates in S",
							"x ∈ constant_composite(M, K, l) ∧ (∀e:A. e ∈ E ⇒ «coordinate»(x, e) ∈ S)",
							By(M, inChart, coordinates, regular, lSubfield, kInL, finiteBasis, basis, subspace)),
						"x lies in K'",
						"its coordinates lie in S")
					b.Take(b.TermAs[Fun[A, A]]("λe:A. «coordinate»(x, e)"))
					b.Show(
						"x is the combination of E with its coordinates",
						By(
							membership[1],
							membership[0],
							compositeModule,
							finiteBasis,
							compositeBasis,
							module_dimension.BasisCoordinatesSpec.At(KScalars, compositeVectors, E, x)))
				})
			a.Backward(
				"a combination of E with coefficients in S lies in the chart",
				func(b *Argument, combination Fact) {
					c, chosen := b.UnpackAs[Fun[A, A]](combination, "c")
					parts := b.Conjuncts(
						chosen,
						"the coefficients lie in S",
						"x is the combination")
					b.Show(
						"the chart holds such combinations",
						parts[1].Rw(),
						By(M, lSubfield, SInField, finiteBasis, EInL, parts[0], ConstantChartCombination.At(m, l, S, E, c)))
				})
		}),
})}

// ConstantChartMeet — charts commute with intersections: the coordinates of
// an element of both charts lie in both subspaces.
var ConstantChartMeet = constantChartMeetThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartMeet",
	Key:  "prop_38412217ab3b0d20",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S T:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"submodule(«scalars»(k), «vectors»(K), S)",
			"submodule(«scalars»(k), «vectors»(K), T)",
		},
		Conclusion: "«chart»(S ∩ T) = «chart»(S) ∩ «chart»(T)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, T *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, SSubspace, TSubspace Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			KVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)")
			meet := a.TermAs[Set[A]]("S ∩ T")
			E, basisData := a.ObtainAs[Set[A]](
				"take a finite k-basis of l",
				"∃E:set(A). finite(E) ∧ module_basis(«scalars»(k), «vectors»(l), E)",
				By(
					finiteExtension,
					field_extension.FiniteExtensionDef.At(m, k, l),
					module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
			basisParts := a.Conjuncts(
				basisData,
				"E is finite",
				"E is a k-basis of l")
			finiteBasis, basis := basisParts[0], basisParts[1]
			meetSubspace := a.Have(
				"S ∩ T is a k-subspace of K",
				"submodule(«scalars»(k), «vectors»(K), S ∩ T)",
				By(SSubspace, TSubspace, submodule.SubmoduleInter.At(kScalars, KVectors, S, T)))
			pointwise := a.Have(
				"an element lies in the chart of S ∩ T exactly when it lies in both charts",
				"∀x:A. x ∈ «chart»(S ∩ T) ⇔ x ∈ «chart»(S) ∧ x ∈ «chart»(T)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.Show(
						"read each chart by coordinates",
						BySets(
							M,
							regular,
							lSubfield,
							kInL,
							finiteBasis,
							basis,
							SSubspace,
							TSubspace,
							meetSubspace,
							ConstantChartCoordinates.At(m, K, k, l, E, meet, x),
							ConstantChartCoordinates.At(m, K, k, l, E, S, x),
							ConstantChartCoordinates.At(m, K, k, l, E, T, x)))
				}))
			a.Show(
				"so the two sets have one set of members",
				BySets(pointwise))
		}),
})}

// ConstantChartContract — the chart of S lies in the composite and meets K
// in S. An element x of K in the chart has the coordinate d·x at an element
// of E where the coordinate d of one is not zero; d is a unit of k, so x
// lies in S.
var ConstantChartContract = constantChartContractThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartContract",
	Key:  "prop_e6cac5a1b94fd102",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "coordinate", Text: "λE:set(A). λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(constant_composite(M, K, l)), E, x, e)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"submodule(«scalars»(k), «vectors»(K), S)",
		},
		Conclusion: "«chart»(S) ⊆ constant_composite(M, K, l) ∧ «chart»(S) ∩ K = S",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subspace Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			KScalars := a.TermAs[RingOps[A]]("«scalars»(K)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			KVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"«vectors»(constant_composite(M, K, l))")
			one := a.TermAs[A]("M.one")
			E, basisData := a.ObtainAs[Set[A]](
				"take a finite k-basis of l",
				"∃E:set(A). finite(E) ∧ module_basis(«scalars»(k), «vectors»(l), E)",
				By(
					finiteExtension,
					field_extension.FiniteExtensionDef.At(m, k, l),
					module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
			basisParts := a.Conjuncts(
				basisData,
				"E is finite",
				"E is a k-basis of l")
			finiteBasis, basis := basisParts[0], basisParts[1]
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					basisParts[0],
					basisParts[1],
					constant_composite.ConstantExtensionData.At(m, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			kSubfield, KSubfield, lInC, EInL, compositeModule := data[0], data[1], data[5], data[6], data[7]
			oneInL := a.Have(
				"one lies in l",
				"M.one ∈ l",
				By(lSubfield, field.SubfieldOne.At(m, l)))
			oneInComposite := a.Have(
				"so one lies in K'",
				"M.one ∈ constant_composite(M, K, l)",
				BySets(oneInL, lInC))
			coordinates := a.Have(
				"a member of the chart lies in K' with its coordinates in S",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ «chart»(S)",
					},
					Conclusion: "x ∈ constant_composite(M, K, l) ∧ (∀e:A. e ∈ E ⇒ «coordinate»(E, x, e) ∈ S)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inChart := b.Assume()
					b.Show(
						"a member of the chart lies in the composite, with coordinates in S",
						By(
							M,
							inChart,
							regular,
							lSubfield,
							kInL,
							finiteBasis,
							basis,
							subspace,
							ConstantChartCoordinates.At(m, K, k, l, E, S, x)))
				}))
			d, dData := a.ObtainAs[A](
				"one has a nonzero coordinate",
				"∃d:A. d ∈ E ∧ «coordinate»(E, M.one, d) ≠ M.zero",
				Derive(func(b *Argument) {
					allZero := b.SupposeNot()
					expansion := b.Conjuncts(
						GroupPremises(
							data[7],
							basisParts[0],
							data[8],
							oneInComposite,
							module_dimension.BasisCoordinatesSpec.At(KScalars, compositeVectors, E, one)),
						"the coordinates are scalars",
						"they vanish off E",
						"one is their combination")[2]
					terms := b.Have(
						"every term of the expansion of one is zero",
						"∀e:A. e ∈ E ⇒ «coordinate»(E, M.one, e) * e = M.zero",
						Derive(func(c *Argument) {
							c.FixAs[A]("e")
							inE := c.Assume()
							member := c.Have(
								"e lies in the field",
								"e ∈ M.carrier",
								BySets(inE, EInL, lSubfield, field.SubfieldSubset.At(m, l)))
							zero := c.Have(
								"the coordinate vanishes",
								"«coordinate»(E, M.one, e) = M.zero",
								By(allZero, inE))
							c.Show(
								"zero times e",
								zero.Rw(),
								ByArith(M, member))
						}))
					b.Show(
						"then one would be zero",
						By(
							M,
							expansion,
							terms,
							compositeModule,
							finiteBasis,
							field.OneNotZeroOn.At(m),
							module.ModuleSumZero.At(
								KScalars, compositeVectors, E, b.TermAs[Fun[A, A]]("λe:A. «coordinate»(E, M.one, e) * e"))))
				}))
			dParts := a.Conjuncts(
				dData,
				"d lies in E",
				"the coordinate of one at d is not zero")
			dInE, dNonzero := dParts[0], dParts[1]
			SInK := a.Have(
				"S lies in K",
				"S ⊆ K",
				By(subspace, submodule.SubmoduleSubset.At(kScalars, KVectors, S)))
			sInField := a.Have(
				"so S lies in the field",
				"S ⊆ M.carrier",
				BySets(SInK, KSubfield, field.SubfieldSubset.At(m, K)))
			SInChart := a.Conjuncts(
				GroupPremises(M, lSubfield, sInField, ConstantChartSubmodule.At(m, l, S)),
				"the field is a module over l",
				"the chart is a submodule",
				"the chart holds S")[2]
			contraction := a.Have(
				"an element of K in the chart lies in S",
				"∀x:A. x ∈ «chart»(S) ∧ x ∈ K ⇒ x ∈ S",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					assumed := b.Conjuncts(
						b.Assume(),
						"x lies in the chart",
						"x lies in K")
					inChart, inK := assumed[0], assumed[1]
					scaled := b.Conjuncts(
						GroupPremises(
							M,
							regular,
							lSubfield,
							kInL,
							basisParts[0],
							basisParts[1],
							oneInL,
							inK,
							dParts[0],
							constant_composite.ConstantCoordinateScale.At(m, K, k, l, E, one, x, d)),
						"the coordinate of one lies in k",
						"x moves out of the coordinate")
					unit := b.TermAs[A]("«coordinate»(E, M.one, d)")
					inverse := b.TermAs[A]("M.inv(«coordinate»(E, M.one, d))")
					memberships := b.Have(
						"the coordinate, its inverse and x lie in the field, and the inverse in k",
						"«coordinate»(E, M.one, d) ∈ M.carrier ∧ "+
							"M.inv(«coordinate»(E, M.one, d)) ∈ k ∧ "+
							"M.inv(«coordinate»(E, M.one, d)) ∈ M.carrier ∧ "+
							"x ∈ M.carrier",
						BySets(
							scaled[0],
							inK,
							kSubfield,
							KSubfield,
							field.SubfieldSubset.At(m, k),
							field.SubfieldSubset.At(m, K),
							field.SubfieldInv.At(m, k, unit)))
					times := b.Have(
						"one times x is x",
						"M.one * x = x",
						ByArith(M, memberships))
					inS := b.Have(
						"the product of the coordinate with x is a coordinate of x, in S",
						"«coordinate»(E, M.one, d) * x ∈ S",
						Derive(func(c *Argument) {
							atD := c.Conjuncts(
								GroupPremises(inChart, coordinates.At(x)),
								"x lies in K'",
								"its coordinates lie in S")[1]
							c.Do(scaled[1].RwRev(), times.Rw())
							c.Show(
								"a coordinate of x",
								By(atD, dInE))
						}))
					cancel := b.Have(
						"the inverse of the coordinate cancels it",
						"M.inv(«coordinate»(E, M.one, d)) * «coordinate»(E, M.one, d) = M.one",
						By(M, memberships, dNonzero, field.MulLeftInverseOn.At(m, unit)))
					back := b.Have(
						"so x is a k-multiple of that product",
						"M.inv(«coordinate»(E, M.one, d)) * («coordinate»(E, M.one, d) * x) = x",
						ByArith(M, memberships, Scaled(x, cancel)))
					b.Show(
						"S is a k-subspace",
						By(
							back,
							inS,
							memberships,
							subspace,
							submodule.SubmoduleSmul.At(
								kScalars, KVectors, S, inverse, b.TermAs[A]("«coordinate»(E, M.one, d) * x"))))
				}))
			a.Show(
				"read the two inclusions off the coordinates",
				BySets(coordinates, contraction, SInK, SInChart))
		}),
})}

// ConstantSubspaceSubmodule — a k-subspace of a subfield K is a k-submodule
// of the whole field.
var ConstantSubspaceSubmodule = constantSubspaceSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "ConstantSubspaceSubmodule",
	Key:  "prop_26b50ad1190b328c",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "kScalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
		},
		Binders: "∀M:field_on(A). ∀K k S:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"submodule(«kScalars», restrict_module(«ambient», K), S)",
		},
		Conclusion: "submodule(«kScalars», «ambient», K) ∧ submodule(«kScalars», «ambient», S)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, S *Expr[Set[A]],
			kSubfield, KSubfield, kInK, subspace Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			kScalars := a.TermAs[RingOps[A]]("«kScalars»")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			whole := a.Have(
				"K is a k-submodule of the field",
				"submodule(«kScalars», «ambient», K)",
				By(
					Normalized,
					M,
					kSubfield,
					KSubfield,
					kInK,
					field.CarrierSubfield.At(m),
					field.SubfieldSubset.At(m, K),
					module_record.RestrictModuleCarrier.At(ambient),
					field_extension.SubfieldSubmodule.At(m, k, K, a.TermAs[Set[A]]("M.carrier"))))
			a.Show(
				"a submodule of a submodule is a submodule",
				By(whole, subspace, submodule.SubmoduleTrans.At(kScalars, ambient, K, S)))
		}),
})}

// ConstantRingSubspace — a ring between k and K is a k-subspace of K.
var ConstantRingSubspace = constantRingSubspaceThm{family.Add(registry.ProofEntry{
	Name: "ConstantRingSubspace",
	Key:  "prop_7c7091855672f001",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"S ⊆ K",
		},
		Conclusion: "submodule(restrict_ring(field_ring(M), k), " +
			"    restrict_module(regular_module(field_ring(M)), K), " +
			"    S)",
	},
		func(a *Argument, M field.FieldFact[on.M], K, k, S *Expr[Set[A]], subringS, kInS, SInK Fact) {
			a.Show(
				"S is a submodule of the field over k, and it lies in K",
				By(
					M,
					subringS,
					kInS,
					SInK,
					principal_ideal_domain.ConstantSubringSubmodule.At(a.TermAs[FieldOps[A]]("M"), k, S),
					submodule.SubmoduleRestrict.At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), k)"),
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))"),
						K,
						S)))
		}),
})}

// ConstantChartIndependent — a subset of K independent over a ring S between k
// and K stays independent over the chart of S: the E-coordinates of a relation
// over the chart are relations over S.
var ConstantChartIndependent = constantChartIndependentThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartIndependent",
	Key:  "prop_6a95d2fcd90a1f33",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "coordinate", Text: "λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(constant_composite(M, K, l)), E, x, e)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E S T:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
			"submodule(«scalars»(k), «vectors»(K), S)",
			"T ⊆ K",
			"module_independent(«scalars»(S), «ambient», T)",
		},
		Conclusion: "module_independent(«scalars»(«chart»(S)), «ambient», T)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E, S, T *Expr[Set[A]],
			regular, lSubfield, kInL, finiteBasis, basis, subspace, TInK, independent Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			SScalars := a.TermAs[RingOps[A]]("«scalars»(S)")
			KScalars := a.TermAs[RingOps[A]]("«scalars»(K)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"«vectors»(constant_composite(M, K, l))")
			composite := a.TermAs[Set[A]]("constant_composite(M, K, l)")
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					constant_composite.ConstantExtensionData.At(ops, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			KSubfield, compositeSubfield, KInC, EInL, compositeModule, compositeBasis :=
				data[1], data[3], data[4], data[6], data[7], data[8]
			TInField := a.Have(
				"T lies in the field",
				"T ⊆ M.carrier",
				BySets(TInK, KSubfield, field.SubfieldSubset.At(ops, K)))
			vanishing := a.Have(
				"a relation over the chart of S among the elements of T vanishes",
				Statement{
					Binders: "∀U:set(A). ∀g:(A → A).",
					Hypotheses: []string{
						"finite(U)",
						"U ⊆ T",
						"∀y:A. y ∈ U ⇒ g(y) ∈ «chart»(S)",
						"module_sum(M.add, M.zero, U, λy:A. g(y) * y) = M.zero",
					},
					Conclusion: "∀x:A. x ∈ U ⇒ g(x) = M.zero",
				},
				Derive(func(b *Argument) {
					U := b.FixAs[Set[A]]("U")
					b.FixAs[Fun[A, A]]("g")
					relation := b.Conjuncts(
						b.Assume(),
						"U is finite",
						"U lies in T",
						"the scalars lie in the chart of S",
						"the relation")
					finiteU, UInT, scalarsInChart, sumZero := relation[0], relation[1], relation[2], relation[3]
					x := b.FixAs[A]("x")
					xInU := b.Assume()
					factors := b.Have(
						"each scalar lies in the composite, its coordinates "+
							"in S, each y in K, and each term in the composite",
						Statement{
							Binders: "∀y:A.",
							Hypotheses: []string{
								"y ∈ U",
							},
							Conclusion: "(g(y) ∈ constant_composite(M, K, l) ∧ ∀e:A. e ∈ E ⇒ «coordinate»(g(y), e) ∈ S) ∧ " +
								"y ∈ K ∧ " +
								"g(y) * y ∈ constant_composite(M, K, l)",
						},
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							inU := c.Assume()
							read := c.Have(
								"a member of the chart lies in the composite with coordinates in S",
								"g(y) ∈ constant_composite(M, K, l) ∧ ∀e:A. e ∈ E ⇒ «coordinate»(g(y), e) ∈ S",
								By(
									M,
									regular,
									lSubfield,
									kInL,
									finiteBasis,
									basis,
									subspace,
									scalarsInChart.At(y),
									inU,
									ConstantChartCoordinates.At(ops, K, k, l, E, S, c.TermAs[A]("g(y)"))))
							yInK := c.Have(
								"y lies in K",
								"y ∈ K",
								BySets(inU, UInT, TInK))
							yInC := c.Have(
								"so it lies in the composite",
								"y ∈ constant_composite(M, K, l)",
								BySets(yInK, KInC))
							c.Show(
								"which is closed under products",
								By(
									read,
									yInK,
									yInC,
									compositeSubfield,
									field.SubfieldMul.At(ops, composite, c.TermAs[A]("g(y)"), y)))
						}))
					term := b.TermAs[Fun[A, A]]("λy:A. g(y) * y")
					coordinatesVanish := b.Have(
						"each coordinate of g(x) vanishes",
						"∀e:A. e ∈ E ⇒ «coordinate»(g(x), e) = M.zero",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							inE := c.Assume()
							coordinate := c.TermAs[Fun[A, A]]("λv:A. «coordinate»(v, e)")
							linear := c.Have(
								"the coordinate at e is K-linear",
								"module_homomorphism(«scalars»(K), "+
									"    «vectors»(constant_composite(M, K, l)), "+
									"    regular_module(«scalars»(K)), "+
									"    λv:A. «coordinate»(v, e))",
								By(
									compositeModule,
									finiteBasis,
									compositeBasis,
									inE,
									module_dimension.BasisCoordinateLinear.At(KScalars, compositeVectors, E, e)))
							scaled := c.Have(
								"on each term the coordinate lies in S and factors out",
								"∀y:A. y ∈ U ⇒ «coordinate»(g(y), e) ∈ S ∧ «coordinate»(g(y) * y, e) = «coordinate»(g(y), e) * y",
								Derive(func(d *Argument) {
									y := d.FixAs[A]("y")
									yInU := d.Assume()
									parts := d.Conjuncts(
										GroupPremises(yInU, factors.At(y)),
										"g(y) lies in the composite",
										"its coordinates lie in S",
										"y lies in K",
										"the term lies in the composite")
									d.Show(
										"the coordinate of a product with a factor from K",
										By(
											M,
											parts[0],
											parts[1],
											parts[2],
											inE,
											regular,
											lSubfield,
											kInL,
											finiteBasis,
											basis,
											constant_composite.ConstantCoordinateProduct.At(ops, K, k, l, E, d.TermAs[A]("g(y)"), y, e)))
								}))
							relationCoordinates := c.Have(
								"the coordinates at e give a relation over S",
								"module_sum(M.add, M.zero, U, λy:A. «coordinate»(g(y), e) * y) = M.zero",
								Derive(func(d *Argument) {
									transported := d.Have(
										"the coordinate of the sum is the sum of the coordinates",
										"«coordinate»(module_sum(M.add, M.zero, U, λy:A. g(y) * y), e) = "+
											"module_sum(M.add, M.zero, U, λy:A. «coordinate»(g(y) * y, e))",
										By(
											finiteU,
											linear,
											factors,
											module_homomorphism.HomSum.At(
												KScalars,
												compositeVectors,
												d.TermAs[module_record.ModuleOps[A, A]]("regular_module(«scalars»(K))"),
												coordinate,
												U,
												term)))
									zero := d.Have(
										"the coordinate of zero is zero",
										"«coordinate»(M.zero, e) = M.zero",
										By(linear, module_homomorphism.HomZero.Read(linear)))
									same := d.Have(
										"the two sums agree term by term",
										"module_sum(M.add, M.zero, U, λy:A. «coordinate»(g(y) * y, e)) = "+
											"module_sum(M.add, M.zero, U, λy:A. «coordinate»(g(y), e) * y)",
										By(
											scaled,
											module.ModuleSumCongruence.At(
												d.TermAs[Op[A]]("M.add"),
												d.TermAs[A]("M.zero"),
												U,
												d.TermAs[Fun[A, A]]("λy:A. «coordinate»(g(y) * y, e)"),
												d.TermAs[Fun[A, A]]("λy:A. «coordinate»(g(y), e) * y"))))
									d.Do(same.RwRev(), transported.RwRev(), sumZero.Rw())
									d.Show(
										"the sum is zero",
										By(zero))
								}))
							c.Show(
								"T is independent over S",
								By(
									independent,
									finiteU,
									UInT,
									scaled,
									relationCoordinates,
									xInU,
									linear_independence.IndependentVanishingCombination.At(
										SScalars, ambient, T, U, c.TermAs[Fun[A, A]]("λy:A. «coordinate»(g(y), e)"), x)))
						}))
					scalar := b.TermAs[A]("g(x)")
					valueInComposite := b.Have(
						"g(x) lies in the composite",
						"g(x) ∈ constant_composite(M, K, l)",
						By(factors.At(x), xInU))
					expansion := b.Conjuncts(
						GroupPremises(
							data[7],
							finiteBasis,
							data[8],
							valueInComposite,
							module_dimension.BasisCoordinatesSpec.At(KScalars, compositeVectors, E, scalar)),
						"the coordinates are scalars",
						"they vanish off E",
						"g(x) is their combination")[2]
					terms := b.Have(
						"every term of the expansion of g(x) is zero",
						"∀e:A. e ∈ E ⇒ «coordinate»(g(x), e) * e = M.zero",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							inE := c.Assume()
							member := c.Have(
								"e lies in the field",
								"e ∈ M.carrier",
								BySets(inE, EInL, lSubfield, field.SubfieldSubset.At(ops, l)))
							c.Show(
								"zero times e",
								GroupPremises(inE, coordinatesVanish.At(e)).Rw(),
								ByArith(M, member))
						}))
					b.Show(
						"so g(x) is an empty combination",
						By(
							expansion,
							terms,
							compositeModule,
							finiteBasis,
							module.ModuleSumZero.At(
								KScalars, compositeVectors, E, b.TermAs[Fun[A, A]]("λe:A. «coordinate»(g(x), e) * e"))))
				}))
			a.Show(
				"T lies in the field and every relation vanishes",
				Unfold(linear_independence.ModuleIndependentDef),
				By(TInField, vanishing))
		}),
})}

// ConstantIndependentLifts — a subset of K independent over k stays
// independent over l: the chart of the constants is l, and independence passes
// to the chart of a subspace.
var ConstantIndependentLifts = constantIndependentLiftsThm{family.Add(registry.ProofEntry{
	Name: "ConstantIndependentLifts",
	Key:  "prop_f3bead3612509ec4",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
		},
		Binders: "∀M:field_on(A). ∀K k l E T:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
			"T ⊆ K",
			"module_independent(«scalars»(k), «ambient», T)",
		},
		Conclusion: "module_independent(«scalars»(l), «ambient», T)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E, T *Expr[Set[A]],
			regular, lSubfield, kInL, finiteBasis, basis, TInK, independent Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					constant_composite.ConstantExtensionData.At(m, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			kSubfield, kInK := data[0], data[2]
			subspace := a.Have(
				"k is a k-subspace of K",
				"submodule(«scalars»(k), «vectors»(K), k)",
				By(
					kSubfield,
					kInK,
					field_extension.SubfieldScalars.Read(M).At(k),
					set_order.SubsetRefl.At(k),
					ConstantRingSubspace.Read(M).At(K, k, k)))
			finiteExtension := a.Have(
				"l is finite over k",
				"finite_extension(M, k, l)",
				By(
					finiteBasis,
					basis,
					field_extension.FiniteExtensionDef.At(m, k, l),
					module_dimension.FiniteDimensionalDef.At(
						a.TermAs[RingOps[A]]("«scalars»(k)"), a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)"))))
			a.Show(
				"the chart of k is l, and independence over k passes to it",
				By(
					Normalized,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					subspace,
					TInK,
					independent,
					finiteExtension,
					ConstantChartOfConstants.Read(M).At(K, k, l),
					ConstantChartIndependent.Read(M).At(K, k, l, E, k, T)))
		}),
})}

// ConstantChartQuotient — charts keep the dimension of a quotient. A k-basis
// U of a complement of T in S stays independent over l, its l-span complements
// the chart of T in the chart of S, and the dimension of either quotient is
// the size of U.
var ConstantChartQuotient = constantChartQuotientThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartQuotient",
	Key:  "prop_480999727f2fe2e1",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "span", Text: "λX:set(A). λY:set(A). " +
				"    module_span(restrict_ring(field_ring(M), X), regular_module(field_ring(M)), Y)"},
			{Name: "quotient", Text: "quotient_module(restrict_module(«ambient», S), T)"},
			{Name: "chartQuotient", Text: "quotient_module(restrict_module(«ambient», «chart»(S)), " +
				"    «chart»(T))"},
		},
		Binders: "∀M:field_on(A). ∀K k l S T:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"submodule(«scalars»(k), «vectors»(K), S)",
			"submodule(«scalars»(k), «vectors»(K), T)",
			"T ⊆ S",
			"finite_dimensional(«scalars»(k), «quotient»)",
		},
		Conclusion: "finite_dimensional(«scalars»(l), «chartQuotient») ∧ " +
			"module_dim(«scalars»(l), «chartQuotient») = module_dim(«scalars»(k), «quotient»)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, T *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, SSubspace, TSubspace, TInS, finiteQuotient Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			lScalars := a.TermAs[RingOps[A]]("«scalars»(l)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			inverse := a.TermAs[Fun[A, A]]("M.inv")
			E, basisData := a.ObtainAs[Set[A]](
				"take a finite k-basis of l",
				"∃E:set(A). finite(E) ∧ module_basis(«scalars»(k), «vectors»(l), E)",
				By(
					finiteExtension,
					field_extension.FiniteExtensionDef.At(m, k, l),
					module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
			basisParts := a.Conjuncts(
				basisData,
				"E is finite",
				"E is a k-basis of l")
			finiteBasis, basis := basisParts[0], basisParts[1]
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					basisParts[0],
					basisParts[1],
					constant_composite.ConstantExtensionData.At(m, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			kSubfield, KSubfield := data[0], data[1]
			fieldsOverK := a.Have(
				"k and l are fields inside their rings",
				"ring_subfield(«scalars»(k), M.inv, k) ∧ ring_subfield(«scalars»(l), M.inv, l)",
				By(
					kSubfield,
					lSubfield,
					field.SubfieldRingSubfield.Read(M).At(k, k),
					field.SubfieldRingSubfield.Read(M).At(l, l)))
			kModule := a.Conjuncts(
				GroupPremises(data[0], M, field_extension.SubfieldScalars.At(m, k)),
				"k is a subring",
				"the field is a module over k")[1]
			SAmbient := a.Conjuncts(
				GroupPremises(M, data[0], data[1], data[2], SSubspace, ConstantSubspaceSubmodule.At(m, K, k, S)),
				"K is a k-submodule of the field",
				"S is a k-submodule of the field")
			KAmbient, SSubmodule := SAmbient[0], SAmbient[1]
			TSubmodule := a.Have(
				"so is T",
				"submodule(«scalars»(k), «ambient», T)",
				By(KAmbient, TSubspace, submodule.SubmoduleTrans.At(kScalars, ambient, K, T)))
			U, complement := a.ObtainAs[Set[A]](
				"lift a k-basis of the quotient to a complement of T in S",
				"∃U:set(A). "+
					"    finite(U) ∧ "+
					"    U ⊆ S ∧ "+
					"    module_independent(«scalars»(k), «ambient», U) ∧ "+
					"    S ⊆ set_mul(M.add, «span»(k, U), T) ∧ "+
					"    «span»(k, U) ∩ T ⊆ {M.zero} ∧ "+
					"    card(U) = module_dim(«scalars»(k), «quotient»)",
				By(
					kModule,
					fieldsOverK,
					SSubmodule,
					TSubmodule,
					TInS,
					finiteQuotient,
					module_dimension.QuotientComplementLift.At(kScalars, ambient, inverse, S, T)))
			parts := a.Conjuncts(
				complement,
				"U is finite",
				"U lies in S",
				"U is independent over k",
				"S lies in the sum",
				"the sum is direct",
				"the size of U is the dimension")
			finiteU, UInS, independentU, SInSum, directSum, sizeU :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			SInK := a.Have(
				"S and T lie in K",
				"S ⊆ K ∧ T ⊆ K",
				By(
					SSubspace,
					TSubspace,
					submodule.SubmoduleSubset.At(kScalars, a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)"), S),
					submodule.SubmoduleSubset.At(kScalars, a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)"), T)))
			inField := a.Have(
				"U lies in K, and K, S, T and U lie in the field",
				"U ⊆ K ∧ K ⊆ M.carrier ∧ S ⊆ M.carrier ∧ T ⊆ M.carrier ∧ U ⊆ M.carrier",
				BySets(UInS, SInK, KSubfield, field.SubfieldSubset.At(m, K)))
			fieldParts := a.Conjuncts(
				inField,
				"U lies in K",
				"K lies in the field",
				"S lies in the field",
				"T lies in the field",
				"U lies in the field")
			UInK, KInField, TInField, UInField := fieldParts[0], fieldParts[1], fieldParts[3], fieldParts[4]
			chartS := a.Conjuncts(
				GroupPremises(M, lSubfield, fieldParts[2], ConstantChartSubmodule.At(m, l, S)),
				"the field is a module over l",
				"the chart of S is a submodule",
				"the chart of S holds S")
			lModule, chartSSubmodule, SInChart := chartS[0], chartS[1], chartS[2]
			chartT := a.Conjuncts(
				a.Have(
					"the chart of T is a submodule holding T",
					"submodule(«scalars»(l), «ambient», «chart»(T)) ∧ T ⊆ «chart»(T)",
					By(M, lSubfield, TInField, ConstantChartSubmodule.At(m, l, T))),
				"the chart of T is a submodule",
				"the chart of T holds T")
			chartTSubmodule, TInChart := chartT[0], chartT[1]
			W := a.TermAs[Set[A]]("«span»(k, U)")
			P := a.TermAs[Set[A]]("«span»(l, U)")
			chartOfT := a.TermAs[Set[A]]("«chart»(T)")
			lifted := a.Have(
				"U stays independent over l",
				"module_independent(«scalars»(l), «ambient», U)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					UInK,
					independentU,
					ConstantIndependentLifts.At(m, K, k, l, E, U)))
			WData := a.Conjuncts(
				a.Have(
					"the k-span of U is a k-submodule of the field, inside K",
					"submodule(«scalars»(k), «ambient», «span»(k, U)) ∧ «span»(k, U) ⊆ K",
					By(
						kModule,
						UInField,
						UInK,
						KAmbient,
						submodule.SpanSubmodule.At(kScalars, ambient, U),
						submodule.SpanLeast.At(kScalars, ambient, U, K))),
				"it is a submodule",
				"it lies in K")
			WSubmodule, WInK := WData[0], WData[1]
			WSubspace := a.Have(
				"so it is a k-subspace of K",
				"submodule(«scalars»(k), «vectors»(K), «span»(k, U))",
				By(WSubmodule, WInK, submodule.SubmoduleRestrict.At(kScalars, ambient, K, W)))
			chartW := a.Have(
				"its chart is the l-span of U",
				"«chart»(«span»(k, U)) = «span»(l, U)",
				Unfold(ConstantChartDef),
				By(lModule, kInL, UInField, submodule.SpanOfSubringSpan.At(lScalars, ambient, kScalars, U)))
			WChart := a.Conjuncts(
				a.Have(
					"the l-span of U holds the k-span and is a submodule over l",
					"«span»(k, U) ⊆ «span»(l, U) ∧ submodule(«scalars»(l), «ambient», «span»(l, U))",
					Derive(func(b *Argument) {
						WInField := b.Have(
							"the k-span lies in the field",
							"«span»(k, U) ⊆ M.carrier",
							BySets(WInK, KInField))
						holds := b.Have(
							"the chart of the k-span holds it",
							"«span»(k, U) ⊆ «chart»(«span»(k, U))",
							By(M, lSubfield, WInField, ConstantChartSubmodule.At(m, l, W)))
						first := b.Have(
							"so the l-span holds it",
							"«span»(k, U) ⊆ «span»(l, U)",
							chartW.RwRev(),
							By(holds))
						b.Show(
							"and a span is a submodule",
							By(first, lModule, UInField, submodule.SpanSubmodule.At(lScalars, ambient, U)))
					})),
				"the l-span holds the k-span",
				"the l-span is a submodule")
			WInP, PSubmodule := WChart[0], WChart[1]
			meet := a.Have(
				"the chart of the meet is the meet of the charts",
				"«chart»(«span»(k, U) ∩ T) = «chart»(«span»(k, U)) ∩ «chart»(T)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					WSubspace,
					TSubspace,
					ConstantChartMeet.At(m, K, k, l, W, T)))
			zeroMeet := a.Have(
				"the chart of the meet is zero",
				"«chart»(«span»(k, U) ∩ T) ⊆ {M.zero}",
				By(
					lModule,
					directSum,
					submodule.ZeroSubmodule.At(lScalars, ambient),
					ConstantChartLeast.At(
						fieldRing, l, a.TermAs[Set[A]]("«span»(k, U) ∩ T"), a.TermAs[Set[A]]("{M.zero}"))))
			directL := a.Have(
				"so the sum over l is direct",
				"«span»(l, U) ∩ «chart»(T) ⊆ {M.zero}",
				chartW.RwRev(),
				meet.RwRev(),
				By(zeroMeet))
			N := a.TermAs[Set[A]]("set_mul(M.add, «span»(l, U), «chart»(T))")
			NData := a.Conjuncts(
				a.Have(
					"the sum of the l-span and the chart of T is a submodule over l holding both",
					"submodule(«scalars»(l), «ambient», set_mul(M.add, «span»(l, U), «chart»(T))) ∧ "+
						"«span»(l, U) ⊆ set_mul(M.add, «span»(l, U), «chart»(T)) ∧ "+
						"«chart»(T) ⊆ set_mul(M.add, «span»(l, U), «chart»(T))",
					By(
						lModule,
						PSubmodule,
						chartTSubmodule,
						submodule.SubmoduleSum.At(lScalars, ambient, P, chartOfT),
						submodule.SumContainsLeft.At(lScalars, ambient, P, chartOfT),
						submodule.SumContainsRight.At(lScalars, ambient, P, chartOfT))),
				"the sum is a submodule",
				"it holds the l-span",
				"it holds the chart of T")
			NSubmodule, PInN, chartTInN := NData[0], NData[1], NData[2]
			WInN := a.Have(
				"it holds the k-span",
				"«span»(k, U) ⊆ set_mul(M.add, «span»(l, U), «chart»(T))",
				BySets(WInP, PInN))
			TInN := a.Have(
				"it holds T",
				"T ⊆ set_mul(M.add, «span»(l, U), «chart»(T))",
				BySets(TInChart, chartTInN))
			SumInN := a.Have(
				"the sum over k lies in it",
				"set_mul(M.add, «span»(k, U), T) ⊆ set_mul(M.add, «span»(l, U), «chart»(T))",
				By(
					NSubmodule,
					kInL,
					WInN,
					TInN,
					submodule.SubmoduleRestrictScalars.At(lScalars, ambient, N, kScalars),
					submodule.SumLeast.At(kScalars, ambient, W, T, N)))
			SInN := a.Have(
				"S lies in the sum over l",
				"S ⊆ set_mul(M.add, «span»(l, U), «chart»(T))",
				BySets(SInSum, SumInN))
			chartSInSum := a.Have(
				"so the chart of S lies in the sum over l",
				"«chart»(S) ⊆ set_mul(M.add, «span»(l, U), «chart»(T))",
				By(NSubmodule, SInN, ConstantChartLeast.At(fieldRing, l, S, N)))
			chartsNested := a.Have(
				"the chart of T lies in the chart of S",
				"«chart»(T) ⊆ «chart»(S)",
				Unfold(ConstantChartDef),
				By(TInS, submodule.SpanMono.At(lScalars, ambient, T, S)))
			UInChart := a.Have(
				"U lies in the chart of S",
				"U ⊆ «chart»(S)",
				BySets(UInS, SInChart))
			a.Show(
				"both dimensions are the size of U",
				By(
					lModule,
					fieldsOverK,
					chartSSubmodule,
					chartTSubmodule,
					chartsNested,
					finiteU,
					UInChart,
					lifted,
					chartSInSum,
					directL,
					sizeU,
					module_dimension.QuotientComplementDim.At(
						lScalars, ambient, inverse, a.TermAs[Set[A]]("«chart»(S)"), chartOfT, U)))
		}),
})}

// ConstantChartDimension — the chart of a finite-dimensional k-subspace is
// finite-dimensional over l, of the same dimension: a k-basis of S is an
// l-basis of its chart.
var ConstantChartDimension = constantChartDimensionThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartDimension",
	Key:  "prop_a2a30dcab448c02d",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "span", Text: "λX:set(A). λY:set(A). " +
				"    module_span(restrict_ring(field_ring(M), X), regular_module(field_ring(M)), Y)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"submodule(«scalars»(k), «vectors»(K), S)",
			"finite_dimensional(«scalars»(k), restrict_module(«ambient», S))",
		},
		Conclusion: "finite_dimensional(«scalars»(l), restrict_module(«ambient», «chart»(S))) ∧ " +
			"module_dim(«scalars»(l), restrict_module(«ambient», «chart»(S))) = " +
			"module_dim(«scalars»(k), restrict_module(«ambient», S))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subspace, finiteDimension Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			lScalars := a.TermAs[RingOps[A]]("«scalars»(l)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			inverse := a.TermAs[Fun[A, A]]("M.inv")
			SVectors := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«ambient», S)")
			chartVectors := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«ambient», «chart»(S))")
			chart := a.TermAs[Set[A]]("«chart»(S)")
			E, basisData := a.ObtainAs[Set[A]](
				"take a finite k-basis of l",
				"∃E:set(A). finite(E) ∧ module_basis(«scalars»(k), «vectors»(l), E)",
				By(
					finiteExtension,
					field_extension.FiniteExtensionDef.At(m, k, l),
					module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
			basisParts := a.Conjuncts(
				basisData,
				"E is finite",
				"E is a k-basis of l")
			finiteBasis, basis := basisParts[0], basisParts[1]
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					basisParts[0],
					basisParts[1],
					constant_composite.ConstantExtensionData.At(m, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			kSubfield, KSubfield := data[0], data[1]
			kModule := a.Conjuncts(
				GroupPremises(data[0], M, field_extension.SubfieldScalars.At(m, k)),
				"k is a subring",
				"the field is a module over k")[1]
			SSubmodule := a.Conjuncts(
				GroupPremises(M, data[0], data[1], data[2], subspace, ConstantSubspaceSubmodule.At(m, K, k, S)),
				"K is a k-submodule of the field",
				"S is a k-submodule of the field")[1]
			U, basisOfS := a.ObtainAs[Set[A]](
				"take a finite k-basis of S",
				"∃U:set(A). finite(U) ∧ module_basis(«scalars»(k), restrict_module(«ambient», S), U)",
				By(finiteDimension, module_dimension.FiniteDimensionalDef.At(kScalars, SVectors)))
			UParts := a.Conjuncts(
				basisOfS,
				"U is finite",
				"U is a k-basis of S")
			finiteU, UBasis := UParts[0], UParts[1]
			restricted := a.Conjuncts(
				a.Have(
					"U is independent over k and spans S",
					"module_independent(«scalars»(k), «ambient», U) ∧ «span»(k, U) = S",
					By(kModule, SSubmodule, UBasis, linear_independence.BasisRestrict.At(kScalars, ambient, S, U))),
				"U is independent over k",
				"U spans S over k")
			independentU, spansS := restricted[0], restricted[1]
			inS := a.Have(
				"U lies in S",
				"U ⊆ S",
				By(UBasis, linear_independence.BasisInCarrier.At(kScalars, SVectors, U)))
			SInK := a.Have(
				"S lies in K",
				"S ⊆ K",
				By(
					subspace,
					submodule.SubmoduleSubset.At(kScalars, a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)"), S)))
			memberships := a.Conjuncts(
				a.Have(
					"U lies in K, and U and S lie in the field",
					"U ⊆ K ∧ U ⊆ M.carrier ∧ S ⊆ M.carrier",
					BySets(inS, SInK, KSubfield, field.SubfieldSubset.At(m, K))),
				"U lies in K",
				"U lies in the field",
				"S lies in the field")
			UInK, UInField := memberships[0], memberships[1]
			chartData := a.Conjuncts(
				GroupPremises(M, lSubfield, memberships[2], ConstantChartSubmodule.At(m, l, S)),
				"the field is a module over l",
				"the chart is a submodule",
				"the chart holds S")
			lModule, chartSubmodule := chartData[0], chartData[1]
			lifted := a.Have(
				"U stays independent over l",
				"module_independent(«scalars»(l), «ambient», U)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					UInK,
					independentU,
					ConstantIndependentLifts.At(m, K, k, l, E, U)))
			spansChart := a.Have(
				"U spans the chart of S over l",
				"«span»(l, U) = «chart»(S)",
				spansS.RwRev(),
				Unfold(ConstantChartDef),
				By(lModule, kInL, UInField, submodule.SpanOfSubringSpan.At(lScalars, ambient, kScalars, U)))
			chartBasis := a.Have(
				"so U is an l-basis of the chart",
				"module_basis(«scalars»(l), restrict_module(«ambient», «chart»(S)), U)",
				By(
					lModule,
					chartSubmodule,
					lifted,
					spansChart,
					linear_independence.BasisRestrict.At(lScalars, ambient, chart, U)))
			lDimension := a.Have(
				"over l the dimension is the size of U",
				"finite_dimensional(«scalars»(l), restrict_module(«ambient», «chart»(S))) ∧ "+
					"module_dim(«scalars»(l), restrict_module(«ambient», «chart»(S))) = card(U)",
				By(
					lModule,
					chartSubmodule,
					lSubfield,
					chartBasis,
					finiteU,
					field.SubfieldRingSubfield.Read(M).At(l, l),
					submodule.SubmoduleModuleOn.At(lScalars, ambient, chart),
					module_dimension.FiniteBasisDim.At(lScalars, chartVectors, inverse, U)))
			kDimension := a.Have(
				"and so it is over k",
				"module_dim(«scalars»(k), restrict_module(«ambient», S)) = card(U)",
				By(
					kModule,
					SSubmodule,
					kSubfield,
					UBasis,
					finiteU,
					field.SubfieldRingSubfield.Read(M).At(k, k),
					submodule.SubmoduleModuleOn.At(kScalars, ambient, S),
					module_dimension.FiniteBasisDim.At(kScalars, SVectors, inverse, U)))
			a.Show(
				"the two dimensions agree",
				By(lDimension, kDimension))
		}),
})}

// ConstantChartMultiplier — a multiplier taking X into a submodule Z over l
// takes the chart of X into Z: its preimage of Z is a submodule over l.
var ConstantChartMultiplier = constantChartMultiplierThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartMultiplier",
	Key:  "prop_ffd9a8e5308073c4",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "lScalars", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
		},
		Binders: "∀M:field_on(A). ∀l X Z:set(A). ∀y u:A.",
		Hypotheses: []string{
			"subfield(M, l)",
			"submodule(«lScalars», «ambient», Z)",
			"y ∈ M.carrier",
			"X ⊆ M.carrier",
			"∀x:A. x ∈ X ⇒ y * x ∈ Z",
			"u ∈ constant_chart(field_ring(M), l, X)",
		},
		Conclusion: "y * u ∈ Z",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			l, X, Z *Expr[Set[A]],
			y, u *Expr[A],
			lSubfield, ZSubmodule, yInField, XInField, multiples, inChart Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			lScalars := a.TermAs[RingOps[A]]("«lScalars»")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			preimage := a.TermAs[Set[A]]("preimage_on(M.carrier, M.mul(y), Z)")
			preimageSubmodule := a.Have(
				"the preimage of Z under multiplication by y is a submodule",
				"submodule(«lScalars», «ambient», preimage_on(M.carrier, M.mul(y), Z))",
				By(
					M,
					lSubfield,
					yInField,
					ZSubmodule,
					field_extension.MultiplicationLinear.At(m, l, y),
					module_homomorphism.HomPreimageSubmodule.At(
						lScalars, ambient, ambient, a.TermAs[Fun[A, A]]("M.mul(y)"), Z)))
			XInPreimage := a.Have(
				"X lies in the preimage",
				"X ⊆ preimage_on(M.carrier, M.mul(y), Z)",
				BySets(XInField, multiples))
			inPreimage := a.Have(
				"the chart of X lies in the preimage",
				"constant_chart(field_ring(M), l, X) ⊆ preimage_on(M.carrier, M.mul(y), Z)",
				By(
					preimageSubmodule,
					XInPreimage,
					ConstantChartLeast.At(a.TermAs[RingOps[A]]("field_ring(M)"), l, X, preimage)))
			a.Show(
				"so y takes u into Z",
				BySets(inChart, inPreimage))
		}),
})}

// ConstantChartProduct — when the products of X and Y lie in a submodule Z
// over l, so do the products of their charts: the product is bilinear over l,
// so each factor may be spanned in turn.
var ConstantChartProduct = constantChartProductThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartProduct",
	Key:  "prop_2b81a71ec2ed921a",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "lScalars", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
		},
		Binders: "∀M:field_on(A). ∀l X Y Z:set(A). ∀u v:A.",
		Hypotheses: []string{
			"subfield(M, l)",
			"submodule(«lScalars», «ambient», Z)",
			"X ⊆ M.carrier",
			"Y ⊆ M.carrier",
			"∀x y:A. x ∈ X ∧ y ∈ Y ⇒ x * y ∈ Z",
			"u ∈ «chart»(X)",
			"v ∈ «chart»(Y)",
		},
		Conclusion: "u * v ∈ Z",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			l, X, Y, Z *Expr[Set[A]],
			u, v *Expr[A],
			lSubfield, ZSubmodule, XInField, YInField, products, uInChart, vInChart Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			lScalars := a.TermAs[RingOps[A]]("«lScalars»")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			chartX := a.TermAs[Set[A]]("«chart»(X)")
			chartXData := a.Conjuncts(
				GroupPremises(M, lSubfield, XInField, ConstantChartSubmodule.At(m, l, X)),
				"the field is a module over l",
				"the chart of X is a submodule",
				"the chart of X holds X")
			chartInField := a.Have(
				"the chart of X lies in the field",
				"«chart»(X) ⊆ M.carrier",
				By(chartXData[1], submodule.SubmoduleSubset.At(lScalars, ambient, chartX)))
			uInField := a.Have(
				"u lies in the field",
				"u ∈ M.carrier",
				BySets(uInChart, chartInField))
			fromRight := a.Have(
				"each y of Y multiplies the chart of X into Z",
				"∀y:A. y ∈ Y ⇒ y * u ∈ Z",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					inY := b.Assume()
					yMember := b.Have(
						"y lies in the field",
						"y ∈ M.carrier",
						BySets(inY, YInField))
					multiples := b.Have(
						"y multiplies X into Z",
						"∀x:A. x ∈ X ⇒ y * x ∈ Z",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							inX := c.Assume()
							xMember := c.Have(
								"x lies in the field",
								"x ∈ M.carrier",
								BySets(inX, XInField))
							swap := c.Have(
								"the product commutes",
								"y * x = x * y",
								ByArith(M, yMember, xMember))
							c.Show(
								"the products lie in Z",
								swap.Rw(),
								By(inX, inY, products.At(x, y)))
						}))
					b.Show(
						"multiplying by y is linear, and X spans the chart",
						By(
							M,
							lSubfield,
							ZSubmodule,
							yMember,
							XInField,
							multiples,
							uInChart,
							ConstantChartMultiplier.At(m, l, X, Z, y, u)))
				}))
			multiples := a.Have(
				"u multiplies Y into Z",
				"∀y:A. y ∈ Y ⇒ u * y ∈ Z",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					inY := b.Assume()
					yMember := b.Have(
						"y lies in the field",
						"y ∈ M.carrier",
						BySets(inY, YInField))
					swap := b.Have(
						"the product commutes",
						"u * y = y * u",
						ByArith(M, uInField, yMember))
					b.Show(
						"the product commutes, and y multiplies the chart of X into Z",
						swap.Rw(),
						By(inY, fromRight.At(y)))
				}))
			a.Show(
				"and u multiplies the chart of Y into Z",
				By(
					M,
					lSubfield,
					ZSubmodule,
					uInField,
					YInField,
					vInChart,
					multiples,
					ConstantChartMultiplier.At(m, l, Y, Z, u, v)))
		}),
})}

// ConstantChartOverChart — when S multiplies X into itself, the chart of S
// multiplies the chart of X into itself: the chart of X is a submodule over the
// chart of S.
var ConstantChartOverChart = constantChartOverChartThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartOverChart",
	Key:  "prop_db6b5331a4989aa1",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
		},
		Binders: "∀M:field_on(A). ∀l S X:set(A).",
		Hypotheses: []string{
			"subfield(M, l)",
			"S ⊆ M.carrier",
			"X ⊆ M.carrier",
			"∀s x:A. s ∈ S ∧ x ∈ X ⇒ s * x ∈ X",
		},
		Conclusion: "submodule(«scalars»(«chart»(S)), «ambient», «chart»(X))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			l, S, X *Expr[Set[A]],
			lSubfield, SInField, XInField, multiplied Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			chartScalars := a.TermAs[RingOps[A]]("«scalars»(«chart»(S))")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			chartX := a.TermAs[Set[A]]("«chart»(X)")
			overL := a.Conjuncts(
				GroupPremises(M, lSubfield, XInField, ConstantChartSubmodule.At(m, l, X)),
				"the field is a module over l",
				"the chart of X is a submodule over l",
				"it holds X")
			products := a.Have(
				"the chart of S multiplies the chart of X into itself",
				"∀u v:A. u ∈ «chart»(S) ∧ v ∈ «chart»(X) ⇒ u * v ∈ «chart»(X)",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					v := b.FixAs[A]("v")
					members := b.Assume()
					productsOfX := b.Have(
						"products of S and X lie in the chart of X",
						"∀s x:A. s ∈ S ∧ x ∈ X ⇒ s * x ∈ «chart»(X)",
						BySets(multiplied, overL[2]))
					b.Show(
						"the product is bilinear over l",
						By(
							M,
							lSubfield,
							overL[1],
							SInField,
							XInField,
							members,
							productsOfX,
							ConstantChartProduct.Read(M).At(l, S, X, chartX, u, v)))
				}))
			a.Show(
				"a subgroup closed under the scalars",
				By(
					submodule.SubmoduleSubgroup.Read(overL[1]),
					products,
					submodule.SubmoduleDef.At(chartScalars, ambient, chartX)))
		}),
})}

// ConstantIdealSubspace — an ideal of a ring between k and K is a k-subspace
// of K.
var ConstantIdealSubspace = constantIdealSubspaceThm{family.Add(registry.ProofEntry{
	Name: "ConstantIdealSubspace",
	Key:  "prop_c8a778a813b060e9",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
		},
		Binders: "∀M:field_on(A). ∀K k S I:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"S ⊆ K",
			"k ⊆ S",
			"ring_ideal(«scalars»(S), I)",
		},
		Conclusion: "submodule(«scalars»(k), «vectors»(K), I)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, S, I *Expr[Set[A]],
			kSubfield, KSubfield, kInK, SInK, kInS, ideal Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			SScalars := a.TermAs[RingOps[A]]("«scalars»(S)")
			KVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)")
			IInS := a.Have(
				"I lies in S",
				"I ⊆ S",
				By(ideal, ring_ideal.IdealSubset.At(SScalars, I)))
			IInK := a.Have(
				"I lies in K",
				"I ⊆ K",
				BySets(IInS, SInK))
			sums := a.Have(
				"I is closed under sums",
				"∀u v:A. u ∈ I ∧ v ∈ I ⇒ u + v ∈ I",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					v := b.FixAs[A]("v")
					members := b.Assume()
					b.Show(
						"I is an ideal",
						By(ideal, members, ring_ideal.IdealAdd.At(SScalars, I, u, v)))
				}))
			multiples := a.Have(
				"I is closed under scalars from k",
				"∀c u:A. c ∈ k ∧ u ∈ I ⇒ c * u ∈ I",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[A]("u")
					members := b.Assume()
					cInS := b.Have(
						"c lies in S",
						"c ∈ S",
						BySets(members, kInS))
					b.Show(
						"k lies in S",
						By(ideal, members, cInS, ring_ideal.IdealMul.At(SScalars, I, c, u)))
				}))
			a.Show(
				"I holds zero and is closed under sums and under scalars from k",
				By(
					M,
					kSubfield,
					KSubfield,
					kInK,
					IInK,
					ideal,
					ring_ideal.IdealZero.At(SScalars, I),
					sums,
					multiples,
					field_extension.ExtensionModuleOn.At(m, k, K),
					submodule.SubmoduleCriterion.At(kScalars, KVectors, I)))
		}),
})}

// ConstantChartSubring — the chart over l of a subring S of the field is a
// subring holding l and S: S multiplies itself into itself, so its chart is
// closed under products, and l acts on the one of S.
var ConstantChartSubring = constantChartSubringThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartSubring",
	Key:  "prop_210b73379141f578",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "constant_chart(field_ring(M), l, S)"},
		},
		Binders: "∀M:field_on(A). ∀l S:set(A).",
		Hypotheses: []string{
			"subfield(M, l)",
			"subring(field_ring(M), S)",
		},
		Conclusion: "subring(field_ring(M), «chart») ∧ l ⊆ «chart» ∧ S ⊆ «chart»",
	},
		func(a *Argument, M field.FieldFact[on.M], l, S *Expr[Set[A]], lSubfield, subringS Fact) {
			m := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			lScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), l)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
			chartScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «chart»)")
			chart := a.TermAs[Set[A]]("«chart»")
			one := a.TermAs[A]("M.one")
			SInField := a.Have(
				"S lies in the field",
				"S ⊆ M.carrier",
				By(subringS, comm_ring.SubringSubset.At(fieldRing, S)))
			chartData := a.Conjuncts(
				GroupPremises(M, lSubfield, SInField, ConstantChartSubmodule.At(m, l, S)),
				"the field is a module over l",
				"the chart is a submodule",
				"the chart holds S")
			chartSubmodule, SInChart := chartData[1], chartData[2]
			overItself := a.Have(
				"S multiplies itself into itself, so its chart is a submodule over itself",
				"submodule(restrict_ring(field_ring(M), «chart»), regular_module(field_ring(M)), «chart»)",
				By(
					lSubfield,
					SInField,
					subringS,
					comm_ring.SubringMul.Read(subringS),
					ConstantChartOverChart.Read(M).At(l, S, S)))
			products := a.Have(
				"the chart of S is closed under products",
				"∀u v:A. u ∈ «chart» ∧ v ∈ «chart» ⇒ u * v ∈ «chart»",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					v := b.FixAs[A]("v")
					members := b.Assume()
					b.Show(
						"a submodule over the chart of S",
						By(members, overItself, submodule.SubmoduleSmul.At(chartScalars, ambient, chart, u, v)))
				}))
			oneInChart := a.Have(
				"one lies in the chart of S",
				"M.one ∈ «chart»",
				BySets(subringS, SInChart, comm_ring.SubringOne.At(fieldRing, S)))
			lInChart := a.Have(
				"l lies in the chart of S",
				"l ⊆ «chart»",
				Derive(func(b *Argument) {
					b.Do(Unfold(set_basic.SubsetDef))
					x := b.FixAs[A]("x")
					inL := b.Assume()
					member := b.Have(
						"x lies in the field",
						"x ∈ M.carrier",
						BySets(inL, lSubfield, field.SubfieldSubset.At(m, l)))
					unit := b.Have(
						"x times one is x",
						"x * M.one = x",
						ByArith(M, member))
					b.Show(
						"the chart is closed under scalars from l",
						By(
							Normalized,
							unit,
							inL,
							oneInChart,
							chartSubmodule,
							submodule.SubmoduleSmul.At(lScalars, ambient, chart, x, one)))
				}))
			inFieldWithZero := a.Have(
				"it lies in the field and holds zero",
				"«chart» ⊆ M.carrier ∧ M.zero ∈ «chart»",
				By(
					chartSubmodule,
					submodule.SubmoduleSubset.At(lScalars, ambient, chart),
					submodule.SubmoduleZero.At(lScalars, ambient, chart)))
			sums := a.Have(
				"it is closed under sums",
				"∀x y:A. x ∈ «chart» ∧ y ∈ «chart» ⇒ x + y ∈ «chart»",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					members := b.Assume()
					b.Show(
						"a submodule over l",
						By(members, chartSubmodule, submodule.SubmoduleAdd.At(lScalars, ambient, chart, x, y)))
				}))
			negatives := a.Have(
				"and under negation",
				"∀x:A. x ∈ «chart» ⇒ -x ∈ «chart»",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					b.Show(
						"a submodule over l",
						By(member, chartSubmodule, submodule.SubmoduleNeg.At(lScalars, ambient, chart, x)))
				}))
			subringChart := a.Have(
				"so the chart of S is a subring",
				"subring(field_ring(M), «chart»)",
				By(
					oneInChart,
					products,
					inFieldWithZero,
					sums,
					negatives,
					comm_ring.SubringDef.At(fieldRing, chart)))
			a.Show(
				"a subring holding l and S",
				By(subringChart, lInChart, SInChart))
		}),
})}

// ConstantChartRing — the chart of a ring S between k and K is a subring of
// the field holding l and S (ConstantChartSubring), and the chart of an ideal of
// S is an ideal of it contracting back to the ideal: S multiplies the ideal into
// itself, so the chart of S multiplies the chart of the ideal into itself, and
// the contraction is the one of the coordinates.
var ConstantChartRing = constantChartRingThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartRing",
	Key:  "prop_5b10fd756670da39",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
		},
		Conclusion: "subring(field_ring(M), «chart»(S)) ∧ " +
			"l ⊆ «chart»(S) ∧ " +
			"S ⊆ «chart»(S) ∧ " +
			"(∀I:set(A). " +
			"    ring_ideal(«scalars»(S), I) ⇒ " +
			"    ring_ideal(«scalars»(«chart»(S)), «chart»(I)) ∧ «chart»(I) ∩ S = I)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subringS, SInK, kInS Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			lScalars := a.TermAs[RingOps[A]]("«scalars»(l)")
			SScalars := a.TermAs[RingOps[A]]("«scalars»(S)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			chartScalars := a.TermAs[RingOps[A]]("«scalars»(«chart»(S))")
			regularData := a.Conjuncts(
				a.Unfolded(regular, function_field.RegularFunctionFieldDef),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"k is perfect",
				"K is finitely generated over k",
				"K has a parameter over k",
				"k is algebraically closed in K")
			kSubfield, KSubfield, kInK := regularData[0], regularData[1], regularData[2]
			KInField := a.Have(
				"K lies in the field",
				"K ⊆ M.carrier",
				By(KSubfield, field.SubfieldSubset.At(m, K)))
			SInField := a.Have(
				"S lies in the field",
				"S ⊆ M.carrier",
				BySets(SInK, KInField))
			ideals := a.Have(
				"the chart of an ideal of S is an ideal contracting to it",
				Statement{
					Binders: "∀I:set(A).",
					Hypotheses: []string{
						"ring_ideal(«scalars»(S), I)",
					},
					Conclusion: "ring_ideal(«scalars»(«chart»(S)), «chart»(I)) ∧ «chart»(I) ∩ S = I",
				},
				Derive(func(b *Argument) {
					I := b.FixAs[Set[A]]("I")
					ideal := b.Assume()
					chartI := b.TermAs[Set[A]]("«chart»(I)")
					IInS := b.Have(
						"I lies in S",
						"I ⊆ S",
						By(ideal, ring_ideal.IdealSubset.At(SScalars, I)))
					IInField := b.Have(
						"I lies in the field",
						"I ⊆ M.carrier",
						BySets(IInS, SInField))
					subspaceI := b.Have(
						"I is a k-subspace of K",
						"submodule(«scalars»(k), «vectors»(K), I)",
						By(M, kSubfield, KSubfield, kInK, SInK, kInS, ideal, ConstantIdealSubspace.At(m, K, k, S, I)))
					contract := b.Conjuncts(
						b.Have(
							"the chart of I lies in the composite and meets K in I",
							"«chart»(I) ⊆ constant_composite(M, K, l) ∧ «chart»(I) ∩ K = I",
							By(
								M,
								regular,
								lSubfield,
								kInL,
								finiteExtension,
								subspaceI,
								ConstantChartContract.At(m, K, k, l, I))),
						"it lies in the composite",
						"it meets K in I")
					chartISubmodule := b.Have(
						"the chart of I is a submodule over l",
						"submodule(«scalars»(l), «ambient», «chart»(I))",
						By(M, lSubfield, IInField, ConstantChartSubmodule.At(m, l, I)))
					multiplied := b.Have(
						"S multiplies I into itself",
						"∀s y:A. s ∈ S ∧ y ∈ I ⇒ s * y ∈ I",
						Derive(func(c *Argument) {
							s := c.FixAs[A]("s")
							y := c.FixAs[A]("y")
							sy := c.Assume()
							c.Show(
								"I is an ideal of S",
								By(sy, ideal, ring_ideal.IdealMul.At(SScalars, I, s, y)))
						}))
					overChart := b.Have(
						"so its chart is a submodule over the chart of S",
						"submodule(«scalars»(«chart»(S)), «ambient», «chart»(I))",
						By(lSubfield, SInField, IInField, multiplied, ConstantChartOverChart.Read(M).At(l, S, I)))
					multiples := b.Have(
						"the chart of S multiplies the chart of I into itself",
						"∀r x:A. r ∈ «chart»(S) ∧ x ∈ «chart»(I) ⇒ r * x ∈ «chart»(I)",
						Derive(func(c *Argument) {
							r := c.FixAs[A]("r")
							x := c.FixAs[A]("x")
							members := c.Assume()
							c.Show(
								"a submodule over the chart of S",
								By(members, overChart, submodule.SubmoduleSmul.At(chartScalars, ambient, chartI, r, x)))
						}))
					chartIInChartS := b.Have(
						"the chart of I lies in the chart of S",
						"«chart»(I) ⊆ «chart»(S)",
						Unfold(ConstantChartDef),
						By(IInS, submodule.SpanMono.At(lScalars, ambient, I, S)))
					zeroInChartI := b.Have(
						"it holds zero",
						"M.zero ∈ «chart»(I)",
						By(chartISubmodule, submodule.SubmoduleZero.At(lScalars, ambient, chartI)))
					sums := b.Have(
						"it is closed under sums",
						"∀x y:A. x ∈ «chart»(I) ∧ y ∈ «chart»(I) ⇒ x + y ∈ «chart»(I)",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							y := c.FixAs[A]("y")
							members := c.Assume()
							c.Show(
								"a submodule over l",
								By(members, chartISubmodule, submodule.SubmoduleAdd.At(lScalars, ambient, chartI, x, y)))
						}))
					idealChart := b.Have(
						"the chart of I is an ideal of the chart of S",
						"ring_ideal(«scalars»(«chart»(S)), «chart»(I))",
						By(
							multiples,
							chartIInChartS,
							zeroInChartI,
							sums,
							ring_ideal.RingIdealDef.At(b.TermAs[RingOps[A]]("«scalars»(«chart»(S))"), chartI)))
					meetsS := b.Have(
						"S lies in K, so meeting S is meeting K",
						"«chart»(I) ∩ S = I",
						BySets(contract[1], SInK, IInS))
					b.Show(
						"an ideal of the chart of S, meeting S in I",
						By(idealChart, meetsS))
				}))
			a.Show(
				"the chart of S is a subring holding l and S, and the ideals",
				By(lSubfield, subringS, ConstantChartSubring.Read(M).At(l, S), ideals))
		}),
})}

// ConstantChartPolynomialImage — the span over l of S[w] is the span over l of
// S with w adjoined. The second is a subring holding l, so a submodule over l,
// and it holds S[w]; the first is a subring holding the chart of S and w.
var ConstantChartPolynomialImage = constantChartPolynomialImageThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartPolynomialImage",
	Key:  "prop_ccab509d66cf0761",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "constant_chart(field_ring(M), l, S)"},
			{Name: "adjoined", Text: "polynomial_image(field_ring(M), S, w)"},
		},
		Binders: "∀M:field_on(A). ∀l S:set(A). ∀w:A.",
		Hypotheses: []string{
			"subfield(M, l)",
			"subring(field_ring(M), S)",
			"w ∈ M.carrier",
		},
		Conclusion: "constant_chart(field_ring(M), l, «adjoined») = " +
			"polynomial_image(field_ring(M), «chart», w)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			l, S *Expr[Set[A]],
			w *Expr[A],
			lSubfield, subringS, wInField Fact,
		) {
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			chart := a.TermAs[Set[A]]("«chart»")
			adjoined := a.TermAs[Set[A]]("«adjoined»")
			wm := a.MemberOf[on.M](w, wInField)
			chartOfAdjoined := a.TermAs[Set[A]]("constant_chart(field_ring(M), l, «adjoined»)")
			chartAdjoined := a.TermAs[Set[A]]("polynomial_image(field_ring(M), «chart», w)")
			chartData := a.Have(
				"the chart of S is a subring holding l and S",
				"subring(field_ring(M), «chart») ∧ l ⊆ «chart» ∧ S ⊆ «chart»",
				By(lSubfield, subringS, ConstantChartSubring.Read(M).At(l, S)))
			adjoinedData := a.Have(
				"S[w] is a subring holding S and w",
				"subring(field_ring(M), «adjoined») ∧ S ⊆ «adjoined» ∧ w ∈ «adjoined»",
				By(subringS, algebraic_element.PolynomialImageSubring.Read(M).At(S, wm)))
			chartAdjoinedData := a.Have(
				"the chart of S with w adjoined is a subring holding the chart of S and w",
				"subring(field_ring(M), polynomial_image(field_ring(M), «chart», w)) ∧ "+
					"«chart» ⊆ polynomial_image(field_ring(M), «chart», w) ∧ "+
					"w ∈ polynomial_image(field_ring(M), «chart», w)",
				By(chartData, algebraic_element.PolynomialImageSubring.Read(M).At(chart, wm)))
			chartOfAdjoinedData := a.Have(
				"the chart of S[w] is a subring holding l and S[w]",
				"subring(field_ring(M), constant_chart(field_ring(M), l, «adjoined»)) ∧ "+
					"l ⊆ constant_chart(field_ring(M), l, «adjoined») ∧ "+
					"«adjoined» ⊆ constant_chart(field_ring(M), l, «adjoined»)",
				By(lSubfield, adjoinedData, ConstantChartSubring.Read(M).At(l, adjoined)))
			inChartAdjoined := a.Have(
				"l and S lie in the chart of S with w adjoined",
				"l ⊆ polynomial_image(field_ring(M), «chart», w) ∧ S ⊆ polynomial_image(field_ring(M), «chart», w)",
				BySets(chartData, chartAdjoinedData))
			adjoinedInChartAdjoined := a.Have(
				"a ring holding S and w, it holds S[w]",
				"«adjoined» ⊆ polynomial_image(field_ring(M), «chart», w)",
				By(
					chartAdjoinedData,
					inChartAdjoined,
					comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(chartAdjoined),
					algebraic_element.PolynomialImageLeast.Read(M).At(S, chartAdjoined, w)))
			lower := a.Have(
				"a ring holding l, it is a submodule over l holding S[w], so it holds the chart of S[w]",
				"constant_chart(field_ring(M), l, «adjoined») ⊆ polynomial_image(field_ring(M), «chart», w)",
				By(
					chartAdjoinedData,
					inChartAdjoined,
					adjoinedInChartAdjoined,
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(l, chartAdjoined),
					ConstantChartLeast.At(fieldRing, l, adjoined, chartAdjoined)))
			SInChartOfAdjoined := a.Have(
				"S lies in the chart of S[w]",
				"S ⊆ constant_chart(field_ring(M), l, «adjoined»)",
				BySets(adjoinedData, chartOfAdjoinedData))
			chartInChartOfAdjoined := a.Have(
				"the chart of S[w] is a submodule over l holding S, so it holds the chart of S",
				"«chart» ⊆ constant_chart(field_ring(M), l, «adjoined»)",
				By(
					chartOfAdjoinedData,
					SInChartOfAdjoined,
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(l, chartOfAdjoined),
					ConstantChartLeast.At(fieldRing, l, S, chartOfAdjoined)))
			wInChartOfAdjoined := a.Have(
				"w lies in the chart of S[w]",
				"w ∈ constant_chart(field_ring(M), l, «adjoined»)",
				BySets(adjoinedData, chartOfAdjoinedData))
			upper := a.Have(
				"a ring holding the chart of S and w, it holds the chart of S with w adjoined",
				"polynomial_image(field_ring(M), «chart», w) ⊆ constant_chart(field_ring(M), l, «adjoined»)",
				By(
					chartOfAdjoinedData,
					chartInChartOfAdjoined,
					wInChartOfAdjoined,
					comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(chartOfAdjoined),
					algebraic_element.PolynomialImageLeast.Read(M).At(chart, chartOfAdjoined, w)))
			a.Show(
				"mutual inclusion",
				By(lower, upper, set_order.SubsetAntisym.At(chartOfAdjoined, chartAdjoined)))
		}),
})}

// ConstantChartSpan — the span of B over the chart of S is the chart of its
// span X over S, and that chart is a submodule over the chart of S. The chart
// of S multiplies the chart of X into itself; conversely the span of B over
// the chart of S is a submodule over S, so it holds X, and over l, so it holds
// the chart of X.
var ConstantChartSpan = constantChartSpanThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartSpan",
	Key:  "prop_5d1b573faae8e156",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "spanned", Text: "module_span(«scalars»(«chart»(S)), «ambient», B)"},
		},
		Binders: "∀M:field_on(A). ∀l S X B:set(A).",
		Hypotheses: []string{
			"subfield(M, l)",
			"subring(field_ring(M), S)",
			"subring(field_ring(M), «chart»(S))",
			"l ⊆ «chart»(S)",
			"S ⊆ «chart»(S)",
			"submodule(«scalars»(S), «ambient», X)",
			"B ⊆ X",
			"module_span(«scalars»(S), «ambient», B) = X",
		},
		Conclusion: "submodule(«scalars»(«chart»(S)), «ambient», «chart»(X)) ∧ «spanned» = «chart»(X)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			l, S, X, B *Expr[Set[A]],
			lSubfield, subringS, subringChart, lInChart, SInChart, XSubmodule, BInX, spansX Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			lScalars := a.TermAs[RingOps[A]]("«scalars»(l)")
			SScalars := a.TermAs[RingOps[A]]("«scalars»(S)")
			chartScalars := a.TermAs[RingOps[A]]("«scalars»(«chart»(S))")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			chartS, chartX := a.TermAs[Set[A]]("«chart»(S)"), a.TermAs[Set[A]]("«chart»(X)")
			spanned := a.TermAs[Set[A]]("«spanned»")
			inField := a.Have(
				"S, X and B lie in the field",
				"S ⊆ M.carrier ∧ X ⊆ M.carrier ∧ B ⊆ M.carrier",
				BySets(
					BInX,
					subringS,
					XSubmodule,
					comm_ring.SubringSubset.Read(subringS),
					submodule.SubmoduleSubset.Read(XSubmodule)))
			overL := a.Conjuncts(
				GroupPremises(M, lSubfield, inField, ConstantChartSubmodule.At(ops, l, X)),
				"the field is a module over l",
				"the chart of X is a submodule over l",
				"it holds X")
			multiplied := a.Have(
				"S multiplies X into itself",
				"∀s x:A. s ∈ S ∧ x ∈ X ⇒ s * x ∈ X",
				Derive(func(b *Argument) {
					s := b.FixAs[A]("s")
					x := b.FixAs[A]("x")
					members := b.Assume()
					b.Show(
						"X is a submodule over S",
						By(members, XSubmodule, submodule.SubmoduleSmul.At(SScalars, ambient, X, s, x)))
				}))
			chartSubmodule := a.Have(
				"so the chart of X is a submodule over the chart of S",
				"submodule(«scalars»(«chart»(S)), «ambient», «chart»(X))",
				By(lSubfield, inField, multiplied, ConstantChartOverChart.Read(M).At(l, S, X)))
			moduleChart := a.Have(
				"the field is a module over the chart of S",
				"module_on(«scalars»(«chart»(S)), «ambient»)",
				By(subringChart, fractional_ideal.FieldModuleOn.Read(M).At(chartS)))
			spannedSubmodule := a.Have(
				"the span of B over the chart of S is a submodule",
				"submodule(«scalars»(«chart»(S)), «ambient», «spanned»)",
				By(inField, submodule.SpanSubmodule.Read(moduleChart).At(B)))
			spannedOverS := a.Have(
				"so it is a submodule over S",
				"submodule(«scalars»(S), «ambient», «spanned»)",
				By(SInChart, submodule.SubmoduleRestrictScalars.Read(spannedSubmodule).At(SScalars)))
			spannedOverL := a.Have(
				"and over l",
				"submodule(«scalars»(l), «ambient», «spanned»)",
				By(lInChart, submodule.SubmoduleRestrictScalars.Read(spannedSubmodule).At(lScalars)))
			BInSpanned := a.Have(
				"it holds B",
				"B ⊆ «spanned»",
				By(submodule.SubsetSpan.At(chartScalars, ambient, B)))
			XInSpanned := a.Have(
				"so it holds X, the span of B over S",
				"X ⊆ «spanned»",
				spansX.RwRev(),
				By(spannedOverS, BInSpanned, submodule.SpanLeast.At(SScalars, ambient, B, spanned)))
			chartInSpanned := a.Have(
				"and the chart of X, the span of X over l",
				"«chart»(X) ⊆ «spanned»",
				By(spannedOverL, XInSpanned, ConstantChartLeast.At(fieldRing, l, X, spanned)))
			BInChart := a.Have(
				"the chart of X holds B",
				"B ⊆ «chart»(X)",
				BySets(BInX, overL[2]))
			spannedInChart := a.Have(
				"so it holds the span of B over the chart of S",
				"«spanned» ⊆ «chart»(X)",
				By(chartSubmodule, BInChart, submodule.SpanLeast.At(chartScalars, ambient, B, chartX)))
			a.Show(
				"the two inclusions give the span",
				By(chartSubmodule, spannedInChart, chartInSpanned, set_order.SubsetAntisym.At(spanned, chartX)))
		}),
})}

// ConstantChartBasis — a basis of a module X over a ring S between k and K
// stays a basis of the chart of X over the chart of S: it stays independent
// and spans the chart.
var ConstantChartBasis = constantChartBasisThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartBasis",
	Key:  "prop_586215f4141aad3e",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S X B:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"submodule(«scalars»(S), «ambient», X)",
			"X ⊆ K",
			"module_basis(«scalars»(S), «vectors»(X), B)",
		},
		Conclusion: "module_basis(«scalars»(«chart»(S)), «vectors»(«chart»(X)), B)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, X, B *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subringS, SInK, kInS, XSubmodule, XInK, basis Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			chartS, chartX := a.TermAs[Set[A]]("«chart»(S)"), a.TermAs[Set[A]]("«chart»(X)")
			E, basisData := a.ObtainAs[Set[A]](
				"take a finite k-basis of l",
				"∃E:set(A). finite(E) ∧ module_basis(«scalars»(k), «vectors»(l), E)",
				By(
					finiteExtension,
					field_extension.FiniteExtensionDef.At(ops, k, l),
					module_dimension.FiniteDimensionalDef.At(kScalars, lVectors)))
			basisParts := a.Conjuncts(
				basisData,
				"E is finite",
				"E is a k-basis of l")
			chartRing := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					SInK,
					kInS,
					ConstantChartRing.At(ops, K, k, l, S)),
				"the chart of S is a subring",
				"it holds l",
				"it holds S",
				"it carries ideals to ideals")
			moduleS := a.Have(
				"the field is a module over S",
				"module_on(«scalars»(S), «ambient»)",
				By(subringS, fractional_ideal.FieldModuleOn.Read(M).At(S)))
			moduleChart := a.Have(
				"and over the chart of S",
				"module_on(«scalars»(«chart»(S)), «ambient»)",
				By(chartRing[0], fractional_ideal.FieldModuleOn.Read(M).At(chartS)))
			overS := a.Conjuncts(
				a.Have(
					"B is independent over S and spans X",
					"module_independent(«scalars»(S), «ambient», B) ∧ module_span(«scalars»(S), «ambient», B) = X",
					By(XSubmodule, basis, linear_independence.BasisRestrict.Read(moduleS).At(X, B))),
				"B is independent over S",
				"B spans X")
			BInX := a.Have(
				"B lies in X",
				"B ⊆ X",
				By(basis, linear_independence.BasisInCarrier.Read(basis)))
			BInK := a.Have(
				"so it lies in K",
				"B ⊆ K",
				BySets(BInX, XInK))
			subspace := a.Have(
				"S is a k-subspace of K",
				"submodule(«scalars»(k), «vectors»(K), S)",
				By(M, subringS, kInS, SInK, ConstantRingSubspace.At(ops, K, k, S)))
			spanned := a.Conjuncts(
				GroupPremises(
					chartRing[1],
					M,
					lSubfield,
					subringS,
					chartRing[0],
					chartRing[2],
					XSubmodule,
					BInX,
					overS[1],
					ConstantChartSpan.At(ops, l, S, X, B)),
				"the chart of X is a submodule over the chart of S",
				"B spans it")
			independent := a.Have(
				"B stays independent over the chart of S",
				"module_independent(«scalars»(«chart»(S)), «ambient», B)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					basisParts[0],
					basisParts[1],
					subspace,
					BInK,
					overS[0],
					ConstantChartIndependent.At(ops, K, k, l, E, S, B)))
			a.Show(
				"independent and spanning, B is a basis of the chart of X",
				By(
					spanned[0],
					independent,
					spanned[1],
					linear_independence.BasisRestrict.Read(moduleChart).At(chartX, B)))
		}),
})}

// ConstantChartSum — charts commute with sums: the sum of the charts of two
// k-subspaces of the field is a submodule over l holding the sum of the
// subspaces, and the chart of that sum holds each chart.
var ConstantChartSum = constantChartSumThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartSum",
	Key:  "prop_1c154ed89bc50e6b",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "sumOfCharts", Text: "set_mul(M.add, «chart»(S), «chart»(T))"},
		},
		Binders: "∀M:field_on(A). ∀k l S T:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, l)",
			"submodule(«scalars»(k), «ambient», S)",
			"submodule(«scalars»(k), «ambient», T)",
		},
		Conclusion: "«chart»(set_mul(M.add, S, T)) = set_mul(M.add, «chart»(S), «chart»(T))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l, S, T *Expr[Set[A]],
			kSubfield, lSubfield, SSubmodule, TSubmodule Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			lScalars := a.TermAs[RingOps[A]]("«scalars»(l)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			sum := a.TermAs[Set[A]]("set_mul(M.add, S, T)")
			chartS, chartT := a.TermAs[Set[A]]("«chart»(S)"), a.TermAs[Set[A]]("«chart»(T)")
			chartOfSum := a.TermAs[Set[A]]("«chart»(set_mul(M.add, S, T))")
			sumOfCharts := a.TermAs[Set[A]]("«sumOfCharts»")
			kModule := a.Conjuncts(
				GroupPremises(M, kSubfield, field_extension.SubfieldScalars.At(ops, k)),
				"k is a subring",
				"the field is a module over k")[1]
			inField := a.Have(
				"S and T lie in the field",
				"S ⊆ M.carrier ∧ T ⊆ M.carrier",
				BySets(submodule.SubmoduleSubset.Read(SSubmodule), submodule.SubmoduleSubset.Read(TSubmodule)))
			chartOfS := a.Conjuncts(
				GroupPremises(M, lSubfield, inField, ConstantChartSubmodule.At(ops, l, S)),
				"the field is a module over l",
				"the chart of S is a submodule",
				"it holds S")
			chartOfT := a.Conjuncts(
				a.Have(
					"and likewise at T",
					"submodule(«scalars»(l), «ambient», «chart»(T)) ∧ T ⊆ «chart»(T)",
					By(M, lSubfield, inField, ConstantChartSubmodule.At(ops, l, T))),
				"the chart of T is a submodule",
				"it holds T")
			lModule := chartOfS[0]
			sumOfChartsSubmodule := a.Have(
				"the sum of the charts is a submodule over l",
				"submodule(«scalars»(l), «ambient», «sumOfCharts»)",
				By(chartOfS[1], chartOfT[0], submodule.SubmoduleSum.Read(lModule).At(chartS, chartT)))
			summandsInSum := a.Have(
				"it holds each chart, so it holds S and T",
				"S ⊆ «sumOfCharts» ∧ T ⊆ «sumOfCharts»",
				BySets(
					chartOfS[1],
					chartOfS[2],
					chartOfT[0],
					chartOfT[1],
					submodule.SumContainsLeft.Read(lModule).At(chartS, chartT),
					submodule.SumContainsRight.Read(lModule).At(chartS, chartT)))
			upper := a.Have(
				"so it holds S + T and the chart of S + T",
				"«chart»(set_mul(M.add, S, T)) ⊆ «sumOfCharts»",
				By(
					sumOfChartsSubmodule,
					summandsInSum,
					submodule.SumLeast.At(lScalars, ambient, S, T, sumOfCharts),
					ConstantChartLeast.At(fieldRing, l, sum, sumOfCharts)))
			summands := a.Have(
				"S + T holds S and T and lies in the field",
				"S ⊆ set_mul(M.add, S, T) ∧ T ⊆ set_mul(M.add, S, T) ∧ set_mul(M.add, S, T) ⊆ M.carrier",
				By(
					kModule,
					SSubmodule,
					TSubmodule,
					submodule.SumContainsLeft.Read(kModule).At(S, T),
					submodule.SumContainsRight.Read(kModule).At(S, T),
					submodule.SubmoduleSum.Read(kModule).At(S, T),
					submodule.SubmoduleSubset.At(a.TermAs[RingOps[A]]("«scalars»(k)"), ambient, sum)))
			chartOfSumData := a.Conjuncts(
				a.Have(
					"its chart is a submodule holding it",
					"submodule(«scalars»(l), «ambient», «chart»(set_mul(M.add, S, T))) ∧ "+
						"set_mul(M.add, S, T) ⊆ «chart»(set_mul(M.add, S, T))",
					By(M, lSubfield, summands, ConstantChartSubmodule.At(ops, l, sum))),
				"the chart of S + T is a submodule",
				"it holds S + T")
			chartOfSumSubmodule := chartOfSumData[0]
			summandsInChart := a.Have(
				"so the chart of S + T holds S and T",
				"S ⊆ «chart»(set_mul(M.add, S, T)) ∧ T ⊆ «chart»(set_mul(M.add, S, T))",
				BySets(summands, chartOfSumData[1]))
			lower := a.Have(
				"so it holds each chart, and their sum",
				"«sumOfCharts» ⊆ «chart»(set_mul(M.add, S, T))",
				By(
					chartOfSumSubmodule,
					summandsInChart,
					ConstantChartLeast.At(fieldRing, l, S, chartOfSum),
					ConstantChartLeast.At(fieldRing, l, T, chartOfSum),
					submodule.SumLeast.At(lScalars, ambient, chartS, chartT, chartOfSum)))
			a.Show(
				"the two inclusions give the equation",
				By(upper, lower, set_order.SubsetAntisym.At(chartOfSum, sumOfCharts)))
		}),
})}

// ConstantChartOfSpan — the chart of a span over a ring S between k and K is the
// span of the chart over the chart of S, each read inside its own field. The span
// of B over the chart of S is the chart of the span of B over S, and the chart of
// B lies between B and that chart.
var ConstantChartOfSpan = constantChartOfSpanThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartOfSpan",
	Key:  "prop_e94f0b361c3f915",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "spanned", Text: "module_span(«scalars»(S), «ambient», B)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S B:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"B ⊆ K",
		},
		Conclusion: "module_span(«scalars»(«chart»(S)), " +
			"    «vectors»(constant_composite(M, K, l)), " +
			"    «chart»(B)) = " +
			"«chart»(module_span(«scalars»(S), «vectors»(K), B))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, B *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subringS, SInK, kInS, BInK Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			SScalars := a.TermAs[RingOps[A]]("«scalars»(S)")
			chartScalars := a.TermAs[RingOps[A]]("«scalars»(«chart»(S))")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			composite := a.TermAs[Set[A]]("constant_composite(M, K, l)")
			chartS, chartB := a.TermAs[Set[A]]("«chart»(S)"), a.TermAs[Set[A]]("«chart»(B)")
			spanned := a.TermAs[Set[A]]("«spanned»")
			chartSpanned := a.TermAs[Set[A]]("«chart»(«spanned»)")
			KSubfield := a.Have(
				"K is a subfield of M",
				"subfield(M, K)",
				By(a.Unfolded(regular, function_field.RegularFunctionFieldDef)))
			compositeData := a.Conjuncts(
				GroupPremises(M, KSubfield, lSubfield, constant_composite.ConstantCompositeSubfield.At(ops, K, l)),
				"the composite is a subfield",
				"it holds K",
				"it holds l")
			compositeRing := a.Conjuncts(
				GroupPremises(compositeData[0], M, field_extension.SubfieldScalars.At(ops, composite)),
				"the composite is a subring",
				"the field is a module over the composite")[0]
			chartRing := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					SInK,
					kInS,
					ConstantChartRing.At(ops, K, k, l, S)),
				"the chart of S is a subring",
				"it holds l",
				"it holds S",
				"it carries ideals to ideals")
			moduleS := a.Have(
				"the field is a module over S",
				"module_on(«scalars»(S), «ambient»)",
				By(subringS, fractional_ideal.FieldModuleOn.Read(M).At(S)))
			moduleChart := a.Have(
				"and over the chart of S",
				"module_on(«scalars»(«chart»(S)), «ambient»)",
				By(chartRing[0], fractional_ideal.FieldModuleOn.Read(M).At(chartS)))
			KOverS := a.Have(
				"K is a submodule over S",
				"submodule(«scalars»(S), «ambient», K)",
				By(
					M,
					KSubfield,
					SInK,
					field_extension.SubfieldScalars.At(ops, K),
					principal_ideal_domain.ConstantSubringSubmodule.At(ops, S, K)))
			BInField := a.Have(
				"B lies in the field",
				"B ⊆ M.carrier",
				BySets(BInK, KSubfield, field.SubfieldSubset.At(ops, K)))
			spannedData := a.Have(
				"the span of B over S is a submodule holding B",
				"submodule(«scalars»(S), «ambient», «spanned») ∧ B ⊆ «spanned»",
				By(
					BInField,
					submodule.SpanSubmodule.Read(moduleS).At(B),
					submodule.SubsetSpan.At(SScalars, ambient, B)))
			spanInK := a.Have(
				"the span of B over S is the same in K",
				"module_span(«scalars»(S), «vectors»(K), B) = «spanned»",
				By(KOverS, BInK, linear_independence.SpanRestrict.Read(moduleS).At(K, B)))
			chartOfSpan := a.Conjuncts(
				a.Have(
					"its chart is a submodule over the chart of S, which B spans",
					"submodule(«scalars»(«chart»(S)), «ambient», «chart»(«spanned»)) ∧ "+
						"module_span(«scalars»(«chart»(S)), «ambient», B) = «chart»(«spanned»)",
					By(
						M,
						lSubfield,
						subringS,
						chartRing[0],
						chartRing[1],
						chartRing[2],
						spannedData,
						ConstantChartSpan.At(ops, l, S, spanned, B))),
				"the chart of the span is a submodule over the chart of S",
				"which B spans")
			spannedSubset := a.Conjuncts(
				a.Have(
					"the chart of the span is a submodule over l holding the span",
					"submodule(«scalars»(l), «ambient», «chart»(«spanned»)) ∧ «spanned» ⊆ «chart»(«spanned»)",
					By(
						M,
						lSubfield,
						spannedData,
						submodule.SubmoduleSubset.At(SScalars, ambient, spanned),
						ConstantChartSubmodule.At(ops, l, spanned))),
				"the chart of the span is a submodule over l",
				"it holds the span")
			BInChartOfSpan := a.Have(
				"so it holds B",
				"B ⊆ «chart»(«spanned»)",
				BySets(spannedData, spannedSubset[1]))
			chartBInChartOfSpan := a.Have(
				"and the chart of B",
				"«chart»(B) ⊆ «chart»(«spanned»)",
				By(spannedSubset[0], BInChartOfSpan, ConstantChartLeast.At(fieldRing, l, B, chartSpanned)))
			BInChartB := a.Have(
				"the chart of B holds B",
				"B ⊆ «chart»(B)",
				By(M, lSubfield, BInField, ConstantChartSubmodule.At(ops, l, B)))
			spanOfChart := a.Have(
				"so the chart of B spans the chart of the span over the chart of S",
				"module_span(«scalars»(«chart»(S)), «ambient», «chart»(B)) = «chart»(«spanned»)",
				By(
					chartOfSpan[0],
					chartOfSpan[1],
					chartBInChartOfSpan,
					BInChartB,
					submodule.SpanLeast.At(chartScalars, ambient, chartB, chartSpanned),
					submodule.SpanMono.At(chartScalars, ambient, B, chartB),
					set_order.SubsetAntisym.At(
						a.TermAs[Set[A]]("module_span(«scalars»(«chart»(S)), «ambient», «chart»(B))"), chartSpanned)))
			inComposite := a.Have(
				"the composite holds B and S",
				"B ⊆ constant_composite(M, K, l) ∧ S ⊆ constant_composite(M, K, l)",
				BySets(BInK, SInK, compositeData[1]))
			chartsInComposite := a.Have(
				"and, a submodule over l, their charts",
				"«chart»(B) ⊆ constant_composite(M, K, l) ∧ «chart»(S) ⊆ constant_composite(M, K, l)",
				By(
					M,
					compositeRing,
					compositeData[2],
					inComposite,
					principal_ideal_domain.ConstantSubringSubmodule.At(ops, l, composite),
					ConstantChartLeast.At(fieldRing, l, B, composite),
					ConstantChartLeast.At(fieldRing, l, S, composite)))
			compositeOverChart := a.Have(
				"so the composite is a submodule over the chart of S",
				"submodule(«scalars»(«chart»(S)), «ambient», constant_composite(M, K, l))",
				By(
					M,
					compositeRing,
					chartsInComposite,
					principal_ideal_domain.ConstantSubringSubmodule.At(ops, chartS, composite)))
			a.Show(
				"each span is the same in its own field as in M",
				spanInK.Rw(),
				By(
					compositeOverChart,
					chartsInComposite,
					spanOfChart,
					linear_independence.SpanRestrict.Read(moduleChart).At(composite, chartB)))
		}),
})}

// ConstantChartFinite — the chart of a ring S between k and K is generated over
// S by a k-basis E of l: a member of the chart is a combination of E with
// coefficients in S.
var ConstantChartFinite = constantChartFiniteThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartFinite",
	Key:  "prop_c38bff1883614c1d",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "spanned", Text: "module_span(«scalars»(S), «ambient», E)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E S:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
		},
		Conclusion: "module_finitely_generated(«scalars»(S), «vectors»(«chart»(S)))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E, S *Expr[Set[A]],
			regular, lSubfield, kInL, finiteE, basis, subS, SInK, kInS Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			scalars := a.TermAs[RingOps[A]]("«scalars»(S)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			chart := a.TermAs[Set[A]]("«chart»(S)")
			spanned := a.TermAs[Set[A]]("«spanned»")
			extension := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					finiteE,
					basis,
					constant_composite.ConstantExtensionData.At(m, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"the composite is a subfield",
				"it holds K",
				"it holds l",
				"E lies in l",
				"the composite is a module over K",
				"with basis E")
			kSubfield, EInL := extension[0], extension[6]
			basisDegree := a.Conjuncts(
				GroupPremises(
					kSubfield, M, lSubfield, kInL, finiteE, basis, field_extension.BasisDegree.At(m, k, l, E)),
				"l is finite over k",
				"of degree the size of E")
			ringData := a.Conjuncts(
				GroupPremises(
					M, regular, lSubfield, kInL, subS, SInK, kInS, basisDegree[0], ConstantChartRing.At(m, K, k, l, S)),
				"the chart is a subring",
				"it holds l",
				"it holds S",
				"the charts of ideals are ideals")
			subChart, lInChart, SInChart := ringData[0], ringData[1], ringData[2]
			moduleAmbient := a.Have(
				"the field is a module over S",
				"module_on(«scalars»(S), «ambient»)",
				By(subS, fractional_ideal.FieldModuleOn.Read(M).At(S)))
			inChart := a.Have(
				"E lies in the chart, and in M",
				"E ⊆ «chart»(S) ∧ E ⊆ M.carrier",
				BySets(EInL, lInChart, lSubfield, field.SubfieldSubset.At(m, l)))
			inChartParts := a.Conjuncts(
				inChart,
				"E lies in the chart",
				"E lies in M")
			spanSubmodule := a.Have(
				"the span of E over S is a submodule of the field",
				"submodule(«scalars»(S), «ambient», «spanned»)",
				By(moduleAmbient, inChartParts[1], submodule.SpanSubmodule.At(scalars, ambient, E)))
			chartSubmodule := a.Have(
				"the chart is a submodule over S",
				"submodule(«scalars»(S), «ambient», «chart»(S))",
				By(M, subChart, SInChart, principal_ideal_domain.ConstantSubringSubmodule.At(m, S, chart)))
			upper := a.Have(
				"the span lies in the chart",
				"«spanned» ⊆ «chart»(S)",
				By(chartSubmodule, inChartParts[0], submodule.SpanLeast.At(scalars, ambient, E, chart)))
			subspace := a.Have(
				"S is a k-subspace of K",
				"submodule(«scalars»(k), «vectors»(K), S)",
				By(M, subS, kInS, SInK, ConstantRingSubspace.At(m, K, k, S)))
			expansions := a.Have(
				"a member of the chart is a combination of E over S",
				"∀x:A. x ∈ «chart»(S) ⇒ x ∈ «spanned»",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					_, expansion := b.ObtainAs[Fun[A, A]](
						"x is a combination of E with coefficients in S",
						"∃c:(A → A). (∀e:A. e ∈ E ⇒ c(e) ∈ S) ∧ x = module_sum(M.add, M.zero, E, λe:A. c(e) * e)",
						By(
							M,
							regular,
							lSubfield,
							kInL,
							finiteE,
							basis,
							subspace,
							member,
							ConstantChartMembers.At(m, K, k, l, E, S, x)))
					parts := b.Conjuncts(
						expansion,
						"the coefficients lie in S",
						"x is the sum")
					terms := b.Have(
						"each term lies in the span",
						"∀e:A. e ∈ E ⇒ c(e) * e ∈ «spanned»",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							inE := c.Assume()
							inSpan := c.Have(
								"e lies in the span",
								"e ∈ «spanned»",
								BySets(inE, submodule.SubsetSpan.At(scalars, ambient, E)))
							c.Show(
								"the span is closed under scalars of S",
								By(
									spanSubmodule,
									parts[0].At(e),
									inE,
									inSpan,
									submodule.SubmoduleSmul.At(scalars, ambient, spanned, c.TermAs[A]("c(e)"), e)))
						}))
					b.Show(
						"and closed under finite sums",
						parts[1].Rw(),
						By(
							moduleAmbient,
							spanSubmodule,
							finiteE,
							terms,
							submodule.SubmoduleModuleSum.At(
								scalars, ambient, spanned, E, b.TermAs[Fun[A, A]]("λe:A. c(e) * e"))))
				}))
			lower := a.Have(
				"the chart lies in the span",
				"«chart»(S) ⊆ «spanned»",
				By(expansions, set_basic.SubsetDef.At(chart, spanned)))
			same := a.Have(
				"so the span is the chart",
				"«spanned» = «chart»(S)",
				By(upper, lower, set_order.SubsetAntisym.At(spanned, chart)))
			a.Show(
				"E generates the chart over S",
				Unfold(principal_ideal_domain.FinitelyGeneratedDef),
				Witness(E),
				By(
					finiteE,
					inChartParts[0],
					same,
					moduleAmbient,
					chartSubmodule,
					linear_independence.SpanRestrict.At(scalars, ambient, chart, E)))
		}),
})}
