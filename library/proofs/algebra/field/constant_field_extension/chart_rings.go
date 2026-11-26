// chart_rings.go — the charts of the rings a function field is built from.
// The chart of the constants is l, the chart of k[t] is l[t], the chart of S
// with t inverted is the chart of S with t inverted, and when K is the
// fraction field of S the composite is the fraction field of the chart of S.
// An element transcendental over k stays transcendental over l.

package constant_field_extension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantChartOfConstants — the chart of the constants is l: l is a submodule
// over itself holding k, and the chart of a ring between k and K holds l.
var ConstantChartOfConstants = constantChartOfConstantsThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartOfConstants",
	Key:  "prop_3a152ee4029bdaa4",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k l:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
		},
		Conclusion: "constant_chart(field_ring(M), l, k) = l",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			constants := a.Have(
				"k is a subring of the field lying in K",
				"subring(field_ring(M), k) ∧ k ⊆ K",
				By(
					a.Unfolded(regular, function_field.RegularFunctionFieldDef),
					field_extension.SubfieldScalars.Read(M).At(k)))
			inside := a.Have(
				"l is a submodule over itself holding k, so it holds the chart of k",
				"constant_chart(field_ring(M), l, k) ⊆ l",
				By(
					M,
					kInL,
					lSubfield,
					field_extension.SubfieldScalars.Read(M).At(l),
					set_order.SubsetRefl.At(l),
					principal_ideal_domain.ConstantSubringSubmodule.At(ops, l, l),
					ConstantChartLeast.At(fieldRing, l, k, l)))
			a.Show(
				"and the chart of a ring between k and K holds l",
				By(
					inside,
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					constants,
					set_order.SubsetRefl.At(k),
					ConstantChartRing.At(ops, K, k, l, k),
					set_order.SubsetAntisym.At(a.TermAs[Set[A]]("constant_chart(field_ring(M), l, k)"), l)))
		}),
})}

// ConstantPolynomialChart — the polynomials in t over l are the chart of the
// polynomials in t over k: the chart is a ring holding l and t, so it holds
// l[t], and l[t] is a submodule over l holding k[t], so it holds the chart.
var ConstantPolynomialChart = constantPolynomialChartThm{family.Add(registry.ProofEntry{
	Name: "ConstantPolynomialChart",
	Key:  "prop_cd6f6b0767af7113",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "over", Text: "λX:set(A). polynomial_image(field_ring(M), X, t)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), l, «over»(k))"},
		},
		Binders: "∀M:field_on(A). ∀K k l:set(A). ∀t:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"t ∈ K",
		},
		Conclusion: "«over»(l) = «chart»",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l *Expr[Set[A]],
			t *Expr[A],
			regular, lSubfield, kInL, finiteExtension, tInK Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			ringM := field.RingOn.Read(M)
			overK, overL := a.TermAs[Set[A]]("«over»(k)"), a.TermAs[Set[A]]("«over»(l)")
			chart := a.TermAs[Set[A]]("«chart»")
			regularData := a.Conjuncts(
				a.Unfolded(regular, function_field.RegularFunctionFieldDef),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"k is perfect",
				"K is finitely generated over k",
				"K has a parameter over k",
				"k is algebraically closed in K")
			KSubfield, kInK := regularData[1], regularData[2]
			tm := a.MemberOf[on.M](t, a.Have(
				"t lies in the field",
				"t ∈ M.carrier",
				BySets(tInK, KSubfield, field.SubfieldSubset.At(ops, K))))
			ringK := a.Conjuncts(
				GroupPremises(regularData[0], algebraic_element.PolynomialImageRing.Read(M).At(k, tm)),
				"k[t] is a subring",
				"it holds k",
				"it holds t",
				"it lies in k(t)")
			ringL := a.Conjuncts(
				GroupPremises(lSubfield, algebraic_element.PolynomialImageRing.Read(M).At(l, tm)),
				"l[t] is a subring",
				"it holds l",
				"it holds t",
				"it lies in l(t)")
			imageInK := a.Have(
				"K is a ring holding k and t, so it holds k[t]",
				"«over»(k) ⊆ K",
				By(
					kInK,
					tInK,
					KSubfield,
					field_extension.SubfieldScalars.Read(M).At(K),
					comm_ring.SubringRingOn.Read(ringM).At(K),
					algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(k, K, t)))
			chartData := a.Conjuncts(
				GroupPremises(
					ringK[0],
					ringK[1],
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					imageInK,
					ConstantChartRing.At(ops, K, k, l, overK)),
				"the chart of k[t] is a subring",
				"it holds l",
				"it holds k[t]",
				"it carries ideals to ideals")
			tInChart := a.Have(
				"t lies in the chart, as k[t] does",
				"t ∈ «chart»",
				BySets(chartData[2], ringK[2]))
			overLInChart := a.Have(
				"the chart is a ring holding l and t, so it holds l[t]",
				"«over»(l) ⊆ «chart»",
				By(
					chartData[0],
					chartData[1],
					tInChart,
					comm_ring.SubringRingOn.Read(ringM).At(chart),
					algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(l, chart, t)))
			kInOverL := a.Have(
				"k lies in l, inside l[t]",
				"k ⊆ «over»(l)",
				BySets(kInL, ringL[1]))
			overKInOverL := a.Have(
				"l[t] is a ring holding k and t, so it holds k[t]",
				"«over»(k) ⊆ «over»(l)",
				By(
					ringL[0],
					kInOverL,
					ringL[2],
					comm_ring.SubringRingOn.Read(ringM).At(overL),
					algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(k, overL, t)))
			chartInOverL := a.Have(
				"l[t] is a submodule over l holding k[t], so it holds the chart",
				"«chart» ⊆ «over»(l)",
				By(
					M,
					ringL[0],
					ringL[1],
					principal_ideal_domain.ConstantSubringSubmodule.At(ops, l, overL),
					overKInOverL,
					ConstantChartLeast.At(fieldRing, l, overK, overL)))
			a.Show(
				"so the two sets are one",
				By(overLInChart, chartInOverL, set_order.SubsetAntisym.At(overL, chart)))
		}),
})}

// ConstantChartAway — the chart of a ring T that is S with t inverted is the
// chart of S with t inverted. Inverting t in the chart of S gives a subring
// holding l and T, so a submodule over l holding the chart of T.
var ConstantChartAway = constantChartAwayThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartAway",
	Key:  "prop_2f1235dc5ddc1ce5",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "away", Text: "ring_away(field_ring(M), «chart»(S), t)"},
		},
		Binders: "∀M:field_on(A). ∀l S T:set(A). ∀t:A.",
		Hypotheses: []string{
			"subring(field_ring(M), «chart»(S))",
			"l ⊆ «chart»(S)",
			"S ⊆ «chart»(S)",
			"t ∈ «chart»(S)",
			"T ⊆ M.carrier",
			"∀x:A. x ∈ T ⇒ ∃n:num. monoid_pow(M.mul, M.one, t, n) * x ∈ S",
		},
		Conclusion: "«chart»(T) = ring_away(restrict_ring(field_ring(M), «chart»(T)), «chart»(S), t)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			l, S, T *Expr[Set[A]],
			t *Expr[A],
			subringChart, lInChart, SInChart, tInChart, TInField, clears Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			chartS, away := a.TermAs[Set[A]]("«chart»(S)"), a.TermAs[Set[A]]("«away»")
			awayRing := a.Conjuncts(
				a.Have(
					"inverting t in the chart of S gives a subring holding it",
					"«chart»(S) ⊆ «away» ∧ subring(field_ring(M), «away»)",
					By(
						tInChart,
						subringChart,
						field.RingOn.Read(M),
						ring_away.RingAwaySubring.At(fieldRing, chartS, t))),
				"it holds the chart of S",
				"it is a subring")
			TInAway := a.Have(
				"T lies in it, a power of t carrying each member into S",
				"T ⊆ «away»",
				BySets(clears, SInChart, TInField, ring_away.RingAwayDef.At(fieldRing, chartS, t)))
			lInAway := a.Have(
				"so it holds l",
				"l ⊆ «away»",
				BySets(lInChart, awayRing[0]))
			inside := a.Have(
				"so the chart of T lies in it, a submodule over l",
				"«chart»(T) ⊆ «away»",
				By(
					M,
					awayRing[1],
					lInAway,
					principal_ideal_domain.ConstantSubringSubmodule.At(ops, l, away),
					TInAway,
					ConstantChartLeast.At(fieldRing, l, T, away)))
			a.Show(
				"read inside the chart of T, under the same operations, that is the claim",
				BySets(
					inside,
					ring_away.RingAwayDef.At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «chart»(T))"), chartS, t),
					ring_away.RingAwayDef.At(fieldRing, chartS, t)))
		}),
})}

// ConstantChartFractions — when K is the fraction field of S, the composite is
// the fraction field of the chart of S: the finitely many E-coordinates of a
// member of the composite share one denominator d in S, which carries the
// member into the chart.
var ConstantChartFractions = constantChartFractionsThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartFractions",
	Key:  "prop_a2672f99fcc3de56",
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
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"fraction_field_carrier(field_ring(restrict_field(M, K)), S)",
		},
		Conclusion: "fraction_field_carrier(field_ring(restrict_field(M, constant_composite(M, K, l))), " +
			"    «chart»(S))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subringS, SInK, kInS, fractions Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			composite := a.TermAs[Set[A]]("constant_composite(M, K, l)")
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
			finiteBasis, basis := basisParts[0], basisParts[1]
			data := a.Conjuncts(
				GroupPremises(
					M,
					regular,
					lSubfield,
					kInL,
					basisParts[0],
					basisParts[1],
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
			KSubfield, compositeSubfield := data[1], data[3]
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
			subspace := a.Have(
				"S is a k-subspace of K",
				"submodule(«scalars»(k), «vectors»(K), S)",
				By(M, subringS, kInS, SInK, ConstantRingSubspace.At(ops, K, k, S)))
			functionField := a.Have(
				"K is a field under the operations of M",
				"field_on(restrict_field(M, K))",
				By(KSubfield, field.SubfieldFieldOn.Read(M).At(K)))
			subringInK := a.Have(
				"read in K, S is a subring",
				"subring(field_ring(restrict_field(M, K)), S)",
				By(
					Normalized,
					subringS,
					SInK,
					field.RestrictFieldRecords.At(ops, K, S),
					comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(S),
					comm_ring.SubringRingOn.Read(field.RingOn.Read(functionField)).At(S)))
			compositeFractions := a.Have(
				"each member of the composite is a fraction of the chart",
				Statement{
					Binders: "∀z:A.",
					Hypotheses: []string{
						"z ∈ constant_composite(M, K, l)",
					},
					Conclusion: "∃p q:A. p ∈ «chart»(S) ∧ q ∈ «chart»(S) ∧ q ≠ M.zero ∧ z * q = p",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					zInC := b.Assume()
					c := b.TermAs[Fun[A, A]]("«coordinate»(E, z)")
					coordinates := b.Have(
						"the coordinates of z lie in K",
						"∀e:A. e ∈ E ⇒ «coordinate»(E, z, e) ∈ K",
						Derive(func(g *Argument) {
							e := g.FixAs[A]("e")
							inE := g.Assume()
							g.Show(
								"a coordinate of a member of the composite",
								By(
									M,
									regular,
									lSubfield,
									kInL,
									finiteBasis,
									basis,
									zInC,
									inE,
									KSubfield,
									field.SubfieldOne.At(ops, K),
									constant_composite.ConstantCoordinateProduct.At(ops, K, k, l, E, z, g.TermAs[A]("M.one"), e)))
						}))
					coefficientImage := b.Have(
						"they form a finite subset of K",
						"finite(image(«coordinate»(E, z), E)) ∧ image(«coordinate»(E, z), E) ⊆ K",
						By(finiteBasis, coordinates, finite_set.FiniteImage.At(c, E), set_image.ImageSubsetIff.At(c, E, K)))
					d, denominator := b.ObtainAs[A](
						"so they share one denominator in S",
						"∃d:A. d ∈ S ∧ d ≠ M.zero ∧ image(M.mul(d), image(«coordinate»(E, z), E)) ⊆ S",
						By(
							subringInK,
							fractions,
							coefficientImage,
							integral_element.FiniteCommonDenominator.Read(functionField).At(
								S, b.TermAs[Set[A]]("image(«coordinate»(E, z), E)"))),
						Named("d"))
					cleared := b.Have(
						"d carries every coordinate into S",
						"∀e:A. e ∈ E ⇒ d * «coordinate»(E, z, e) ∈ S",
						BySets(denominator))
					members := b.Have(
						"z and d lie in the composite, d in S and in the chart",
						"d ∈ K ∧ d ∈ constant_composite(M, K, l) ∧ d ∈ «chart»(S) ∧ d ∈ M.carrier ∧ z ∈ M.carrier",
						BySets(
							denominator,
							zInC,
							SInK,
							data[4],
							chartRing[2],
							compositeSubfield,
							field.SubfieldSubset.At(ops, composite)))
					product := b.Have(
						"so z · d lies in the composite",
						"z * d ∈ constant_composite(M, K, l)",
						By(zInC, members, compositeSubfield, field.SubfieldMul.At(ops, composite, z, d)))
					productCoordinates := b.Have(
						"and its coordinates are d times those of z, in S",
						"∀e:A. e ∈ E ⇒ «coordinate»(E, z * d, e) ∈ S",
						Derive(func(g *Argument) {
							e := g.FixAs[A]("e")
							inE := g.Assume()
							parts := g.Conjuncts(
								GroupPremises(
									M,
									regular,
									lSubfield,
									kInL,
									basisParts[0],
									basisParts[1],
									zInC,
									members,
									inE,
									constant_composite.ConstantCoordinateProduct.At(ops, K, k, l, E, z, d, e)),
								"the coordinate of z lies in K",
								"d comes out of the coordinate")
							inField := g.Have(
								"which lies in the field",
								"«coordinate»(E, z, e) ∈ M.carrier",
								BySets(parts[0], KSubfield, field.SubfieldSubset.At(ops, K)))
							turned := g.Have(
								"the product commutes",
								"«coordinate»(E, z, e) * d = d * «coordinate»(E, z, e)",
								ByArith(M, inField, members))
							g.Show(
								"so the coordinate is d times the coordinate of z",
								parts[1].Rw(),
								turned.Rw(),
								By(cleared.At(e), inE))
						}))
					chartMember := b.Have(
						"so z · d lies in the chart",
						"z * d ∈ «chart»(S)",
						By(
							M,
							regular,
							lSubfield,
							kInL,
							finiteBasis,
							basis,
							subspace,
							product,
							productCoordinates,
							ConstantChartCoordinates.At(ops, K, k, l, E, S, b.TermAs[A]("z * d"))))
					b.Take(b.TermAs[A]("z * d"))
					b.Take(d)
					b.Show(
						"z is the fraction (z · d) / d",
						By(chartMember, members, denominator))
				}))
			chartInComposite := a.Have(
				"the chart lies in the composite",
				"«chart»(S) ⊆ constant_composite(M, K, l)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subspace,
					ConstantChartContract.At(ops, K, k, l, S)))
			a.Show(
				"the chart lies in the composite and its fractions fill it",
				Simp(Fwd(field.FractionFieldCarrierDef)),
				By(chartInComposite, compositeFractions))
		}),
})}

// ConstantChartOfAway — extending the constants of S with f inverted is
// inverting f in the chart of S. ConstantChartAway gives one inclusion; for the
// other, a power of inv(f) carries S into S[1/f], so it carries the chart of S
// into the chart of S[1/f], and it undoes the power of f clearing the member.
var ConstantChartOfAway = constantChartOfAwayThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartOfAway",
	Key:  "prop_b28ec95b866bbfc0",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
			{Name: "away", Text: "ring_away(field_ring(M), S, f)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S:set(A). ∀f:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"f ∈ S",
			"f ≠ M.zero",
		},
		Conclusion: "«chart»(«away») = ring_away(field_ring(M), «chart»(S), f)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, l, S *Expr[Set[A]],
		f *Expr[A],
		regular, lSubfield, kInL, finiteExtension, subringS, SInK, kInS, fInS, nonzero Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
		ring := field.RingOn.Read(M)
		powers := comm_ring.MulMonoidOn.Read(ring)
		away := a.TermAs[Set[A]]("«away»")
		chartT := a.TermAs[Set[A]]("«chart»(«away»)")
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
		subringChart, lInChart, SInChart := chartRing[0], chartRing[1], chartRing[2]
		SInField := a.Have(
			"S lies in M",
			"S ⊆ M.carrier",
			By(comm_ring.SubringSubset.Read(subringS)))
		fm := a.MemberOf[on.M](f, a.Have(
			"f lies in M",
			"f ∈ M.carrier",
			BySets(fInS, SInField)))
		inverse := field.InvIn.Read(M).At(fm)
		awayData := a.Have(
			"S[1/f] lies in M, a power of f clearing each of its members",
			"«away» ⊆ M.carrier ∧ (∀x:A. x ∈ «away» ⇒ ∃n:num. monoid_pow(M.mul, M.one, f, n) * x ∈ S)",
			BySets(ring_away.RingAwayDef.At(fieldRing, S, f)))
		fInChart := a.Have(
			"f lies in the chart of S",
			"f ∈ «chart»(S)",
			BySets(fInS, SInChart))
		chartAway := a.Have(
			"The chart of S[1/f] is its members a power of f brings into the chart of S",
			"«chart»(«away») = ring_away(restrict_ring(field_ring(M), «chart»(«away»)), «chart»(S), f)",
			By(
				subringChart,
				lInChart,
				SInChart,
				fInChart,
				awayData,
				ConstantChartAway.Read(M).At(l, S, away, f)))
		chartData := a.Conjuncts(
			GroupPremises(lSubfield, awayData, ConstantChartSubmodule.Read(M).At(l, away)),
			"M is a module over l",
			"the chart of S[1/f] is a submodule over l",
			"it holds S[1/f]")
		chartInField := a.Have(
			"The chart of S[1/f] lies in M",
			"«chart»(«away») ⊆ M.carrier",
			By(submodule.SubmoduleSubset.Read(chartData[1])))
		a.Do(Simp(Fwd(set_basic.Extension)))
		x := a.FixAs[A]("x")
		a.Iff()
		a.Forward(
			"a member of the chart of S[1/f] is cleared by a power of f",
			func(c *Argument, inChart Fact) {
				cleared := c.Have(
					"Some power of f brings it into the chart of S",
					"x ∈ ring_away(restrict_ring(field_ring(M), «chart»(«away»)), «chart»(S), f)",
					By(inChart, chartAway))
				opened := c.Simplified(cleared, Fwd(ring_away.RingAwayMember))
				c.Show(
					"and it lies in M",
					Simp(Fwd(ring_away.RingAwayMember)),
					BySets(opened, chartInField))
			})
		a.Backward(
			"a power of inv(f) undoes the clearing",
			func(c *Argument, inAway Fact) {
				parts := c.Conjuncts(
					c.Simplified(inAway, Fwd(ring_away.RingAwayMember)),
					"x lies in M",
					"a power of f brings x into the chart of S")
				n, clearing := c.UnpackAs[Nat](parts[1], "n")
				xm := c.MemberOf[on.M](x, parts[0])
				h, hIs := c.LetAs[A]("h", "monoid_pow(M.mul, M.one, f, n)")
				e, eIs := c.LetAs[A]("e", "monoid_pow(M.mul, M.one, M.inv(f), n)")
				hm := c.MemberOf[on.M](h, c.Have(
					"The power of f lies in M",
					"h ∈ M.carrier",
					By(Normalized, hIs, comm_monoid.PowIn.Read(powers).At(fm, n))))
				em := c.MemberOf[on.M](e, c.Have(
					"so does the power of inv(f)",
					"e ∈ M.carrier",
					By(Normalized, eIs, comm_monoid.PowIn.Read(powers).At(inverse, n))))
				cancels := c.Have(
					"The two powers cancel",
					"h * e = M.one",
					By(
						Normalized,
						hIs,
						eIs,
						nonzero,
						field.MulRightInverseOn.Read(M).At(fm),
						comm_monoid.PowInverseOn.Read(powers).At(fm, inverse, n)))
				carries := c.Have(
					"The power of inv(f) carries S into S[1/f], the power of f clearing it",
					"∀s:A. s ∈ S ⇒ e * s ∈ «chart»(«away»)",
					Derive(func(d *Argument) {
						y := d.FixAs[A]("y")
						yInS := d.Assume()
						ym := d.MemberOf[on.M](y, d.Have(
							"y lies in M",
							"y ∈ M.carrier",
							BySets(yInS, SInField)))
						product := comm_ring.MulIn.Read(ring).At(em, ym)
						undone := d.Have(
							"h undoes e on y",
							"h * (e * y) = y",
							ByArith(ring, Scaled(y, cancels), hm, em, ym))
						cleared := d.Have(
							"so a power of f brings e · y into S",
							"∃m:num. monoid_pow(M.mul, M.one, f, m) * (e * y) ∈ S",
							Witness(n),
							By(Normalized, hIs, undone, yInS))
						inAway := d.Have(
							"e · y lies in S[1/f]",
							"e * y ∈ «away»",
							By(product, cleared, ring_away.RingAwayMember.At(fieldRing, S, f, d.TermAs[A]("e * y"))))
						d.Show(
							"which lies in its chart",
							BySets(inAway, chartData[2]))
					}))
				moved := c.Have(
					"The power of inv(f) carries the chart of S into the chart of S[1/f]",
					"e * (h * x) ∈ «chart»(«away»)",
					By(
						carries,
						clearing,
						lSubfield,
						chartData[1],
						SInField,
						em,
						ConstantChartMultiplier.Read(M).At(l, S, chartT, em, c.TermAs[A]("h * x"))))
				undone := c.Have(
					"and e undoes h on x",
					"e * (h * x) = x",
					ByArith(ring, Scaled(x, cancels), hm, em, xm))
				c.Show(
					"so x lies in the chart of S[1/f]",
					By(moved, undone))
			})
	}),
})}
