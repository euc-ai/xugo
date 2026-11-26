// constant_split.go — the maximal ideals of a chart over a maximal ideal of
// its ring. For a ring S between k and K, K regular over k, the l-points of the
// chart S' in M restrict bijectively to the k-points of S, a point of S' taking
// S into a subfield holding l takes S' into it, and the kernel of an l-point
// over a maximal ideal m of S of degree d is maximal, of degree e with
// e·gcd(d, r) = d; so the maximal ideals of S' over m number gcd(d, r), each of
// degree d / gcd(d, r). An ideal of S' over an ideal of finite colength has
// finite colength over l.

package constant_splitting

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/residue_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantPointsInField — restriction to S is a bijection from the l-points of
// the chart of S in M to the k-points of S in M: the bijection at the target M,
// which is M restricted to its own carrier.
var ConstantPointsInField = constantPointsInFieldThm{family.Add(registry.ProofEntry{
	Name: "ConstantPointsInField",
	Key:  "prop_367ab798f9fdf3e",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "points", Text: "algebra_points( " +
				"    restrict_ring(field_ring(M), constant_chart(field_ring(M), l, S)), " +
				"    field_ring(M), " +
				"    l, " +
				"    λx:A. x)"},
			{Name: "restriction", Text: "λψ:A → A. λx:A. COND(x ∈ S, ψ(x), M.zero)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"S ⊆ K",
		},
		Conclusion: "injective_on(«points», «restriction») ∧ " +
			"image(«restriction», «points») = " +
			"algebra_points(restrict_ring(field_ring(M), S), field_ring(M), k, λx:A. x)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subringS, kInS, SInK Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			ring := a.TermAs[RingOps[A]]("field_ring(M)")
			carrier := a.TermAs[Set[A]]("M.carrier")
			lInCarrier := a.Have(
				"l lies in the carrier of M",
				"l ⊆ M.carrier",
				By(lSubfield, field.SubfieldSubset.At(ops, l)))
			a.Show(
				"the target M is M restricted to its own carrier, a subfield holding l",
				By(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					kInS,
					SInK,
					lInCarrier,
					field.CarrierSubfield.Read(M),
					module_record.RestrictRingCarrier.At(ring),
					ConstantChartPoints.Read(M).At(K, k, l, S, carrier)))
		}),
})}

// ConstantPointValues — an l-point ψ of the chart of S taking S into a subfield
// T holding l takes the whole chart into T. Its restriction to S is a k-point
// of S with values in T, which extends to an l-point of the chart in T; read in
// M the extension has the restriction of ψ, so it is ψ.
var ConstantPointValues = constantPointValuesThm{family.Add(registry.ProofEntry{
	Name: "ConstantPointValues",
	Key:  "prop_449faf9c91c0bf09",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), l, S)"},
			{Name: "points", Text: "algebra_points(«scalars»(«chart»), field_ring(M), l, λx:A. x)"},
			{Name: "pointsInT", Text: "algebra_points(«scalars»(«chart»), «scalars»(T), l, λx:A. x)"},
			{Name: "below", Text: "algebra_points(«scalars»(S), field_ring(M), k, λx:A. x)"},
			{Name: "belowInT", Text: "algebra_points(«scalars»(S), «scalars»(T), k, λx:A. x)"},
			{Name: "restriction", Text: "λψ:A → A. λx:A. COND(x ∈ S, ψ(x), M.zero)"},
			{Name: "restricted", Text: "λx:A. COND(x ∈ S, ψ(x), M.zero)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S T:set(A). ∀ψ:(A → A).",
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
			"ψ ∈ «points»",
			"image(ψ, S) ⊆ T",
		},
		Conclusion: "image(ψ, «chart») ⊆ T",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, T *Expr[Set[A]],
			ψ *Arrow[A, A],
			regular, lSubfield, kInL, finiteExtension, subringS, kInS, SInK, TSubfield, lInT, point, onS Fact,
		) {
			zero := a.TermAs[A]("M.zero")
			chart := a.TermAs[Set[A]]("«chart»")
			points := a.TermAs[Set[Fun[A, A]]]("«points»")
			pointsInT := a.TermAs[Set[Fun[A, A]]]("«pointsInT»")
			restriction := a.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
			restricted := a.TermAs[Fun[A, A]]("«restricted»")
			inM := a.Have(
				"in M restriction is one-to-one on the points of the chart, onto the points of S",
				"injective_on(«points», «restriction») ∧ image(«restriction», «points») = «below»",
				By(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					kInS,
					SInK,
					ConstantPointsInField.Read(M).At(K, k, l, S)))
			inT := a.Have(
				"and so it is in T",
				"injective_on(«pointsInT», «restriction») ∧ image(«restriction», «pointsInT») = «belowInT»",
				By(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					kInS,
					SInK,
					TSubfield,
					lInT,
					ConstantChartPoints.Read(M).At(K, k, l, S, T)))
			below := a.Have(
				"ψ restricts to a point of S",
				"«restricted» ∈ «below»",
				By(inM, point, set_image.FunInImage.At(restriction, points, ψ)))
			belowInT := a.Have(
				"with its values in T, since on S it is ψ",
				"«restricted» ∈ «belowInT»",
				By(
					below,
					onS,
					TSubfield,
					ring_homomorphism.RestrictionImageKernel.At(S, S, zero, ψ),
					set_order.SubsetRefl.At(S),
					residue_points.PointsInSubfield.Read(M).At(k, S, T, restricted)))
			θ, θData := a.ObtainAs[Fun[A, A]](
				"it extends to a point θ of the chart in T",
				"∃θ:A → A. «restricted» = «restriction»(θ) ∧ θ ∈ «pointsInT»",
				By(belowInT, inT, set_basic.InImage.At(restriction, pointsInT, restricted)))
			inField := a.Have(
				"read in M, θ is a point of the chart with values in T",
				"θ ∈ «points» ∧ image(θ, «chart») ⊆ T",
				By(θData, TSubfield, residue_points.PointsInSubfield.Read(M).At(l, chart, T, θ)))
			same := a.Have(
				"θ and ψ have one restriction, so they are one point",
				"θ = ψ",
				By(inM, θData, inField, point, functions.InjectiveOnDef.At(points, restriction)))
			a.Show(
				"so ψ takes the chart into T",
				By(Normalized, inField, same))
		}),
})}

// ConstantPointDegree — an l-point ψ of the chart S' of S whose kernel n lies
// over a maximal ideal m of S of degree d: n is maximal, of finite degree e over
// l, and e·gcd(d, r) = d. The values of ψ on S are the subfield with q^d
// elements, those on S' the subfield with q^(r·e) elements. The first lies in
// the second, so d ∣ r·e. And S' lands in every subfield with q^L elements
// holding the two generating subfields, so r·e divides each common multiple L
// of d and r.
var ConstantPointDegree = constantPointDegreeThm{family.Add(registry.ProofEntry{
	Name: "ConstantPointDegree",
	Key:  "prop_eb25506f00248cf3",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), «constants», S)"},
			{Name: "residues", Text: "quotient_module(«vectors»(S), m)"},
			{Name: "degree", Text: "module_dim(«scalars»(k), «residues»)"},
			{Name: "points", Text: "algebra_points(«scalars»(«chart»), field_ring(M), «constants», λx:A. x)"},
			{Name: "below", Text: "algebra_points(«scalars»(S), field_ring(M), k, λx:A. x)"},
			{Name: "kernel", Text: "ring_kernel(M.zero, «chart», ψ)"},
			{Name: "chartResidues", Text: "quotient_module(«vectors»(«chart»), «kernel»)"},
			{Name: "index", Text: "module_dim(«scalars»(«constants»), «chartResidues»)"},
			{Name: "restriction", Text: "λψ:A → A. λx:A. COND(x ∈ S, ψ(x), M.zero)"},
			{Name: "restricted", Text: "λx:A. COND(x ∈ S, ψ(x), M.zero)"},
			{Name: "within", Text: "λL:num. finite_constants(field_ring(M), card(k), L)"},
			{Name: "common", Text: "«within»(«degree» * r)"},
		},
		Binders: "∀M:field_on(A). ∀K k S m:set(A). ∀r:num. ∀ψ:(A → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
			"0 < r",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"maximal_ideal(«scalars»(S), m)",
			"finite_dimensional(«scalars»(k), «residues»)",
			"ψ ∈ «points»",
			"«kernel» ∩ S = m",
		},
		Conclusion: "maximal_ideal(«scalars»(«chart»), «kernel») ∧ " +
			"finite_dimensional(«scalars»(«constants»), «chartResidues») ∧ " +
			"«index» * nat_gcd(«degree», r) = «degree»",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, S, m *Expr[Set[A]],
			r *Expr[Nat],
			ψ *Arrow[A, A],
			closed, regular, finiteK, positiveR, subringS, SInK, kInS, maximal, finiteResidues, point, over Fact,
		) {
			zero := a.TermAs[A]("M.zero")
			constants := a.TermAs[Set[A]]("«constants»")
			chart := a.TermAs[Set[A]]("«chart»")
			kernel := a.TermAs[Set[A]]("«kernel»")
			points := a.TermAs[Set[Fun[A, A]]]("«points»")
			restriction := a.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
			restricted := a.TermAs[Fun[A, A]]("«restricted»")
			degree := a.TermAs[Nat]("«degree»")
			index := a.TermAs[Nat]("«index»")
			product := a.TermAs[Nat]("«degree» * r")
			power := a.TermAs[Nat]("r * «index»")
			common := a.TermAs[Set[A]]("«common»")
			data := a.Have(
				"l is a finite subfield of M holding k, of finite degree over it",
				"subfield(M, k) ∧ "+
					"subfield(M, «constants») ∧ "+
					"k ⊆ «constants» ∧ "+
					"finite(«constants») ∧ "+
					"finite_extension(M, k, «constants»)",
				By(closed, regular, finiteK, positiveR, constant_galois.ConstantCompositeData.Read(M).At(K, k, r)))
			inChart := a.Have(
				"the chart is a subring of M holding l and S",
				"subring(field_ring(M), «chart») ∧ «constants» ⊆ «chart» ∧ S ⊆ «chart»",
				By(
					data,
					regular,
					subringS,
					SInK,
					kInS,
					constant_field_extension.ConstantChartRing.Read(M).At(K, k, constants, S)))
			cut := a.Have(
				"cutting ψ down to S keeps its values on S and its kernel there",
				"image(«restricted», S) = image(ψ, S) ∧ ring_kernel(M.zero, S, «restricted») = «kernel» ∩ S",
				By(inChart, ring_homomorphism.RestrictionImageKernel.At(S, chart, zero, ψ)))
			below := a.Have(
				"ψ restricts to a point of S",
				"«restricted» ∈ «below»",
				By(
					data,
					regular,
					subringS,
					kInS,
					SInK,
					point,
					ConstantPointsInField.Read(M).At(K, k, constants, S),
					set_image.FunInImage.At(restriction, points, ψ)))
			image := a.Have(
				"its kernel is m, so ψ maps S onto the subfield with q^d elements",
				"image(ψ, S) = «within»(«degree»)",
				By(
					closed,
					data,
					finiteK,
					subringS,
					kInS,
					maximal,
					finiteResidues,
					below,
					cut,
					over,
					residue_points.ResiduePointImage.Read(M).At(k, S, m, restricted)))
			positiveD := a.Have(
				"d is positive",
				"0 < «degree»",
				By(
					data,
					finiteK,
					subringS,
					kInS,
					maximal,
					finiteResidues,
					residue_points.ResidueSize.Read(M).At(k, S, m)))
			values := a.Have(
				"ψ takes the chart into the subfield with q^L elements, for L a common multiple of d and r",
				"∀L:num. 0 < L ∧ «degree» ∣ L ∧ r ∣ L ⇒ image(ψ, «chart») ⊆ «within»(L)",
				Derive(func(b *Argument) {
					L := b.FixAs[Nat]()
					multiple := b.Assume()
					target := b.TermAs[Set[A]]("«within»(L)")
					subfieldT := b.Have(
						"the subfield with q^L elements",
						"subfield(M, «within»(L))",
						By(closed, data, finiteK, multiple, finite_field.FiniteConstantsSubfield.Read(M).At(k, L)))
					holds := b.Have(
						"holds l and the subfield with q^d elements",
						"«constants» ⊆ «within»(L) ∧ «within»(«degree») ⊆ «within»(L)",
						By(
							closed,
							data,
							finiteK,
							positiveD,
							positiveR,
							multiple,
							finite_field.FiniteConstantsContained.Read(M).At(k, r, L),
							finite_field.FiniteConstantsContained.Read(M).At(k, degree, L)))
					onS := b.Have(
						"so it holds the values of ψ on S",
						"image(ψ, S) ⊆ «within»(L)",
						By(image, holds))
					b.Show(
						"and therefore those on the chart",
						By(
							regular,
							data,
							subringS,
							kInS,
							SInK,
							subfieldT,
							holds,
							point,
							onS,
							ConstantPointValues.Read(M).At(K, k, constants, S, target, ψ)))
				}))
			positiveProduct := a.Have(
				"d·r is a positive common multiple of d and r",
				"0 < «degree» * r ∧ «degree» ∣ «degree» * r ∧ r ∣ «degree» * r",
				ByArith(
					positiveD,
					positiveR,
					nat_arith.MulEqZero.At(degree, r),
					nat_divides.DividesOwnMultiple.At(degree, r),
					nat_divides.DividesOwnMultiple.At(r, degree)))
			intoCommon := a.Have(
				"so ψ takes the chart into the finite subfield with q^(d·r) elements",
				"image(ψ, «chart») ⊆ «common»",
				By(values.At(product), positiveProduct))
			commonData := a.Have(
				"which is a finite subfield of M holding l",
				"subfield(M, «common») ∧ finite(«common») ∧ «constants» ⊆ «common»",
				By(
					closed,
					data,
					finiteK,
					positiveProduct,
					positiveR,
					finite_field.FiniteConstantsSubfield.Read(M).At(k, product),
					cardinality.HasSizeDef,
					finite_field.FiniteConstantsContained.Read(M).At(k, r, product)))
			pointInCommon := a.Have(
				"so ψ is a point of the chart in that subfield",
				"ψ ∈ algebra_points(«scalars»(«chart»), «scalars»(«common»), «constants», λx:A. x)",
				By(
					point,
					intoCommon,
					commonData,
					residue_points.PointsInSubfield.Read(M).At(constants, chart, common, ψ)))
			residue := a.Have(
				"so its kernel is maximal, of finite degree over l",
				"maximal_ideal(«scalars»(«chart»), «kernel») ∧ "+
					"finite_dimensional(«scalars»(«constants»), «chartResidues»)",
				By(
					data,
					commonData,
					inChart,
					pointInCommon,
					residue_points.PointKernelMaximal.Read(M).At(constants, chart, common, ψ)))
			imageChart := a.Have(
				"ψ maps the chart onto the subfield with q^(r·e) elements, as l has q^r",
				"image(ψ, «chart») = «within»(r * «index»)",
				By(
					closed,
					data,
					inChart,
					residue,
					point,
					residue_points.ResiduePointImage.Read(M).At(constants, chart, kernel, ψ),
					finite_field.FiniteConstantsSubfield.Read(M).At(k, r),
					cardinality.HasSizeDef,
					finiteK,
					positiveR,
					finite_field.FiniteConstantsTower.At(
						a.TermAs[RingOps[A]]("field_ring(M)"), a.TermAs[Nat]("card(k)"), r, index)))
			positiveIndex := a.Have(
				"e is positive",
				"0 < «index»",
				By(data, inChart, residue, residue_points.ResidueSize.Read(M).At(constants, chart, kernel)))
			positivePower := a.Have(
				"r·e is positive",
				"0 < r * «index»",
				ByArith(positiveR, positiveIndex, nat_arith.MulEqZero.At(r, index)))
			dividesPower := a.Have(
				"the values on S lie among those on the chart, so d ∣ r·e",
				"«degree» ∣ r * «index»",
				By(
					closed,
					data,
					finiteK,
					positiveD,
					positivePower,
					inChart,
					image,
					imageChart,
					set_image.ImageSubset.At(ψ, S, chart),
					finite_field.FiniteConstantsContained.Read(M).At(k, degree, power)))
			least := a.Have(
				"r·e divides every positive common multiple of d and r",
				"∀L:num. 0 < L ∧ «degree» ∣ L ∧ r ∣ L ⇒ r * «index» ∣ L",
				Derive(func(b *Argument) {
					L := b.FixAs[Nat]()
					multiple := b.Assume()
					b.Show(
						"the values on the chart lie in the subfield with q^L elements",
						By(
							closed,
							data,
							finiteK,
							positivePower,
							multiple,
							imageChart,
							values.At(L),
							finite_field.FiniteConstantsContained.Read(M).At(k, power, L)))
				}))
			a.Show(
				"so e·gcd(d, r) = d",
				By(
					residue,
					positiveD,
					positiveR,
					dividesPower,
					least,
					nat_gcd.GcdFromCommonMultiples.At(degree, r, index)))
		}),
})}

// ConstantResidueFinite — an ideal n of the chart S' over an ideal m of S of
// finite colength has finite colength over l: S'/mS' has the k-dimension of
// S/m, and S'/n is a quotient of it.
var ConstantResidueFinite = constantResidueFiniteThm{family.Add(registry.ProofEntry{
	Name: "ConstantResidueFinite",
	Key:  "prop_95532e7253179b5f",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "ambient", Text: "regular_module(field_ring(M))"},
			{Name: "chart", Text: "λX:set(A). constant_chart(field_ring(M), l, X)"},
		},
		Binders: "∀M:field_on(A). ∀K k l S m n:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"ring_ideal(«scalars»(S), m)",
			"finite_dimensional(«scalars»(k), quotient_module(«vectors»(S), m))",
			"ring_ideal(«scalars»(«chart»(S)), n)",
			"m ⊆ n",
		},
		Conclusion: "finite_dimensional(«scalars»(l), quotient_module(«vectors»(«chart»(S)), n))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, S, m, n *Expr[Set[A]],
			regular, lSubfield, kInL, finiteExtension, subringS, SInK, kInS, idealM, finiteResidues, idealN, mInN Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			ring := a.TermAs[RingOps[A]]("field_ring(M)")
			lScalars := a.TermAs[RingOps[A]]("«scalars»(l)")
			SScalars := a.TermAs[RingOps[A]]("«scalars»(S)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
			carrier := a.TermAs[Set[A]]("M.carrier")
			chartS := a.TermAs[Set[A]]("«chart»(S)")
			chartM := a.TermAs[Set[A]]("«chart»(m)")
			inverse := a.TermAs[Fun[A, A]]("M.inv")
			regularData := a.Have(
				"k and K are subfields of M, k in K",
				"subfield(M, k) ∧ subfield(M, K) ∧ k ⊆ K",
				By(regular, function_field.RegularFunctionFieldDef.At(ops, k, K)))
			inChart := a.Have(
				"the chart of S is a subring of M holding l",
				"subring(field_ring(M), «chart»(S)) ∧ l ⊆ «chart»(S)",
				By(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subringS,
					SInK,
					kInS,
					constant_field_extension.ConstantChartRing.Read(M).At(K, k, l, S)))
			subspaces := a.Have(
				"over k, S and m are subspaces of K",
				"submodule(«scalars»(k), «vectors»(K), S) ∧ submodule(«scalars»(k), «vectors»(K), m)",
				By(
					regularData,
					subringS,
					kInS,
					SInK,
					idealM,
					constant_field_extension.ConstantRingSubspace.Read(M).At(K, k, S),
					constant_field_extension.ConstantIdealSubspace.Read(M).At(K, k, S, m)))
			mInS := a.Have(
				"m lies in S",
				"m ⊆ S",
				By(idealM, ring_ideal.IdealSubset.At(SScalars, m)))
			quotient := a.Have(
				"S'/mS' is finite over l",
				"finite_dimensional(«scalars»(l), quotient_module(«vectors»(«chart»(S)), «chart»(m)))",
				By(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					subspaces,
					mInS,
					finiteResidues,
					constant_field_extension.ConstantChartQuotient.Read(M).At(K, k, l, S, m)))
			inside := a.Have(
				"l, the chart, n and m all lie in the carrier of M, n in the chart",
				"l ⊆ M.carrier ∧ «chart»(S) ⊆ M.carrier ∧ n ⊆ «chart»(S) ∧ m ⊆ M.carrier",
				By(
					lSubfield,
					inChart,
					idealN,
					mInS,
					subringS,
					field.SubfieldSubset.At(ops, l),
					comm_ring.SubringSubset.At(ring, chartS),
					comm_ring.SubringSubset.At(ring, S),
					ring_ideal.IdealSubset.At(a.TermAs[RingOps[A]]("«scalars»(«chart»(S))"), n),
					set_order.SubsetTrans))
			chartModules := a.Have(
				"over l the chart and the chart of m are submodules of M",
				"module_on(«scalars»(l), «ambient») ∧ "+
					"submodule(«scalars»(l), «ambient», «chart»(S)) ∧ "+
					"submodule(«scalars»(l), «ambient», «chart»(m))",
				By(
					lSubfield,
					inside,
					inChart,
					constant_field_extension.ConstantChartSubmodule.Read(M).At(l, m),
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(l, chartS)))
			idealModule := a.Have(
				"and so is n, an ideal of a ring holding l",
				"submodule(«scalars»(l), «ambient», n)",
				By(
					lSubfield,
					inside,
					inChart,
					idealN,
					field.CarrierSubfield.Read(M),
					constant_field_extension.ConstantIdealSubspace.Read(M).At(carrier, l, chartS, n),
					constant_field_extension.ConstantSubspaceSubmodule.Read(M).At(carrier, l, n),
					set_order.SubsetRefl.At(carrier)))
			chartInN := a.Have(
				"n holds m, so it holds the chart of m",
				"«chart»(m) ⊆ n",
				By(idealModule, mInN, constant_field_extension.ConstantChartLeast.At(ring, l, m, n)))
			a.Show(
				"so S'/n is a quotient of a finite space",
				By(
					chartModules,
					inside,
					chartInN,
					quotient,
					idealModule,
					field.SubfieldRingSubfield.Read(M).At(l, l),
					lSubfield,
					module_dimension.QuotientChainDim.At(lScalars, ambient, inverse, chartS, n, chartM)))
		}),
})}

// MaximalIdealSplitting — the maximal ideals of the chart S' of S over the
// field l with q^r elements lying over a maximal ideal m of S of degree d
// number gcd(d, r), each of degree d / gcd(d, r) over l. Restriction to S
// carries the l-points of S' with kernel over m bijectively onto the d k-points
// of S with kernel m. Their kernels are those ideals, and the points with
// kernel n are as many as the degree of n, which is the same for every n.
var MaximalIdealSplitting = maximalIdealSplittingThm{family.Add(registry.ProofEntry{
	Name: "MaximalIdealSplitting",
	Key:  "prop_7654cfb20f992be4",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), r)"},
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), «constants», S)"},
			{Name: "residues", Text: "quotient_module(«vectors»(S), m)"},
			{Name: "degree", Text: "module_dim(«scalars»(k), «residues»)"},
			{Name: "gcd", Text: "nat_gcd(«degree», r)"},
			{Name: "points", Text: "algebra_points(«scalars»(«chart»), field_ring(M), «constants», λx:A. x)"},
			{Name: "below", Text: "algebra_points(«scalars»(S), field_ring(M), k, λx:A. x)"},
			{Name: "restriction", Text: "λψ:A → A. λx:A. COND(x ∈ S, ψ(x), M.zero)"},
			{Name: "kernelOf", Text: "λψ:A → A. ring_kernel(M.zero, «chart», ψ)"},
			{Name: "above", Text: "{n:set(A) | maximal_ideal(«scalars»(«chart»), n) ∧ n ∩ S = m}"},
			{Name: "pointsOver", Text: "{ψ:A → A | ψ ∈ «points» ∧ ring_kernel(M.zero, «chart», ψ) ∩ S = m}"},
			{Name: "base", Text: "{φ:A → A | φ ∈ «below» ∧ ring_kernel(M.zero, S, φ) = m}"},
			{Name: "fibre", Text: "λn:set(A). {ψ:A → A | ψ ∈ «points» ∧ ring_kernel(M.zero, «chart», ψ) = n}"},
			{Name: "index", Text: "λn:set(A). " +
				"    module_dim(«scalars»(«constants»), quotient_module(«vectors»(«chart»), n))"},
		},
		Binders: "∀M:field_on(A). ∀K k S m:set(A). ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
			"0 < r",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"maximal_ideal(«scalars»(S), m)",
			"finite_dimensional(«scalars»(k), «residues»)",
		},
		Conclusion: "has_size(«above», «gcd») ∧ " +
			"(∀n:set(A). maximal_ideal(«scalars»(«chart»), n) ∧ n ∩ S = m ⇒ «index»(n) * «gcd» = «degree»)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, S, m *Expr[Set[A]],
			r *Expr[Nat],
			closed, regular, finiteK, positiveR, subringS, SInK, kInS, maximal, finiteResidues Fact,
		) {
			zero := a.TermAs[A]("M.zero")
			constants := a.TermAs[Set[A]]("«constants»")
			chart := a.TermAs[Set[A]]("«chart»")
			chartRing := a.TermAs[RingOps[A]]("«scalars»(«chart»)")
			sRing := a.TermAs[RingOps[A]]("«scalars»(S)")
			points := a.TermAs[Set[Fun[A, A]]]("«points»")
			pointsOver := a.TermAs[Set[Fun[A, A]]]("«pointsOver»")
			base := a.TermAs[Set[Fun[A, A]]]("«base»")
			above := a.TermAs[Set[Set[A]]]("«above»")
			restriction := a.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
			kernelOf := a.TermAs[Fun[Fun[A, A], Set[A]]]("«kernelOf»")
			degree := a.TermAs[Nat]("«degree»")
			gcd := a.TermAs[Nat]("«gcd»")
			data := a.Have(
				"l is a finite subfield of M holding k, of finite degree over it",
				"subfield(M, k) ∧ "+
					"subfield(M, «constants») ∧ "+
					"k ⊆ «constants» ∧ "+
					"finite(«constants») ∧ "+
					"finite_extension(M, k, «constants»)",
				By(closed, regular, finiteK, positiveR, constant_galois.ConstantCompositeData.Read(M).At(K, k, r)))
			inChart := a.Have(
				"the chart is a subring of M holding l and S",
				"subring(field_ring(M), «chart») ∧ «constants» ⊆ «chart» ∧ S ⊆ «chart»",
				By(
					data,
					regular,
					subringS,
					SInK,
					kInS,
					constant_field_extension.ConstantChartRing.Read(M).At(K, k, constants, S)))
			bijection := a.Have(
				"restriction is one-to-one on the points of the chart, onto the points of S",
				"injective_on(«points», «restriction») ∧ image(«restriction», «points») = «below»",
				By(data, regular, subringS, kInS, SInK, ConstantPointsInField.Read(M).At(K, k, constants, S)))
			baseSize := a.Have(
				"the points of S with kernel m number d",
				"has_size(«base», «degree»)",
				By(
					closed,
					data,
					finiteK,
					subringS,
					kInS,
					maximal,
					finiteResidues,
					residue_points.ResiduePoints.Read(M).At(k, S, m)))
			positiveD := a.Have(
				"d is positive",
				"0 < «degree»",
				By(
					data,
					finiteK,
					subringS,
					kInS,
					maximal,
					finiteResidues,
					residue_points.ResidueSize.Read(M).At(k, S, m)))
			forward := a.Have(
				"a point of the chart restricts to a point of S, its kernel cut down to S",
				Statement{
					Binders:    "∀ψ:A → A.",
					Hypotheses: []string{"ψ ∈ «points»"},
					Conclusion: "(λx:A. COND(x ∈ S, ψ(x), M.zero)) ∈ «below» ∧ " +
						"ring_kernel(M.zero, S, λx:A. COND(x ∈ S, ψ(x), M.zero)) = ring_kernel(M.zero, «chart», ψ) ∩ S",
				},
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, A]]()
					point := b.Assume()
					b.Show(
						"restriction carries the points of the chart to those of S, and it cuts the kernel down to S",
						By(
							bijection,
							inChart,
							point,
							set_image.FunInImage.At(restriction, points, ψ),
							ring_homomorphism.RestrictionImageKernel.At(S, chart, zero, ψ)))
				}))
			extension := a.Have(
				"a point of S is the restriction of a point of the chart",
				"∀φ:(A → A). φ ∈ «below» ⇒ ∃ψ:(A → A). ψ ∈ «points» ∧ φ = λx:A. COND(x ∈ S, ψ(x), M.zero)",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]()
					point := b.Assume()
					b.Show(
						"restriction takes the points of the chart onto those of S",
						By(bijection, point, set_basic.InImage.At(restriction, points, φ)))
				}))
			intoBase := a.Have(
				"a point of the chart over m restricts to a point of S with kernel m",
				"∀ψ:(A → A). ψ ∈ «pointsOver» ⇒ (λx:A. COND(x ∈ S, ψ(x), M.zero)) ∈ «base»",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, A]]()
					inOver := b.Assume()
					b.Show(
						"its restriction has the kernel cut down to S",
						BySets(forward.At(ψ), inOver))
				}))
			ontoBase := a.Have(
				"a point of S with kernel m restricts a point of the chart over m",
				"∀φ:(A → A). φ ∈ «base» ⇒ φ ∈ image(«restriction», «pointsOver»)",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]()
					inBase := b.Assume()
					parts := b.Have(
						"φ is a point of S with kernel m",
						"φ ∈ «below» ∧ ring_kernel(M.zero, S, φ) = m",
						BySets(inBase))
					ψ, ψData := b.ObtainAs[Fun[A, A]](
						"it is the restriction of a point ψ of the chart",
						"∃ψ:A → A. ψ ∈ «points» ∧ φ = (λx:A. COND(x ∈ S, ψ(x), M.zero))",
						By(extension.At(φ), parts))
					kernelOver := b.Have(
						"the kernel of ψ lies over m",
						"ring_kernel(M.zero, «chart», ψ) ∩ S = m",
						By(forward.At(ψ), ψData, parts))
					inOver := b.Have(
						"so ψ is a point over m",
						"ψ ∈ «pointsOver»",
						BySets(ψData, kernelOver))
					b.Show(
						"and φ is its restriction",
						By(ψData, inOver, set_image.FunInImage.At(restriction, pointsOver, ψ)))
				}))
			intoBaseSet := a.Have(
				"restriction carries the points over m into the points of S with kernel m",
				"image(«restriction», «pointsOver») ⊆ «base»",
				By(intoBase, set_image.ImageSubsetIff.At(restriction, pointsOver, base)))
			ontoBaseSet := a.Have(
				"and onto them",
				"«base» ⊆ image(«restriction», «pointsOver»)",
				By(ontoBase, set_basic.SubsetDef))
			imageBase := a.Have(
				"so restriction carries the points over m onto the points of S with kernel m",
				"image(«restriction», «pointsOver») = «base»",
				By(intoBaseSet, ontoBaseSet, set_order.SubsetAntisym))
			overInPoints := a.Have(
				"the points over m are points of the chart",
				"«pointsOver» ⊆ «points»",
				SetTac())
			injective := a.Have(
				"one to one",
				"injective_on(«pointsOver», «restriction»)",
				By(bijection, overInPoints, functions.InjectiveOnSubset.At(restriction, pointsOver, points)))
			overSize := a.Have(
				"so the points over m number d",
				"has_size(«pointsOver», «degree»)",
				By(
					injective,
					imageBase,
					baseSize,
					cardinality.HasSizeImageInjEq.At(restriction, pointsOver, degree)))
			perIdeal := a.Have(
				"over an ideal n the points with kernel n are counted by the degree of n, and there is one",
				Statement{
					Binders:    "∀n:set(A).",
					Hypotheses: []string{"maximal_ideal(«scalars»(«chart»), n)", "n ∩ S = m"},
					Conclusion: "has_size(«fibre»(n), «index»(n)) ∧ " +
						"(∃ψ:A → A. ψ ∈ «points» ∧ ring_kernel(M.zero, «chart», ψ) = n) ∧ " +
						"«index»(n) * «gcd» = «degree»",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Set[A]]()
					parts := b.Conjuncts(
						b.Assume(),
						"n is maximal",
						"n lies over m")
					mInN := b.Have(
						"m lies in n",
						"m ⊆ n",
						BySets(parts[1]))
					ideals := b.Have(
						"n and m are ideals",
						"ring_ideal(«scalars»(«chart»), n) ∧ ring_ideal(«scalars»(S), m)",
						By(
							parts[0],
							maximal,
							ring_ideal.MaximalIdealIdeal.At(chartRing, n),
							ring_ideal.MaximalIdealIdeal.At(sRing, m)))
					finite := b.Have(
						"the residues of n are finite over l",
						"finite_dimensional(«scalars»(«constants»), quotient_module(«vectors»(«chart»), n))",
						By(
							regular,
							data,
							subringS,
							SInK,
							kInS,
							ideals,
							finiteResidues,
							mInN,
							ConstantResidueFinite.Read(M).At(K, k, constants, S, m, n)))
					sized := b.Have(
						"so the points with kernel n number the degree of n",
						"has_size(«fibre»(n), «index»(n))",
						By(
							closed,
							data,
							inChart,
							parts[0],
							finite,
							residue_points.ResiduePoints.Read(M).At(constants, chart, n)))
					exists := b.Have(
						"and there is such a point",
						"∃ψ:A → A. ψ ∈ «points» ∧ ring_kernel(M.zero, «chart», ψ) = n",
						By(
							closed,
							data,
							inChart,
							parts[0],
							finite,
							residue_points.ResiduePointExists.Read(M).At(constants, chart, n)))
					degreeOf := b.Have(
						"which gives the degree of n",
						"«index»(n) * «gcd» = «degree»",
						Derive(func(c *Argument) {
							ψ, ψData := c.UnpackAs[Fun[A, A]](exists)
							kernelOver := c.Have(
								"the kernel of ψ lies over m",
								"ring_kernel(M.zero, «chart», ψ) ∩ S = m",
								By(ψData, parts[1]))
							c.Show(
								"the degree of the kernel of ψ divides out gcd(d, r)",
								By(
									closed,
									regular,
									finiteK,
									positiveR,
									subringS,
									SInK,
									kInS,
									maximal,
									finiteResidues,
									kernelOver,
									ψData,
									ConstantPointDegree.Read(M).At(K, k, S, m, r, ψ)))
						}))
					b.Show(
						"the three together",
						By(sized, exists, degreeOf))
				}))
			u, uEq := a.ObtainAs[Nat](
				"write d = gcd(d, r)·u",
				"∃u:num. «degree» = «gcd» * u",
				By(nat_gcd.Gcd.At(degree, r), nat_divides.DividesFactor.At(gcd, degree)))
			nonzero := a.Have(
				"gcd(d, r) and u are not zero, as d is positive",
				"«gcd» ≠ 0 ∧ u ≠ 0",
				ByArith(uEq, positiveD, nat_arith.MulEqZero.At(gcd, u)))
			fibres := a.Have(
				"the points over m with kernel n number u, for each n: the degree of n is u",
				Statement{
					Binders:    "∀n:set(A).",
					Hypotheses: []string{"n ∈ «above»"},
					Conclusion: "has_size({ψ:A → A | ψ ∈ «pointsOver» ∧ ring_kernel(M.zero, «chart», ψ) = n}, u)",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Set[A]]()
					parts := b.Have(
						"n is maximal, over m",
						"maximal_ideal(«scalars»(«chart»), n) ∧ n ∩ S = m",
						BySets(b.Assume()))
					index := b.TermAs[Nat]("«index»(n)")
					counted := b.Have(
						"the points with kernel n number the degree of n",
						"has_size(«fibre»(n), «index»(n)) ∧ «index»(n) * «gcd» = «degree»",
						By(perIdeal.At(n), parts))
					same := b.Have(
						"a point with kernel n lies over m already",
						"{ψ:A → A | ψ ∈ «pointsOver» ∧ ring_kernel(M.zero, «chart», ψ) = n} = «fibre»(n)",
						BySets(parts))
					size := b.Have(
						"cancelling gcd(d, r), that degree is u",
						"«index»(n) = u",
						By(
							counted,
							uEq,
							nonzero,
							nat_arith.MulEqLCancel.At(gcd, index, u),
							nat_arith.MulSym.At(index, gcd)))
					b.Show(
						"so the fibre has u elements",
						By(counted, same, size))
				}))
			intoAbove := a.Have(
				"the kernel of a point over m is a maximal ideal over m",
				"∀ψ:(A → A). ψ ∈ «pointsOver» ⇒ ring_kernel(M.zero, «chart», ψ) ∈ «above»",
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, A]]()
					parts := b.Have(
						"ψ is a point of the chart with kernel over m",
						"ψ ∈ «points» ∧ ring_kernel(M.zero, «chart», ψ) ∩ S = m",
						BySets(b.Assume()))
					maximalKernel := b.Have(
						"its kernel is maximal",
						"maximal_ideal(«scalars»(«chart»), ring_kernel(M.zero, «chart», ψ))",
						By(
							closed,
							regular,
							finiteK,
							positiveR,
							subringS,
							SInK,
							kInS,
							maximal,
							finiteResidues,
							parts,
							ConstantPointDegree.Read(M).At(K, k, S, m, r, ψ)))
					b.Show(
						"so it is an ideal over m",
						BySets(parts, maximalKernel))
				}))
			hitsAbove := a.Have(
				"every maximal ideal over m is the kernel of a point over m",
				"∀n:set(A). n ∈ «above» ⇒ n ∈ image(«kernelOf», «pointsOver»)",
				Derive(func(b *Argument) {
					n := b.FixAs[Set[A]]()
					parts := b.Have(
						"n is maximal, over m",
						"maximal_ideal(«scalars»(«chart»), n) ∧ n ∩ S = m",
						BySets(b.Assume()))
					ψ, ψData := b.ObtainAs[Fun[A, A]](
						"take a point ψ with kernel n",
						"∃ψ:A → A. ψ ∈ «points» ∧ ring_kernel(M.zero, «chart», ψ) = n",
						By(perIdeal.At(n), parts))
					inOver := b.Have(
						"ψ lies over m",
						"ψ ∈ «pointsOver»",
						BySets(ψData, parts))
					b.Show(
						"and n is its kernel",
						By(ψData, inOver, set_image.FunInImage.At(kernelOf, pointsOver, ψ)))
				}))
			inAbove := a.Have(
				"the kernels of the points over m are maximal ideals over m",
				"image(«kernelOf», «pointsOver») ⊆ «above»",
				By(intoAbove, set_image.ImageSubsetIff.At(kernelOf, pointsOver, above)))
			allAbove := a.Have(
				"and every such ideal is a kernel",
				"«above» ⊆ image(«kernelOf», «pointsOver»)",
				By(hitsAbove, set_basic.SubsetDef))
			imageIdeals := a.Have(
				"so the maximal ideals over m are exactly the kernels of the points over m",
				"image(«kernelOf», «pointsOver») = «above»",
				By(inAbove, allAbove, set_order.SubsetAntisym))
			finiteOver := a.Have(
				"the points over m are finitely many, d in all",
				"finite(«pointsOver») ∧ card(«pointsOver») = «degree»",
				By(overSize, cardinality.HasSizeDef))
			finiteAbove := a.Have(
				"the ideals are finitely many",
				"finite(«above»)",
				By(finiteOver, imageIdeals, finite_set.FiniteImage.At(kernelOf, pointsOver)))
			oneIdeal := a.Have(
				"a point over m has its kernel as its one ideal over m",
				"∀ψ:(A → A). ψ ∈ «pointsOver» ⇒ ∃!n:set(A). n ∈ «above» ∧ ring_kernel(M.zero, «chart», ψ) = n",
				By(intoAbove))
			scaled := a.Simplified(
				GroupPremises(
					finiteAbove, nat_sum.ScalarLeft.At(u, a.TermAs[Fun[Set[A], Nat]]("λn:set(A). 1"), above)),
				Fwd(nat_arith.MulOne))
			counted := a.Have(
				"counted by the fibres of the kernel, they number u·#ideals",
				"card(«pointsOver») = u * card(«above»)",
				CalcEq(
					Leg(
						a.TermAs[Nat]("nat_sum(«above», λn:set(A). u)"),
						"each ideal over m has a fibre of u points",
						By(
							finiteOver,
							oneIdeal,
							fibres,
							nat_sum.CardByFibres.At(
								pointsOver,
								above,
								a.TermAs[Fun[Fun[A, A], Fun[Set[A], Bool]]](
									"λψ:A → A. λn:set(A). ring_kernel(M.zero, «chart», ψ) = n"),
								a.TermAs[Fun[Set[A], Nat]]("λn:set(A). u")))),
					Leg(
						a.TermAs[Nat]("u * nat_sum(«above», λn:set(A). 1)"),
						"the constant comes out of the sum",
						By(finiteAbove, scaled)),
					FinalLeg(
						"and the sum of ones is the number of ideals",
						By(finiteAbove, nat_sum.SumOfOnes.At(above)))))
			number := a.TermAs[Nat]("card(«above»)")
			count := a.Have(
				"cancelling u from u·#ideals = d = gcd(d, r)·u",
				"card(«above») = «gcd»",
				By(
					finiteOver,
					counted,
					uEq,
					nonzero,
					nat_arith.MulEqLCancel.At(u, number, gcd),
					nat_arith.MulSym.At(gcd, u)))
			a.Show(
				"so there are gcd(d, r) ideals, each of the degree found",
				By(finiteAbove, count, perIdeal, cardinality.HasSizeDef))
		}),
})}
