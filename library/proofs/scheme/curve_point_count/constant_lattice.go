// constant_lattice.go — the cohomology of a lattice pair survives a constant
// extension. H⁰ is the meet of the two charts, and a chart of a meet is the meet
// of the charts; H¹ is the ambient modulo the sum of the charts, and the ambient
// and the sum of the extended pair are the charts of the ambient and the sum of
// the pair. The dimensions of a chart and of a quotient of charts are the
// dimensions before the extension, and the genus is the second of them at the
// structure pair.

package curve_point_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantChartLatticeDimensions — an invertible pair keeps both cohomology
// dimensions over a constant extension. H⁰ of the extended pair is the meet of
// the charts, the chart of the meet, of the dimension of the meet. H¹ of the
// extended pair is the chart of the ambient modulo the chart of the sum, of the
// dimension of the ambient modulo the sum.
var ConstantChartLatticeDimensions = constantChartLatticeDimensionsThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartLatticeDimensions",
	Key:  "prop_3de9c3559244203d",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λS:set(A). restrict_ring(field_ring(M), S)"},
			{Name: "vectors", Text: "λS:set(A). restrict_module(regular_module(field_ring(M)), S)"},
			{Name: "chart", Text: "λS:set(A). constant_chart(field_ring(M), l, S)"},
			{Name: "chartPair", Text: "(«chart»(fst(X)), «chart»(snd(X)))"},
			{Name: "pairAmbient", Text: "lattice_pair_ambient(«scalars»(A₀₁), «vectors»(K), X)"},
			{Name: "pairSum", Text: "set_mul(M.add, fst(X), snd(X))"},
		},
		Binders: "∀M:field_on(A). ∀K k l A₀ A₁ A₀₁:set(A). ∀t:A. ∀X:prod(set(A), set(A)).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"«ambientInvertible»(X)",
		},
		Conclusion: "module_dim(«scalars»(l), " +
			"    lattice_pair_h0(«vectors»(constant_composite(M, K, l)), «chartPair»)) = " +
			"module_dim(«scalars»(k), lattice_pair_h0(«vectors»(K), X)) ∧ " +
			"lattice_pair_h1_dim(«scalars»(«chart»(A₀₁)), " +
			"    l, " +
			"    «vectors»(constant_composite(M, K, l)), " +
			"    «chartPair») = " +
			"lattice_pair_h1_dim(«scalars»(A₀₁), k, «vectors»(K), X)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X *Expr[Prod[Set[A], Set[A]]],
			regular, curve, lSubfield, kInL, finiteExtension, invertible Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
			functionField := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			functionRing := a.TermAs[RingOps[A]]("«ambientRing»")
			overlapRing := a.TermAs[RingOps[A]]("«scalars»(A₀₁)")
			inverse := a.TermAs[A]("M.inv(t)")
			KVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"«vectors»(constant_composite(M, K, l))")
			kScalars := a.TermAs[RingOps[A]]("«scalars»(k)")
			first, second := a.TermAs[Set[A]]("fst(X)"), a.TermAs[Set[A]]("snd(X)")
			meet := a.TermAs[Set[A]]("fst(X) ∩ snd(X)")
			ambient, sum := a.TermAs[Set[A]]("«pairAmbient»"), a.TermAs[Set[A]]("«pairSum»")
			extended := a.TermAs[Prod[Set[A], Set[A]]]("«chartPair»")
			kData := a.Conjuncts(
				a.Have(
					"k and K are subfields of M, k lying in K",
					"subfield(M, k) ∧ subfield(M, K) ∧ k ⊆ K",
					By(a.Unfolded(regular, function_field.RegularFunctionFieldDef))),
				"k is a subfield of M",
				"so is K",
				"k lies in K")
			kSubfield, inField, kInK := kData[0], kData[1], kData[2]
			functionFieldOn := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			charts := a.Conjuncts(
				GroupPremises(inField, curve, CurveOverLineChartsInField.Read(M).At(K, k, A0, A1, A01, t)),
				"A₀ is a subring of M",
				"so is A₁",
				"so is the overlap",
				"k lies in A₀",
				"and in A₁",
				"and in the overlap",
				"A₀ lies in K",
				"so does A₁",
				"so does the overlap",
				"t lies in A₀")
			biaffine := a.Have(
				"the charts and their overlap are a biaffine datum",
				"biaffine(«scalars»(A₀₁), A₀, A₁, t, M.inv(t))",
				By(a.Simplified(
					GroupPremises(
						functionFieldOn, curve, algebraic_curve.CurveLatticeData.At(functionField, k, A0, A1, A01, t)),
					InAmbient)))
			finiteCohomology := a.Have(
				"X has finite cohomology over k",
				"lattice_pair_finite(«scalars»(A₀₁), k, «vectors»(K), X)",
				By(
					curve,
					invertible,
					a.Simplified(
						algebraic_curve.InvertibleFinite.Read(functionFieldOn).At(k, A0, A1, A01, t, X),
						InAmbient)))
			pair := a.Have(
				"X is a lattice pair over the overlap, inside K",
				"lattice_pair(«scalars»(A₀₁), A₀, A₁, «vectors»(K), X)",
				By(
					invertible,
					invertible_lattice_pair.InvertibleLatticePairDef.At(functionRing, A0, A1, A01, X),
					module_record.RestrictRingTwice.At(fieldRing, K, A01),
					module_record.RegularModuleRestrict.At(fieldRing, K)))
			rings := a.Have(
				"the overlap is a subring of M lying in K and holding k, itself a subring of M",
				"subring(field_ring(M), A₀₁) ∧ subring(field_ring(M), k) ∧ A₀₁ ⊆ K ∧ k ⊆ A₀₁",
				By(M, kSubfield, charts[2], charts[5], charts[8], field_extension.SubfieldScalars.At(ops, k)))
			overlapIsRing := a.Have(
				"the overlap is a ring",
				"comm_ring_on(«scalars»(A₀₁))",
				By(charts[2], comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(A01)))
			constants := a.Have(
				"with k a subring of it",
				"subring(«scalars»(A₀₁), k)",
				By(
					Normalized,
					rings,
					comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(k),
					comm_ring.SubringRingOn.Read(overlapIsRing).At(k),
					module_record.RestrictRingTwice.At(fieldRing, A01, k)))
			overK := a.Conjuncts(
				a.Have(
					"over k, the charts of X, their sum and its ambient are subspaces of K",
					"module_on(«scalars»(k), «vectors»(K)) ∧ "+
						"submodule(«scalars»(k), «vectors»(K), fst(X)) ∧ "+
						"submodule(«scalars»(k), «vectors»(K), snd(X)) ∧ "+
						"submodule(«scalars»(k), «vectors»(K), «pairSum») ∧ "+
						"submodule(«scalars»(k), «vectors»(K), «pairAmbient»)",
					By(
						Normalized,
						biaffine,
						charts[3],
						charts[4],
						constants,
						pair,
						lattice_pair.PairOverSubring.At(overlapRing, A0, A1, t, inverse, k, KVectors, X),
						module_record.RestrictRingTwice.At(fieldRing, A01, k))),
				"K is a space over k",
				"the first chart of X is a subspace",
				"so is the second",
				"so is their sum",
				"and so is the ambient")
			finiteParts := a.Conjuncts(
				a.Have(
					"read in M, H⁰ and H¹ are finite-dimensional over k",
					"finite_dimensional(«scalars»(k), "+
						"    restrict_module(regular_module(field_ring(M)), fst(X) ∩ snd(X))) ∧ "+
						"finite_dimensional(«scalars»(k), "+
						"    quotient_module(restrict_module(regular_module(field_ring(M)), «pairAmbient»), «pairSum»))",
					By(
						finiteCohomology,
						lattice_pair.LatticePairFiniteDef.At(overlapRing, k, KVectors, X),
						lattice_pair.RestrictedPairCohomology.At(fieldRing, A01, k, K, X),
						module_record.RestrictRingTwice.At(fieldRing, A01, k))),
				"H⁰ is finite-dimensional",
				"and so is H¹")
			meetCharts := a.Have(
				"the meet of the charts is the chart of the meet",
				"«chart»(fst(X) ∩ snd(X)) = «chart»(fst(X)) ∩ «chart»(snd(X))",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					overK[1],
					overK[2],
					constant_field_extension.ConstantChartMeet.At(ops, K, k, l, first, second)))
			h0 := a.Have(
				"so H⁰ of the extended pair has the dimension of H⁰ of X",
				"module_dim(«scalars»(l), "+
					"    lattice_pair_h0(«vectors»(constant_composite(M, K, l)), «chartPair»)) = "+
					"module_dim(«scalars»(k), lattice_pair_h0(«vectors»(K), X))",
				Simp(Fwd(lattice_pair.RestrictedPairCohomology), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				meetCharts.RwRev(),
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					finiteParts[0],
					submodule.SubmoduleInter.At(kScalars, KVectors, first, second),
					overK[1],
					overK[2],
					constant_field_extension.ConstantChartDimension.At(ops, K, k, l, meet)))
			extendedAmbient := a.Have(
				"the ambient of the extended pair is the chart of the ambient",
				"lattice_pair_ambient(«scalars»(«chart»(A₀₁)), "+
					"    «vectors»(constant_composite(M, K, l)), "+
					"    «chartPair») = "+
					"«chart»(«pairAmbient»)",
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					rings,
					overK[1],
					submodule.SubmoduleSubset.At(kScalars, KVectors, first),
					constant_field_extension.ConstantChartOfSpan.At(ops, K, k, l, A01, first),
					lattice_pair.LatticePairAmbientDef.At(
						a.TermAs[RingOps[A]]("«scalars»(«chart»(A₀₁))"), compositeVectors, extended),
					lattice_pair.LatticePairAmbientDef.At(overlapRing, KVectors, X),
					pairs.Fst))
			extendedSum := a.Have(
				"and the chart of the sum is the sum of the charts",
				"«chart»(«pairSum») = set_mul(M.add, «chart»(fst(X)), «chart»(snd(X)))",
				By(
					M,
					kSubfield,
					lSubfield,
					inField,
					kInK,
					constant_field_extension.ConstantSubspaceSubmodule.At(ops, K, k, first),
					constant_field_extension.ConstantSubspaceSubmodule.At(ops, K, k, second),
					overK[1],
					overK[2],
					constant_field_extension.ConstantChartSum.At(ops, k, l, first, second)))
			h1 := a.Have(
				"so H¹ of the extended pair has the dimension of H¹ of X",
				"lattice_pair_h1_dim(«scalars»(«chart»(A₀₁)), "+
					"    l, "+
					"    «vectors»(constant_composite(M, K, l)), "+
					"    «chartPair») = "+
					"lattice_pair_h1_dim(«scalars»(A₀₁), k, «vectors»(K), X)",
				Simp(Fwd(lattice_pair.RestrictedPairCohomology), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				extendedAmbient.Rw(),
				extendedSum.RwRev(),
				By(
					M,
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					overK[3],
					overK[4],
					pair,
					lattice_pair.ChartSumInAmbient.At(overlapRing, A0, A1, KVectors, X),
					finiteParts[1],
					constant_field_extension.ConstantChartQuotient.At(ops, K, k, l, ambient, sum)))
			a.Show(
				"the two dimensions",
				By(h0, h1))
		}),
})}

// ConstantChartGenus — a constant extension keeps the genus: the genus is the
// dimension of H¹ of the structure pair, which is invertible, and the charts of
// the structure pair are the structure pair of the extended curve.
var ConstantChartGenus = constantChartGenusThm{family.Add(registry.ProofEntry{
	Name: "ConstantChartGenus",
	Key:  "prop_66872deccf08d39d",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "chart", Text: "λS:set(A). constant_chart(field_ring(M), l, S)"},
		},
		Binders: "∀M:field_on(A). ∀K k l A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"curve_over_line(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
		},
		Conclusion: "curve_genus(restrict_ring(field_ring(M), constant_composite(M, K, l)), " +
			"    l, " +
			"    «chart»(A₀), " +
			"    «chart»(A₁), " +
			"    «chart»(A₀₁)) = " +
			"curve_genus(«ambientRing», k, A₀, A₁, A₀₁)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			regular, curve, lSubfield, kInL, finiteExtension Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			functionField := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			inField := a.Have(
				"K is a subfield of M",
				"subfield(M, K)",
				By(a.Unfolded(regular, function_field.RegularFunctionFieldDef)))
			functionFieldOn := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			structurePair := a.Have(
				"the structure pair is invertible",
				"«ambientInvertible»((A₀, A₁))",
				By(
					Normalized,
					functionFieldOn,
					curve,
					algebraic_curve.CurveLatticeData.At(functionField, k, A0, A1, A01, t),
					field.RestrictFieldRing.At(ops, K)))
			a.Show(
				"the genus is the dimension of H¹ of the structure pair, kept by the extension",
				Simp(
					Fwd(algebraic_curve.CurveGenusDef),
					Fwd(module_record.RestrictRingTwice),
					Fwd(module_record.RegularModuleRestrict)),
				By(
					M,
					regular,
					curve,
					lSubfield,
					kInL,
					finiteExtension,
					structurePair,
					ConstantChartLatticeDimensions.At(
						ops, K, k, l, A0, A1, A01, t, a.TermAs[Prod[Set[A], Set[A]]]("(A₀, A₁)")),
					pairs.Fst,
					pairs.Snd))
		}),
})}
