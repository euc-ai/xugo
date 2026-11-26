package fixed_twist_models

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_splitting"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/constant_twist"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	"github.com/euc-ai/xugo/library/proofs/scheme/plane_model"
	"github.com/euc-ai/xugo/library/proofs/scheme/twisted_count"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// _fixedTwistChart is FixedTwistChartData read apart, one fact per clause.
type _fixedTwistChart struct {
	subfieldK, finiteK, regular, regularTwist, subfieldConstants, kInConstants, finiteConstants,
	subfieldComposite, LInComposite, constantsInComposite,
	constantsClosed, ringC, CInL, kInC, ringAway, awayInTwist, kInAway, charts, positiveOrder Fact
}

// readFixedTwistChart reads FixedTwistChartData apart at one twist.
func readFixedTwistChart(a *Argument, models, inGroup, data Fact) _fixedTwistChart {
	clauses := a.Conjuncts(
		GroupPremises(models, inGroup, data),
		"k is a subfield",
		"k is finite",
		"L is regular over k",
		"the twist field is regular over k",
		"the constants l are a subfield",
		"they hold k",
		"they are of finite degree over k",
		"the composite L·l is a subfield",
		"it holds L",
		"it holds l",
		"the q-th power keeps l",
		"C is a subring",
		"C lies in L",
		"C holds k",
		"the chart with a(t) inverted is a subring",
		"it lies in the twist field",
		"it holds k",
		"the two rings have one chart over l",
		"the order of s is positive")
	return _fixedTwistChart{
		clauses[0],
		clauses[1],
		clauses[2],
		clauses[3],
		clauses[4],
		clauses[5],
		clauses[6],
		clauses[7],
		clauses[8],
		clauses[9],
		clauses[10],
		clauses[11],
		clauses[12],
		clauses[13],
		clauses[14],
		clauses[15],
		clauses[16],
		clauses[17],
		clauses[18],
	}
}

// _fixedTwistModels is fixed_twist_models read apart, one fact per clause.
type _fixedTwistModels struct {
	good, twists Fact
}

// readFixedTwistModels reads fixed_twist_models apart through its definition:
// the good open the models live over, and the model of each twist field.
func readFixedTwistModels(a *Argument, models Fact) _fixedTwistModels {
	clauses := a.Conjuncts(
		a.Unfolded(models, FixedTwistModelsDef),
		"the models live over a good open",
		"each twist field has its model")
	return _fixedTwistModels{clauses[0], clauses[1]}
}

// FixedTwistChartData — where the rings of one twist of fixed models sit. L and
// the twist field are regular over k
// (constant_twist.CyclicConstantTwistDescent); the order e of s is positive, so
// l, the field of q^e constants, is a subfield of finite degree over k, kept by
// the q-th power and lying with L in their composite; C is a subring of L
// holding k; the affine chart of the model is a subring of the twist field
// holding k and a(t), so inverting a(t) in it gives a subring D of the twist
// field holding k (ring_away.RingAwayInSubfield); and the model's own
// clause says D and C have one chart over l.
var FixedTwistChartData = fixedTwistChartDataThm{family.Add(registry.ProofEntry{
	Name: "FixedTwistChartData",
	Key:  "prop_d2e86e1300ec46e9",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀z:(permutation(A) → A). " +
			"∀F:(permutation(A) → num → A). " +
			"∀b:(permutation(A) → num). " +
			"∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"fixed_twist_models(M, k, L, t, C, a, z, F, b)",
			"s ∈ field_automorphisms(M, «base», L)",
		},
		Conclusion: "subfield(M, k) ∧ " +
			"finite(k) ∧ " +
			"regular_function_field(M, k, L) ∧ " +
			"regular_function_field(M, k, «field») ∧ " +
			"subfield(M, «constants») ∧ " +
			"k ⊆ «constants» ∧ " +
			"finite_extension(M, k, «constants») ∧ " +
			"subfield(M, «composite») ∧ " +
			"L ⊆ «composite» ∧ " +
			"«constants» ⊆ «composite» ∧ " +
			"(∀c:A. c ∈ «constants» ⇒ monoid_pow(M.mul, M.one, c, card(k)) ∈ «constants») ∧ " +
			"subring(field_ring(M), C) ∧ " +
			"C ⊆ L ∧ " +
			"k ⊆ C ∧ " +
			"subring(field_ring(M), «away») ∧ " +
			"«away» ⊆ «field» ∧ " +
			"k ⊆ «away» ∧ " +
			"constant_chart(field_ring(M), «constants», «away») = " +
			"constant_chart(field_ring(M), «constants», C) ∧ " +
			"0 < permutation_order(s)",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
			{Name: "field", Text: "constant_twist_field(M, k, L, s)"},
			{Name: "affine", Text: "plane_chart_zero(restrict_ring(field_ring(M), «field»), k, t, z(s))"},
			{Name: "secondChart", Text: "plane_chart_one(restrict_field(M, «field»), k, t, z(s), b(s))"},
			{Name: "overlap", Text: "ring_away(restrict_ring(field_ring(M), «field»), «affine», t)"},
			{Name: "polynomialsInTwist", Text: "polynomial_image(field_ring(restrict_field(M, «field»)), " +
				"    k, " +
				"    t)"},
			{Name: "away", Text: "ring_away(field_ring(M), «affine», polynomial_eval(a, t))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		z *Arrow[Permutation[A], A],
		F *Arrow2[Permutation[A], Nat, A],
		b *Arrow[Permutation[A], Nat],
		s *Expr[Permutation[A]],
		closed, models, inGroup Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		twist := arg.TermAs[Set[A]]("«field»")
		affine := arg.TermAs[Set[A]]("«affine»")
		secondChart := arg.TermAs[Set[A]]("«secondChart»")
		overlap := arg.TermAs[Set[A]]("«overlap»")
		onTwist := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «field»)")
		value := arg.TermAs[A]("polynomial_eval(a, t)")
		base := arg.TermAs[Set[A]]("«base»")
		order := arg.TermAs[Nat]("permutation_order(s)")
		opened := readFixedTwistModels(arg, models)
		good, twists := opened.good, opened.twists
		regular, finiteK :=
			galois_good_open.GoodOpenRegular.Read(good), galois_good_open.GoodOpenConstantsFinite.Read(good)
		regularTwist := arg.Have(
			"the twist field is regular over k by descent",
			"regular_function_field(M, k, «field»)",
			By(
				closed,
				regular,
				finiteK,
				galois_good_open.GoodOpenParameterIn.Read(good),
				galois_good_open.GoodOpenParameterTranscendental.Read(good),
				galois_good_open.GoodOpenGalois.Read(good),
				inGroup,
				constant_twist.CyclicConstantTwistDescent.Read(M).At(k, L, t, s)))
		subfieldTwist := arg.Have(
			"so it is a subfield",
			"subfield(M, «field»)",
			By(regularTwist, function_field.RegularFunctionFieldDef.At(fieldM, k, twist)))
		twistField := arg.Have(
			"a field under the operations of M",
			"field_on(restrict_field(M, «field»))",
			By(subfieldTwist, field.SubfieldFieldOn.Read(M).At(twist)))
		modelData := arg.Conjuncts(
			GroupPremises(inGroup, twists.At(s)),
			"the twist field has its integral plane model",
			"C and D have one chart over l")
		curve := arg.Have(
			"the model's two charts make a curve over the line",
			"curve_over_line(restrict_field(M, «field»), k, t, «affine», «secondChart», «overlap»)",
			By(
				subfieldTwist,
				modelData[0],
				plane_model.PlaneEquationBiaffineCurve.Read(M).At(
					twist, k, t, arg.TermAs[A]("z(s)"), arg.TermAs[Fun[Nat, A]]("F(s)"), arg.TermAs[Nat]("b(s)"))))
		affineData := arg.Conjuncts(
			arg.Have(
				"so the affine chart is a subring of the twist field holding k[t], which holds k",
				"subring(field_ring(restrict_field(M, «field»)), «affine») ∧ "+
					"k ⊆ «polynomialsInTwist» ∧ "+
					"«polynomialsInTwist» ⊆ «affine»",
				By(
					curve,
					algebraic_curve.CurveOverItsLine.Read(twistField).At(k, affine, secondChart, overlap, t))),
			"the affine chart is a subring of the twist field",
			"k lies in k[t]",
			"k[t] lies in the affine chart")
		subringInTwist, kInPolynomials, polynomialsInAffine := affineData[0], affineData[1], affineData[2]
		subringInRestriction := arg.Have(
			"read inside the ring on the twist field",
			"subring(restrict_ring(field_ring(M), «field»), «affine»)",
			By(subringInTwist, field.RestrictFieldRing.At(fieldM, twist)))
		affineInTwist := arg.Have(
			"the affine chart lies in the twist field",
			"«affine» ⊆ «field»",
			By(comm_ring.SubringSubset.Read(subringInRestriction)))
		affineInCarrier := arg.Have(
			"and in M",
			"«affine» ⊆ M.carrier",
			BySets(affineInTwist, subfieldTwist, field.SubfieldSubset.At(fieldM, twist)))
		subringAffine := arg.Have(
			"so the affine chart is a subring of M",
			"subring(field_ring(M), «affine»)",
			By(
				affineInCarrier,
				subringInRestriction,
				comm_ring.SubringDef.At(R, affine),
				comm_ring.SubringDef.At(onTwist, affine)))
		inPolynomials := arg.Have(
			"a(t) is the value of a polynomial over k",
			"polynomial_eval(a, t) ∈ polynomial_image(field_ring(M), k, t)",
			BySets(
				galois_good_open.GoodOpenDenominatorOver.Read(good),
				algebraic_element.PolynomialImageDef.At(R, k, t)))
		valueInAffine := arg.Have(
			"so it lies in the affine chart",
			"polynomial_eval(a, t) ∈ «affine»",
			BySets(
				inPolynomials,
				polynomialsInAffine,
				algebraic_element.PolynomialsOverRestriction.At(fieldM, twist, k, t)))
		away := arg.Conjuncts(
			arg.Have(
				"inverting a(t) in the affine chart gives a subring D of the twist field holding it",
				"subring(field_ring(M), «away») ∧ «affine» ⊆ «away» ∧ «away» ⊆ «field»",
				By(
					subringAffine,
					subfieldTwist,
					affineInTwist,
					valueInAffine,
					galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
					ring_away.RingAwayInSubfield.Read(M).At(affine, twist, value))),
			"D is a subring",
			"it holds the affine chart",
			"it lies in the twist field")
		kInAway := arg.Have(
			"it holds k",
			"k ⊆ «away»",
			BySets(kInPolynomials, polynomialsInAffine, away[1]))
		positive := arg.Have(
			"the order of s is positive",
			"0 < permutation_order(s)",
			By(
				good,
				galois_good_open.GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
				galois_good_open.GoodOpenFieldSubfield.Read(good),
				galois_good_open.GoodOpenRationalInField.Read(good),
				galois_good_open.GoodOpenFiniteExtension.Read(good),
				inGroup,
				field_automorphism.AutomorphismOrderFacts.Read(M).At(base, L, s)))
		constants := arg.Conjuncts(
			arg.Have(
				"l is a subfield of finite degree over k, which it holds, and sits with L inside their composite",
				"subfield(M, «constants») ∧ "+
					"k ⊆ «constants» ∧ "+
					"finite_extension(M, k, «constants») ∧ "+
					"subfield(M, «composite») ∧ "+
					"L ⊆ «composite» ∧ "+
					"«constants» ⊆ «composite»",
				By(
					M,
					closed,
					regular,
					finiteK,
					positive,
					constant_galois.ConstantCompositeData.Read(M).At(L, k, order))),
			"l is a subfield",
			"l holds k",
			"l is of finite degree over k",
			"the composite is a subfield",
			"it holds L",
			"it holds l")
		ringOnConstants := arg.Have(
			"l is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), «constants»))",
			By(constants[0], field.SubfieldCommRing.Read(M).At(arg.TermAs[Set[A]]("«constants»"))))
		closedUnderPower := arg.Have(
			"so it holds the powers of its members",
			"∀c:A. c ∈ «constants» ⇒ monoid_pow(M.mul, M.one, c, card(k)) ∈ «constants»",
			By(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringOnConstants))))
		arg.Show(
			"these are the clauses",
			By(
				galois_good_open.GoodOpenConstantsSubfield.Read(good),
				finiteK,
				regular,
				regularTwist,
				constants[0],
				constants[1],
				constants[2],
				constants[3],
				constants[4],
				constants[5],
				closedUnderPower,
				good,
				galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, C, t, a),
				galois_good_open.GoodOpenChartInField.Read(good),
				galois_good_open.GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a),
				away[0],
				away[2],
				kInAway,
				modelData[1],
				positive))
	}),
})}

// FixedTwistActsOnChart — the twist φ is a ring endomorphism of the common chart
// B of C and D over l, and it is the q-th power on l, s on C, which s keeps, and
// the identity on D, inside the twist field. As an automorphism of the composite
// L·l it is a ring map on B, which lies in the composite; and where φ sends B
// into B is a subring of B holding l and C, so it is all of B
// (constant_splitting.ConstantChartGenerated).
var FixedTwistActsOnChart = fixedTwistActsOnChartThm{family.Add(registry.ProofEntry{
	Name: "FixedTwistActsOnChart",
	Key:  "prop_5fdc27c74f18e890",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀z:(permutation(A) → A). " +
			"∀F:(permutation(A) → num → A). " +
			"∀b:(permutation(A) → num). " +
			"∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"fixed_twist_models(M, k, L, t, C, a, z, F, b)",
			"s ∈ field_automorphisms(M, «base», L)",
		},
		Conclusion: "ring_homomorphism(«onChart», «onChart», permutation_map(«twist»)) ∧ " +
			"(∀c:A. c ∈ «constants» ⇒ permutation_map(«twist», c) = monoid_pow(M.mul, M.one, c, card(k))) ∧ " +
			"(∀x:A. " +
			"    x ∈ C ⇒ permutation_map(«twist», x) = permutation_map(s, x) ∧ permutation_map(s, x) ∈ C) ∧ " +
			"(∀y:A. y ∈ «away» ⇒ permutation_map(«twist», y) = y)",
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
			{Name: "onComposite", Text: "restrict_ring(field_ring(M), «composite»)"},
			{Name: "twist", Text: "constant_twist_automorphism(M, k, L, s)"},
			{Name: "away", Text: "ring_away(field_ring(M), " +
				"    plane_chart_zero(restrict_ring(field_ring(M), constant_twist_field(M, k, L, s)), " +
				"        k, " +
				"        t, " +
				"        z(s)), " +
				"    polynomial_eval(a, t))"},
			{Name: "chart", Text: "constant_chart(field_ring(M), «constants», C)"},
			{Name: "onChart", Text: "restrict_ring(field_ring(M), «chart»)"},
			{Name: "keptByTwist", Text: "preimage_on(«chart», permutation_map(«twist»), «chart»)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		z *Arrow[Permutation[A], A],
		F *Arrow2[Permutation[A], Nat, A],
		b *Arrow[Permutation[A], Nat],
		s *Expr[Permutation[A]],
		closed, models, inGroup Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		base := arg.TermAs[Set[A]]("«base»")
		constants := arg.TermAs[Set[A]]("«constants»")
		composite := arg.TermAs[Set[A]]("«composite»")
		onComposite := arg.TermAs[module_record.RingOps[A]]("«onComposite»")
		chart := arg.TermAs[Set[A]]("«chart»")
		onChart := arg.TermAs[module_record.RingOps[A]]("«onChart»")
		twist := arg.TermAs[Permutation[A]]("«twist»")
		twistMap := arg.TermAs[Fun[A, A]]("permutation_map(«twist»)")
		data := readFixedTwistChart(
			arg, models, inGroup, FixedTwistChartData.Read(M).At(k, L, t, C, a, z, F, b, s))
		good := readFixedTwistModels(arg, models).good
		acts := arg.Conjuncts(
			GroupPremises(
				closed,
				data.regular,
				data.finiteK,
				galois_good_open.GoodOpenParameterIn.Read(good),
				galois_good_open.GoodOpenParameterTranscendental.Read(good),
				galois_good_open.GoodOpenGalois.Read(good),
				inGroup,
				constant_twist.ConstantTwistActs.Read(M).At(k, L, t, s)),
			"the Frobenius lift is an automorphism over L",
			"it is the q-th power on l",
			"the lift of s is an automorphism over l",
			"it is s on L",
			"the twist is an automorphism of the composite over k(t)",
			"it is s on L",
			"it is the q-th power on l",
			"it fixes the twist field")
		automorphism, onL, onConstants, onTwistField := acts[4], acts[5], acts[6], acts[7]
		image := arg.Have(
			"s carries C onto itself",
			"image(permutation_map(s), C) = C",
			By(inGroup, galois_good_open.GoodOpenAutomorphismsKeepChart.Read(good).At(s)))
		keeps := arg.Have(
			"so s keeps C",
			"∀x:A. x ∈ C ⇒ permutation_map(s, x) ∈ C",
			BySets(image))
		ringMap := arg.Have(
			"the twist is a ring map on the composite",
			"ring_homomorphism(«onComposite», «onComposite», permutation_map(«twist»))",
			By(
				M,
				data.subfieldComposite,
				automorphism,
				field.RestrictFieldRing.At(fieldM, composite),
				field_automorphism.AutomorphismRingHomomorphism.Read(M).At(base, composite, twist)))
		intoM := arg.Have(
			"with values in M",
			"ring_homomorphism(«onComposite», field_ring(M), permutation_map(«twist»))",
			By(
				ringMap,
				data.subfieldComposite,
				field.RingOn.Read(M),
				field.SubfieldSubset.At(fieldM, composite),
				ring_homomorphism.RingHomExtendTarget.At(onComposite, R, twistMap, composite)))
		chartData := arg.Conjuncts(
			arg.Have(
				"the chart is a subring holding l and C",
				"subring(field_ring(M), «chart») ∧ «constants» ⊆ «chart» ∧ C ⊆ «chart»",
				By(
					data.regular,
					data.subfieldConstants,
					data.kInConstants,
					data.finiteConstants,
					data.ringC,
					data.CInL,
					data.kInC,
					constant_field_extension.ConstantChartRing.Read(M).At(L, k, constants, C))),
			"the chart is a subring of M",
			"it holds l",
			"it holds C")
		subringChart, constantsInChart, CInChart := chartData[0], chartData[1], chartData[2]
		overConstants := arg.Have(
			"the composite is a submodule over l",
			"submodule(restrict_ring(field_ring(M), «constants»), regular_module(field_ring(M)), «composite»)",
			By(
				data.subfieldComposite,
				field.SubfieldSubring.Read(M),
				data.constantsInComposite,
				principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(constants, composite)))
		CInComposite := arg.Have(
			"holding C, which lies in L",
			"C ⊆ «composite»",
			BySets(data.CInL, data.LInComposite))
		chartInComposite := arg.Have(
			"so it holds the chart",
			"«chart» ⊆ «composite»",
			By(
				overConstants,
				CInComposite,
				constant_field_extension.ConstantChartLeast.At(R, constants, C, composite)))
		subringInComposite := arg.Have(
			"which is a subring of the composite",
			"subring(«onComposite», «chart»)",
			By(
				subringChart,
				chartInComposite,
				comm_ring.SubringDef.At(onComposite, chart),
				comm_ring.SubringDef.At(R, chart)))
		onChartMap := arg.Have(
			"so the twist is a ring map on the chart",
			"ring_homomorphism(«onChart», field_ring(M), permutation_map(«twist»))",
			By(
				intoM,
				subringInComposite,
				module_record.RestrictRingTwice.At(R, composite, chart),
				ring_homomorphism.RingHomRestrictSource.At(onComposite, R, twistMap, chart)))
		preimage := arg.Have(
			"the part of the chart it keeps is a subring",
			"subring(«onChart», «keptByTwist»)",
			By(
				onChartMap,
				subringChart,
				ring_homomorphism.RingMapPreimageSubring.At(onChart, R, twistMap, chart)))
		holdsConstants := arg.Have(
			"which holds l, the q-th power keeping l",
			"«constants» ⊆ «keptByTwist»",
			BySets(constantsInChart, onConstants, data.constantsClosed))
		holdsC := arg.Have(
			"and C, where the twist is s",
			"C ⊆ «keptByTwist»",
			BySets(CInChart, data.CInL, onL, keeps))
		cover := arg.Have(
			"so it is the whole chart",
			"«chart» ⊆ «keptByTwist»",
			By(
				data.regular,
				data.subfieldConstants,
				data.kInConstants,
				data.finiteConstants,
				data.ringC,
				data.CInL,
				data.kInC,
				preimage,
				holdsConstants,
				holdsC,
				constant_splitting.ConstantChartGenerated.Read(M).At(
					L, k, constants, C, arg.TermAs[Set[A]]("«keptByTwist»"))))
		into := arg.Have(
			"the twist keeps the chart",
			"∀y:A. y ∈ «chart» ⇒ permutation_map(«twist», y) ∈ «chart»",
			BySets(cover))
		endomorphism := arg.Have(
			"so it is a ring endomorphism of the chart",
			"ring_homomorphism(«onChart», «onChart», permutation_map(«twist»))",
			By(
				onChartMap,
				subringChart,
				into,
				ring_homomorphism.RingHomCorestrict.At(onChart, R, twistMap, chart)))
		onC := arg.Have(
			"on C the twist is s, which keeps C",
			"∀x:A. x ∈ C ⇒ permutation_map(«twist», x) = permutation_map(s, x) ∧ permutation_map(s, x) ∈ C",
			BySets(data.CInL, onL, keeps))
		onAway := arg.Have(
			"and the chart with a(t) inverted lies in the twist field, which it fixes",
			"∀y:A. y ∈ «away» ⇒ permutation_map(«twist», y) = y",
			BySets(data.awayInTwist, onTwistField))
		arg.Show(
			"these are the four clauses",
			By(endomorphism, onConstants, onC, onAway))
	}),
})}

// TwistEquationSpreads — let B be the common chart over l, and S a ring between
// k and a function field with the same chart. For a point ψ of B, the equation
// ψ(y)^Q = ψ(φ y), Q = |k|^m, spreads from S to B: y ↦ ψ(y)^Q and y ↦ ψ(φ y)
// are ring maps on B (twisted_count.PointFrobenius, FixedTwistActsOnChart),
// they agree on S by assumption and on l, where e ∣ m - 1 makes the Q-th power
// the q-th power (finite_field.FiniteConstantsShiftedPower), so they agree on B
// (constant_splitting.ConstantChartMapsAgree).
var TwistEquationSpreads = twistEquationSpreadsThm{family.Add(registry.ProofEntry{
	Name: "TwistEquationSpreads",
	Key:  "prop_59ba1a71e532c348",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀z:(permutation(A) → A). " +
			"∀F:(permutation(A) → num → A). " +
			"∀b:(permutation(A) → num). " +
			"∀s:permutation(A). " +
			"∀m:num. " +
			"∀K S:set(A). " +
			"∀ψ:(A → A). " +
			"∀y:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"fixed_twist_models(M, k, L, t, C, a, z, F, b)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
			"0 < m",
			"permutation_order(s) ∣ m - 1",
			"regular_function_field(M, k, K)",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"k ⊆ S",
			"«chartOfS» = «chart»",
			"ψ ∈ «points»",
			"∀x:A. x ∈ S ⇒ «power»(x) = ψ(permutation_map(«twist», x))",
			"y ∈ «chart»",
		},
		Conclusion: "«power»(y) = ψ(permutation_map(«twist», y))",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "twist", Text: "constant_twist_automorphism(M, k, L, s)"},
			{Name: "chart", Text: "constant_chart(field_ring(M), «constants», C)"},
			{Name: "chartOfS", Text: "constant_chart(field_ring(M), «constants», S)"},
			{Name: "onChart", Text: "restrict_ring(field_ring(M), «chart»)"},
			{Name: "onChartOfS", Text: "restrict_ring(field_ring(M), «chartOfS»)"},
			{Name: "points", Text: "algebra_points(«onChart», field_ring(M), «constants», λx:A. x)"},
			{Name: "power", Text: "λv:A. monoid_pow(M.mul, M.one, ψ(v), card(k) ^ m)"},
			{Name: "twisted", Text: "λv:A. ψ(permutation_map(«twist», v))"},
			{Name: "whole", Text: "restrict_ring(field_ring(M), M.carrier)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		z *Arrow[Permutation[A], A],
		F *Arrow2[Permutation[A], Nat, A],
		b *Arrow[Permutation[A], Nat],
		s *Expr[Permutation[A]],
		m *Expr[Nat],
		K, S *Expr[Set[A]],
		ψ *Arrow[A, A],
		y *Expr[A],
		closed, models, inGroup, positive, divides, regularK, subringS, SInK, kInS, charts, point, onS, yIn Fact,
	) {
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		constants := arg.TermAs[Set[A]]("«constants»")
		onChart := arg.TermAs[module_record.RingOps[A]]("«onChart»")
		carrier := arg.TermAs[Set[A]]("M.carrier")
		identity := arg.TermAs[Fun[A, A]]("λx:A. x")
		twistMap := arg.TermAs[Fun[A, A]]("permutation_map(«twist»)")
		power := arg.TermAs[Fun[A, A]]("«power»")
		twisted := arg.TermAs[Fun[A, A]]("«twisted»")
		size := arg.TermAs[Nat]("card(k)")
		order := arg.TermAs[Nat]("permutation_order(s)")
		data := readFixedTwistChart(
			arg, models, inGroup, FixedTwistChartData.Read(M).At(k, L, t, C, a, z, F, b, s))
		acts := arg.Conjuncts(
			GroupPremises(closed, models, inGroup, FixedTwistActsOnChart.Read(M).At(k, L, t, C, a, z, F, b, s)),
			"the twist is a ring endomorphism of the chart",
			"it is the q-th power on l",
			"it is s on C",
			"it fixes the chart with a(t) inverted")
		pointData := arg.Conjuncts(
			arg.Have(
				"ψ is a ring map fixing l and vanishing off the chart",
				"ring_homomorphism(«onChart», field_ring(M), ψ) ∧ "+
					"(∀x:A. x ∈ «constants» ⇒ ψ(x) = x) ∧ "+
					"(∀x:A. x ∉ «chart» ⇒ ψ(x) = M.zero)",
				By(point, algebra_points.AlgebraPointsMember.At(onChart, R, constants, identity, ψ))),
			"ψ is a ring map",
			"it fixes l",
			"it vanishes off the chart")
		hom, fixes, off := pointData[0], pointData[1], pointData[2]
		twistedMap := arg.Have(
			"y ↦ ψ(φ y) is a ring map on the chart",
			"ring_homomorphism(«onChart», field_ring(M), «twisted»)",
			By(acts[0], hom, ring_homomorphism.RingHomCompose.At(onChart, onChart, R, twistMap, ψ)))
		fixesK := arg.Have(
			"ψ fixes k, which lies in l",
			"∀x:A. x ∈ k ⇒ ψ(x) = x",
			BySets(data.kInConstants, fixes))
		whole := arg.Have(
			"M is M restricted to its own carrier",
			"«whole» = field_ring(M)",
			By(module_record.RestrictRingCarrier.At(R)))
		overM := arg.Have(
			"so ψ is a point over k in M",
			"ψ ∈ algebra_points(«onChart», field_ring(M), k, λx:A. x)",
			By(hom, fixesK, off, algebra_points.AlgebraPointsMember.At(onChart, R, k, identity, ψ)))
		overK := arg.Have(
			"read in that ring",
			"ψ ∈ algebra_points(«onChart», «whole», k, λx:A. x)",
			By(whole, overM))
		carrierInside := arg.Have(
			"the values are taken in M itself, a set inside M",
			"M.carrier ⊆ M.carrier",
			BySets())
		powerPoint := arg.Have(
			"so is its Q-th power",
			"«power» ∈ algebra_points(«onChart», «whole», k, λx:A. x)",
			By(
				closed,
				data.subfieldK,
				data.finiteK,
				positive,
				carrierInside,
				overK,
				twisted_count.PointFrobenius.Read(M).At(k, carrier, m, onChart, ψ)))
		powerMap := arg.Have(
			"y ↦ ψ(y)^Q is a ring map on the chart",
			"ring_homomorphism(«onChart», field_ring(M), «power»)",
			By(whole, powerPoint, algebra_points.AlgebraPointsMember.At(onChart, R, k, identity, power)))
		agreeOnConstants := arg.Have(
			"the two maps agree on l",
			"∀c:A. c ∈ «constants» ⇒ «power»(c) = ψ(permutation_map(«twist», c))",
			Derive(func(d *Argument) {
				c := d.FixAs[A]("c")
				in := d.Assume()
				qth := d.TermAs[A]("monoid_pow(M.mul, M.one, c, card(k))")
				shifted := d.Have(
					"on l the Q-th power is the q-th power",
					"monoid_pow(M.mul, M.one, c, card(k) ^ m) = monoid_pow(M.mul, M.one, c, card(k))",
					By(
						field.RingOn.Read(M),
						positive,
						divides,
						in,
						finite_field.FiniteConstantsShiftedPower.At(R, size, order, m, c)))
				d.Show(
					"ψ fixes c, and it fixes c^q, which is φ c and lies in l",
					By(shifted, in, fixes.At(c), acts[1].At(c), data.constantsClosed.At(c), fixes.At(qth)))
			}))
		powerOnS := arg.Have(
			"read on the chart of S, y ↦ ψ(y)^Q is a ring map",
			"ring_homomorphism(«onChartOfS», field_ring(M), «power»)",
			By(charts, powerMap))
		twistedOnS := arg.Have(
			"and so is y ↦ ψ(φ y)",
			"ring_homomorphism(«onChartOfS», field_ring(M), «twisted»)",
			By(charts, twistedMap))
		yInS := arg.Have(
			"and y lies in it",
			"y ∈ «chartOfS»",
			By(charts, yIn))
		arg.Show(
			"the two maps agree on the chart",
			By(
				regularK,
				data.subfieldConstants,
				data.kInConstants,
				data.finiteConstants,
				subringS,
				SInK,
				kInS,
				powerOnS,
				twistedOnS,
				agreeOnConstants,
				onS,
				yInS,
				constant_splitting.ConstantChartMapsAgree.Read(M).At(K, k, constants, S, R, power, twisted, y)))
	}),
})}

// FixedTwistPointsOfAway — restriction to D is a bijection of W, the points ψ of
// the common chart B with ψ(y)^Q = ψ(φ y), onto the points of D with values in
// F_Q. It is a bijection of all the points of B onto the points of D in M
// (constant_splitting.ConstantPointsInField), and φ fixes D, so on D the equation says
// that ψ takes its values in F_Q; it spreads from D to B (TwistEquationSpreads).
var FixedTwistPointsOfAway = fixedTwistPointsOfAwayThm{family.Add(registry.ProofEntry{
	Name: "FixedTwistPointsOfAway",
	Key:  "prop_d6d49b0b8b21e68a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀z:(permutation(A) → A). " +
			"∀F:(permutation(A) → num → A). " +
			"∀b:(permutation(A) → num). " +
			"∀s:permutation(A). " +
			"∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"fixed_twist_models(M, k, L, t, C, a, z, F, b)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
			"0 < m",
			"permutation_order(s) ∣ m - 1",
		},
		Conclusion: "injective_on(«fixed», «restriction») ∧ " +
			"image(«restriction», «fixed») = «rationalPoints»",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "twist", Text: "constant_twist_automorphism(M, k, L, s)"},
			{Name: "field", Text: "constant_twist_field(M, k, L, s)"},
			{Name: "away", Text: "ring_away(field_ring(M), " +
				"    plane_chart_zero(restrict_ring(field_ring(M), «field»), k, t, z(s)), " +
				"    polynomial_eval(a, t))"},
			{Name: "chart", Text: "constant_chart(field_ring(M), «constants», C)"},
			{Name: "onChart", Text: "restrict_ring(field_ring(M), «chart»)"},
			{Name: "points", Text: "algebra_points(«onChart», field_ring(M), «constants», λx:A. x)"},
			{Name: "fixed", Text: "{ψ:A → A | " +
				"    ψ ∈ «points» ∧ " +
				"    (∀y:A. " +
				"        y ∈ «chart» ⇒ " +
				"        monoid_pow(M.mul, M.one, ψ(y), card(k) ^ m) = ψ(permutation_map(«twist», y)))}"},
			{Name: "restriction", Text: "λψ:A → A. λx:A. COND(x ∈ «away», ψ(x), M.zero)"},
			{Name: "onAway", Text: "restrict_ring(field_ring(M), «away»)"},
			{Name: "rational", Text: "finite_constants(field_ring(M), card(k), m)"},
			{Name: "pointsInM", Text: "algebra_points(«onAway», field_ring(M), k, λx:A. x)"},
			{Name: "rationalPoints", Text: "algebra_points(«onAway», " +
				"    restrict_ring(field_ring(M), «rational»), " +
				"    k, " +
				"    λx:A. x)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		z *Arrow[Permutation[A], A],
		F *Arrow2[Permutation[A], Nat, A],
		b *Arrow[Permutation[A], Nat],
		s *Expr[Permutation[A]],
		m *Expr[Nat],
		closed, models, inGroup, positive, divides Fact,
	) {
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		twistField := arg.TermAs[Set[A]]("«field»")
		constants := arg.TermAs[Set[A]]("«constants»")
		away := arg.TermAs[Set[A]]("«away»")
		onChart := arg.TermAs[module_record.RingOps[A]]("«onChart»")
		onAway := arg.TermAs[module_record.RingOps[A]]("«onAway»")
		rational := arg.TermAs[Set[A]]("«rational»")
		points := arg.TermAs[Set[Fun[A, A]]]("«points»")
		fixed := arg.TermAs[Set[Fun[A, A]]]("«fixed»")
		pointsInM := arg.TermAs[Set[Fun[A, A]]]("«pointsInM»")
		rationalPoints := arg.TermAs[Set[Fun[A, A]]]("«rationalPoints»")
		restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		identity := arg.TermAs[Fun[A, A]]("λx:A. x")
		size := arg.TermAs[Nat]("card(k)")
		data := readFixedTwistChart(
			arg, models, inGroup, FixedTwistChartData.Read(M).At(k, L, t, C, a, z, F, b, s))
		acts := arg.Conjuncts(
			GroupPremises(closed, models, inGroup, FixedTwistActsOnChart.Read(M).At(k, L, t, C, a, z, F, b, s)),
			"the twist is a ring endomorphism of the chart",
			"it is the q-th power on l",
			"it is s on C",
			"it fixes D")
		subfieldRational := arg.Have(
			"F_Q is a subfield of M",
			"subfield(M, «rational»)",
			By(
				closed,
				data.subfieldK,
				data.finiteK,
				positive,
				finite_field.FiniteConstantsSubfield.Read(M).At(k, m)))
		subringRational := arg.Have(
			"so a subring",
			"subring(field_ring(M), «rational»)",
			By(subfieldRational, field.SubfieldSubring.Read(M)))
		awayIsChart := arg.Have(
			"D lies in the chart of D",
			"«away» ⊆ constant_chart(field_ring(M), «constants», «away»)",
			By(
				data.regularTwist,
				data.subfieldConstants,
				data.kInConstants,
				data.finiteConstants,
				data.ringAway,
				data.awayInTwist,
				data.kInAway,
				constant_field_extension.ConstantChartRing.Read(M).At(twistField, k, constants, away)))
		awayInChart := arg.Have(
			"which is the common chart",
			"«away» ⊆ «chart»",
			By(data.charts, awayIsChart))
		bijection := arg.Conjuncts(
			arg.Have(
				"restriction is a bijection of the points of that chart onto the points of D in M",
				"injective_on(«points», «restriction») ∧ image(«restriction», «points») = «pointsInM»",
				By(
					M,
					data.charts,
					data.regularTwist,
					data.subfieldConstants,
					data.kInConstants,
					data.finiteConstants,
					data.ringAway,
					data.kInAway,
					data.awayInTwist,
					constant_splitting.ConstantPointsInField.Read(M).At(twistField, k, constants, away))),
			"restriction is one-to-one on the points",
			"their restrictions are the points of D in M")
		retarget := arg.Have(
			"a point of D in F_Q is a point of D in M with values in F_Q",
			"∀e:(A → A). e ∈ «rationalPoints» ⇔ e ∈ «pointsInM» ∧ (∀x:A. x ∈ «away» ⇒ e(x) ∈ «rational»)",
			arg.ForEach(func(e *Expr[Fun[A, A]]) Action {
				return By(
					subringRational,
					field.RingOn.Read(M),
					algebra_points.AlgebraPointsInSubring.At(R, onAway, k, identity, e, rational))
			}))
		fixedInPoints := arg.Have(
			"W lies among the points of the chart",
			"«fixed» ⊆ «points»",
			BySets())
		rationalInM := arg.Have(
			"and the points in F_Q among those in M",
			"«rationalPoints» ⊆ «pointsInM»",
			BySets(retarget))
		inside := arg.Have(
			"the restrictions lie among the points of D in M",
			"image(«restriction», «points») ⊆ «pointsInM»",
			BySets(bijection[1]))
		restrictions := arg.Have(
			"each of them",
			"∀ψ:(A → A). ψ ∈ «points» ⇒ «restriction»(ψ) ∈ «pointsInM»",
			By(inside, set_image.ImageSubsetIff.At(restriction, points, pointsInM)))
		matches := arg.Have(
			"a point lies in W exactly as its restriction has values in F_Q",
			"∀ψ:(A → A). ψ ∈ «points» ⇒ (ψ ∈ «fixed» ⇔ «restriction»(ψ) ∈ «rationalPoints»)",
			Derive(func(d *Argument) {
				ψ := d.FixAs[Fun[A, A]]("ψ")
				point := d.Assume()
				restricted := d.TermAs[Fun[A, A]]("«restriction»(ψ)")
				hom := d.Have(
					"ψ is a ring map on the chart",
					"ring_homomorphism(«onChart», field_ring(M), ψ)",
					By(point, algebra_points.AlgebraPointsMember.At(onChart, R, constants, identity, ψ)))
				below := d.Have(
					"its restriction is a point of D in M",
					"«restriction»(ψ) ∈ «pointsInM»",
					By(point, restrictions.At(ψ)))
				onValues := d.Have(
					"on D the equation says ψ has values in F_Q, as φ fixes D",
					Statement{
						Binders:    "∀x:A.",
						Hypotheses: []string{"x ∈ «away»"},
						Conclusion: "ψ(x) ∈ «rational» ⇔ " +
							"monoid_pow(M.mul, M.one, ψ(x), card(k) ^ m) = ψ(permutation_map(«twist», x))",
					},
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						inAway := e.Assume()
						inChart := e.Have(
							"x lies in the chart",
							"x ∈ «chart»",
							BySets(inAway, awayInChart))
						value := e.Have(
							"so ψ(x) lies in M",
							"ψ(x) ∈ M.carrier",
							By(inChart, ring_homomorphism.MapIn.Read(hom)))
						e.Show(
							"F_Q is the points of M the Q-th power fixes, and φ x = x",
							BySets(value, acts[3].At(x), inAway, finite_field.FiniteConstantsDef.At(R, size, m)))
					}))
				d.Iff()
				d.Forward(
					"a point of W has values in F_Q on D",
					func(e *Argument, inFixed Fact) {
						equation := e.Have(
							"ψ satisfies the equation on the chart",
							"∀y:A. y ∈ «chart» ⇒ monoid_pow(M.mul, M.one, ψ(y), card(k) ^ m) = ψ(permutation_map(«twist», y))",
							BySets(inFixed))
						values := e.Have(
							"so its restriction has values in F_Q",
							"∀x:A. x ∈ «away» ⇒ «restriction»(ψ, x) ∈ «rational»",
							Derive(func(f *Argument) {
								x := f.FixAs[A]("x")
								inAway := f.Assume()
								inChart := f.Have(
									"x lies in the chart",
									"x ∈ «chart»",
									BySets(inAway, awayInChart))
								f.Show(
									"the equation at x",
									By(inAway, onValues.At(x), equation.At(x), inChart))
							}))
						e.Show(
							"so it is a point of D in F_Q",
							By(below, values, retarget.At(restricted)))
					})
				d.Backward(
					"a point with values in F_Q on D satisfies the equation on the chart",
					func(e *Argument, inRational Fact) {
						values := e.Have(
							"its restriction has values in F_Q",
							"∀x:A. x ∈ «away» ⇒ «restriction»(ψ, x) ∈ «rational»",
							By(inRational, retarget.At(restricted)))
						onA := e.Have(
							"so the equation holds on D",
							"∀x:A. x ∈ «away» ⇒ monoid_pow(M.mul, M.one, ψ(x), card(k) ^ m) = ψ(permutation_map(«twist», x))",
							Derive(func(f *Argument) {
								x := f.FixAs[A]("x")
								inAway := f.Assume()
								f.Show(
									"the value at x lies in F_Q",
									By(inAway, onValues.At(x), values.At(x)))
							}))
						everywhere := e.Have(
							"and spreads to the chart",
							"∀y:A. y ∈ «chart» ⇒ monoid_pow(M.mul, M.one, ψ(y), card(k) ^ m) = ψ(permutation_map(«twist», y))",
							Derive(func(f *Argument) {
								y := f.FixAs[A]("y")
								inChart := f.Assume()
								f.Show(
									"by TwistEquationSpreads at D",
									By(
										closed,
										models,
										inGroup,
										positive,
										divides,
										data.regularTwist,
										data.ringAway,
										data.awayInTwist,
										data.kInAway,
										data.charts,
										point,
										onA,
										inChart,
										TwistEquationSpreads.Read(M).At(k, L, t, C, a, z, F, b, s, m, twistField, away, ψ, y)))
							}))
						e.Show(
							"which puts ψ in W",
							BySets(point, everywhere))
					})
			}))
		arg.Show(
			"so restriction is a bijection of W onto the points in F_Q",
			By(
				bijection[0],
				bijection[1],
				fixedInPoints,
				rationalInM,
				matches,
				set_image.BijectionRestricts.At(restriction, points, fixed, pointsInM, rationalPoints)))
	}),
})}

// FixedTwistPointsOfGoodOpen — restriction to C is a bijection of W onto the
// twisted evaluations of C. It is a bijection of all the points of B onto the
// points of C in M (constant_splitting.ConstantPointsInField), φ is s on C, so the
// equation of W on C is the twist equation, and it spreads from C to B
// (TwistEquationSpreads). A point of W takes D into F_Q, as φ fixes D, so it takes
// B, the chart of D, into the algebraic closure of k, which holds F_Q and l
// (constant_splitting.ConstantPointValues): its restriction is a geometric point of C.
var FixedTwistPointsOfGoodOpen = fixedTwistPointsOfGoodOpenThm{family.Add(registry.ProofEntry{
	Name: "FixedTwistPointsOfGoodOpen",
	Key:  "prop_f3471c09e13c7dc3",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀z:(permutation(A) → A). " +
			"∀F:(permutation(A) → num → A). " +
			"∀b:(permutation(A) → num). " +
			"∀s:permutation(A). " +
			"∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"fixed_twist_models(M, k, L, t, C, a, z, F, b)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
			"0 < m",
			"permutation_order(s) ∣ m - 1",
		},
		Conclusion: "injective_on(«fixed», «restriction») ∧ image(«restriction», «fixed») = «twisted»",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "twist", Text: "constant_twist_automorphism(M, k, L, s)"},
			{Name: "field", Text: "constant_twist_field(M, k, L, s)"},
			{Name: "away", Text: "ring_away(field_ring(M), " +
				"    plane_chart_zero(restrict_ring(field_ring(M), «field»), k, t, z(s)), " +
				"    polynomial_eval(a, t))"},
			{Name: "chart", Text: "constant_chart(field_ring(M), «constants», C)"},
			{Name: "chartOfAway", Text: "constant_chart(field_ring(M), «constants», «away»)"},
			{Name: "onChart", Text: "restrict_ring(field_ring(M), «chart»)"},
			{Name: "points", Text: "algebra_points(«onChart», field_ring(M), «constants», λx:A. x)"},
			{Name: "pointsOfAway", Text: "algebra_points(restrict_ring(field_ring(M), «chartOfAway»), " +
				"    field_ring(M), " +
				"    «constants», " +
				"    λx:A. x)"},
			{Name: "fixed", Text: "{ψ:A → A | " +
				"    ψ ∈ «points» ∧ " +
				"    (∀y:A. " +
				"        y ∈ «chart» ⇒ " +
				"        monoid_pow(M.mul, M.one, ψ(y), card(k) ^ m) = ψ(permutation_map(«twist», y)))}"},
			{Name: "restriction", Text: "λψ:A → A. λx:A. COND(x ∈ C, ψ(x), M.zero)"},
			{Name: "onC", Text: "restrict_ring(field_ring(M), C)"},
			{Name: "rational", Text: "finite_constants(field_ring(M), card(k), m)"},
			{Name: "pointsInM", Text: "algebra_points(«onC», field_ring(M), k, λx:A. x)"},
			{Name: "twisted", Text: "twisted_evaluations(M, k, C, card(k) ^ m, s)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		z *Arrow[Permutation[A], A],
		F *Arrow2[Permutation[A], Nat, A],
		b *Arrow[Permutation[A], Nat],
		s *Expr[Permutation[A]],
		m *Expr[Nat],
		closed, models, inGroup, positive, divides Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		twistField := arg.TermAs[Set[A]]("«field»")
		constants := arg.TermAs[Set[A]]("«constants»")
		away := arg.TermAs[Set[A]]("«away»")
		chartOfAway := arg.TermAs[Set[A]]("«chartOfAway»")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		order := arg.TermAs[Nat]("permutation_order(s)")
		onChart := arg.TermAs[module_record.RingOps[A]]("«onChart»")
		onC := arg.TermAs[module_record.RingOps[A]]("«onC»")
		points := arg.TermAs[Set[Fun[A, A]]]("«points»")
		fixed := arg.TermAs[Set[Fun[A, A]]]("«fixed»")
		pointsInM := arg.TermAs[Set[Fun[A, A]]]("«pointsInM»")
		twisted := arg.TermAs[Set[Fun[A, A]]]("«twisted»")
		restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		identity := arg.TermAs[Fun[A, A]]("λx:A. x")
		size := arg.TermAs[Nat]("card(k)")
		data := readFixedTwistChart(
			arg, models, inGroup, FixedTwistChartData.Read(M).At(k, L, t, C, a, z, F, b, s))
		acts := arg.Conjuncts(
			GroupPremises(closed, models, inGroup, FixedTwistActsOnChart.Read(M).At(k, L, t, C, a, z, F, b, s)),
			"the twist is a ring endomorphism of the chart",
			"it is the q-th power on l",
			"it is s on C",
			"it fixes D")
		closureField := arg.Conjuncts(
			GroupPremises(data.subfieldK, algebraic_element.AlgebraicElementsSubfield.Read(M).At(k)),
			"the algebraic points form a subfield",
			"they hold k")
		rationalInClosure := arg.Have(
			"they hold F_Q",
			"«rational» ⊆ algebraic_elements(M, k)",
			By(data.subfieldK, data.finiteK, positive, finite_field.FiniteConstantsInClosure.Read(M).At(k, m)))
		constantsInClosure := arg.Have(
			"and l",
			"«constants» ⊆ algebraic_elements(M, k)",
			By(
				data.subfieldK,
				data.finiteK,
				data.positiveOrder,
				finite_field.FiniteConstantsInClosure.Read(M).At(k, order)))
		subringClosure := arg.Have(
			"so they form a subring",
			"subring(field_ring(M), algebraic_elements(M, k))",
			By(closureField[0], field.SubfieldSubring.Read(M)))
		CInChart := arg.Have(
			"C lies in the chart",
			"C ⊆ «chart»",
			By(
				data.regular,
				data.subfieldConstants,
				data.kInConstants,
				data.finiteConstants,
				data.ringC,
				data.CInL,
				data.kInC,
				constant_field_extension.ConstantChartRing.Read(M).At(L, k, constants, C)))
		awayInChart := arg.Have(
			"and so does D",
			"«away» ⊆ «chart»",
			By(
				data.charts,
				data.regularTwist,
				data.subfieldConstants,
				data.kInConstants,
				data.finiteConstants,
				data.ringAway,
				data.awayInTwist,
				data.kInAway,
				constant_field_extension.ConstantChartRing.Read(M).At(twistField, k, constants, away)))
		bijection := arg.Conjuncts(
			arg.Have(
				"restriction is a bijection of the points of the chart onto the points of C in M",
				"injective_on(«points», «restriction») ∧ image(«restriction», «points») = «pointsInM»",
				By(
					M,
					data.regular,
					data.subfieldConstants,
					data.kInConstants,
					data.finiteConstants,
					data.ringC,
					data.kInC,
					data.CInL,
					constant_splitting.ConstantPointsInField.Read(M).At(L, k, constants, C))),
			"restriction is one-to-one on the points",
			"their restrictions are the points of C in M")
		inside := arg.Have(
			"the restrictions lie among the points of C in M",
			"image(«restriction», «points») ⊆ «pointsInM»",
			BySets(bijection[1]))
		restrictions := arg.Have(
			"each of them",
			"∀ψ:(A → A). ψ ∈ «points» ⇒ «restriction»(ψ) ∈ «pointsInM»",
			By(inside, set_image.ImageSubsetIff.At(restriction, points, pointsInM)))
		evaluations := arg.Have(
			"a geometric point of C is a point of C in M with values in the closure",
			"∀e:(A → A). "+
				"    e ∈ geometric_evaluation_points(M, k, C) ⇔ "+
				"    e ∈ «pointsInM» ∧ (∀x:A. x ∈ C ⇒ e(x) ∈ algebraic_elements(M, k))",
			arg.ForEach(func(e *Expr[Fun[A, A]]) Action {
				return By(
					subringClosure,
					field.RingOn.Read(M),
					galois_good_open.GeometricEvaluationPointsDef.At(fieldM, k, C),
					algebra_points.AlgebraPointsInSubring.At(R, onC, k, identity, e, closure))
			}))
		twistedMember := arg.Have(
			"a twisted evaluation is a geometric point of C whose "+
				"Q-th powers on C are its values at the images under s",
			"∀e:(A → A). "+
				"    e ∈ «twisted» ⇔ "+
				"    e ∈ geometric_evaluation_points(M, k, C) ∧ "+
				"    (∀x:A. x ∈ C ⇒ monoid_pow(M.mul, M.one, e(x), card(k) ^ m) = e(permutation_map(s, x)))",
			BySets(twisted_count.TwistedEvaluationsDef.At(fieldM, k, C, arg.TermAs[Nat]("card(k) ^ m"), s)))
		fixedInPoints := arg.Have(
			"W lies among the points of the chart",
			"«fixed» ⊆ «points»",
			BySets())
		twistedInM := arg.Have(
			"and the twisted evaluations among the points of C in M",
			"«twisted» ⊆ «pointsInM»",
			BySets(evaluations, twistedMember))
		matches := arg.Have(
			"a point lies in W exactly as its restriction is a twisted evaluation",
			"∀ψ:(A → A). ψ ∈ «points» ⇒ (ψ ∈ «fixed» ⇔ «restriction»(ψ) ∈ «twisted»)",
			Derive(func(d *Argument) {
				ψ := d.FixAs[Fun[A, A]]("ψ")
				point := d.Assume()
				restricted := d.TermAs[Fun[A, A]]("«restriction»(ψ)")
				hom := d.Have(
					"ψ is a ring map on the chart",
					"ring_homomorphism(«onChart», field_ring(M), ψ)",
					By(point, algebra_points.AlgebraPointsMember.At(onChart, R, constants, identity, ψ)))
				below := d.Have(
					"its restriction is a point of C in M",
					"«restriction»(ψ) ∈ «pointsInM»",
					By(point, restrictions.At(ψ)))
				onValues := d.Have(
					"on C the restriction is ψ, s keeps C, and φ is s there",
					Statement{
						Binders:    "∀x:A.",
						Hypotheses: []string{"x ∈ C"},
						Conclusion: "«restriction»(ψ, x) = ψ(x) ∧ " +
							"«restriction»(ψ, permutation_map(s, x)) = ψ(permutation_map(«twist», x))",
					},
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						inC := e.Assume()
						e.Show(
							"both restrictions take their first branch",
							By(Normalized, inC, acts[2].At(x)))
					}))
				d.Iff()
				d.Forward(
					"a point of W restricts to a twisted evaluation",
					func(e *Argument, inFixed Fact) {
						equation := e.Have(
							"ψ satisfies the equation on the chart",
							"∀y:A. y ∈ «chart» ⇒ monoid_pow(M.mul, M.one, ψ(y), card(k) ^ m) = ψ(permutation_map(«twist», y))",
							BySets(inFixed))
						intoClosure := e.Have(
							"ψ takes D into the closure: φ fixes D, so ψ takes it into F_Q",
							"∀x:A. x ∈ «away» ⇒ ψ(x) ∈ algebraic_elements(M, k)",
							Derive(func(f *Argument) {
								x := f.FixAs[A]("x")
								inAway := f.Assume()
								inChart := f.Have(
									"x lies in the chart",
									"x ∈ «chart»",
									BySets(inAway, awayInChart))
								value := f.Have(
									"so ψ(x) lies in M",
									"ψ(x) ∈ M.carrier",
									By(inChart, ring_homomorphism.MapIn.Read(hom)))
								inRational := f.Have(
									"and the Q-th power fixes it",
									"ψ(x) ∈ «rational»",
									BySets(
										value,
										inAway,
										inChart,
										equation.At(x),
										acts[3].At(x),
										finite_field.FiniteConstantsDef.At(R, size, m)))
								f.Show(
									"F_Q lies in the closure",
									BySets(inRational, rationalInClosure))
							}))
						onAway := e.Have(
							"that is, its image",
							"image(ψ, «away») ⊆ algebraic_elements(M, k)",
							By(intoClosure, set_image.ImageSubsetIff.At(ψ, away, closure)))
						pointOfAway := e.Have(
							"ψ is a point of the chart of D",
							"ψ ∈ «pointsOfAway»",
							By(data.charts, point))
						onChartOfAway := e.Have(
							"so it takes that chart into the closure",
							"image(ψ, «chartOfAway») ⊆ algebraic_elements(M, k)",
							By(
								data.regularTwist,
								data.subfieldConstants,
								data.kInConstants,
								data.finiteConstants,
								data.ringAway,
								data.kInAway,
								data.awayInTwist,
								closureField[0],
								constantsInClosure,
								pointOfAway,
								onAway,
								constant_splitting.ConstantPointValues.Read(M).At(twistField, k, constants, away, closure, ψ)))
						valuesOnChart := e.Have(
							"which is to say, point by point",
							"∀y:A. y ∈ «chartOfAway» ⇒ ψ(y) ∈ algebraic_elements(M, k)",
							By(onChartOfAway, set_image.ImageSubsetIff.At(ψ, chartOfAway, closure)))
						values := e.Have(
							"so the restriction of ψ has values in the closure",
							"∀x:A. x ∈ C ⇒ «restriction»(ψ, x) ∈ algebraic_elements(M, k)",
							Derive(func(f *Argument) {
								x := f.FixAs[A]("x")
								inC := f.Assume()
								inChart := f.Have(
									"x lies in the chart of D, the common chart",
									"x ∈ «chartOfAway»",
									BySets(inC, CInChart, data.charts))
								f.Show(
									"on C the restriction is ψ",
									By(inC, inChart, valuesOnChart.At(x)))
							}))
						onCEquation := e.Have(
							"and satisfies the twist equation",
							Statement{
								Binders:    "∀x:A.",
								Hypotheses: []string{"x ∈ C"},
								Conclusion: "monoid_pow(M.mul, M.one, «restriction»(ψ, x), card(k) ^ m) = " +
									"«restriction»(ψ, permutation_map(s, x))",
							},
							Derive(func(f *Argument) {
								x := f.FixAs[A]("x")
								inC := f.Assume()
								inChart := f.Have(
									"x lies in the chart",
									"x ∈ «chart»",
									BySets(inC, CInChart))
								f.Show(
									"the equation at x",
									By(inC, inChart, onValues.At(x), equation.At(x)))
							}))
						e.Show(
							"so it is a twisted evaluation",
							BySets(below, values, onCEquation, evaluations.At(restricted), twistedMember.At(restricted)))
					})
				d.Backward(
					"a point restricting to a twisted evaluation satisfies the equation on the chart",
					func(e *Argument, inTwisted Fact) {
						twistEquation := e.Have(
							"its restriction satisfies the twist equation",
							Statement{
								Binders: "∀x:A.",
								Hypotheses: []string{
									"x ∈ C",
								},
								Conclusion: "monoid_pow(M.mul, M.one, «restriction»(ψ, x), card(k) ^ m) = " +
									"«restriction»(ψ, permutation_map(s, x))",
							},
							BySets(inTwisted, twistedMember.At(restricted)))
						onCEquation := e.Have(
							"so the equation holds on C",
							"∀x:A. x ∈ C ⇒ monoid_pow(M.mul, M.one, ψ(x), card(k) ^ m) = ψ(permutation_map(«twist», x))",
							Derive(func(f *Argument) {
								x := f.FixAs[A]("x")
								inC := f.Assume()
								f.Show(
									"the twist equation at x",
									By(inC, onValues.At(x), twistEquation.At(x)))
							}))
						everywhere := e.Have(
							"and spreads to the chart",
							"∀y:A. y ∈ «chart» ⇒ monoid_pow(M.mul, M.one, ψ(y), card(k) ^ m) = ψ(permutation_map(«twist», y))",
							Derive(func(f *Argument) {
								y := f.FixAs[A]("y")
								inChart := f.Assume()
								f.Show(
									"by TwistEquationSpreads at C",
									By(
										closed,
										models,
										inGroup,
										positive,
										divides,
										data.regular,
										data.ringC,
										data.CInL,
										data.kInC,
										point,
										onCEquation,
										inChart,
										TwistEquationSpreads.Read(M).At(k, L, t, C, a, z, F, b, s, m, L, C, ψ, y)))
							}))
						e.Show(
							"which puts ψ in W",
							BySets(point, everywhere))
					})
			}))
		arg.Show(
			"so restriction is a bijection of W onto the twisted evaluations",
			By(
				bijection[0],
				bijection[1],
				fixedInPoints,
				twistedInM,
				matches,
				set_image.BijectionRestricts.At(restriction, points, fixed, pointsInM, twisted)))
	}),
})}

// FixedTwistPointCorrespondence — the points of D, the affine chart of the twist
// field with a(t) inverted, in the field of Q = |k|^m elements are as many as the
// twisted evaluations of C at Q, when the order of s divides m - 1. Both are in
// bijection with W, the points ψ of the common chart of D and C over l with
// ψ(y)^Q = ψ(φ y): restriction to D and restriction to C are the two bijections
// (FixedTwistPointsOfAway, FixedTwistPointsOfGoodOpen), and the twisted
// evaluations are finitely many (twisted_count.TwistedEvaluationsFinite), so W is finite.
var FixedTwistPointCorrespondence = fixedTwistPointCorrespondenceThm{family.Add(registry.ProofEntry{
	Name: "FixedTwistPointCorrespondence",
	Key:  "prop_8f5a9ae7035e7168",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀z:(permutation(A) → A). " +
			"∀F:(permutation(A) → num → A). " +
			"∀b:(permutation(A) → num). " +
			"∀s:permutation(A). " +
			"∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"fixed_twist_models(M, k, L, t, C, a, z, F, b)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
			"0 < m",
			"permutation_order(s) ∣ m - 1",
		},
		Conclusion: "card(algebra_points(restrict_ring(field_ring(M), " +
			"            ring_away(field_ring(M), " +
			"                plane_chart_zero( " +
			"                    restrict_ring(field_ring(M), constant_twist_field(M, k, L, s)), " +
			"                    k, " +
			"                    t, " +
			"                    z(s)), " +
			"                polynomial_eval(a, t))), " +
			"        restrict_ring(field_ring(M), finite_constants(field_ring(M), card(k), m)), " +
			"        k, " +
			"        λx:A. x)) = " +
			"twisted_evaluation_count(M, k, C, card(k) ^ m, s)",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "twist", Text: "constant_twist_automorphism(M, k, L, s)"},
			{Name: "away", Text: "ring_away(field_ring(M), " +
				"    plane_chart_zero(restrict_ring(field_ring(M), constant_twist_field(M, k, L, s)), " +
				"        k, " +
				"        t, " +
				"        z(s)), " +
				"    polynomial_eval(a, t))"},
			{Name: "chart", Text: "constant_chart(field_ring(M), «constants», C)"},
			{Name: "points", Text: "algebra_points(restrict_ring(field_ring(M), «chart»), " +
				"    field_ring(M), " +
				"    «constants», " +
				"    λx:A. x)"},
			{Name: "fixed", Text: "{ψ:A → A | " +
				"    ψ ∈ «points» ∧ " +
				"    (∀y:A. " +
				"        y ∈ «chart» ⇒ " +
				"        monoid_pow(M.mul, M.one, ψ(y), card(k) ^ m) = ψ(permutation_map(«twist», y)))}"},
			{Name: "restrictionToAway", Text: "λψ:A → A. λx:A. COND(x ∈ «away», ψ(x), M.zero)"},
			{Name: "restrictionToC", Text: "λψ:A → A. λx:A. COND(x ∈ C, ψ(x), M.zero)"},
			{Name: "rationalPoints", Text: "algebra_points(restrict_ring(field_ring(M), «away»), " +
				"    restrict_ring(field_ring(M), finite_constants(field_ring(M), card(k), m)), " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "twisted", Text: "twisted_evaluations(M, k, C, card(k) ^ m, s)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		z *Arrow[Permutation[A], A],
		F *Arrow2[Permutation[A], Nat, A],
		b *Arrow[Permutation[A], Nat],
		s *Expr[Permutation[A]],
		m *Expr[Nat],
		closed, models, inGroup, positive, divides Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		fixed := arg.TermAs[Set[Fun[A, A]]]("«fixed»")
		toAway := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restrictionToAway»")
		toC := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restrictionToC»")
		power := arg.TermAs[Nat]("card(k) ^ m")
		good := readFixedTwistModels(arg, models).good
		ofAway := arg.Conjuncts(
			GroupPremises(
				closed,
				models,
				inGroup,
				positive,
				divides,
				FixedTwistPointsOfAway.Read(M).At(k, L, t, C, a, z, F, b, s, m)),
			"restriction to D is one-to-one on W",
			"it carries W onto the points of D in F_Q")
		ofC := arg.Conjuncts(
			GroupPremises(
				closed,
				models,
				inGroup,
				positive,
				divides,
				FixedTwistPointsOfGoodOpen.Read(M).At(k, L, t, C, a, z, F, b, s, m)),
			"restriction to C is one-to-one on W",
			"it carries W onto the twisted evaluations")
		finiteTwisted := arg.Have(
			"the twisted evaluations are finitely many",
			"finite(«twisted»)",
			By(
				closed,
				good,
				positive,
				inGroup,
				twisted_count.TwistedEvaluationsFinite.Read(M).At(k, L, t, C, a, m, s)))
		finiteFixed := arg.Have(
			"so W is finite, restriction to C being one-to-one on it",
			"finite(«fixed»)",
			By(ofC[0], ofC[1], finiteTwisted, finite_set.FiniteImageInjEq.At(toC, fixed)))
		countAway := arg.Have(
			"W has as many members as the points of D in F_Q",
			"card(«rationalPoints») = card(«fixed»)",
			By(ofAway[0], ofAway[1], finiteFixed, cardinality.CardImageInj.At(toAway, fixed)))
		countC := arg.Have(
			"and as the twisted evaluations",
			"card(«twisted») = card(«fixed»)",
			By(ofC[0], ofC[1], finiteFixed, cardinality.CardImageInj.At(toC, fixed)))
		arg.Show(
			"so the two counts agree",
			By(countAway, countC, twisted_count.TwistedEvaluationCountDef.At(fieldM, k, C, power, s)))
	}),
})}
