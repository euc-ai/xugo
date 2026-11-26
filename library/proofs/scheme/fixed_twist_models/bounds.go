package fixed_twist_models

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/constant_twist"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	"github.com/euc-ai/xugo/library/proofs/scheme/plane_model"
	"github.com/euc-ai/xugo/library/proofs/scheme/rational_point_bound"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// FixedTwistModelUpperBound — one twist of fixed models obeys the square-field
// bound: for s in the group there are constants B and Q₀ such that, for m > 0
// with e(s) dividing m - 1, |k|^m = r² and Q₀ ≤ |k|^m, the twisted count of the
// chart C at |k|^m is at most |k|^m + B·r. The model of the twist field gives B
// and Q₀ (rational_point_bound.IntegralPlaneModelSquareFieldUpperBound), and l, the field of
// |k|^m elements, is one of the fields that bound speaks of. The twisted count
// is the number of points in l of the chart with a(t) inverted
// (FixedTwistPointCorrespondence), and inverting the unit a(t) adds no points to
// the chart, which has finitely many (algebra_points.AlgebraPointsAwayCardLe).
var FixedTwistModelUpperBound = fixedTwistModelUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "FixedTwistModelUpperBound",
	Key:  "prop_57481a1d9e76b1af",
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
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "∃B Q₀:num. ∀m r:num. " +
			"    0 < m ∧ permutation_order(s) ∣ m - 1 ∧ card(k) ^ m = r * r ∧ Q₀ ≤ card(k) ^ m ⇒ " +
			"    twisted_evaluation_count(M, k, C, card(k) ^ m, s) ≤ card(k) ^ m + B * r",
		Abbrev: Abbrev{
			{Name: "chart", Text: "plane_chart_zero( " +
				"    restrict_ring(field_ring(M), constant_twist_field(M, k, L, s)), k, t, z(s))"},
			{Name: "overlap", Text: "ring_away( " +
				"    restrict_ring(field_ring(M), constant_twist_field(M, k, L, s)), «chart», t)"},
			{Name: "secondChart", Text: "plane_chart_one( " +
				"    restrict_field(M, constant_twist_field(M, k, L, s)), k, t, z(s), b(s))"},
			{Name: "polynomialsInTwist", Text: "polynomial_image( " +
				"    field_ring(restrict_field(M, constant_twist_field(M, k, L, s))), k, t)"},
			{Name: "points", Text: "λX:set(A). λl:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), restrict_ring(field_ring(M), l), k, λx:A. x)"},
		},
	},
		func(
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
			twist := arg.TermAs[Set[A]]("constant_twist_field(M, k, L, s)")
			chart := arg.TermAs[Set[A]]("«chart»")
			secondChart := arg.TermAs[Set[A]]("«secondChart»")
			overlap := arg.TermAs[Set[A]]("«overlap»")
			value := arg.TermAs[A]("polynomial_eval(a, t)")
			opened := readFixedTwistModels(arg, models)
			good, twists := opened.good, opened.twists
			finiteK := galois_good_open.GoodOpenConstantsFinite.Read(good)
			subfieldTwist := arg.Have(
				"the twist field is a subfield, a regular function field over k by descent",
				"subfield(M, constant_twist_field(M, k, L, s))",
				By(
					M,
					closed,
					galois_good_open.GoodOpenRegular.Read(good),
					finiteK,
					galois_good_open.GoodOpenParameterIn.Read(good),
					galois_good_open.GoodOpenParameterTranscendental.Read(good),
					galois_good_open.GoodOpenGalois.Read(good),
					inGroup,
					constant_twist.CyclicConstantTwistDescent.Read(M).At(k, L, t, s),
					function_field.RegularFunctionFieldDef.At(fieldM, k, twist)))
			twistField := arg.Have(
				"so it is a field under the operations of M",
				"field_on(restrict_field(M, constant_twist_field(M, k, L, s)))",
				By(subfieldTwist, field.SubfieldFieldOn.Read(M).At(twist)))
			model := arg.Have(
				"the twist field has its integral plane model",
				"integral_plane_model(restrict_field(M, constant_twist_field(M, k, L, s)), k, t, z(s), F(s), b(s))",
				By(twists.At(s), inGroup))
			curve := arg.Have(
				"the model's two charts make a curve over the line",
				"curve_over_line(restrict_field(M, constant_twist_field(M, k, L, s)), "+
					"    k, "+
					"    t, "+
					"    «chart», "+
					"    «secondChart», "+
					"    «overlap»)",
				By(
					subfieldTwist,
					model,
					plane_model.PlaneEquationBiaffineCurve.Read(M).At(
						twist, k, t, arg.TermAs[A]("z(s)"), arg.TermAs[Fun[Nat, A]]("F(s)"), arg.TermAs[Nat]("b(s)"))))
			chartData := arg.Conjuncts(
				arg.Have(
					"so the chart is a subring of the twist field holding k[t], which holds k",
					"subring(field_ring(restrict_field(M, constant_twist_field(M, k, L, s))), «chart») ∧ "+
						"k ⊆ «polynomialsInTwist» ∧ "+
						"«polynomialsInTwist» ⊆ «chart»",
					By(curve, algebraic_curve.CurveOverItsLine.Read(twistField).At(k, chart, secondChart, overlap, t))),
				"the chart is a subring of the twist field",
				"k lies in k[t]",
				"k[t] lies in the chart")
			subringInTwist, kInPolynomials, polynomialsInChart := chartData[0], chartData[1], chartData[2]
			subringInRestriction := arg.Have(
				"read inside the ring on the twist field",
				"subring(restrict_ring(field_ring(M), constant_twist_field(M, k, L, s)), «chart»)",
				By(subringInTwist, field.RestrictFieldRing.At(fieldM, twist)))
			chartInCarrier := arg.Have(
				"the chart lies in M",
				"«chart» ⊆ M.carrier",
				BySets(
					comm_ring.SubringSubset.Read(subringInRestriction),
					subfieldTwist,
					field.SubfieldSubset.At(fieldM, twist)))
			subringChart := arg.Have(
				"so the chart is a subring of M",
				"subring(field_ring(M), «chart»)",
				By(
					chartInCarrier,
					subringInRestriction,
					comm_ring.SubringDef.At(R, chart),
					comm_ring.SubringDef.At(
						arg.TermAs[module_record.RingOps[A]](
							"restrict_ring(field_ring(M), constant_twist_field(M, k, L, s))"),
						chart)))
			kInChart := arg.Have(
				"k lies in the chart",
				"k ⊆ «chart»",
				BySets(kInPolynomials, polynomialsInChart))
			inPolynomials := arg.Have(
				"a(t) is the value of a polynomial over k",
				"polynomial_eval(a, t) ∈ polynomial_image(field_ring(M), k, t)",
				BySets(
					galois_good_open.GoodOpenDenominatorOver.Read(good),
					algebraic_element.PolynomialImageDef.At(R, k, t)))
			valueInChart := arg.Have(
				"so it lies in the chart",
				"polynomial_eval(a, t) ∈ «chart»",
				BySets(
					inPolynomials,
					polynomialsInChart,
					algebraic_element.PolynomialsOverRestriction.At(fieldM, twist, k, t)))
			valueInCarrier := arg.Have(
				"and in M",
				"polynomial_eval(a, t) ∈ M.carrier",
				BySets(valueInChart, chartInCarrier))
			valueMember := arg.MemberOf[on.M](value, valueInCarrier)
			inverse := field.InvIn.Read(M).At(valueMember)
			B, Q0, planeBound := arg.Unpack2As[Nat, Nat](
				GroupPremises(
					subfieldTwist,
					model,
					rational_point_bound.IntegralPlaneModelSquareFieldUpperBound.Read(M).At(
						twist, k, t, arg.TermAs[A]("z(s)"), arg.TermAs[Fun[Nat, A]]("F(s)"), arg.TermAs[Nat]("b(s)"))),
				"B",
				"Q₀")
			arg.Take(B)
			arg.Take(Q0)
			m := arg.FixAs[Nat]("m")
			r := arg.FixAs[Nat]("r")
			assumed := arg.Conjuncts(
				arg.Assume(),
				"m is positive",
				"e(s) divides m - 1",
				"|k|^m is the square of r",
				"|k|^m is at least Q₀")
			positive, divides, square, atLeastQ0 := assumed[0], assumed[1], assumed[2], assumed[3]
			l := arg.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), m)")
			constants := arg.Conjuncts(
				arg.Have(
					"l, the field of |k|^m elements of M, is a finite subfield holding k",
					"subfield(M, finite_constants(field_ring(M), card(k), m)) ∧ "+
						"k ⊆ finite_constants(field_ring(M), card(k), m) ∧ "+
						"finite(finite_constants(field_ring(M), card(k), m)) ∧ "+
						"card(finite_constants(field_ring(M), card(k), m)) = card(k) ^ m",
					By(
						closed,
						galois_good_open.GoodOpenConstantsSubfield.Read(good),
						finiteK,
						positive,
						finite_field.FiniteConstantsSubfield.Read(M).At(k, m),
						cardinality.HasSizeDef)),
				"l is a subfield",
				"l holds k",
				"l is finite",
				"l has |k|^m elements")
			subfieldConstants, kInConstants, finiteConstants, sizeConstants :=
				constants[0], constants[1], constants[2], constants[3]
			planePoints := arg.Have(
				"the chart has at most |k|^m + B·r points in l",
				"card(«points»(«chart», finite_constants(field_ring(M), card(k), m))) ≤ card(k) ^ m + B * r",
				By(
					subfieldConstants,
					finiteConstants,
					kInConstants,
					sizeConstants,
					square,
					atLeastQ0,
					planeBound.At(l, r)))
			finitePoints := arg.Have(
				"which are finitely many",
				"finite(«points»(«chart», finite_constants(field_ring(M), card(k), m)))",
				By(
					subfieldTwist,
					curve,
					finiteConstants,
					curve_point_count.CurvePointSetsFinite.Read(M).At(twist, k, chart, secondChart, overlap, t, l)))
			fewer := arg.Have(
				"inverting the unit a(t) adds no point",
				"card(«points»(ring_away(field_ring(M), «chart», polynomial_eval(a, t)), "+
					"        finite_constants(field_ring(M), card(k), m))) ≤ "+
					"card(«points»(«chart», finite_constants(field_ring(M), card(k), m)))",
				By(
					field.RingOn.Read(M),
					subringChart,
					kInChart,
					valueInChart,
					inverse,
					galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
					field.MulRightInverseOn.Read(M).At(valueMember),
					finitePoints,
					algebra_point_bounds.AlgebraPointsAwayCardLe.At(
						R,
						arg.TermAs[module_record.RingOps[A]](
							"restrict_ring(field_ring(M), finite_constants(field_ring(M), card(k), m))"),
						chart,
						k,
						arg.TermAs[Fun[A, A]]("λx:A. x"),
						value,
						inverse)))
			counted := arg.Have(
				"and the chart with a(t) inverted counts the twisted evaluations in l",
				"card(«points»(ring_away(field_ring(M), «chart», polynomial_eval(a, t)), "+
					"        finite_constants(field_ring(M), card(k), m))) = "+
					"twisted_evaluation_count(M, k, C, card(k) ^ m, s)",
				By(
					closed,
					models,
					inGroup,
					positive,
					divides,
					FixedTwistPointCorrespondence.Read(M).At(k, L, t, C, a, z, F, b, s, m)))
			arg.Show(
				"so the twisted count obeys the bound of the chart",
				ByArith(fewer, planePoints, counted))
		}),
})}

// FixedTwistedUpperBound — for a good open over a square field, and m with
// 2|G| dividing m - 1, the twisted count of the chart at |k|^m is at most
// |k|^m + B √|k|^m, with B and a threshold m₀ fixed before s and m. Refining the
// open (TwistModelsRefineGoodOpen) yields models of all the twist fields and
// costs at most |G| deg c twisted points. Each twist has constants of its own
// (FixedTwistModelUpperBound); they are chosen along the finite group, and the
// sums of the chosen constants bound them all. With r² = |k|, e(s) divides |G|,
// so divides m - 1, and |k|^m = (r^m)²; the threshold falls below m, which is
// below |k|^m (nat_order.LessThanPowSelf). The refinement's cost is absorbed by
// r^m ≥ 1, and r^m is the root of |k|^m in ℝ.
var FixedTwistedUpperBound = fixedTwistedUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "FixedTwistedUpperBound",
	Key:  "prop_a148545e588e1f91",
	Reading: "B and m₀ are chosen before s and m, so one bound serves every automorphism of " +
		"the group at every admissible m. That card(k) is a square makes every |k|^m one, the form " +
		"in which the bound of each twist is stated, and 2|G| dividing m - 1 makes the order of " +
		"every s divide m - 1. The count is that of the given chart C, not of a refinement of it.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"∃r:num. card(k) = r * r",
		},
		Conclusion: "∃B:real. ∃m₀:num. " +
			"    real_of_num(0) ≤ B ∧ " +
			"    (∀s:permutation(A). ∀m:num. " +
			"        s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L) ∧ " +
			"        0 < m ∧ " +
			"        m₀ ≤ m ∧ " +
			"        2 * card(field_automorphisms(M, field_adjoin(M, k, {t}), L)) ∣ m - 1 ⇒ " +
			"        real_of_num(twisted_evaluation_count(M, k, C, card(k) ^ m, s)) ≤ " +
			"        real_of_num(card(k) ^ m) + B * real_sqrt(real_of_num(card(k) ^ m)))",
		Abbrev: Abbrev{
			{Name: "group", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "refined", Text: "λc:(num → A). ring_away(field_ring(M), C, polynomial_eval(c, t))"},
			{Name: "cost", Text: "λc:(num → A). " +
				"    card(field_automorphisms(M, field_adjoin(M, k, {t}), L)) * polynomial_degree(c)"},
			{Name: "bounded", Text: "λc:(num → A). λs:permutation(A). λB:num. λQ₀:num. ∀m r:num. " +
				"    0 < m ∧ permutation_order(s) ∣ m - 1 ∧ card(k) ^ m = r * r ∧ Q₀ ≤ card(k) ^ m ⇒ " +
				"    twisted_evaluation_count(M, k, «refined»(c), card(k) ^ m, s) ≤ card(k) ^ m + B * r"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			C *Expr[Set[A]],
			a *Arrow[Nat, A],
			closed, good, square Fact,
		) {
			group := arg.TermAs[Set[Permutation[A]]]("«group»")
			adjoined := arg.TermAs[Set[A]]("field_adjoin(M, k, {t})")
			card := arg.TermAs[Nat]("card(k)")
			order := arg.TermAs[Nat]("card(«group»)")
			finiteGroup := GroupPremises(good, galois_good_open.GoodOpenGroupFinite.Read(M).At(k, L, C, t, a))
			atLeastTwo := arg.Have(
				"k is a finite subfield, so it has at least two elements",
				"2 ≤ card(k)",
				By(
					galois_good_open.GoodOpenConstantsSubfield.Read(good),
					galois_good_open.GoodOpenConstantsFinite.Read(good),
					finite_field.FiniteSubfieldPrimePower.Read(M).At(k)))
			r, root := arg.UnpackAs[Nat](square, "r")
			rootNonzero := arg.Have(
				"r is not zero",
				"r ≠ 0",
				ByArith(atLeastTwo, root, nat_arith.MulEqZero.At(r, r)))
			_, refinement := arg.ObtainAs[Fun[Nat, A]](
				"refining the open by a polynomial c gives models of "+
					"the twist fields, at a cost of |G| deg c twisted points",
				"∃c:(num → A). "+
					"    (∃z:(permutation(A) → A). ∃F:(permutation(A) → num → A). ∃b:(permutation(A) → num). "+
					"        fixed_twist_models(M, k, L, t, «refined»(c), polynomial_mul(a, c), z, F, b)) ∧ "+
					"    (∀s:permutation(A). ∀m:num. "+
					"        s ∈ «group» ∧ 0 < m ⇒ "+
					"        twisted_evaluation_count(M, k, C, card(k) ^ m, s) ≤ "+
					"        twisted_evaluation_count(M, k, «refined»(c), card(k) ^ m, s) + «cost»(c))",
				By(closed, good, TwistModelsRefineGoodOpen.Read(M).At(k, L, C, t, a)))
			refined := arg.Conjuncts(
				refinement,
				"the refined open carries models of the twist fields",
				"and loses at most |G| deg c twisted points")
			z, F, b, models := arg.Unpack3As[Fun[Permutation[A], A], Fun2[Permutation[A], Nat, A], Fun[Permutation[A], Nat]](
				refined[0], "z", "F", "b")
			comparison := refined[1]
			perTwist := arg.Have(
				"each twist has constants of its own",
				"∀s:permutation(A). s ∈ «group» ⇒ ∃B Q₀:num. «bounded»(c, s, B, Q₀)",
				Derive(func(d *Argument) {
					s := d.FixAs[Permutation[A]]("s")
					inGroup := d.Assume()
					d.Show(
						"the bound at one twist of the refined models",
						By(
							closed,
							models,
							inGroup,
							FixedTwistModelUpperBound.Read(M).At(
								k,
								L,
								t,
								d.TermAs[Set[A]]("«refined»(c)"),
								d.TermAs[Fun[Nat, A]]("polynomial_mul(a, c)"),
								z,
								F,
								b,
								s)))
				}))
			choice := arg.Have(
				"a pair for each member of the group is a pair of maps on the group",
				Statement{
					Binders:    "∀R:(permutation(A) → num → num → bool).",
					Hypotheses: []string{"∀s:permutation(A). s ∈ «group» ⇒ ∃u v:num. R(s, u, v)"},
					Conclusion: "∃f g:(permutation(A) → num). ∀s:permutation(A). s ∈ «group» ⇒ R(s, f(s), g(s))",
				},
				Derive(func(d *Argument) {
					d.FixAs[Fun[Permutation[A], Fun2[Nat, Nat, Bool]]]("R")
					each := d.Assume()
					d.Show(
						"the maps are the choices",
						By(each))
				}))
			B, Q0, chosen := arg.Obtain2As[Fun[Permutation[A], Nat], Fun[Permutation[A], Nat]](
				"choose the constants along the group",
				"∃B Q₀:(permutation(A) → num). ∀s:permutation(A). s ∈ «group» ⇒ «bounded»(c, s, B(s), Q₀(s))",
				By(perTwist, choice.At(arg.TermAs[Fun[Permutation[A], Fun2[Nat, Nat, Bool]]]("«bounded»(c)"))))
			total := arg.TermAs[Nat]("nat_sum(«group», B)")
			cost := arg.TermAs[Nat]("«cost»(c)")
			arg.Take(arg.TermAs[Real]("real_of_num(nat_sum(«group», B) + «cost»(c))"))
			arg.Take(arg.TermAs[Nat]("nat_sum(«group», Q₀)"))
			arg.Show(
				"the sums of the chosen constants, with the cost of the refinement, bound every twist",
				SplitConj(
					Case(
						"the constant, a natural number, is not negative",
						ByArith()),
					Case(
						"the bound at s and m",
						Derive(func(d *Argument) {
							s := d.FixAs[Permutation[A]]("s")
							m := d.FixAs[Nat]("m")
							assumed := d.Conjuncts(
								d.Assume(),
								"s lies in the group",
								"m is positive",
								"m is past the threshold",
								"2|G| divides m - 1")
							inGroup, positive, past, divides := assumed[0], assumed[1], assumed[2], assumed[3]
							power := d.TermAs[Nat]("r ^ m")
							count := d.TermAs[Nat]("twisted_evaluation_count(M, k, C, card(k) ^ m, s)")
							bound := d.TermAs[Nat]("card(k) ^ m + (nat_sum(«group», B) + «cost»(c)) * r ^ m")
							orderDivides := d.Have(
								"e(s) divides |G|, so it divides m - 1",
								"permutation_order(s) ∣ m - 1",
								By(
									good,
									galois_good_open.GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
									galois_good_open.GoodOpenFieldSubfield.Read(good),
									galois_good_open.GoodOpenRationalInField.Read(good),
									galois_good_open.GoodOpenFiniteExtension.Read(good),
									inGroup,
									divides,
									field_automorphism.AutomorphismOrderFacts.Read(M).At(adjoined, L, s),
									nat_divides.DividesTrans.At(d.TermAs[Nat]("permutation_order(s)"), order, d.TermAs[Nat]("m - 1")),
									nat_divides.DividesTrans.At(order, d.TermAs[Nat]("2 * card(«group»)"), d.TermAs[Nat]("m - 1")),
									nat_divides.DividesOwnMultiple.At(order, d.TermAs[Nat]("2"))))
							powerSquare := d.Have(
								"|k|^m is the square of r^m",
								"card(k) ^ m = r ^ m * r ^ m",
								By(Normalized, root, nat_arith.MulPowDistrib.At(r, r, m)))
							threshold := d.Have(
								"its constant Q₀(s) is below the sum of them, below m, below |k|^m",
								"Q₀(s) ≤ card(k) ^ m",
								ByArith(
									past,
									finiteGroup,
									inGroup,
									atLeastTwo,
									nat_sum.TermLeSum.At(Q0, group, s),
									nat_order.LessThanPowSelf.At(card, m)))
							summand := d.Have(
								"and B(s) is below the sum of the B",
								"B(s) ≤ nat_sum(«group», B)",
								By(finiteGroup, inGroup, nat_sum.TermLeSum.At(B, group, s)))
							twistBound := d.Have(
								"so the refined chart obeys the bound of s at r^m",
								"twisted_evaluation_count(M, k, «refined»(c), card(k) ^ m, s) ≤ card(k) ^ m + B(s) * r ^ m",
								By(chosen.At(s, m, power), inGroup, positive, orderDivides, powerSquare, threshold))
							comparing := d.Have(
								"and the chart loses at most the cost of the refinement",
								"twisted_evaluation_count(M, k, C, card(k) ^ m, s) ≤ "+
									"twisted_evaluation_count(M, k, «refined»(c), card(k) ^ m, s) + «cost»(c)",
								By(comparison.At(s, m), inGroup, positive))
							powerPositive := d.Have(
								"r^m is positive",
								"0 < r ^ m",
								By(rootNonzero, nat_order.PowPositive.At(r, m)))
							natural := d.Have(
								"so the cost is absorbed by r^m ≥ 1",
								"twisted_evaluation_count(M, k, C, card(k) ^ m, s) ≤ "+
									"card(k) ^ m + (nat_sum(«group», B) + «cost»(c)) * r ^ m",
								ByArith(
									comparing,
									twistBound,
									summand,
									powerPositive,
									nat_order.LessEqMulRightCancel.At(d.TermAs[Nat]("B(s)"), total, power),
									nat_order.LessEqMulNonzero.At(cost, power)))
							realSquare := d.Have(
								"in ℝ, |k|^m is the square of r^m",
								"real_of_num(card(k) ^ m) = real_pow(real_of_num(r ^ m), 2)",
								ByArith(powerSquare))
							nonnegative := d.Have(
								"and r^m is nonnegative",
								"real_of_num(0) ≤ real_of_num(r ^ m)",
								ByArith())
							realRoot := d.Have(
								"so r^m is the root of |k|^m",
								"real_of_num(r ^ m) = real_sqrt(real_of_num(card(k) ^ m))",
								By(
									realSquare,
									nonnegative,
									real_sqrt.SqrtUnique.At(
										d.TermAs[Real]("real_of_num(card(k) ^ m)"), d.TermAs[Real]("real_of_num(r ^ m)"))))
							cast := d.Have(
								"the natural bound holds in ℝ",
								"real_of_num(twisted_evaluation_count(M, k, C, card(k) ^ m, s)) ≤ "+
									"real_of_num(card(k) ^ m + (nat_sum(«group», B) + «cost»(c)) * r ^ m)",
								By(natural, real_construction.OfNumLessEq.At(count, bound)))
							d.Show(
								"and the root stands for r^m",
								realRoot.RwRev(),
								ByArith(cast, real_construction.OfNumAdd, real_construction.OfNumMul))
						}))))
		}),
})}
