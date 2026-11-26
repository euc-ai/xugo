package twisted_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/twisted_counting"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// GoodPointKeepsDenominator — a point of a ring holding the constants, t and
// the inverse of a(t) does not kill a(t): it fixes the coefficients of a, so
// it carries a(t) to the value of a at the image of t, and a ring map keeps a
// unit from vanishing, one not being zero.
var GoodPointKeepsDenominator = goodPointKeepsDenominatorThm{family.Add(registry.ProofEntry{
	Name: "GoodPointKeepsDenominator",
	Key:  "prop_e810e734a44d8fac",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀S U:set(A). ∀e:(A → A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"k ⊆ S",
			"t ∈ S",
			"M.inv(polynomial_eval(a, t)) ∈ S",
			"e ∈ algebra_points(«source», «target», k, λx:A. x)",
		},
		Conclusion: "polynomial_eval(a, e(t)) ≠ M.zero",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "target", Text: "restrict_ring(field_ring(M), U)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		S, U *Expr[Set[A]],
		e *Arrow[A, A],
		good, kInS, tInS, inverseInS, point Fact,
	) {
		source := arg.TermAs[RingOps[A]]("«source»")
		target := arg.TermAs[RingOps[A]]("«target»")
		zero := arg.TermAs[A]("M.zero")
		value := arg.TermAs[A]("polynomial_eval(a, t)")
		inverse := arg.TermAs[A]("M.inv(polynomial_eval(a, t))")
		valueIn := arg.MemberOf[on.M](value, arg.Have(
			"a(t) lies in the chart, inside L, inside M",
			"polynomial_eval(a, t) ∈ M.carrier",
			BySets(
				good,
				galois_good_open.GoodOpenDenominatorInChart.Read(M).At(k, L, C, t, a),
				galois_good_open.GoodOpenChartInField.Read(good),
				field.SubfieldSubset.Read(galois_good_open.GoodOpenFieldSubfield.Read(good)))))
		inverted := arg.Have(
			"a(t) is nonzero, so its inverse inverts it",
			"polynomial_eval(a, t) * M.inv(polynomial_eval(a, t)) = M.one",
			By(
				galois_good_open.GoodOpenDenominatorValueNonzero.Read(good),
				field.MulRightInverseOn.Read(M).At(valueIn)))
		hom := arg.Have(
			"e is a ring map",
			"ring_homomorphism(«source», «target», e)",
			By(
				point,
				algebra_points.AlgebraPointsMember.At(source, target, k, arg.TermAs[Fun[A, A]]("λx:A. x"), e)))
		overK := galois_good_open.GoodOpenDenominatorOver.Read(good)
		overS := arg.Have(
			"a is a polynomial over S",
			"polynomial_over(S, a)",
			By(kInS, overK, polynomial.PolynomialOverMono.At(zero, k, S, a)))
		sourceRing := ring_homomorphism.Source.Read(hom)
		targetRing := ring_homomorphism.Target.Read(hom)
		valueInS := arg.Have(
			"a(t) lies in S",
			"polynomial_eval(a, t) ∈ S",
			By(overS, tInS, polynomial_evaluation.EvalIn.Read(sourceRing).AsFact().At(a, t)))
		carried := arg.Have(
			"e fixes the coefficients of a, so it carries a(t) to the value of a at e(t)",
			"e(polynomial_eval(a, t)) = polynomial_eval(a, e(t))",
			By(kInS, tInS, overK, point, galois_good_open.PointAtPolynomialValue.Read(M).At(k, S, U, t, a, e)))
		arg.Show(
			"if that value vanished, e would send one to zero",
			Derive(func(b *Argument) {
				vanishes := b.SupposeNot()
				b.Show(
					"but one is not zero",
					By(
						Normalized,
						vanishes,
						carried,
						inverted,
						valueInS,
						inverseInS,
						field.OneNotZeroOn.Read(M),
						ring_homomorphism.MapOne.Read(hom),
						ring_homomorphism.MapMul.Read(hom).AsFact().At(value, inverse),
						ring_homomorphism.MapIn.Read(hom).AsFact().At(inverse),
						comm_ring.MulLeftZeroOn.Read(targetRing).AsFact().At(e.Apply(inverse))))
			}))
	}),
})}

// PointFrobenius — raising its values to the power card(k)^m, m > 0, keeps a
// point: the power map is a ring endomorphism of M fixing k and zero, and a
// ring under the operations of M is closed under it.
var PointFrobenius = pointFrobeniusThm{family.Add(registry.ProofEntry{
	Name: "PointFrobenius",
	Key:  "prop_b7ae291c1b88d29f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k U:set(A). ∀m:num. ∀R:ring_ops(A). ∀ev:(A → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"0 < m",
			"U ⊆ M.carrier",
			"ev ∈ algebra_points(R, «target», k, λx:A. x)",
		},
		Conclusion: "(λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m)) ∈ " +
			"algebra_points(R, «target», k, λx:A. x)",
		Abbrev: Abbrev{
			{Name: "target", Text: "restrict_ring(field_ring(M), U)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, U *Expr[Set[A]],
		m *Expr[Nat],
		R *Expr[RingOps[A]],
		ev *Arrow[A, A],
		closedField, subfieldK, finiteK, positive, inside, point Fact,
	) {
		ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
		target := arg.TermAs[RingOps[A]]("«target»")
		identity := arg.TermAs[Fun[A, A]]("λx:A. x")
		power := arg.TermAs[Nat]("card(k) ^ m")
		frobenius := arg.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), card(k) ^ m)")
		powered := arg.TermAs[Fun[A, A]]("λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m)")
		parts := arg.Conjuncts(
			arg.Have(
				"ev is a ring map fixing k and vanishing off the carrier",
				"ring_homomorphism(R, «target», ev) ∧ "+
					"(∀x:A. x ∈ k ⇒ ev(x) = x) ∧ "+
					"(∀x:A. x ∉ R.carrier ⇒ ev(x) = M.zero)",
				By(point, algebra_points.AlgebraPointsMember.At(R, target, k, identity, ev))),
			"ev is a ring map",
			"ev fixes k",
			"ev vanishes off the carrier")
		hom, fixes, offCarrier := parts[0], parts[1], parts[2]
		targetRing := ring_homomorphism.Target.Read(hom)
		endomorphism := arg.Have(
			"the card(k)^m-th power is a ring endomorphism of M",
			"ring_homomorphism(field_ring(M), field_ring(M), frobenius_power(field_ring(M), card(k) ^ m))",
			By(subfieldK, finiteK, positive, finite_field.FiniteSubfieldPowerEndomorphism.Read(M).At(k, m)))
		intoM := arg.Have(
			"ev is a ring map into M",
			"ring_homomorphism(R, field_ring(M), ev)",
			By(hom, field.RingOn.Read(M), inside, ring_homomorphism.RingHomExtendTarget.At(R, ringM, ev, U)))
		composite := arg.Have(
			"so its composite with the power map is one",
			"ring_homomorphism(R, field_ring(M), λy:A. frobenius_power(field_ring(M), card(k) ^ m, ev(y)))",
			By(intoM, endomorphism, ring_homomorphism.RingHomCompose.At(R, ringM, ringM, ev, frobenius)))
		intoRingM := arg.Have(
			"which raises the values of ev to that power",
			"ring_homomorphism(R, field_ring(M), λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m))",
			By(Normalized, composite, finite_field.FrobeniusPowerDef))
		subringU := arg.Have(
			"the target is a subring of M",
			"subring(field_ring(M), U)",
			By(inside, targetRing, field.RingOn.Read(M), comm_ring.SubringRingOn.At(ringM, U)))
		valuesInU := arg.Have(
			"the powers of values of ev stay in the target",
			"∀x:A. x ∈ R.carrier ⇒ monoid_pow(M.mul, M.one, ev(x), card(k) ^ m) ∈ U",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				b.Show(
					"the value lies in the target, whose multiplication is that of M",
					By(
						xIn,
						ring_homomorphism.MapIn.Read(hom).AsFact().At(x),
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(targetRing)).AsFact().At(ev.Apply(x), power)))
			}))
		corestricted := arg.Have(
			"so the powered map is a ring map into the target",
			"ring_homomorphism(R, «target», λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m))",
			By(intoRingM, subringU, valuesInU, ring_homomorphism.RingHomCorestrict.At(R, ringM, powered, U)))
		fixed := arg.Have(
			"k is fixed by the power",
			"k ⊆ finite_constants(field_ring(M), card(k), m)",
			By(
				closedField,
				subfieldK,
				finiteK,
				positive,
				finite_field.FiniteConstantsSubfield.Read(M).At(k, m)))
		fixesK := arg.Have(
			"the powered map fixes k",
			"∀x:A. x ∈ k ⇒ monoid_pow(M.mul, M.one, ev(x), card(k) ^ m) = x",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				b.Show(
					"ev fixes x, and so does the power",
					BySets(
						xIn,
						fixes.At(x),
						fixed,
						finite_field.FiniteConstantsDef.At(ringM, arg.TermAs[Nat]("card(k)"), m)))
			}))
		zeroPower := arg.Have(
			"the power of zero is zero",
			"monoid_pow(M.mul, M.one, M.zero, card(k) ^ m) = M.zero",
			By(Normalized, ring_homomorphism.MapZero.Read(endomorphism), finite_field.FrobeniusPowerDef))
		offC := arg.Have(
			"so the powered map vanishes off the carrier",
			"∀x:A. x ∉ R.carrier ⇒ monoid_pow(M.mul, M.one, ev(x), card(k) ^ m) = M.zero",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xOut := b.Assume()
				b.Show(
					"ev vanishes there",
					By(Normalized, xOut, zeroPower, offCarrier.At(x)))
			}))
		arg.Show(
			"which makes the powered map a point",
			By(
				corestricted,
				fixesK,
				offC,
				algebra_points.AlgebraPointsMember.At(R, target, k, identity, powered)))
	}),
})}

// GoodPointBase — a geometric point sends t to a good base point: its values
// are algebraic over k, and it does not kill a(t), the inverse of which lies
// in the chart.
var GoodPointBase = goodPointBaseThm{family.Add(registry.ProofEntry{
	Name: "GoodPointBase",
	Key:  "prop_41d761c00c38c025",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀ev:(A → A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"ev ∈ geometric_evaluation_points(M, k, C)",
		},
		Conclusion: "ev(t) ∈ algebraic_elements(M, k) ∧ polynomial_eval(a, ev(t)) ≠ M.zero",
		Abbrev: Abbrev{
			{Name: "chart", Text: "restrict_ring(field_ring(M), C)"},
			{Name: "closed", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		ev *Arrow[A, A],
		good, point Fact,
	) {
		chart := arg.TermAs[RingOps[A]]("«chart»")
		closed := arg.TermAs[RingOps[A]]("«closed»")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		asPoint := arg.Have(
			"ev is a point of the chart with values algebraic over k",
			"ev ∈ algebra_points(«chart», «closed», k, λx:A. x)",
			Simp(Rev(galois_good_open.GeometricEvaluationPointsDef)),
			By(point))
		ringMap := arg.Have(
			"so it is a ring map to those values",
			"ring_homomorphism(«chart», «closed», ev)",
			By(
				asPoint,
				algebra_points.AlgebraPointsMember.At(chart, closed, k, arg.TermAs[Fun[A, A]]("λx:A. x"), ev)))
		arg.Show(
			"it keeps a(t) from vanishing, and sends t into the values",
			By(
				good,
				galois_good_open.GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a),
				galois_good_open.GoodOpenParameterInChart.Read(M).At(k, L, C, t, a),
				galois_good_open.GoodOpenDenominatorInverseInChart.Read(M).At(k, L, C, t, a),
				asPoint,
				ring_homomorphism.MapIn.Read(ringMap).AsFact().At(t),
				GoodPointKeepsDenominator.Read(M).At(k, L, t, C, a, C, closure, ev)))
	}),
})}

// RationalPointOverGoodBase — a rational point of the chart lies on the fibre
// over its value at t, and that value is a rational base point that is good:
// it is algebraic over k and a does not vanish there, a geometric point sending
// t to a good base point, and the power fixes it.
var RationalPointOverGoodBase = rationalPointOverGoodBaseThm{family.Add(registry.ProofEntry{
	Name: "RationalPointOverGoodBase",
	Key:  "prop_2c0149e3b8e8f2",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀m:num. ∀ev:(A → A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"ev ∈ «rational»",
		},
		Conclusion: "ev ∈ geometric_fibre(M, k, C, t, ev(t)) ∧ " +
			"ev(t) ∈ algebraic_elements(M, k) ∧ " +
			"monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t) ∧ " +
			"polynomial_eval(a, ev(t)) ≠ M.zero",
		Abbrev: Abbrev{
			{Name: "rational", Text: "{e:(A → A) | " +
				"    e ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    monoid_pow(M.mul, M.one, e(t), card(k) ^ m) = e(t)}"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		m *Expr[Nat],
		ev *Arrow[A, A],
		good, rational Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		point := arg.Conjuncts(
			arg.Have(
				"ev is a geometric point with fixed value at t",
				"ev ∈ geometric_evaluation_points(M, k, C) ∧ monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)",
				BySets(rational)),
			"ev is a geometric point",
			"its value at t is fixed")
		base := arg.Have(
			"it sends t to a good base point",
			"ev(t) ∈ algebraic_elements(M, k) ∧ polynomial_eval(a, ev(t)) ≠ M.zero",
			By(good, point[0], GoodPointBase.Read(M).At(k, L, t, C, a, ev)))
		arg.Show(
			"so ev lies on the fibre over that point",
			BySets(
				point[0],
				point[1],
				base,
				galois_good_open.GeometricFibreDef.At(fieldM, k, C, t, ev.Apply(t))))
	}),
})}

// RationalPointsFreeAction — the automorphism group acts freely on the
// geometric points whose value at t is fixed by the power card(k)^m: each such
// point lies over a good base point, on a fibre the group acts on freely, the
// action keeps the fibre and so the value at t, and these fibres are finitely
// many finite sets.
var RationalPointsFreeAction = rationalPointsFreeActionThm{family.Add(registry.ProofEntry{
	Name: "RationalPointsFreeAction",
	Key:  "prop_9cda8c8b2f2bebca",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"0 < m",
		},
		Conclusion: "free_finite_action(galois_group(M, field_adjoin(M, k, {t}), L), " +
			"    «rational», " +
			"    evaluation_action(field_ring(M), C))",
		Abbrev: Abbrev{
			{Name: "G", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "rational", Text: "{ev:(A → A) | " +
				"    ev ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)}"},
			{Name: "fibre", Text: "λx:A. geometric_fibre(M, k, C, t, x)"},
			{Name: "base", Text: "{x:A | " +
				"    x ∈ algebraic_elements(M, k) ∧ " +
				"    monoid_pow(M.mul, M.one, x, card(k) ^ m) = x ∧ " +
				"    polynomial_eval(a, x) ≠ M.zero}"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		m *Expr[Nat],
		closedField, good, positive Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
		adjoinedField := arg.TermAs[Set[A]]("field_adjoin(M, k, {t})")
		rational := arg.TermAs[Set[Fun[A, A]]]("«rational»")
		base := arg.TermAs[Set[A]]("«base»")
		fibre := arg.TermAs[Fun[A, Set[Fun[A, A]]]]("«fibre»")
		order := arg.TermAs[Nat]("card(k)")
		fibreMember := arg.Have(
			"a map lies on the fibre over x when it is a geometric point sending t to x",
			"∀x:A. ∀ev:(A → A). ev ∈ «fibre»(x) ⇔ ev ∈ geometric_evaluation_points(M, k, C) ∧ ev(t) = x",
			BySets(galois_good_open.GeometricFibreDef))
		overBase := arg.Have(
			"a rational point lies on the fibre over a good "+
				"base point, and the group acts freely on that fibre",
			Statement{
				Binders:    "∀ev:(A → A).",
				Hypotheses: []string{"ev ∈ «rational»"},
				Conclusion: "ev ∈ «fibre»(ev(t)) ∧ " +
					"ev(t) ∈ «base» ∧ " +
					"free_finite_action(galois_group(M, field_adjoin(M, k, {t}), L), " +
					"    «fibre»(ev(t)), " +
					"    evaluation_action(field_ring(M), C))",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				over := b.Conjuncts(
					GroupPremises(good, b.Assume(), RationalPointOverGoodBase.Read(M).At(k, L, t, C, a, m, ev)),
					"ev lies on the fibre over its value at t",
					"that value is algebraic over k",
					"the power fixes it",
					"a does not vanish there")
				onFibre := galois_good_open.ReadGoodFibre(b, good, b.TermAs[A]("ev(t)"), over[1], over[3])
				b.Show(
					"ev lies on the fibre through itself",
					BySets(over[0], over[1], over[2], over[3], onFibre.Free))
			}))
		staysRational := arg.Have(
			"a point of the fibre through a rational point is rational, with the same value at t",
			"∀ev ew:(A → A). ev ∈ «rational» ∧ ew ∈ «fibre»(ev(t)) ⇒ ew ∈ «rational»",
			Derive(func(b *Argument) {
				b.FixAs[Fun[A, A]]("ev")
				ew := b.FixAs[Fun[A, A]]("ew")
				given := b.Conjuncts(
					b.Assume(),
					"ev is rational",
					"ew lies on its fibre")
				b.Show(
					"the condition reads the value at t alone",
					BySets(given[0], given[1], fibreMember.At(b.TermAs[A]("ev(t)"), ew)))
			}))
		onRational := arg.Have(
			"the action laws hold at a rational point, and keep it rational",
			Statement{
				Binders:    "∀ev:(A → A).",
				Hypotheses: []string{"ev ∈ «rational»"},
				Conclusion: "evaluation_action(field_ring(M), C, permutation_identity, ev) = ev ∧ " +
					"(∀g h:permutation(A). " +
					"    g ∈ «G» ∧ h ∈ «G» ⇒ " +
					"    evaluation_action(field_ring(M), C, g, ev) ∈ «rational» ∧ " +
					"    evaluation_action(field_ring(M), C, permutation_compose(g, h), ev) = " +
					"    evaluation_action(field_ring(M), C, g, evaluation_action(field_ring(M), C, h, ev)) ∧ " +
					"    (evaluation_action(field_ring(M), C, g, ev) = ev ⇒ g = permutation_identity))",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				evIn := b.Assume()
				on := b.Conjuncts(
					GroupPremises(evIn, overBase.At(ev)),
					"ev lies on the fibre through it",
					"which lies over a good base point",
					"and the group acts freely on the fibre")
				free := b.Conjuncts(
					b.Unfolded(on[2], twisted_counting.FreeFiniteActionDef),
					"the group is a group on its carrier",
					"the carrier is finite",
					"the fibre is finite",
					"the identity acts trivially",
					"the action laws")
				unit, laws := free[3], free[4]
				identity := b.Have(
					"the identity leaves ev where it is",
					"evaluation_action(field_ring(M), C, permutation_identity, ev) = ev",
					By(on[0], unit.At(ev)))
				translated := b.Have(
					"elements of the group keep ev rational and multiply freely",
					Statement{
						Binders: "∀g h:permutation(A).",
						Hypotheses: []string{
							"g ∈ «G»",
							"h ∈ «G»",
						},
						Conclusion: "evaluation_action(field_ring(M), C, g, ev) ∈ «rational» ∧ " +
							"evaluation_action(field_ring(M), C, permutation_compose(g, h), ev) = " +
							"evaluation_action(field_ring(M), C, g, evaluation_action(field_ring(M), C, h, ev)) ∧ " +
							"(evaluation_action(field_ring(M), C, g, ev) = ev ⇒ g = permutation_identity)",
					},
					Derive(func(c *Argument) {
						g := c.FixAs[symmetric_group.Permutation[A]]("g")
						h := c.FixAs[symmetric_group.Permutation[A]]("h")
						inG := c.Assume()
						law := c.Have(
							"the fibre through ev carries the laws",
							"evaluation_action(field_ring(M), C, g, ev) ∈ «fibre»(ev(t)) ∧ "+
								"evaluation_action(field_ring(M), C, permutation_compose(g, h), ev) = "+
								"evaluation_action(field_ring(M), C, g, evaluation_action(field_ring(M), C, h, ev)) ∧ "+
								"(evaluation_action(field_ring(M), C, g, ev) = ev ⇒ g = permutation_identity)",
							By(inG, on[0], laws.At(g, h, ev)))
						c.Show(
							"and its points are rational",
							By(
								law,
								evIn,
								staysRational.At(ev, c.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), C, g, ev)"))))
					}))
				b.Show(
					"which is the claim",
					By(identity, translated))
			}))
		endomorphism := arg.Conjuncts(
			GroupPremises(
				galois_good_open.GoodOpenConstantsSubfield.Read(good),
				galois_good_open.GoodOpenConstantsFinite.Read(good),
				positive,
				finite_field.FiniteSubfieldPowerEndomorphism.Read(M).At(k, m)),
			"the power map is a ring endomorphism",
			"the power exceeds one",
			"and is zero in M")
		fixedPoints := arg.Have(
			"the points fixed by the power are finitely many",
			"finite(finite_constants(field_ring(M), card(k), m))",
			By(endomorphism[1], finite_field.FiniteConstantsBound.Read(M).At(order, m)))
		baseInFixed := arg.Have(
			"a good base point is a point of M fixed by the power",
			"«base» ⊆ finite_constants(field_ring(M), card(k), m)",
			BySets(
				algebraic_element.AlgebraicElementsDef.At(fieldM, k),
				finite_field.FiniteConstantsDef.At(ringM, order, m)))
		finiteBase := arg.Have(
			"so the good base points are finitely many",
			"finite(«base»)",
			By(
				fixedPoints,
				baseInFixed,
				finite_set.FiniteSubset.At(
					base, arg.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), m)"))))
		finiteFibres := arg.Have(
			"and the fibre over each is finite, the group acting on it",
			"∀x:A. x ∈ «base» ⇒ finite(«fibre»(x))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				goodBase := b.Have(
					"x is a good base point",
					"x ∈ algebraic_elements(M, k) ∧ polynomial_eval(a, x) ≠ M.zero",
					BySets(xIn))
				onFibre := galois_good_open.ReadGoodFibre(b, good, x, goodBase)
				b.Show(
					"a free finite action is on a finite set",
					By(b.Unfolded(onFibre.Free, twisted_counting.FreeFiniteActionDef)))
			}))
		fibres := arg.TermAs[Set[Set[Fun[A, A]]]]("image(«fibre», «base»)")
		finiteUnion := arg.Have(
			"so the fibres over the good base points have a finite union",
			"finite(⋃image(«fibre», «base»))",
			By(
				finiteFibres,
				finiteBase,
				finite_set.FiniteImage.At(fibre, base),
				finite_set.FiniteFiniteUnions.At(fibres),
				set_image.ForallInImage.At(
					fibre, base, arg.TermAs[Fun[Set[Fun[A, A]], Bool]]("λs:set(A → A). finite(s)"))))
		covered := arg.Have(
			"which holds every rational point",
			"«rational» ⊆ ⋃image(«fibre», «base»)",
			BySets(overBase))
		finiteRational := arg.Have(
			"so the rational points are finitely many",
			"finite(«rational»)",
			By(
				finiteUnion,
				covered,
				finite_set.FiniteSubset.At(rational, arg.TermAs[Set[Fun[A, A]]]("⋃image(«fibre», «base»)"))))
		identity := arg.Have(
			"the identity fixes each rational point",
			"∀ev:(A → A). ev ∈ «rational» ⇒ evaluation_action(field_ring(M), C, permutation_identity, ev) = ev",
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				evIn := b.Assume()
				b.Show(
					"by the laws at ev",
					By(evIn, onRational.At(ev)))
			}))
		laws := arg.Have(
			"the elements of the group keep the rational points and act on them multiplicatively and freely",
			Statement{
				Binders:    "∀g h:permutation(A). ∀ev:(A → A).",
				Hypotheses: []string{"g ∈ «G»", "h ∈ «G»", "ev ∈ «rational»"},
				Conclusion: "evaluation_action(field_ring(M), C, g, ev) ∈ «rational» ∧ " +
					"evaluation_action(field_ring(M), C, permutation_compose(g, h), ev) = " +
					"evaluation_action(field_ring(M), C, g, evaluation_action(field_ring(M), C, h, ev)) ∧ " +
					"(evaluation_action(field_ring(M), C, g, ev) = ev ⇒ g = permutation_identity)",
			},
			Derive(func(b *Argument) {
				g := b.FixAs[symmetric_group.Permutation[A]]("g")
				h := b.FixAs[symmetric_group.Permutation[A]]("h")
				ev := b.FixAs[Fun[A, A]]("ev")
				given := b.Conjuncts(
					b.Assume(),
					"g lies in the group",
					"h lies in the group",
					"ev is rational")
				opened := b.Conjuncts(
					GroupPremises(given[2], onRational.At(ev)),
					"the identity fixes ev",
					"the group acts at ev")
				b.Show(
					"by the laws at ev",
					By(given[0], given[1], opened[1].At(g, h)))
			}))
		arg.Show(
			"which are the conditions of a free finite action",
			Unfold(twisted_counting.FreeFiniteActionDef),
			By(
				field_automorphism.GaloisGroupOn.Read(M).At(adjoinedField, L),
				good,
				galois_good_open.GoodOpenGroupFinite.Read(M).At(k, L, C, t, a),
				finiteRational,
				identity,
				laws))
	}),
})}

// GoodGroupFixesChartData — the automorphism group fixes k(t) pointwise, so it
// fixes the constants, t and the inverse of a(t), which lie there.
var GoodGroupFixesChartData = goodGroupFixesChartDataThm{family.Add(registry.ProofEntry{
	Name: "GoodGroupFixesChartData",
	Key:  "prop_8b4206a7db82fa4f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀s:permutation(A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "(∀x:A. x ∈ k ⇒ permutation_map(s, x) = x) ∧ " +
			"permutation_map(s, t) = t ∧ " +
			"permutation_map(s, M.inv(polynomial_eval(a, t))) = M.inv(polynomial_eval(a, t))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		s *Expr[symmetric_group.Permutation[A]],
		good, sIn Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		adjoinedField := arg.TermAs[Set[A]]("field_adjoin(M, k, {t})")
		fixed := arg.Have(
			"s fixes k(t) pointwise",
			"∀x:A. x ∈ field_adjoin(M, k, {t}) ⇒ permutation_map(s, x) = x",
			BySets(sIn, field_automorphism.FieldAutomorphismsDef.At(fieldM, adjoinedField, L)))
		arg.Show(
			"and k(t) holds the constants, t and the inverse of a(t)",
			BySets(
				fixed,
				galois_good_open.GoodOpenConstantsInRational.Read(good),
				galois_good_open.GoodOpenParameterInRational.Read(good),
				good,
				galois_good_open.GoodOpenDenominatorInverseInRational.Read(M).At(k, L, C, t, a)))
	}),
})}

// TwistedEvaluationsAreMoved — the evaluations twisted by s are the rational
// points the power map moves as the inverse of s does: at t a twisted
// evaluation has a value fixed by the power, s fixing t, and off the chart both
// sides of the motion vanish, a power of zero being zero.
var TwistedEvaluationsAreMoved = twistedEvaluationsAreMovedThm{family.Add(registry.ProofEntry{
	Name: "TwistedEvaluationsAreMoved",
	Key:  "prop_e2cb3f121163d566",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀m:num. " +
			"∀s:permutation(A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"0 < m",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "«twisted» = " +
			"{ev:(A → A) | " +
			"    ev ∈ «rational» ∧ " +
			"    «frobenius»(ev) = evaluation_action(field_ring(M), C, permutation_inverse(s), ev)}",
		Abbrev: Abbrev{
			{Name: "twisted", Text: "twisted_evaluations(M, k, C, card(k) ^ m, s)"},
			{Name: "rational", Text: "{ev:(A → A) | " +
				"    ev ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)}"},
			{Name: "frobenius", Text: "λev:(A → A). λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m)"},
			{Name: "chart", Text: "restrict_ring(field_ring(M), C)"},
			{Name: "closed", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		m *Expr[Nat],
		s *Expr[symmetric_group.Permutation[A]],
		good, positive, sIn Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
		chart := arg.TermAs[RingOps[A]]("«chart»")
		closed := arg.TermAs[RingOps[A]]("«closed»")
		inverse := arg.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)")
		twisted := arg.Have(
			"an evaluation is twisted by s when it is a geometric point "+
				"whose powers on the chart are its values at the images under s",
			"∀ev:(A → A). "+
				"    ev ∈ «twisted» ⇔ "+
				"    ev ∈ geometric_evaluation_points(M, k, C) ∧ "+
				"    (∀x:A. x ∈ C ⇒ monoid_pow(M.mul, M.one, ev(x), card(k) ^ m) = ev(permutation_map(s, x)))",
			BySets(TwistedEvaluationsDef.At(fieldM, k, C, arg.TermAs[Nat]("card(k) ^ m"), s)))
		endomorphism := arg.Have(
			"the power map is a ring endomorphism of M",
			"ring_homomorphism(field_ring(M), field_ring(M), frobenius_power(field_ring(M), card(k) ^ m))",
			By(
				galois_good_open.GoodOpenConstantsSubfield.Read(good),
				galois_good_open.GoodOpenConstantsFinite.Read(good),
				positive,
				finite_field.FiniteSubfieldPowerEndomorphism.Read(M).At(k, m)))
		zeroPower := arg.Have(
			"so the power of zero is zero",
			"monoid_pow(M.mul, M.one, M.zero, card(k) ^ m) = M.zero",
			By(Normalized, ring_homomorphism.MapZero.Read(endomorphism), finite_field.FrobeniusPowerDef))
		fixesT := arg.Have(
			"s fixes t",
			"permutation_map(s, t) = t",
			By(good, sIn, GoodGroupFixesChartData.Read(M).At(k, L, t, C, a, s)))
		twice := arg.Have(
			"inverting s twice returns s",
			"permutation_inverse(permutation_inverse(s)) = s",
			By(group.InvInv.Read(symmetric_group.SymmetricGroup)))
		member := arg.Have(
			"an evaluation is twisted by s exactly when it is rational and moved as the inverse of s",
			"∀ev:(A → A). "+
				"    ev ∈ «twisted» ⇔ "+
				"    ev ∈ "+
				"    {ev:(A → A) | "+
				"        ev ∈ «rational» ∧ "+
				"        «frobenius»(ev) = evaluation_action(field_ring(M), C, permutation_inverse(s), ev)}",
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				b.Iff()
				b.Forward(
					"a twisted evaluation has a fixed value at t and moves as the inverse of s",
					func(c *Argument, inTwisted Fact) {
						parts := c.Conjuncts(
							c.Have(
								"ev is a geometric point with its twist",
								"ev ∈ geometric_evaluation_points(M, k, C) ∧ "+
									"(∀x:A. x ∈ C ⇒ monoid_pow(M.mul, M.one, ev(x), card(k) ^ m) = ev(permutation_map(s, x)))",
								By(twisted.At(ev), inTwisted)),
							"ev is a geometric point",
							"its twist holds on the chart")
						twist := parts[1]
						atT := c.Have(
							"its value at t is fixed, s fixing t",
							"monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)",
							By(good, galois_good_open.GoodOpenParameterInChart.Read(M).At(k, L, C, t, a), twist.At(t), fixesT))
						asPoint := c.Have(
							"ev is a point of the chart with values algebraic over k",
							"ev ∈ algebra_points(«chart», «closed», k, λx:A. x)",
							Simp(Rev(galois_good_open.GeometricEvaluationPointsDef)),
							By(parts[0]))
						off := c.Have(
							"ev vanishes off the chart",
							"∀y:A. y ∉ C ⇒ ev(y) = M.zero",
							By(
								asPoint,
								algebra_points.AlgebraPointsMember.At(chart, closed, k, c.TermAs[Fun[A, A]]("λx:A. x"), ev)))
						moved := c.Have(
							"and the power map moves it as the inverse of s",
							"«frobenius»(ev) = evaluation_action(field_ring(M), C, permutation_inverse(s), ev)",
							Funext(),
							Derive(func(d *Argument) {
								y := d.FixAs[A]("y")
								action := galois_good_open.EvaluationActionDef.At(ringM, C, inverse, ev, y)
								d.Cases(d.Term("y ∈ C"))
								d.When(
									"on the chart this is the twist at y",
									func(e *Argument, inside Fact) {
										e.Show(
											"the inverse of the inverse of s being s",
											By(inside, twist.At(y), twice, action))
									})
								d.Otherwise(
									"off the chart both sides vanish",
									func(e *Argument, outside Fact) {
										e.Show(
											"a power of zero being zero",
											By(outside, off.At(y), zeroPower, action))
									})
							}))
						c.Show(
							"so ev is one of the moved rational points",
							BySets(parts[0], atT, moved))
					})
				b.Backward(
					"a rational point moved as the inverse of s satisfies the twist on the chart",
					func(c *Argument, inMoved Fact) {
						parts := c.Conjuncts(
							c.Have(
								"ev is a geometric point the power map moves",
								"ev ∈ geometric_evaluation_points(M, k, C) ∧ "+
									"monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t) ∧ "+
									"«frobenius»(ev) = evaluation_action(field_ring(M), C, permutation_inverse(s), ev)",
								BySets(inMoved)),
							"ev is a geometric point",
							"its value at t is fixed",
							"the power map moves it as the inverse of s")
						twist := c.Have(
							"read at a point of the chart, the motion is the twist",
							"∀x:A. x ∈ C ⇒ monoid_pow(M.mul, M.one, ev(x), card(k) ^ m) = ev(permutation_map(s, x))",
							Derive(func(d *Argument) {
								x := d.FixAs[A]("x")
								xIn := d.Assume()
								d.Show(
									"the action reads ev at the inverse of the inverse of s",
									By(
										Normalized,
										xIn,
										twice,
										parts[2],
										galois_good_open.EvaluationActionDef.At(ringM, C, inverse, ev, x)))
							}))
						c.Show(
							"so ev is twisted by s",
							By(twisted.At(ev), parts[0], twist))
					})
			}))
		arg.Show(
			"which is the equation of the two sets",
			BySets(member))
	}),
})}

// TwistedEvaluationsFinite — the evaluations twisted by s are finitely many:
// they are among the rational points.
var TwistedEvaluationsFinite = twistedEvaluationsFiniteThm{family.Add(registry.ProofEntry{
	Name: "TwistedEvaluationsFinite",
	Key:  "prop_c40f0404deffa14a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀m:num. " +
			"∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"0 < m",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "finite(twisted_evaluations(M, k, C, card(k) ^ m, s))",
		Abbrev: Abbrev{
			{Name: "rational", Text: "{ev:(A → A) | " +
				"    ev ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)}"},
			{Name: "frobenius", Text: "λev:(A → A). λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		m *Expr[Nat],
		s *Expr[symmetric_group.Permutation[A]],
		closedField, good, positive, sIn Fact,
	) {
		rational := arg.TermAs[Set[Fun[A, A]]]("«rational»")
		free := arg.Have(
			"the group acts freely on the finite set of rational points",
			"free_finite_action(galois_group(M, field_adjoin(M, k, {t}), L), "+
				"    «rational», "+
				"    evaluation_action(field_ring(M), C))",
			By(closedField, good, positive, RationalPointsFreeAction.Read(M).At(k, L, t, C, a, m)))
		finiteRational := arg.Have(
			"so the rational points are finitely many",
			"finite(«rational»)",
			By(arg.Unfolded(free, twisted_counting.FreeFiniteActionDef)))
		arg.Show(
			"and the twisted evaluations are moved rational points",
			GroupPremises(good, positive, sIn, TwistedEvaluationsAreMoved.Read(M).At(k, L, t, C, a, m, s)).Rw(),
			By(
				finiteRational,
				finite_set.FiniteRestrict.At(
					rational,
					arg.TermAs[Set[Fun[A, A]]](
						"λev:(A → A). «frobenius»(ev) = evaluation_action(field_ring(M), C, permutation_inverse(s), ev)"))))
	}),
})}

// TwistedEvaluationCountByInvariant — summed over a subgroup H, the twisted
// evaluations number card(H) for each value of r at a rational point whose
// value the power map does not change, r being a map on the rational points
// that tells the H-orbits apart: the group acts freely on the rational points,
// the power map commutes with the action and keeps them, and the evaluations
// twisted by s are the rational points the power map moves as the inverse of s.
var TwistedEvaluationCountByInvariant = twistedEvaluationCountByInvariantThm{family.Add(registry.ProofEntry{
	Name: "TwistedEvaluationCountByInvariant",
	Key:  "prop_3c778ccb02cf50b2",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀H:set(permutation(A)). " +
			"∀m:num. " +
			"∀r:((A → A) → B).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, field_adjoin(M, k, {t}), L), H)",
			"0 < m",
			"∀ev ew:(A → A). " +
				"    ev ∈ «rational» ∧ ew ∈ «rational» ⇒ " +
				"    (r(ev) = r(ew) ⇔ ∃h:permutation(A). h ∈ H ∧ evaluation_action(field_ring(M), C, h, ev) = ew)",
		},
		Conclusion: "nat_sum(H, λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)) = " +
			"card(H) * card({r(ev) | ev:(A → A) | ev ∈ «rational» ∧ r(«frobenius»(ev)) = r(ev)})",
		Abbrev: Abbrev{
			{Name: "G", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "rational", Text: "{ev:(A → A) | " +
				"    ev ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)}"},
			{Name: "frobenius", Text: "λev:(A → A). λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m)"},
			{Name: "movedAs", Text: "λg:permutation(A). " +
				"    {ev:(A → A) | " +
				"        ev ∈ «rational» ∧ «frobenius»(ev) = evaluation_action(field_ring(M), C, g, ev)}"},
			{Name: "chart", Text: "restrict_ring(field_ring(M), C)"},
			{Name: "closed", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		m *Expr[Nat],
		r *Arrow[Fun[A, A], B],
		closedField, good, subgroup, positive, separates Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
		chart := arg.TermAs[RingOps[A]]("«chart»")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		groupTerm := arg.TermAs[group.GroupOps[symmetric_group.Permutation[A]]](
			"galois_group(M, field_adjoin(M, k, {t}), L)")
		endomorphism := arg.Have(
			"the power map is a ring endomorphism of M",
			"ring_homomorphism(field_ring(M), field_ring(M), frobenius_power(field_ring(M), card(k) ^ m))",
			By(
				galois_good_open.GoodOpenConstantsSubfield.Read(good),
				galois_good_open.GoodOpenConstantsFinite.Read(good),
				positive,
				finite_field.FiniteSubfieldPowerEndomorphism.Read(M).At(k, m)))
		zeroPower := arg.Have(
			"so the power of zero is zero",
			"monoid_pow(M.mul, M.one, M.zero, card(k) ^ m) = M.zero",
			By(Normalized, ring_homomorphism.MapZero.Read(endomorphism), finite_field.FrobeniusPowerDef))
		free := arg.Have(
			"the group acts freely on the rational points",
			"free_finite_action(galois_group(M, field_adjoin(M, k, {t}), L), "+
				"    «rational», "+
				"    evaluation_action(field_ring(M), C))",
			By(closedField, good, positive, RationalPointsFreeAction.Read(M).At(k, L, t, C, a, m)))
		groupOn := arg.Have(
			"so the group is a group on its set",
			"group_on(galois_group(M, field_adjoin(M, k, {t}), L))",
			By(arg.Unfolded(free, twisted_counting.FreeFiniteActionDef)))
		inG := arg.Have(
			"H lies in the group",
			"∀h:permutation(A). h ∈ H ⇒ h ∈ «G»",
			BySets(subgroup, group.SubgroupSubset.At(groupTerm, H)))
		commutes := arg.Have(
			"the power map commutes with the action",
			Statement{
				Binders:    "∀g:permutation(A). ∀ev:(A → A).",
				Hypotheses: []string{"g ∈ H", "ev ∈ «rational»"},
				Conclusion: "«frobenius»(evaluation_action(field_ring(M), C, g, ev)) = " +
					"evaluation_action(field_ring(M), C, g, «frobenius»(ev))",
			},
			Derive(func(b *Argument) {
				g := b.FixAs[symmetric_group.Permutation[A]]("g")
				ev := b.FixAs[Fun[A, A]]("ev")
				b.Assume()
				powered := b.TermAs[Fun[A, A]]("«frobenius»(ev)")
				b.Do(Funext())
				y := b.FixAs[A]("y")
				before := galois_good_open.EvaluationActionDef.At(ringM, C, g, ev, y)
				after := galois_good_open.EvaluationActionDef.At(ringM, C, g, powered, y)
				b.Cases(b.Term("y ∈ C"))
				b.When(
					"on the chart both sides are the power of ev at the inverse of g",
					func(c *Argument, inside Fact) {
						c.Show(
							"the action reads ev there",
							By(inside, before, after))
					})
				b.Otherwise(
					"off the chart both sides vanish",
					func(c *Argument, outside Fact) {
						c.Show(
							"a power of zero being zero",
							By(outside, before, after, zeroPower))
					})
			}))
		closureInside := arg.Have(
			"the values lie in M",
			"algebraic_elements(M, k) ⊆ M.carrier",
			BySets(algebraic_element.AlgebraicElementsDef.At(fieldM, k)))
		keepsRational := arg.Have(
			"the power map keeps the rational points",
			"∀ev:(A → A). ev ∈ «rational» ⇒ «frobenius»(ev) ∈ «rational»",
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				evIn := b.Assume()
				parts := b.Conjuncts(
					b.Have(
						"ev is a geometric point with fixed value at t",
						"ev ∈ geometric_evaluation_points(M, k, C) ∧ monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)",
						BySets(evIn)),
					"ev is a geometric point",
					"its value at t is fixed")
				asPoint := b.Have(
					"ev is a point of the chart with values algebraic over k",
					"ev ∈ algebra_points(«chart», «closed», k, λx:A. x)",
					Simp(Rev(galois_good_open.GeometricEvaluationPointsDef)),
					By(parts[0]))
				powered := b.Have(
					"so is its power",
					"(λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m)) ∈ "+
						"algebra_points(«chart», «closed», k, λx:A. x)",
					By(
						closedField,
						galois_good_open.GoodOpenConstantsSubfield.Read(good),
						galois_good_open.GoodOpenConstantsFinite.Read(good),
						positive,
						closureInside,
						asPoint,
						PointFrobenius.Read(M).At(k, closure, m, chart, ev)))
				geometric := b.Have(
					"which is a geometric point",
					"«frobenius»(ev) ∈ geometric_evaluation_points(M, k, C)",
					Simp(Fwd(galois_good_open.GeometricEvaluationPointsDef)),
					By(powered))
				b.Show(
					"with the same fixed value at t",
					BySets(geometric, parts[1]))
			}))
		movedSum := arg.Have(
			"the fixed-orbit formula, read on r",
			"nat_sum(H, λg:permutation(A). card(«movedAs»(g))) = "+
				"card(H) * card({r(ev) | ev:(A → A) | ev ∈ «rational» ∧ r(«frobenius»(ev)) = r(ev)})",
			By(
				free,
				subgroup,
				commutes,
				keepsRational,
				separates,
				twisted_counting.FreeActionTwistedCountByInvariant.At(groupTerm,
					H,
					arg.TermAs[Set[Fun[A, A]]]("«rational»"),
					arg.TermAs[Fun2[symmetric_group.Permutation[A], Fun[A, A], Fun[A, A]]](
						"evaluation_action(field_ring(M), C)"),
					arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«frobenius»"),
					r)))
		inverted := arg.Have(
			"inversion does not change the sum over H",
			"nat_sum(H, λg:permutation(A). card(«movedAs»(permutation_inverse(g)))) = "+
				"nat_sum(H, λg:permutation(A). card(«movedAs»(g)))",
			By(
				groupOn,
				subgroup,
				twisted_counting.SubgroupSumInverse.At(
					groupTerm,
					H,
					arg.TermAs[Fun[symmetric_group.Permutation[A], Nat]]("λg:permutation(A). card(«movedAs»(g))"))))
		termwise := arg.Have(
			"the count twisted by s is the number of rational points moved as its inverse",
			Statement{
				Binders:    "∀s:permutation(A).",
				Hypotheses: []string{"s ∈ H"},
				Conclusion: "twisted_evaluation_count(M, k, C, card(k) ^ m, s) = " +
					"card(«movedAs»(permutation_inverse(s)))",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				sIn := b.Assume()
				inGroup := b.Have(
					"s lies in the group",
					"s ∈ «G»",
					By(sIn, inG))
				b.Show(
					"the twisted evaluations are those moved rational points",
					Simp(Fwd(TwistedEvaluationCountDef)),
					GroupPremises(
						good, positive, inGroup, TwistedEvaluationsAreMoved.Read(M).At(k, L, t, C, a, m, s)).Rw(),
					Basic())
			}))
		sameSum := arg.Have(
			"so the sum of the counts is the sum over the inverses",
			"nat_sum(H, λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)) = "+
				"nat_sum(H, λg:permutation(A). card(«movedAs»(permutation_inverse(g))))",
			By(
				termwise,
				nat_sum.Congruence.At(
					H,
					arg.TermAs[Fun[symmetric_group.Permutation[A], Nat]](
						"λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)"),
					arg.TermAs[Fun[symmetric_group.Permutation[A], Nat]](
						"λg:permutation(A). card(«movedAs»(permutation_inverse(g)))"))))
		arg.Show(
			"the three equations chain",
			By(sameSum, inverted, movedSum))
	}),
})}

// GoodActionKeepsT — the automorphism group does not move the value at t: it
// and the inverses of its elements fix t, a point of the chart.
var GoodActionKeepsT = goodActionKeepsTThm{family.Add(registry.ProofEntry{
	Name: "GoodActionKeepsT",
	Key:  "prop_ee7571cdf885ce3f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀s:permutation(A). " +
			"∀ev:(A → A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "evaluation_action(field_ring(M), C, s, ev, t) = ev(t)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		s *Expr[symmetric_group.Permutation[A]],
		ev *Arrow[A, A],
		good, sIn Fact,
	) {
		ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
		fixes := arg.Have(
			"s fixes t",
			"permutation_map(s, t) = t",
			By(good, sIn, GoodGroupFixesChartData.Read(M).At(k, L, t, C, a, s)))
		inverseFixes := arg.Have(
			"so its inverse does",
			"permutation_map(permutation_inverse(s), t) = t",
			By(Normalized, fixes, symmetric_group.MapInverse.At(s, t)))
		arg.Show(
			"the action reads ev at the inverse of s, and t lies in the chart",
			By(
				Normalized,
				good,
				galois_good_open.GoodOpenParameterInChart.Read(M).At(k, L, C, t, a),
				inverseFixes,
				galois_good_open.EvaluationActionDef.At(ringM, C, s, ev, t)))
	}),
})}

// GoodFibreTwistCountOverBase — summed over the whole automorphism group, the
// twisted evaluations number the group's size for each good base point fixed by
// the power: the value at t tells the orbits of the group apart, the fibres
// being torsors, and every good base point is hit, its fibre having as many
// points as the group.
var GoodFibreTwistCountOverBase = goodFibreTwistCountOverBaseThm{family.Add(registry.ProofEntry{
	Name: "GoodFibreTwistCountOverBase",
	Key:  "prop_3df5943eea1a5081",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀C:set(A). ∀a:(num → A). ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"0 < m",
		},
		Conclusion: "nat_sum(«G», " +
			"    λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)) = " +
			"card(«G») * good_base_count(field_ring(M), k, a, card(k) ^ m)",
		Abbrev: Abbrev{
			{Name: "G", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "rational", Text: "{ev:(A → A) | " +
				"    ev ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)}"},
			{Name: "fibre", Text: "λx:A. geometric_fibre(M, k, C, t, x)"},
			{Name: "good", Text: "{x:A | " +
				"    x ∈ M.carrier ∧ " +
				"    monoid_pow(M.mul, M.one, x, card(k) ^ m) = x ∧ " +
				"    polynomial_eval(a, x) ≠ M.zero}"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		m *Expr[Nat],
		closedField, good, positive Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
		G := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«G»")
		order := arg.TermAs[Nat]("card(k)")
		power := arg.TermAs[Nat]("card(k) ^ m")
		fibreMember := arg.Have(
			"a map lies on the fibre over x when it is a geometric point sending t to x",
			"∀x:A. ∀ev:(A → A). ev ∈ «fibre»(x) ⇔ ev ∈ geometric_evaluation_points(M, k, C) ∧ ev(t) = x",
			BySets(galois_good_open.GeometricFibreDef))
		subfieldK := galois_good_open.GoodOpenConstantsSubfield.Read(good)
		free := arg.Have(
			"the group acts freely on the rational points",
			"free_finite_action(galois_group(M, field_adjoin(M, k, {t}), L), "+
				"    «rational», "+
				"    evaluation_action(field_ring(M), C))",
			By(closedField, good, positive, RationalPointsFreeAction.Read(M).At(k, L, t, C, a, m)))
		facts := arg.Conjuncts(
			arg.Unfolded(free, twisted_counting.FreeFiniteActionDef),
			"the group is a group on its set",
			"which is finite",
			"the rational points are finite",
			"the identity acts trivially",
			"the action laws")
		groupOn, finiteG := facts[0], facts[1]
		subgroupG := arg.Have(
			"the whole group is a subgroup of itself",
			"subgroup(galois_group(M, field_adjoin(M, k, {t}), L), «G»)",
			By(group.CarrierSubgroupOn.Read(groupOn)))
		separates := arg.Have(
			"two rational points have one value at t exactly when the group moves one to the other",
			Statement{
				Binders:    "∀ev ew:(A → A).",
				Hypotheses: []string{"ev ∈ «rational»", "ew ∈ «rational»"},
				Conclusion: "ev(t) = ew(t) ⇔ " +
					"∃h:permutation(A). h ∈ «G» ∧ evaluation_action(field_ring(M), C, h, ev) = ew",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				ew := b.FixAs[Fun[A, A]]("ew")
				given := b.Conjuncts(
					b.Assume(),
					"ev is rational",
					"ew is rational")
				b.Iff()
				b.Forward(
					"both lie on the fibre over that value, a torsor",
					func(c *Argument, same Fact) {
						over := c.Conjuncts(
							GroupPremises(good, given[0], RationalPointOverGoodBase.Read(M).At(k, L, t, C, a, m, ev)),
							"ev lies on its fibre",
							"its value at t is algebraic",
							"the power fixes it",
							"a does not vanish there")
						sameFibre := c.Have(
							"ew lies on the fibre through ev",
							"ew ∈ «fibre»(ev(t))",
							BySets(same, given[1], fibreMember.At(c.TermAs[A]("ev(t)"), ew)))
						torsor := galois_good_open.ReadGoodFibre(c, good, c.TermAs[A]("ev(t)"), over[1], over[3])
						c.Show(
							"any two of its points are translates",
							By(over[0], sameFibre, torsor.Transitive.At(ev, ew)))
					})
				b.Backward(
					"the group does not move the value at t",
					func(c *Argument, translated Fact) {
						h, moved := c.UnpackAs[symmetric_group.Permutation[A]](translated, "h")
						parts := c.Conjuncts(
							moved,
							"h lies in the group",
							"h moves ev to ew")
						c.Show(
							"ew(t) is the value at t of a translate of ev",
							By(Normalized, good, parts[0], parts[1], GoodActionKeepsT.Read(M).At(k, L, t, C, a, h, ev)))
					})
			}))
		notOne := arg.Have(
			"the power exceeds one, so it is not one",
			"card(k) ^ m ≠ 1",
			ByArith(
				subfieldK,
				galois_good_open.GoodOpenConstantsFinite.Read(good),
				positive,
				finite_field.FiniteSubfieldPowerEndomorphism.Read(M).At(k, m)))
		hit := arg.Have(
			"the values at t of rational points are the good points fixed by the power",
			"∀x:A. "+
				"    (∃ev:(A → A). "+
				"        (ev ∈ «rational» ∧ monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)) ∧ x = ev(t)) ⇔ "+
				"    x ∈ «good»",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				b.Iff()
				b.Forward(
					"a rational point lies over a good base point",
					func(c *Argument, valued Fact) {
						ev, onIt := c.UnpackAs[Fun[A, A]](valued, "ev")
						parts := c.Conjuncts(
							onIt,
							"ev is rational",
							"its value at t is fixed",
							"that value is x")
						c.Show(
							"so x lies in M, is fixed by the power, and a does not vanish there",
							BySets(
								parts[2],
								GroupPremises(good, parts[0], RationalPointOverGoodBase.Read(M).At(k, L, t, C, a, m, ev)),
								algebraic_element.AlgebraicElementsDef.At(fieldM, k)))
					})
				b.Backward(
					"a good point has a fibre as large as the group, so a point on it",
					func(c *Argument, inGood Fact) {
						facts := c.Conjuncts(
							c.Have(
								"x is a point of M fixed by the power, where a does not vanish",
								"x ∈ M.carrier ∧ monoid_pow(M.mul, M.one, x, card(k) ^ m) = x ∧ polynomial_eval(a, x) ≠ M.zero",
								BySets(inGood)),
							"x lies in M",
							"the power fixes x",
							"a does not vanish at x")
						fixedPoint := c.Have(
							"x is a fixed point of the power",
							"x ∈ finite_constants(field_ring(M), card(k), m)",
							BySets(facts[0], facts[1], finite_field.FiniteConstantsDef.At(ringM, order, m)))
						algebraic := c.Have(
							"so it is algebraic over k",
							"algebraic_over(M, k, x)",
							By(subfieldK, notOne, fixedPoint, finite_field.FiniteConstantsAlgebraic.Read(M).At(k, order, m, x)))
						goodBase := c.Have(
							"so x is a good base point",
							"x ∈ algebraic_elements(M, k) ∧ polynomial_eval(a, x) ≠ M.zero",
							BySets(facts[0], algebraic, facts[2], algebraic_element.AlgebraicElementsDef.At(fieldM, k)))
						torsor := galois_good_open.ReadGoodFibre(c, good, x, goodBase)
						finiteFibre := c.Have(
							"the fibre is finite",
							"finite(«fibre»(x))",
							By(c.Unfolded(torsor.Free, twisted_counting.FreeFiniteActionDef)))
						points := c.TermAs[Set[Fun[A, A]]]("«fibre»(x)")
						nonempty := c.Have(
							"and not empty, the group holding the identity",
							"«fibre»(x) ≠ ∅",
							Derive(func(d *Argument) {
								empty := d.SupposeNot()
								sizeZero := d.Have(
									"the fibre would have no points",
									"card(«fibre»(x)) = 0",
									By(empty, finiteFibre, cardinality.CardEqZero.At(points)))
								emptyGroup := d.Have(
									"so neither would the group",
									"«G» = ∅",
									By(sizeZero, torsor.Card, finiteG, cardinality.CardEqZero.At(G)))
								d.Show(
									"but the group holds its identity",
									BySets(emptyGroup, group.OneIn.Read(groupOn)))
							}))
						ev, onFibre := c.ObtainAs[Fun[A, A]](
							"so the fibre holds a point",
							"∃ev:(A → A). ev ∈ «fibre»(x)",
							BySets(nonempty))
						c.Take(ev)
						c.Show(
							"which is rational, x being fixed by the power",
							BySets(onFibre, facts[1], fibreMember.At(x, ev)))
					})
			}))
		values := arg.Have(
			"so the values of the rational points are the good points",
			"{ev(t) | ev:(A → A) | ev ∈ «rational» ∧ monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)} = "+
				"«good»",
			BySets(hit))
		counted := arg.Have(
			"the count read on the value at t",
			"nat_sum(«G», λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)) = "+
				"card(«G») * "+
				"card({ev(t) | "+
				"        ev:(A → A) | "+
				"        ev ∈ «rational» ∧ monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)})",
			By(
				closedField,
				good,
				subgroupG,
				positive,
				separates,
				TwistedEvaluationCountByInvariant.Read(M).At(
					k, L, t, C, a, G, m, arg.TermAs[Fun[Fun[A, A], A]]("λe:(A → A). e(t)"))))
		arg.Show(
			"and the good points are what the base count counts",
			By(arg.Simplified(counted, Fwd(values)), GoodBaseCountDef.At(ringM, k, a, power)))
	}),
})}

// GoodFibreTwistCountOverChart — summed over a subgroup H, the twisted
// evaluations number card(H) for each point of the invariant chart with values
// in the field of the power: restriction to the invariant chart tells the
// H-orbits apart, by the agreement clause of the good open; the restriction of
// a rational point is a point of the chart, with values fixed by the power
// exactly when the power map does not change it; and every such point comes by
// restriction from a point of the fibre under it, by the image clause.
var GoodFibreTwistCountOverChart = goodFibreTwistCountOverChartThm{family.Add(registry.ProofEntry{
	Name: "GoodFibreTwistCountOverChart",
	Key:  "prop_4c2ca21920b08205",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀H:set(permutation(A)). " +
			"∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, field_adjoin(M, k, {t}), L), H)",
			"0 < m",
		},
		Conclusion: "nat_sum(H, λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)) = " +
			"card(H) * card(«chartPoints»)",
		Abbrev: Abbrev{
			{Name: "G", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "rational", Text: "{ev:(A → A) | " +
				"    ev ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    monoid_pow(M.mul, M.one, ev(t), card(k) ^ m) = ev(t)}"},
			{Name: "frobenius", Text: "λev:(A → A). λy:A. monoid_pow(M.mul, M.one, ev(y), card(k) ^ m)"},
			{Name: "fibre", Text: "λx:A. geometric_fibre(M, k, C, t, x)"},
			{Name: "restriction", Text: "λev:(A → A). λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero)"},
			{Name: "invariant", Text: "restrict_ring(field_ring(M), invariant_chart(C, H))"},
			{Name: "closed", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
			{Name: "constantRing", Text: "restrict_ring(field_ring(M), " +
				"    finite_constants(field_ring(M), card(k), m))"},
			{Name: "chartPoints", Text: "algebra_points(«invariant», «constantRing», k, λx:A. x)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		m *Expr[Nat],
		closedField, good, subgroup, positive Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
		order := arg.TermAs[Nat]("card(k)")
		invariantChart := arg.TermAs[Set[A]]("invariant_chart(C, H)")
		invariant := arg.TermAs[RingOps[A]]("«invariant»")
		constantRing := arg.TermAs[RingOps[A]]("«constantRing»")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		fixedSet := arg.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), m)")
		identity := arg.TermAs[Fun[A, A]]("λx:A. x")
		groupTerm := arg.TermAs[group.GroupOps[symmetric_group.Permutation[A]]](
			"galois_group(M, field_adjoin(M, k, {t}), L)")
		restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		fibreMember := arg.Have(
			"a map lies on the fibre over x when it is a geometric point sending t to x",
			"∀x:A. ∀ev:(A → A). ev ∈ «fibre»(x) ⇔ ev ∈ geometric_evaluation_points(M, k, C) ∧ ev(t) = x",
			BySets(galois_good_open.GeometricFibreDef))
		invariantFibreMember := arg.Have(
			"a map lies on the fibre of the invariant chart over z when it "+
				"is a point of that chart with algebraic values sending t to z",
			"∀z:A. ∀f:(A → A). "+
				"    f ∈ geometric_fibre(M, k, invariant_chart(C, H), t, z) ⇔ "+
				"    f ∈ algebra_points(«invariant», «closed», k, λx:A. x) ∧ f(t) = z",
			BySets(
				galois_good_open.GeometricFibreDef,
				galois_good_open.GeometricEvaluationPointsDef.At(fieldM, k, invariantChart)))
		subfieldK := arg.Have(
			"k is a subfield",
			"subfield(M, k)",
			By(galois_good_open.GoodOpenConstantsSubfield.Read(good)))
		finiteK := arg.Have(
			"k is finite",
			"finite(k)",
			By(galois_good_open.GoodOpenConstantsFinite.Read(good)))
		inG := arg.Have(
			"H lies in the group",
			"∀h:permutation(A). h ∈ H ⇒ h ∈ «G»",
			BySets(subgroup, group.SubgroupSubset.At(groupTerm, H)))
		fixed := arg.Have(
			"H fixes the constants, t and the inverse of a(t)",
			Statement{
				Binders:    "∀s:permutation(A).",
				Hypotheses: []string{"s ∈ H"},
				Conclusion: "(∀x:A. x ∈ k ⇒ permutation_map(s, x) = x) ∧ " +
					"permutation_map(s, t) = t ∧ " +
					"permutation_map(s, M.inv(polynomial_eval(a, t))) = M.inv(polynomial_eval(a, t))",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				sIn := b.Assume()
				inGroup := b.Have(
					"s lies in the group",
					"s ∈ «G»",
					By(sIn, inG))
				b.Show(
					"which fixes them",
					By(good, inGroup, GoodGroupFixesChartData.Read(M).At(k, L, t, C, a, s)))
			}))
		inChart := arg.Have(
			"the invariant chart is the part of the chart H fixes",
			"∀x:A. x ∈ invariant_chart(C, H) ⇔ x ∈ C ∧ (∀s:permutation(A). s ∈ H ⇒ permutation_map(s, x) = x)",
			BySets(galois_good_open.InvariantChartDef.At(C, H)))
		chartData := arg.Have(
			"so it holds the constants, t and the inverse of a(t)",
			"k ⊆ invariant_chart(C, H) ∧ "+
				"t ∈ invariant_chart(C, H) ∧ "+
				"M.inv(polynomial_eval(a, t)) ∈ invariant_chart(C, H)",
			BySets(
				good,
				galois_good_open.GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a),
				galois_good_open.GoodOpenParameterInChart.Read(M).At(k, L, C, t, a),
				galois_good_open.GoodOpenDenominatorInverseInChart.Read(M).At(k, L, C, t, a),
				fixed,
				inChart))
		onChart := arg.Conjuncts(
			chartData,
			"the invariant chart holds k",
			"it holds t",
			"it holds the inverse of a(t)")
		kInD, tInD, inverseInD := onChart[0], onChart[1], onChart[2]
		separates := arg.Have(
			"two rational points have one restriction to the "+
				"invariant chart exactly when H moves one to the other",
			Statement{
				Binders:    "∀ev ew:(A → A).",
				Hypotheses: []string{"ev ∈ «rational»", "ew ∈ «rational»"},
				Conclusion: "«restriction»(ev) = «restriction»(ew) ⇔ " +
					"∃h:permutation(A). h ∈ H ∧ evaluation_action(field_ring(M), C, h, ev) = ew",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				ew := b.FixAs[Fun[A, A]]("ew")
				given := b.Conjuncts(
					b.Assume(),
					"ev is rational",
					"ew is rational")
				over := b.Conjuncts(
					GroupPremises(good, given[0], RationalPointOverGoodBase.Read(M).At(k, L, t, C, a, m, ev)),
					"ev lies on its fibre",
					"its value at t is algebraic",
					"the power fixes it",
					"a does not vanish there")
				torsor := galois_good_open.ReadGoodFibre(b, good, b.TermAs[A]("ev(t)"), over[1], over[3])
				readings := b.Conjuncts(
					GroupPremises(subgroup, torsor.Quotients.At(H)),
					"restriction carries the fibre onto the points of the invariant chart over ev(t)",
					"points of the fibre agree on the invariant chart exactly when H moves one to the other")
				agreement := readings[1]
				b.Iff()
				b.Forward(
					"one restriction means agreement on the invariant chart, which holds t",
					func(c *Argument, same Fact) {
						agree := c.Have(
							"ev and ew agree on the invariant chart",
							"∀y:A. y ∈ invariant_chart(C, H) ⇒ ev(y) = ew(y)",
							Derive(func(d *Argument) {
								d.FixAs[A]("y")
								yIn := d.Assume()
								d.Show(
									"the restrictions are ev and ew there",
									By(yIn, same))
							}))
						atT := c.Have(
							"so they agree at t",
							"ev(t) = ew(t)",
							By(tInD, agree.At(t)))
						sameFibre := c.Have(
							"and ew lies on the fibre through ev",
							"ew ∈ «fibre»(ev(t))",
							BySets(atT, given[1], fibreMember.At(c.TermAs[A]("ev(t)"), ew)))
						c.Show(
							"the agreement clause gives the element of H",
							By(over[0], sameFibre, agree, agreement.At(ev, ew)))
					})
				b.Backward(
					"an element of H keeps the fibre and moves nothing on the invariant chart",
					func(c *Argument, translated Fact) {
						h, moved := c.UnpackAs[symmetric_group.Permutation[A]](translated, "h")
						parts := c.Conjuncts(
							moved,
							"h lies in H",
							"h moves ev to ew")
						inGroup := c.Have(
							"h lies in the group",
							"h ∈ «G»",
							By(parts[0], inG))
						atT := c.Have(
							"which keeps the value at t",
							"ev(t) = ew(t)",
							By(Normalized, good, inGroup, parts[1], GoodActionKeepsT.Read(M).At(k, L, t, C, a, h, ev)))
						sameFibre := c.Have(
							"so ew lies on the fibre through ev",
							"ew ∈ «fibre»(ev(t))",
							BySets(atT, given[1], fibreMember.At(c.TermAs[A]("ev(t)"), ew)))
						agree := c.Have(
							"and the agreement clause makes them agree on the invariant chart",
							"∀y:A. y ∈ invariant_chart(C, H) ⇒ ev(y) = ew(y)",
							By(over[0], sameFibre, translated, agreement.At(ev, ew)))
						c.Show(
							"so they have one restriction",
							Funext(),
							Derive(func(d *Argument) {
								y := d.FixAs[A]("y")
								d.Cases(d.Term("y ∈ invariant_chart(C, H)"))
								d.When(
									"on the invariant chart they agree",
									func(e *Argument, inside Fact) {
										e.Show(
											"the restrictions are ev and ew there",
											By(inside, agree.At(y)))
									})
								d.Otherwise(
									"off it both restrictions vanish",
									func(e *Argument, outside Fact) {
										e.Show(
											"by definition",
											By(outside))
									})
							}))
					})
			}))
		counted := arg.Have(
			"the count read on the restriction",
			"nat_sum(H, λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)) = "+
				"card(H) * "+
				"card({«restriction»(ev) | "+
				"        ev:(A → A) | "+
				"        ev ∈ «rational» ∧ «restriction»(«frobenius»(ev)) = «restriction»(ev)})",
			By(
				closedField,
				good,
				subgroup,
				positive,
				separates,
				TwistedEvaluationCountByInvariant.Read(M).At(k, L, t, C, a, H, m, restriction)))
		subringFixed := arg.Have(
			"the fixed points of the power form a subfield, so a subring",
			"subring(field_ring(M), finite_constants(field_ring(M), card(k), m))",
			By(
				closedField,
				subfieldK,
				finiteK,
				positive,
				finite_field.FiniteConstantsSubfield.Read(M).At(k, m),
				field.SubfieldSubring.Read(M)))
		subringClosure := arg.Have(
			"the algebraic points form a subfield, so a subring",
			"subring(field_ring(M), algebraic_elements(M, k))",
			By(
				subfieldK,
				algebraic_element.AlgebraicElementsSubfield.Read(M).At(k),
				field.SubfieldSubring.Read(M)))
		notOne := arg.Have(
			"the power exceeds one, so it is not one",
			"card(k) ^ m ≠ 1",
			ByArith(
				subfieldK,
				finiteK,
				positive,
				finite_field.FiniteSubfieldPowerEndomorphism.Read(M).At(k, m)))
		fixedIff := arg.Have(
			"the fixed points are the points of M the power fixes",
			"∀y:A. "+
				"    y ∈ finite_constants(field_ring(M), card(k), m) ⇔ "+
				"    y ∈ M.carrier ∧ monoid_pow(M.mul, M.one, y, card(k) ^ m) = y",
			BySets(finite_field.FiniteConstantsDef.At(ringM, order, m)))
		fixedInside := arg.Have(
			"they lie in M",
			"finite_constants(field_ring(M), card(k), m) ⊆ M.carrier",
			BySets(fixedIff))
		closureInside := arg.Have(
			"as do the algebraic points",
			"algebraic_elements(M, k) ⊆ M.carrier",
			BySets(algebraic_element.AlgebraicElementsDef.At(fieldM, k)))
		fixedAlgebraic := arg.Have(
			"a point fixed by the power is algebraic over k",
			"∀y:A. y ∈ finite_constants(field_ring(M), card(k), m) ⇒ y ∈ algebraic_elements(M, k)",
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				yIn := b.Assume()
				algebraic := b.Have(
					"the power not being one",
					"algebraic_over(M, k, y)",
					By(subfieldK, notOne, yIn, finite_field.FiniteConstantsAlgebraic.Read(M).At(k, order, m, y)))
				b.Show(
					"and it lies in M",
					BySets(yIn, algebraic, fixedIff, algebraic_element.AlgebraicElementsDef.At(fieldM, k)))
			}))
		hit := arg.Have(
			"the restrictions the power map does not change are the "+
				"points of the invariant chart with values fixed by the power",
			"∀e:(A → A). "+
				"    (∃ev:(A → A). "+
				"        (ev ∈ «rational» ∧ «restriction»(«frobenius»(ev)) = «restriction»(ev)) ∧ "+
				"        e = «restriction»(ev)) ⇔ "+
				"    e ∈ «chartPoints»",
			Derive(func(b *Argument) {
				e := b.FixAs[Fun[A, A]]("e")
				b.Iff()
				b.Forward(
					"a restriction is a point of the invariant chart, with values "+
						"fixed by the power when the power map does not change it",
					func(c *Argument, stable Fact) {
						ev, onIt := c.UnpackAs[Fun[A, A]](stable, "ev")
						parts := c.Conjuncts(
							onIt,
							"ev is rational",
							"the power map does not change its restriction",
							"e is that restriction")
						over := c.Conjuncts(
							GroupPremises(good, parts[0], RationalPointOverGoodBase.Read(M).At(k, L, t, C, a, m, ev)),
							"ev lies on its fibre",
							"its value at t is algebraic",
							"the power fixes it",
							"a does not vanish there")
						torsor := galois_good_open.ReadGoodFibre(c, good, c.TermAs[A]("ev(t)"), over[1], over[3])
						readings := c.Conjuncts(
							GroupPremises(subgroup, torsor.Quotients.At(H)),
							"restriction carries the fibre onto the points of the invariant chart over ev(t)",
							"points of the fibre agree on the invariant chart exactly when H moves one to the other")
						restricted := c.TermAs[Fun[A, A]]("«restriction»(ev)")
						inImage := c.Have(
							"the restriction of ev lies in the image of the fibre",
							"«restriction»(ev) ∈ image(«restriction», «fibre»(ev(t)))",
							By(over[0], set_image.FunInImage.At(restriction, c.TermAs[Set[Fun[A, A]]]("«fibre»(ev(t))"), ev)))
						chartPoint := c.Have(
							"so it is a point of the invariant chart with algebraic values",
							"«restriction»(ev) ∈ algebra_points(«invariant», «closed», k, λx:A. x)",
							BySets(
								c.Simplified(inImage, Fwd(readings[0])),
								invariantFibreMember.At(c.TermAs[A]("ev(t)"), restricted)))
						ringMap := c.Have(
							"so it is a ring map to the algebraic points",
							"ring_homomorphism(«invariant», «closed», «restriction»(ev))",
							By(
								chartPoint,
								algebra_points.AlgebraPointsMember.At(
									invariant, c.TermAs[RingOps[A]]("«closed»"), k, identity, restricted)))
						valuesFixed := c.Have(
							"its values are fixed by the power",
							Statement{
								Binders: "∀y:A.",
								Hypotheses: []string{
									"y ∈ invariant_chart(C, H)",
								},
								Conclusion: "«restriction»(ev, y) ∈ finite_constants(field_ring(M), card(k), m)",
							},
							Derive(func(d *Argument) {
								y := d.FixAs[A]("y")
								yIn := d.Assume()
								inClosure := d.Have(
									"the value at y is algebraic",
									"«restriction»(ev, y) ∈ algebraic_elements(M, k)",
									By(yIn, ring_homomorphism.MapIn.Read(ringMap).AsFact().At(y)))
								power := d.Have(
									"and the power map does not change it",
									"monoid_pow(M.mul, M.one, «restriction»(ev, y), card(k) ^ m) = «restriction»(ev, y)",
									By(yIn, parts[1]))
								d.Show(
									"so it is a point of M fixed by the power",
									BySets(inClosure, power, fixedIff, algebraic_element.AlgebraicElementsDef.At(fieldM, k)))
							}))
						point := c.Have(
							"so it is a point with values fixed by the power",
							"«restriction»(ev) ∈ «chartPoints»",
							By(
								field.RingOn.Read(M),
								closureInside,
								subringFixed,
								valuesFixed,
								chartPoint,
								algebra_points.AlgebraPointsChangeTarget.At(
									ringM, invariant, k, identity, restricted, closure, fixedSet)))
						c.Show(
							"and e is that restriction",
							parts[2].Rw(),
							By(point))
					})
				b.Backward(
					"a point of the invariant chart lifts to the fibre under it, and its values are fixed by the power",
					func(c *Argument, inPoints Fact) {
						opened := c.Conjuncts(
							c.Have(
								"e is a ring map to the fixed points, vanishing off the invariant chart",
								"ring_homomorphism(«invariant», «constantRing», e) ∧ "+
									"(∀y:A. y ∉ invariant_chart(C, H) ⇒ e(y) = M.zero)",
								By(inPoints, algebra_points.AlgebraPointsMember.At(invariant, constantRing, k, identity, e))),
							"e is a ring map to the fixed points",
							"e vanishes off the invariant chart")
						ringMap := opened[0]
						valuesFixed := c.Have(
							"its values on the invariant chart are fixed by the power",
							"∀y:A. y ∈ invariant_chart(C, H) ⇒ e(y) ∈ finite_constants(field_ring(M), card(k), m)",
							Derive(func(d *Argument) {
								y := d.FixAs[A]("y")
								yIn := d.Assume()
								d.Show(
									"it is a ring map to them",
									By(yIn, ring_homomorphism.MapIn.Read(ringMap).AsFact().At(y)))
							}))
						valuesClosed := c.Have(
							"so they are algebraic",
							"∀y:A. y ∈ invariant_chart(C, H) ⇒ e(y) ∈ algebraic_elements(M, k)",
							Derive(func(d *Argument) {
								y := d.FixAs[A]("y")
								yIn := d.Assume()
								d.Show(
									"a point fixed by the power is algebraic",
									By(yIn, valuesFixed.At(y), fixedAlgebraic.At(d.TermAs[A]("e(y)"))))
							}))
						keepsDenominator := c.Have(
							"e does not kill a(t), whose inverse lies in the invariant chart",
							"polynomial_eval(a, e(t)) ≠ M.zero",
							By(
								good,
								kInD,
								tInD,
								inverseInD,
								inPoints,
								GoodPointKeepsDenominator.Read(M).At(k, L, t, C, a, invariantChart, fixedSet, e)))
						closurePoint := c.Have(
							"e is a point of the invariant chart with algebraic values",
							"e ∈ algebra_points(«invariant», «closed», k, λx:A. x)",
							By(
								field.RingOn.Read(M),
								fixedInside,
								subringClosure,
								valuesClosed,
								inPoints,
								algebra_points.AlgebraPointsChangeTarget.At(ringM, invariant, k, identity, e, fixedSet, closure)))
						goodBase := c.Have(
							"e(t) is a good base point",
							"e(t) ∈ algebraic_elements(M, k) ∧ polynomial_eval(a, e(t)) ≠ M.zero",
							By(tInD, valuesClosed.At(t), keepsDenominator))
						torsor := galois_good_open.ReadGoodFibre(c, good, c.TermAs[A]("e(t)"), goodBase)
						readings := c.Conjuncts(
							GroupPremises(subgroup, torsor.Quotients.At(H)),
							"restriction carries the fibre onto the points of the invariant chart over e(t)",
							"points of the fibre agree on the invariant chart exactly when H moves one to the other")
						onItself := c.Have(
							"e is a point of the invariant chart over e(t)",
							"e ∈ geometric_fibre(M, k, invariant_chart(C, H), t, e(t))",
							By(closurePoint, invariantFibreMember.At(c.TermAs[A]("e(t)"), e)))
						inImage := c.Have(
							"so e lies in the image of the fibre under it",
							"e ∈ image(«restriction», «fibre»(e(t)))",
							readings[0].Rw(),
							By(onItself))
						ev, lifted := c.ObtainAs[Fun[A, A]](
							"so e is the restriction of a point of that fibre",
							"∃ev:(A → A). e = «restriction»(ev) ∧ ev ∈ «fibre»(e(t))",
							By(inImage, set_basic.InImage.At(restriction, c.TermAs[Set[Fun[A, A]]]("«fibre»(e(t))"), e)))
						parts := c.Conjuncts(
							lifted,
							"e is the restriction of ev",
							"ev lies on the fibre under e")
						fixedAtT := c.Have(
							"the power fixes e(t)",
							"monoid_pow(M.mul, M.one, e(t), card(k) ^ m) = e(t)",
							By(tInD, valuesFixed.At(t), fixedIff.At(c.TermAs[A]("e(t)"))))
						rational := c.Have(
							"so ev is rational",
							"ev ∈ «rational»",
							BySets(parts[1], fixedAtT, fibreMember.At(c.TermAs[A]("e(t)"), ev)))
						unchanged := c.Have(
							"and the power map does not change its restriction, the values of e being fixed",
							"«restriction»(«frobenius»(ev)) = «restriction»(ev)",
							Funext(),
							Derive(func(d *Argument) {
								y := d.FixAs[A]("y")
								d.Cases(d.Term("y ∈ invariant_chart(C, H)"))
								d.When(
									"on the invariant chart ev is e, whose values are fixed",
									func(g *Argument, inside Fact) {
										value := g.Have(
											"e(y) is the value of ev at y",
											"e(y) = ev(y)",
											By(inside, parts[0]))
										fixedValue := g.Have(
											"which the power fixes",
											"monoid_pow(M.mul, M.one, e(y), card(k) ^ m) = e(y)",
											By(inside, valuesFixed.At(y), fixedIff.At(g.TermAs[A]("e(y)"))))
										g.Show(
											"the restriction of the power is the power of the restriction",
											By(Normalized, inside, value, fixedValue))
									})
								d.Otherwise(
									"off it both restrictions vanish",
									func(g *Argument, outside Fact) {
										g.Show(
											"by definition",
											By(outside))
									})
							}))
						c.Take(ev)
						c.Show(
							"so ev is the rational point we want",
							By(rational, unchanged, parts[0]))
					})
			}))
		values := arg.Have(
			"so the stable restrictions are the points of the invariant chart with values fixed by the power",
			"{«restriction»(ev) | "+
				"    ev:(A → A) | "+
				"    ev ∈ «rational» ∧ «restriction»(«frobenius»(ev)) = «restriction»(ev)} = "+
				"«chartPoints»",
			BySets(hit))
		arg.Show(
			"which turns the count into the count of those points",
			By(arg.Simplified(counted, Fwd(values))))
	}),
})}

// GoodFibreTwistCounting — the exact good-fibre counts over a finite field: the
// twisted evaluations of the Frobenius power, summed over the automorphism
// group, count the good base points the power fixes; summed over a subgroup H,
// they count the points of the invariant chart with values in the field of the
// power. Both are the fixed-orbit formula for the free action on the rational
// points, read on the invariant that tells the orbits apart: the value at t for
// the whole group, the restriction to the invariant chart for H.
var GoodFibreTwistCounting = goodFibreTwistCountingThm{family.Add(registry.ProofEntry{
	Name: "GoodFibreTwistCounting",
	Key:  "prop_16e9fedb14421293",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k L:set(A). " +
			"∀t:A. " +
			"∀C:set(A). " +
			"∀a:(num → A). " +
			"∀H:set(permutation(A)). " +
			"∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"subgroup(galois_group(M, field_adjoin(M, k, {t}), L), H)",
			"0 < m",
		},
		Conclusion: "nat_sum(field_automorphisms(M, field_adjoin(M, k, {t}), L), " +
			"    λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)) = " +
			"card(field_automorphisms(M, field_adjoin(M, k, {t}), L)) * " +
			"good_base_count(field_ring(M), k, a, card(k) ^ m) ∧ " +
			"nat_sum(H, λs:permutation(A). twisted_evaluation_count(M, k, C, card(k) ^ m, s)) = " +
			"card(H) * " +
			"card(algebra_points(restrict_ring(field_ring(M), invariant_chart(C, H)), " +
			"        restrict_ring(field_ring(M), finite_constants(field_ring(M), card(k), m)), " +
			"        k, " +
			"        λx:A. x))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		C *Expr[Set[A]],
		a *Arrow[Nat, A],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		m *Expr[Nat],
		closedField, good, subgroup, positive Fact,
	) {
		arg.Show(
			"the whole group counts the good base points, and H the points of its invariant chart",
			By(
				closedField,
				good,
				subgroup,
				positive,
				GoodFibreTwistCountOverBase.Read(M).At(k, L, t, C, a, m),
				GoodFibreTwistCountOverChart.Read(M).At(k, L, t, C, a, H, m)))
	}),
})}
