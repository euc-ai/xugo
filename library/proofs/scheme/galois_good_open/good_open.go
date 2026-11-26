package galois_good_open

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// A good open read clause by clause
// ---------------------------------------------------------------------------

// GoodOpenRegular — the function field of a good open is regular over its
// constants k.
var GoodOpenRegular = goodOpenRegularThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenRegular",
	Key:   "prop_7f68e031dc3d2c0",
	Build: GaloisGoodOpenDef.Entry().Conjunct("regular_function_field(R, k, L)"),
})}

// GoodOpenConstantsFinite — the constants k of a good open are finite.
var GoodOpenConstantsFinite = goodOpenConstantsFiniteThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenConstantsFinite",
	Key:   "prop_6da45a382cb2ab0d",
	Build: GaloisGoodOpenDef.Entry().Conjunct("finite(k)"),
})}

// GoodOpenParameterIn — the parameter t of a good open lies in L.
var GoodOpenParameterIn = goodOpenParameterInThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenParameterIn",
	Key:   "prop_70775b30e062ecce",
	Build: GaloisGoodOpenDef.Entry().Conjunct("t ∈ L"),
})}

// GoodOpenParameterTranscendental — the parameter t of a good open is
// transcendental over k.
var GoodOpenParameterTranscendental = goodOpenParameterTranscendentalThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenParameterTranscendental",
	Key:   "prop_9ecf62351584aa92",
	Build: GaloisGoodOpenDef.Entry().Conjunct("¬algebraic_over(R, k, t)"),
})}

// GoodOpenGalois — L is Galois over k(t).
var GoodOpenGalois = goodOpenGaloisThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenGalois",
	Key:   "prop_f7458af68672427",
	Build: GaloisGoodOpenDef.Entry().Conjunct("galois_over(R, field_adjoin(R, k, {t}), L)"),
})}

// GoodOpenChartInField — the chart C lies in L.
var GoodOpenChartInField = goodOpenChartInFieldThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenChartInField",
	Key:   "prop_661b1de56ea307ee",
	Build: GaloisGoodOpenDef.Entry().Conjunct("C ⊆ L"),
})}

// GoodOpenChartRing — the chart C is a ring under the operations of the
// ambient field.
var GoodOpenChartRing = goodOpenChartRingThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenChartRing",
	Key:   "prop_bef3de1c9448d573",
	Build: GaloisGoodOpenDef.Entry().Conjunct("comm_ring_on(restrict_ring(field_ring(R), C))"),
})}

// GoodOpenDenominatorOver — the polynomial a whose value at t the chart
// inverts is a polynomial over k.
var GoodOpenDenominatorOver = goodOpenDenominatorOverThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenDenominatorOver",
	Key:   "prop_c68fc6a47622bc3",
	Build: GaloisGoodOpenDef.Entry().Conjunct("polynomial_over(R.zero, k, a)"),
})}

// GoodOpenDenominatorNonzero — the polynomial a is not the zero polynomial.
var GoodOpenDenominatorNonzero = goodOpenDenominatorNonzeroThm{family.Add(registry.ProofEntry{
	Name:  "GoodOpenDenominatorNonzero",
	Key:   "prop_31dcd9c4842294dc",
	Build: GaloisGoodOpenDef.Entry().Conjunct("a ≠ vec_zero(R.zero)"),
})}

// GoodOpenChartHoldsBase — the chart holds k[t] with a(t) inverted.
var GoodOpenChartHoldsBase = goodOpenChartHoldsBaseThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenChartHoldsBase",
	Key:  "prop_982d9041fd4f9ee8",
	Build: GaloisGoodOpenDef.Entry().Conjunct(
		"ring_away(field_ring(R), " +
			"    polynomial_image(field_ring(R), k, t), " +
			"    polynomial_eval(R.add, R.zero, R.mul, R.one, a, t)) ⊆ " +
			"C"),
})}

// GoodOpenChartInverts — the chart is its own localization at a(t): it
// already inverts a(t).
var GoodOpenChartInverts = goodOpenChartInvertsThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenChartInverts",
	Key:  "prop_c6d068b1455e048a",
	Build: GaloisGoodOpenDef.Entry().Conjunct(
		"C = ring_away(field_ring(R), C, polynomial_eval(R.add, R.zero, R.mul, R.one, a, t))"),
})}

// GoodOpenFractionField — L is the fraction field of the chart.
var GoodOpenFractionField = goodOpenFractionFieldThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenFractionField",
	Key:  "prop_69fd3a0cfd067240",
	Build: GaloisGoodOpenDef.Entry().Conjunct(
		"fraction_field_carrier(restrict_ring(field_ring(R), L), C)"),
})}

// GoodOpenChartFinite — the chart is a finite module over k[t] with a(t)
// inverted.
var GoodOpenChartFinite = goodOpenChartFiniteThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenChartFinite",
	Key:  "prop_26dee5a8a174efc7",
	Build: GaloisGoodOpenDef.Entry().Conjunct(
		"module_finitely_generated(restrict_ring(field_ring(R), " +
			"        ring_away(field_ring(R), " +
			"            polynomial_image(field_ring(R), k, t), " +
			"            polynomial_eval(R.add, R.zero, R.mul, R.one, a, t))), " +
			"    restrict_module(regular_module(field_ring(R)), C))"),
})}

// GoodOpenAutomorphismsKeepChart — every automorphism of L over k(t) maps
// the chart onto itself.
var GoodOpenAutomorphismsKeepChart = goodOpenAutomorphismsKeepChartThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenAutomorphismsKeepChart",
	Key:  "prop_3ec175bd7344cc9",
	Build: GaloisGoodOpenDef.Entry().Conjunct(Statement{
		Binders: "∀s:permutation(A).",
		Hypotheses: []string{
			"s ∈ field_automorphisms(R, field_adjoin(R, k, {t}), L)",
		},
		Conclusion: "image(permutation_map(s), C) = C",
	}),
})}

// GoodOpenFibresTorsors — over each algebraic point x with a(x) ≠ 0 the
// geometric fibre of the chart is a torsor of the group, and each subgroup's
// invariant chart reads its quotient off the fibre.
var GoodOpenFibresTorsors = goodOpenFibresTorsorsThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenFibresTorsors",
	Key:  "prop_4d2a8dda9832b22b",
	Build: GaloisGoodOpenDef.Entry().Conjunct(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ algebraic_elements(R, k)",
			"polynomial_eval(R.add, R.zero, R.mul, R.one, a, x) ≠ R.zero",
		},
		Conclusion: "free_finite_action(galois_group(R, field_adjoin(R, k, {t}), L), " +
			"    geometric_fibre(R, k, C, t, x), " +
			"    evaluation_action(field_ring(R), C)) ∧ " +
			"card(geometric_fibre(R, k, C, t, x)) = " +
			"card(field_automorphisms(R, field_adjoin(R, k, {t}), L)) ∧ " +
			"(∀ev ew:(A → A). " +
			"    ev ∈ geometric_fibre(R, k, C, t, x) ∧ ew ∈ geometric_fibre(R, k, C, t, x) ⇒ " +
			"    ∃s:permutation(A). " +
			"        s ∈ field_automorphisms(R, field_adjoin(R, k, {t}), L) ∧ " +
			"        evaluation_action(field_ring(R), C, s, ev) = ew) ∧ " +
			"(∀H:set(permutation(A)). " +
			"    subgroup(galois_group(R, field_adjoin(R, k, {t}), L), H) ⇒ " +
			"    image(λev:(A → A). λy:A. COND(y ∈ invariant_chart(C, H), ev(y), R.zero), " +
			"        geometric_fibre(R, k, C, t, x)) = " +
			"    geometric_fibre(R, k, invariant_chart(C, H), t, x) ∧ " +
			"    (∀ev ew:(A → A). " +
			"        ev ∈ geometric_fibre(R, k, C, t, x) ∧ ew ∈ geometric_fibre(R, k, C, t, x) ⇒ " +
			"        ((∀y:A. y ∈ invariant_chart(C, H) ⇒ ev(y) = ew(y)) ⇔ " +
			"            ∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(R), C, s, ev) = ew)))",
	}),
})}

// GoodFibre is the fibre clause of a good open read at a good base point x:
// the group acts freely on the fibre over x, the fibre has as many points as
// the group, any two of its points are translates, and the subgroups read
// their quotients off it.
type GoodFibre struct {
	Free, Card, Transitive, Quotients Fact
}

// ReadGoodFibre reads GoodOpenFibresTorsors at x, the goodBase facts
// discharging x ∈ algebraic_elements(M, k) and a(x) ≠ 0.
func ReadGoodFibre(a *Argument, good Fact, x *Expr[A], goodBase ...Fact) GoodFibre {
	listed := make([]any, 0, len(goodBase)+1)
	for _, f := range goodBase {
		listed = append(listed, f)
	}
	parts := a.Conjuncts(
		GroupPremises(append(listed, GoodOpenFibresTorsors.Read(good).At(x))...),
		"the group acts freely on the fibre",
		"the fibre has as many points as the group",
		"any two points of the fibre are translates",
		"the subgroups read off the fibre")
	return GoodFibre{parts[0], parts[1], parts[2], parts[3]}
}

// ---------------------------------------------------------------------------
// The derived facts of a good open
// ---------------------------------------------------------------------------

// GoodOpenConstantsSubfield — the constants k of a good open are a subfield.
var GoodOpenConstantsSubfield = goodOpenConstantsSubfieldThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenConstantsSubfield",
	Key:  "prop_54df3e7ee381583f",
	Build: GaloisGoodOpenDef.Entry().Law("subfield(R, k)",
		func(a *Argument, good Fact) {
			a.Show(
				"L is a regular function field over k, whose constants are a subfield",
				By(a.Unfolded(GoodOpenRegular.Read(good), function_field.RegularFunctionFieldDef)))
		}),
})}

// GoodOpenFieldSubfield — the function field L of a good open is a subfield.
var GoodOpenFieldSubfield = goodOpenFieldSubfieldThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenFieldSubfield",
	Key:  "prop_d44a7c6ac5f4c479",
	Build: GaloisGoodOpenDef.Entry().Law("subfield(R, L)",
		func(a *Argument, good Fact) {
			a.Show(
				"L is a regular function field over k, a subfield",
				By(a.Unfolded(GoodOpenRegular.Read(good), function_field.RegularFunctionFieldDef)))
		}),
})}

// GoodOpenConstantsInField — the constants k of a good open lie in L.
var GoodOpenConstantsInField = goodOpenConstantsInFieldThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenConstantsInField",
	Key:  "prop_83c22535b06ba7d6",
	Build: GaloisGoodOpenDef.Entry().Law("k ⊆ L",
		func(a *Argument, good Fact) {
			a.Show(
				"L is a regular function field over k, holding its constants",
				By(a.Unfolded(GoodOpenRegular.Read(good), function_field.RegularFunctionFieldDef)))
		}),
})}

// GoodParameterInField reads off a good open that its parameter t is a point
// of the field M: t lies in L, a subfield of M.
func GoodParameterInField(arg *Argument, t *Expr[A], good Fact) *Member[A, on.M] {
	return arg.MemberOf[on.M](t, arg.Have(
		"t lies in L, which lies in M",
		"t ∈ M.carrier",
		BySets(
			GoodOpenParameterIn.Read(good),
			field.SubfieldSubset.Read(GoodOpenFieldSubfield.Read(good)))))
}

// GoodOpenRationalSubfield — k(t) is a subfield on a good open: k is a
// subfield and t a point of the field.
var GoodOpenRationalSubfield = goodOpenRationalSubfieldThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenRationalSubfield",
	Key:  "prop_56dd3348e4176e2c",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "subfield(M, field_adjoin(M, k, {t}))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		tm := GoodParameterInField(arg, t, good)
		arg.Show(
			"so k(t) is a subfield, k being one",
			By(
				GoodOpenConstantsSubfield.Read(good),
				tm,
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)))
	}),
})}

// GoodOpenConstantsInRational — k(t) holds the constants k: k lies in every
// subfield holding k and t, so in their meet.
var GoodOpenConstantsInRational = goodOpenConstantsInRationalThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenConstantsInRational",
	Key:  "prop_1e06ecf2f9f205b4",
	Build: GaloisGoodOpenDef.Entry().Law("k ⊆ field_adjoin(R, k, {t})",
		func(a *Argument, _ Fact) {
			a.Show(
				"k lies in every subfield holding k and t, so in their meet",
				Unfold(algebraic_element.FieldAdjoinDef),
				BySets())
		}),
})}

// GoodOpenParameterInRational — k(t) holds the parameter t: t lies in every
// subfield holding k and t, so in their meet.
var GoodOpenParameterInRational = goodOpenParameterInRationalThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenParameterInRational",
	Key:  "prop_132fac89b2701899",
	Build: GaloisGoodOpenDef.Entry().Law("t ∈ field_adjoin(R, k, {t})",
		func(a *Argument, _ Fact) {
			a.Show(
				"t lies in every subfield holding k and t, so in their meet",
				Unfold(algebraic_element.FieldAdjoinDef),
				BySets())
		}),
})}

// GoodOpenRationalInField — k(t) lies in L: L is a subfield holding k and t,
// one of the subfields k(t) is the meet of.
var GoodOpenRationalInField = goodOpenRationalInFieldThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenRationalInField",
	Key:  "prop_3648bf4361e8893d",
	Build: GaloisGoodOpenDef.Entry().Law("field_adjoin(R, k, {t}) ⊆ L",
		func(a *Argument, good Fact) {
			member := a.Have(
				"L is a subfield holding k and t, one of the sets k(t) is the meet of",
				"L ∈ {N:set(A) | subfield(R, N) ∧ k ⊆ N ∧ {t} ⊆ N}",
				BySets(
					GoodOpenFieldSubfield.Read(good),
					GoodOpenConstantsInField.Read(good),
					GoodOpenParameterIn.Read(good)))
			a.Show(
				"and a meet lies in each of its members",
				Unfold(algebraic_element.FieldAdjoinDef),
				BySets(member))
		}),
})}

// GoodOpenFiniteExtension — L is a finite extension of k(t): it is Galois
// over k(t).
var GoodOpenFiniteExtension = goodOpenFiniteExtensionThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenFiniteExtension",
	Key:  "prop_3c00ca32de8d89bc",
	Build: GaloisGoodOpenDef.Entry().Law("finite_extension(R, field_adjoin(R, k, {t}), L)",
		func(a *Argument, good Fact) {
			a.Show(
				"L is Galois over k(t), and a Galois extension is finite",
				By(a.Unfolded(GoodOpenGalois.Read(good), galois_correspondence.GaloisOverDef)))
		}),
})}

// GoodOpenGroupFinite — the group of L over k(t) is finite: L is a finite
// extension of k(t).
var GoodOpenGroupFinite = goodOpenGroupFiniteThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenGroupFinite",
	Key:  "prop_d8670a4c88032d46",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "finite(field_automorphisms(M, field_adjoin(M, k, {t}), L))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		arg.Show(
			"L is a finite extension of the subfield k(t) inside it, so its group over k(t) is finite",
			By(
				good,
				GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
				GoodOpenFieldSubfield.Read(good),
				GoodOpenRationalInField.Read(good),
				GoodOpenFiniteExtension.Read(good),
				field_automorphism.AutomorphismsBound.Read(M).At(arg.TermAs[Set[A]]("field_adjoin(M, k, {t})"), L)))
	}),
})}

// GoodOpenPolynomialsSubring — k[t] is a subring on a good open: k is a
// subfield and t a point of the field.
var GoodOpenPolynomialsSubring = goodOpenPolynomialsSubringThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenPolynomialsSubring",
	Key:  "prop_7f096b55e5458333",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "subring(field_ring(M), polynomial_image(field_ring(M), k, t))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		tm := GoodParameterInField(arg, t, good)
		arg.Show(
			"so k[t] is a subring, k being a subfield",
			By(GoodOpenConstantsSubfield.Read(good), algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
	}),
})}

// GoodOpenConstantsInPolynomials — k[t] holds the constants k.
var GoodOpenConstantsInPolynomials = goodOpenConstantsInPolynomialsThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenConstantsInPolynomials",
	Key:  "prop_247e549ffd48af49",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "k ⊆ polynomial_image(field_ring(M), k, t)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		tm := GoodParameterInField(arg, t, good)
		arg.Show(
			"so k[t] holds k, the values of the constant polynomials",
			By(GoodOpenConstantsSubfield.Read(good), algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
	}),
})}

// GoodOpenParameterInPolynomials — k[t] holds the parameter t.
var GoodOpenParameterInPolynomials = goodOpenParameterInPolynomialsThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenParameterInPolynomials",
	Key:  "prop_ed71ccab1460ea4f",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "t ∈ polynomial_image(field_ring(M), k, t)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		tm := GoodParameterInField(arg, t, good)
		arg.Show(
			"so k[t] holds t, the value of the polynomial X",
			By(GoodOpenConstantsSubfield.Read(good), algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
	}),
})}

// GoodOpenChartSubring — the chart C is a subring: it lies in L, inside the
// field, and is a ring under the field's operations.
var GoodOpenChartSubring = goodOpenChartSubringThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenChartSubring",
	Key:  "prop_7a78692f66f14c29",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "subring(field_ring(M), C)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		inField := arg.Have(
			"C lies in L, which lies in M",
			"C ⊆ M.carrier",
			BySets(
				GoodOpenChartInField.Read(good),
				field.SubfieldSubset.Read(GoodOpenFieldSubfield.Read(good))))
		arg.Show(
			"a subset of M that is a ring under M's operations is a subring",
			By(GoodOpenChartRing.Read(good), inField, comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(C)))
	}),
})}

// GoodOpenPolynomialsInChart — the chart holds k[t]: k[t] lies in k[t] with
// a(t) inverted, which the chart holds.
var GoodOpenPolynomialsInChart = goodOpenPolynomialsInChartThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenPolynomialsInChart",
	Key:  "prop_cad14dc60685f212",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "polynomial_image(field_ring(M), k, t) ⊆ C",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		away := arg.Have(
			"k[t] is a subring holding a(t), so it lies in k[t] with a(t) inverted",
			"polynomial_image(field_ring(M), k, t) ⊆ "+
				"ring_away(field_ring(M), polynomial_image(field_ring(M), k, t), polynomial_eval(a, t))",
			By(
				field.RingOn.Read(M),
				good,
				GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
				GoodOpenDenominatorInPolynomials.Read(good),
				ring_away.RingAwaySubring.At(
					arg.TermAs[RingOps[A]]("field_ring(M)"),
					arg.TermAs[Set[A]]("polynomial_image(field_ring(M), k, t)"),
					arg.TermAs[A]("polynomial_eval(a, t)"))))
		arg.Show(
			"which the chart holds",
			BySets(away, GoodOpenChartHoldsBase.Read(good)))
	}),
})}

// GoodOpenConstantsInChart — the chart holds the constants k: they lie in
// k[t], which the chart holds.
var GoodOpenConstantsInChart = goodOpenConstantsInChartThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenConstantsInChart",
	Key:  "prop_29c14c8b2c5667ea",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "k ⊆ C",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		arg.Show(
			"k lies in k[t], which lies in C",
			BySets(
				good,
				GoodOpenConstantsInPolynomials.Read(M).At(k, L, C, t, a),
				GoodOpenPolynomialsInChart.Read(M).At(k, L, C, t, a)))
	}),
})}

// GoodOpenParameterInChart — the chart holds the parameter t: it lies in
// k[t], which the chart holds.
var GoodOpenParameterInChart = goodOpenParameterInChartThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenParameterInChart",
	Key:  "prop_381c41af0791772b",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "t ∈ C",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		arg.Show(
			"t lies in k[t], which lies in C",
			BySets(
				good,
				GoodOpenParameterInPolynomials.Read(M).At(k, L, C, t, a),
				GoodOpenPolynomialsInChart.Read(M).At(k, L, C, t, a)))
	}),
})}

// GoodOpenDenominatorInPolynomials — a(t) lies in k[t]: a is a polynomial
// over k.
var GoodOpenDenominatorInPolynomials = goodOpenDenominatorInPolynomialsThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenDenominatorInPolynomials",
	Key:  "prop_d1ab0c2767db4366",
	Build: GaloisGoodOpenDef.Entry().Law("polynomial_eval(R.add, R.zero, R.mul, R.one, a, t) ∈ "+
		"polynomial_image(field_ring(R), k, t)",
		func(
			arg *Argument,
			R *Expr[FieldOps[A]],
			k, _ *Expr[Set[A]],
			t *Expr[A],
			_ *Expr[Set[A]],
			a *Arrow[Nat, A],
			good Fact,
		) {
			arg.Show(
				"a(t) is the value at t of a polynomial over k",
				BySets(
					GoodOpenDenominatorOver.Read(good),
					algebraic_element.PolynomialImageDef.At(arg.TermAs[RingOps[A]]("field_ring(R)"), k, t)))
		}),
})}

// GoodOpenDenominatorValueNonzero — a(t) is not zero: a nonzero polynomial
// over k does not vanish at t, which is transcendental over k.
var GoodOpenDenominatorValueNonzero = goodOpenDenominatorValueNonzeroThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenDenominatorValueNonzero",
	Key:  "prop_8cc23cce7d27545f",
	Build: GaloisGoodOpenDef.Entry().Law("polynomial_eval(R.add, R.zero, R.mul, R.one, a, t) ≠ R.zero",
		func(
			arg *Argument,
			R *Expr[FieldOps[A]],
			k, _ *Expr[Set[A]],
			t *Expr[A],
			_ *Expr[Set[A]],
			a *Arrow[Nat, A],
			good Fact,
		) {
			arg.Show(
				"a is a nonzero polynomial over k, and t is transcendental over k",
				By(
					GoodOpenParameterTranscendental.Read(good),
					GoodOpenDenominatorOver.Read(good),
					GoodOpenDenominatorNonzero.Read(good),
					algebraic_element.AlgebraicOverDef.At(R, k, t)))
		}),
})}

// GoodOpenDenominatorInChart — the chart holds a(t): it lies in k[t], which
// the chart holds.
var GoodOpenDenominatorInChart = goodOpenDenominatorInChartThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenDenominatorInChart",
	Key:  "prop_7d157ee4eb24b654",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "polynomial_eval(a, t) ∈ C",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		arg.Show(
			"a(t) lies in k[t], which lies in C",
			BySets(
				good,
				GoodOpenDenominatorInPolynomials.Read(good),
				GoodOpenPolynomialsInChart.Read(M).At(k, L, C, t, a)))
	}),
})}

// GoodOpenDenominatorInverseInChart — the chart holds the inverse of a(t):
// k[t] with a(t) inverted holds it, and the chart holds k[t] with a(t)
// inverted.
var GoodOpenDenominatorInverseInChart = goodOpenDenominatorInverseInChartThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenDenominatorInverseInChart",
	Key:  "prop_f720ed876ede263",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "M.inv(polynomial_eval(a, t)) ∈ C",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		value := arg.TermAs[A]("polynomial_eval(a, t)")
		valueIn := arg.MemberOf[on.M](value, arg.Have(
			"a(t) lies in C, inside L, inside M",
			"polynomial_eval(a, t) ∈ M.carrier",
			BySets(
				good,
				GoodOpenDenominatorInChart.Read(M).At(k, L, C, t, a),
				GoodOpenChartInField.Read(good),
				field.SubfieldSubset.Read(GoodOpenFieldSubfield.Read(good)))))
		inverted := arg.Have(
			"a(t) is nonzero, so its inverse inverts it",
			"polynomial_eval(a, t) * M.inv(polynomial_eval(a, t)) = M.one",
			By(GoodOpenDenominatorValueNonzero.Read(good), field.MulRightInverseOn.Read(M).At(valueIn)))
		away := GroupPremises(
			field.RingOn.Read(M),
			good,
			GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a),
			GoodOpenDenominatorInPolynomials.Read(good),
			ring_away.RingAwaySubring.At(
				arg.TermAs[RingOps[A]]("field_ring(M)"),
				arg.TermAs[Set[A]]("polynomial_image(field_ring(M), k, t)"),
				value))
		arg.Show(
			"k[t] with a(t) inverted holds the inverse of a(t), a point "+
				"of M inverting it, and the chart holds k[t] with a(t) inverted",
			BySets(GoodOpenChartHoldsBase.Read(good), inverted, field.InvIn.Read(M).At(valueIn), away))
	}),
})}

// GoodOpenDenominatorInRational — a(t) lies in k(t): it lies in k[t], which
// lies in k(t).
var GoodOpenDenominatorInRational = goodOpenDenominatorInRationalThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenDenominatorInRational",
	Key:  "prop_59d7a37443ab17c8",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "polynomial_eval(a, t) ∈ field_adjoin(M, k, {t})",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		tm := GoodParameterInField(arg, t, good)
		arg.Show(
			"a(t) lies in k[t], which lies in k(t), k being a subfield and t a point of M",
			BySets(
				GoodOpenDenominatorInPolynomials.Read(good),
				GroupPremises(
					GoodOpenConstantsSubfield.Read(good), algebraic_element.PolynomialImageRing.Read(M).At(k, tm))))
	}),
})}

// GoodOpenDenominatorInverseInRational — k(t) holds the inverse of a(t): it
// is a subfield holding a(t).
var GoodOpenDenominatorInverseInRational = goodOpenDenominatorInverseInRationalThm{family.Add(registry.ProofEntry{
	Name: "GoodOpenDenominatorInverseInRational",
	Key:  "prop_95de7f036773da4a",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A).",
		Hypotheses: []string{"galois_good_open(M, k, L, t, C, a)"},
		Conclusion: "M.inv(polynomial_eval(a, t)) ∈ field_adjoin(M, k, {t})",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		good Fact,
	) {
		arg.Show(
			"k(t) is a subfield holding a(t), so it holds its inverse",
			By(
				good,
				GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
				GoodOpenDenominatorInRational.Read(M).At(k, L, C, t, a),
				field.SubfieldInv.At(
					arg.TermAs[FieldOps[A]]("M"),
					arg.TermAs[Set[A]]("field_adjoin(M, k, {t})"),
					arg.TermAs[A]("polynomial_eval(a, t)"))))
	}),
})}
