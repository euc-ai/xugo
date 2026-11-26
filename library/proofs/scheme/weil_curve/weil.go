// weil.go — the Weil conjectures assembled: for a smooth curve over a finite field,
// for a smooth projective equation curve through its presentation by two charts,
// and for one over every finite field, carried into a closed field holding a
// transcendental point.

package weil_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/rational_function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_formal_series"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_zeta"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_presentation"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_transfer"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// WeilConjecturesOfAgreeingCounts — the predicate weil_conjectures reads its
// count function at positive m only: two count functions N and N₁ that agree
// past 0 satisfy it together, with the same q, g and P. The proof moves each
// clause through the agreement: the four coefficient clauses do not read the
// counts; the coefficient sequences N(m)/m and N₁(m)/m are one function, both
// zero at 0, so the exponential identity is read through that equation; and
// the power sums and the Hasse-Weil bound are stated at positive m, where the
// counts coincide.
var WeilConjecturesOfAgreeingCounts = weilConjecturesOfAgreeingCountsThm{family.Add(registry.ProofEntry{
	Name: "WeilConjecturesOfAgreeingCounts",
	Key:  "prop_e4a1ac648a1b18d8",
	Build: family.Theorem(Statement{
		Binders: "∀q g:num. ∀N N₁:(num → num). ∀P:(num → real).",
		Hypotheses: []string{
			"weil_conjectures(q, g, N, P)",
			"∀m:num. 0 < m ⇒ N₁(m) = N(m)",
		},
		Conclusion: "weil_conjectures(q, g, N₁, P)",
	}, func(
		a *Argument,
		q, g *Expr[Nat],
		N, N1 *Expr[Fun[Nat, Nat]],
		P *Expr[Fun[Nat, Real]],
		holds, agree Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(holds, WeilConjecturesDef),
			"P has integer coefficients",
			"with constant term 1",
			"of degree 2g",
			"with leading coefficient q^g",
			"(1 − T)(1 − qT) times the formal exponential of the counts N is P",
			"the coefficients are reciprocal",
			"the reciprocal roots have modulus √q and power sums the counts N",
			"the counts N satisfy the Hasse-Weil bound")
		sameCoefficients := a.Have(
			"The two coefficient sequences agree",
			"(λm:num. COND(m = 0, real_of_num(0), real_of_num(N₁(m)) / real_of_num(m))) = "+
				"(λm:num. COND(m = 0, real_of_num(0), real_of_num(N(m)) / real_of_num(m)))",
			Funext(),
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]()
				b.Cases(b.Term("m = 0"))
				b.When(
					"At 0 both are zero",
					func(c *Argument, zero Fact) {
						c.Show(
							"The conditional takes its first branch on both sides",
							By(zero))
					})
				b.Otherwise(
					"Past 0 the counts agree",
					func(c *Argument, nonzero Fact) {
						c.Show(
							"The numerators are one count",
							By(Normalized, nonzero, nat_order.PosIffNonzero.At(m), agree.At(m)))
					})
			}))
		roots := a.Have(
			"The power sums of the reciprocal roots give the counts N₁",
			"∃a:(num → complex). "+
				"    (λn:num. complex_of_real(P(n))) = reciprocal_product(2 * g, a) ∧ "+
				"    (∀i:num. i < 2 * g ⇒ complex_abs(a(i)) = real_sqrt(real_of_num(q))) ∧ "+
				"    (∀m:num. "+
				"        0 < m ⇒ "+
				"        complex_of_real(real_of_num(N₁(m))) = "+
				"        complex_sub(complex_of_real(real_of_num(q ^ m + 1)), finite_power_sum(2 * g, a, m)))",
			Derive(func(b *Argument) {
				spectrum, onRoots := b.UnpackAs[Fun[Nat, Complex]](parts[6], "a")
				rootParts := b.Conjuncts(
					onRoots,
					"P is the product of the 2g factors 1 − a(i)T",
					"each reciprocal root has modulus √q",
					"their power sums give the counts N")
				powerSums := b.Have(
					"The same power sums give the counts N₁",
					Statement{
						Binders:    "∀m:num.",
						Hypotheses: []string{"0 < m"},
						Conclusion: "complex_of_real(real_of_num(N₁(m))) = " +
							"complex_sub(complex_of_real(real_of_num(q ^ m + 1)), finite_power_sum(2 * g, a, m))",
					},
					By(agree, rootParts[2]))
				b.Take(spectrum)
				b.Show(
					"The roots keep their first two properties",
					By(rootParts[0], rootParts[1], powerSums))
			}))
		bound := a.Have(
			"The counts N₁ satisfy the Hasse-Weil bound",
			Statement{
				Binders:    "∀m:num.",
				Hypotheses: []string{"0 < m"},
				Conclusion: "real_abs(real_of_num(N₁(m)) - real_of_num(q ^ m + 1)) ≤ " +
					"real_of_num(2 * g) * real_sqrt(real_of_num(q ^ m))",
			},
			By(agree, parts[7]))
		// (1 − T)(1 − qT) times the formal exponential of N₁ is P: the identity for N read
		// through the coefficient sequences.
		zeta := a.Simplified(parts[4], Rev(sameCoefficients))
		a.Show(
			"Each clause holds at N₁: four never read the counts, the "+
				"rest read them past 0 or through the coefficient sequences",
			Simp(Fwd(WeilConjecturesDef)),
			By(parts[0], parts[1], parts[2], parts[3], zeta, parts[5], roots, bound))
	}),
})}

// FullWeilConjecturesCurves — the Weil conjectures for a smooth curve over a
// finite field k of q elements: its point counts N(m) over the extensions of
// degree m, its genus g and the numerator P of its zeta function satisfy
// weil_conjectures (WeilConjecturesDef), and the series of effective-divisor
// counts is the formal exponential of N(m)/m. Rationality and the functional
// equation give the coefficient facts, the logarithmic recurrence gives the
// exponential through real_formal_series.RealFormalExpOfCounts, the trace
// formula supplies the reciprocal roots and the Riemann hypothesis their
// moduli, and the predicate is closed from its definition.
var FullWeilConjecturesCurves = fullWeilConjecturesCurvesThm{family.Add(registry.ProofEntry{
	Name: "FullWeilConjecturesCurves",
	Key:  "prop_2f7f8ea53f542954",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "weil_conjectures(card(k), «genus», «count», «numerator») ∧ " +
			"(λn:num. «effective»(int_of_num(n))) = " +
			"formal_exp_zero(real_ring, " +
			"    λm:num. COND(m = 0, real_of_num(0), real_of_num(«count»(m)) / real_of_num(m)))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		hypotheses Fact,
	) {
		rationality := arg.Conjuncts(
			GroupPremises(hypotheses, curve_zeta.ZetaNumeratorRationality.Read(M).At(K, k, A0, A1, A01, t)),
			"P has integer coefficients",
			"P has constant term one",
			"P has degree at most 2g",
			"P has no coefficient above 2g",
			"P at one is the order of the degree-zero class group",
			"(1 − T)(1 − qT) times the effective-divisor series is P")
		functional := arg.Conjuncts(
			GroupPremises(hypotheses, curve_zeta.CurveZetaFunctionalEquation.Read(M).At(K, k, A0, A1, A01, t)),
			"P has degree exactly 2g",
			"its top coefficient is q^g",
			"its coefficients are reciprocal")
		logarithm := arg.Conjuncts(
			GroupPremises(
				hypotheses, curve_zeta.ZetaEulerProductAndLogDerivative.Read(M).At(K, k, A0, A1, A01, t)),
			"the effective-divisor series solves the recurrence with the point counts as its counting sequence",
			"its coefficients are those of the Euler product")
		series := arg.TermAs[Fun[Nat, Real]]("λn:num. «effective»(n)")
		counts := arg.TermAs[Fun[Nat, Real]]("λm:num. real_of_num(«count»(m))")
		exponential := arg.Have(
			"so that series is the formal exponential of N(m)/m",
			"(λn:num. «effective»(n)) = "+
				"formal_exp_zero(real_ring, "+
				"    λm:num. COND(m = 0, real_of_num(0), real_of_num(«count»(m)) / real_of_num(m)))",
			By(logarithm[0], real_formal_series.RealFormalExpOfCounts.At(series, counts)))
		// (1 − T)(1 − qT) times the formal exponential is P: the rationality identity read
		// through the exponential.
		zeta := arg.Simplified(rationality[5], Fwd(exponential))
		trace := arg.Conjuncts(
			GroupPremises(hypotheses, curve_zeta.CurvePointCountTraceFormula.Read(M).At(K, k, A0, A1, A01, t)),
			"P has a family of 2g reciprocal roots",
			"and every such family computes the point counts and the base changes of P")
		roots := arg.Have(
			"take such a family: P is its product, the Riemann hypothesis "+
				"gives its moduli and the trace formula its power sums",
			"∃a:(num → complex). "+
				"    (λn:num. complex_of_real(«numerator»(n))) = reciprocal_product(2 * «genus», a) ∧ "+
				"    (∀i:num. i < 2 * «genus» ⇒ complex_abs(a(i)) = real_sqrt(«q»)) ∧ "+
				"    (∀m:num. "+
				"        0 < m ⇒ "+
				"        complex_of_real(real_of_num(«count»(m))) = "+
				"        complex_sub(complex_of_real(real_of_num(card(k) ^ m + 1)), "+
				"            finite_power_sum(2 * «genus», a, m)))",
			Derive(func(arg *Argument) {
				a, reciprocal := arg.UnpackAs[Fun[Nat, Complex]](trace[0], "a")
				product := arg.Conjuncts(
					arg.Unfolded(reciprocal, curve_zeta.CurveReciprocalRootsDef),
					"no reciprocal root is zero",
					"P is the product of the 2g factors 1 − a(i)T")
				moduli := arg.Conjuncts(
					GroupPremises(
						hypotheses, reciprocal, RiemannHypothesisGeneralCurves.Read(M).At(K, k, A0, A1, A01, t, a)),
					"each reciprocal root has modulus √q",
					"each zero of P has modulus 1/√q")
				counting := arg.Conjuncts(
					GroupPremises(reciprocal, trace[1].At(a)),
					"the point counts are q^m + 1 less the power sums",
					"the product of the roots is q^g",
					"over each extension the numerator has their powers as reciprocal roots",
					"their reversed polynomial vanishes at each of them")
				arg.Take(a)
				arg.Show(
					"these roots have all three properties",
					By(product[1], moduli[0], counting[0]))
			}))
		weil := arg.Have(
			"these facts, with the bound in every extension, are the Weil conjectures for the curve",
			"weil_conjectures(card(k), «genus», «count», «numerator»)",
			Simp(Fwd(WeilConjecturesDef)),
			By(
				rationality[0],
				rationality[1],
				functional[0],
				functional[1],
				zeta,
				functional[2],
				roots,
				hypotheses,
				HasseWeilAllExtensions.Read(M)))
		arg.Show(
			"the conjectures, and the effective-divisor series as the exponential of the counts",
			By(weil, exponential))
	}),
})}

// FullWeilProjectiveEquationCurves — the Weil conjectures for a smooth
// projective curve cut out by equations over a finite field k: the curve has
// a presentation by two charts, of the curve's genus, whose counts are the
// numbers of projective points over the finite extensions of k, and the
// curve's own genus and projective counts satisfy weil_conjectures with the
// presentation's zeta numerator. The presentation's charts carry the
// projective points injectively onto their evaluation points, which the
// presentation counts, so each count of the theorem for the presentation
// reads as a number of projective points; the predicate reads its counts at
// positive degrees only, so it passes from the presentation's data to the
// curve's through that equality of counts and the equality of genera.
var FullWeilProjectiveEquationCurves = fullWeilProjectiveEquationCurvesThm{family.Add(registry.ProofEntry{
	Name: "FullWeilProjectiveEquationCurves",
	Key:  "prop_908253eba990108a",
	Reading: "The transcendental point is the presentation's own need: the " +
		"function field K sits inside M at transcendence degree one over k, so M " +
		"must not be algebraic over k. WeilConjecturesOverFiniteFields discharges it.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"∃u:A. u ∈ M.carrier ∧ ¬algebraic_over(M, k, u)",
			"smooth_projective_equation_curve(M, k, n, E)",
		},
		Conclusion: "∃K A₀ A₁ A₀₁:set(A). ∃t:A. " +
			"    subfield(M, K) ∧ " +
			"    smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁) ∧ " +
			"    curve_genus(restrict_ring(field_ring(M), K), k, A₀, A₁, A₀₁) = " +
			"    projective_equation_genus(field_ring(M), k, n, E) ∧ " +
			"    (∀m:num. " +
			"        0 < m ⇒ card(«points»(m)) = curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, m)) ∧ " +
			"    weil_conjectures(card(k), " +
			"        projective_equation_genus(field_ring(M), k, n, E), " +
			"        λm:num. card(«points»(m)), " +
			"        curve_zeta_numerator(restrict_ring(field_ring(M), K), k, A₀, A₁, A₀₁))",
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k))"},
			{Name: "points", Text: "λr:num. " +
				"    projective_equation_points(field_ring(M), k, «constants»(r), n, E)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		closed, transcendental, curve Fact,
	) {
		// The claim keeps of the presentation what this proof reads.
		K, A0, A1, A01, t, presented := a.Obtain5As[Set[A], Set[A], Set[A], Set[A], A](
			"The presentation of the curve supplies its function "+
				"field K, two charts, their overlap and a parameter",
			"∃K A₀ A₁ A₀₁:set(A). ∃t:A. "+
				"    subfield(M, K) ∧ "+
				"    smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁) ∧ "+
				"    curve_genus(restrict_ring(field_ring(M), K), k, A₀, A₁, A₀₁) = "+
				"    projective_equation_genus(field_ring(M), k, n, E) ∧ "+
				"    (∀r:num. "+
				"        0 < r ⇒ "+
				"        ∃f:((num → A) → prod(bool, A → A)). "+
				"            injective_on(«points»(r), f) ∧ "+
				"            image(f, «points»(r)) = curve_evaluation_points(M, k, «constants»(r), t, A₀, A₁))",
			By(
				closed,
				transcendental,
				curve,
				projective_presentation.SmoothProjectiveBiaffinePresentation.Read(M).At(k, n, E)))
		data := a.Conjuncts(
			presented,
			"K is a subfield of M",
			"the presentation is a smooth finite curve",
			"of the curve's genus",
			"and its evaluation points are the curve's projective points")
		subK, smooth, genus, carried := data[0], data[1], data[2], data[3]
		smoothDatum := a.Unfolded(smooth, smooth_curve.SmoothFiniteFieldCurveDef)
		count := a.Have(
			"Over each extension the curve counts the projective points",
			"∀m:num. 0 < m ⇒ card(«points»(m)) = «count»(m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]()
				positive := b.Assume()
				l := b.TermAs[Set[A]]("«constants»(m)")
				points := b.TermAs[Set[Fun[Nat, A]]]("«points»(m)")
				extension := b.Have(
					"The constants of degree m are a finite subfield of M containing k",
					"subfield(M, «constants»(m)) ∧ k ⊆ «constants»(m) ∧ has_size(«constants»(m), card(k) ^ m)",
					By(
						closed,
						projective_curve.CurveConstantsSubfield.Read(curve),
						projective_curve.CurveConstantsFinite.Read(curve),
						positive,
						finite_field.FiniteConstantsSubfield.Read(M).At(k, m)))
				evaluation := b.Conjuncts(
					b.Have(
						"The charts count the evaluation points",
						"finite(curve_evaluation_points(M, k, «constants»(m), t, A₀, A₁)) ∧ "+
							"card(curve_evaluation_points(M, k, «constants»(m), t, A₀, A₁)) = "+
							"curve_rational_point_count(field_ring(M), k, «constants»(m), A₀, A₁, A₀₁)",
						By(
							subK,
							smoothDatum,
							extension,
							cardinality.HasSizeDef,
							curve_point_count.EvaluationPointsCount.Read(M).At(K, k, A0, A1, A01, t, l))),
					"the evaluation points are finite",
					"and the charts count them")
				f, bijection := b.UnpackAs[Fun[Fun[Nat, A], Prod[Bool, Fun[A, A]]]](
					GroupPremises(positive, carried.At(m)), "f")
				transport := b.Conjuncts(
					bijection,
					"f is injective on the projective points",
					"and carries them onto the evaluation points")
				finitePoints := b.Have(
					"The projective points are finite, as their injective image is",
					"finite(«points»(m))",
					By(transport[0], transport[1], evaluation[0], finite_set.FiniteImageInjEq.At(f, points)))
				b.Show(
					"The injection keeps the count, and the evaluation points give the curve's",
					CalcEq(
						Leg(
							b.TermAs[Nat]("card(image(f, «points»(m)))"),
							"an injective image has as many points",
							By(transport[0], finitePoints, cardinality.CardImageInj.At(f, points))),
						Leg(
							b.TermAs[Nat]("card(curve_evaluation_points(M, k, «constants»(m), t, A₀, A₁))"),
							"which are the evaluation points",
							transport[1].Rw(),
							Basic()),
						Leg(
							b.TermAs[Nat]("curve_rational_point_count(field_ring(M), k, «constants»(m), A₀, A₁, A₀₁)"),
							"which the charts count",
							By(evaluation[1])),
						FinalLeg(
							"which is the count over the extension of degree m",
							ByArith(
								positive,
								curve_point_count.CurveExtensionCountDef.At(
									b.TermAs[module_record.RingOps[A]]("field_ring(M)"), k, A0, A1, A01, m))),
					))
			}))
		weil := a.Conjuncts(
			GroupPremises(closed, subK, smooth, FullWeilConjecturesCurves.Read(M).At(K, k, A0, A1, A01, t)),
			"the presentation satisfies the Weil conjectures",
			"and its effective-divisor series is the formal exponential of its counts")
		weilCurve := a.Have(
			"The curve's genus and projective counts satisfy the Weil conjectures "+
				"with the presentation's numerator: the counts agree past 0",
			"weil_conjectures(card(k), "+
				"    projective_equation_genus(field_ring(M), k, n, E), "+
				"    λm:num. card(«points»(m)), "+
				"    «numerator»)",
			genus.RwRev(),
			By(weil[0], count, WeilConjecturesOfAgreeingCounts))
		a.Take(K)
		a.Take(A0)
		a.Take(A1)
		a.Take(A01)
		a.Take(t)
		a.Show(
			"The presentation carries the conjectures to the curve",
			By(subK, smooth, genus, count, weilCurve))
	}),
})}

// _ClosurePoint is a point of the closure of M(x) that
// rational_function_field.FunctionFieldClosure builds for a field M on A.
type _ClosurePoint = Set[Prod[Nat, Fun[Nat, Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]]]

// WeilConjecturesOverFiniteFields — the Weil conjectures for every smooth
// projective curve over every finite field: a smooth projective equation
// curve over a finite subfield k of an algebraically closed field M
// satisfies weil_conjectures at its own genus and its numbers of projective
// points over the fields of q^m elements, q = |k|, for some numerator P. M
// may be algebraic over k, so the curve is carried along the embedding ι of
// M into the algebraic closure N of M(x)
// (rational_function_field.FunctionFieldClosure), whose variable t is
// transcendental over ι(M) and so over ι(k): over N the carried curve is
// smooth (projective_transfer.CarriedSmoothCurve) and
// FullWeilProjectiveEquationCurves gives it a numerator P. ι keeps the size
// of k, the genus and every count (projective_transfer.CarriedPointCount,
// projective_transfer.CarriedHilbertFunction), and weil_conjectures reads
// the counts at positive degrees only (WeilConjecturesOfAgreeingCounts), so
// P serves the curve over M.
var WeilConjecturesOverFiniteFields = weilConjecturesOverFiniteFieldsThm{family.Add(registry.ProofEntry{
	Name: "WeilConjecturesOverFiniteFields",
	Key:  "prop_768e08ad52e8fada",
	Reading: "M is any algebraically closed field and k any finite subfield of it, so every finite " +
		"field is covered: it embeds in its algebraic closure. k finite and a subfield are conjuncts " +
		"of the curve predicate, smooth_projective_equation_curve: the equations are forms over k, and " +
		"the geometric conditions — a prime ideal, a point, the Jacobian rank — are read over M.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
		},
		Conclusion: "∃P:(num → real). " +
			"    weil_conjectures(card(k), " +
			"        projective_equation_genus(field_ring(M), k, n, E), " +
			"        λm:num. " +
			"            card(projective_equation_points(field_ring(M), " +
			"                    k, " +
			"                    finite_constants(field_ring(M), card(k), m), " +
			"                    n, " +
			"                    E)), " +
			"        P)",
		Abbrev: Abbrev{
			{Name: "carriedForms", Text: "λι:(A → B). image(λP:((num → num) → A). λm:(num → num). ι(P(m)), E)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		closed, curve Fact,
	) {
		N, ι, t, closure := a.Unpack3As[FieldOps[_ClosurePoint], Fun[A, _ClosurePoint], _ClosurePoint](
			rational_function_field.FunctionFieldClosure.Read(M),
			"N",
			"ι",
			"t")
		host := a.Conjuncts(
			closure,
			"N is a field",
			"N is algebraically closed",
			"ι carries M into N as rings",
			"t lies in N",
			"t is transcendental over ι(M)")
		fieldN, closedN, hom, tInN, transcendentalOverM := host[0], host[1], host[2], host[3], host[4]
		subK := projective_curve.CurveConstantsSubfield.Read(curve)
		carriedK := a.TermAs[Set[_ClosurePoint]]("image(ι, k)")
		carriedE := a.TermAs[Set[Fun[Fun[Nat, Nat], _ClosurePoint]]]("«carriedForms»(ι)")
		transcendental := a.Have(
			"t is transcendental over ι(k) as well",
			"t ∈ N.carrier ∧ ¬algebraic_over(N, image(ι, k), t)",
			Derive(func(b *Argument) {
				inside := b.Have(
					"ι(k) is a part of ι(M), k being a subfield of M",
					"image(ι, k) ⊆ image(ι, M.carrier)",
					By(subK, field.SubfieldSubset, set_image.ImageSubset.At(ι, k, b.TermAs[Set[A]]("M.carrier"))))
				b.Show(
					"Algebraic over ι(k), t would be algebraic over ι(M)",
					By(
						tInN,
						transcendentalOverM,
						inside,
						algebraic_element.AlgebraicOverMono.Read(fieldN).At(
							carriedK, b.TermAs[Set[_ClosurePoint]]("image(ι, M.carrier)"), t)))
			}))
		smooth := a.Have(
			"Carried along ι, the curve is a smooth projective equation curve over N, with constants ι(k)",
			"smooth_projective_equation_curve(N, image(ι, k), n, «carriedForms»(ι))",
			By(
				closed,
				closedN,
				fieldN,
				hom,
				curve,
				subK,
				projective_curve.CurveEquationsForms.Read(curve),
				projective_transfer.CarriedSmoothCurve.Read(M).At(N, ι, k, n, E)))
		weilN := a.Have(
			"Over N, where t is transcendental over ι(k), the carried curve satisfies the Weil conjectures",
			"∃P:(num → real). "+
				"    weil_conjectures(card(image(ι, k)), "+
				"        projective_equation_genus(field_ring(N), image(ι, k), n, «carriedForms»(ι)), "+
				"        λm:num. "+
				"            card(projective_equation_points(field_ring(N), "+
				"                    image(ι, k), "+
				"                    finite_constants(field_ring(N), card(image(ι, k)), m), "+
				"                    n, "+
				"                    «carriedForms»(ι))), "+
				"        P)",
			By(
				closedN,
				transcendental,
				smooth,
				FullWeilProjectiveEquationCurves.Read(fieldN).At(carriedK, n, carriedE)))
		polynomials := a.Have(
			"The equations are polynomials over k",
			"E ⊆ polynomial_algebra_ring(restrict_ring(field_ring(M), k), {i:num | i ≤ n}).carrier",
			BySets(curve, projective_curve.CurveEquationsForms, homogeneous_polynomial.FormPolynomial))
		transfer := a.Conjuncts(
			GroupPremises(
				fieldN,
				closed,
				hom,
				subK,
				projective_curve.CurveConstantsFinite.Read(curve),
				polynomials,
				projective_transfer.CarriedPointCount.Read(M).At(N, ι, k, n, E)),
			"ι keeps the size q of k",
			"and over the field of q^m elements the carried curve has as many points as the curve")
		genus := a.Have(
			"ι keeps the Hilbert function, and with it the genus",
			"projective_equation_genus(field_ring(N), image(ι, k), n, «carriedForms»(ι)) = "+
				"projective_equation_genus(field_ring(M), k, n, E)",
			By(
				fieldN,
				hom,
				subK,
				polynomials,
				projective_transfer.CarriedHilbertFunction.Read(M).At(N, ι, k, n, E)))
		P, carriedWeil := a.UnpackAs[Fun[Nat, Real]](weilN, "P")
		// ι keeps q and the genus: the conjectures over N, read at q = |k| and at the curve's genus.
		sameData := a.Simplified(carriedWeil, Fwd(transfer[0]), Fwd(genus))
		a.Take(P)
		a.Show(
			"The counts over N and over M agree past 0, so P serves the curve over M",
			By(sameData, transfer[1], WeilConjecturesOfAgreeingCounts))
	}),
})}
