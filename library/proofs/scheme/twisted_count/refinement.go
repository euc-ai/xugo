package twisted_count

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/twisted_counting"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// _chartAway is galois_good_open.ChartAwayFacts read apart: c(t) lies in C and
// is nonzero, and C lies in its localization at c(t), which lies in L and is a
// good open.
type _chartAway struct {
	valueIn, valueNonzero, inAway, awayInL, localized Fact
}

// readChartAway reads galois_good_open.ChartAwayFacts at a good open and a
// nonzero polynomial c over k.
func readChartAway(
	arg *Argument,
	M field.FieldFact[on.M],
	k, L, C *Expr[Set[A]],
	t *Expr[A],
	a, c *Arrow[Nat, A],
	good, overK, nonzero Fact,
) _chartAway {
	parts := arg.Conjuncts(
		GroupPremises(good, overK, nonzero, galois_good_open.ChartAwayFacts.Read(M).At(k, L, C, t, a, c)),
		"c(t) lies in C",
		"c(t) is nonzero",
		"C lies in the localization",
		"the localization lies in L",
		"the localization is a good open")
	return _chartAway{parts[0], parts[1], parts[2], parts[3], parts[4]}
}

// TwistEquationAway — the twist equation of a point e of C with c(t) inverted
// spreads from C: y ↦ e(y)^Q and y ↦ e(s y) are points of the localization
// (PointFrobenius, galois_good_open.EvaluationActionPoint), they agree on C,
// and restriction to C is injective on the points of the localization.
var TwistEquationAway = twistEquationAwayThm{family.Add(registry.ProofEntry{
	Name: "TwistEquationAway",
	Key:  "prop_ca6959734b727bc7",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "G", Text: "field_automorphisms(M, «base», L)"},
			{Name: "closed", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
			{Name: "away", Text: "ring_away(field_ring(M), C, polynomial_eval(c, t))"},
			{Name: "onAway", Text: "restrict_ring(field_ring(M), «away»)"},
			{Name: "points", Text: "algebra_points(«onAway», «closed», k, λy:A. y)"},
			{Name: "power", Text: "λv:A. monoid_pow(M.mul, M.one, e(v), card(k) ^ m)"},
			{Name: "action", Text: "evaluation_action(field_ring(M), «away», permutation_inverse(s), e)"},
			{Name: "restriction", Text: "λφ:(A → A). λx:A. COND(x ∈ C, φ(x), M.zero)"},
		},
		Binders: "∀M:field_on(A). " +
			"∀k L C:set(A). " +
			"∀t:A. " +
			"∀a c:(num → A). " +
			"∀m:num. " +
			"∀s:permutation(A). " +
			"∀e:(A → A). " +
			"∀y:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"polynomial_over(k, c)",
			"c ≠ vec_zero",
			"0 < m",
			"s ∈ «G»",
			"e ∈ geometric_evaluation_points(M, k, «away»)",
			"∀x:A. x ∈ C ⇒ «power»(x) = e(permutation_map(s, x))",
			"y ∈ «away»",
		},
		Conclusion: "«power»(y) = e(permutation_map(s, y))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a, c *Arrow[Nat, A],
		m *Expr[Nat],
		s *Expr[symmetric_group.Permutation[A]],
		e *Arrow[A, A],
		y *Expr[A],
		closedField, good, overK, nonzero, positive, inG, point, onC, yIn Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(M)")
		base := arg.TermAs[Set[A]]("«base»")
		value := arg.TermAs[A]("polynomial_eval(c, t)")
		away := arg.TermAs[Set[A]]("«away»")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		onAway := arg.TermAs[RingOps[A]]("«onAway»")
		product := arg.TermAs[Fun[Nat, A]]("polynomial_mul(a, c)")
		points := arg.TermAs[Set[Fun[A, A]]]("«points»")
		restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		inverse := arg.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)")
		chart := readChartAway(arg, M, k, L, C, t, a, c, good, overK, nonzero)
		subfieldK := galois_good_open.GoodOpenConstantsSubfield.Read(good)
		kInC := arg.Have(
			"k lies in C",
			"k ⊆ C",
			By(good, galois_good_open.GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a)))
		subringC := arg.Have(
			"C is a subring",
			"subring(field_ring(M), C)",
			By(good, galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, C, t, a)))
		kInAway := arg.Have(
			"k lies in the localization",
			"k ⊆ «away»",
			BySets(kInC, chart.inAway))
		algebraicSubfield := arg.Have(
			"the algebraic elements are a subfield",
			"subfield(M, algebraic_elements(M, k))",
			By(subfieldK, algebraic_element.AlgebraicElementsSubfield.Read(M).AsFact().At(k)))
		closureInField := arg.Have(
			"lying in M",
			"algebraic_elements(M, k) ⊆ M.carrier",
			By(algebraicSubfield, field.SubfieldSubset.At(ops, closure)))
		injective := arg.Conjuncts(
			GroupPremises(
				subringC,
				algebraicSubfield,
				kInC,
				chart.valueIn,
				chart.valueNonzero,
				algebra_point_bounds.AlgebraPointsAwayInFieldRestriction.Read(M).At(C, k, closure, value)),
			"restriction to C is injective on the points of the localization",
			"its image is the points of C not killing c(t)")[0]
		inPoints := arg.Have(
			"e is a point of the localization",
			"e ∈ «points»",
			By(point, galois_good_open.GeometricEvaluationPointsDef.At(ops, k, away)))
		powerPoint := arg.Have(
			"so is y ↦ e(y)^Q",
			"«power» ∈ «points»",
			By(
				closedField,
				subfieldK,
				galois_good_open.GoodOpenConstantsFinite.Read(good),
				positive,
				closureInField,
				inPoints,
				PointFrobenius.Read(M).At(k, closure, m, onAway, e)))
		twice := arg.Have(
			"inverting s twice returns s",
			"permutation_inverse(permutation_inverse(s)) = s",
			By(group.InvInv.Read(symmetric_group.SymmetricGroup)))
		keeps := arg.Conjuncts(
			GroupPremises(
				chart.localized, inG, galois_good_open.GroupKeepsChart.Read(M).At(k, L, away, t, product, s)),
			"G holds the inverse of s",
			"s keeps the localization, and so does its inverse")
		twiceIn := arg.Have(
			"the inverse of the inverse of s lies in G, and keeps the localization",
			"permutation_inverse(permutation_inverse(s)) ∈ «G» ∧ "+
				"(∀v:A. v ∈ «away» ⇒ permutation_map(permutation_inverse(permutation_inverse(s)), v) ∈ «away»)",
			By(twice, inG, keeps[1]))
		actionPoint := arg.Have(
			"so y ↦ e(s y) is a point of the localization",
			"«action» ∈ «points»",
			Simp(Rev(galois_good_open.GeometricEvaluationPointsDef)),
			By(
				galois_good_open.GoodOpenFieldSubfield.Read(good),
				galois_good_open.GoodOpenConstantsInRational.Read(good),
				chart.localized,
				galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, away, t, product),
				chart.awayInL,
				kInAway,
				twiceIn,
				point,
				galois_good_open.EvaluationActionPoint.Read(M).At(k, base, L, away, inverse, e)))
		values := arg.Have(
			"on the localization the action reads e at s y",
			Statement{
				Binders:    "∀u:A.",
				Hypotheses: []string{"u ∈ «away»"},
				Conclusion: "evaluation_action(field_ring(M), «away», permutation_inverse(s), e, u) = " +
					"e(permutation_map(s, u))",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[A]("u")
				inAway := b.Assume()
				b.Show(
					"the inverse of the inverse of s being s",
					By(twice, inAway, galois_good_open.EvaluationActionDef.At(fieldRing, away, inverse, e, u)))
			}))
		agree := arg.Have(
			"the two points restrict to one map on C",
			"«restriction»(«power») = «restriction»(«action»)",
			Funext(),
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				b.Cases(b.Term("x ∈ C"))
				b.When(
					"on C the two agree by the assumption, C lying in the localization",
					BySets(chart.inAway, onC.At(x), values.At(x)))
				b.Otherwise(
					"off C both restrictions vanish",
					func(d *Argument, outside Fact) {
						d.Show(
							"by the definition of restriction",
							By(outside))
					})
			}))
		same := arg.Have(
			"so the two points are one",
			"«power» = «action»",
			By(injective, powerPoint, actionPoint, agree, functions.InjectiveOnDef.At(points, restriction)))
		arg.Show(
			"and at y this is the equation",
			By(same, yIn, values.At(y)))
	}),
})}

// TwistedPointsAway — restriction to C is a bijection from the points of C with
// c(t) inverted twisted by s onto the points of C twisted by s not killed by c at
// t. On the points the bijection is onto those not killing c(t), the value of c at
// the image of t; the restriction of a twisted point is twisted, s keeping C; and
// an extension of a twisted point is twisted by TwistEquationAway.
var TwistedPointsAway = twistedPointsAwayThm{family.Add(registry.ProofEntry{
	Name: "TwistedPointsAway",
	Key:  "prop_6e22d3e659321742",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "G", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "away", Text: "ring_away(field_ring(M), C, polynomial_eval(c, t))"},
			{Name: "twisted", Text: "λX:set(A). twisted_evaluations(M, k, X, card(k) ^ m, s)"},
			{Name: "live", Text: "{ev:(A → A) | ev ∈ «twisted»(C) ∧ polynomial_eval(c, ev(t)) ≠ M.zero}"},
			{Name: "restriction", Text: "λev:(A → A). λy:A. COND(y ∈ C, ev(y), M.zero)"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a c:(num → A). ∀m:num. ∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"polynomial_over(k, c)",
			"c ≠ vec_zero",
			"0 < m",
			"s ∈ «G»",
		},
		Conclusion: "injective_on(«twisted»(«away»), «restriction») ∧ " +
			"image(«restriction», «twisted»(«away»)) = «live»",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a, c *Arrow[Nat, A],
		m *Expr[Nat],
		s *Expr[symmetric_group.Permutation[A]],
		closedField, good, overK, nonzero, positive, inG Fact,
	) {
		value := arg.TermAs[A]("polynomial_eval(c, t)")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		twistedAway := arg.TermAs[Set[Fun[A, A]]]("«twisted»(«away»)")
		pointsAway := arg.TermAs[Set[Fun[A, A]]]("geometric_evaluation_points(M, k, «away»)")
		ops := arg.TermAs[FieldOps[A]]("M")
		power := arg.TermAs[Nat]("card(k) ^ m")
		twistedOnAway := TwistedEvaluationsDef.At(ops, k, arg.TermAs[Set[A]]("«away»"), power, s)
		twistedOnC := TwistedEvaluationsDef.At(ops, k, C, power, s)
		chart := readChartAway(arg, M, k, L, C, t, a, c, good, overK, nonzero)
		kInC := arg.Have(
			"k lies in C",
			"k ⊆ C",
			By(good, galois_good_open.GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a)))
		subringC := arg.Have(
			"C is a subring",
			"subring(field_ring(M), C)",
			By(good, galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, C, t, a)))
		algebraicSubfield := arg.Have(
			"the algebraic elements are a subfield",
			"subfield(M, algebraic_elements(M, k))",
			By(
				galois_good_open.GoodOpenConstantsSubfield.Read(good),
				algebraic_element.AlgebraicElementsSubfield.Read(M).AsFact().At(k)))
		bijection := arg.Conjuncts(
			arg.Simplified(
				GroupPremises(
					subringC,
					algebraicSubfield,
					kInC,
					chart.valueIn,
					chart.valueNonzero,
					algebra_point_bounds.AlgebraPointsAwayInFieldRestriction.Read(M).At(C, k, closure, value)),
				Rev(galois_good_open.GeometricEvaluationPointsDef)),
			"restriction is injective on the points of the localization",
			"its image is the points of C not killing c(t)")
		inside := arg.Have(
			"the twisted points of the localization are among its points",
			"«twisted»(«away») ⊆ geometric_evaluation_points(M, k, «away»)",
			BySets(twistedOnAway))
		injective := arg.Have(
			"so restriction is injective on them",
			"injective_on(«twisted»(«away»), «restriction»)",
			By(bijection[0], inside, functions.InjectiveOnSubset.At(restriction, twistedAway, pointsAway)))
		keepsC := arg.Have(
			"s keeps C",
			"∀y:A. y ∈ C ⇒ permutation_map(s, y) ∈ C",
			By(good, inG, galois_good_open.GroupKeepsChart.Read(M).At(k, L, C, t, a, s)))
		atParameter := arg.Have(
			"a point of C sends c(t) to c at the image of t",
			Statement{
				Binders:    "∀ψ:(A → A).",
				Hypotheses: []string{"ψ ∈ geometric_evaluation_points(M, k, C)"},
				Conclusion: "ψ(polynomial_eval(c, t)) = polynomial_eval(c, ψ(t))",
			},
			Derive(func(b *Argument) {
				ψ := b.FixAs[Fun[A, A]]("ψ")
				point := b.Assume()
				b.Show(
					"it fixes the coefficients of c",
					By(
						kInC,
						good,
						galois_good_open.GoodOpenParameterInChart.Read(M).At(k, L, C, t, a),
						overK,
						point,
						galois_good_open.GeometricEvaluationPointsDef.At(ops, k, C),
						galois_good_open.PointAtPolynomialValue.Read(M).At(k, C, closure, t, c, ψ)))
			}))
		pointwise := arg.Have(
			"a map is the restriction of a twisted point of the localization "+
				"exactly when it is a twisted point of C not killed by c at t",
			"∀ψ:(A → A). ψ ∈ image(«restriction», «twisted»(«away»)) ⇔ ψ ∈ «live»",
			Derive(func(b *Argument) {
				ψ := b.FixAs[Fun[A, A]]("ψ")
				b.Iff()
				b.Forward(
					"the restriction of a twisted point is twisted",
					func(d *Argument, inImage Fact) {
						e, chosen := d.ObtainAs[Fun[A, A]](
							"ψ restricts a twisted point e",
							"∃e:(A → A). ψ = «restriction»(e) ∧ e ∈ «twisted»(«away»)",
							By(inImage, set_basic.InImage.At(restriction, twistedAway, ψ)))
						parts := d.Conjuncts(
							chosen,
							"ψ restricts e",
							"e is twisted")
						data := d.Conjuncts(
							d.Have(
								"e is a point with its twist",
								"e ∈ geometric_evaluation_points(M, k, «away») ∧ "+
									"(∀x:A. x ∈ «away» ⇒ monoid_pow(M.mul, M.one, e(x), card(k) ^ m) = e(permutation_map(s, x)))",
								BySets(parts[1], twistedOnAway)),
							"e is a point of the localization",
							"e is twisted on the localization")
						restricts := d.Have(
							"ψ restricts a point",
							"∃g:(A → A). ψ = «restriction»(g) ∧ g ∈ geometric_evaluation_points(M, k, «away»)",
							Witness(e),
							By(parts[0], data[0]))
						amongPoints := d.Have(
							"so ψ lies in the image on the points",
							"ψ ∈ image(«restriction», geometric_evaluation_points(M, k, «away»))",
							By(restricts, set_basic.InImage.At(restriction, pointsAway, ψ)))
						pointOfC := d.Conjuncts(
							d.Have(
								"so ψ is a point of C not killing c(t)",
								"ψ ∈ geometric_evaluation_points(M, k, C) ∧ ψ(polynomial_eval(c, t)) ≠ M.zero",
								BySets(amongPoints, bijection[1])),
							"ψ is a point of C",
							"ψ does not kill c(t)")
						twist := d.Have(
							"and ψ is twisted, s keeping C",
							"∀x:A. x ∈ C ⇒ monoid_pow(M.mul, M.one, ψ(x), card(k) ^ m) = ψ(permutation_map(s, x))",
							Derive(func(f *Argument) {
								x := f.FixAs[A]("x")
								inC := f.Assume()
								inAway := f.Have(
									"x lies in the localization",
									"x ∈ «away»",
									BySets(inC, chart.inAway))
								moved := f.Have(
									"s x lies in C",
									"permutation_map(s, x) ∈ C",
									By(inC, keepsC.At(x)))
								f.Show(
									"ψ is e on C",
									By(parts[0], inC, moved, inAway, data[1].At(x)))
							}))
						d.Show(
							"so ψ is a twisted point of C not killed by c at t",
							BySets(pointOfC[0], pointOfC[1], atParameter.At(ψ), twist, twistedOnC))
					})
				b.Backward(
					"an extension of a twisted point is twisted",
					func(d *Argument, inLive Fact) {
						parts := d.Conjuncts(
							d.Have(
								"ψ is a twisted point of C not killed by c at t",
								"ψ ∈ geometric_evaluation_points(M, k, C) ∧ "+
									"(∀x:A. x ∈ C ⇒ monoid_pow(M.mul, M.one, ψ(x), card(k) ^ m) = ψ(permutation_map(s, x))) ∧ "+
									"polynomial_eval(c, ψ(t)) ≠ M.zero",
								BySets(inLive, twistedOnC)),
							"ψ is a point of C",
							"ψ is twisted",
							"c does not vanish at the image of t")
						pointAlive := d.Have(
							"so ψ does not kill c(t)",
							"ψ ∈ {φ:A → A | φ ∈ geometric_evaluation_points(M, k, C) ∧ φ(polynomial_eval(c, t)) ≠ M.zero}",
							BySets(parts[0], atParameter.At(ψ), parts[2]))
						amongPoints := d.Have(
							"so ψ lies in the image on the points",
							"ψ ∈ image(«restriction», geometric_evaluation_points(M, k, «away»))",
							bijection[1].Rw(),
							By(pointAlive))
						e, chosen := d.ObtainAs[Fun[A, A]](
							"ψ restricts a point e of the localization",
							"∃e:(A → A). ψ = «restriction»(e) ∧ e ∈ geometric_evaluation_points(M, k, «away»)",
							By(amongPoints, set_basic.InImage.At(restriction, pointsAway, ψ)))
						restricted := d.Conjuncts(
							chosen,
							"ψ restricts e",
							"e is a point of the localization")
						onC := d.Have(
							"e is twisted on C, being ψ there",
							"∀x:A. x ∈ C ⇒ monoid_pow(M.mul, M.one, e(x), card(k) ^ m) = e(permutation_map(s, x))",
							Derive(func(f *Argument) {
								x := f.FixAs[A]("x")
								inC := f.Assume()
								moved := f.Have(
									"s x lies in C",
									"permutation_map(s, x) ∈ C",
									By(inC, keepsC.At(x)))
								f.Show(
									"ψ is e on C",
									By(restricted[0], inC, moved, parts[1].At(x)))
							}))
						spreads := d.Have(
							"so it is twisted on the localization",
							"∀y:A. y ∈ «away» ⇒ monoid_pow(M.mul, M.one, e(y), card(k) ^ m) = e(permutation_map(s, y))",
							Derive(func(f *Argument) {
								y := f.FixAs[A]("y")
								inAway := f.Assume()
								f.Show(
									"the twist spreads from C",
									By(
										closedField,
										good,
										overK,
										nonzero,
										positive,
										inG,
										restricted[1],
										onC,
										inAway,
										TwistEquationAway.Read(M).At(k, L, C, t, a, c, m, s, e, y)))
							}))
						twistedPoint := d.Have(
							"so e is a twisted point of the localization",
							"e ∈ «twisted»(«away»)",
							BySets(restricted[1], spreads, twistedOnAway))
						restricts := d.Have(
							"ψ restricts a twisted point",
							"∃g:(A → A). ψ = «restriction»(g) ∧ g ∈ «twisted»(«away»)",
							Witness(e),
							By(restricted[0], twistedPoint))
						d.Show(
							"so ψ lies in the image on the twisted points",
							By(restricts, set_basic.InImage.At(restriction, twistedAway, ψ)))
					})
			}))
		arg.Show(
			"restriction is injective, and its image is the twisted points of C not killed by c at t",
			By(
				injective,
				pointwise,
				set_basic.Extension.At(
					arg.TermAs[Set[Fun[A, A]]]("image(«restriction», «twisted»(«away»))"),
					arg.TermAs[Set[Fun[A, A]]]("«live»"))))
	}),
})}

// PointsOverRootsBound — a set of points of a good open chart killing the
// nonzero polynomial c at t has at most card(G) · deg(c) points: each carries
// c(t) to c at its value at t, so the set lies among the points of C killing
// c(t); over each value of t lie at most card(G) points of C, a torsor of G
// over a good base point and none elsewhere; and KilledPointsBound counts the
// points killing c(t).
var PointsOverRootsBound = pointsOverRootsBoundThm{family.Add(registry.ProofEntry{
	Name: "PointsOverRootsBound",
	Key:  "prop_664c3f67f1314c77",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "G", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "killed", Text: "{ev:(A → A) | " +
				"    ev ∈ geometric_evaluation_points(M, k, C) ∧ ev(polynomial_eval(c, t)) = M.zero}"},
			{Name: "fibre", Text: "λy:A. geometric_fibre(M, k, C, t, y)"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a c:(num → A). ∀S:set(A → A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"polynomial_over(k, c)",
			"c ≠ vec_zero",
			"∀ev:(A → A). " +
				"    ev ∈ S ⇒ ev ∈ geometric_evaluation_points(M, k, C) ∧ polynomial_eval(c, ev(t)) = M.zero",
		},
		Conclusion: "card(S) ≤ card(«G») * polynomial_degree(c)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a, c *Arrow[Nat, A],
		S *Expr[Set[Fun[A, A]]],
		good, overK, nonzero, inS Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		killed := arg.TermAs[Set[Fun[A, A]]]("«killed»")
		size := arg.TermAs[Nat]("card(«G»)")
		kInC := arg.Have(
			"k lies in C",
			"k ⊆ C",
			By(good, galois_good_open.GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a)))
		tInC := arg.Have(
			"t lies in C",
			"t ∈ C",
			By(good, galois_good_open.GoodOpenParameterInChart.Read(M).At(k, L, C, t, a)))
		subringC := arg.Have(
			"C is a subring",
			"subring(field_ring(M), C)",
			By(good, galois_good_open.GoodOpenChartSubring.Read(M).At(k, L, C, t, a)))
		algebraicSubfield := arg.Have(
			"the algebraic elements are a subfield",
			"subfield(M, algebraic_elements(M, k))",
			By(
				galois_good_open.GoodOpenConstantsSubfield.Read(good),
				algebraic_element.AlgebraicElementsSubfield.Read(M).AsFact().At(k)))
		carried := arg.Have(
			"a point of C carries c(t) to c at the image of t",
			Statement{
				Binders:    "∀ev:(A → A).",
				Hypotheses: []string{"ev ∈ geometric_evaluation_points(M, k, C)"},
				Conclusion: "ev(polynomial_eval(c, t)) = polynomial_eval(c, ev(t))",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				point := b.Assume()
				b.Show(
					"it fixes the coefficients of c",
					By(
						kInC,
						tInC,
						overK,
						point,
						galois_good_open.GeometricEvaluationPointsDef.At(ops, k, C),
						galois_good_open.PointAtPolynomialValue.Read(M).At(k, C, closure, t, c, ev)))
			}))
		among := arg.Have(
			"so the points of S kill c(t)",
			"S ⊆ «killed»",
			BySets(inS, carried))
		overGood := arg.Have(
			"a point of C sends t to a good base point",
			Statement{
				Binders:    "∀ev:(A → A).",
				Hypotheses: []string{"ev ∈ geometric_evaluation_points(M, k, C)"},
				Conclusion: "ev(t) ∈ algebraic_elements(M, k) ∧ polynomial_eval(a, ev(t)) ≠ M.zero",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				point := b.Assume()
				b.Show(
					"the chart inverts a(t)",
					By(good, point, GoodPointBase.Read(M).At(k, L, t, C, a, ev)))
			}))
		fibres := arg.Have(
			"over each value of t lie finitely many points of C, at most card(G)",
			"∀y:A. finite(«fibre»(y)) ∧ card(«fibre»(y)) ≤ card(«G»)",
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				b.Cases(b.Term("y ∈ algebraic_elements(M, k) ∧ polynomial_eval(a, y) ≠ M.zero"))
				b.When(
					"over a good base point the fibre is a torsor of G",
					func(d *Argument, goodBase Fact) {
						fibre := galois_good_open.ReadGoodFibre(d, good, y, goodBase)
						finiteFibre := d.Have(
							"G acts freely on the fibre, which is finite",
							"finite(«fibre»(y))",
							By(d.Unfolded(fibre.Free, twisted_counting.FreeFiniteActionDef)))
						d.Show(
							"and has card(G) points",
							ByArith(finiteFibre, fibre.Card))
					})
				b.Otherwise(
					"over any other value lies no point of C",
					func(d *Argument, bad Fact) {
						empty := d.Have(
							"each point of C sends t to a good base point",
							"«fibre»(y) = ∅",
							BySets(galois_good_open.GeometricFibreDef.At(ops, k, C, t, y), bad, overGood))
						d.Show(
							"and the empty set is finite, with no points",
							empty.Rw(),
							ByArith(finite_set.FiniteRules.Inst[Fun[A, A]](), cardinality.CardClauses.Inst[Fun[A, A]]()))
					})
			}))
		bound := arg.Conjuncts(
			arg.Simplified(
				GroupPremises(
					subringC,
					algebraicSubfield,
					kInC,
					tInC,
					overK,
					nonzero,
					arg.Simplified(
						fibres,
						Fwd(galois_good_open.GeometricFibreDef),
						Fwd(galois_good_open.GeometricEvaluationPointsDef)),
					algebra_point_bounds.KilledPointsBound.Read(M).At(C, k, closure, t, c, size)),
				Rev(galois_good_open.GeometricEvaluationPointsDef)),
			"the points of C killing c(t) are finitely many",
			"they number at most deg(c) · card(G)")
		fewer := arg.Have(
			"S has no more points than those",
			"card(S) ≤ card(«killed»)",
			By(bound[0], among, cardinality.CardSubset.At(S, killed)))
		arg.Show(
			"so at most card(G) · deg(c)",
			ByArith(fewer, bound[1]))
	}),
})}

// TwistedCountOffRefinement — inverting c(t) changes the count of points twisted
// by s by at most card(G) · deg(c): the twisted points of the localization are
// those of C not killed by c at t (TwistedPointsAway), and those killed are few
// (PointsOverRootsBound).
var TwistedCountOffRefinement = twistedCountOffRefinementThm{family.Add(registry.ProofEntry{
	Name: "TwistedCountOffRefinement",
	Key:  "prop_a0f73ecdd7f4525c",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "G", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "away", Text: "ring_away(field_ring(M), C, polynomial_eval(c, t))"},
			{Name: "twisted", Text: "λX:set(A). twisted_evaluations(M, k, X, card(k) ^ m, s)"},
			{Name: "live", Text: "{ev:(A → A) | ev ∈ «twisted»(C) ∧ polynomial_eval(c, ev(t)) ≠ M.zero}"},
			{Name: "dead", Text: "{ev:(A → A) | ev ∈ «twisted»(C) ∧ polynomial_eval(c, ev(t)) = M.zero}"},
			{Name: "restriction", Text: "λev:(A → A). λy:A. COND(y ∈ C, ev(y), M.zero)"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a c:(num → A). ∀m:num. ∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"galois_good_open(M, k, L, t, C, a)",
			"polynomial_over(k, c)",
			"c ≠ vec_zero",
			"0 < m",
			"s ∈ «G»",
		},
		Conclusion: "twisted_evaluation_count(M, k, «away», card(k) ^ m, s) ≤ " +
			"twisted_evaluation_count(M, k, C, card(k) ^ m, s) ∧ " +
			"twisted_evaluation_count(M, k, C, card(k) ^ m, s) ≤ " +
			"twisted_evaluation_count(M, k, «away», card(k) ^ m, s) + card(«G») * polynomial_degree(c)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a, c *Arrow[Nat, A],
		m *Expr[Nat],
		s *Expr[symmetric_group.Permutation[A]],
		closedField, good, overK, nonzero, positive, inG Fact,
	) {
		away := arg.TermAs[Set[A]]("«away»")
		product := arg.TermAs[Fun[Nat, A]]("polynomial_mul(a, c)")
		restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		twistedC := arg.TermAs[Set[Fun[A, A]]]("«twisted»(C)")
		twistedAway := arg.TermAs[Set[Fun[A, A]]]("«twisted»(«away»)")
		live := arg.TermAs[Set[Fun[A, A]]]("«live»")
		dead := arg.TermAs[Set[Fun[A, A]]]("«dead»")
		chart := readChartAway(arg, M, k, L, C, t, a, c, good, overK, nonzero)
		finiteC := arg.Have(
			"C has finitely many twisted points",
			"finite(«twisted»(C))",
			By(closedField, good, positive, inG, TwistedEvaluationsFinite.Read(M).At(k, L, t, C, a, m, s)))
		finiteAway := arg.Have(
			"and so does the localization",
			"finite(«twisted»(«away»))",
			By(
				closedField,
				chart.localized,
				positive,
				inG,
				TwistedEvaluationsFinite.Read(M).At(k, L, t, away, product, m, s)))
		bijection := arg.Conjuncts(
			GroupPremises(
				closedField,
				good,
				overK,
				nonzero,
				positive,
				inG,
				TwistedPointsAway.Read(M).At(k, L, C, t, a, c, m, s)),
			"restriction is injective on the twisted points of the localization",
			"its image is the twisted points of C not killed by c at t")
		liveCount := arg.Have(
			"the twisted points of C not killed by c at t are as many as those of the localization",
			"card(«live») = card(«twisted»(«away»))",
			bijection[1].RwRev(),
			By(finiteAway, bijection[0], cardinality.CardImageInj.At(restriction, twistedAway)))
		partition := arg.Have(
			"c at t kills a twisted point of C or does not, and not both",
			"«dead» ∪ «live» = «twisted»(C) ∧ «dead» ∩ «live» = ∅",
			BySets())
		split := arg.Have(
			"so C counts the two parts",
			"card(«twisted»(C)) = card(«dead») + card(«live»)",
			By(finiteC, partition, cardinality.CardOfDisjointParts.At(dead, live, twistedC)))
		killed := arg.Have(
			"they are points of C killing c at t",
			Statement{
				Binders: "∀ev:(A → A).",
				Hypotheses: []string{
					"ev ∈ «dead»",
				},
				Conclusion: "ev ∈ geometric_evaluation_points(M, k, C) ∧ polynomial_eval(c, ev(t)) = M.zero",
			},
			BySets(
				TwistedEvaluationsDef.At(arg.TermAs[FieldOps[A]]("M"), k, C, arg.TermAs[Nat]("card(k) ^ m"), s)))
		deadBound := arg.Have(
			"so they number at most card(G) · deg(c)",
			"card(«dead») ≤ card(«G») * polynomial_degree(c)",
			By(good, overK, nonzero, killed, PointsOverRootsBound.Read(M).At(k, L, C, t, a, c, dead)))
		arg.Do(Simp(Fwd(TwistedEvaluationCountDef)))
		arg.Show(
			"both bounds follow from the count of C",
			ByArith(liveCount, split, deadBound))
	}),
})}
