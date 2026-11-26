// arithmetic.go — the arithmetic of closed divisors. A closed divisor's
// pair is a finite product in the commutative monoid of invertible pairs
// and its degree a finite sum of integers; both are read at the integer
// exponents of their points. So the sum of two divisors is one enlarged
// fold over the union of the supports, split term by term.

package closed_divisor

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/signed_ideal_power"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CurveDivisorPairProduct — the invertible pairs of a curve are a commutative
// monoid, each with its integer powers P^[n], P⁻¹ taken n times for n ≥ 0 and
// P taken −n times for n < 0; and the pair of a divisor with finite invertible
// support is the product of the powers of its points. The fold of a divisor's
// steps and the monoid's product over its support take a new pair alike.
var CurveDivisorPairProduct = curveDivisorPairProductThm{family.Add(registry.ProofEntry{
	Name: "CurveDivisorPairProduct",
	Key:  "prop_92ae3b6ac8d79c93",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "comm_monoid_on(«invertiblePairs», «pairMul», (A₀, A₁)) ∧ " +
			"(∀X Y:prod(set(A), set(A)). " +
			"    «pairInvertible»(X) ∧ «pairInvertible»(Y) ∧ «pairMul»(X, Y) = (A₀, A₁) ⇒ " +
			"    Y = «pairInverse»(X)) ∧ " +
			"(∀P:prod(set(A), set(A)). " +
			"    «pairInvertible»(P) ⇒ " +
			"    «pairPower»(P, int_of_num(0)) = (A₀, A₁) ∧ " +
			"    «pairPower»(P, -int_of_num(1)) = P ∧ " +
			"    (∀n:int. «pairPower»(P, n) ∈ «invertiblePairs») ∧ " +
			"    (∀i j:int. «pairPower»(P, i + j) = «pairMul»(«pairPower»(P, i), «pairPower»(P, j)))) ∧ " +
			"(∀D:(prod(set(A), set(A)) → int). " +
			"    finite(fun_support(int_of_num(0), D)) ∧ " +
			"    (∀P:prod(set(A), set(A)). D(P) ≠ 0 ⇒ «pairInvertible»(P)) ⇒ " +
			"    «pairInvertible»(curve_divisor_pair(field_ring(L), A₀, A₁, A₀₁, D)) ∧ " +
			"    curve_divisor_pair(field_ring(L), A₀, A₁, A₀₁, D) = " +
			"    module_sum(«pairMul», " +
			"        (A₀, A₁), " +
			"        fun_support(int_of_num(0), D), " +
			"        λP:prod(set(A), set(A)). «pairPower»(P, D(P))))",
		Abbrev: Abbrev{
			{Name: "pairMul", Text: "lattice_pair_mul(field_ring(L), A₀, A₁)"},
			{Name: "pairInverse", Text: "lattice_pair_inverse(field_ring(L), A₀, A₁)"},
			{Name: "pairInvertible", Text: "invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁)"},
			{Name: "invertiblePairs", Text: "{N:prod(set(A), set(A)) | «pairInvertible»(N)}"},
			{Name: "pairPower", Text: "λP:prod(set(A), set(A)). λn:int. " +
				"    COND(&0 ≤ n, " +
				"        monoid_pow(«pairMul», (A₀, A₁), «pairInverse»(P), num_of_int(n)), " +
				"        monoid_pow(«pairMul», (A₀, A₁), P, num_of_int(-n)))"},
			{Name: "divisorStep", Text: "λD:(prod(set(A), set(A)) → int). " +
				"λP:prod(set(A), set(A)). " +
				"λN:prod(set(A), set(A)). " +
				"    COND(«pairInvertible»(P), «pairMul»(«pairPower»(P, D(P)), N), N)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			data := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			overlapInField, biaffine := data[0], data[1]
			monoid := a.Have(
				"the invertible pairs form a commutative monoid "+
					"under the product, with the structure pair its unit",
				"comm_monoid_on(«invertiblePairs», «pairMul», (A₀, A₁))",
				By(
					overlapInField,
					biaffine,
					invertible_lattice_pair.InvertiblePairsCommMonoid.Read(L).At(A0, A1, A01, t)))
			unique := a.Have(
				"a pair's inverse is the only pair multiplying it to the structure pair",
				Statement{
					Binders:    "∀X Y:prod(set(A), set(A)).",
					Hypotheses: []string{"«pairInvertible»(X) ∧ «pairInvertible»(Y) ∧ «pairMul»(X, Y) = (A₀, A₁)"},
					Conclusion: "Y = «pairInverse»(X)",
				},
				Derive(func(b *Argument) {
					X, Y := b.FixAs[_IdealPair]("X"), b.FixAs[_IdealPair]("Y")
					given := b.Conjuncts(
						b.Assume(),
						"X is invertible",
						"Y is invertible",
						"X and Y multiply to the structure pair")
					inverse := b.Conjuncts(
						GroupPremises(
							data[0],
							data[1],
							given[0],
							invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, X)),
						"the inverse pair is invertible",
						"X times its inverse is the structure pair",
						"the inverse of the inverse is X")
					inv := b.TermAs[_IdealPair]("«pairInverse»(X)")
					b.Show(
						"Y is the structure pair times Y, which regroups to the inverse of X times the structure pair",
						CalcEq(
							Leg(
								b.TermAs[_IdealPair]("«pairMul»(«pairMul»(X, «pairInverse»(X)), Y)"),
								"X times its inverse is the structure pair, the unit",
								By(inverse[1], given[1], comm_monoid.LeftIdentityOn.Read(monoid).AsFact().At(Y))),
							Leg(
								b.TermAs[_IdealPair]("«pairMul»(«pairMul»(«pairInverse»(X), X), Y)"),
								"the two factors commute",
								By(given[0], inverse[0], comm_monoid.CommOn.Read(monoid).AsFact().At(X, inv))),
							Leg(
								b.TermAs[_IdealPair]("«pairMul»(«pairInverse»(X), «pairMul»(X, Y))"),
								"the product associates",
								By(given[0], given[1], inverse[0], comm_monoid.AssocOn.Read(monoid).AsFact().At(inv, X, Y))),
							Leg(
								b.TermAs[_IdealPair]("«pairMul»(«pairInverse»(X), (A₀, A₁))"),
								"X and Y multiply to the structure pair",
								By(Normalized, given[2])),
							FinalLeg(
								"the structure pair is the unit",
								By(inverse[0], comm_monoid.RightIdentityOn.Read(monoid).AsFact().At(inv)))))
				}))
			laws := a.Have(
				"at an invertible pair the integer powers follow the signed power laws",
				Statement{
					Binders:    "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{"«pairInvertible»(P)"},
					Conclusion: "«pairPower»(P, int_of_num(0)) = (A₀, A₁) ∧ " +
						"«pairPower»(P, -int_of_num(1)) = P ∧ " +
						"(∀n:int. «pairPower»(P, n) ∈ «invertiblePairs») ∧ " +
						"(∀i j:int. «pairPower»(P, i + j) = «pairMul»(«pairPower»(P, i), «pairPower»(P, j)))",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					invertible := b.Assume()
					inverse := b.Conjuncts(
						GroupPremises(
							data[0],
							data[1],
							invertible,
							invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, P)),
						"the inverse pair is invertible",
						"P times its inverse is the structure pair",
						"the inverse of the inverse is P")
					b.Show(
						"P and its inverse are inverse members of the monoid",
						By(
							invertible,
							inverse[0],
							inverse[1],
							Read(signed_ideal_power.SignedPowerLaws, monoid).At(P, b.TermAs[_IdealPair]("«pairInverse»(P)"))))
				}))
			products := a.Have(
				"a divisor with finite invertible support has the product of its powers as its pair",
				Statement{
					Binders: "∀D:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{
						"finite(fun_support(int_of_num(0), D)) ∧ (∀P:prod(set(A), set(A)). D(P) ≠ 0 ⇒ «pairInvertible»(P))",
					},
					Conclusion: "«pairInvertible»(curve_divisor_pair(field_ring(L), A₀, A₁, A₀₁, D)) ∧ " +
						"curve_divisor_pair(field_ring(L), A₀, A₁, A₀₁, D) = " +
						"module_sum(«pairMul», " +
						"    (A₀, A₁), " +
						"    fun_support(int_of_num(0), D), " +
						"    λP:prod(set(A), set(A)). «pairPower»(P, D(P)))",
				},
				Derive(func(b *Argument) {
					D := b.FixAs[Fun[_IdealPair, Int]]("D")
					support := b.Conjuncts(
						b.Assume(),
						"the support is finite",
						"its pairs are invertible")
					fold := b.Conjuncts(
						GroupPremises(curve, curve_degree.DivisorFoldRecursion.Read(L).At(k, A0, A1, A01, t, D)),
						"the empty fold is the structure pair",
						"a new pair applies its step to the fold before it",
						"every finite fold is invertible")
					term := b.TermAs[Fun[_IdealPair, _IdealPair]]("λP:prod(set(A), set(A)). «pairPower»(P, D(P))")
					supportSet := b.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), D)")
					b.Do(Unfold(curve_degree.CurveDivisorPairDef))
					invertible := b.Have(
						"the fold over the finite support is invertible",
						"«pairInvertible»(set_fold(«divisorStep»(D), fun_support(int_of_num(0), D), (A₀, A₁)))",
						By(support[0], fold[2].At(supportSet)))
					value := b.Have(
						"the fold and the product agree on every finite set of invertible pairs, the support among them",
						"set_fold(«divisorStep»(D), fun_support(int_of_num(0), D), (A₀, A₁)) = "+
							"module_sum(«pairMul», "+
							"    (A₀, A₁), "+
							"    fun_support(int_of_num(0), D), "+
							"    λP:prod(set(A), set(A)). «pairPower»(P, D(P)))",
						ByInduction(
							finite_set.FiniteInductFreshOn.At(
								b.TermAs[Set[Set[_IdealPair]]](
									"λu:set(prod(set(A), set(A))). "+
										"    set_fold(«divisorStep»(D), u, (A₀, A₁)) = "+
										"    module_sum(«pairMul», (A₀, A₁), u, λP:prod(set(A), set(A)). «pairPower»(P, D(P)))"),
								b.TermAs[Set[_IdealPair]]("λP:prod(set(A), set(A)). «pairInvertible»(P)"),
								supportSet),
							support[0],
							support[1],
							functions.InFunSupport,
							Case(
								"the empty fold and the empty product are the structure pair",
								By(fold[0], module.ModuleSumEmpty)),
							Case(
								"a new pair multiplies both by its power",
								Derive(func(c *Argument) {
									P := c.FixAs[_IdealPair]("P")
									u := c.FixAs[Set[_IdealPair]]("u")
									carried := c.Conjuncts(
										c.Assume(),
										"the fold and the product agree on u",
										"P is a new pair of u",
										"u is finite",
										"P is invertible",
										"the pairs of u are invertible")
									agree, fresh, finite, invertible, onU := carried[0], carried[1], carried[2], carried[3], carried[4]
									powers := c.Have(
										"the powers of a pair of u are invertible",
										"∀Q:prod(set(A), set(A)). Q ∈ u ⇒ «pairPower»(Q, D(Q)) ∈ «invertiblePairs»",
										Derive(func(d *Argument) {
											Q := d.FixAs[_IdealPair]("Q")
											inU := d.Assume()
											d.Show(
												"Q is invertible",
												By(inU, onU.At(Q), laws.At(Q)))
										}))
									stepped := c.Have(
										"the fold takes P by its step",
										"set_fold(«divisorStep»(D), insert(P, u), (A₀, A₁)) = "+
											"«pairMul»(«pairPower»(P, D(P)), set_fold(«divisorStep»(D), u, (A₀, A₁)))",
										By(fresh, finite, invertible, fold[1].At(P, u)))
									power := c.Have(
										"the power at P is invertible",
										"«pairPower»(P, D(P)) ∈ «invertiblePairs»",
										By(invertible, laws.At(P)))
									taken := c.Have(
										"the product takes P by its power",
										"module_sum(«pairMul», (A₀, A₁), insert(P, u), λQ:prod(set(A), set(A)). «pairPower»(Q, D(Q))) = "+
											"«pairMul»(«pairPower»(P, D(P)), "+
											"    module_sum(«pairMul», (A₀, A₁), u, λQ:prod(set(A), set(A)). «pairPower»(Q, D(Q))))",
										By(fresh, finite, power, powers, Read(module.ModuleSumInsertMonoid, monoid).At(u, P, term)))
									c.Show(
										"both take the factor at P",
										By(agree, stepped, taken))
								}))))
					b.Show(
						"the fold over the support is the invertible pair, and it is the product",
						By(invertible, value))
				}))
			a.Show(
				"the monoid, its inverses, its powers and the products",
				By(monoid, unique, laws, products))
		}),
})}

// ChartPointInvertible — the ideal a closed point has in a chart, the whole
// chart off the point and a maximal ideal on it, is an invertible fractional
// ideal inside the chart. The whole chart is the structure pair's, and a
// maximal ideal of a chart is a nonzero ideal.
var ChartPointInvertible = chartPointInvertibleThm{family.Add(registry.ProofEntry{
	Name: "ChartPointInvertible",
	Key:  "prop_165ec96913d1ca7f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀H:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"H = A₀ ∨ maximal_ideal(restrict_ring(field_ring(L), A₀), H)",
		},
		Conclusion: "invertible_fractional(field_ring(L), A₀, H) ∧ H ⊆ A₀",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			H *Expr[Set[A]],
			curve, chartPoint Fact,
		) {
			a.Cases(a.TermAs[Bool]("H = A₀"))
			a.When(
				"the whole chart is the first component of the invertible structure pair",
				func(b *Argument, whole Fact) {
					overLine := b.Have(
						"the curve lies over the line of t",
						"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
						By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
					data := b.Conjuncts(
						GroupPremises(overLine, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
						"the overlap lies in L",
						"the charts and their overlap are a biaffine datum",
						"k is a subfield",
						"the structure pair is a lattice pair",
						"its ambient is the overlap",
						"the structure pair is invertible",
						"the constants form a field",
						"the constants lie in both charts")
					chart := b.Have(
						"so chart 0, its first component, is invertible",
						"invertible_fractional(field_ring(L), A₀, A₀)",
						By(b.Unfolded(data[5], invertible_lattice_pair.InvertibleLatticePairDef), pairs.Fst))
					b.Show(
						"H is chart 0, a part of itself",
						whole.Rw(),
						By(chart, set_order.SubsetRefl))
				})
			a.Otherwise(
				"a maximal ideal of the chart is a nonzero ideal",
				func(b *Argument, notWhole Fact) {
					maximal := b.Have(
						"H, not the whole chart, is maximal in it",
						"maximal_ideal(restrict_ring(field_ring(L), A₀), H)",
						By(Normalized, notWhole, chartPoint))
					ideal := b.Have(
						"so it is an ideal",
						"ring_ideal(restrict_ring(field_ring(L), A₀), H)",
						By(
							maximal,
							ring_ideal.MaximalIdealDef.At(b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀)"), H)))
					subring := b.Have(
						"of a chart that is a subring of L",
						"subring(field_ring(L), A₀)",
						By(curve, smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t)))
					inChart := b.Have(
						"so H lies in the chart",
						"H ⊆ A₀",
						By(subring, ideal, fractional_ideal.IntegralIdealFractional.Read(L).At(A0, H)))
					invertible := b.Have(
						"and H, a nonzero ideal, is invertible",
						"invertible_fractional(field_ring(L), A₀, H)",
						By(
							curve,
							maximal,
							ideal,
							smooth_curve.ChartMaximalNonzero.Read(L).At(k, A0, A1, A01, t, H),
							smooth_curve.ChartIdealInvertible.Read(L).At(k, A0, A1, A01, t, H)))
					b.Show(
						"H is invertible, and lies in the chart",
						By(invertible, inChart))
				})
		}),
})}

// ChartIdealsInvertiblePair — two invertible fractional ideals inside the two
// charts of a curve that generate one ideal of the overlap are an invertible
// pair: each is a module over its chart, and the ideal of the overlap each
// generates is its span, so the two spans agree.
var ChartIdealsInvertiblePair = chartIdealsInvertiblePairThm{family.Add(registry.ProofEntry{
	Name: "ChartIdealsInvertiblePair",
	Key:  "prop_d62111715b6e7ef4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"invertible_fractional(field_ring(L), A₀, fst(P)) ∧ fst(P) ⊆ A₀",
			"invertible_fractional(field_ring(L), A₁, snd(P)) ∧ snd(P) ⊆ A₁",
			"ideal_span(«overlap», fst(P)) = ideal_span(«overlap», snd(P))",
		},
		Conclusion: "«scInvertible»(P)",
		Abbrev: Abbrev{
			{Name: "field", Text: "regular_module(field_ring(L))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the curve",
				"fst(P) is invertible",
				"inside chart 0",
				"snd(P) is invertible",
				"inside chart 1",
				"they generate one ideal of the overlap")
			invertible0, in0, invertible1, in1, spans := given[1], given[2], given[3], given[4], given[5]
			data := a.Conjuncts(
				GroupPremises(given[0], algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in the field",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field under L's operations",
				"the constants lie in both charts")
			rings := a.Conjuncts(
				GroupPremises(
					data[0], data[1], invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, t)),
				"chart 0 lies in the overlap",
				"chart 1 lies in the overlap",
				"the overlap is a subring of L",
				"chart 0 is a subring of L",
				"chart 1 is a subring of L")
			structure := a.Conjuncts(
				a.Unfolded(data[3], lattice_pair.LatticePairDef),
				"the field is a module over the overlap",
				"chart 0 is a module over itself",
				"chart 1 is a module over itself",
				"and the two span one module")
			inOverlap := a.Have(
				"the two ideals lie in the overlap",
				"fst(P) ⊆ A₀₁ ∧ snd(P) ⊆ A₀₁",
				BySets(rings[0], rings[1], in0, in1))
			parts := a.Conjuncts(
				inOverlap,
				"fst(P) lies in the overlap",
				"snd(P) lies in the overlap")
			fstP, sndP := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			spanned := a.Have(
				"so the two span one module over the overlap",
				"module_span(«overlap», «field», fst(P)) = module_span(«overlap», «field», snd(P))",
				By(
					spans,
					rings[2],
					parts[0],
					parts[1],
					fractional_ideal.SpanInSubringIsIdealSpan.Read(L).At(A01, fstP),
					fractional_ideal.SpanInSubringIsIdealSpan.Read(L).At(A01, sndP)))
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			lattice := a.Have(
				"P is a lattice pair over the overlap",
				"lattice_pair(«overlap», A₀, A₁, «field», P)",
				Unfold(lattice_pair.LatticePairDef),
				Simp(Fwd(module_record.RestrictRingTwice)),
				By(
					structure[0],
					invertible0,
					invertible1,
					spanned,
					fractional_ideal.InvertibleFractionalDef.At(ring, A0, fstP),
					fractional_ideal.InvertibleFractionalDef.At(ring, A1, sndP)))
			a.Show(
				"the two invertible components and the lattice pair",
				Unfold(invertible_lattice_pair.InvertibleLatticePairDef),
				By(invertible0, invertible1, lattice))
		}),
})}

// ClosedPointInvertible — a closed point of a smooth curve is an invertible
// pair: on each chart its ideal is invertible and lies inside the chart, the
// second chart read through the swap, and the point generates one ideal of the
// overlap.
var ClosedPointInvertible = closedPointInvertibleThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointInvertible",
	Key:  "prop_2429bb8b19728392",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(P)",
		},
		Conclusion: "«scInvertible»(P)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			curve, closedPoint Fact,
		) {
			point := a.Conjuncts(
				a.Unfolded(closedPoint, smooth_curve.CurveClosedPointDef),
				"fst(P) is chart 0 or maximal in it",
				"snd(P) is chart 1 or maximal in it",
				"P is not the structure pair",
				"its two ideals generate one ideal of the overlap",
				"which is proper where P lies on both charts")
			first := a.Have(
				"fst(P) is invertible inside chart 0",
				"invertible_fractional(field_ring(L), A₀, fst(P)) ∧ fst(P) ⊆ A₀",
				By(curve, point[0], ChartPointInvertible.Read(L).At(k, A0, A1, A01, t, a.TermAs[Set[A]]("fst(P)"))))
			swapped := a.Have(
				"the curve reads the same from its other chart",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			second := a.Have(
				"so snd(P) is invertible inside chart 1",
				"invertible_fractional(field_ring(L), A₁, snd(P)) ∧ snd(P) ⊆ A₁",
				By(
					swapped,
					point[1],
					ChartPointInvertible.Read(L).At(
						k, A1, A0, A01, a.TermAs[A]("L.inv(t)"), a.TermAs[Set[A]]("snd(P)"))))
			a.Show(
				"the two ideals, generating one ideal of the overlap, are an invertible pair",
				By(
					curve,
					smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					first,
					second,
					point[3],
					ChartIdealsInvertiblePair.Read(L).At(k, A0, A1, A01, t, P)))
		}),
})}

// ClosedDivisorPairProduct — on a smooth curve the invertible pairs of L are a
// commutative monoid with unique inverses, a closed point is invertible with its
// integer powers, and a closed divisor's pair is invertible and the product of
// the powers of its points. The curve lying over its line gives the monoid and
// the fold; a closed point is invertible, so both read at closed points.
var ClosedDivisorPairProduct = closedDivisorPairProductThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorPairProduct",
	Key:  "prop_e6fa039d98fbcb73",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "comm_monoid_on(«scInvertibles», «scMul», (A₀, A₁)) ∧ " +
			"(∀X Y:prod(set(A), set(A)). " +
			"    «scInvertible»(X) ∧ «scInvertible»(Y) ∧ «scMul»(X, Y) = (A₀, A₁) ⇒ Y = «scInverse»(X)) ∧ " +
			"(∀P:prod(set(A), set(A)). " +
			"    «scPoint»(P) ⇒ " +
			"    «scPower»(P, int_of_num(0)) = (A₀, A₁) ∧ " +
			"    «scPower»(P, -int_of_num(1)) = P ∧ " +
			"    (∀n:int. «scPower»(P, n) ∈ «scInvertibles») ∧ " +
			"    (∀i j:int. «scPower»(P, i + j) = «scMul»(«scPower»(P, i), «scPower»(P, j)))) ∧ " +
			"(∀D:(prod(set(A), set(A)) → int). " +
			"    «scDivisor»(D) ⇒ " +
			"    «scInvertible»(«scPair»(D)) ∧ " +
			"    «scPair»(D) = " +
			"    module_sum(«scMul», " +
			"        (A₀, A₁), " +
			"        fun_support(int_of_num(0), D), " +
			"        λP:prod(set(A), set(A)). «scPower»(P, D(P))))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			overLine := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			laws := a.Conjuncts(
				GroupPremises(overLine, CurveDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at an invertible pair",
				"the pair of a divisor with finite invertible support")
			powers := a.Have(
				"a closed point is invertible, so it has the integer powers of one",
				Statement{
					Binders:    "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{"«scPoint»(P)"},
					Conclusion: "«scPower»(P, int_of_num(0)) = (A₀, A₁) ∧ " +
						"«scPower»(P, -int_of_num(1)) = P ∧ " +
						"(∀n:int. «scPower»(P, n) ∈ «scInvertibles») ∧ " +
						"(∀i j:int. «scPower»(P, i + j) = «scMul»(«scPower»(P, i), «scPower»(P, j)))",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					point := b.Assume()
					invertible := b.Have(
						"P is invertible",
						"«scInvertible»(P)",
						By(curve, point, ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P)))
					b.Show(
						"the laws at the invertible pair P",
						By(Normalized, invertible, laws[2].At(P)))
				}))
			products := a.Have(
				"a closed divisor has finite support of invertible pairs",
				Statement{
					Binders:    "∀D:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{"«scDivisor»(D)"},
					Conclusion: "«scInvertible»(«scPair»(D)) ∧ " +
						"«scPair»(D) = " +
						"module_sum(«scMul», " +
						"    (A₀, A₁), " +
						"    fun_support(int_of_num(0), D), " +
						"    λP:prod(set(A), set(A)). «scPower»(P, D(P)))",
				},
				Derive(func(b *Argument) {
					D := b.FixAs[Fun[_IdealPair, Int]]("D")
					divisor := b.Conjuncts(
						b.Unfolded(b.Assume(), ClosedDivisorDef),
						"the support is finite",
						"its pairs are closed points")
					invertible := b.Have(
						"the pairs of the support are invertible",
						"∀P:prod(set(A), set(A)). D(P) ≠ 0 ⇒ «scInvertible»(P)",
						Derive(func(c *Argument) {
							P := c.FixAs[_IdealPair]("P")
							nonzero := c.Assume()
							c.Show(
								"each is a closed point",
								By(curve, nonzero, divisor[1].At(P), ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P)))
						}))
					b.Show(
						"the pair of a closed divisor is the curve's fold",
						Unfold(ClosedDivisorPairDef),
						By(divisor[0], invertible, laws[3].At(D)))
				}))
			a.Show(
				"the monoid, its inverses, its powers and the products",
				By(laws[0], laws[1], powers, products))
		}),
})}

// ClosedDivisorZero — the zero divisor has empty support, so its pair is the
// empty product, the structure pair, and its degree the empty sum 0.
var ClosedDivisorZero = closedDivisorZeroThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorZero",
	Key:  "prop_c09fa47581261d7f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "«scDivisor»(λP:prod(set(A), set(A)). 0) ∧ " +
			"«scPair»(λP:prod(set(A), set(A)). 0) = (A₀, A₁) ∧ " +
			"«scDegree»(λP:prod(set(A), set(A)). 0) = 0",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			products := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")
			empty := a.Have(
				"no pair has a nonzero coefficient",
				"fun_support(int_of_num(0), λP:prod(set(A), set(A)). 0) = ∅",
				BySets())
			divisor := a.Have(
				"the zero divisor has empty support",
				"«scDivisor»(λP:prod(set(A), set(A)). 0)",
				Unfold(ClosedDivisorDef),
				empty.Rw(),
				By(finite_set.FiniteRules))
			pair := a.Have(
				"its pair is the empty product",
				"«scPair»(λP:prod(set(A), set(A)). 0) = (A₀, A₁)",
				By(
					divisor,
					empty,
					products[3].At(a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). 0")),
					module.ModuleSumEmpty))
			degree := a.Have(
				"its degree is the empty sum",
				"«scDegree»(λP:prod(set(A), set(A)). 0) = 0",
				Unfold(ClosedDivisorDegreeDef),
				empty.Rw(),
				By(module.ModuleSumEmpty))
			a.Show(
				"the zero divisor is closed, with the structure pair and degree 0",
				By(divisor, pair, degree))
		}),
})}

// ClosedDivisorOfSupport — a function supported in a finite set of closed points
// is a closed divisor: its support is a part of that set.
var ClosedDivisorOfSupport = closedDivisorOfSupportThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorOfSupport",
	Key:  "prop_28e6fe9404e38f60",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁ A₀₁:set(A). " +
			"∀s:set(prod(set(A), set(A))). " +
			"∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"finite(s)",
			"∀P:prod(set(A), set(A)). P ∈ s ⇒ curve_closed_point(R, A₀, A₁, A₀₁, P)",
			"∀P:prod(set(A), set(A)). D(P) ≠ 0 ⇒ P ∈ s",
		},
		Conclusion: "closed_divisor(R, A₀, A₁, A₀₁, D)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1, A01 *Expr[Set[A]],
			s *Expr[Set[_IdealPair]],
			D *Arrow[_IdealPair, Int],
			finiteS, closedPoints, supported Fact,
		) {
			part := a.Have(
				"the support of D is a part of s",
				"fun_support(int_of_num(0), D) ⊆ s",
				BySets(supported))
			a.Show(
				"so it is finite, and its pairs are closed points",
				Unfold(ClosedDivisorDef),
				By(
					finiteS,
					closedPoints,
					supported,
					part,
					finite_set.FiniteSubset.At(a.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), D)"), s)))
		}),
})}

// ClosedDivisorAdd — the sum of two closed divisors is a closed divisor, its
// pair the product of their pairs, its degree the sum of their degrees: the
// pair and the degree each read an integer additively at every closed point.
var ClosedDivisorAdd = closedDivisorAddThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorAdd",
	Key:  "prop_661325c58c8b66cf",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D E:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
			"«scDivisor»(E)",
		},
		Conclusion: "«scDivisor»(λP:prod(set(A), set(A)). D(P) + E(P)) ∧ " +
			"«scPair»(λP:prod(set(A), set(A)). D(P) + E(P)) = " +
			"lattice_pair_mul(field_ring(L), A₀, A₁, «scPair»(D), «scPair»(E)) ∧ " +
			"«scDegree»(λP:prod(set(A), set(A)). D(P) + E(P)) = «scDegree»(D) + «scDegree»(E)",
		Abbrev: Abbrev{
			{Name: "supports", Text: "fun_support(int_of_num(0), D) ∪ fun_support(int_of_num(0), E)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D, E *Arrow[_IdealPair, Int],
			curve, closedD, closedE Fact,
		) {
			products := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")
			monoid, powers, pairOf := products[0], products[2], products[3]
			divisorD := a.Conjuncts(
				a.Unfolded(closedD, ClosedDivisorDef),
				"the support of D is finite",
				"its pairs are closed points")
			divisorE := a.Conjuncts(
				a.Unfolded(closedE, ClosedDivisorDef),
				"the support of E is finite",
				"its pairs are closed points")
			supportD := a.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), D)")
			supportE := a.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), E)")
			supports := a.TermAs[Set[_IdealPair]]("«supports»")
			finiteSupports := a.Have(
				"the two supports together are finite",
				"finite(«supports»)",
				By(divisorD[0], divisorE[0], finite_set.FiniteUnion.At(supportD, supportE)))
			inD := a.Have(
				"they hold the support of D",
				"∀P:prod(set(A), set(A)). D(P) ≠ 0 ⇒ P ∈ «supports»",
				BySets())
			inE := a.Have(
				"and the support of E",
				"∀P:prod(set(A), set(A)). E(P) ≠ 0 ⇒ P ∈ «supports»",
				BySets())
			inSum := a.Have(
				"and the support of D + E, whose coefficient vanishes where both do",
				"∀P:prod(set(A), set(A)). D(P) + E(P) ≠ 0 ⇒ P ∈ «supports»",
				Derive(func(b *Argument) {
					b.FixAs[_IdealPair]("P")
					nonzero := b.Assume()
					off := b.SupposeNot()
					vanishes := b.Have(
						"off the two supports both coefficients vanish",
						"D(P) = 0 ∧ E(P) = 0",
						BySets(off))
					b.Show(
						"so their sum vanishes",
						ByArith(nonzero, vanishes))
				}))
			closedPoints := a.Have(
				"the pairs of the two supports are closed points",
				"∀P:prod(set(A), set(A)). P ∈ «supports» ⇒ «scPoint»(P)",
				a.ForEach(func(P *Expr[_IdealPair]) Action {
					return BySets(divisorD[1].At(P), divisorE[1].At(P))
				}))
			divisor := a.Have(
				"so D + E, supported in them, is a closed divisor",
				"«scDivisor»(λP:prod(set(A), set(A)). D(P) + E(P))",
				By(
					finiteSupports,
					closedPoints,
					inSum,
					At(
						ClosedDivisorOfSupport,
						a.TermAs[RingOps[A]]("field_ring(L)"),
						A0,
						A1,
						A01,
						supports,
						a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). D(P) + E(P)"))))
			laws := a.Have(
				"at each point of the two supports the power reads its integer additively",
				Statement{
					Binders: "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{
						"P ∈ «supports»",
					},
					Conclusion: "(∀n:int. «scPower»(P, n) ∈ «scInvertibles») ∧ " +
						"«scPower»(P, int_of_num(0)) = (A₀, A₁) ∧ " +
						"(∀i j:int. «scPower»(P, i + j) = «scMul»(«scPower»(P, i), «scPower»(P, j)))",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					inSupports := b.Assume()
					b.Show(
						"each is a closed point",
						By(Normalized, inSupports, closedPoints.At(P), powers.At(P)))
				}))
			intAdd := a.TermAs[Fun2[Int, Int, Int]]("int_add")
			intZero := a.TermAs[Int]("0")
			pair := a.Have(
				"the pair of D + E is the product of the two pairs",
				"«scPair»(λP:prod(set(A), set(A)). D(P) + E(P)) = "+
					"lattice_pair_mul(field_ring(L), A₀, A₁, «scPair»(D), «scPair»(E))",
				CalcEq(
					Leg(
						a.TermAs[_IdealPair](
							"module_sum(«scMul», "+
								"    (A₀, A₁), "+
								"    fun_support(int_of_num(0), λP:prod(set(A), set(A)). D(P) + E(P)), "+
								"    λP:prod(set(A), set(A)). «scPower»(P, D(P) + E(P)))"),
						"the pair of the closed divisor D + E is the product of its powers",
						By(divisor, pairOf.At(a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). D(P) + E(P)")))),
					Leg(
						a.TermAs[_IdealPair](
							"«scMul»(module_sum(«scMul», "+
								"        (A₀, A₁), "+
								"        fun_support(int_of_num(0), D), "+
								"        λP:prod(set(A), set(A)). «scPower»(P, D(P))), "+
								"    module_sum(«scMul», "+
								"        (A₀, A₁), "+
								"        fun_support(int_of_num(0), E), "+
								"        λP:prod(set(A), set(A)). «scPower»(P, E(P))))"),
						"the sum over the supports splits",
						By(
							finiteSupports,
							inD,
							inE,
							laws,
							module.SupportSumAdditive.Read(monoid).At(
								supports, intAdd, intZero, D, E, a.TermAs[Fun2[_IdealPair, Int, _IdealPair]]("«scPower»")))),
					FinalLeg(
						"the two products are the pairs of D and E",
						By(closedD, closedE, pairOf.At(D), pairOf.At(E)))))
			integers := a.Have(
				"the integers are a commutative monoid under addition",
				"comm_monoid_on(𝕌, int_add, 0)",
				By(
					int_real_lift.AddMonoid,
					comm_monoid.CommMonoidOnUniverse.At(a.TermAs[Fun2[Int, Int, Int]]("int_add"), a.TermAs[Int]("0"))))
			degreeLaws := a.Have(
				"each point reads an integer additively by multiplying with its degree",
				Statement{
					Binders: "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{
						"P ∈ «supports»",
					},
					Conclusion: "(∀n:int. n * «scPointDegree»(P) ∈ 𝕌) ∧ " +
						"int_of_num(0) * «scPointDegree»(P) = 0 ∧ " +
						"(∀i j:int. (i + j) * «scPointDegree»(P) = i * «scPointDegree»(P) + j * «scPointDegree»(P))",
				},
				Derive(func(b *Argument) {
					b.FixAs[_IdealPair]("P")
					b.Assume()
					b.Show(
						"integers multiply and distribute",
						By(Normalized, set_basic.InUniv, int_real_lift.MulLeftZero, int_real_lift.RightDistrib))
				}))
			degree := a.Have(
				"the degree of D + E is the sum of the two degrees",
				"«scDegree»(λP:prod(set(A), set(A)). D(P) + E(P)) = «scDegree»(D) + «scDegree»(E)",
				Unfold(ClosedDivisorDegreeDef),
				By(
					finiteSupports,
					inD,
					inE,
					degreeLaws,
					module.SupportSumAdditive.Read(integers).At(
						supports,
						intAdd,
						intZero,
						D,
						E,
						a.TermAs[Fun2[_IdealPair, Int, Int]]("λP:prod(set(A), set(A)). λn:int. n * «scPointDegree»(P)"))))
			a.Show(
				"D + E is closed, with the product of the pairs and the sum of the degrees",
				By(divisor, pair, degree))
		}),
})}

// ClosedDivisorNegate — −D is a closed divisor on the support of D, and it
// undoes D: D + (−D) is the zero divisor, so the two pairs multiply to the
// structure pair, whence the pair of −D is the inverse of the invertible pair of
// D, and the two degrees add to 0.
var ClosedDivisorNegate = closedDivisorNegateThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorNegate",
	Key:  "prop_980e8f9dedbf763c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
		},
		Conclusion: "«scDivisor»(λP:prod(set(A), set(A)). -D(P)) ∧ " +
			"«scInvertible»(«scPair»(D)) ∧ " +
			"«scPair»(λP:prod(set(A), set(A)). -D(P)) = " +
			"lattice_pair_inverse(field_ring(L), A₀, A₁, «scPair»(D)) ∧ " +
			"«scDegree»(λP:prod(set(A), set(A)). -D(P)) = -«scDegree»(D)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_IdealPair, Int],
			curve, closedD Fact,
		) {
			products := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")
			unique, pairOf := products[1], products[3]
			divisorD := a.Conjuncts(
				a.Unfolded(closedD, ClosedDivisorDef),
				"the support of D is finite",
				"its pairs are closed points")
			nonzero := a.Have(
				"where −D is nonzero D is",
				"∀P:prod(set(A), set(A)). -D(P) ≠ 0 ⇒ D(P) ≠ 0",
				Derive(func(b *Argument) {
					b.FixAs[_IdealPair]("P")
					b.Show(
						"the negative of zero is zero",
						ByArith(b.Assume()))
				}))
			negative := a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). -D(P)")
			divisor := a.Have(
				"so −D, supported in the support of D, is a closed divisor",
				"«scDivisor»(λP:prod(set(A), set(A)). -D(P))",
				By(
					divisorD[0],
					divisorD[1],
					nonzero,
					At(
						ClosedDivisorOfSupport,
						a.TermAs[RingOps[A]]("field_ring(L)"),
						A0,
						A1,
						A01,
						a.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), D)"),
						negative)))
			sum := a.Conjuncts(
				GroupPremises(curve, closedD, divisor, ClosedDivisorAdd.Read(L).At(k, A0, A1, A01, t, D, negative)),
				"D and −D add to a closed divisor",
				"its pair is the product of their pairs",
				"its degree is the sum of their degrees")
			zero := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorZero.Read(L).At(k, A0, A1, A01, t)),
				"the zero divisor is a closed divisor",
				"its pair is the structure pair",
				"its degree is 0")
			cancels := a.Have(
				"D and −D add to the zero divisor",
				"(λP:prod(set(A), set(A)). D(P) + -D(P)) = (λP:prod(set(A), set(A)). int_of_num(0))",
				Funext(),
				ByArith())
			pairZero := a.Have(
				"so the pair of their sum is the structure pair",
				"«scPair»(λP:prod(set(A), set(A)). D(P) + -D(P)) = (A₀, A₁)",
				cancels.Rw(),
				By(zero[1]))
			degreeZero := a.Have(
				"and its degree is 0",
				"«scDegree»(λP:prod(set(A), set(A)). D(P) + -D(P)) = 0",
				cancels.Rw(),
				By(zero[2]))
			invertibleD := a.Have(
				"the pair of D is invertible",
				"«scInvertible»(«scPair»(D))",
				By(closedD, pairOf.At(D)))
			invertibleNegative := a.Have(
				"so is the pair of −D",
				"«scInvertible»(«scPair»(λP:prod(set(A), set(A)). -D(P)))",
				By(divisor, pairOf.At(negative)))
			inverse := a.Have(
				"the pair of −D is the inverse of the pair of D",
				"«scPair»(λP:prod(set(A), set(A)). -D(P)) = "+
					"lattice_pair_inverse(field_ring(L), A₀, A₁, «scPair»(D))",
				By(
					invertibleD,
					invertibleNegative,
					sum[1],
					pairZero,
					unique.At(
						a.TermAs[_IdealPair]("«scPair»(D)"),
						a.TermAs[_IdealPair]("«scPair»(λP:prod(set(A), set(A)). -D(P))"))))
			degree := a.Have(
				"the two degrees add to 0",
				"«scDegree»(λP:prod(set(A), set(A)). -D(P)) = -«scDegree»(D)",
				ByArith(sum[2], degreeZero))
			a.Show(
				"−D is closed, the pair of D is invertible with "+
					"inverse the pair of −D, and the degree changes sign",
				By(divisor, invertibleD, inverse, degree))
		}),
})}

// ClosedDivisorSub — the difference of two closed divisors is a closed divisor,
// its pair the pair of D over the pair of E, its degree the difference of their
// degrees: D − E is the sum of D and −E.
var ClosedDivisorSub = closedDivisorSubThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorSub",
	Key:  "prop_7d79ea33888403e3",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D E:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
			"«scDivisor»(E)",
		},
		Conclusion: "«scDivisor»(«difference») ∧ " +
			"«scPair»(«difference») = " +
			"lattice_pair_mul(field_ring(L), " +
			"    A₀, " +
			"    A₁, " +
			"    «scPair»(D), " +
			"    lattice_pair_inverse(field_ring(L), A₀, A₁, «scPair»(E))) ∧ " +
			"«scDegree»(«difference») = «scDegree»(D) - «scDegree»(E)",
		Abbrev: Abbrev{
			{Name: "difference", Text: "λP:prod(set(A), set(A)). D(P) - E(P)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D, E *Arrow[_IdealPair, Int],
			curve, divisorD, divisorE Fact,
		) {
			negated := a.Conjuncts(
				GroupPremises(curve, divisorE, ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, E)),
				"−E is a closed divisor",
				"the pair of E is invertible",
				"the pair of −E is its inverse",
				"its degree is the negative degree")
			added := a.Conjuncts(
				GroupPremises(
					negated[0],
					curve,
					divisorD,
					ClosedDivisorAdd.Read(L).At(
						k, A0, A1, A01, t, D, a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). -E(P)"))),
				"D + (−E) is a closed divisor",
				"its pair is the product of the pairs",
				"its degree is the sum of the degrees")
			spelled := a.Have(
				"D − E is the sum of D and −E",
				"«difference» = (λP:prod(set(A), set(A)). D(P) + -E(P))",
				Funext(),
				ByArith())
			divisor := a.Have(
				"so D − E is a closed divisor",
				"«scDivisor»(«difference»)",
				spelled.Rw(),
				By(added[0]))
			pair := a.Have(
				"whose pair is the pair of D times the inverse of the pair of E",
				"«scPair»(«difference») = "+
					"lattice_pair_mul(field_ring(L), "+
					"    A₀, "+
					"    A₁, "+
					"    «scPair»(D), "+
					"    lattice_pair_inverse(field_ring(L), A₀, A₁, «scPair»(E)))",
				spelled.Rw(),
				By(added[1], negated[2]))
			degree := a.Have(
				"and whose degree is the difference of the degrees",
				"«scDegree»(«difference») = «scDegree»(D) - «scDegree»(E)",
				spelled.Rw(),
				ByArith(added[2], negated[3]))
			a.Show(
				"the divisor, its pair and its degree",
				By(divisor, pair, degree))
		}),
})}

// ClosedDivisorPoint — the divisor n·P of a closed point P is closed, of degree
// n times the degree of P, and at −1 its pair is P itself: the support of a
// multiple of P is a part of {P}, so its sum is the term at P.
var ClosedDivisorPoint = closedDivisorPointThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorPoint",
	Key:  "prop_c30f5c9b779d7b08",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:int.",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(P)",
		},
		Conclusion: "«scDivisor»(λQ:prod(set(A), set(A)). COND(Q = P, n, 0)) ∧ " +
			"«scDegree»(λQ:prod(set(A), set(A)). COND(Q = P, n, 0)) = n * «scPointDegree»(P) ∧ " +
			"«scPair»(λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), 0)) = P",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			n *Expr[Int],
			curve, point Fact,
		) {
			products := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")
			monoid, powers, pairOf := products[0], products[2], products[3]
			only := a.Have(
				"a multiple of P is nonzero at P alone",
				"∀m:int. ∀Q:prod(set(A), set(A)). COND(Q = P, m, 0) ≠ 0 ⇒ Q ∈ {P}",
				BySets())
			parts := a.Have(
				"so its support is a part of {P}",
				"∀m:int. fun_support(int_of_num(0), λQ:prod(set(A), set(A)). COND(Q = P, m, 0)) ⊆ {P}",
				BySets())
			single := a.Have(
				"{P} is a set of closed points",
				"∀Q:prod(set(A), set(A)). Q ∈ {P} ⇒ «scPoint»(Q)",
				a.ForEach(func(Q *Expr[_IdealPair]) Action {
					return By(Normalized, point, set_basic.InSing.At(Q, P))
				}))
			atP := a.Have(
				"a multiple of P with P off its support is the zero multiple",
				"∀m:int. P ∉ fun_support(int_of_num(0), λQ:prod(set(A), set(A)). COND(Q = P, m, 0)) ⇒ m = 0",
				Derive(func(b *Argument) {
					b.FixAs[Int]("m")
					b.Show(
						"at P the coefficient is m",
						BySets(b.Assume()))
				}))
			divisors := a.Have(
				"a multiple of P is a closed divisor",
				"∀m:int. «scDivisor»(λQ:prod(set(A), set(A)). COND(Q = P, m, 0))",
				Derive(func(b *Argument) {
					m := b.FixAs[Int]("m")
					b.Show(
						"it is supported in {P}, a finite set of closed points",
						By(
							single,
							only.At(m),
							finite_set.FiniteSing.At(P),
							At(
								ClosedDivisorOfSupport,
								b.TermAs[RingOps[A]]("field_ring(L)"),
								A0,
								A1,
								A01,
								b.TermAs[Set[_IdealPair]]("{P}"),
								b.TermAs[Fun[_IdealPair, Int]]("λQ:prod(set(A), set(A)). COND(Q = P, m, 0)"))))
				}))
			integers := a.Have(
				"the integers are a commutative monoid under addition",
				"comm_monoid_on(𝕌, int_add, 0)",
				By(
					int_real_lift.AddMonoid,
					comm_monoid.CommMonoidOnUniverse.At(a.TermAs[Fun2[Int, Int, Int]]("int_add"), a.TermAs[Int]("0"))))
			offDegree := a.Have(
				"with P off the support the multiple is zero, and its term at P vanishes",
				Statement{
					Hypotheses: []string{"P ∉ fun_support(int_of_num(0), λQ:prod(set(A), set(A)). COND(Q = P, n, 0))"},
					Conclusion: "COND(P = P, n, 0) * «scPointDegree»(P) = 0",
				},
				Derive(func(b *Argument) {
					off := b.Assume()
					vanishes := b.Have(
						"n is zero",
						"n = 0",
						By(off, atP.At(n)))
					b.Show(
						"zero times the degree of P vanishes",
						vanishes.Rw(),
						By(int_real_lift.MulLeftZero))
				}))
			termIsInteger := a.Have(
				"the term at P is an integer",
				"COND(P = P, n, 0) * «scPointDegree»(P) ∈ 𝕌",
				By(set_basic.InUniv))
			degree := a.Have(
				"the degree of n·P is its one term, n times the degree of P",
				"«scDegree»(λQ:prod(set(A), set(A)). COND(Q = P, n, 0)) = n * «scPointDegree»(P)",
				Unfold(ClosedDivisorDegreeDef),
				By(
					parts.At(n),
					offDegree,
					termIsInteger,
					module.ModuleSumSingleMonoid.Read(integers).At(
						a.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), λQ:prod(set(A), set(A)). COND(Q = P, n, 0))"),
						P,
						a.TermAs[Fun[_IdealPair, Int]]("λQ:prod(set(A), set(A)). COND(Q = P, n, 0) * «scPointDegree»(Q)"))))
			minusOne := a.TermAs[Int]("-1")
			minusP := a.TermAs[Fun[_IdealPair, Int]]("λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), 0)")
			offPair := a.Have(
				"P lies on the support of −P, so its term at P is not asked to be the structure pair",
				Statement{
					Hypotheses: []string{
						"P ∉ fun_support(int_of_num(0), λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), 0))",
					},
					Conclusion: "«scPower»(P, COND(P = P, -int_of_num(1), 0)) = (A₀, A₁)",
				},
				Derive(func(b *Argument) {
					off := b.Assume()
					contradiction := b.Have(
						"−1 would be 0",
						"-1 = int_of_num(0)",
						By(off, atP.At(minusOne)))
					b.Show(
						"and it is not",
						By(contradiction))
				}))
			termIn := a.Have(
				"the term at P is invertible",
				"«scPower»(P, COND(P = P, -int_of_num(1), 0)) ∈ «scInvertibles»",
				By(point, powers.At(P)))
			pair := a.Have(
				"the pair of −P is P",
				"«scPair»(λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), 0)) = P",
				CalcEq(
					Leg(
						a.TermAs[_IdealPair](
							"module_sum(«scMul», "+
								"    (A₀, A₁), "+
								"    fun_support(int_of_num(0), λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), 0)), "+
								"    λQ:prod(set(A), set(A)). «scPower»(Q, COND(Q = P, -int_of_num(1), 0)))"),
						"the pair of a closed divisor is the product of its powers",
						By(divisors.At(minusOne), pairOf.At(minusP))),
					Leg(
						a.TermAs[_IdealPair]("«scPower»(P, COND(P = P, -int_of_num(1), 0))"),
						"its one term is the power at P",
						By(
							parts.At(minusOne),
							offPair,
							termIn,
							module.ModuleSumSingleMonoid.Read(monoid).At(
								a.TermAs[Set[_IdealPair]](
									"fun_support(int_of_num(0), λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), 0))"),
								P,
								a.TermAs[Fun[_IdealPair, _IdealPair]](
									"λQ:prod(set(A), set(A)). «scPower»(Q, COND(Q = P, -int_of_num(1), 0))")))),
					FinalLeg(
						"the power at −1 is P",
						By(point, powers.At(P)))))
			a.Show(
				"n·P is closed, of degree n times that of P, and the pair of −P is P",
				By(divisors.At(n), degree, pair))
		}),
})}
