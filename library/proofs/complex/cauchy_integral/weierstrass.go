// weierstrass.go — the second-order remainder of a bounded holomorphic
// function on a disc, from its power series and Cauchy's estimates, and
// Weierstrass's theorem in the form the M-test gives it: the sum of a
// normally convergent series of holomorphic functions is holomorphic and
// is differentiated term by term.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/registry"
)

// TangentRemainderBound — a function holomorphic on a disc of radius r and
// bounded by M there differs from its tangent line at the centre by at
// most 2M|h|²/r², for |h| ≤ r/2. Its power series Σ a(n)(z − c)ⁿ about c
// has a(0) = g(c) and a(1) = d, so the remainder at c + h is the tail
// Σ a(n + 2)hⁿ⁺². With q = |h|/r ≤ 1/2, Cauchy's estimate at the full
// radius bounds its n-th term by M·q²·qⁿ, and the geometric series of
// ratio q sums those bounds to M·q²/(1 − q) ≤ 2M·q².
var TangentRemainderBound = tangentRemainderBoundThm{family.Add(registry.ProofEntry{
	Name: "TangentRemainderBound",
	Key:  "prop_3c589554309b553f",
	Build: family.Theorem(Statement{
		Binders: "∀g:(complex → complex). ∀c d h:complex. ∀r M:real.",
		Hypotheses: []string{
			"&0 < r",
			"holomorphic_on({z:complex | |z - c| < r}, g)",
			"∀z:complex. |z - c| < r ⇒ |g(z)| ≤ M",
			"complex_derivative_at(g, c, d)",
			"|h| ≤ r / &2",
		},
		Conclusion: "|g(c + h) - g(c) - d * h| ≤ &2 * M * (|h| * |h|) / (r * r)",
	},
		func(
			arg *Argument,
			g *Arrow[Complex, Complex],
			c, d, h *Expr[Complex],
			r, M *Expr[Real],
			positive, holomorphic, bounded, derivative, small Fact,
		) {
			a, expansion := arg.UnpackAs[Fun[Nat, Complex]](
				GroupPremises(holomorphic, PowerSeriesExpansion.At(g, c, r)),
				"a")
			centre := arg.Have(
				"the centre lies in the disc",
				"|c - c| < r",
				ByArith(positive))
			constant := arg.Have(
				"at the centre the series sums to a(0), so a(0) = g(c)",
				"a(0) = g(c)",
				By(
					expansion.At(c),
					centre,
					complex_power_series.PowerSeriesAtCentre.At(a, c),
					complex_series.SumsUnique.At(
						arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n) * (c - c) ^ n"),
						arg.TermAs[Complex]("a(0)"),
						g.Apply(c))))
			l, derived := arg.UnpackAs[Complex](
				GroupPremises(expansion, centre, complex_power_series.PowerSeriesDerivativeDisc.At(a, g, c, r, c)),
				"l")
			slope := arg.Have(
				"the derived series sums at the centre to 1·a(1), the derivative there, so a(1) = d",
				"a(1) = d",
				ByArith(
					derived,
					derivative,
					complex_derivative.DerivativeUnique.At(g, c, l, d),
					complex_power_series.PowerSeriesAtCentre.At(
						arg.TermAs[Fun[Nat, Complex]]("λn:num. &(n + 1) * a(n + 1)"), c),
					complex_series.SumsUnique.At(
						arg.TermAs[Fun[Nat, Complex]]("λn:num. &(n + 1) * a(n + 1) * (c - c) ^ n"),
						l,
						arg.TermAs[Complex]("&(0 + 1) * a(0 + 1)"))))
			nonnegative := arg.Have(
				"M bounds |g(c)|, so M ≥ 0",
				"&0 ≤ M",
				ByArith(bounded.At(c), centre))
			shifted := arg.TermAs[Complex]("c + h")
			shift := arg.Have(
				"c + h − c is h",
				"c + h - c = h",
				ByArith())
			nearby := arg.Simplified(expansion.At(shifted), Fwd(shift))
			atPoint := arg.Have(
				"c + h lies within r/2 of c, where the series of the a(n)hⁿ sums to g(c + h)",
				"complex_sums(λn:num. a(n) * h ^ n, g(c + h))",
				ByArith(nearby, small, positive))
			add := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			terms := arg.TermAs[Fun[Nat, Complex]]("λk:num. a(k) * h ^ k")
			zero, one := arg.TermAs[Nat]("0"), arg.TermAs[Nat]("1")
			remainder := arg.Have(
				"its first two terms are a(0) + a(1)·h = g(c) + d·h",
				"g(c + h) - Σ_{k∈0 .. 1} a(k) * h ^ k = g(c + h) - g(c) - d * h",
				ByArith(
					constant,
					slope,
					monoidal.PeelRight.Read(add).At(one, zero, terms),
					monoidal.IntervalPoint.Read(add).At(zero, terms)))
			tail := arg.Have(
				"so the series from index 2 sums to the remainder g(c + h) − g(c) − d·h",
				"complex_sums(λn:num. a(n + 2) * h ^ (n + 2), g(c + h) - g(c) - d * h)",
				// SumsOffset at m = 1 indexes the tail n + 1 + 1; respell n + 2 to match.
				Simp(Fwd(nat_arith.Two), Fwd(nat_arith.AddSuc)), // n + 2 ↦ suc(n + 1)
				Simp(Fwd(nat_arith.Add1)),                       // suc(n + 1) ↦ n + 1 + 1
				By(atPoint, remainder, complex_series.SumsOffset.At(terms, g.Apply(shifted), one)))
			q, ratio := arg.LetAs[Real]("q", "|h| / r")
			scale := arg.Have(
				"|h| is q·r",
				"|h| = q * r",
				ByArith(ratio, positive))
			bounds := arg.Have(
				"0 ≤ q ≤ 1/2, as |h| ≤ r/2",
				"&0 ≤ q ∧ q ≤ &1 / &2",
				ByArith(scale, small, positive))
			termBound := arg.Have(
				"the n-th term of the tail is at most M·q²·qⁿ in size",
				"∀n:num. |a(n + 2) * h ^ (n + 2)| ≤ M * real_pow(q, 2) * real_pow(q, n)",
				Derive(func(e *Argument) {
					n := e.FixAs[Nat]("n")
					index := e.TermAs[Nat]("n + 2")
					coefficient := e.Have(
						"Cauchy's estimate at the full radius, for the coefficient a(n + 2)",
						"|a(n + 2)| * real_pow(r, n + 2) ≤ M",
						By(expansion, positive, bounded, CauchyEstimateDisc.At(g, a, c, r, M, index)))
					e.Show(
						"write |h| as q·r and scale Cauchy's estimate by qⁿ⁺²",
						real_order_ring.OrderCalc(e.Ctx()).CalcLeibniz(
							e.TermAs[Real]("|a(n + 2) * h ^ (n + 2)|"),
							EqLeg(
								e.TermAs[Real]("|a(n + 2)| * real_pow(r, n + 2) * real_pow(q, n + 2)"),
								"|h| = q·r, so |h|ⁿ⁺² = qⁿ⁺²·rⁿ⁺²",
								ByArith(scale, Scaled(e.TermAs[Real]("|a(n + 2)|"), real_pow.MulPowDistrib.At(q, r, index)))),
							LeLeg(
								e.TermAs[Real]("M * real_pow(q, n + 2)"),
								"the estimate, scaled by qⁿ⁺² ≥ 0",
								ByArith(coefficient, bounds, real_pow.PowNonneg.At(q, index))),
							EqLeg(
								e.TermAs[Real]("M * real_pow(q, 2) * real_pow(q, n)"),
								"qⁿ⁺² is qⁿ·q²",
								ByArith(Scaled(M, real_pow.PowAdd.At(q, n, e.TermAs[Nat]("2")))))))
				}))
			weight := arg.TermAs[Real]("M * real_pow(q, 2)")
			dominating := arg.Have(
				"q < 1, so M·q² times the geometric series of ratio q sums to M·q²/(1 − q)",
				"real_sums(λn:num. M * real_pow(q, 2) * real_pow(q, n), M * real_pow(q, 2) * real_inv(&1 - q))",
				ByArith(
					bounds,
					real_series.Geometric.At(q),
					real_series.SumsScale.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(q, n)"),
						arg.TermAs[Real]("real_inv(&1 - q)"),
						weight)))
			arg.Show(
				"compare the tail with the geometric series, then use q ≤ 1/2",
				real_order_ring.OrderCalc(arg.Ctx()).CalcLeibniz(
					arg.TermAs[Real]("|g(c + h) - g(c) - d * h|"),
					LeLeg(
						arg.TermAs[Real]("M * real_pow(q, 2) * real_inv(&1 - q)"),
						"the tail is dominated term by term by that geometric series",
						By(
							termBound,
							tail,
							dominating,
							complex_series.ComparisonBound.At(
								arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + 2) * h ^ (n + 2)"),
								arg.TermAs[Fun[Nat, Real]]("λn:num. M * real_pow(q, 2) * real_pow(q, n)"),
								arg.TermAs[Complex]("g(c + h) - g(c) - d * h"),
								arg.TermAs[Real]("M * real_pow(q, 2) * real_inv(&1 - q)")))),
					LeLeg(
						arg.TermAs[Real]("M * real_pow(q, 2) * &2"),
						"1 − q ≥ 1/2, so 1/(1 − q) ≤ 2, scaled by M·q² ≥ 0",
						ByArith(
							nonnegative,
							bounds,
							real_order_field.InvAntitoneWeak.At(arg.TermAs[Real]("&1 / &2"), arg.TermAs[Real]("&1 - q")))),
					EqLeg(
						arg.TermAs[Real]("&2 * M * (|h| * |h|) / (r * r)"),
						"q² is |h|²/r²",
						ByArith(ratio, positive))))
		}),
	Reading: "The bound uses nothing of g but its size on the disc, which is " +
		"what lets it be summed over a series of functions with summable sizes.",
})}

// SeriesHolomorphic — a series of functions holomorphic on a set S,
// dominated on a disc about each point of S by a convergent series of
// numbers, has a sum that is holomorphic on S. Each of those discs lies in
// S, so S is open without being assumed so.
var SeriesHolomorphic = seriesHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "SeriesHolomorphic",
	Key:  "prop_49c9088c6a581fae",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(complex). ∀g:(num → complex → complex).",
		Hypotheses: []string{
			"∀n:num. holomorphic_on(S, g(n))",
			"∀c:complex. " +
				"    c ∈ S ⇒ " +
				"    ∃r:real. ∃M:(num → real). ∃t:real. " +
				"        &0 < r ∧ real_sums(M, t) ∧ ∀n:num. ∀z:complex. |z - c| < r ⇒ z ∈ S ∧ |g(n, z)| ≤ M(n)",
		},
		Conclusion: "∃f:(complex → complex). " +
			"    (∀z:complex. z ∈ S ⇒ complex_sums(λn:num. g(n, z), f(z))) ∧ holomorphic_on(S, f)",
	},
		func(a *Argument, S *Expr[Set[Complex]], g *Arrow2[Nat, Complex, Complex], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"each term is holomorphic",
				"each point has a local majorant")
			termsHolomorphic, majorants := parts[0], parts[1]
			pointwise := a.Have(
				"at each point the local majorant gives a sum, by comparison",
				"∀w:complex. w ∈ S ⇒ ∃v:complex. complex_sums(λn:num. g(n, w), v)",
				Derive(func(b *Argument) {
					w := b.FixAs[Complex]()
					member := b.Assume()
					_, M, t, disc := b.Obtain3As[Real, Fun[Nat, Real], Real](
						"choose the majorant on the disc about w",
						"∃r:real. ∃M:(num → real). ∃t:real. "+
							"    &0 < r ∧ real_sums(M, t) ∧ (∀n:num. ∀z:complex. |z - w| < r ⇒ z ∈ S ∧ |g(n, z)| ≤ M(n))",
						By(member, majorants.At(w)),
						Named("r", "M", "t"))
					discParts := b.Conjuncts(
						disc,
						"the radius is positive",
						"the majorant has sum t",
						"the majorant bounds the terms")
					centre := b.Have(
						"the centre lies in its disc",
						"|w - w| < r",
						ByArith(discParts[0]))
					bounded := b.Have(
						"the majorant bounds the moduli at the centre",
						"∀n:num. |g(n, w)| ≤ M(n)",
						b.ForEach(func(n *Expr[Nat]) Action { return By(centre, discParts[2].At(n, w)) }))
					b.Show(
						"so the complex series has a sum at w, by comparison with the summable majorant",
						By(
							Normalized,
							bounded,
							discParts[1],
							complex_series.Comparison.At(b.TermAs[Fun[Nat, Complex]]("λn:num. g(n, w)"), M, t)))
				}))
			F, sums := a.ObtainAs[Fun[Complex, Complex]](
				"choose a pointwise sum function",
				"∃F:(complex → complex). ∀w:complex. w ∈ S ⇒ complex_sums(λn:num. g(n, w), F(w))",
				By(pointwise),
				Named("F"))
			pointDerivatives := a.Have(
				"each holomorphic term has a derivative at each point of S",
				"∀n:num. ∀w:complex. w ∈ S ⇒ ∃d:complex. complex_derivative_at(g(n), w, d)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					b.FixAs[Complex]()
					member := b.Assume()
					b.Show(
						"read holomorphy as existence of a derivative",
						By(
							member,
							termsHolomorphic.At(n),
							complex_derivative.HolomorphicOnDef.At(S, b.TermAs[Fun[Complex, Complex]]("g(n)"))))
				}))
			D, derivatives := a.ObtainAs[Fun2[Nat, Complex, Complex]](
				"choose the derivatives as a family",
				"∃D:(num → complex → complex). ∀n:num. ∀w:complex. w ∈ S ⇒ complex_derivative_at(g(n), w, D(n, w))",
				By(pointDerivatives))
			holomorphic := a.Have(
				"the termwise derivative theorem makes the sum holomorphic",
				"holomorphic_on(S, F)",
				Simp(Fwd(complex_derivative.HolomorphicOnDef)),
				Derive(func(b *Argument) {
					w := b.FixAs[Complex]()
					member := b.Assume()
					b.Show(
						"F has a derivative at w",
						By(derivatives, majorants, sums, member, SeriesDerivative.At(S, g, D, F, w)))
				}))
			a.Take(F)
			a.Show(
				"the function F is the pointwise sum and is holomorphic",
				By(sums, holomorphic))
		}),
	Reading: "The majorant is local: one disc and one summable sequence for each " +
		"point, which is what uniform convergence on compact sets comes to. The discs lie " +
		"in S, so S is open by that clause and is not assumed to be. This is Weierstrass's " +
		"theorem in the form his M-test gives; no notion of uniform convergence is named.",
})}

// SeriesDerivative — the sum of such a series has, at each point, the sum
// of the terms' derivatives as its derivative.
var SeriesDerivative = seriesDerivativeThm{family.Add(registry.ProofEntry{
	Name: "SeriesDerivative",
	Key:  "prop_b586cb42abb8d9c8",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(complex). ∀g g':(num → complex → complex). ∀f:(complex → complex). ∀z:complex.",
		Hypotheses: []string{
			"∀n:num. ∀w:complex. w ∈ S ⇒ complex_derivative_at(g(n), w, g'(n, w))",
			"∀c:complex. " +
				"    c ∈ S ⇒ " +
				"    ∃r:real. ∃M:(num → real). ∃t:real. " +
				"        &0 < r ∧ real_sums(M, t) ∧ ∀n:num. ∀w:complex. |w - c| < r ⇒ w ∈ S ∧ |g(n, w)| ≤ M(n)",
			"∀w:complex. w ∈ S ⇒ complex_sums(λn:num. g(n, w), f(w))",
			"z ∈ S",
		},
		Conclusion: "∃d:complex. complex_sums(λn:num. g'(n, z), d) ∧ complex_derivative_at(f, z, d)",
		Abbrev: Abbrev{
			{Name: "halfStep", Text: "λr:real. &(r / &2)"},
			{Name: "increment", Text: "λn:num. λh:complex. g(n, z + h) - g(n, z)"},
			{Name: "linear", Text: "λn:num. λh:complex. g'(n, z) * h"},
			{Name: "remainder", Text: "λn:num. λh:complex. «increment»(n, h) - «linear»(n, h)"},
			{Name: "weight", Text: "λr:real. λh:complex. &2 * (|h| * |h|) / (r * r)"},
		},
	},
		func(
			a *Argument,
			S *Expr[Set[Complex]],
			g, dg *Arrow2[Nat, Complex, Complex],
			f *Arrow[Complex, Complex],
			z *Expr[Complex],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"each term has its given derivative on the domain",
				"each point has a disc with a summable majorant",
				"the series sums pointwise to f",
				"the centre belongs to the domain")
			derivatives, localMajorant, pointwise, centre := parts[0], parts[1], parts[2], parts[3]
			zero := a.TermAs[Nat]("0")
			r, M, t, discData := a.Obtain3As[Real, Fun[Nat, Real], Real](
				"choose a majorized disc about z",
				"∃r:real. ∃M:(num → real). ∃t:real. "+
					"    &0 < r ∧ real_sums(M, t) ∧ (∀n:num. ∀w:complex. |w - z| < r ⇒ w ∈ S ∧ |g(n, w)| ≤ M(n))",
				By(centre, localMajorant.At(z)),
				Named("r", "M", "t"))
			discParts := a.Conjuncts(
				discData,
				"the radius is positive",
				"the majorant sums to t",
				"the disc bounds every term")
			positive, majorantSum, discBound := discParts[0], discParts[1], discParts[2]
			inside := a.Have(
				"the whole disc lies in the domain",
				"∀w:complex. |w - z| < r ⇒ w ∈ S",
				Derive(func(b *Argument) {
					w := b.FixAs[Complex]()
					near := b.Assume()
					b.Show(
						"the majorant supplies domain membership",
						By(near, discBound.At(zero, w)))
				}))
			bounds := a.Have(
				"each term is bounded by its majorant on the disc",
				"∀n:num. ∀w:complex. |w - z| < r ⇒ |g(n, w)| ≤ M(n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					w := b.FixAs[Complex]()
					near := b.Assume()
					b.Show(
						"read the pointwise majorant at this point",
						By(near, discBound.At(n, w)))
				}))
			holomorphic := a.Have(
				"each term is holomorphic on the disc",
				"∀n:num. holomorphic_on(«disc»(z, r), g(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					b.Show(
						"supply the given derivative at each point of the disc",
						Simp(Fwd(complex_derivative.HolomorphicOnDef)),
						Derive(func(c *Argument) {
							w := c.FixAs[Complex]("w")
							inDisc := c.Assume()
							near := c.Have(
								"disc membership bounds the distance",
								"|w - z| < r",
								BySets(inDisc))
							c.Take(dg.Apply(n, w))
							c.Show(
								"the disc point lies in S",
								By(near, inside.At(w), derivatives.At(n, w)))
						}))
				}))
			remainders := a.Have(
				"each term has the quadratic tangent bound at half the disc radius",
				"∀n:num. ∀h:complex. |h| ≤ r / &2 ⇒ |«remainder»(n, h)| ≤ &2 * M(n) * (|h| * |h|) / (r * r)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					h := b.FixAs[Complex]()
					small := b.Assume()
					b.Show(
						"apply the tangent estimate on the majorized disc",
						By(
							positive,
							holomorphic.At(n),
							bounds.At(n),
							centre,
							derivatives.At(n, z),
							small,
							TangentRemainderBound.At(
								b.TermAs[Fun[Complex, Complex]]("g(n)"), z, dg.Apply(n, z), h, r, b.TermAs[Real]("M(n)"))))
				}))
			half := a.TermAs[Complex]("«halfStep»(r)")
			halfNorm := a.Have(
				"the positive real step has modulus r/2",
				"|«halfStep»(r)| = r / &2",
				ByArith(positive, complex_abs.AbsOfNonnegReal.At(a.TermAs[Real]("r / &2"))))
			halfNear := a.Have(
				"the centre and its half-radius translate lie in the disc",
				"|z + «halfStep»(r) - z| < r ∧ |z - z| < r",
				Derive(func(b *Argument) {
					shift := b.Have(
						"subtract the centre from its translate",
						"z + «halfStep»(r) - z = «halfStep»(r)",
						ByArith())
					b.Show(
						"the half-radius is strictly below the radius",
						Simp(Fwd(shift), Fwd(halfNorm)),
						ByArith(positive))
				}))
			slopes := a.Have(
				"the half-radius step bounds the derivative by 5M(n)/r",
				"∀n:num. |g'(n, z)| ≤ (&5 / r) * M(n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					atHalf := b.TermAs[Complex]("z + «halfStep»(r)")
					atCentre := g.Apply(n, z)
					increment := b.Have(
						"the increment of the term is bounded by two majorant values",
						"|«increment»(n, «halfStep»(r))| ≤ &2 * M(n)",
						Simp(Fwd(complex_field.ComplexSubDef)),
						ByArith(
							halfNear,
							bounds.At(n, atHalf),
							bounds.At(n, z),
							complex_abs.AbsTriangle.At(g.Apply(n, atHalf), b.TermAs[Complex]("-g(n, z)")),
							complex_abs.AbsNeg.At(atCentre)))
					remainderBound := b.Have(
						"at this step the quadratic remainder is at most half the majorant",
						"|«remainder»(n, «halfStep»(r))| ≤ M(n) / &2",
						ByArith(positive, halfNorm, remainders.At(n, half)))
					product := b.Have(
						"the tangent term, the increment less the remainder, is at most (5/2)·M(n)",
						"|«linear»(n, «halfStep»(r))| ≤ (&5 / &2) * M(n)",
						Derive(func(c *Argument) {
							decompose := c.Have(
								"write the difference as a sum for the triangle inequality",
								"«linear»(n, «halfStep»(r)) = «increment»(n, «halfStep»(r)) + -«remainder»(n, «halfStep»(r))",
								ByArith())
							c.Show(
								"add the bounds for the increment and remainder",
								ByArith(
									decompose,
									increment,
									remainderBound,
									complex_abs.AbsNeg.At(c.TermAs[Complex]("«remainder»(n, «halfStep»(r))")),
									complex_abs.AbsTriangle.At(
										c.TermAs[Complex]("«increment»(n, «halfStep»(r))"),
										c.TermAs[Complex]("-«remainder»(n, «halfStep»(r))"))))
						}))
					scaled := b.Have(
						"the tangent term has modulus |g'(n, z)|·r/2, so |g'(n, z)|·r is at most 5·M(n)",
						"|g'(n, z)| * r ≤ &5 * M(n)",
						ByArith(halfNorm, product, complex_abs.AbsMul.At(dg.Apply(n, z), half)))
					quotient := b.Have(
						"the scaled majorant (5/r)·M(n) is 5·M(n)/r",
						"(&5 / r) * M(n) = (&5 * M(n)) / r",
						ByArith(positive))
					b.Show(
						"divide by the positive radius",
						Simp(Fwd(quotient)),
						By(
							positive,
							scaled,
							real_order_field.LessEqDivMulLeft.At(b.TermAs[Real]("|g'(n, z)|"), b.TermAs[Real]("&5 * M(n)"), r)))
				}))
			slopeScale := a.TermAs[Real]("&5 / r")
			derivativeTerms := a.TermAs[Fun[Nat, Complex]]("λn:num. g'(n, z)")
			d, derivativeSum := a.ObtainAs[Complex](
				"the derivatives are dominated by the scaled majorant, "+
					"which sums to (5/r)·t, so by comparison they have a sum d",
				"∃d:complex. complex_sums(λn:num. g'(n, z), d)",
				By(
					slopes,
					majorantSum,
					real_series.SumsScale.At(M, t, slopeScale),
					complex_series.Comparison.At(
						derivativeTerms,
						a.TermAs[Fun[Nat, Real]]("λn:num. (&5 / r) * M(n)"),
						a.TermAs[Real]("(&5 / r) * t"))),
				Named("d"))
			quadratic := a.Have(
				"summing the termwise remainders gives a quadratic remainder for f",
				"∀h:complex. |h| < r / &2 ⇒ |f(z + h) - f(z) - d * h| ≤ (&2 * t / (r * r)) * (|h| ^ 2)",
				Derive(func(b *Argument) {
					h := b.FixAs[Complex]()
					small := b.Assume()
					near := b.Have(
						"the translate by h stays in the disc",
						"|z + h - z| < r",
						Derive(func(c *Argument) {
							shift := c.Have(
								"subtract the centre from its translate",
								"z + h - z = h",
								ByArith())
							c.Show(
								"h is smaller than the radius",
								Simp(Fwd(shift)),
								ByArith(positive, small))
						}))
					scaled := b.Have(
						"multiplying each derivative by h multiplies the sum by h",
						"complex_sums(λn:num. «linear»(n, h), d * h)",
						By(
							derivativeSum,
							complex_series.SumsScale.At(derivativeTerms, d, h),
							comm_monoid.Comm.Read(complex_field.MulMonoid)))
					shifted := b.TermAs[Complex]("z + h")
					linearSum := b.TermAs[Complex]("d * h")
					termRemainders := b.TermAs[Fun[Nat, Complex]]("λn:num. «remainder»(n, h)")
					sumRemainder := b.TermAs[Complex]("f(z + h) - f(z) - d * h")
					remSum := b.Have(
						"subtract the series at z and the scaled derivative series from the series at z + h",
						"complex_sums(λn:num. «remainder»(n, h), f(z + h) - f(z) - d * h)",
						By(
							near,
							inside.At(shifted),
							pointwise.At(shifted),
							centre,
							pointwise.At(z),
							scaled,
							complex_series.SumsSub.At(
								b.TermAs[Fun[Nat, Complex]]("λn:num. g(n, z + h)"),
								b.TermAs[Fun[Nat, Complex]]("λn:num. g(n, z)"), f.Apply(shifted), f.Apply(z)),
							complex_series.SumsSub.At(
								b.TermAs[Fun[Nat, Complex]]("λn:num. «increment»(n, h)"),
								b.TermAs[Fun[Nat, Complex]]("λn:num. «linear»(n, h)"),
								b.TermAs[Complex]("f(z + h) - f(z)"), linearSum)))
					dominated := b.Have(
						"the termwise quadratic estimates share a single scale factor",
						"∀n:num. |«remainder»(n, h)| ≤ «weight»(r, h) * M(n)",
						b.ForEach(func(n *Expr[Nat]) Action { return ByArith(small, positive, remainders.At(n, h)) }))
					weight := b.TermAs[Real]("«weight»(r, h)")
					bound := b.Have(
						"the sum of the bounds is the common factor times t",
						"|f(z + h) - f(z) - d * h| ≤ «weight»(r, h) * t",
						By(
							dominated,
							remSum,
							majorantSum,
							real_series.SumsScale.At(M, t, weight),
							complex_series.ComparisonBound.At(
								termRemainders, b.TermAs[Fun[Nat, Real]]("λn:num. «weight»(r, h) * M(n)"),
								sumRemainder, b.TermAs[Real]("«weight»(r, h) * t"))))
					b.Show(
						"collect the quadratic factor",
						ByArith(positive, bound, real_pow.PowTwo.At(b.TermAs[Real]("|h|"))))
				}))
			a.Take(d)
			a.Show(
				"the quadratic remainder makes d the derivative of f at z",
				ByArith(
					quadratic,
					positive,
					derivativeSum,
					complex_derivative.DerivativeFromQuadraticRemainder.At(
						f, z, d, a.TermAs[Real]("&2 * t / (r * r)"), a.TermAs[Real]("r / &2"))))
		}),
})}
