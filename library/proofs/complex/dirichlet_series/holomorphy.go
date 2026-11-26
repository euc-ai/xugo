// holomorphy.go — a Dirichlet series as a holomorphic function: its finite
// partial sums, which are entire; on an open half-plane of absolute
// convergence, with its derivative taken term by term; and on Re s > 0
// when its coefficients have bounded partial sums, where summation by
// parts gives a series of holomorphic terms dominated by a polynomial in
// |s| times (n + 1)^(−Re s − 1), and such a series has a holomorphic sum
// on Re s > 0.

package dirichlet_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// DirichletSeriesLocalMajorant — a real point between the boundary and the
// centre of a disc supplies a summable majorant for every term on that disc.
var DirichletSeriesLocalMajorant = dirichletSeriesLocalMajorantThm{family.Add(registry.ProofEntry{
	Name: "DirichletSeriesLocalMajorant",
	Key:  "prop_389af6f937fa46ff",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀c:real. ∀u:complex.",
		Hypotheses: []string{
			"∀σ:real. c < σ ⇒ ∃t:real. real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ), t)",
			"c < re(u)",
		},
		Conclusion: "∃r:real. ∃M:(num → real). ∃t:real. " +
			"    &0 < r ∧ " +
			"    real_sums(M, t) ∧ " +
			"    ∀n:num. ∀z:complex. " +
			"        |z - u| < r ⇒ " +
			"        z ∈ {w:complex | c < re(w)} ∧ |a(n + 1) * complex_cpow(&(n + 1), -z)| ≤ M(n)",
	}, func(
		arg *Argument,
		a *Arrow[Nat, Complex],
		c *Expr[Real],
		u *Expr[Complex],
		absolute, inside Fact,
	) {
		σ, midDef := arg.LetAs[Real]("σ", "(re(u) + c) / &2")
		ρ, radiusDef := arg.LetAs[Real]("ρ", "re(u) - σ")
		m, majorantDef := arg.LetAs[Fun[Nat, Real]]("m", "λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ)")
		between := arg.Have(
			"the midpoint lies between the boundary and the centre",
			"c < σ ∧ σ < re(u)",
			ByArith(midDef, inside))
		positive := arg.Have(
			"the radius is positive",
			"&0 < ρ",
			ByArith(radiusDef, between))
		t, sums := arg.ObtainAs[Real](
			"absolute convergence at the midpoint gives a sum for the majorant",
			"∃t:real. real_sums(m, t)",
			Simp(Fwd(majorantDef)),
			By(absolute.At(σ), between))
		arg.Show(
			"use the disc from the centre to the midpoint and its summable majorant",
			Witness(ρ),
			Witness(m),
			Witness(t),
			SplitConj(
				Case(
					"the radius is positive and the majorant has a sum",
					By(positive, sums)),
				Case(
					"the disc lies in the half-plane and the majorant bounds the terms",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						z := b.FixAs[Complex]("z")
						near := b.Assume()
						toRight := b.Have(
							"the real part drops by at most the distance to the centre",
							"σ < re(z)",
							ByArith(radiusDef, near, complex_abs.PartsNonexpanding.At(z, u)))
						b.Show(
							"each point in the disc is to the right of the midpoint",
							SplitConj(
								Case(
									"it belongs to the open half-plane",
									ByArith(toRight, between)),
								Case(
									"its term is bounded by the majorant at the midpoint",
									Simp(Fwd(majorantDef)),
									Derive(func(d *Argument) {
										x, baseDef := d.LetAs[Real]("x", "&(n + 1)")
										atLeast := d.Have(
											"the base is at least one",
											"&1 ≤ x",
											ByArith(baseDef))
										powerBound := d.Have(
											"at a base of at least one the power x^(−z) is at most x^(−σ) in modulus, σ being below Re z",
											"|complex_cpow(&x, -z)| ≤ real_rpow(x, -σ)",
											ByArith(atLeast, toRight, complex_cpow.AbsCpowNegLessEq.At(x, σ, z)))
										coefficient := d.TermAs[Complex]("a(n + 1)")
										d.Show(
											"the modulus of the term is |a(n + 1)| times that of the power, which the power bound bounds",
											ByArith(
												powerBound,
												complex_abs.AbsMul.At(coefficient, d.TermAs[Complex]("complex_cpow(&x, -z)")),
												complex_abs.AbsNonneg.At(coefficient)))
									}))))
					}))))
	}),
})}

// DirichletTermDerivative — differentiating a Dirichlet term multiplies its
// coefficient by the negative logarithm of its positive index.
var DirichletTermDerivative = dirichletTermDerivativeThm{family.Add(registry.ProofEntry{
	Name: "DirichletTermDerivative",
	Key:  "prop_32df2b32a407145a",
	Build: family.Theorem(
		"∀a:(num → complex). ∀n:num. ∀z:complex. "+
			"    complex_derivative_at(λw:complex. a(n + 1) * complex_cpow(&(n + 1), -w), "+
			"        z, "+
			"        -&(log(&(n + 1))) * a(n + 1) * complex_cpow(&(n + 1), -z))",
		func(arg *Argument, a *Arrow[Nat, Complex], n *Expr[Nat], z *Expr[Complex]) {
			x, baseDef := arg.LetAs[Real]("x", "&(n + 1)")
			positive := arg.Have(
				"the index gives a positive real base",
				"&0 < x",
				ByArith(baseDef))
			one := arg.TermAs[Complex]("&1")
			id := arg.TermAs[Fun[Complex, Complex]]("λw:complex. w")
			negated := arg.Have(
				"negation has derivative negative one",
				"complex_derivative_at(λw:complex. -w, z, -&1)",
				By(complex_derivative.DerivativeId.At(z), complex_derivative.DerivativeNeg.At(id, z, one)))
			power := arg.TermAs[Fun[Complex, Complex]]("λw:complex. complex_cpow(&x, w)")
			powerSlope := arg.TermAs[Complex]("complex_cpow(&x, -z) * &(log(x))")
			slope := arg.Have(
				"the power has its exponential derivative at the negated argument",
				"complex_derivative_at(λw:complex. complex_cpow(&x, w), -z, complex_cpow(&x, -z) * &(log(x)))",
				By(positive, complex_cpow.CpowDerivativeExponent.At(x, arg.TermAs[Complex]("-z"))))
			composed := arg.Have(
				"the chain rule supplies the negative sign",
				"complex_derivative_at((λw:complex. complex_cpow(&x, w)) ∘ (λw:complex. -w), "+
					"    z, "+
					"    (complex_cpow(&x, -z) * &(log(x))) * (-&1))",
				By(
					negated,
					slope,
					complex_derivative.DerivativeChain.At(power, arg.TermAs[Fun[Complex, Complex]]("λw:complex. -w"),
						z, powerSlope, arg.TermAs[Complex]("-&1"))))
			negatedPowerSlope := arg.Simplified(composed, Fwd(functions.ComposeApply))
			arg.Show(
				"scale the derivative by the fixed coefficient and collect the factors",
				ByArith(
					negatedPowerSlope,
					complex_derivative.DerivativeScale.At(
						arg.TermAs[Fun[Complex, Complex]]("λw:complex. complex_cpow(&x, -w)"),
						z,
						arg.TermAs[Complex]("(complex_cpow(&x, -z) * &(log(x))) * (-&1)"),
						arg.TermAs[Complex]("a(n + 1)"))))
		}),
})}

// PartialSumHolomorphic — a finite Dirichlet sum Σ_{n=1}^N a(n)·n^(−s) is
// entire: each of its terms has the derivative DirichletTermDerivative
// gives, and a finite sum of holomorphic functions is holomorphic.
var PartialSumHolomorphic = partialSumHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "PartialSumHolomorphic",
	Key:  "prop_24715beb99f6ac0a",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → complex). ∀N:num.",
		Conclusion: "holomorphic_on(𝕌, λz:complex. Σ_{n∈1 .. N} a(n) * complex_cpow(&n, -z))",
	}, func(arg *Argument, a *Arrow[Nat, Complex], N *Expr[Nat]) {
		U := arg.TermAs[Set[Complex]]("𝕌")
		one := arg.TermAs[Nat]("1")
		seg := arg.TermAs[Set[Nat]]("1 .. N")
		terms := arg.TermAs[Fun2[Nat, Complex, Complex]]("λn:num. λz:complex. a(n) * complex_cpow(&n, -z)")
		pointwise := arg.Have(
			"every term in the segment has a complex derivative",
			"∀n:num. n ∈ 1 .. N ⇒ holomorphic_on(𝕌, λz:complex. a(n) * complex_cpow(&n, -z))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				inSeg := b.Assume()
				successor := b.Have(
					"the positive index is the successor of its predecessor",
					"n - 1 + 1 = n",
					ByArith(inSeg, num_segment.Membership.At(n, one, N)))
				b.Show(
					"apply the Dirichlet term derivative at the predecessor",
					Simp(Fwd(complex_derivative.HolomorphicOnDef)),
					Derive(func(c *Argument) {
						z := c.FixAs[Complex]("z")
						c.Assume()
						c.Take(c.TermAs[Complex]("-&(log(&n)) * a(n) * complex_cpow(&n, -z)"))
						c.Show(
							"substitute the successor index",
							By(successor, DirichletTermDerivative.At(a, c.TermAs[Nat]("n - 1"), z)))
					}))
			}))
		arg.Show(
			"sum the holomorphic terms over the finite interval",
			By(pointwise, num_segment.Finite.At(one, N), complex_derivative.HolomorphicOnSum.At(U, seg, terms)))
	}),
})}

// DirichletSeriesHolomorphic — a Dirichlet series that converges
// absolutely at every real σ > c is holomorphic on the half-plane
// Re s > c: at each point of it DirichletSeriesDerivative gives the
// derivative.
var DirichletSeriesHolomorphic = dirichletSeriesHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "DirichletSeriesHolomorphic",
	Key:  "prop_95e9339e3b79ca4e",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀c:real.",
		Hypotheses: []string{
			"∀σ:real. c < σ ⇒ ∃t:real. real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ), t)",
		},
		Conclusion: "holomorphic_on({s:complex | c < re(s)}, λs:complex. dirichlet_series(a, s))",
	}, func(arg *Argument, a *Arrow[Nat, Complex], c *Expr[Real], absolute Fact) {
		arg.Do(Unfold(complex_derivative.HolomorphicOnDef))
		z := arg.FixAs[Complex]("z")
		inside := arg.Assume()
		arg.Show(
			"at z the derivative is minus the series of log n · a(n)",
			Witness(arg.TermAs[Complex]("-dirichlet_series(λn:num. &(log(&n)) * a(n), z)")),
			By(absolute, inside, DirichletSeriesDerivative.At(a, c, z)))
	}),
})}

// DirichletSeriesDerivative — on such a half-plane the derivative of a
// Dirichlet series is minus the Dirichlet series of log n · a(n): term by
// term it is the series of −log n · a(n), and scaling that series by −1
// gives the series of log n · a(n) and the negated sum.
var DirichletSeriesDerivative = dirichletSeriesDerivativeThm{family.Add(registry.ProofEntry{
	Name: "DirichletSeriesDerivative",
	Key:  "prop_d873f8baa92bee2d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀c:real. ∀s:complex.",
		Hypotheses: []string{
			"∀σ:real. c < σ ⇒ ∃t:real. real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ), t)",
			"c < re(s)",
		},
		Conclusion: "complex_derivative_at(λz:complex. dirichlet_series(a, z), " +
			"    s, " +
			"    -dirichlet_series(λn:num. &(log(&n)) * a(n), s))",
	}, func(
		arg *Argument,
		a *Arrow[Nat, Complex],
		c *Expr[Real],
		s *Expr[Complex],
		absolute, toRight Fact,
	) {
		S, planeDef := arg.LetAs[Set[Complex]]("S", "{z:complex | c < re(z)}")
		g, termsDef := arg.LetAs[Fun2[Nat, Complex, Complex]](
			"g", "λn:num. λz:complex. a(n + 1) * complex_cpow(&(n + 1), -z)")
		b, coefficientsDef := arg.LetAs[Fun[Nat, Complex]]("b", "λn:num. -&(log(&n)) * a(n)")
		h, differentiatedDef := arg.LetAs[Fun2[Nat, Complex, Complex]](
			"h", "λn:num. λz:complex. b(n + 1) * complex_cpow(&(n + 1), -z)")
		local := arg.Have(
			"each point in the half-plane has a disc with a summable majorant",
			Statement{
				Binders:    "∀u:complex.",
				Hypotheses: []string{"u ∈ S"},
				Conclusion: "∃r:real. ∃M:(num → real). ∃t:real. " +
					"    &0 < r ∧ real_sums(M, t) ∧ (∀n:num. ∀z:complex. |z - u| < r ⇒ z ∈ S ∧ |g(n, z)| ≤ M(n))",
			},
			Derive(func(d *Argument) {
				u := d.FixAs[Complex]("u")
				inside := d.Assume()
				above := d.Have(
					"the centre lies to the right of the boundary",
					"c < re(u)",
					BySets(planeDef, inside))
				d.Show(
					"the local majorant bounds the Dirichlet terms on the disc",
					Simp(Fwd(planeDef), Fwd(termsDef)),
					By(absolute, above, At(DirichletSeriesLocalMajorant, a, c, u)))
			}))
		derivatives := arg.Have(
			"the differentiated terms use the logarithm-weighted coefficients",
			"∀n:num. ∀z:complex. z ∈ S ⇒ complex_derivative_at(g(n), z, h(n, z))",
			Derive(func(d *Argument) {
				n := d.FixAs[Nat]("n")
				z := d.FixAs[Complex]("z")
				d.Assume()
				d.Show(
					"differentiate a single Dirichlet term",
					Simp(Fwd(coefficientsDef), Fwd(termsDef), Fwd(differentiatedDef)),
					By(At(DirichletTermDerivative, a, n, z)))
			}))
		inside := arg.Have(
			"the point lies inside the half-plane",
			"s ∈ S",
			BySets(planeDef, toRight))
		sums := arg.Have(
			"the terms sum to the selected Dirichlet value throughout the half-plane",
			"∀z:complex. z ∈ S ⇒ complex_sums(λn:num. g(n, z), dirichlet_series(a, z))",
			Derive(func(d *Argument) {
				z := d.FixAs[Complex]("z")
				member := d.Assume()
				above := d.Have(
					"the real part is beyond the boundary",
					"c < re(z)",
					BySets(planeDef, member))
				σ := d.TermAs[Real]("re(z)")
				t, sizes := d.ObtainAs[Real](
					"absolute convergence at the real part gives a sum for the term majorant",
					"∃t:real. real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -re(z)), t)",
					By(absolute.At(σ), above))
				v, summed := d.ObtainAs[Complex](
					"the same majorant gives a Dirichlet sum at z",
					"∃v:complex. dirichlet_sums(a, z, v) ∧ |v| ≤ t",
					ByArith(sizes, AbsolutelyConvergentRight.At(a, σ, t, z)))
				parts := d.Conjuncts(
					summed,
					"the series sums to v",
					"the majorant bounds the modulus of v")
				value := d.Have(
					"the selected value is v",
					"dirichlet_series(a, z) = v",
					By(parts[0], DirichletSeriesValue.At(a, z, v)))
				d.Show(
					"the weighted terms sum to the selected value",
					Simp(Fwd(value), Fwd(termsDef)),
					By(parts[0], DirichletSumsDef.At(a, z, v)))
			}))
		F := arg.TermAs[Fun[Complex, Complex]]("λz:complex. dirichlet_series(a, z)")
		d, differentiated := arg.UnpackAs[Complex](
			GroupPremises(local, sums, derivatives, inside, cauchy_integral.SeriesDerivative.At(S, g, h, F, s)),
			"d")
		parts := arg.Conjuncts(
			differentiated,
			"the differentiated terms sum to d",
			"d is the derivative")
		weightedSum := arg.Simplified(parts[0], Fwd(differentiatedDef))
		doubleNegation := group.InvInv.Read(abelian_group.Group.Read(complex_field.AddGroup))
		scaled := arg.Have(
			"the series of b sums to d, so −1 times its coefficients sum to −1 times d",
			"dirichlet_sums(λn:num. -complex_of_real(&1) * b(n), s, -complex_of_real(&1) * d)",
			By(
				weightedSum,
				DirichletSumsDef.At(b, s, d),
				DirichletSumsScale.At(b, s, d, arg.TermAs[Complex]("-complex_of_real(&1)"))))
		negated := arg.Simplified(
			scaled,
			Fwd(comm_ring.NegOneMul.Read(complex_field.CommRing)),
			Fwd(coefficientsDef),
			Fwd(comm_ring.MulLeftNeg.Read(complex_field.CommRing)),
			Fwd(doubleNegation))
		value := arg.Have(
			"−1 times −log n · a(n) is log n · a(n), so −d is the selected value of the series of log n · a(n)",
			"dirichlet_series(λn:num. &(log(&n)) * a(n), s) = -d",
			By(
				negated,
				DirichletSeriesValue.At(
					arg.TermAs[Fun[Nat, Complex]]("λn:num. &(log(&n)) * a(n)"), s, arg.TermAs[Complex]("-d"))))
		arg.Show(
			"the derivative d is minus that value",
			Simp(Fwd(value), Fwd(doubleNegation)),
			By(parts[1]))
	}),
	Reading: "The derived series converges absolutely on the same open " +
		"half-plane, log n being below every power of n, so the statement iterates. " +
		"The coefficient at n = 0 is the logarithm at 0, which the series never reads.",
})}

// DominatedSeriesHolomorphic — a series of functions holomorphic on the
// half-plane Re s > 0, its n-th term at most C·(|s| + 1)²·(n + 1)^(−Re s − 1),
// has a holomorphic sum there: on the disc of radius Re c / 2 about a point c
// the bound is uniform, C·(|c| + Re c / 2 + 1)²·(n + 1)^(−Re c / 2 − 1), and
// that majorant series converges.
var DominatedSeriesHolomorphic = dominatedSeriesHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "DominatedSeriesHolomorphic",
	Key:  "prop_b0a329f0c4978496",
	Build: family.Sections(Statement{
		Binders: "∀g:(num → complex → complex). ∀C:real.",
		Hypotheses: []string{
			"∀n:num. holomorphic_on({s:complex | &0 < re(s)}, g(n))",
			"∀n:num. ∀s:complex. " +
				"    &0 < re(s) ⇒ |g(n, s)| ≤ C * (|s| + &1) * (|s| + &1) * real_rpow(&(n + 1), -re(s) - &1)",
		},
		Conclusion: "∃F:(complex → complex). " +
			"    (∀s:complex. &0 < re(s) ⇒ complex_sums(λn:num. g(n, s), F(s))) ∧ " +
			"    holomorphic_on({s:complex | &0 < re(s)}, F)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		disc := rightHalfPlaneDisc(ctx)
		return ctx.Theorem(headline, func(
			arg *Argument,
			g *Arrow2[Nat, Complex, Complex],
			C *Expr[Real],
			holomorphic, bounded Fact,
		) {
			S, halfPlane := arg.LetAs[Set[Complex]]("S", "{z:complex | &0 < re(z)}")
			one := arg.TermAs[Real]("&1")
			nonnegative := arg.Have(
				"C is nonnegative: at s = 1 and n = 0 it bounds a modulus by a positive multiple of C",
				"&0 ≤ C",
				ByArith(
					complex_field.PartsOfReal.At(one),
					bounded.At(arg.TermAs[Nat]("0"), arg.TermAs[Complex]("&1")),
					real_rpow.RpowPositive.At(arg.TermAs[Real]("&(0 + 1)"), arg.TermAs[Real]("-re(&1) - &1"))))
			majorized := arg.Have(
				"each point has a disc with a summable majorant",
				Statement{
					Binders:    "∀c:complex.",
					Hypotheses: []string{"c ∈ S"},
					Conclusion: "∃r:real. ∃M:(num → real). ∃t:real. " +
						"    &0 < r ∧ real_sums(M, t) ∧ (∀n:num. ∀z:complex. |z - c| < r ⇒ z ∈ S ∧ |g(n, z)| ≤ M(n))",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[Complex]("c")
					inS := b.Assume()
					r, radius := b.LetAs[Real]("r", "re(c) / &2")
					K, size := b.LetAs[Real]("K", "|c| + r + &1")
					P, powers := b.LetAs[Fun[Nat, Real]]("P", "λn:num. real_rpow(&(n + 1), -(r + &1))")
					L, majorant := b.LetAs[Fun[Nat, Real]]("L", "λn:num. C * K * K * P(n)")
					positive := b.Have(
						"the centre has positive real part",
						"&0 < re(c)",
						BySets(inS, halfPlane))
					rpos := b.Have(
						"the radius is positive and the power exponent exceeds one",
						"&0 < r ∧ &1 < r + &1",
						ByArith(positive, radius))
					A, powerSum := b.ObtainAs[Real](
						"the powers sum at the exponent r + 1",
						"∃A:real. real_sums(P, A)",
						By(rpos, powers, real_rpow.RpowSeriesConverges.At(b.TermAs[Real]("r + &1"))))
					summed := b.Have(
						"scaling the summable powers by C·K² gives the majorant's sum",
						"real_sums(L, C * K * K * A)",
						By(powerSum, majorant, real_series.SumsScale.At(P, A, b.TermAs[Real]("C * K * K"))))
					nearby := b.Have(
						"on the disc the terms are bounded by the majorant",
						"∀n:num. ∀z:complex. |z - c| < r ⇒ z ∈ S ∧ |g(n, z)| ≤ L(n)",
						Derive(func(d *Argument) {
							n := d.FixAs[Nat]("n")
							z := d.FixAs[Complex]("z")
							near := d.Assume()
							location := d.Have(
								"the disc controls the real part and modulus",
								"r < re(z) ∧ |z| ≤ |c| + r",
								By(Normalized, near, radius, At(disc, c, z)))
							right := d.Have(
								"its real part exceeds the positive radius",
								"&0 < re(z)",
								ByArith(location, rpos))
							inside := d.Have(
								"so the point is in the half-plane",
								"z ∈ S",
								BySets(right, halfPlane))
							square := d.Have(
								"C·(|z| + 1)² is at most C·K², since |z| + 1 ≤ K",
								"C * (|z| + &1) * (|z| + &1) ≤ C * K * K",
								ByArith(
									location,
									size,
									nonnegative,
									real_order_ring.LessEqMul2.At(
										d.TermAs[Real]("|z| + &1"), K, d.TermAs[Real]("|z| + &1"), K),
									real_order_ring.LessEqMulLeft.At(
										C, d.TermAs[Real]("(|z| + &1) * (|z| + &1)"), d.TermAs[Real]("K * K"))))
							exponent := d.TermAs[Real]("-re(z) - &1")
							power := d.Have(
								"the power at Re z is at most the power at r, the base n + 1 being at least one",
								"real_rpow(&(n + 1), -re(z) - &1) ≤ P(n)",
								Simp(Fwd(powers)),
								ByArith(
									location,
									real_rpow.RpowLessEqExponent.At(
										d.TermAs[Real]("&(n + 1)"), exponent, d.TermAs[Real]("-(r + &1)"))))
							bound := d.Have(
								"so the term is at most C·K²·P(n)",
								"|g(n, z)| ≤ L(n)",
								Simp(Fwd(majorant)),
								ByArith(
									right,
									nonnegative,
									square,
									power,
									bounded.At(n, z),
									real_rpow.RpowNonneg.At(d.TermAs[Real]("&(n + 1)"), exponent),
									real_order_ring.LessEqMul2.At(
										d.TermAs[Real]("C * (|z| + &1) * (|z| + &1)"),
										d.TermAs[Real]("C * K * K"),
										d.TermAs[Real]("real_rpow(&(n + 1), -re(z) - &1)"),
										d.TermAs[Real]("P(n)"))))
							d.Show(
								"the point stays in the half-plane, its term under the majorant",
								By(inside, bound))
						}))
					b.Take(r)
					b.Take(L)
					b.Take(b.TermAs[Real]("C * K * K * A"))
					b.Show(
						"the chosen disc and majorant satisfy the summability criterion",
						By(rpos, summed, nearby))
				}))
			F, sums := arg.UnpackAs[Fun[Complex, Complex]](
				GroupPremises(holomorphic, majorized, cauchy_integral.SeriesHolomorphic.At(S, g)), "F")
			arg.Take(F)
			arg.Show(
				"a point of positive real part is a point of S",
				BySets(sums, halfPlane))
		})
	}),
})}

// BoundedSumsHolomorphic — a Dirichlet series whose coefficients have
// bounded partial sums is holomorphic on the half-plane Re s > 0.
var BoundedSumsHolomorphic = boundedSumsHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "BoundedSumsHolomorphic",
	Key:  "prop_6cf6d25c47350002",
	Build: family.Sections(Statement{
		Binders:    "∀a:(num → complex). ∀B:real.",
		Hypotheses: []string{"∀M:num. |Σ_{k∈1 .. M} a(k)| ≤ B"},
		Conclusion: "holomorphic_on({s:complex | &0 < re(s)}, λs:complex. dirichlet_series(a, s))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		negPower := negativePowerHolomorphic(ctx)
		termBound := abelTermBound(ctx)
		transfer := abelSeriesTransfer(ctx)
		return ctx.Theorem(headline, func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			B *Expr[Real],
			bounded Fact,
		) {
			S, halfPlane := arg.LetAs[Set[Complex]]("S", "{z:complex | &0 < re(z)}")
			_, partials := arg.LetAs[Fun[Nat, Complex]]("A", "λm:num. Σ_{k∈1 .. m} a(k)")
			g, terms := arg.LetAs[Fun[Nat, Fun[Complex, Complex]]]("g",
				"λn:num. λz:complex. A(n + 1) * (complex_cpow(&(n + 1), -z) - complex_cpow(&(n + 2), -z))")
			openS := arg.Have(
				"the positive-real-part half-plane is open",
				"S ∈ complex_topology",
				By(halfPlane, complex_topology.RightHalfPlaneOpen.At(arg.TermAs[Real]("&0"))))
			entire := arg.Have(
				"each summation-by-parts term is holomorphic",
				"∀n:num. holomorphic_on(S, g(n))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					x := b.TermAs[Real]("&(n + 1)")
					y := b.TermAs[Real]("&(n + 2)")
					bases := b.Have(
						"the adjacent bases are positive",
						"&0 < &(n + 1) ∧ &0 < &(n + 2)",
						ByArith())
					left := b.Have(
						"the lower-base power is holomorphic",
						"holomorphic_on(S, λz:complex. complex_cpow(&(n + 1), -z))",
						By(bases, At(negPower, x, S)))
					right := b.Have(
						"the upper-base power is holomorphic",
						"holomorphic_on(S, λz:complex. complex_cpow(&(n + 2), -z))",
						By(bases, At(negPower, y, S)))
					fx := b.TermAs[Fun[Complex, Complex]]("λz:complex. complex_cpow(&(n + 1), -z)")
					fy := b.TermAs[Fun[Complex, Complex]]("λz:complex. complex_cpow(&(n + 2), -z)")
					difference := b.Have(
						"the difference of the powers is holomorphic",
						"holomorphic_on(S, λz:complex. complex_cpow(&(n + 1), -z) - complex_cpow(&(n + 2), -z))",
						By(left, right, complex_derivative.HolomorphicOnSub.At(S, fx, fy)))
					k := b.TermAs[Complex]("A(n + 1)")
					constant := b.TermAs[Fun[Complex, Complex]]("λz:complex. A(n + 1)")
					delta := b.TermAs[Fun[Complex, Complex]](
						"λz:complex. complex_cpow(&(n + 1), -z) - complex_cpow(&(n + 2), -z)")
					b.Show(
						"multiply by the constant partial sum",
						By(
							Normalized,
							terms,
							difference,
							complex_derivative.HolomorphicOnConst.At(S, k),
							complex_derivative.HolomorphicOnMul.At(S, constant, delta)))
				}))
			dominated := arg.Have(
				"each Abel term is at most B·(|z| + 1)²·(n + 1)^(−Re z − 1), its partial sum being at most B",
				Statement{
					Binders:    "∀n:num. ∀z:complex.",
					Hypotheses: []string{"&0 < re(z)"},
					Conclusion: "|g(n, z)| ≤ B * (|z| + &1) * (|z| + &1) * real_rpow(&(n + 1), -re(z) - &1)",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					z := b.FixAs[Complex]("z")
					positive := b.Assume()
					b.Show(
						"bound the Abel term at the partial sum A(n + 1)",
						Simp(Fwd(terms)),
						By(positive, bounded, At(termBound, n, b.TermAs[Complex]("A(n + 1)"), z, B)))
				}))
			h, holomorphic := arg.UnpackAs[Fun[Complex, Complex]](
				GroupPremises(arg.Simplified(
					entire,
					Fwd(halfPlane)), dominated, DominatedSeriesHolomorphic.At(g, B)), "h")
			agrees := arg.Have(
				"the Abel sum agrees pointwise with the Dirichlet series",
				"∀z:complex. z ∈ S ⇒ dirichlet_series(a, z) = h(z)",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					inS := b.Assume()
					positive := b.Have(
						"the real part is positive",
						"&0 < re(z)",
						BySets(inS, halfPlane))
					sum := b.Have(
						"the Abel terms sum to h(z)",
						"complex_sums(λn:num. g(n, z), h(z))",
						By(positive, holomorphic))
					value := b.TermAs[Complex]("h(z)")
					summed := b.Have(
						"summation by parts gives the Dirichlet sum",
						"dirichlet_sums(a, z, h(z))",
						By(Normalized, positive, sum, terms, partials, bounded, At(transfer, a, B, z, value)))
					b.Show(
						"read the value of the convergent series",
						By(summed, DirichletSeriesValue.At(a, z, value)))
				}))
			arg.Show(
				"the Dirichlet series has the same holomorphy on the half-plane",
				By(
					halfPlane,
					openS,
					holomorphic,
					agrees,
					complex_derivative.HolomorphicOnAgree.At(S,
						arg.TermAs[Fun[Complex, Complex]]("λs:complex. dirichlet_series(a, s)"), h)))
		})
	}),
})}

// A positive real base raised to a negative complex exponent is entire.
func negativePowerHolomorphic(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀x:real. ∀S:set(complex).",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "holomorphic_on(S, λz:complex. complex_cpow(&x, -z))",
	}, func(a *Argument, x *Expr[Real], S *Expr[Set[Complex]], positive Fact) {
		id := a.TermAs[Fun[Complex, Complex]]("λz:complex. z")
		power := a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_cpow(&x, z)")
		negation := a.TermAs[Fun[Complex, Complex]]("λz:complex. -z")
		a.Show(
			"the power, entire in its exponent, composed with negation",
			By(
				positive,
				complex_cpow.CpowHolomorphicExponent.At(x),
				complex_derivative.HolomorphicOnId.At(S),
				complex_derivative.HolomorphicOnNeg.At(S, id),
				set_basic.InUniv.Inst[Complex](),
				complex_derivative.HolomorphicOnCompose.At(S, a.TermAs[Set[Complex]]("𝕌"), power, negation),
				functions.ComposeApply))
	})
}

// A disc of half the real part gives simultaneous real-part and modulus bounds.
func rightHalfPlaneDisc(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀c z:complex.",
		Hypotheses: []string{"|z - c| < re(c) / &2"},
		Conclusion: "re(c) / &2 < re(z) ∧ |z| ≤ |c| + re(c) / &2",
	}, func(a *Argument, c, z *Expr[Complex], near Fact) {
		displacement := a.TermAs[Complex]("z - c")
		split := a.Have(
			"recover z from its displacement",
			"z = (z - c) + c",
			ByArith())
		a.Show(
			"compare real parts and use the triangle inequality for the modulus",
			ByArith(
				near,
				split,
				complex_abs.AbsTriangle.At(displacement, c),
				complex_abs.PartsNonexpanding.At(z, c)))
	})
}

// The Abel term is at most B·(|z| + 1)² times a power of n + 1.
func abelTermBound(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀n:num. ∀u z:complex. ∀B:real.",
		Hypotheses: []string{"|u| ≤ B", "&0 < re(z)"},
		Conclusion: "|u * (complex_cpow(&(n + 1), -z) - complex_cpow(&(n + 2), -z))| ≤ " +
			"B * (|z| + &1) * (|z| + &1) * real_rpow(&(n + 1), -re(z) - &1)",
	}, func(a *Argument, n *Expr[Nat], u, z *Expr[Complex], B *Expr[Real], bounds Fact) {
		x := a.TermAs[Real]("&(n + 1)")
		y := a.TermAs[Real]("&(n + 2)")
		difference := a.TermAs[Complex](
			"complex_cpow(&(n + 1), -z) - complex_cpow(&(n + 2), -z)")
		guards := a.Have(
			"the adjacent bases are positive and the exponent is in the half-plane",
			"&0 < &(n + 1) ∧ &(n + 1) ≤ &(n + 2) ∧ -&1 ≤ re(z)",
			ByArith(bounds))
		delta := a.Have(
			"the power difference is bounded by the size of z times a power",
			"|complex_cpow(&(n + 1), -z) - complex_cpow(&(n + 2), -z)| ≤ "+
				"|z| * real_rpow(&(n + 1), -re(z) - &1)",
			ByArith(guards, complex_cpow.CpowDifferenceBound.At(x, y, z)))
		majorant := a.Have(
			"and |z| is at most (|z| + 1)², the power being nonnegative",
			"|complex_cpow(&(n + 1), -z) - complex_cpow(&(n + 2), -z)| ≤ "+
				"(|z| + &1) * (|z| + &1) * real_rpow(&(n + 1), -re(z) - &1)",
			ByArith(delta, real_rpow.RpowNonneg.At(x, a.TermAs[Real]("-re(z) - &1"))))
		a.Show(
			"multiply by the bounded coefficient",
			ByArith(
				bounds,
				majorant,
				complex_abs.AbsMul.At(u, difference),
				complex_abs.AbsNonneg.At(difference)))
	})
}
