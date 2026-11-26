// uniform.go — uniform convergence inside the radius: on every closed
// interval about 0 that lies inside the interval of convergence, the
// partial sums of a power series approach its sum at one rate at every
// point, and so the sum, a uniform limit of polynomials there, is
// continuous at every point of the interval of convergence.

package real_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_uniform_convergence"
	"github.com/euc-ai/xugo/library/registry"
)

// PowerSeriesUniform — a power series converges uniformly on every closed
// interval ⟦−r, r⟧ inside its interval of convergence: past one index the
// partial sums are within ε of the sum f at every point of ⟦−r, r⟧ at
// once. The series converges absolutely at r, and on ⟦−r, r⟧ each term
// a(n)·xⁿ is at most |a(n)·rⁿ| in size, so the Weierstrass M-test gives a
// uniform limit g of the partial sums there. Each value g(x) is a sum of
// the series at x, and so is f(x), so g is f on ⟦−r, r⟧, and f is as good
// a uniform limit there as g.
var PowerSeriesUniform = powerSeriesUniformThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesUniform",
	Key:  "prop_a7cb61b0c435ee7",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀f:(real → real). ∀R r:real.",
		Hypotheses: []string{
			"∀x:real. |x| < R ⇒ real_sums(λn:num. a(n) * real_pow(x, n), f(x))",
			"&0 ≤ r",
			"r < R",
		},
		Conclusion: "real_converges_uniformly_on(«I», «S», f)",
		Abbrev: Abbrev{
			{Name: "S", Text: "λn:num. λx:real. Σ_{k∈0 .. n} a(k) * real_pow(x, k)"},
			{Name: "I", Text: "{x:real | |x| ≤ r}"},
		},
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Real],
			f *Arrow[Real, Real],
			R, r *Expr[Real],
			sums, nonneg, below Fact,
		) {
			converges := arg.Have(
				"the series converges at every point of ⟬−R, R⟭",
				"∀y:real. |y| < R ⇒ ∃s:real. real_sums(λn:num. a(n) * real_pow(y, n), s)",
				By(Normalized, sums))
			t, sizes := arg.ObtainAs[Real](
				"r lies in ⟬−R, R⟭, so the series converges absolutely at r",
				"∃t:real. real_sums(λn:num. |a(n) * real_pow(r, n)|, t)",
				ByArith(converges, nonneg, below, PowerSeriesAbsoluteInside.At(a, R, r)))
			dominated := arg.Have(
				"on ⟦−r, r⟧ each term is at most its size at r",
				"∀n:num. ∀x:real. |x| ≤ r ⇒ |a(n) * real_pow(x, n)| ≤ |a(n) * real_pow(r, n)|",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					d.FixAs[Real]()
					within := d.Assume()
					powers := d.Have(
						"|x|ⁿ ≤ |r|ⁿ, as |x| ≤ r = |r|",
						"real_pow(|x|, n) ≤ real_pow(|r|, n)",
						ByArith(within, nonneg, real_pow.PowMonoBase.At(d.TermAs[Real]("|x|"), d.TermAs[Real]("|r|"), n)))
					d.Show(
						"times |a(n)| ≥ 0: |a(n)·xⁿ| = |a(n)|·|x|ⁿ ≤ |a(n)|·|r|ⁿ = |a(n)·rⁿ|",
						ByArith(powers, real_sgn_abs.AbsNonneg.At(a.Apply(n))))
				}))
			g, limit := arg.ObtainAs[Fun[Real, Real]](
				"the M-test with the majorant |a(n)·rⁿ|: the partial sums converge uniformly on ⟦−r, r⟧ to some g",
				"∃g:(real → real). "+
					"    (∀x:real. |x| ≤ r ⇒ real_sums(λn:num. a(n) * real_pow(x, n), g(x))) ∧ "+
					"    real_converges_uniformly_on(«I», «S», g)",
				By(
					dominated,
					sizes,
					real_uniform_convergence.WeierstrassMajorant.At(
						arg.TermAs[Fun2[Nat, Real, Real]]("λn:num. λx:real. a(n) * real_pow(x, n)"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n) * real_pow(r, n)|"),
						arg.TermAs[Set[Real]]("«I»"),
						t)))
			parts := arg.Conjuncts(
				limit,
				"at each point of ⟦−r, r⟧ the series sums to g(x)",
				"and the partial sums converge to g uniformly there")
			agree := arg.Have(
				"so g is f on ⟦−r, r⟧: a series has only one sum",
				"∀x:real. |x| ≤ r ⇒ g(x) = f(x)",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					within := d.Assume()
					d.Show(
						"at x the series sums to g(x), and, as |x| ≤ r < R, to f(x)",
						ByArith(
							parts[0].At(x),
							sums.At(x),
							within,
							below,
							real_series.SumsUnique.At(
								d.TermAs[Fun[Nat, Real]]("λn:num. a(n) * real_pow(x, n)"),
								d.TermAs[Real]("g(x)"),
								f.Apply(x))))
				}))
			arg.Show(
				"so the partial sums converge uniformly to f on ⟦−r, r⟧ as well",
				By(
					parts[1],
					agree,
					real_uniform_convergence.UniformLimitCongruence.At(
						arg.TermAs[Fun2[Nat, Real, Real]]("«S»"),
						g,
						f,
						arg.TermAs[Set[Real]]("«I»"))))
		}),
})}

// PowerSeriesContinuous — the sum of a power series is continuous at
// every point inside its interval of convergence. For |c| < R take r
// halfway between |c| and R. On ⟦−r, r⟧ the partial sums, polynomials and
// so continuous, converge uniformly to the sum f, so f is continuous on
// ⟦−r, r⟧; and ⟦−r, r⟧ holds the ball of radius r − |c| about c, so f is
// continuous at c.
var PowerSeriesContinuous = powerSeriesContinuousThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesContinuous",
	Key:  "prop_8751f0ace9bc88a1",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀f:(real → real). ∀R c:real.",
		Hypotheses: []string{
			"∀x:real. |x| < R ⇒ real_sums(λn:num. a(n) * real_pow(x, n), f(x))",
			"|c| < R",
		},
		Conclusion: "real_continuous_at(f, c)",
		Abbrev: Abbrev{
			{Name: "S", Text: "λn:num. λx:real. Σ_{k∈0 .. n} a(k) * real_pow(x, k)"},
			{Name: "I", Text: "{x:real | |x| ≤ r}"},
		},
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Real],
			f *Arrow[Real, Real],
			R, c *Expr[Real],
			sums, inside Fact,
		) {
			r, rDef := arg.LetAs[Real]("r", "(|c| + R) / &2")
			between := arg.Have(
				"r lies strictly between |c| and R",
				"&0 ≤ r ∧ |c| < r ∧ r < R",
				ByArith(rDef, inside))
			interval := arg.TermAs[Set[Real]]("«I»")
			uniform := arg.Have(
				"the partial sums converge to f uniformly on ⟦−r, r⟧",
				"real_converges_uniformly_on(«I», «S», f)",
				By(sums, between, At(PowerSeriesUniform, a, f, R, r)))
			polynomials := arg.Have(
				"each partial sum is a polynomial, so it is continuous on ⟦−r, r⟧",
				"∀n:num. real_continuous_on(«I», «S»(n))",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					partial := d.TermAs[Fun[Real, Real]]("«S»(n)")
					polynomial := d.Have(
						"the n-th partial sum is the polynomial of degree at most n with coefficients a",
						"polynomial_function(«S»(n))",
						Derive(func(e *Argument) {
							e.Do(Unfold(real_polynomial.PolynomialFunctionDef))
							e.Take(n)
							e.Take(a)
							e.Show(
								"at degree n with coefficients a, the polynomial is the partial sum itself at every x",
								Basic())
						}))
					d.Show(
						"a polynomial is continuous at every point",
						By(
							polynomial,
							real_continuous.PolynomialFunctionContinuous.At(partial),
							real_continuous.ContinuousMapIffPointwise.At(partial),
							real_continuous.ContinuousAtOn.At(partial, interval)))
				}))
			continuousOn := arg.Have(
				"so f, their uniform limit, is continuous on ⟦−r, r⟧",
				"real_continuous_on(«I», f)",
				By(
					polynomials,
					uniform,
					real_uniform_convergence.UniformLimitContinuous.At(
						arg.TermAs[Fun2[Nat, Real, Real]]("«S»"),
						f,
						interval)))
			ball := arg.Have(
				"the ball of radius r − |c| about c lies in ⟦−r, r⟧: |x| ≤ |x − c| + |c|",
				"∀x:real. |x - c| < r - |c| ⇒ |x| ≤ r",
				ByArith())
			arg.Show(
				"c is interior to ⟦−r, r⟧, so f is continuous at c",
				ByArith(
					continuousOn,
					between,
					ball,
					real_continuous.ContinuousAtInterior.At(f, interval, c, arg.TermAs[Real]("r - |c|"))))
		}),
})}
