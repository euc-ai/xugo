// integral.go — the integral commutes with uniform limits: a uniform
// limit of integrable functions on ⟦a, b⟧ is integrable, its integral the
// limit of their integrals, and a uniformly convergent series of
// integrable functions is integrated term by term.

package real_uniform_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/registry"
)

// UniformLimitIntegral — a sequence of functions with integrals I(n) on
// ⟦a, b⟧, converging uniformly on ⟦a, b⟧ to g: then g has an integral on
// ⟦a, b⟧, and it is the limit of the I(n).
//
// The integrals form a Cauchy sequence. Past the index at which any two
// members lie within η = ε/(b − a + 1) of each other on ⟦a, b⟧, the
// difference f(m) − f(n) has integral I(m) − I(n), at most η·(b − a) < ε in
// size. So the I(n) converge, to some J. That g has integral J is the ε/3
// argument: with η = (ε/3)/(b − a + 1), past N₁ every member is within η
// of g on ⟦a, b⟧, past N₂ the integrals are within ε/3 of J, and below some
// mesh δ the Riemann sums of f(N₁ + N₂) are within ε/3 of its integral. On
// a partition finer than δ the Riemann sum of g lies within η·(b − a) < ε/3
// of that of f(N₁ + N₂), which lies within ε/3 of I(N₁ + N₂), which lies
// within ε/3 of J.
var UniformLimitIntegral = uniformLimitIntegralThm{family.Add(registry.ProofEntry{
	Name: "UniformLimitIntegral",
	Key:  "prop_f00b937acc860a02",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → real → real). ∀g:(real → real). ∀a b:real. ∀I:(num → real).",
		Hypotheses: []string{
			"∀n:num. real_has_integral(f(n), a, b, I(n))",
			"real_converges_uniformly_on(⟦a, b⟧, f, g)",
		},
		Conclusion: "∃J:real. real_has_integral(g, a, b, J) ∧ I ⟶ J",
	},
		func(
			arg *Argument,
			f *Arrow2[Nat, Real, Real],
			g *Arrow[Real, Real],
			a, b *Expr[Real],
			I *Arrow[Nat, Real],
			integrals, uniform Fact,
		) {
			ordered := arg.Have(
				"an interval over which f(0) has an integral is ordered",
				"a ≤ b",
				By(integrals.At(arg.TermAs[Nat]("0")), real_integral.RealHasIntegralDef))
			together := arg.Have(
				"by the uniform Cauchy criterion, past some index "+
					"any two members are within ε of each other on ⟦a, b⟧",
				"∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. ∀x:real. N ≤ m ∧ N ≤ n ∧ x ∈ ⟦a, b⟧ ⇒ |f(m)(x) - f(n)(x)| < ε",
				By(uniform, UniformCauchy))
			cauchy := arg.Have(
				"so the integrals form a Cauchy sequence",
				"real_cauchy(I)",
				Derive(func(c *Argument) {
					c.Do(Unfold(real_sequences.RealCauchyDef))
					c.FixAs[Real]()
					pos := c.Assume()
					η, ηDef := c.LetAs[Real]("η", "ε / (b - a + &1)")
					small := c.Have(
						"η is positive, and η·(b − a) < ε",
						"&0 < η ∧ η * (b - a) < ε",
						ByArith(ηDef, ordered, pos))
					N, within := c.ObtainAs[Nat](
						"past some N any two members are within η of each other on ⟦a, b⟧",
						"∃N:num. ∀m n:num. ∀x:real. N ≤ m ∧ N ≤ n ∧ x ∈ ⟦a, b⟧ ⇒ |f(m)(x) - f(n)(x)| < η",
						By(together.At(η), small))
					c.Take(N)
					m := c.FixAs[Nat]()
					n := c.FixAs[Nat]()
					past := c.Assume()
					difference := c.Have(
						"for m, n past N the difference f(m) − f(n) is at most η in size on ⟦a, b⟧",
						"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(m)(x) - f(n)(x)| ≤ η",
						c.ForEach(func(x *Expr[Real]) Action {
							return By(within.At(m, n, x), past, real_order_ring.LessEqOfLessThan)
						}))
					fm := c.TermAs[Fun[Real, Real]]("f(m)")
					fn := c.TermAs[Fun[Real, Real]]("f(n)")
					bound := c.Have(
						"f(m) − f(n) has integral I(m) − I(n), which is therefore at most η·(b − a) in size",
						"|I(m) - I(n)| ≤ η * (b - a)",
						By(
							integrals.At(m),
							integrals.At(n),
							difference,
							real_integral.HasIntegralSub.At(fm, fn, a, b, I.Apply(m), I.Apply(n)),
							real_integral.HasIntegralBound.At(
								c.TermAs[Fun[Real, Real]]("λx:real. f(m)(x) - f(n)(x)"),
								a,
								b,
								c.TermAs[Real]("I(m) - I(n)"),
								η)))
					c.Show(
						"|I(m) − I(n)| ≤ η·(b − a) < ε",
						ByArith(bound, small))
				}))
			J, limit := arg.ObtainAs[Real](
				"a Cauchy sequence converges: the integrals tend to some J",
				"∃J:real. I ⟶ J",
				By(cauchy, real_sequences.CauchyIffConvergent))
			meshes := arg.Have(
				"for every ε some mesh brings the Riemann sums of g within ε of J",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀n:num. ∀p t:(num → real). " +
						"        p(0) = a ∧ " +
						"        p(n + 1) = b ∧ " +
						"        (∀k:num. k ≤ n ⇒ p(k) ≤ t(k) ∧ t(k) ≤ p(k + 1) ∧ p(k + 1) - p(k) < δ) ⇒ " +
						"        |Σ_{k∈0 .. n} g(t(k)) * (p(k + 1) - p(k)) - J| < ε)",
				},
				Derive(func(c *Argument) {
					near := c.Unfolded(uniform, RealConvergesUniformlyOnDef)
					tail := c.Unfolded(limit, real_sequences.RealConvergesToDef)
					c.FixAs[Real]()
					pos := c.Assume()
					η, ηDef := c.LetAs[Real]("η", "ε / &3 / (b - a + &1)")
					small := c.Have(
						"ε/3 and η are positive, and η·(b − a) < ε/3",
						"&0 < ε / &3 ∧ &0 < η ∧ η * (b - a) < ε / &3",
						ByArith(ηDef, ordered, pos))
					N1, uniformly := c.ObtainAs[Nat](
						"past some N₁ every member is within η of g on ⟦a, b⟧",
						"∃N₁:num. ∀n:num. ∀x:real. N₁ ≤ n ∧ x ∈ ⟦a, b⟧ ⇒ |f(n)(x) - g(x)| < η",
						By(near.At(η), small))
					N2, converging := c.ObtainAs[Nat](
						"past some N₂ every integral is within ε/3 of J",
						"∃N₂:num. ∀n:num. N₂ ≤ n ⇒ |I(n) - J| < ε / &3",
						By(tail.At(c.TermAs[Real]("ε / &3")), small))
					m := c.TermAs[Nat]("N₁ + N₂")
					closeToG := c.Have(
						"f(N₁ + N₂) is within η of g on ⟦a, b⟧",
						"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(N₁ + N₂)(x) - g(x)| ≤ η",
						c.ForEach(func(x *Expr[Real]) Action {
							return By(uniformly.At(m, x), nat_order.LessEqAdd.At(N1, N2), real_order_ring.LessEqOfLessThan)
						}))
					δ, fine := c.ObtainAs[Real](
						"f(N₁ + N₂) has integral I(N₁ + N₂): below some mesh δ its Riemann sums are within ε/3 of it",
						"∃δ:real. "+
							"    &0 < δ ∧ "+
							"    (∀n:num. ∀p t:(num → real). "+
							"        p(0) = a ∧ "+
							"        p(n + 1) = b ∧ "+
							"        (∀k:num. k ≤ n ⇒ p(k) ≤ t(k) ∧ t(k) ≤ p(k + 1) ∧ p(k + 1) - p(k) < δ) ⇒ "+
							"        |Σ_{k∈0 .. n} f(N₁ + N₂)(t(k)) * (p(k + 1) - p(k)) - I(N₁ + N₂)| < ε / &3)",
						By(integrals.At(m), real_integral.RealHasIntegralDef, small))
					mesh := c.Conjuncts(
						fine,
						"δ is positive",
						"below δ the Riemann sums of f(N₁ + N₂) are within ε/3 of its integral")
					c.Take(δ)
					c.Show(
						"the mesh δ serves g",
						SplitConj(
							Case(
								"δ is positive",
								By(mesh[0])),
							Case(
								"below δ the Riemann sum of g is within η·(b − a) of that of f(N₁ + N₂), so within ε of J",
								Derive(func(d *Argument) {
									n := d.FixAs[Nat]()
									p := d.FixAs[Fun[Nat, Real]]()
									t := d.FixAs[Fun[Nat, Real]]()
									partition := d.Assume()
									sums := d.Have(
										"the Riemann sums of f(N₁ + N₂) and of g differ by at most η·(b − a)",
										"|Σ_{k∈0 .. n} f(N₁ + N₂)(t(k)) * (p(k + 1) - p(k)) - "+
											"Σ_{k∈0 .. n} g(t(k)) * (p(k + 1) - p(k))| ≤ "+
											"η * (b - a)",
										By(
											closeToG,
											partition,
											real_integral.RiemannSumsClose.At(d.TermAs[Fun[Real, Real]]("f(N₁ + N₂)"), g, a, b, η, n, p, t)))
									d.Show(
										"g's sum is within η·(b − a) < ε/3 of f(N₁ + N₂)'s, within ε/3 of I(N₁ + N₂), within ε/3 of J",
										ByArith(
											mesh[1].At(n, p, t),
											partition,
											sums,
											converging.At(m),
											nat_order.LessEqAddLeft.At(N1, N2),
											small))
								}))))
				}))
			integrable := arg.Have(
				"so g has integral J on ⟦a, b⟧",
				"real_has_integral(g, a, b, J)",
				By(ordered, meshes, real_integral.RealHasIntegralDef))
			arg.Take(J)
			arg.Show(
				"g has integral J, and J is the limit of the integrals",
				By(integrable, limit))
		}),
})}

// UniformSumsIntegral — term-by-term integration: a series of functions
// with integrals c(k) on ⟦a, b⟧, whose partial sums converge uniformly on
// ⟦a, b⟧ to g, has g integrable on ⟦a, b⟧, and the series of the c(k) sums
// to its integral.
//
// Each partial sum has the partial sum of the c(k) as its integral, so the
// integral of the uniform limit g is the limit of those partial sums,
// which is what it means for the series of the c(k) to sum to it.
var UniformSumsIntegral = uniformSumsIntegralThm{family.Add(registry.ProofEntry{
	Name: "UniformSumsIntegral",
	Key:  "prop_e75da114cdd18a36",
	Build: family.Theorem(Statement{
		Binders: "∀u:(num → real → real). ∀c:(num → real). ∀g:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"∀k:num. real_has_integral(u(k), a, b, c(k))",
			"real_converges_uniformly_on(⟦a, b⟧, «S», g)",
		},
		Conclusion: "∃J:real. real_has_integral(g, a, b, J) ∧ real_sums(c, J)",
		Abbrev: Abbrev{
			{Name: "S", Text: "λn:num. λx:real. Σ_{k∈0 .. n} u(k)(x)"},
		},
	},
		func(
			arg *Argument,
			u *Arrow2[Nat, Real, Real],
			c *Arrow[Nat, Real],
			g *Arrow[Real, Real],
			a, b *Expr[Real],
			integrals, uniform Fact,
		) {
			J, limit := arg.ObtainAs[Real](
				"each partial sum has the partial sum of the c(k) as its "+
					"integral; their uniform limit g has the limit J of these",
				"∃J:real. real_has_integral(g, a, b, J) ∧ (λn:num. Σ_{k∈0 .. n} c(k)) ⟶ J",
				By(
					integrals,
					real_integral.HasIntegralSum,
					uniform,
					UniformLimitIntegral.At(
						arg.TermAs[Fun2[Nat, Real, Real]]("«S»"),
						g,
						a,
						b,
						arg.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k∈0 .. n} c(k)"))))
			arg.Take(J)
			arg.Show(
				"a series sums to the limit of its partial sums",
				By(limit, real_series.RealSumsDef))
		}),
})}
