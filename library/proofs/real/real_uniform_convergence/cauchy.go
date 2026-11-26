// cauchy.go — a uniform limit is a pointwise one, the Cauchy criterion
// for uniform convergence, and the Weierstrass M-test, which is that
// criterion read at the partial sums of a series of functions.

package real_uniform_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// UniformImpPointwise — a sequence of functions converging uniformly on
// s converges, at each point of s, to the limit's value there: the index
// that serves every point of s at once serves that one.
var UniformImpPointwise = uniformImpPointwiseThm{family.Add(registry.ProofEntry{
	Name: "UniformImpPointwise",
	Key:  "prop_6aa06d1894445ea3",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → real → real). ∀g:(real → real). ∀s:set(real). ∀x:real.",
		Hypotheses: []string{
			"real_converges_uniformly_on(s, f, g)",
			"x ∈ s",
		},
		Conclusion: "(λn:num. f(n)(x)) ⟶ g(x)",
	},
		func(
			a *Argument,
			f *Arrow2[Nat, Real, Real],
			g *Arrow[Real, Real],
			s *Expr[Set[Real]],
			x *Expr[Real],
			uniform, xIn Fact,
		) {
			near := a.Unfolded(uniform, RealConvergesUniformlyOnDef)
			a.Do(Unfold(real_sequences.RealConvergesToDef))
			ε := a.FixAs[Real]()
			pos := a.Assume()
			a.Show(
				"the index past which every point of s is within ε of g serves x",
				By(near.At(ε), pos, xIn))
		}),
})}

// UniformCauchy — the Cauchy criterion for uniform convergence: a
// sequence of functions converges uniformly on s exactly when, for every
// ε > 0, one index puts any two of its members past it within ε of each
// other at every point of s.
//
// Forward, two members past the index the limit gives at ε/2 are each
// within ε/2 of it. Backward, at each point of s the values form a Cauchy
// sequence, which converges to its upper limit, and that is the limit
// function. Given ε, the criterion at ε/2 hands over an index N. For
// n ≥ N and x in s the values at x converge, so past some M they are
// within ε/2 of the limit; at m = N + M, past both, f(n)(x) is within
// ε/2 of f(m)(x), which is within ε/2 of the limit.
var UniformCauchy = uniformCauchyThm{family.Add(registry.ProofEntry{
	Name: "UniformCauchy",
	Key:  "prop_e2d48d76f8cda004",
	Build: family.Theorem("∀f:(num → real → real). ∀s:set(real). "+
		"    (∃g:(real → real). real_converges_uniformly_on(s, f, g)) ⇔ "+
		"    ∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. ∀x:real. N ≤ m ∧ N ≤ n ∧ x ∈ s ⇒ |f(m)(x) - f(n)(x)| < ε",
		func(a *Argument, f *Arrow2[Nat, Real, Real], s *Expr[Set[Real]]) {
			a.Iff()
			a.Forward(
				"two members past the index the limit gives at ε/2 are each within ε/2 of it",
				func(b *Argument, convergent Fact) {
					_, uniform := b.UnpackAs[Fun[Real, Real]](convergent)
					near := b.Unfolded(uniform, RealConvergesUniformlyOnDef)
					b.FixAs[Real]()
					pos := b.Assume()
					half := b.TermAs[Real]("ε / &2")
					halfPos := b.Have(
						"half of ε is again a positive distance",
						"&0 < ε / &2",
						ByArith(pos))
					N, tail := b.ObtainAs[Nat](
						"an index past which every member is within ε/2 of g on all of s",
						"∃N:num. ∀n:num. ∀x:real. N ≤ n ∧ x ∈ s ⇒ |f(n)(x) - g(x)| < ε / &2",
						By(near.At(half), halfPos))
					b.Take(N)
					m := b.FixAs[Nat]()
					n := b.FixAs[Nat]()
					x := b.FixAs[Real]()
					past := b.Assume()
					b.Show(
						"f(m)(x) and f(n)(x) are each within ε/2 of g(x), so within ε of each other",
						ByArith(tail.At(m, x), tail.At(n, x), past))
				})
			a.Backward(
				"the values at each point converge to their upper limit, and they do so uniformly",
				func(b *Argument, cauchy Fact) {
					pointwise := b.Have(
						"at each point of s the values form a Cauchy sequence",
						"∀x:real. x ∈ s ⇒ real_cauchy(λn:num. f(n)(x))",
						Derive(func(c *Argument) {
							c.FixAs[Real]()
							xIn := c.Assume()
							c.Do(Unfold(real_sequences.RealCauchyDef))
							ε := c.FixAs[Real]()
							pos := c.Assume()
							c.Show(
								"the index the criterion gives at ε serves at x",
								By(cauchy.At(ε), pos, xIn))
						}))
					toLimit := b.Have(
						"so they converge, to their upper limit",
						"∀x:real. x ∈ s ⇒ (λn:num. f(n)(x)) ⟶ real_limsup(λn:num. f(n)(x))",
						By(pointwise, real_sequences.CauchyConverges))

					b.Take(b.TermAs[Fun[Real, Real]]("λx:real. real_limsup(λn:num. f(n)(x))"))
					b.Do(Unfold(RealConvergesUniformlyOnDef))
					b.FixAs[Real]()
					pos := b.Assume()
					half := b.TermAs[Real]("ε / &2")
					halfPos := b.Have(
						"half of ε is again a positive distance",
						"&0 < ε / &2",
						ByArith(pos))
					N, together := b.ObtainAs[Nat](
						"the criterion at ε/2: past some N any two members are within ε/2 of each other on all of s",
						"∃N:num. ∀m n:num. ∀x:real. N ≤ m ∧ N ≤ n ∧ x ∈ s ⇒ |f(m)(x) - f(n)(x)| < ε / &2",
						By(cauchy.At(half), halfPos))
					b.Take(N)
					n := b.FixAs[Nat]()
					x := b.FixAs[Real]()
					guards := b.Conjuncts(
						b.Assume(),
						"n is past N",
						"x is a point of s")
					past, xIn := guards[0], guards[1]
					_, nearLimit := b.ObtainAs[Nat](
						"the values at x converge: past some M they are within ε/2 of the limit",
						"∃M:num. ∀m:num. M ≤ m ⇒ |f(m)(x) - real_limsup(λn:num. f(n)(x))| < ε / &2",
						By(toLimit.At(x), xIn, halfPos, real_sequences.RealConvergesToDef))
					m := b.TermAs[Nat]("N + M")
					b.Show(
						"at m = N + M, past both, f(n)(x) is within ε/2 of f(m)(x), which is within ε/2 of the limit",
						ByArith(together.At(m, n, x), nearLimit.At(m), past, xIn))
				})
		}),
})}

// WeierstrassMajorant — the Weierstrass M-test (majorant test): a series
// of functions dominated on s, term by term, by a convergent series of
// numbers M(n) sums at each point of s, and its partial sums converge to
// the sum uniformly on s.
//
// The bound on u(n) is the same at every point, so the tails of the
// series become small at every point at once: past the index where the
// tails of M are below ε, a tail of u at x is at most the same tail of M.
// Two partial sums differ by the tail between them, so the partial sums
// meet the uniform Cauchy criterion and converge uniformly to some g; at
// each point of s they converge to g's value there, which is what it
// means for the series to sum to it.
var WeierstrassMajorant = weierstrassMajorantThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassMajorant",
	Key:  "prop_9ea8a4a237d6d619",
	Build: family.Theorem(Statement{
		Binders: "∀u:(num → real → real). ∀M:(num → real). ∀s:set(real). ∀t:real.",
		Hypotheses: []string{
			"∀n:num. ∀x:real. x ∈ s ⇒ |u(n)(x)| ≤ M(n)",
			"real_sums(M, t)",
		},
		Conclusion: "∃g:(real → real). " +
			"    (∀x:real. x ∈ s ⇒ real_sums(λn:num. u(n)(x), g(x))) ∧ real_converges_uniformly_on(s, «S», g)",
		Abbrev: Abbrev{
			{Name: "S", Text: "λn:num. λx:real. Σ_{k∈0 .. n} u(k)(x)"},
		},
	},
		func(
			a *Argument,
			u *Arrow2[Nat, Real, Real],
			M *Arrow[Nat, Real],
			s *Expr[Set[Real]],
			t *Expr[Real],
			bound, sums Fact,
		) {
			mTails := a.Have(
				"M has a sum, so its tails become uniformly small",
				"∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. N ≤ m ⇒ |Σ_{k∈m .. n} M(k)| < ε",
				By(sums, real_series.SumsCauchy))
			tails := a.Have(
				"so do the tails of u, by one index at every point of s: each is at most the same tail of M",
				"∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. ∀x:real. N ≤ m ∧ x ∈ s ⇒ |Σ_{k∈m .. n} u(k)(x)| < ε",
				Derive(func(c *Argument) {
					ε := c.FixAs[Real]()
					pos := c.Assume()
					N, small := c.ObtainAs[Nat](
						"past some N every tail of M is below ε",
						"∃N:num. ∀m n:num. N ≤ m ⇒ |Σ_{k∈m .. n} M(k)| < ε",
						By(mTails.At(ε), pos))
					c.Take(N)
					m := c.FixAs[Nat]()
					n := c.FixAs[Nat]()
					c.FixAs[Real]()
					past := c.Assume()
					c.Show(
						"term by term |u(k)(x)| ≤ M(k), so the tail of u at "+
							"x is at most the tail of M, at most its size, below ε",
						ByArith(
							small.At(m, n),
							bound,
							past,
							real_sum.IntervalDominated.At(m, n, c.TermAs[Fun[Nat, Real]]("λk:num. u(k)(x)"), M),
							real_sgn_abs.AbsDominates.At(c.TermAs[Real]("Σ_{k∈m .. n} M(k)"))))
				}))
			difference := a.Have(
				"two partial sums at a point differ by the tail between them",
				"∀p q:num. ∀x:real. p ≤ q ⇒ Σ_{k∈0 .. q} u(k)(x) = Σ_{k∈0 .. p} u(k)(x) + Σ_{k∈p + 1 .. q} u(k)(x)",
				Derive(func(c *Argument) {
					p := c.FixAs[Nat]()
					q := c.FixAs[Nat]()
					c.FixAs[Real]()
					upTo := c.Assume()
					d, offset := c.ObtainAs[Nat](
						"q is p plus an offset d",
						"∃d:num. q = p + d",
						By(upTo, nat_order.LessEqExists.At(q, p)))
					c.Show(
						"the interval from 0 to p + d cut after p",
						By(
							offset,
							real_sum.SplitAt.At(c.TermAs[Nat]("0"), p, d, c.TermAs[Fun[Nat, Real]]("λk:num. u(k)(x)")),
							nat_order.ZeroLessEq.At(c.TermAs[Nat]("p + 1"))))
				}))
			cauchy := a.Have(
				"so the partial sums are uniformly Cauchy on s",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃N:num. ∀m n:num. ∀x:real. " +
						"    N ≤ m ∧ N ≤ n ∧ x ∈ s ⇒ |Σ_{k∈0 .. m} u(k)(x) - Σ_{k∈0 .. n} u(k)(x)| < ε",
				},
				Derive(func(c *Argument) {
					ε := c.FixAs[Real]()
					pos := c.Assume()
					N, small := c.ObtainAs[Nat](
						"past some N every tail of u is below ε on all of s",
						"∃N:num. ∀m n:num. ∀x:real. N ≤ m ∧ x ∈ s ⇒ |Σ_{k∈m .. n} u(k)(x)| < ε",
						By(tails.At(ε), pos))
					c.Take(N)
					m := c.FixAs[Nat]()
					n := c.FixAs[Nat]()
					x := c.FixAs[Real]()
					past := c.Assume()
					c.Cases(c.Term("m ≤ n"))
					c.When(
						"m ≤ n: the partial sum to n is the one to m plus the tail from m + 1 to n",
						func(d *Argument, upTo Fact) {
							d.Show(
								"a tail starting past N, so below ε",
								ByArith(difference.At(m, n, x), small.At(d.TermAs[Nat]("m + 1"), n, x), upTo, past))
						})
					c.Otherwise(
						"n < m: the partial sum to m is the one to n plus the tail from n + 1 to m",
						func(d *Argument, beyond Fact) {
							d.Show(
								"a tail starting past N, so below ε",
								ByArith(difference.At(n, m, x), small.At(d.TermAs[Nat]("n + 1"), m, x), beyond, past))
						})
				}))

			partial := a.TermAs[Fun2[Nat, Real, Real]]("«S»")
			g, uniform := a.ObtainAs[Fun[Real, Real]](
				"by the Cauchy criterion they converge uniformly on s, to some g",
				"∃g:(real → real). real_converges_uniformly_on(s, «S», g)",
				By(cauchy, UniformCauchy))
			a.Take(g)
			pointwise := a.Have(
				"at each point of s the partial sums converge to g's value there, so the series sums to it",
				"∀x:real. x ∈ s ⇒ real_sums(λn:num. u(n)(x), g(x))",
				Derive(func(c *Argument) {
					x := c.FixAs[Real]()
					xIn := c.Assume()
					c.Show(
						"a uniform limit is a pointwise one, and a series sums to the limit of its partial sums",
						By(uniform, xIn, UniformImpPointwise.At(partial, g, s, x), real_series.RealSumsDef))
				}))
			a.Show(
				"g is the sum at every point of s and the uniform limit of the partial sums",
				By(pointwise, uniform))
		}),
})}
