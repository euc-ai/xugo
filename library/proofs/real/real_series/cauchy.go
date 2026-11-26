// cauchy.go — the Cauchy criterion for series, and the terms of a
// convergent series tending to 0 and so bounded.

package real_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// SumsCauchy — the Cauchy criterion for series. A series has a sum
// exactly when its partial sums converge, that is, when they are Cauchy;
// and a tail is the difference of two partial sums. So an index past
// which the partial sums are within ε of each other bounds by ε every
// tail starting beyond it, and an index past which the tails are below ε
// is one past which the partial sums are within ε, two of them differing
// by the tail between them.
var SumsCauchy = sumsCauchyThm{family.Add(registry.ProofEntry{
	Name: "SumsCauchy",
	Key:  "prop_1af2017b6591825a",
	Build: family.Theorem("∀a:(num → real). "+
		"    (∃s:real. real_sums(a, s)) ⇔ "+
		"    ∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. N ≤ m ⇒ |Σ_{k∈m .. n} a(k)| < ε",
		func(arg *Argument, a *Arrow[Nat, Real]) {
			difference := arg.Have(
				"a tail is the difference of two partial sums",
				"∀p q:num. p ≤ q ⇒ Σ_{k∈0 .. q} a(k) = Σ_{k∈0 .. p} a(k) + Σ_{k∈p + 1 .. q} a(k)",
				Derive(func(e *Argument) {
					p := e.FixAs[Nat]()
					q := e.FixAs[Nat]()
					upTo := e.Assume()
					offset, offsetEq := e.ObtainAs[Nat](
						"q is p plus an offset d",
						"∃d:num. q = p + d",
						By(upTo, nat_order.LessEqExists.At(q, p)))
					e.Show(
						"the interval from 0 to p + d cut after p",
						By(
							Normalized,
							offsetEq,
							real_sum.SplitAt.At(e.TermAs[Nat]("0"), p, offset, a),
							nat_order.ZeroLessEq.At(e.TermAs[Nat]("p + 1"))))
				}))

			arg.Iff()
			arg.Forward(
				"the partial sums are Cauchy, and a tail starting past N is a difference of two of them past N",
				func(b *Argument, summable Fact) {
					s, sums := b.UnpackAs[Real](summable)
					toSum := b.Have(
						"the partial sums tend to the sum s",
						"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
						By(sums, RealSumsDef))
					partial := b.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k∈0 .. n} a(k)")
					cauchy := b.Have(
						"so they are Cauchy",
						"real_cauchy(λn:num. Σ_{k∈0 .. n} a(k))",
						By(toSum, real_sequences.ConvergentImpCauchy.At(partial, s)))
					near := b.Unfolded(cauchy, real_sequences.RealCauchyDef)
					ε := b.FixAs[Real]()
					pos := b.Assume()
					_, within := b.ObtainAs[Nat](
						"past some N any two partial sums are within ε",
						"∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ |Σ_{k∈0 .. m} a(k) - Σ_{k∈0 .. n} a(k)| < ε",
						By(near.At(ε), pos))
					b.Take(b.TermAs[Nat]("N + 1"))
					m := b.FixAs[Nat]()
					n := b.FixAs[Nat]()
					pastM := b.Assume()
					b.Cases(b.Term("n < m"))
					b.When(
						"n < m: the tail from m to n is empty",
						func(c *Argument, before Fact) {
							c.Show(
								"its sum is 0, and |0| < ε",
								By(before, pos, real_sum.EmptyInterval.At(n, m, a), real_sgn_abs.AbsOfZero))
						})
					b.Otherwise(
						"m ≤ n: with m = p + 1 the tail is the partial sum to n less the one to p",
						func(c *Argument, notBefore Fact) {
							p, successor := c.ObtainAs[Nat](
								"m, past N + 1, is p + 1 for some p",
								"∃p:num. m = p + 1",
								Derive(func(d *Argument) {
									d.Take(d.TermAs[Nat]("m - 1"))
									d.Show(
										"m is at least 1",
										ByArith(pastM))
								}))
							c.Show(
								"p and n are both past N, so it is below ε",
								ByArith(notBefore, pastM, successor, difference.At(p, n), within.At(p, n)))
						})
				})
			arg.Backward(
				"small tails make the partial sums Cauchy, so they converge and the series sums to their limit",
				func(b *Argument, tails Fact) {
					cauchy := b.Have(
						"the partial sums are Cauchy",
						"real_cauchy(λn:num. Σ_{k∈0 .. n} a(k))",
						Simp(Fwd(real_sequences.RealCauchyDef)),
						Derive(func(c *Argument) {
							ε := c.FixAs[Real]()
							pos := c.Assume()
							N, small := c.ObtainAs[Nat](
								"past some N every tail is below ε",
								"∃N:num. ∀m n:num. N ≤ m ⇒ |Σ_{k∈m .. n} a(k)| < ε",
								By(tails.At(ε), pos))
							c.Take(N)
							m := c.FixAs[Nat]()
							n := c.FixAs[Nat]()
							past := c.Assume()
							c.Cases(c.Term("m ≤ n"))
							c.When(
								"m ≤ n: the partial sums to m and to n differ by the tail from m + 1 to n",
								func(d *Argument, upTo Fact) {
									d.Show(
										"a tail starting past N, so below ε",
										ByArith(upTo, past, difference.At(m, n), small.At(d.TermAs[Nat]("m + 1"), n)))
								})
							c.Otherwise(
								"n < m: they differ by the tail from n + 1 to m",
								func(d *Argument, beyond Fact) {
									d.Show(
										"a tail starting past N, so below ε",
										ByArith(beyond, past, difference.At(n, m), small.At(d.TermAs[Nat]("n + 1"), m)))
								})
						}))
					toLimit := b.Have(
						"a Cauchy sequence tends to its upper limit",
						"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ real_limsup(λn:num. Σ_{k∈0 .. n} a(k))",
						By(cauchy, real_sequences.CauchyConverges))
					b.Take(b.TermAs[Real]("real_limsup(λn:num. Σ_{k∈0 .. n} a(k))"))
					b.Show(
						"so the series sums to it",
						By(toLimit, RealSumsDef))
				})
		}),
})}

// SumsTermsTendToZero — the Cauchy criterion read at a one-term tail. A
// series with a sum has, for every ε > 0, an index N past which every
// tail is below ε in size; the tail from n to n is the single term a(n),
// so past N every term lies within ε of 0.
var SumsTermsTendToZero = sumsTermsTendToZeroThm{family.Add(registry.ProofEntry{
	Name: "SumsTermsTendToZero",
	Key:  "prop_e6b0aab51b06951",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀s:real.",
		Hypotheses: []string{
			"real_sums(a, s)",
		},
		Conclusion: "a ⟶ &0",
	},
		func(arg *Argument, a *Arrow[Nat, Real], s *Expr[Real], sums Fact) {
			tails := arg.Have(
				"a has a sum, so its tails become uniformly small",
				"∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. N ≤ m ⇒ |Σ_{k∈m .. n} a(k)| < ε",
				Simp(Rev(SumsCauchy)),
				By(Normalized, sums))
			near := arg.Have(
				"so past some index every term lies within ε of 0",
				"∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - &0| < ε",
				Derive(func(d *Argument) {
					ε := d.FixAs[Real]()
					pos := d.Assume()
					N, small := d.ObtainAs[Nat](
						"past some N every tail is below ε",
						"∃N:num. ∀m n:num. N ≤ m ⇒ |Σ_{k∈m .. n} a(k)| < ε",
						By(tails.At(ε), pos))
					d.Take(N)
					n := d.FixAs[Nat]()
					past := d.Assume()
					d.Show(
						"the tail from n to n is the term a(n) and starts past N, so |a(n) − 0| = |a(n)| < ε",
						By(
							Normalized,
							small.At(n, n),
							past,
							real_sum.IntervalPoint.At(n, a),
							real_ring.SubRightZero.At(a.Apply(n))))
				}))
			arg.Show(
				"which is a tending to 0, by the definition of the limit",
				By(near, real_sequences.RealConvergesToDef))
		}),
})}

// SumsTermsBounded — a convergent series has bounded terms: they tend to
// 0, and a convergent sequence is bounded.
var SumsTermsBounded = sumsTermsBoundedThm{family.Add(registry.ProofEntry{
	Name: "SumsTermsBounded",
	Key:  "prop_d8e8908bea538641",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real).",
		Hypotheses: []string{
			"∃s:real. real_sums(a, s)",
		},
		Conclusion: "∃B:real. ∀n:num. |a(n)| ≤ B",
	},
		func(arg *Argument, a *Arrow[Nat, Real], converges Fact) {
			s, sums := arg.UnpackAs[Real](converges)
			arg.Show(
				"the terms tend to 0, and a convergent sequence is bounded",
				By(
					sums,
					SumsTermsTendToZero.At(a, s),
					real_sequences.ConvergentBounded.At(a, arg.TermAs[Real]("&0"))))
		}),
})}
