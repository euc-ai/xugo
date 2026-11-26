// radius.go — Abel's lemma and the radius of convergence: a power series
// whose terms stay bounded at r converges absolutely at every point
// closer to 0 than r, and so the points where it converges fill an
// interval about 0.

package real_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// PowerSeriesAbelBounded — Abel's lemma: when the terms a(n)·rⁿ stay
// bounded by B, the series converges absolutely at every x closer to 0
// than r. With q = |x|/|r|, which lies in ⟦0, 1⟭, each |a(n)·xⁿ| is
// |a(n)·rⁿ|·qⁿ ≤ B·qⁿ, and B times the geometric series of q has a sum.
var PowerSeriesAbelBounded = powerSeriesAbelBoundedThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAbelBounded",
	Key:  "prop_8c8d60c74389ec3c",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀r B x:real.",
		Hypotheses: []string{
			"∀n:num. |a(n) * real_pow(r, n)| ≤ B",
			"|x| < |r|",
		},
		Conclusion: "∃s:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, s)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], r, B, x *Expr[Real], bounded, inside Fact) {
			positive := arg.Have(
				"r is not 0: |r| exceeds |x| ≥ 0",
				"&0 < |r|",
				ByArith(inside))
			q, qDef := arg.LetAs[Real]("q", "|x| / |r|")
			scaled := arg.Have(
				"|x| is q times |r|",
				"|x| = q * |r|",
				By(
					qDef,
					positive,
					real_order_field.EqDivMulLeft.At(q, arg.TermAs[Real]("|x|"), arg.TermAs[Real]("|r|"))))
			ratio := arg.Have(
				"so q lies in ⟦0, 1⟭, as |x| < |r|",
				"&0 ≤ q ∧ q < &1",
				ByArith(scaled, inside, positive))
			termwise := arg.Have(
				"each |a(n)·xⁿ| is at most B·qⁿ",
				"∀n:num. |a(n) * real_pow(x, n)| ≤ B * real_pow(q, n)",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					split := d.Have(
						"|x|ⁿ = qⁿ·|r|ⁿ, so the size of the term at x is its size at r times qⁿ",
						"|a(n) * real_pow(x, n)| = |a(n) * real_pow(r, n)| * real_pow(q, n)",
						Simp(Fwd(real_sgn_abs.AbsMul), Fwd(real_pow.AbsPow)),
						scaled.Rw(),
						Simp(Fwd(real_pow.MulPowDistrib)),
						ByArith())
					d.Show(
						"the size at r is at most B, and qⁿ ≥ 0",
						ByArith(bounded.At(n), split, ratio, real_pow.PowNonneg.At(q, n)))
				}))
			small := arg.Have(
				"q is below 1 in size",
				"|q| < &1",
				ByArith(ratio))
			geometric := arg.Have(
				"B times the geometric series of q sums to B·(1 − q)⁻¹",
				"real_sums(λn:num. B * real_pow(q, n), B * real_inv(&1 - q))",
				By(small, real_series.Geometric.At(q), real_series.SumsScale))
			arg.Show(
				"the series of sizes is dominated termwise by it, so it has a sum by comparison",
				By(
					termwise,
					geometric,
					real_sgn_abs.AbsIdempotent,
					real_series.Comparison.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n) * real_pow(x, n)|"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. B * real_pow(q, n)"),
						arg.TermAs[Real]("B * real_inv(&1 - q)"),
						arg.TermAs[Nat]("0"))))
		}),
})}

// PowerSeriesAbel — Abel's lemma for a series that converges at r: it
// converges absolutely at every x closer to 0 than r. The terms of a
// convergent series are bounded, and the bounded form applies.
var PowerSeriesAbel = powerSeriesAbelThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAbel",
	Key:  "prop_8354c02d3870a772",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀r x:real.",
		Hypotheses: []string{
			"∃s:real. real_sums(λn:num. a(n) * real_pow(r, n), s)",
			"|x| < |r|",
		},
		Conclusion: "∃s:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, s)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], r, x *Expr[Real], converges, inside Fact) {
			B, bounded := arg.ObtainAs[Real](
				"the series converges at r, so its terms there are bounded",
				"∃B:real. ∀n:num. |a(n) * real_pow(r, n)| ≤ B",
				By(
					converges,
					real_series.SumsTermsBounded.At(arg.TermAs[Fun[Nat, Real]]("λn:num. a(n) * real_pow(r, n)"))))
			arg.Show(
				"so the bounded form of Abel's lemma applies at r",
				By(bounded, inside, PowerSeriesAbelBounded.At(a, r, B, x)))
		}),
})}

// PowerSeriesAbsoluteInside — a power series that converges at every
// point of ⟬−R, R⟭ converges absolutely there: for |x| < R the point
// r = (|x| + R)/2 lies strictly between |x| and R, the series converges
// at r, and Abel's lemma at r applies.
var PowerSeriesAbsoluteInside = powerSeriesAbsoluteInsideThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAbsoluteInside",
	Key:  "prop_4516988f02c8f504",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀R x:real.",
		Hypotheses: []string{
			"∀y:real. |y| < R ⇒ ∃s:real. real_sums(λn:num. a(n) * real_pow(y, n), s)",
			"|x| < R",
		},
		Conclusion: "∃s:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, s)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], R, x *Expr[Real], converges, inside Fact) {
			r, rDef := arg.LetAs[Real]("r", "(|x| + R) / &2")
			between := arg.Have(
				"r lies strictly between |x| and R",
				"|x| < |r| ∧ |r| < R",
				ByArith(rDef, inside))
			arg.Show(
				"the series converges at r, and Abel's lemma at r applies",
				By(between, converges.At(r), PowerSeriesAbel.At(a, r, x)))
		}),
})}

// PowerSeriesAbsoluteBeyond — inside the interval where a power series
// converges, between each |x| < R and R lies a point ρ at which the
// series without its first term converges absolutely: ρ = (|x| + R)/2
// lies strictly between |x| and R, the series converges absolutely there,
// and dropping the first term |a(0)| of the series of sizes drops it from
// the sum.
var PowerSeriesAbsoluteBeyond = powerSeriesAbsoluteBeyondThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAbsoluteBeyond",
	Key:  "prop_613b53ea51bcb637",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀R x:real.",
		Hypotheses: []string{
			"∀y:real. |y| < R ⇒ ∃s:real. real_sums(λn:num. a(n) * real_pow(y, n), s)",
			"|x| < R",
		},
		Conclusion: "∃ρ t:real. |x| < ρ ∧ ρ < R ∧ real_sums(λn:num. |a(n + 1) * real_pow(ρ, n + 1)|, t)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], R, x *Expr[Real], converges, inside Fact) {
			ρ, ρDef := arg.LetAs[Real]("ρ", "(|x| + R) / &2")
			between := arg.Have(
				"ρ lies strictly between |x| and R",
				"|x| < ρ ∧ ρ < R ∧ |ρ| < R",
				ByArith(ρDef, inside))
			_, sizes := arg.ObtainAs[Real](
				"the series converges absolutely at ρ",
				"∃t:real. real_sums(λn:num. |a(n) * real_pow(ρ, n)|, t)",
				By(converges, between, PowerSeriesAbsoluteInside.At(a, R, ρ)))
			arg.Take(ρ)
			arg.Take(arg.TermAs[Real]("t - |a(0)|"))
			arg.Show(
				"dropping the first term |a(0)| from the series of sizes drops it from the sum",
				ByArith(sizes, between, real_series.SumsShift))
		}),
})}

// RadiusOfConvergence — a power series has a radius of convergence:
// either it converges absolutely everywhere, or some R ≥ 0 separates
// absolute convergence for |x| < R from divergence for |x| > R. The radii
// r at which the terms a(n)·rⁿ stay bounded form a set S, which holds 0.
// If S has no upper bound, every x has a point r of S beyond |x|, and
// Abel's lemma at r gives absolute convergence at x. Otherwise R is the
// supremum of S: below it lies a point of S, and Abel's lemma applies
// there; and where the series converges its terms are bounded, which
// puts |x| in S and so at most R.
var RadiusOfConvergence = radiusOfConvergenceThm{family.Add(registry.ProofEntry{
	Name: "RadiusOfConvergence",
	Key:  "prop_72bd1b613989d314",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real).",
		Conclusion: "(∀x:real. ∃s:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, s)) ∨ " +
			"(∃R:real. " +
			"    &0 ≤ R ∧ " +
			"    (∀x:real. |x| < R ⇒ ∃s:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, s)) ∧ " +
			"    (∀x:real. R < |x| ⇒ ¬(∃s:real. real_sums(λn:num. a(n) * real_pow(x, n), s))))",
		Abbrev: Abbrev{
			{Name: "S", Text: "{r:real | ∃B:real. ∀n:num. |a(n) * real_pow(r, n)| ≤ B}"},
		},
	},
		func(arg *Argument, a *Arrow[Nat, Real]) {
			S := arg.TermAs[Set[Real]]("«S»")
			zero := arg.TermAs[Real]("&0")
			abel := arg.Have(
				"the series converges absolutely at every x closer to 0 than a point r of S, by Abel's lemma",
				"∀r x:real. r ∈ «S» ∧ |x| < r ⇒ ∃s:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, s)",
				Derive(func(d *Argument) {
					r := d.FixAs[Real]()
					x := d.FixAs[Real]()
					given := d.Conjuncts(
						d.Assume(),
						"r lies in S",
						"x is closer to 0 than r")
					B, bounded := d.UnpackAs[Real](given[0])
					inside := d.Have(
						"r is positive, so |x| < |r|",
						"|x| < |r|",
						ByArith(given[1]))
					d.Show(
						"Abel's lemma at r",
						By(bounded, inside, PowerSeriesAbelBounded.At(a, r, B, x)))
				}))
			zeroBound := arg.Have(
				"at r = 0 the terms are a(0) and then 0, all at most |a(0)| in size",
				"∀n:num. |a(n) * real_pow(&0, n)| ≤ |a(0)|",
				Derive(func(d *Argument) {
					d.Induct("n")
					d.Base(
						"at n = 0 the term is a(0)·0⁰ = a(0)",
						ByArith())
					d.Step(
						"past 0 the power of 0 vanishes, and with it the term",
						ByArith())
				}))
			zeroIn := arg.Have(
				"so 0 lies in S",
				"&0 ∈ «S»",
				By(zeroBound))

			arg.Cases(arg.Term("∃b:real. ∀r:real. r ∈ «S» ⇒ r ≤ b"))
			arg.Otherwise(
				"S has no upper bound: the series converges absolutely everywhere",
				func(b *Argument, unbounded Fact) {
					everywhere := b.Have(
						"every x has a point of S beyond |x|, and Abel's lemma applies there",
						"∀x:real. ∃s:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, s)",
						Derive(func(d *Argument) {
							x := d.FixAs[Real]()
							r, beyond := d.ObtainAs[Real](
								"|x| bounds no S, so some point r of S exceeds it",
								"∃r:real. r ∈ «S» ∧ |x| < r",
								By(unbounded, real_order_ring.NotLessEq))
							d.Show(
								"Abel's lemma at r",
								By(abel.At(r, x), beyond))
						}))
					b.Show(
						"the first alternative holds",
						By(everywhere))
				})
			arg.When(
				"S is bounded above: its supremum R is the radius",
				func(b *Argument, bounded Fact) {
					R := b.TermAs[Real]("sup(«S»)")
					nonempty := b.Have(
						"S is not empty, as it holds 0",
						"«S» ≠ ∅",
						By(zeroIn, set_basic.MemberNotEmpty.At(S)))
					nonneg := b.Have(
						"0 lies in S, so the supremum is at least 0",
						"&0 ≤ sup(«S»)",
						By(bounded, zeroIn, real_sup_inf.MemberLessEqSup.At(S, zero)))
					inside := b.Have(
						"below the supremum the series converges absolutely: a point of S lies beyond |x|",
						"∀x:real. |x| < sup(«S») ⇒ ∃s:real. real_sums(λn:num. |a(n) * real_pow(x, n)|, s)",
						Derive(func(d *Argument) {
							x := d.FixAs[Real]()
							below := d.Assume()
							r, beyond := d.ObtainAs[Real](
								"|x| is below the supremum of S, so some point r of S exceeds it",
								"∃r:real. r ∈ «S» ∧ |x| < r",
								By(nonempty, below, real_sup_inf.SupApproach.At(S, d.TermAs[Real]("|x|"))))
							d.Show(
								"Abel's lemma at r",
								By(abel.At(r, x), beyond))
						}))
					within := b.Have(
						"where the series converges, |x| is at most the supremum",
						"∀x:real. (∃s:real. real_sums(λn:num. a(n) * real_pow(x, n), s)) ⇒ |x| ≤ sup(«S»)",
						Derive(func(d *Argument) {
							d.FixAs[Real]()
							converges := d.Assume()
							_, boundedTerms := d.ObtainAs[Real](
								"the series converges at x, so its terms there are bounded",
								"∃B:real. ∀n:num. |a(n) * real_pow(x, n)| ≤ B",
								By(
									converges,
									real_series.SumsTermsBounded.At(d.TermAs[Fun[Nat, Real]]("λn:num. a(n) * real_pow(x, n)"))))
							sameSize := d.Have(
								"the terms at |x| have the sizes of the terms at x",
								"∀n:num. |a(n) * real_pow(|x|, n)| = |a(n) * real_pow(x, n)|",
								Simp(Fwd(real_sgn_abs.AbsMul), Fwd(real_pow.AbsPow), Fwd(real_sgn_abs.AbsIdempotent)),
								Basic())
							atAbs := d.Have(
								"so |x| lies in S",
								"|x| ∈ «S»",
								By(sameSize, boundedTerms))
							d.Show(
								"and a point of S is at most the supremum",
								By(bounded, atAbs, real_sup_inf.MemberLessEqSup.At(S, d.TermAs[Real]("|x|"))))
						}))
					outside := b.Have(
						"so beyond the supremum the series diverges",
						"∀x:real. sup(«S») < |x| ⇒ ¬∃s:real. real_sums(λn:num. a(n) * real_pow(x, n), s)",
						By(within, real_order_ring.NotLessEq))
					b.Do(Right())
					b.Take(R)
					b.Show(
						"the second alternative holds at R = sup S",
						By(nonneg, inside, outside))
				})
		}),
})}
