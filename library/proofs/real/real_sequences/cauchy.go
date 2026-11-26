// cauchy.go — Cauchy sequences (README, "Cauchy means convergent").
//
// A convergent sequence is Cauchy. A Cauchy sequence is bounded — and so,
// being Cauchy, is a convergent one — converges to any cluster point it
// has, and so to its upper limit; the Cauchy criterion is the
// equivalence.

package real_sequences

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// ConvergentImpCauchy — a convergent sequence is Cauchy.
//
// Given ε > 0, the limit is asked for half of it: it hands over an
// index N past which every term is within ε/2 of l. Two terms past N
// are then within ε of each other, each being within ε/2 of l.
var ConvergentImpCauchy = convergentImpCauchyThm{family.Add(registry.ProofEntry{
	Name: "ConvergentImpCauchy",
	Key:  "prop_554481e8e5ffe7b1",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l:real.",
		Hypotheses: []string{
			"a ⟶ l",
		},
		Conclusion: "real_cauchy(a)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l *Expr[Real], limit Fact) {
			near := arg.Unfolded(limit, RealConvergesToDef)

			// The goal read as its ε-N statement: pairs of terms, and no limit
			// named.
			arg.Do(Unfold(RealCauchyDef))
			arg.FixAs[Real]()
			pos := arg.Assume()
			half := arg.TermAs[Real]("ε / &2")
			halfPos := arg.Have(
				"half of ε is again a positive distance",
				"&0 < ε / &2",
				ByArith(pos))
			N, tail := arg.Obtain(
				"a ⟶ l at ε/2 hands over an index past which every term is within ε/2 of l",
				"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε / &2",
				By(near.At(half), halfPos))

			arg.Take(N)
			m := arg.FixAs[Nat]()
			n := arg.FixAs[Nat]()
			past := arg.Assume()
			arg.Show(
				"two terms past N, each within ε/2 of l, are within ε of each other",
				ByArith(tail.At(m), tail.At(n), past))
		}),
})}

// CauchyBounded — a Cauchy sequence is bounded.
//
// Cauchy at ε = 1 hands over an index N past which any two terms are
// within 1 of each other, so every term past N is within 1 of a(N) and
// its size is at most |a(N)| + 1. The terms up to N are finitely many,
// and a finite stretch of a sequence is bounded: by induction on its
// length, each new term raising the bound to the larger of the old
// bound and its own size. The larger of the two bounds bounds every
// term, since every index is up to N or past it. The bound is read off
// the Cauchy index, which is why the statement asserts it exists.
var CauchyBounded = cauchyBoundedThm{family.Add(registry.ProofEntry{
	Name: "CauchyBounded",
	Key:  "prop_4a1d3f3fddf3c882",
	Build: family.Sections(Statement{
		Binders: "∀a:(num → real).",
		Hypotheses: []string{
			"real_cauchy(a)",
		},
		Conclusion: "∃B:real. ∀n:num. |a(n)| ≤ B",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A finite stretch of a sequence is bounded.
			prefix := ctx.Lemma("∀a:(num → real). ∀N:num. ∃B:real. ∀n:num. n ≤ N ⇒ |a(n)| ≤ B",
				func(arg *Argument, a *Arrow[Nat, Real]) {
					arg.Induct("N")
					arg.Base(
						"N = 0: the one term a(0) is bounded by its own size",
						func(b *Argument) {
							first := b.TermAs[Real]("|a(0)|")
							b.Take(first)
							n := b.FixAs[Nat]()
							upTo := b.Assume()
							zero := b.Have(
								"the one index up to 0 is 0 itself",
								"n = 0",
								By(upTo, nat_order.LessEqZeroClause.At(n)))
							b.Show(
								"so a(n) is a(0), and |a(0)| ≤ |a(0)|",
								zero.Rw(),
								Cite(real_order_ring.LessEqRefl))
						})
					arg.Step(
						"suc N: the larger of the old bound and the size of a(suc N)",
						func(b *Argument, ih Fact) {
							old, bound := b.UnpackAs[Real](ih)
							N := b.TermAs[Nat]("N")
							next := b.TermAs[Real]("|a(suc(N))|")
							b.Take(b.TermAs[Real]("max(B₀, |a(suc(N))|)"))
							n := b.FixAs[Nat]()
							upTo := b.Assume()
							size := b.TermAs[Real]("|a(n)|")
							b.Show(
								"n ≤ suc N puts n up to N, within the old bound, or at suc N itself; either way below the max",
								By(
									bound.At(n),
									upTo,
									nat_order.LessEqSucClause.At(n, N),
									real_sup_inf.LessEqMax.At(old, next, size),
									real_order_ring.LessEqRefl.At(size)))
						})
				})

			return ctx.Theorem(headline,
				func(arg *Argument, a *Arrow[Nat, Real], isCauchy Fact) {
					near := arg.Unfolded(isCauchy, RealCauchyDef)
					N, tail := arg.ObtainAs[Nat](
						"Cauchy at ε = 1 hands over an index past which any two terms are within 1 of each other",
						"∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ |a(m) - a(n)| < &1",
						By(near.At(arg.TermAs[Real]("&1")), real_order_ring.ZeroLessThanOne))
					prefixBound, upToN := arg.UnpackAs[Real](At(prefix, a, N))

					tailBound := arg.TermAs[Real]("|a(N₀)| + &1")
					arg.Take(arg.TermAs[Real]("max(B₀, |a(N₀)| + &1)"))
					n := arg.FixAs[Nat]()
					size := arg.TermAs[Real]("|a(n)|")
					total := arg.Have(
						"every index is up to N or past it",
						"n ≤ N₀ ∨ N₀ ≤ n",
						By(nat_order.LessEqTotal.At(n, N)))
					arg.Do(total.SplitDisj(
						LeftHolds(
							"n up to N: the prefix bound",
							Given(func(b *Argument, upTo Fact) {
								b.Show(
									"|a(n)| ≤ B₀, the first of the two bounds",
									By(upToN.At(n), upTo, real_sup_inf.LessEqMax.At(prefixBound, tailBound, size)))
							})),
						RightHolds(
							"n past N: within 1 of a(N)",
							Given(func(b *Argument, past Fact) {
								within := b.Have(
									"the Cauchy estimate at the pair (n, N)",
									"|a(n) - a(N₀)| < &1",
									By(tail.At(n, N), past, nat_order.LessEqRefl.At(N)))
								below := b.Have(
									"so |a(n)| is at most |a(N)| + 1",
									"|a(n)| ≤ |a(N₀)| + &1",
									ByArith(within))
								b.Show(
									"and |a(N)| + 1 is the second of the two bounds",
									By(below, real_sup_inf.LessEqMax.At(prefixBound, tailBound, size)))
							})),
					))
				})
		}),
})}

// ConvergentBounded — a convergent sequence is bounded.
//
// It is Cauchy, and a Cauchy sequence is bounded.
var ConvergentBounded = convergentBoundedThm{family.Add(registry.ProofEntry{
	Name: "ConvergentBounded",
	Key:  "prop_9c12df168b39ac46",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l:real.",
		Hypotheses: []string{
			"a ⟶ l",
		},
		Conclusion: "∃B:real. ∀n:num. |a(n)| ≤ B",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l *Expr[Real], convergent Fact) {
			arg.Show(
				"converging to l, the sequence is Cauchy, and a Cauchy sequence is bounded",
				By(convergent, ConvergentImpCauchy.At(a, l), CauchyBounded.At(a)))
		}),
})}

// CauchyClusterPointConverges — a Cauchy sequence converges to each of
// its cluster points.
//
// A Cauchy sequence that returns near l infinitely often cannot wander
// off, because its terms stay near each other. For ε > 0, Cauchy at
// ε/2 hands over an index N past which any two terms are within ε/2 of
// each other; the cluster point, asked at ε/2 past N, hands over one
// term a(n), n ≥ N, within ε/2 of l. Every term past N is within ε/2
// of that a(n), hence within ε of l.
var CauchyClusterPointConverges = cauchyClusterPointConvergesThm{family.Add(registry.ProofEntry{
	Name: "CauchyClusterPointConverges",
	Key:  "prop_eb998d8b9c454d59",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l:real.",
		Hypotheses: []string{
			"real_cauchy(a)",
			"real_cluster_point(a, l)",
		},
		Conclusion: "a ⟶ l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l *Expr[Real], isCauchy, clusters Fact) {
			cauchy := arg.Unfolded(isCauchy, RealCauchyDef)
			cluster := arg.Unfolded(clusters, RealClusterPointDef)

			arg.Do(Unfold(RealConvergesToDef))
			arg.FixAs[Real]()
			pos := arg.Assume()
			half := arg.TermAs[Real]("ε / &2")
			halfPos := arg.Have(
				"half of ε is positive too",
				"&0 < ε / &2",
				ByArith(pos))

			N0, together := arg.Obtain(
				"Cauchy at ε/2: past some index N any two terms lie within ε/2 of each other",
				"∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ |a(m) - a(n)| < ε / &2",
				By(cauchy.At(half), halfPos))
			n0, returned := arg.Obtain(
				"the cluster point asked at ε/2 past N: some term a(n), n ≥ N, lies within ε/2 of l",
				"∃n:num. N₀ ≤ n ∧ |a(n) - l| < ε / &2",
				By(cluster.At(half), halfPos))

			arg.Take(N0)
			m := arg.FixAs[Nat]("m")
			past := arg.Assume()
			arg.Show(
				"|a(m) − l| ≤ |a(m) − a(n)| + |a(n) − l| < ε/2 + ε/2 = ε",
				ByArith(together.At(m, n0), past, returned))
		}),
})}

// CauchyConverges — a Cauchy sequence converges, and its limit is its
// upper limit, real_limsup(a).
//
// A Cauchy sequence is bounded, so its upper limit is a cluster point
// of it — Bolzano–Weierstrass, by the upper limit. And a Cauchy
// sequence converges to each of its cluster points. The limit is
// named, as the monotone theorems name theirs; that some limit exists
// is the classical sentence read off it.
var CauchyConverges = cauchyConvergesThm{family.Add(registry.ProofEntry{
	Name: "CauchyConverges",
	Key:  "prop_6b09c50380082ac5",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real).",
		Hypotheses: []string{
			"real_cauchy(a)",
		},
		Conclusion: "a ⟶ real_limsup(a)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], isCauchy Fact) {
			B0, bounded := arg.ObtainAs[Real](
				"a Cauchy sequence is bounded: some B bounds every term in size",
				"∃B:real. ∀n:num. |a(n)| ≤ B",
				By(isCauchy, CauchyBounded.At(a)))
			upperLimit := arg.TermAs[Real]("real_limsup(a)")
			arg.Show(
				"so its upper limit is a cluster point of it, and a "+
					"Cauchy sequence converges to each of its cluster points",
				By(isCauchy, bounded, BoundedClusterPoint.At(a, B0), CauchyClusterPointConverges.At(a, upperLimit)))
		}),
})}

// CauchyIffConvergent — the Cauchy criterion: a sequence is Cauchy
// exactly when it converges.
//
// Forward the limit is exhibited: the upper limit, to which a Cauchy
// sequence converges. Backward whichever limit the sequence has serves.
var CauchyIffConvergent = cauchyIffConvergentThm{family.Add(registry.ProofEntry{
	Name: "CauchyIffConvergent",
	Key:  "prop_eda450e4f5736593",
	Build: family.Theorem("∀a:(num → real). real_cauchy(a) ⇔ ∃l:real. a ⟶ l",
		func(arg *Argument, a *Arrow[Nat, Real]) {
			arg.Iff()
			arg.Forward(
				"a Cauchy sequence has a limit: its upper limit",
				func(b *Argument, isCauchy Fact) {
					b.Take(b.TermAs[Real]("real_limsup(a)"))
					b.Show(
						"a Cauchy sequence converges to the infimum of its tail suprema",
						By(isCauchy, CauchyConverges.At(a)))
				})
			arg.Backward(
				"a sequence with a limit is Cauchy",
				func(b *Argument, convergent Fact) {
					l0, toL := b.UnpackAs[Real](convergent)
					b.Show(
						"convergence to that l makes the sequence Cauchy",
						By(toL, ConvergentImpCauchy.At(a, l0)))
				})
		}),
})}
