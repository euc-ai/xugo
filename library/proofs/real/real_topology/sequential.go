// sequential.go — closedness and compactness read along sequences: a
// closed set keeps the limits of its sequences, and a compact set holds a
// limit of a subsequence of each of its sequences.

package real_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Closed sets keep their limits
// ---------------------------------------------------------------------------

// ClosedIffSequential — a set of reals is closed exactly when it holds
// the limit of every convergent sequence of its points.
//
// A closed set gives each real outside it a radius missing it
// (ClosedIff). If a sequence of points of s tended to a limit l outside
// s, a radius δ about l would miss s; the
// limit, asked for δ, hands over an index N past which the terms are
// within δ of l, so a(N) misses s — and it is a point of s.
//
// Conversely, take x outside s and suppose no radius about x misses s:
// every ball about x meets s. The ball of radius 1/(n + 1) holds a point
// of s for each n, and choosing one for each n is a sequence of points of
// s tending to x, its n-th term within 1/(n + 1) of x. So x is in s by
// the hypothesis, though it lies outside.
var ClosedIffSequential = closedIffSequentialThm{family.Add(registry.ProofEntry{
	Name: "ClosedIffSequential",
	Key:  "prop_fb50123f60f64a9e",
	Build: family.Sections("∀s:set(real). "+
		"    closed_in(real_topology, s) ⇔ ∀a:(num → real). ∀l:real. (∀n:num. a(n) ∈ s) ∧ a ⟶ l ⇒ l ∈ s",
		func(ctx *Script, headline string) *GoalStackNode {
			// One point of s chosen in each ball of radius 1/(n + 1) about x
			// is a sequence tending to x.
			approachingSequence := ctx.Lemma(Statement{
				Binders: "∀s:set(real). ∀x:real.",
				Hypotheses: []string{
					"∀δ:real. &0 < δ ⇒ ∃y:real. |y - x| < δ ∧ y ∈ s",
				},
				Conclusion: "∃a:(num → real). (∀n:num. a(n) ∈ s) ∧ a ⟶ x",
			},
				func(arg *Argument, s *Expr[Set[Real]], x *Expr[Real], everyBall Fact) {
					pointPerIndex := arg.Have(
						"for each n the ball of radius 1/(n + 1) about x holds a point of s",
						"∀n:num. ∃y:real. |y - x| < real_inv(&n + &1) ∧ y ∈ s",
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							positive := b.Have(
								"1/(n + 1) is a positive radius, n + 1 being positive",
								"&0 < real_inv(&n + &1)",
								ByArith(real_order_field.InvPos.At(b.TermAs[Real]("&n + &1"))))
							b.Show(
								"so the ball of that radius meets s",
								By(everyBall.At(b.TermAs[Real]("real_inv(&n + &1)")), positive))
						}))
					a0, points := arg.ObtainAs[Fun[Nat, Real]](
						"choosing one such point for each n is a sequence a₀",
						"∃a:(num → real). ∀n:num. |a(n) - x| < real_inv(&n + &1) ∧ a(n) ∈ s",
						By(pointPerIndex))
					arg.Take(a0)
					arg.Do(SplitConj(
						Case(
							"every term of a₀ is a point of s",
							By(points)),
						Case(
							"and a₀ ⟶ x, its n-th term lying within 1/(n + 1) of x",
							By(real_sequences.WithinReciprocalConverges, points)),
					))
				})

			return ctx.Theorem(headline,
				func(arg *Argument, s *Expr[Set[Real]]) {
					arg.Iff()

					arg.Forward(
						"a limit outside s has a ball about it missing s, and the tail of the sequence enters that ball",
						func(b *Argument, closed Fact) {
							missing := b.Have(
								"s is closed: a real outside it has a radius missing it",
								"∀x:real. x ∉ s ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∉ s",
								Simp(Rev(ClosedIff)),
								By(closed))
							b.FixAs[Fun[Nat, Real]]() // the sequence a, named by the statement for the claim texts
							l := b.FixAs[Real]()
							given := b.Conjuncts(
								b.Assume(),
								"every term of a is a point of s",
								"a ⟶ l")
							outside := b.SupposeNot()

							d, radius := b.ObtainAs[Real](
								"so a radius δ about l misses s",
								"∃δ:real. &0 < δ ∧ ∀y:real. |y - l| < δ ⇒ y ∉ s",
								By(missing.At(l), outside))
							ball := b.Conjuncts(
								radius,
								"δ is positive",
								"the reals within δ of l lie outside s")
							approach := b.Unfolded(given[1], real_sequences.RealConvergesToDef)
							N0, tail := b.ObtainAs[Nat](
								"a ⟶ l, asked for δ as its ε, hands over an index N past which the terms are within δ of l",
								"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < δ",
								By(approach.At(d), ball[0]))
							near := b.Have(
								"a(N) itself is within δ of l",
								"|a(N) - l| < δ",
								By(tail.At(N0), nat_order.LessEqRefl.At(N0)))
							b.Show(
								"so a(N) lies outside s, though every term is a point of s",
								By(ball[1].At(b.TermAs[Real]("a(N)")), near, given[0].At(N0)))
						})

					arg.Backward(
						"a point outside s has a ball about it missing s, "+
							"or points of s closing in on it would put it in s",
						func(b *Argument, keepsLimits Fact) {
							// Closedness read by radii: each real outside s has one
							// missing s.
							b.Do(Simp(Fwd(ClosedIff)))
							x := b.FixAs[Real]()
							outside := b.Assume()
							noRadius := b.SupposeNot()
							everyBall := b.Have(
								"then every ball about x meets s",
								"∀δ:real. &0 < δ ⇒ ∃y:real. |y - x| < δ ∧ y ∈ s",
								By(Normalized, noRadius))
							a0, sequence := b.ObtainAs[Fun[Nat, Real]](
								"so a sequence a₀ of points of s tends to x",
								"∃a:(num → real). (∀n:num. a(n) ∈ s) ∧ a ⟶ x",
								By(At(approachingSequence, s, x), everyBall))
							inS := b.Have(
								"s keeps the limit of a₀, so x lies in s",
								"x ∈ s",
								By(keepsLimits.At(a0, x), sequence))
							b.Show(
								"yet x lies outside s",
								By(outside, inS))
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// Compact sets hold a limit of every sequence
// ---------------------------------------------------------------------------

// CompactSubsequence — a sequence of points of a compact set of reals has
// a subsequence converging to a point of the set. The set is bounded, so
// Bolzano–Weierstrass gives a convergent subsequence; it is closed, the
// line being Hausdorff, so it keeps the limit of that subsequence, whose
// terms are terms of the sequence and lie in it.
var CompactSubsequence = compactSubsequenceThm{family.Add(registry.ProofEntry{
	Name: "CompactSubsequence",
	Key:  "prop_ddc7935dc3355ccf",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(real). ∀a:(num → real).",
		Hypotheses: []string{
			"compact_in(real_topology, k)",
			"∀n:num. a(n) ∈ k",
		},
		Conclusion: "∃σ:(num → num). ∃l:real. (∀j:num. σ(j) < σ(j + 1)) ∧ a ∘ σ ⟶ l ∧ l ∈ k",
	},
		func(arg *Argument, k *Expr[Set[Real]], a *Arrow[Nat, Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"k is compact",
				"every term lies in k")
			bound, size := arg.ObtainAs[Real](
				"a compact set is bounded: some B bounds the size of its points",
				"∃B:real. ∀x:real. x ∈ k ⇒ |x| ≤ B",
				By(CompactBounded.At(k), parts[0]))
			bounded := arg.Have(
				"so every term has size at most B",
				"∀n:num. |a(n)| ≤ B",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					b.Show(
						"a(n) is a point of k",
						By(size.At(a.Apply(n)), parts[1].At(n)))
				}))
			sigma, limit, found := arg.Obtain2As[Fun[Nat, Nat], Real](
				"Bolzano–Weierstrass: a bounded sequence has a subsequence a ∘ σ tending to some l",
				"∃σ:(num → num). ∃l:real. (∀j:num. σ(j) < σ(j + 1)) ∧ a ∘ σ ⟶ l",
				By(real_sequences.BolzanoWeierstrass.At(a, bound), bounded))
			closed := arg.Have(
				"the line is Hausdorff, so the compact set k is closed",
				"closed_in(real_topology, k)",
				By(parts[0], compact.CompactClosed.Read(RealTopology).At(k), RealHausdorff))
			keepsLimits := arg.Have(
				"a closed set keeps the limits of its sequences",
				"∀b:(num → real). ∀m:real. (∀n:num. b(n) ∈ k) ∧ b ⟶ m ⇒ m ∈ k",
				Simp(Rev(ClosedIffSequential)),
				By(closed))
			inK := arg.Have(
				"the terms of a ∘ σ are terms of a, so they lie in k",
				"∀n:num. (a ∘ σ)(n) ∈ k",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					b.Show(
						"(a ∘ σ)(n) is a(σ(n))",
						Unfold(functions.ComposeApply),
						By(parts[1]))
				}))
			held := arg.Conjuncts(
				found,
				"σ rises strictly",
				"a ∘ σ ⟶ l")
			limitIn := arg.Have(
				"so k keeps the limit l of the subsequence",
				"l ∈ k",
				By(keepsLimits.At(arg.TermAs[Fun[Nat, Real]]("a ∘ σ"), limit), inK, held[1]))
			arg.Take(sigma)
			arg.Take(limit)
			arg.Show(
				"σ rises strictly, a ∘ σ tends to l, and l lies in k",
				By(held[0], held[1], limitIn))
		}),
})}
