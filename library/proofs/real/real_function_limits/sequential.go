// sequential.go — the sequential characterization (README, "The
// sequential characterization"): the chapter read against
// real_sequences, a function limit followed along the sequences that
// tend to the point, in both directions — from the function limit to
// the sequences, and back. The Argument receiver is `arg`, because the
// statements bind the sequence as `a`; a bare `a ⟶ c` is real_sequences'
// sequence limit, and `o` is the constant behind `∘`.

package real_function_limits

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// LimitAtImpSequential — a function limit carries every sequence that
// tends to the point without touching it to a sequence tending to the
// limit.
//
// Fix ε > 0. The function limit answers ε with a radius δ₀, inside whose
// punctured ball the values of f are within ε of l; the sequence limit,
// asked for δ₀ as its ε, answers with an index N₀ past which the terms
// are within δ₀ of c. Past N₀ a term is within δ₀ of c and, never being
// c, at a positive distance from it — a point of the punctured ball — so
// f carries it within ε of l.
var LimitAtImpSequential = limitAtImpSequentialThm{family.Add(registry.ProofEntry{
	Name: "LimitAtImpSequential",
	Key:  "prop_e68b287c2a246de5",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l:real. ∀a:(num → real).",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"∀n:num. a(n) ≠ c",
			"a ⟶ c",
		},
		Conclusion: "f ∘ a ⟶ l",
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			c, l *Expr[Real],
			a *Arrow[Nat, Real],
			toL, avoid, toC Fact,
		) {
			// The two limits, read before the goal is unfolded, by the first
			// engine fact of definitions.go's header.
			near := arg.Unfolded(toL, RealLimitAtDef)
			approach := arg.Unfolded(toC, real_sequences.RealConvergesToDef)

			// The goal read as its ε-N statement, and `o` unfolded so that the
			// terms of f ∘ a are the values f(a(n)).
			arg.Do(Unfold(real_sequences.RealConvergesToDef), Unfold(functions.ComposeApply))
			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			d0, radius := arg.Obtain(
				"f ⟶ l (at c) at ε hands over a radius δ₀ inside which the values of f are within ε of l",
				"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε",
				By(near.At(eps), pos))
			within := arg.Have(
				"on the punctured ball of radius δ₀ the values of f are within ε of l",
				"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - l| < ε",
				By(radius))
			N0, tail := arg.Obtain(
				"a ⟶ c, asked for the positive radius δ₀ as its ε, hands "+
					"over an index N₀ past which the terms are within δ₀ of c",
				"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - c| < δ₀",
				By(approach.At(d0), radius))

			arg.Take(N0)
			n := arg.FixAs[Nat]()
			past := arg.Assume()
			point := a.Apply(n)
			inBall := arg.Have(
				"a(n) ≠ c makes a(n) − c nonzero, so |a(n) − c| is positive, "+
					"and past N₀ it is below δ₀: a(n) lies in the punctured ball",
				"&0 < |a(n) - c| ∧ |a(n) - c| < δ₀",
				By(
					real_sgn_abs.AbsPosIffNonzero.At(arg.TermAs[Real]("a(n) - c")),
					real_ring.SubEqZero.At(point, c),
					avoid.At(n),
					tail.At(n),
					past))
			arg.Show(
				"so f carries a(n) within ε of l",
				By(within.At(point), inBall))
		}),
})}

// SequentialImpLimitAt — a function that carries every sequence tending
// to c without touching it to a sequence tending to l tends to l at c.
// By contradiction: an ε the function limit fails at picks out, ball by
// ball, a sequence that f carries nowhere near l.
//
// Suppose not. Then some ε > 0 is answered by no radius: every punctured
// ball around c holds a point where f is not within ε of l. The ball of
// radius 1/(n + 1) holds one for each n, and choosing one for each n is a
// sequence that never touches c and tends to it, its n-th term being
// within 1/(n + 1) of c. The hypothesis carries it to a sequence of
// values tending to l, so past some index those values are within ε of
// l — and at that index the value is not.
var SequentialImpLimitAt = sequentialImpLimitAtThm{family.Add(registry.ProofEntry{
	Name: "SequentialImpLimitAt",
	Key:  "prop_52d894245b7ae389",
	Build: family.Sections(Statement{
		Binders: "∀f:(real → real). ∀c l:real.",
		Hypotheses: []string{
			"∀a:(num → real). (∀n:num. a(n) ≠ c) ∧ a ⟶ c ⇒ f ∘ a ⟶ l",
		},
		Conclusion: "f ⟶ l (at c)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The ε the definition fails at, then one bad point in each ball of
			// radius 1/(n + 1).
			badSequence := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀c l:real.",
				Hypotheses: []string{
					"¬(f ⟶ l (at c))",
				},
				Conclusion: "∃ε:real. " +
					"    &0 < ε ∧ " +
					"    (∃a:(num → real). ∀n:num. " +
					"        &0 < |a(n) - c| ∧ |a(n) - c| < real_inv(&n + &1) ∧ ¬(|f(a(n)) - l| < ε))",
			},
				func(arg *Argument, f *Arrow[Real, Real], c, l *Expr[Real], notLimit Fact) {
					fails := arg.Unfolded(notLimit, RealLimitAtDef)
					eps, failing := arg.Obtain(
						"f ⟶ l (at c) failing, some ε > 0 is answered by no radius: every "+
							"punctured ball around c holds a point where f is not within ε of l",
						"∃ε:real. &0 < ε ∧ ∀δ:real. &0 < δ ⇒ ∃x:real. (&0 < |x - c| ∧ |x - c| < δ) ∧ ¬(|f(x) - l| < ε)",
						By(fails))
					everyBall := arg.Have(
						"every punctured ball around c holds such a point",
						"∀δ:real. &0 < δ ⇒ ∃x:real. &0 < |x - c| ∧ |x - c| < δ ∧ ¬(|f(x) - l| < ε₀)",
						By(failing))
					pointPerIndex := arg.Have(
						"for each n the ball of radius 1/(n + 1) holds one",
						"∀n:num. ∃x:real. (&0 < |x - c| ∧ |x - c| < real_inv(&n + &1)) ∧ ¬(|f(x) - l| < ε₀)",
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							positive := b.Have(
								"1/(n + 1) is a positive radius, n + 1 being positive",
								"&0 < real_inv(&n + &1)",
								ByArith(real_order_field.InvPos.At(b.TermAs[Real]("&n + &1"))))
							b.Show(
								"so the punctured ball of that radius holds a point where f is not within ε of l",
								By(everyBall.At(b.TermAs[Real]("real_inv(&n + &1)")), positive))
						}))
					chosen := arg.Have(
						"choosing one point for each n is a sequence",
						"∃a:(num → real). ∀n:num. "+
							"    (&0 < |a(n) - c| ∧ |a(n) - c| < real_inv(&n + &1)) ∧ ¬(|f(a(n)) - l| < ε₀)",
						By(pointPerIndex))
					arg.Take(eps)
					arg.Show(
						"ε is positive, and that sequence is the one asked for",
						By(failing, chosen))
				})

			return ctx.Theorem(headline,
				func(arg *Argument, f *Arrow[Real, Real], c, l *Expr[Real], sequential Fact) {
					notLimit := arg.SupposeNot()
					eps, badEps := arg.Obtain(
						"then some ε > 0 has a sequence closing in on c at whose terms f is not within ε of l",
						"∃ε:real. "+
							"    &0 < ε ∧ "+
							"    ∃a:(num → real). ∀n:num. "+
							"        (&0 < |a(n) - c| ∧ |a(n) - c| < real_inv(&n + &1)) ∧ ¬(|f(a(n)) - l| < ε)",
						By(At(badSequence, f, c, l), notLimit))
					a0, badPoint := arg.Obtain(
						"call that sequence a₀",
						"∃a:(num → real). ∀n:num. "+
							"    (&0 < |a(n) - c| ∧ |a(n) - c| < real_inv(&n + &1)) ∧ ¬(|f(a(n)) - l| < ε₀)",
						By(badEps))

					avoid := arg.Have(
						"no term of a₀ is c: each lies at a positive distance from it",
						"∀n:num. a₀(n) ≠ c",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]()
							b.Show(
								"|a₀(n) − c| is positive, so a₀(n) − c is nonzero",
								By(
									badPoint.At(n),
									real_sgn_abs.AbsPosIffNonzero.At(b.TermAs[Real]("a₀(n) - c")),
									real_ring.SubEqZero.At(b.TermAs[Real]("a₀(n)"), c)))
						}))
					tends := arg.Have(
						"a₀ ⟶ c, its n-th term lying within 1/(n + 1) of c",
						"a₀ ⟶ c",
						By(real_sequences.WithinReciprocalConverges, badPoint))
					carried := arg.Have(
						"so f carries a₀ to a sequence tending to l",
						"f ∘ a₀ ⟶ l",
						By(sequential.At(a0), avoid, tends))

					// That limit read as its ε-N statement, `o` unfolded so that the
					// terms of f ∘ a₀ are the values f(a₀(n)).
					valuesApproach := arg.Unfolded(
						arg.Unfolded(carried, real_sequences.RealConvergesToDef), functions.ComposeApply)
					N0, tail := arg.ObtainAs[Nat](
						"asked for ε₀, it hands over an index N₀ past which the values are within ε₀ of l",
						"∃N:num. ∀n:num. N ≤ n ⇒ |f(a₀(n)) - l| < ε₀",
						By(valuesApproach.At(eps), badEps))
					arg.Show(
						"at N₀ itself the value f(a₀(N₀)) is within ε₀ of l, and it is not",
						By(tail.At(N0), badPoint.At(N0), nat_order.LessEqRefl.At(N0)))
				})
		}),
})}
