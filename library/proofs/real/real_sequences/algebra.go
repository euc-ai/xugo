// algebra.go — the algebra of limits (README, "The algebra of limits"):
// the constant sequence, then the negative, the sum, the difference, the
// product and the scalar multiple of sequences with limits, and last the
// squeeze read on the distance.
//
// The sum and the product stand on the index two limits share
// (LimitCommonIndex); the difference and the scalar multiple are their
// corollaries, through the negative and the constant, and the squeeze on
// the distance is a corollary of the sum and the difference.

package real_sequences

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// LimitConst — a constant sequence tends to its value.
//
// Any index answers any ε: every term is k itself, at distance
// |k − k| = 0 from k, which is below ε. The index is taken to be 0.
var LimitConst = limitConstThm{family.Add(registry.ProofEntry{
	Name: "LimitConst",
	Key:  "prop_397684d385101977",
	Build: family.Theorem("∀k:real. (λn:num. k) ⟶ k",
		func(arg *Argument, k *Expr[Real]) {
			arg.Do(Unfold(RealConvergesToDef))
			arg.FixAs[Real]()
			pos := arg.Assume()
			arg.Take(arg.TermAs[Nat]("0"))
			arg.FixAs[Nat]()
			arg.Assume()
			arg.Show(
				"every term is k, at distance |k − k| = 0 from k, which is below ε",
				ByArith(pos))
		}),
})}

// LimitNeg — the negative of a sequence tends to the negative of its
// limit.
//
// The same index answers the same ε: |−a(n) − (−l)| = |a(n) − l|, so the
// index past which the terms of a lie within ε of l serves −a and −l.
var LimitNeg = limitNegThm{family.Add(registry.ProofEntry{
	Name: "LimitNeg",
	Key:  "prop_b03bec45cf6a29e5",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l:real.",
		Hypotheses: []string{
			"a ⟶ l",
		},
		Conclusion: "(λn:num. -a(n)) ⟶ -l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l *Expr[Real], limit Fact) {
			near := arg.Unfolded(limit, RealConvergesToDef)
			arg.Do(Unfold(RealConvergesToDef))
			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			N0, tail := arg.Obtain(
				"a ⟶ l at ε hands over an index N₀ past which every term of a is within ε of l",
				"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε",
				By(near.At(eps), pos))
			arg.Take(N0)
			n := arg.FixAs[Nat]()
			past := arg.Assume()
			arg.Show(
				"|−a(n) − (−l)| = |a(n) − l| < ε",
				ByArith(tail.At(n), past))
		}),
})}

// LimitAdd — the sum of two sequences tends to the sum of their limits.
//
// Each limit is given half of ε: past the index the two limits share at
// ε/2, a(n) is within ε/2 of l and b(n) within ε/2 of m, and the triangle
// inequality puts a(n) + b(n) within ε/2 + ε/2 = ε of l + m.
var LimitAdd = limitAddThm{family.Add(registry.ProofEntry{
	Name: "LimitAdd",
	Key:  "prop_48aac6ee660cc07e",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀l m:real.",
		Hypotheses: []string{
			"a ⟶ l",
			"b ⟶ m",
		},
		Conclusion: "(λn:num. a(n) + b(n)) ⟶ l + m",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], l, m *Expr[Real], limits Fact) {
			shared := arg.Have(
				"the two limits share, for every positive ε, one index "+
					"past which a is within ε of l and b within ε of m",
				"∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε ∧ |b(n) - m| < ε",
				By(LimitCommonIndex, limits))
			arg.Do(Unfold(RealConvergesToDef))
			arg.FixAs[Real]()
			pos := arg.Assume()
			half := arg.TermAs[Real]("ε / &2")
			halfPos := arg.Have(
				"half of ε is positive",
				"&0 < ε / &2",
				ByArith(pos))
			N0, tail := arg.Obtain(
				"the shared index at ε/2 is some N₀, past which a is within ε/2 of l and b within ε/2 of m",
				"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε / &2 ∧ |b(n) - m| < ε / &2",
				By(shared.At(half), halfPos))
			arg.Take(N0)
			n := arg.FixAs[Nat]()
			past := arg.Assume()
			near := arg.Have(
				"n lies past N₀, so a(n) is within ε/2 of l and b(n) within ε/2 of m",
				"|a(n) - l| < ε / &2 ∧ |b(n) - m| < ε / &2",
				By(tail.At(n), past))
			arg.Show(
				"|(a(n) + b(n)) − (l + m)| ≤ |a(n) − l| + |b(n) − m| < ε/2 + ε/2 = ε",
				ByArith(near))
		}),
})}

// LimitSub — the difference of two sequences tends to the difference of
// their limits.
//
// a − b is a + (−b): the negative of b tends to −m, so the sum of a and
// −b tends to l + (−m), which is l − m.
var LimitSub = limitSubThm{family.Add(registry.ProofEntry{
	Name: "LimitSub",
	Key:  "prop_5696161676391b7d",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀l m:real.",
		Hypotheses: []string{
			"a ⟶ l",
			"b ⟶ m",
		},
		Conclusion: "(λn:num. a(n) - b(n)) ⟶ l - m",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], l, m *Expr[Real], limits Fact) {
			negB := arg.Have(
				"b tends to m, so its negative tends to −m",
				"(λn:num. -b(n)) ⟶ -m",
				By(LimitNeg, limits))
			// Subtraction is addition of the negation, in the sequence and
			// in the limit alike.
			arg.Do(Simp(Fwd(real_ring.RealSubDef)))
			arg.Show(
				"a tends to l and −b to −m, so a + (−b) tends to l + (−m)",
				By(LimitAdd, limits, negB))
		}),
})}

// LimitMul — the product of two sequences tends to the product of their
// limits.
//
// One tolerance serves both limits. Past an index where a(n) is within η
// of l and b(n) within η of m, the deviation of the product splits into
// three terms, a(n)·b(n) − l·m = (a(n) − l)(b(n) − m) + l(b(n) − m) +
// m(a(n) − l), bounded by η·η, |l|·η and |m|·η; with η ≤ 1 the first is
// below η, so the whole is below η·(|l| + |m| + 1). The tolerance
// η = ε / (ε + |l| + |m| + 1) is positive, at most 1, and makes that
// bound less than ε — so the estimate needs no bound on a beyond the
// tolerance itself.
var LimitMul = limitMulThm{family.Add(registry.ProofEntry{
	Name: "LimitMul",
	Key:  "prop_f01f22e208dbe49a",
	Build: family.Sections(Statement{
		Binders: "∀a b:(num → real). ∀l m:real.",
		Hypotheses: []string{
			"a ⟶ l",
			"b ⟶ m",
		},
		Conclusion: "(λn:num. a(n) * b(n)) ⟶ l * m",
		Abbrev: Abbrev{
			{Name: "tolerance", Text: "ε / (ε + |l| + |m| + &1)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The deviation of a product from a product splits into three
			// terms, each a product with one deviation as a factor. A lemma of
			// its own because it has no premise: a `By` needs one, and the
			// arithmetic closer does not derive the triangle inside the close
			// that also combines the three bounds.
			threeTerms := ctx.Lemma("∀u v l m:real. "+
				"    |u * v - l * m| ≤ |(u - l) * (v - m)| + |l * (v - m)| + |m * (u - l)|",
				func(s *Argument, u, v, l, m *Expr[Real]) {
					s.Show(
						"u·v − l·m = (u − l)(v − m) + l(v − m) + m(u − l), and the "+
							"absolute value of a sum is at most the sum of the absolute values",
						ByArith())
				})
			// The estimate at a tolerance η ≤ 1: the three terms are below
			// η, |l|·η and |m|·η.
			estimate := ctx.Lemma(Statement{
				Binders: "∀u v l m η:real.",
				Hypotheses: []string{
					"&0 < η",
					"η ≤ &1",
					"|u - l| < η",
					"|v - m| < η",
				},
				Conclusion: "|u * v - l * m| < η * (|l| + |m| + &1)",
			},
				func(s *Argument, u, v, l, m, η *Expr[Real], bounds Fact) {
					devU, devV := s.TermAs[Real]("u - l"), s.TermAs[Real]("v - m")
					absDevU, absDevV := s.TermAs[Real]("|u - l|"), s.TermAs[Real]("|v - m|")

					// Stated on its own: the closer reads η·η ≤ η as a goal but does
					// not find it inside the rung that needs it.
					square := s.Have(
						"η is at most 1, so η·η is at most η",
						"η * η ≤ η",
						ByArith(bounds))
					first := s.Have(
						"|(u − l)(v − m)| = |u − l|·|v − m| < η·η ≤ η",
						"|(u - l) * (v - m)| < η",
						ByArith(
							real_order_ring.LessThanMul2.At(absDevU, η, absDevV, η),
							real_sgn_abs.AbsNonneg.At(devU),
							real_sgn_abs.AbsNonneg.At(devV),
							square,
							bounds))
					second := s.Have(
						"|l(v − m)| = |l|·|v − m| ≤ |l|·η",
						"|l * (v - m)| ≤ |l| * η",
						ByArith(real_sgn_abs.AbsNonneg.At(l), bounds))
					third := s.Have(
						"|m(u − l)| = |m|·|u − l| ≤ |m|·η",
						"|m * (u - l)| ≤ |m| * η",
						ByArith(real_sgn_abs.AbsNonneg.At(m), bounds))
					s.Show(
						"the three terms add to less than η + |l|·η + |m|·η = η·(|l| + |m| + 1)",
						ByArith(At(threeTerms, u, v, l, m), first, second, third))
				})

			return ctx.Theorem(headline,
				func(arg *Argument, a, b *Arrow[Nat, Real], l, m *Expr[Real], limits Fact) {
					shared := arg.Have(
						"the two limits share, for every positive ε, one index "+
							"past which a is within ε of l and b within ε of m",
						"∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε ∧ |b(n) - m| < ε",
						By(LimitCommonIndex, limits))
					arg.Do(Unfold(RealConvergesToDef))
					eps := arg.FixAs[Real]()
					pos := arg.Assume()

					denominator := arg.TermAs[Real]("ε + |l| + |m| + &1")
					η := arg.TermAs[Real]("«tolerance»")
					denomPos := arg.Have(
						"ε + |l| + |m| + 1 is positive",
						"&0 < ε + |l| + |m| + &1",
						ByArith(pos))
					ηPos := arg.Have(
						"so the tolerance η, a quotient of two positives, is positive",
						"&0 < «tolerance»",
						ByArith(pos, denomPos))
					ηOne := arg.Have(
						"and at most 1, ε being at most ε + |l| + |m| + 1",
						"«tolerance» ≤ &1",
						ByArith(denomPos))
					ηBound := arg.Have(
						"and η·(|l| + |m| + 1) < η·(ε + |l| + |m| + 1) = ε",
						"«tolerance» * (|l| + |m| + &1) < ε",
						ByArith(field.DivLeftMul.Read(real_field.Field).At(eps, denominator), pos, ηPos))

					N0, tail := arg.Obtain(
						"the shared index at η: past some N₀, a is within η of l and b within η of m",
						"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < «tolerance» ∧ |b(n) - m| < «tolerance»",
						By(shared.At(η), ηPos))
					arg.Take(N0)
					n := arg.FixAs[Nat]()
					past := arg.Assume()
					near := arg.Have(
						"n lies past N₀, so a(n) is within η of l and b(n) within η of m",
						"|a(n) - l| < «tolerance» ∧ |b(n) - m| < «tolerance»",
						By(tail.At(n), past))
					product := arg.Have(
						"the estimate at a(n) and b(n): |a(n)·b(n) − l·m| < η·(|l| + |m| + 1)",
						"|a(n) * b(n) - l * m| < «tolerance» * (|l| + |m| + &1)",
						By(At(estimate, a.Apply(n), b.Apply(n), l, m, η), ηPos, ηOne, near))
					arg.Show(
						"so |a(n)·b(n) − l·m| < η·(|l| + |m| + 1) < ε",
						ByArith(product, ηBound))
				})
		}),
})}

// LimitScale — a scalar multiple of a sequence tends to the scalar
// multiple of its limit.
//
// k·a is the product of the constant sequence k and a: the constant
// tends to k and a to l, so the product tends to k·l.
var LimitScale = limitScaleThm{family.Add(registry.ProofEntry{
	Name: "LimitScale",
	Key:  "prop_6f92ec2d99ef0716",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l k:real.",
		Hypotheses: []string{
			"a ⟶ l",
		},
		Conclusion: "(λn:num. k * a(n)) ⟶ k * l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l, k *Expr[Real], limit Fact) {
			arg.Show(
				"the constant sequence k tends to k and a to l, so their product k·a tends to k·l",
				By(LimitMul, LimitConst.At(k), limit))
		}),
})}

// LimitSqueezeDistance — a sequence within a vanishing distance of a
// convergent sequence has its limit: the squeeze, read on the distance.
//
// |c(n) − p(n)| ≤ g(n) pins c(n) between p(n) − g(n) and p(n) + g(n) at
// every index. By the difference and the sum laws those two sequences
// tend to l − 0 and l + 0, both of which are l, so the squeeze, from
// index 0 on, gives c ⟶ l. The distance is bounded at every index, not
// past some N, because that is the form its consumer, the Cauchy
// product, has in hand; the squeeze reads bounds from an index on, so
// the pinned bounds carry the guard `∀n. 0 ≤ n ⇒`.
var LimitSqueezeDistance = limitSqueezeDistanceThm{family.Add(registry.ProofEntry{
	Name: "LimitSqueezeDistance",
	Key:  "prop_62c6ca7d3c89ddf1",
	Build: family.Theorem(Statement{
		Binders: "∀c p g:(num → real). ∀l:real.",
		Hypotheses: []string{
			"∀n:num. |c(n) - p(n)| ≤ g(n)",
			"g ⟶ &0",
			"p ⟶ l",
		},
		Conclusion: "c ⟶ l",
	},
		func(arg *Argument, c, p, g *Arrow[Nat, Real], l *Expr[Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"c(n) lies within g(n) of p(n) at every index",
				"g tends to 0",
				"and p tends to l")
			within, toZero, toL := parts[0], parts[1], parts[2]

			pinned := arg.Have(
				"so from index 0 on, c(n) is pinned between p(n) − g(n) and p(n) + g(n)",
				"∀n:num. 0 ≤ n ⇒ p(n) - g(n) ≤ c(n) ∧ c(n) ≤ p(n) + g(n)",
				arg.ForEach(func(n *Expr[Nat]) Action { return ByArith(within.At(n)) }))
			zero := arg.TermAs[Real]("&0")
			lower := arg.Have(
				"p − g tends to l − 0, which is l",
				"(λn:num. p(n) - g(n)) ⟶ l",
				By(Normalized, toL, toZero, LimitSub.At(p, g, l, zero), real_ring.SubRightZero.At(l)))
			upper := arg.Have(
				"and p + g tends to l + 0, which is l as well",
				"(λn:num. p(n) + g(n)) ⟶ l",
				By(Normalized, toL, toZero, LimitAdd.At(p, g, l, zero), real_ring.AddRightId.At(l)))
			arg.Show(
				"pinned between two sequences that tend to l, c tends to l",
				By(pinned, lower, upper, LimitSqueeze))
		}),
})}
