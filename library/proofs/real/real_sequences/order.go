// order.go — two limits past one index, and what it settles: limits keep
// order, a limit is one number, and the squeeze (README, "Two limits past
// one index: order, uniqueness and the squeeze"); and, read the other
// way, a level below the limit is cleared by the late terms by a fixed
// step.
//
// A limit speaks only of the terms past an index, and two limits share,
// for every ε, one index past which both hold. So an inequality between
// two sequences that holds past a given index N carries over to their
// limits; read against a constant sequence, a bound every term keeps is
// kept by the limit, and read for a sequence against itself, both ways,
// that is uniqueness. And a sequence pinned past N between two with one
// limit has that limit; so has one that agrees past N with a convergent
// sequence.
//
// Read from index 0 on, LimitLessEq and LimitSqueeze ask for their fact
// under the guard `0 ≤ n ⇒`: a fact about every index supplies that as
// it stands, with the guard or without.

package real_sequences

import (
	. "github.com/euc-ai/xugo/library/authoring"

	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// LimitCommonIndex — two limits share, for every ε, one index past which
// both sequences are within ε of their limits.
//
// Each limit answers ε with an index of its own. Their sum is past both,
// so an index past the sum is past each of them — and there a(n) is within
// ε of l and b(n) within ε of m.
var LimitCommonIndex = limitCommonIndexThm{family.Add(registry.ProofEntry{
	Name: "LimitCommonIndex",
	Key:  "prop_b5bc84fc3b55d552",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀l m ε:real.",
		Hypotheses: []string{
			"a ⟶ l",
			"b ⟶ m",
			"&0 < ε",
		},
		Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε ∧ |b(n) - m| < ε",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], l, m *Expr[Real], toL, toM Fact) {
			nearL := arg.Unfolded(toL, RealConvergesToDef)
			nearM := arg.Unfolded(toM, RealConvergesToDef)

			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			_, tailL := arg.Obtain(
				"a ⟶ l at ε hands over an index N₁ past which the terms of a are within ε of l",
				"∃N₁:num. ∀n:num. N₁ ≤ n ⇒ |a(n) - l| < ε",
				By(nearL.At(eps), pos))
			_, tailM := arg.Obtain(
				"and b ⟶ m at ε an index N₂ past which the terms of b are within ε of m",
				"∃N₂:num. ∀n:num. N₂ ≤ n ⇒ |b(n) - m| < ε",
				By(nearM.At(eps), pos))
			index := arg.TermAs[Nat]("N₁ + N₂")

			arg.Take(index)
			n := arg.FixAs[Nat]()
			pastBoth := arg.Assume()
			pastN1 := arg.Have(
				"n is past N₁, which N₁ + N₂ is past",
				"N₁ ≤ n",
				ByArith(pastBoth))
			pastN2 := arg.Have(
				"and past N₂, which N₁ + N₂ is past too",
				"N₂ ≤ n",
				ByArith(pastBoth))
			arg.Show(
				"so a(n) is within ε of l and b(n) within ε of m",
				By(tailL.At(n), tailM.At(n), pastN1, pastN2))
		}),
})}

// LimitLessEq — limits keep order.
//
// Were m < l, let ε = (l − m)/2, which is positive. The two limits share
// one index N₁ past which every a(n) is within ε of l and every b(n)
// within ε of m. At n = N + N₁, past N and N₁ at once, then, a(n) ≤ b(n),
// while a(n) lies above l − ε and b(n) below m + ε — and those two bounds
// are the same number, the midpoint of l and m, so the terms would cross.
var LimitLessEq = limitLessEqThm{family.Add(registry.ProofEntry{
	Name: "LimitLessEq",
	Key:  "prop_441cdac46859b7a9",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀l m:real. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. N ≤ n ⇒ a(n) ≤ b(n)",
			"a ⟶ l",
			"b ⟶ m",
		},
		Conclusion: "l ≤ m",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], l, m *Expr[Real], N *Expr[Nat], given Fact) {
			reversed := arg.SupposeNot()
			eps := arg.TermAs[Real]("(l - m) / &2")
			pos := arg.Have(
				"half the gap is a positive ε",
				"&0 < (l - m) / &2",
				ByArith(reversed))

			dominated := arg.Have(
				"past N the terms of a lie below those of b",
				"∀n:num. N ≤ n ⇒ a(n) ≤ b(n)",
				By(given))
			limits := arg.Have(
				"and a ⟶ l while b ⟶ m",
				"a ⟶ l ∧ b ⟶ m",
				By(given))
			N1, tail := arg.ObtainAs[Nat](
				"the two limits answer ε with one index N₁, past "+
					"which a(n) is within ε of l and b(n) within ε of m",
				"∃N₁:num. ∀n:num. N₁ ≤ n ⇒ |a(n) - l| < (l - m) / &2 ∧ |b(n) - m| < (l - m) / &2",
				By(LimitCommonIndex.At(a, b, l, m, eps), limits, pos))

			index := arg.TermAs[Nat]("N + N₁")
			pastN := arg.Have(
				"the index N + N₁ is past N",
				"N ≤ N + N₁",
				Cite(nat_order.LessEqAdd, N, N1))
			pastN1 := arg.Have(
				"and past N₁",
				"N₁ ≤ N + N₁",
				Cite(nat_order.LessEqAddLeft, N, N1))

			ordered := arg.Have(
				"the index is past N, so there a(n) ≤ b(n)",
				"a(N + N₁) ≤ b(N + N₁)",
				By(dominated.At(index), pastN))
			near := arg.Have(
				"and past N₁, so there a(n) is within ε of l and b(n) within ε of m",
				"|a(N + N₁) - l| < (l - m) / &2 ∧ |b(N + N₁) - m| < (l - m) / &2",
				By(tail.At(index), pastN1))

			arg.Show(
				"yet there a(n) lies above l − ε and b(n) below m + ε, "+
					"and those are the same number, the midpoint of l and m",
				ByArith(ordered, near))
		}),
})}

// LimitLessEqBound — a bound above that every term of a convergent
// sequence keeps, its limit keeps too: the sequence lies below the
// constant sequence at M, which tends to M, and limits keep order.
var LimitLessEqBound = limitLessEqBoundThm{family.Add(registry.ProofEntry{
	Name: "LimitLessEqBound",
	Key:  "prop_e90093e73f5011ed",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l M:real.",
		Hypotheses: []string{
			"a ⟶ l",
			"∀n:num. a(n) ≤ M",
		},
		Conclusion: "l ≤ M",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l, M *Expr[Real], converges, bounded Fact) {
			constant := arg.TermAs[Fun[Nat, Real]]("λn:num. M")
			arg.Show(
				"a lies below the constant sequence at M, which tends to M, and limits keep order",
				By(bounded, converges, LimitConst.At(M), LimitLessEq.At(a, constant, l, M, arg.TermAs[Nat]("0"))))
		}),
})}

// BoundLessEqLimit — a bound below that every term of a convergent
// sequence keeps, its limit keeps too: the constant sequence at M lies
// below the sequence and tends to M, and limits keep order.
var BoundLessEqLimit = boundLessEqLimitThm{family.Add(registry.ProofEntry{
	Name: "BoundLessEqLimit",
	Key:  "prop_2390c61bdd64d3ee",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l M:real.",
		Hypotheses: []string{
			"a ⟶ l",
			"∀n:num. M ≤ a(n)",
		},
		Conclusion: "M ≤ l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l, M *Expr[Real], converges, bounded Fact) {
			constant := arg.TermAs[Fun[Nat, Real]]("λn:num. M")
			arg.Show(
				"the constant sequence at M lies below a and tends to M, and limits keep order",
				By(bounded, converges, LimitConst.At(M), LimitLessEq.At(constant, a, M, l, arg.TermAs[Nat]("0"))))
		}),
})}

// LimitUnique — a sequence has at most one limit.
//
// Limits keep order, and a sequence lies below itself at every index; so
// each of two limits of one sequence is at most the other, and they are
// equal.
var LimitUnique = limitUniqueThm{family.Add(registry.ProofEntry{
	Name: "LimitUnique",
	Key:  "prop_4418e8e871686066",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l m:real.",
		Hypotheses: []string{
			"a ⟶ l",
			"a ⟶ m",
		},
		Conclusion: "l = m",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l, m *Expr[Real], toL, toM Fact) {
			self := arg.Have(
				"a sequence lies below itself at every index",
				"∀n:num. 0 ≤ n ⇒ a(n) ≤ a(n)",
				Derive(func(g *Argument) {
					n := g.FixAs[Nat]()
					g.Assume()
					g.Show(
						"a(n) ≤ a(n)",
						By(real_order_ring.LessEqRefl.At(a.Apply(n))))
				}))
			start := arg.TermAs[Nat]("0")
			below := arg.Have(
				"so l ≤ m, limits keeping order",
				"l ≤ m",
				By(self, toL, toM, LimitLessEq.At(a, a, l, m, start)))
			above := arg.Have(
				"and m ≤ l, read the other way",
				"m ≤ l",
				By(self, toM, toL, LimitLessEq.At(a, a, m, l, start)))
			arg.Show(
				"each limit is at most the other, so they are equal",
				By(below, above, real_construction.LessEqAntisym.At(l, m)))
		}),
})}

// LimitSqueeze — a sequence pinned, past some index, between two
// sequences with one limit has that limit.
//
// Fix ε > 0. The two outer limits share an index N₁ past which a(n) and
// c(n) are both within ε of l. Past N + N₁ — past N, where b is pinned
// between a and c, and past N₁ — then l − ε < a(n) ≤ b(n) ≤ c(n) < l + ε,
// so b(n) is within ε of l as well.
var LimitSqueeze = limitSqueezeThm{family.Add(registry.ProofEntry{
	Name: "LimitSqueeze",
	Key:  "prop_f3aacc690613132f",
	Build: family.Theorem(Statement{
		Binders: "∀a b c:(num → real). ∀l:real. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. N ≤ n ⇒ a(n) ≤ b(n) ∧ b(n) ≤ c(n)",
			"a ⟶ l",
			"c ⟶ l",
		},
		Conclusion: "b ⟶ l",
	},
		func(arg *Argument, a, b, c *Arrow[Nat, Real], l *Expr[Real], N *Expr[Nat], given Fact) {
			shared := arg.Have(
				"the two outer limits share, for every positive ε, "+
					"one index past which a and c are both within ε of l",
				"∀ε:real. &0 < ε ⇒ ∃N₁:num. ∀n:num. N₁ ≤ n ⇒ |a(n) - l| < ε ∧ |c(n) - l| < ε",
				By(LimitCommonIndex, given))
			pinned := arg.Have(
				"past N, b is pinned between a and c",
				"∀n:num. N ≤ n ⇒ a(n) ≤ b(n) ∧ b(n) ≤ c(n)",
				By(given))
			arg.Do(Unfold(RealConvergesToDef))
			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			_, tail := arg.Obtain(
				"the shared index at ε: some N₁ past which a and c are both within ε of l",
				"∃N₁:num. ∀n:num. N₁ ≤ n ⇒ |a(n) - l| < ε ∧ |c(n) - l| < ε",
				By(shared.At(eps), pos))
			index := arg.TermAs[Nat]("N + N₁")

			arg.Take(index)
			n := arg.FixAs[Nat]()
			pastBoth := arg.Assume()
			pastN := arg.Have(
				"n is past N, which N + N₁ is past",
				"N ≤ n",
				ByArith(pastBoth))
			pastN1 := arg.Have(
				"and past N₁, which N + N₁ is past too",
				"N₁ ≤ n",
				ByArith(pastBoth))
			sandwiched := arg.Have(
				"past N, a(n) ≤ b(n) ≤ c(n)",
				"a(n) ≤ b(n) ∧ b(n) ≤ c(n)",
				By(pinned.At(n), pastN))
			near := arg.Have(
				"and past N₁, a(n) and c(n) are both within ε of l",
				"|a(n) - l| < ε ∧ |c(n) - l| < ε",
				By(tail.At(n), pastN1))
			arg.Show(
				"l − ε < a(n) ≤ b(n) ≤ c(n) < l + ε, so b(n) is within ε of l",
				ByArith(sandwiched, near))
		}),
})}

// LimitEventuallyEqual — a sequence that agrees with a convergent one from
// some index on has its limit: from that index on it is pinned between the
// convergent sequence and itself, and LimitSqueeze above applies.
var LimitEventuallyEqual = limitEventuallyEqualThm{family.Add(registry.ProofEntry{
	Name: "LimitEventuallyEqual",
	Key:  "prop_fc85f1b6879d6a0d",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀l:real. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. N ≤ n ⇒ a(n) = b(n)",
			"a ⟶ l",
		},
		Conclusion: "b ⟶ l",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], l *Expr[Real], N *Expr[Nat], agree, limit Fact) {
			between := arg.Have(
				"from N on, b(n) lies between a(n) and a(n)",
				"∀n:num. N ≤ n ⇒ a(n) ≤ b(n) ∧ b(n) ≤ a(n)",
				ByArith(agree))
			arg.Show(
				"so b is squeezed between a and itself",
				By(between, limit, LimitSqueeze.At(a, b, a, l, N)))
		}),
})}

// LimitAboveIff — a convergent sequence has its limit above c exactly
// when, for some k, all its terms from some index on exceed
// c + 1/(k + 1). If c < l, take 1/(k + 1) below half the gap l − c and an
// index past which the terms lie within that half of l. Conversely, terms
// from N on at least c + 1/(k + 1) keep their limit at least there, which
// is above c. The late terms are written a(N + m), with no guard on m, so
// that the set where they clear the level is an intersection over every
// m — the form a measurable limit is cut out in.
var LimitAboveIff = limitAboveIffThm{family.Add(registry.ProofEntry{
	Name: "LimitAboveIff",
	Key:  "prop_4efd27c3e46809f3",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → real). ∀l c:real.",
		Hypotheses: []string{"a ⟶ l"},
		Conclusion: "c < l ⇔ ∃k N:num. ∀m:num. c + real_inv(&k + &1) < a(N + m)",
	}, func(arg *Argument, a *Arrow[Nat, Real], l, c *Expr[Real], converges Fact) {
		arg.Iff()
		arg.Forward(
			"below the limit, the late terms clear c by a step 1/(k + 1)",
			func(b *Argument, below Fact) {
				half := b.TermAs[Real]("(l - c) / &2")
				k, small := b.ObtainAs[Nat](
					"some 1/(k + 1) lies below half the gap l − c",
					"∃k:num. real_inv(&k + &1) < (l - c) / &2",
					ByArith(below, real_archimedean.ExistsReciprocalBelow.At(half)))
				near := b.Unfolded(converges, RealConvergesToDef)
				N, close := b.ObtainAs[Nat](
					"past some N every term lies within half the gap of l",
					"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < (l - c) / &2",
					ByArith(below, near.At(half)))
				b.Take(k)
				b.Take(N)
				b.FixAs[Nat]("m")
				b.Show(
					"the term at N + m lies above l − (l − c)/2, which is above c + 1/(k + 1)",
					ByArith(small, close.At(b.TermAs[Nat]("N + m"))))
			})
		arg.Backward(
			"terms eventually above c + 1/(k + 1) keep the limit at or above it",
			func(b *Argument, eventually Fact) {
				_, N, above := b.Unpack2As[Nat, Nat](eventually)
				step := b.TermAs[Real]("c + real_inv(&k + &1)")
				fromN := b.Have(
					"from N on, every term is at least c + 1/(k + 1)",
					"∀n:num. N ≤ n ⇒ c + real_inv(&k + &1) ≤ a(n)",
					Derive(func(d *Argument) {
						n := d.FixAs[Nat]("n")
						past := d.Assume()
						j, shift := d.ObtainAs[Nat](
							"n lies j places past N",
							"∃j:num. n = N + j",
							By(past, nat_order.LessEqExists.At(n, N)))
						d.Show(
							"and the term there exceeds c + 1/(k + 1)",
							ByArith(shift, above.At(j)))
					}))
				limitAbove := b.Have(
					"so the limit is at least c + 1/(k + 1), the limit of the constant sequence",
					"c + real_inv(&k + &1) ≤ l",
					By(
						fromN,
						converges,
						LimitLessEq.At(b.TermAs[Fun[Nat, Real]]("λn:num. c + real_inv(&k + &1)"), a, step, l, N),
						LimitConst.At(step)))
				positive := b.Have(
					"1/(k + 1) is positive",
					"&0 < real_inv(&k + &1)",
					ByArith(real_order_field.InvPos.At(b.TermAs[Real]("&k + &1"))))
				b.Show(
					"so the limit lies above c",
					ByArith(limitAbove, positive))
			})
	}),
})}
