// compare.go — comparing sums over partitions. Two partitions of one
// interval compare without a common refinement: the overlaps of one
// interval with the pieces of a partition add up to its length, so a sum
// over the pieces of one partition and a sum over the pieces of another
// are one double sum over pairs of pieces, weighted by their overlaps,
// which compares termwise. On one tagged partition, the Riemann sums of
// two functions close at every point are close, so the integral sees only
// the values on ⟦a, b⟧, and the oriented integral only the values between
// its bounds; the sums of two functions that agree away from
// the ends of ⟦a, b⟧ differ only on the end strips. Partitions of two
// adjacent intervals, run one after the other, are a partition of their
// union whose Riemann sum is the sum of theirs.

package real_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// PartitionOverlapSum — the pieces of a partition q of ⟦a, b⟧ cut an
// interval ⟦u, v⟧ inside ⟦a, b⟧ into overlaps whose lengths add up to
// v − u. The overlap of ⟦u, v⟧ with the piece from q(j) to q(j + 1) is the
// rise across the piece of the clamp z ↦ min(v, max(u, z)) of the line onto
// ⟦u, v⟧, so the overlaps telescope from the clamp of a, which is u, to the
// clamp of b, which is v.
var PartitionOverlapSum = partitionOverlapSumThm{family.Add(registry.ProofEntry{
	Name: "PartitionOverlapSum",
	Key:  "prop_348a4994eacc14b6",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real. ∀m:num. ∀q:(num → real). ∀u v:real.",
		Hypotheses: []string{
			"«partition»(a, b, m, q)",
			"a ≤ u",
			"u ≤ v",
			"v ≤ b",
		},
		Conclusion: "Σ_{j∈0 .. m} max(&0, min(v, q(j + 1)) - max(u, q(j))) = v - u",
	},
		func(arg *Argument, a, b *Expr[Real], m *Expr[Nat], q *Arrow[Nat, Real], u, v *Expr[Real],
			start, end, rising, low, ordered, high Fact) {
			clamped := arg.Have(
				"each overlap is the rise of the clamp min(v, max(u, ·)) across its piece",
				Statement{
					Binders: "∀j:num.",
					Hypotheses: []string{
						"j ≤ m",
					},
					Conclusion: "max(&0, min(v, q(j + 1)) - max(u, q(j))) = " +
						"min(v, max(u, q(j + 1))) - min(v, max(u, q(j)))",
				},
				arg.ForEach(func(j *Expr[Nat]) Action { return ByArith(rising.At(j), ordered) }))
			telescoping := arg.Have(
				"so the overlaps add up to a telescoping sum",
				"Σ_{j∈0 .. m} max(&0, min(v, q(j + 1)) - max(u, q(j))) = "+
					"Σ_{j∈0 .. m} (min(v, max(u, q(j + 1))) - min(v, max(u, q(j))))",
				By(clamped, real_sum.IntervalCongruence))
			arg.Show(
				"which collapses to the clamp of q(m + 1) = b less the clamp of q(0) = a, that is v − u",
				ByArith(
					telescoping,
					start,
					end,
					low,
					ordered,
					high,
					real_sum.TelescopeUp.At(
						arg.TermAs[Nat]("0"),
						m,
						arg.TermAs[Fun[Nat, Real]]("λj:num. min(v, max(u, q(j)))"))))
		}),
})}

// PartitionSumsCompare — the comparison principle for two partitions p and
// q of one interval: a sum over the pieces of p, each weighted by g, is at
// most a sum over the pieces of q, each weighted by h, as soon as g(k) ≤ h(j)
// wherever piece k of p overlaps piece j of q. The overlaps of piece k with
// the pieces of q add up to its length, and those of piece j with the pieces
// of p to its length (PartitionOverlapSum), so the two sums are double sums
// over the pairs of pieces, g(k) and h(j) times their overlap. Termwise
// g(k) times the overlap is at most h(j) times it, since the overlap is
// empty unless the pieces meet.
var PartitionSumsCompare = partitionSumsCompareThm{family.Add(registry.ProofEntry{
	Name: "PartitionSumsCompare",
	Key:  "prop_49a31c753055b6f8",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real. ∀n m:num. ∀p q g h:(num → real).",
		Hypotheses: []string{
			"«partition»(a, b, n, p)",
			"«partition»(a, b, m, q)",
			"∀k j:num. k ≤ n ∧ j ≤ m ∧ p(k) < q(j + 1) ∧ q(j) < p(k + 1) ⇒ g(k) ≤ h(j)",
		},
		Conclusion: "Σ_{k∈0 .. n} g(k) * (p(k + 1) - p(k)) ≤ Σ_{j∈0 .. m} h(j) * (q(j + 1) - q(j))",
		Abbrev: Abbrev{
			{Name: "overlap", Text: "λk:num. λj:num. max(&0, min(p(k + 1), q(j + 1)) - max(p(k), q(j)))"},
		},
	},
		func(arg *Argument, a, b *Expr[Real], n, m *Expr[Nat], p, q, g, h *Arrow[Nat, Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"p starts at a",
				"and ends at b",
				"and rises piece by piece",
				"q starts at a",
				"and ends at b",
				"and rises piece by piece",
				"where pieces meet, the weight of p is at most that of q")
			rows := arg.Have(
				"the overlaps of piece k of p with the pieces of q add up to its length",
				"∀k:num. k ≤ n ⇒ g(k) * (p(k + 1) - p(k)) = Σ_{j∈0 .. m} g(k) * «overlap»(k, j)",
				Derive(func(c *Argument) {
					k := c.FixAs[Nat]()
					inside := c.Assume()
					c.Show(
						"piece k of p lies in ⟦a, b⟧, and g(k) moves into the sum",
						ByArith(
							parts[0],
							parts[1],
							parts[2],
							parts[3],
							parts[4],
							parts[5],
							inside,
							PartitionPiecesInInterval.At(a, b, n, p, k),
							PartitionOverlapSum.At(a, b, m, q, p.Apply(k), c.TermAs[Real]("p(k + 1)")),
							real_sum.ScalarLeft.At(
								g.Apply(k),
								c.TermAs[Fun[Nat, Real]]("λj:num. «overlap»(k, j)"),
								c.TermAs[Set[Nat]]("0 .. m"))))
				}))
			symmetric := arg.Have(
				"an overlap does not depend on which of the two pieces is named first",
				"∀k j:num. max(&0, min(q(j + 1), p(k + 1)) - max(q(j), p(k))) = «overlap»(k, j)",
				ByArith())
			cols := arg.Have(
				"and the overlaps of piece j of q with the pieces of p add up to its length",
				"∀j:num. j ≤ m ⇒ h(j) * (q(j + 1) - q(j)) = Σ_{k∈0 .. n} h(j) * «overlap»(k, j)",
				Derive(func(c *Argument) {
					j := c.FixAs[Nat]()
					inside := c.Assume()
					named := c.Have(
						"summed over the pieces of p, the overlaps read the same in either naming",
						"Σ_{k∈0 .. n} max(&0, min(q(j + 1), p(k + 1)) - max(q(j), p(k))) = Σ_{k∈0 .. n} «overlap»(k, j)",
						By(symmetric, real_sum.IntervalCongruence))
					c.Show(
						"piece j of q lies in ⟦a, b⟧, and h(j) moves into the sum",
						ByArith(
							parts[0],
							parts[1],
							parts[2],
							parts[3],
							parts[4],
							parts[5],
							inside,
							named,
							PartitionPiecesInInterval.At(a, b, m, q, j),
							PartitionOverlapSum.At(a, b, n, p, q.Apply(j), c.TermAs[Real]("q(j + 1)")),
							real_sum.ScalarLeft.At(
								h.Apply(j),
								c.TermAs[Fun[Nat, Real]]("λk:num. «overlap»(k, j)"),
								c.TermAs[Set[Nat]]("0 .. n"))))
				}))
			termwise := arg.Have(
				"g(k) times an overlap is at most h(j) times it, since the overlap is empty unless the pieces meet",
				"∀k j:num. k ≤ n ∧ j ≤ m ⇒ g(k) * «overlap»(k, j) ≤ h(j) * «overlap»(k, j)",
				Derive(func(c *Argument) {
					k := c.FixAs[Nat]()
					j := c.FixAs[Nat]()
					indices := c.Assume()
					c.Cases(c.Term("p(k) < q(j + 1) ∧ q(j) < p(k + 1)"))
					c.When(
						"where the pieces meet, g(k) ≤ h(j) and the overlap is not negative",
						func(d *Argument, meet Fact) {
							d.Show(
								"so multiplying by the overlap keeps the order",
								By(
									parts[6].At(k, j),
									indices,
									meet,
									real_order_ring.LessEqMulRight.At(g.Apply(k), h.Apply(j), d.TermAs[Real]("«overlap»(k, j)")),
									real_sup_inf.MaxUpperBound.At(
										d.TermAs[Real]("&0"),
										d.TermAs[Real]("min(p(k + 1), q(j + 1)) - max(p(k), q(j))"))))
						})
					c.Otherwise(
						"where they do not meet, the overlap is empty and both sides vanish",
						func(d *Argument, apart Fact) {
							empty := d.Have(
								"the overlap is empty",
								"«overlap»(k, j) = &0",
								ByArith(apart))
							d.Show(
								"both sides are 0",
								ByArith(empty))
						})
				}))
			rowwise := arg.Have(
				"so row by row the weights of p times the overlaps sum to at most those of q",
				"∀k:num. k ≤ n ⇒ Σ_{j∈0 .. m} g(k) * «overlap»(k, j) ≤ Σ_{j∈0 .. m} h(j) * «overlap»(k, j)",
				arg.ForEach(func(k *Expr[Nat]) Action {
					return By(termwise.At(k), real_sum.IntervalMonotone)
				}))
			left := arg.Have(
				"the left sum is the double sum of g(k) times the overlaps",
				"Σ_{k∈0 .. n} g(k) * (p(k + 1) - p(k)) = Σ_{k∈0 .. n} Σ_{j∈0 .. m} g(k) * «overlap»(k, j)",
				By(rows, real_sum.IntervalCongruence))
			right := arg.Have(
				"the right sum is the double sum of h(j) times the overlaps",
				"Σ_{j∈0 .. m} h(j) * (q(j + 1) - q(j)) = Σ_{j∈0 .. m} Σ_{k∈0 .. n} h(j) * «overlap»(k, j)",
				By(cols, real_sum.IntervalCongruence))
			compared := arg.Have(
				"the two double sums compare row by row",
				"Σ_{k∈0 .. n} Σ_{j∈0 .. m} g(k) * «overlap»(k, j) ≤ "+
					"Σ_{k∈0 .. n} Σ_{j∈0 .. m} h(j) * «overlap»(k, j)",
				By(rowwise, real_sum.IntervalMonotone))
			exchanged := arg.Have(
				"and a double sum may be taken in either order",
				"Σ_{k∈0 .. n} Σ_{j∈0 .. m} h(j) * «overlap»(k, j) = "+
					"Σ_{j∈0 .. m} Σ_{k∈0 .. n} h(j) * «overlap»(k, j)",
				Cite(real_sum.IntervalSwap))
			arg.Show(
				"so the left sum is at most the right one",
				ByArith(left, right, compared, exchanged))
		}),
})}

// PartitionSumsClose — two sums over partitions of one interval are close
// when their weights are: if g(k) and h(j) differ by at most η wherever
// piece k of p meets piece j of q, the two sums differ by at most
// η·(b − a). Each sum is at most the other with η added to every weight
// (PartitionSumsCompare), and adding η to every weight adds η·(b − a).
var PartitionSumsClose = partitionSumsCloseThm{family.Add(registry.ProofEntry{
	Name: "PartitionSumsClose",
	Key:  "prop_c637079cb459974f",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real. ∀n m:num. ∀p q g h:(num → real). ∀η:real.",
		Hypotheses: []string{
			"«partition»(a, b, n, p)",
			"«partition»(a, b, m, q)",
			"∀k j:num. k ≤ n ∧ j ≤ m ∧ p(k) < q(j + 1) ∧ q(j) < p(k + 1) ⇒ |g(k) - h(j)| ≤ η",
		},
		Conclusion: "|Σ_{k∈0 .. n} g(k) * (p(k + 1) - p(k)) - Σ_{j∈0 .. m} h(j) * (q(j + 1) - q(j))| ≤ " +
			"η * (b - a)",
	},
		func(
			arg *Argument,
			a, b *Expr[Real],
			n, m *Expr[Nat],
			p, q, g, h *Arrow[Nat, Real],
			η *Expr[Real],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"p starts at a",
				"and ends at b",
				"and rises piece by piece",
				"q starts at a",
				"and ends at b",
				"and rises piece by piece",
				"where pieces meet, the weights differ by at most η")
			below := arg.Have(
				"where pieces meet, g(k) is at most h(j) + η",
				"∀k j:num. k ≤ n ∧ j ≤ m ∧ p(k) < q(j + 1) ∧ q(j) < p(k + 1) ⇒ g(k) ≤ h(j) + η",
				Derive(func(c *Argument) {
					k := c.FixAs[Nat]()
					j := c.FixAs[Nat]()
					meet := c.Assume()
					c.Show(
						"since they differ by at most η",
						ByArith(parts[6].At(k, j), meet))
				}))
			above := arg.Have(
				"and h(j) is at most g(k) + η",
				"∀j k:num. j ≤ m ∧ k ≤ n ∧ q(j) < p(k + 1) ∧ p(k) < q(j + 1) ⇒ h(j) ≤ g(k) + η",
				Derive(func(c *Argument) {
					j := c.FixAs[Nat]()
					k := c.FixAs[Nat]()
					meet := c.Assume()
					c.Show(
						"since they differ by at most η",
						ByArith(parts[6].At(k, j), meet))
				}))
			up := arg.Have(
				"so the sum over p is at most the sum over q with η added to its weights",
				"Σ_{k∈0 .. n} g(k) * (p(k + 1) - p(k)) ≤ Σ_{j∈0 .. m} (h(j) + η) * (q(j + 1) - q(j))",
				By(
					PartitionSumsCompare.At(a, b, n, m, p, q, g, arg.TermAs[Fun[Nat, Real]]("λj:num. h(j) + η")),
					parts[0],
					parts[1],
					parts[2],
					parts[3],
					parts[4],
					parts[5],
					below))
			down := arg.Have(
				"and the sum over q is at most the sum over p with η added to its weights",
				"Σ_{j∈0 .. m} h(j) * (q(j + 1) - q(j)) ≤ Σ_{k∈0 .. n} (g(k) + η) * (p(k + 1) - p(k))",
				By(
					PartitionSumsCompare.At(a, b, m, n, q, p, h, arg.TermAs[Fun[Nat, Real]]("λk:num. g(k) + η")),
					parts[0],
					parts[1],
					parts[2],
					parts[3],
					parts[4],
					parts[5],
					above))
			raisedQ := arg.Have(
				"adding η to the weights over q adds η times the total length b − a",
				"Σ_{j∈0 .. m} (h(j) + η) * (q(j + 1) - q(j)) = Σ_{j∈0 .. m} h(j) * (q(j + 1) - q(j)) + η * (b - a)",
				Simp(
					Fwd(real_ring.RightDistrib),
					Rev(real_sum.IntervalAdd),
					Rev(real_sum.ScalarLeft.Inst[Nat]()),
					Fwd(real_sum.TelescopeUp)),
				ByArith(parts[3], parts[4]))
			raisedP := arg.Have(
				"and over p likewise",
				"Σ_{k∈0 .. n} (g(k) + η) * (p(k + 1) - p(k)) = Σ_{k∈0 .. n} g(k) * (p(k + 1) - p(k)) + η * (b - a)",
				Simp(
					Fwd(real_ring.RightDistrib),
					Rev(real_sum.IntervalAdd),
					Rev(real_sum.ScalarLeft.Inst[Nat]()),
					Fwd(real_sum.TelescopeUp)),
				ByArith(parts[0], parts[1]))
			arg.Show(
				"so each sum is within η·(b − a) of the other",
				ByArith(up, down, raisedQ, raisedP))
		}),
})}

// RiemannSumsClose — two functions within η of each other at every point
// of ⟦a, b⟧ have Riemann sums within η·(b − a) of each other on every
// tagged partition of ⟦a, b⟧. One partition carries two functions here,
// where PartitionSumsClose compares two partitions by their weights.
//
// Every tag lies in ⟦a, b⟧, so piece by piece the two terms
// f(t(k))·(p(k + 1) − p(k)) and g(t(k))·(p(k + 1) − p(k)) differ by at
// most η times the length of the piece, which is nonnegative. Summed, the
// difference of the Riemann sums is at most η times the sum of the
// lengths, and the lengths telescope to p(n + 1) − p(0) = b − a.
var RiemannSumsClose = riemannSumsCloseThm{family.Add(registry.ProofEntry{
	Name: "RiemannSumsClose",
	Key:  "prop_2e6f3bbb5ac1b7f",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀a b η:real. ∀n:num. ∀p t:(num → real).",
		Hypotheses: []string{
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x) - g(x)| ≤ η",
			"p(0) = a",
			"p(n + 1) = b",
			"∀k:num. k ≤ n ⇒ p(k) ≤ t(k) ∧ t(k) ≤ p(k + 1)",
		},
		Conclusion: "|Σ_{k∈0 .. n} f(t(k)) * (p(k + 1) - p(k)) - " +
			"Σ_{k∈0 .. n} g(t(k)) * (p(k + 1) - p(k))| ≤ " +
			"η * (b - a)",
	},
		func(
			arg *Argument,
			f, g *Arrow[Real, Real],
			a, b, η *Expr[Real],
			n *Expr[Nat],
			p, t *Arrow[Nat, Real],
			near, start, end, tagged Fact,
		) {
			termwise := arg.Have(
				"piece by piece the two terms differ by at most η times the length of the piece",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"0 ≤ i",
						"i ≤ n",
					},
					Conclusion: "|f(t(i)) * (p(i + 1) - p(i)) - g(t(i)) * (p(i + 1) - p(i))| ≤ η * (p(i + 1) - p(i))",
				},
				Derive(func(c *Argument) {
					i := c.FixAs[Nat]()
					inRange := c.Assume()
					tag := t.Apply(i)
					inside := c.Have(
						"the tag t(i) lies in ⟦a, b⟧",
						"a ≤ t(i) ∧ t(i) ≤ b",
						By(start, end, tagged, inRange, PartitionTagsInInterval))
					piece := c.Have(
						"so f and g are within η of each other there, and the piece has nonnegative length",
						"&0 ≤ p(i + 1) - p(i) ∧ |f(t(i)) - g(t(i))| ≤ η",
						ByArith(near.At(tag), tagged.At(i), inRange, inside))
					gap := c.TermAs[Real]("f(t(i)) - g(t(i))")
					length := c.TermAs[Real]("p(i + 1) - p(i)")
					c.Show(
						"the difference of the two terms is |f(t(i)) − g(t(i))| times the length, at most η times it",
						ByArith(
							piece,
							real_ring.SubRightDistrib.At(f.Apply(tag), g.Apply(tag), length),
							real_sgn_abs.AbsMul.At(gap, length),
							real_sgn_abs.AbsFixedIffNonneg.At(length),
							real_order_ring.LessEqMulRight.At(c.TermAs[Real]("|f(t(i)) - g(t(i))|"), η, length)))
				}))
			zero := arg.TermAs[Nat]("0")
			fTerms := arg.TermAs[Fun[Nat, Real]]("λk:num. f(t(k)) * (p(k + 1) - p(k))")
			gTerms := arg.TermAs[Fun[Nat, Real]]("λk:num. g(t(k)) * (p(k + 1) - p(k))")
			dominated := arg.Have(
				"the difference of the Riemann sums is the sum of the "+
					"termwise differences, at most the sum of η times the lengths",
				"|Σ_{k∈0 .. n} f(t(k)) * (p(k + 1) - p(k)) - Σ_{k∈0 .. n} g(t(k)) * (p(k + 1) - p(k))| ≤ "+
					"Σ_{k∈0 .. n} η * (p(k + 1) - p(k))",
				By(
					termwise,
					real_sum.IntervalSub.At(zero, n, fTerms, gTerms),
					real_sum.IntervalDominated.At(
						zero,
						n,
						arg.TermAs[Fun[Nat, Real]]("λk:num. f(t(k)) * (p(k + 1) - p(k)) - g(t(k)) * (p(k + 1) - p(k))"),
						arg.TermAs[Fun[Nat, Real]]("λk:num. η * (p(k + 1) - p(k))"))))
			lengths := arg.Have(
				"the lengths of the pieces telescope to p(n + 1) − p(0) = b − a",
				"Σ_{k∈0 .. n} η * (p(k + 1) - p(k)) = η * (b - a)",
				Simp(Rev(real_sum.ScalarLeft.Inst[Nat]()), Fwd(real_sum.TelescopeUp)),
				ByArith(start, end))
			arg.Show(
				"so the Riemann sums differ by at most η·(b − a)",
				By(dominated, lengths))
		}),
})}

// HasIntegralCongruence — the integral sees only the values on ⟦a, b⟧: a
// function that agrees with f there has f's integral. f and g are within 0
// of each other on ⟦a, b⟧, so on a tagged partition of ⟦a, b⟧ their Riemann
// sums lie within 0·(b − a) of each other (RiemannSumsClose), that is, are
// equal, and the meshes that serve f serve g.
var HasIntegralCongruence = hasIntegralCongruenceThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralCongruence",
	Key:  "prop_cb0f6829e979f7d0",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀a b I:real.",
		Hypotheses: []string{
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ f(x) = g(x)",
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "real_has_integral(g, a, b, I)",
	},
		func(arg *Argument, f, g *Arrow[Real, Real], a, b, I *Expr[Real], agree, toI Fact) {
			integral := arg.Conjuncts(
				arg.Unfolded(toI, RealHasIntegralDef),
				"the interval is ordered",
				"for every ε some mesh brings the Riemann sums of f within ε of I")
			apart := arg.Have(
				"f and g are within 0 of each other on ⟦a, b⟧",
				"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x) - g(x)| ≤ &0",
				arg.ForEach(func(x *Expr[Real]) Action { return ByArith(agree.At(x)) }))
			same := arg.Have(
				"so on every tagged partition of ⟦a, b⟧ the two Riemann sums are equal",
				Statement{
					Binders: "∀δ:real. ∀n:num. ∀p t:(num → real).",
					Hypotheses: []string{
						"«finePartition»(a, b, δ, n, p, t)",
					},
					Conclusion: "«riemannSum»(f, n, p, t) = «riemannSum»(g, n, p, t)",
				},
				Derive(func(c *Argument) {
					c.FixAs[Real]()
					n := c.FixAs[Nat]()
					p := c.FixAs[Fun[Nat, Real]]()
					t := c.FixAs[Fun[Nat, Real]]()
					fine := c.Assume()
					c.Show(
						"they are within 0·(b − a) of each other",
						ByArith(apart, fine, RiemannSumsClose.At(f, g, a, b, c.TermAs[Real]("&0"), n, p, t)))
				}))
			arg.Show(
				"so the meshes that bring the Riemann sums of f within ε of I serve g",
				Unfold(RealHasIntegralDef),
				By(integral[0], integral[1], same))
		}),
})}

// IntegralCongruence — the oriented integral sees only the values between
// its bounds: two functions that agree between a and b, whichever way round
// they stand, have the same integral from a to b. They agree on
// ⟦min(a, b), max(a, b)⟧, so they have the same integrals there
// (HasIntegralCongruence, each way round), and the integral from a to b is
// the one chosen over that interval: over ⟦a, b⟧ when a ≤ b, and negated
// over ⟦b, a⟧ when b < a.
var IntegralCongruence = integralCongruenceThm{family.Add(registry.ProofEntry{
	Name: "IntegralCongruence",
	Key:  "prop_2040f78c78bd8e3c",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"∀x:real. min(a, b) ≤ x ∧ x ≤ max(a, b) ⇒ f(x) = g(x)",
		},
		Conclusion: "real_integral(f, a, b) = real_integral(g, a, b)",
	},
		func(arg *Argument, f, g *Arrow[Real, Real], a, b *Expr[Real], agree Fact) {
			low, high := arg.TermAs[Real]("min(a, b)"), arg.TermAs[Real]("max(a, b)")
			same := arg.Have(
				"f and g agree on ⟦min(a, b), max(a, b)⟧, so each has there every integral the other has",
				"∀I:real. "+
					"    real_has_integral(f, min(a, b), max(a, b), I) ⇔ real_has_integral(g, min(a, b), max(a, b), I)",
				arg.ForEach(func(I *Expr[Real]) Action {
					return By(
						agree,
						HasIntegralCongruence.At(f, g, low, high, I),
						HasIntegralCongruence.At(g, f, low, high, I))
				}))
			arg.Show(
				"the integral from a to b is the one chosen over that "+
					"interval, ⟦a, b⟧ when a ≤ b and ⟦b, a⟧ negated otherwise",
				Unfold(RealIntegralDef),
				By(same, real_sup_inf.RealMinDef.At(a, b), real_sup_inf.RealMaxDef.At(a, b)))
		}),
})}

// RiemannSumsAgreeInside — two functions that agree on ⟦c, d⟧ ⊆ ⟦a, b⟧ and
// differ by at most M on ⟦a, b⟧ have Riemann sums within
// M·((c − a) + (b − d) + 2δ) of each other on a tagged partition of ⟦a, b⟧
// finer than δ: only the end strips ⟦a, c⟧ and ⟦d, b⟧ count, each widened
// by the mesh.
//
// Cut ⟦a, b⟧ at c + δ and d − δ. A piece of the partition that meets the
// middle piece ⟦c + δ, d − δ⟧ is shorter than δ, so its tag lies in
// ⟦c, d⟧, where the two functions agree: the comparison principle
// (PartitionSumsCompare) weighs the termwise differences against M on the
// two end pieces and 0 on the middle one. When ⟦c, d⟧ is shorter than 2δ
// there is no middle piece, and M·(b − a) already bounds the difference.
var RiemannSumsAgreeInside = riemannSumsAgreeInsideThm{family.Add(registry.ProofEntry{
	Name: "RiemannSumsAgreeInside",
	Key:  "prop_446ae066dc467de8",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀a b c d M δ:real. ∀n:num. ∀p t:(num → real).",
		Hypotheses: []string{
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x) - g(x)| ≤ M",
			"∀x:real. c ≤ x ∧ x ≤ d ⇒ f(x) = g(x)",
			"a ≤ c",
			"c ≤ d",
			"d ≤ b",
			"«finePartition»(a, b, δ, n, p, t)",
		},
		Conclusion: "|«riemannSum»(f, n, p, t) - «riemannSum»(g, n, p, t)| ≤ " +
			"M * ((c - a) + (b - d) + &2 * δ)",
		Abbrev: Abbrev{
			{Name: "cuts", Text: "λj:num. COND(j = 0, a, COND(j = 1, c + δ, COND(j = 2, d - δ, b)))"},
		},
	},
		func(
			arg *Argument,
			f, g *Arrow[Real, Real],
			a, b, c, d, M, δ *Expr[Real],
			n *Expr[Nat],
			p, t *Arrow[Nat, Real],
			near, agree, ac, cd, db, fine Fact,
		) {
			pieces := arg.Conjuncts(
				fine,
				"p starts at a",
				"and ends at b",
				"each piece holds its tag and is shorter than δ")
			rising := arg.Have(
				"the points of p rise from a to b",
				"«partition»(a, b, n, p)",
				By(FinePartitionIsPartition.At(a, b, δ, n, p, t), pieces[0], pieces[1], pieces[2]))
			bound := arg.Have(
				"M is not negative",
				"&0 ≤ M",
				ByArith(near.At(a), ac, cd, db))
			arg.Cases(arg.Term("&2 * δ ≤ d - c"))
			arg.Otherwise(
				"when ⟦c, d⟧ is shorter than 2δ, M·(b − a) bounds the difference",
				func(e *Argument, short Fact) {
					crude := e.Have(
						"two functions within M of each other have Riemann sums within M·(b − a)",
						"|«riemannSum»(f, n, p, t) - «riemannSum»(g, n, p, t)| ≤ M * (b - a)",
						By(near, pieces[0], pieces[1], pieces[2], RiemannSumsClose))
					strips := e.TermAs[Real]("(c - a) + (b - d) + &2 * δ")
					wider := e.Have(
						"and b − a is less than (c − a) + (b − d) + 2δ",
						"b - a ≤ (c - a) + (b - d) + &2 * δ",
						ByArith(short))
					e.Show(
						"so M·(b − a) is at most M·((c − a) + (b − d) + 2δ)",
						ByArith(crude, bound, wider, real_order_ring.LessEqMulLeft.At(M, e.TermAs[Real]("b - a"), strips)))
				})
			arg.When(
				"when ⟦c, d⟧ is at least 2δ long, cut ⟦a, b⟧ at c + δ and d − δ",
				func(e *Argument, long Fact) {
					zero := e.TermAs[Nat]("0")
					two := e.TermAs[Nat]("2")
					positive := e.Have(
						"δ is positive, the first piece of p being shorter than δ",
						"&0 < δ",
						ByArith(pieces[2].At(zero)))
					risingCuts := e.Have(
						"the cuts a, c + δ, d − δ, b rise",
						"«partition»(a, b, 2, «cuts»)",
						ByArith(long, ac, db, positive))
					termwise := e.Have(
						"a piece of p meeting the middle piece has its tag in ⟦c, "+
							"d⟧, where f and g agree; elsewhere they differ by at most M",
						Statement{
							Binders: "∀k j:num.",
							Hypotheses: []string{
								"k ≤ n",
								"j ≤ 2",
								"p(k) < «cuts»(j + 1)",
								"«cuts»(j) < p(k + 1)",
							},
							Conclusion: "|f(t(k)) - g(t(k))| ≤ COND(j = 1, &0, M)",
						},
						Derive(func(h *Argument) {
							k := h.FixAs[Nat]()
							h.FixAs[Nat]()
							meet := h.Assume()
							h.Cases(h.Term("j = 1"))
							h.When(
								"the middle piece: its piece of p is shorter than δ, so the tag lies in ⟦c, d⟧",
								func(o *Argument, middle Fact) {
									o.Show(
										"where f and g agree",
										ByArith(middle, meet, pieces[2].At(k), agree.At(t.Apply(k))))
								})
							h.Otherwise(
								"an end piece: the tag lies in ⟦a, b⟧",
								func(o *Argument, end Fact) {
									o.Show(
										"where f and g differ by at most M",
										ByArith(
											end,
											meet,
											pieces[0],
											pieces[1],
											pieces[2],
											near.At(t.Apply(k)),
											PartitionTagsInInterval.At(a, b, n, p, t, k)))
								})
						}))
					compared := e.Have(
						"weighed against the cuts, the termwise differences "+
							"count M on the end pieces and 0 on the middle one",
						"Σ_{k∈0 .. n} |f(t(k)) - g(t(k))| * (p(k + 1) - p(k)) ≤ "+
							"Σ_{j∈0 .. 2} COND(j = 1, &0, M) * («cuts»(j + 1) - «cuts»(j))",
						By(
							rising,
							risingCuts,
							termwise,
							PartitionSumsCompare.At(
								a,
								b,
								n,
								two,
								p,
								e.TermAs[Fun[Nat, Real]]("«cuts»"),
								e.TermAs[Fun[Nat, Real]]("λk:num. |f(t(k)) - g(t(k))|"),
								e.TermAs[Fun[Nat, Real]]("λj:num. COND(j = 1, &0, M)"))))
					weights := e.TermAs[Fun[Nat, Real]]("λj:num. COND(j = 1, &0, M) * («cuts»(j + 1) - «cuts»(j))")
					ends := e.Have(
						"the end pieces are c + δ − a and b − (d − δ) long",
						"Σ_{j∈0 .. 2} COND(j = 1, &0, M) * («cuts»(j + 1) - «cuts»(j)) = "+
							"M * (c + δ - a) + M * (b - (d - δ))",
						ByArith(
							real_sum.PeelLeft.At(zero, two, weights),
							real_sum.PeelLeft.At(e.TermAs[Nat]("1"), two, weights),
							real_sum.IntervalPoint.At(two, weights)))
					perTerm := e.Have(
						"piece by piece the two terms differ by |f(t(i)) − g(t(i))| times the length of the piece",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"0 ≤ i",
								"i ≤ n",
							},
							Conclusion: "|f(t(i)) * (p(i + 1) - p(i)) - g(t(i)) * (p(i + 1) - p(i))| ≤ " +
								"|f(t(i)) - g(t(i))| * (p(i + 1) - p(i))",
						},
						Derive(func(h *Argument) {
							i := h.FixAs[Nat]()
							inRange := h.Assume()
							length := h.TermAs[Real]("p(i + 1) - p(i)")
							nonneg := h.Have(
								"the piece has nonnegative length",
								"&0 ≤ p(i + 1) - p(i)",
								ByArith(pieces[2].At(i), inRange))
							h.Show(
								"the difference of the terms is the difference of the values times the length",
								ByArith(
									nonneg,
									real_ring.SubRightDistrib.At(f.Apply(t.Apply(i)), g.Apply(t.Apply(i)), length),
									real_sgn_abs.AbsMul.At(h.TermAs[Real]("f(t(i)) - g(t(i))"), length),
									real_sgn_abs.AbsFixedIffNonneg.At(length)))
						}))
					dominated := e.Have(
						"so the Riemann sums differ by at most the sum of the termwise differences times the lengths",
						"|«riemannSum»(f, n, p, t) - «riemannSum»(g, n, p, t)| ≤ "+
							"Σ_{k∈0 .. n} |f(t(k)) - g(t(k))| * (p(k + 1) - p(k))",
						By(
							perTerm,
							real_sum.IntervalSub.At(
								zero,
								n,
								e.TermAs[Fun[Nat, Real]]("λk:num. f(t(k)) * (p(k + 1) - p(k))"),
								e.TermAs[Fun[Nat, Real]]("λk:num. g(t(k)) * (p(k + 1) - p(k))")),
							real_sum.IntervalDominated.At(
								zero,
								n,
								e.TermAs[Fun[Nat, Real]]("λk:num. f(t(k)) * (p(k + 1) - p(k)) - g(t(k)) * (p(k + 1) - p(k))"),
								e.TermAs[Fun[Nat, Real]]("λk:num. |f(t(k)) - g(t(k))| * (p(k + 1) - p(k))"))))
					e.Show(
						"so they differ by at most M·((c − a) + (b − d) + 2δ)",
						ByArith(dominated, compared, ends))
				})
		}),
})}

// PartitionJoin — two tagged partitions finer than δ, of ⟦a, c⟧ and of
// ⟦c, b⟧, join into one of ⟦a, b⟧ finer than δ whose Riemann sum is the sum
// of theirs. The join runs through the points and tags of the first up to
// index n₁ and then through those of the second, shifted by n₁ + 1; at the
// seam the first ends at c where the second starts, so its last piece ends
// where the join's next point stands. Its Riemann sum splits at n₁: up to
// n₁ its terms are the first partition's, and past n₁, read back by the
// shift, the second's.
var PartitionJoin = partitionJoinThm{family.Add(registry.ProofEntry{
	Name: "PartitionJoin",
	Key:  "prop_b4171772d32d3d46",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). " +
			"∀a c b δ:real. " +
			"∀n₁:num. " +
			"∀p₁ t₁:(num → real). " +
			"∀n₂:num. " +
			"∀p₂ t₂:(num → real).",
		Hypotheses: []string{
			"«finePartition»(a, c, δ, n₁, p₁, t₁)",
			"«finePartition»(c, b, δ, n₂, p₂, t₂)",
		},
		Conclusion: "∃n:num. ∃p t:(num → real). " +
			"    «finePartition»(a, b, δ, n, p, t) ∧ " +
			"    «riemannSum»(f, n, p, t) = «riemannSum»(f, n₁, p₁, t₁) + «riemannSum»(f, n₂, p₂, t₂)",
		Abbrev: Abbrev{
			{Name: "join", Text: "λu:(num → real). λv:(num → real). λk:num. " +
				"    COND(k ≤ n₁, u(k), v(k - (n₁ + 1)))"},
			{Name: "joinTerm", Text: "λk:num. " +
				"    f(«join»(t₁, t₂, k)) * («join»(p₁, p₂, k + 1) - «join»(p₁, p₂, k))"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			a, c, b, δ *Expr[Real],
			n1 *Expr[Nat],
			p1, t1 *Arrow[Nat, Real],
			n2 *Expr[Nat],
			p2, t2 *Arrow[Nat, Real],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"p₁ starts at a",
				"and ends at c",
				"each piece of p₁ holds its tag and is shorter than δ",
				"p₂ starts at c",
				"and ends at b",
				"each piece of p₂ holds its tag and is shorter than δ")
			seam := arg.Have(
				"p₁ ends at c, where p₂ starts, so up to n₁ the point after k is p₁'s",
				"∀k:num. k ≤ n₁ ⇒ «join»(p₁, p₂, k + 1) = p₁(k + 1)",
				Derive(func(d *Argument) {
					d.FixAs[Nat]()
					within := d.Assume()
					d.Cases(d.Term("k + 1 ≤ n₁"))
					d.When(
						"short of n₁ the join is still running through p₁",
						func(e *Argument, inner Fact) {
							e.Show(
								"so the point after k is p₁(k + 1)",
								By(inner))
						})
					d.Otherwise(
						"at n₁ the point after k is the first point of p₂",
						func(e *Argument, last Fact) {
							at := e.Have(
								"k is n₁",
								"k = n₁",
								ByArith(last, within))
							e.Show(
								"and p₂(0) = c = p₁(n₁ + 1)",
								ByArith(at, parts[1], parts[3]))
						})
				}))
			pieces := arg.Have(
				"each piece of the join holds its tag and is shorter than δ",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"k ≤ n₁ + n₂ + 1",
					},
					Conclusion: "«join»(p₁, p₂, k) ≤ «join»(t₁, t₂, k) ∧ " +
						"«join»(t₁, t₂, k) ≤ «join»(p₁, p₂, k + 1) ∧ " +
						"«join»(p₁, p₂, k + 1) - «join»(p₁, p₂, k) < δ",
				},
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					within := d.Assume()
					d.Cases(d.Term("k ≤ n₁"))
					d.When(
						"up to n₁ it is piece k of p₁, the last of them ending at the seam",
						func(e *Argument, early Fact) {
							e.Show(
								"which holds its tag and is shorter than δ",
								ByArith(seam.At(k), parts[2].At(k), early))
						})
					d.Otherwise(
						"past n₁ it is piece k − (n₁ + 1) of p₂",
						func(e *Argument, late Fact) {
							next := e.Have(
								"whose right end has index k + 1 − (n₁ + 1) in p₂",
								"k + 1 - (n₁ + 1) = k - (n₁ + 1) + 1",
								ByArith(late))
							e.Show(
								"which holds its tag and is shorter than δ",
								ByArith(parts[5].At(e.TermAs[Nat]("k - (n₁ + 1)")), late, within, next))
						})
				}))
			leftTerms := arg.Have(
				"up to n₁ the terms of the join's Riemann sum are those of p₁'s",
				"∀k:num. k ≤ n₁ ⇒ «joinTerm»(k) = f(t₁(k)) * (p₁(k + 1) - p₁(k))",
				arg.ForEach(func(k *Expr[Nat]) Action { return ByArith(seam.At(k)) }))
			leftSum := arg.Have(
				"so up to n₁ the join's Riemann sum is p₁'s",
				"Σ_{k∈0 .. n₁} «joinTerm»(k) = «riemannSum»(f, n₁, p₁, t₁)",
				By(leftTerms, real_sum.IntervalCongruence))
			count := arg.Have(
				"the join's last index n₁ + n₂ + 1 lies n₁ + 1 past n₂, the last of p₂",
				"n₁ + n₂ + 1 = n₂ + (n₁ + 1)",
				ByArith())
			rightSum := arg.Have(
				"past n₁ the join is p₂ shifted by n₁ + 1, so there its Riemann sum is p₂'s",
				"Σ_{k∈n₁ + 1 .. n₁ + n₂ + 1} «joinTerm»(k) = «riemannSum»(f, n₂, p₂, t₂)",
				ByArith(
					count,
					real_sum.Shift.At(
						arg.TermAs[Nat]("0"),
						n2,
						arg.TermAs[Nat]("n₁ + 1"),
						arg.TermAs[Fun[Nat, Real]]("«joinTerm»"))))
			split := arg.Have(
				"the join's Riemann sum splits at n₁",
				"Σ_{k∈0 .. n₁ + n₂ + 1} «joinTerm»(k) = "+
					"Σ_{k∈0 .. n₁} «joinTerm»(k) + Σ_{k∈n₁ + 1 .. n₁ + n₂ + 1} «joinTerm»(k)",
				ByArith(
					nat_arith.AddAssoc.At(n1, n2, arg.TermAs[Nat]("1")),
					real_sum.SplitAt.At(
						arg.TermAs[Nat]("0"),
						n1,
						arg.TermAs[Nat]("n₂ + 1"),
						arg.TermAs[Fun[Nat, Real]]("«joinTerm»"))))
			arg.Take(arg.TermAs[Nat]("n₁ + n₂ + 1"))
			arg.Take(arg.TermAs[Fun[Nat, Real]]("«join»(p₁, p₂)"))
			arg.Take(arg.TermAs[Fun[Nat, Real]]("«join»(t₁, t₂)"))
			arg.Show(
				"the join runs from p₁(0) = a to p₂(n₂ + 1) = b, and its Riemann sum is the sum of the two",
				ByArith(parts[0], parts[4], pieces, split, leftSum, rightSum))
		}),
})}
