// cover.go — the covering lemmas the length of an interval rests on: a
// closed interval covered by open intervals is shorter than their total
// length. An open interval ⟬c(i), d(i)⟭ with d(i) ≤ c(i) is empty, and
// it counts with length 0, max(d(i) - c(i), &0).

package lebesgue_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteCoverLength — a closed interval covered by finitely many open
// intervals is shorter than their total length. By induction on the
// number of intervals. With none, nothing covers a. Otherwise a lies in
// some interval ⟬c(j), d(j)⟭ of the family. If that interval reaches past
// b it alone is longer than ⟦a, b⟧. If it ends at d(j) ≤ b, no point from
// d(j) on lies in it, so the other intervals cover ⟦d(j), b⟧ and are, by
// induction, longer than b - d(j); and d(j) - a is less than the length
// of the interval at j.
var FiniteCoverLength = finiteCoverLengthThm{family.Add(registry.ProofEntry{
	Name: "FiniteCoverLength",
	Key:  "prop_254c810060b0ee6",
	Build: family.Theorem(Statement{
		Binders: "∀c d:(A → real). ∀k:set(A). ∀a b:real.",
		Hypotheses: []string{
			"finite(k)",
			"a ≤ b",
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ ∃i:A. i ∈ k ∧ c(i) < x ∧ x < d(i)",
		},
		Conclusion: "b - a < Σ_{i∈k} max(d(i) - c(i), &0)",
	}, func(arg *Argument, c, d *Arrow[A, Real]) {
		byCount := arg.Have(
			"by induction on the number n of intervals",
			Statement{
				Binders: "∀n:num. ∀k:set(A). ∀a b:real.",
				Hypotheses: []string{
					"finite(k)",
					"card(k) = n",
					"a ≤ b",
					"∀x:real. a ≤ x ∧ x ≤ b ⇒ ∃i:A. i ∈ k ∧ c(i) < x ∧ x < d(i)",
				},
				Conclusion: "b - a < Σ_{i∈k} max(d(i) - c(i), &0)",
			},
			Derive(func(ind *Argument) {
				ind.Induct("n")
				ind.Base(
					"with no intervals at all, nothing covers a",
					By(cardinality.CardEqZero, real_order_ring.LessEqRefl, set_basic.NotInEmpty))
				ind.Step(
					"with suc(n) intervals, set aside the one that holds a",
					func(step *Argument, ih Fact) {
						k := step.FixAs[Set[A]]("k")
						a := step.FixAs[Real]("a")
						b := step.FixAs[Real]("b")
						hyps := step.Conjuncts(
							step.Assume(),
							"k is finite",
							"k has suc(n) members",
							"a ≤ b",
							"the intervals of k cover ⟦a, b⟧")
						finite, count, ordered, covered := hyps[0], hyps[1], hyps[2], hyps[3]

						j, holdsA := step.ObtainAs[A](
							"an interval of the family holds a",
							"∃j:A. j ∈ k ∧ c(j) < a ∧ a < d(j)",
							By(covered.At(a), ordered, real_order_ring.LessEqRefl))
						total := step.BigOpAs[A, Real]("Σ_{i∈k} max(d(i) - c(i), &0)")
						rest := step.TermAs[Set[A]]("delete(k, j)")
						length := step.TermAs[Real]("d(j) - c(j)")
						zero := step.TermAs[Real]("&0")
						split := step.Have(
							"the total splits off the interval at j",
							"Σ_{i∈k} max(d(i) - c(i), &0) = Σ_{i∈delete(k, j)} max(d(i) - c(i), &0) + max(d(j) - c(j), &0)",
							ByArith(real_sum.Delete.At(k, total.Summand(), j), finite, holdsA))

						step.Cases(step.Term("d(j) ≤ b"))
						step.Otherwise(
							"b lies inside the interval at j, which alone is longer than ⟦a, b⟧",
							func(br *Argument, inside Fact) {
								br.Show(
									"the other intervals add a nonnegative amount",
									ByArith(
										split,
										inside,
										holdsA,
										real_sup_inf.MaxUpperBound.At(length, zero),
										real_sum.Nonneg.At(rest, total.Summand()),
										real_sup_inf.MaxUpperBound))
							})
						step.When(
							"the interval at j ends inside ⟦a, b⟧, and the others cover ⟦d(j), b⟧",
							func(br *Argument, past Fact) {
								others := br.Have(
									"the other intervals cover ⟦d(j), b⟧",
									"∀x:real. d(j) ≤ x ∧ x ≤ b ⇒ ∃i:A. i ∈ delete(k, j) ∧ c(i) < x ∧ x < d(i)",
									Derive(func(pt *Argument) {
										x := pt.FixAs[Real]("x")
										within := pt.Assume()
										above := pt.Have(
											"x lies in ⟦a, b⟧",
											"a ≤ x",
											ByArith(holdsA, within))
										i, holdsX := pt.Obtain(
											"an interval of the family holds x",
											"∃i:A. i ∈ k ∧ c(i) < x ∧ x < d(i)",
											By(covered.At(x), above, within))
										pt.Take(i)
										pt.Show(
											"it is not the interval at j, which ends at or before x",
											By(within, holdsX, set_basic.InDelete, real_order_ring.NotLessEq))
									}))
								fewer := br.Have(
									"setting j aside leaves n intervals",
									"card(delete(k, j)) = n",
									ByArith(cardinality.CountsOneMore.At(k, j), finite, count, holdsA))
								shorter := br.Have(
									"by induction, they are longer than ⟦d(j), b⟧",
									"b - d(j) < Σ_{i∈delete(k, j)} max(d(i) - c(i), &0)",
									By(ih.At(rest, d.Apply(j), b), finite_set.FiniteDeleteImp.At(k, j), finite, fewer, past, others))
								br.Show(
									"and d(j) - a is less than the length of the interval at j",
									ByArith(split, shorter, holdsA, real_sup_inf.MaxUpperBound.At(length, zero)))
							})
					})
			}))
		arg.Show(
			"a finite family of intervals has some number of members",
			By(byCount))
	}),
})}

// CountableCoverLength — a closed interval covered by a sequence of open
// intervals is shorter than the total length of some initial segment of
// them. The interval ⟦a, b⟧ is compact and the open intervals cover it,
// so finitely many of them do — those at a finite set u of indices. By
// FiniteCoverLength they are longer than ⟦a, b⟧, and u lies in some
// segment 0 .. N, over which the sum of the nonnegative lengths is no
// smaller.
var CountableCoverLength = countableCoverLengthThm{family.Add(registry.ProofEntry{
	Name: "CountableCoverLength",
	Key:  "prop_affc099a395ac953",
	Build: family.Theorem(Statement{
		Binders: "∀c d:(num → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ ∃n:num. c(n) < x ∧ x < d(n)",
		},
		Conclusion: "∃N:num. b - a < Σ_{n∈0 .. N} max(d(n) - c(n), &0)",
		Abbrev: Abbrev{
			{Name: "interval", Text: "λn:num. ⟬c(n), d(n)⟭"},
		},
	}, func(arg *Argument, c, d *Arrow[Nat, Real], a, b *Expr[Real], ordered, covered Fact) {
		open := arg.Have(
			"each of the intervals is open",
			"image(«interval», 𝕌) ⊆ real_topology",
			By(set_image.ImageSubsetIff, real_topology.OpenIntervalOpen))
		covering := arg.Have(
			"together they cover ⟦a, b⟧",
			"⟦a, b⟧ ⊆ ⋃image(«interval», 𝕌)",
			BySets(covered))
		D, finitely := arg.ObtainAs[Set[Set[Real]]](
			"⟦a, b⟧ is compact, so finitely many of them already cover it",
			"∃D:set(set(real)). D ⊆ image(«interval», 𝕌) ∧ finite(D) ∧ ⟦a, b⟧ ⊆ ⋃D",
			By(compact.CompactInDef, real_topology.ClosedIntervalCompact.At(a, b), open, covering))
		u, indexed := arg.ObtainAs[Set[Nat]](
			"they are the intervals at a finite set u of indices",
			"∃u:set(num). finite(u) ∧ D ⊆ image(«interval», u)",
			By(
				finitely,
				finite_set.FiniteSubsetImageImp.At(
					arg.TermAs[Fun[Nat, Set[Real]]]("«interval»"),
					arg.TermAs[Set[Nat]]("𝕌"),
					D)))
		coversU := arg.Have(
			"the intervals at u cover ⟦a, b⟧",
			"∀x:real. a ≤ x ∧ x ≤ b ⇒ ∃i:num. i ∈ u ∧ c(i) < x ∧ x < d(i)",
			BySets(indexed, finitely))
		shorter := arg.Have(
			"so they are longer than ⟦a, b⟧",
			"b - a < Σ_{i∈u} max(d(i) - c(i), &0)",
			By(FiniteCoverLength.At(c, d, u, a, b), indexed, ordered, coversU))
		N, bounded := arg.ObtainAs[Nat](
			"the finite set u lies in a segment 0 .. N",
			"∃N:num. u ⊆ 0 .. N",
			By(num_segment.FiniteIffBounded.At(u), indexed))
		arg.Take(N)
		total := arg.BigOpAs[Nat, Real]("Σ_{n∈0 .. N} max(d(n) - c(n), &0)")
		arg.Show(
			"the intervals at the rest of 0 .. N add a nonnegative amount",
			ByArith(
				shorter,
				bounded,
				real_sum.Subset.At(u, total.Range(), total.Summand()),
				num_segment.Finite.At(arg.TermAs[Nat]("0"), N),
				real_sup_inf.MaxUpperBound))
	}),
})}
