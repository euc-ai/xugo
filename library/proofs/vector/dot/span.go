// span.go — what the form says about a whole span, said by checking
// finitely many vectors.
//
// A span is the set of combinations of the first k members of a family,
// so a vector of it is a fold of scalar multiples of those members and
// nothing else. Linearity in the first argument crosses that fold and
// takes each coefficient out of its summand, and what is left is built
// from the pairings against the k members themselves. A subspace
// presented by a family therefore costs no more to test than the family
// does — which is what lets a decomposition speak of a vector
// orthogonal to a subspace without checking it against every vector of
// one.

package dot

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// OrthogonalToSpan — the form carries through a combination, so the k
// checks the hypothesis makes are all the checks there are.
//
// A vector of the span is a combination of the family and nothing else,
// so what must vanish is the form against a single fold. Symmetry puts
// that fold into the argument linearity is stated in; the form crosses
// it, every summand gives up its coefficient, and what remains is a
// fold each of whose summands is a multiple of a pairing the hypothesis
// sends to zero — the element the ring's addition folds from, so the
// fold is that element. The coefficients are quantified away before the
// span is ever opened, which is why nothing about the family is asked
// for: no dimension, no independence, not even that the k members are
// distinct.
var OrthogonalToSpan = orthogonalToSpanThm{family.Add(registry.ProofEntry{
	Name: "OrthogonalToSpan",
	Key:  "prop_8435246ce7fbea45",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀n k:num. ∀e:(num → num → A). ∀z w:(num → A).",
			Hypotheses: []string{
				"∀i:num. i < k ⇒ ⟪z, e(i)⟫_n = R.zero",
				"w ∈ vec_span(k, e)",
			},
			Conclusion: "⟪z, w⟫_n = R.zero",
		},
		func(
			a *Argument,
			ring Fact,
			n, k *Expr[Nat],
			e *Arrow2[Nat, Nat, A],
			z, w *Vec[A, DimN],
			orthogonal, member Fact,
		) {
			combinations := a.Have(
				"z pairs to zero against every combination of the family's first k members",
				"∀c:(num → A). ⟪z, Σ_{i<k} c(i) • e(i)⟫_n = R.zero",
				Derive(func(b *Argument) {
					b.Fix("c")

					vanishing := b.Have(
						"on the range the combination folds over, every summand vanishes",
						"∀i:num. i ∈ {i:num | i < k} ⇒ c(i) * ⟪e(i), z⟫_n = R.zero",
						Derive(func(d *Argument) {
							d.Fix("i")
							inRange := d.Assume()
							below := d.Have(
								"the index is one of the first k",
								"i < k",
								BySets(inRange))
							d.Show(
								"and there z is orthogonal to the family — in either order, "+
									"the form being symmetric — so the summand is a multiple of zero",
								By(orthogonal, below, ring, Sym, comm_ring.MulRightZero))
						}))

					finite := b.Have(
						"the index range is finite",
						"finite({i:num | i < k})",
						Cite(num_segment.FiniteBelowStrict))

					b.Do(CalcEq(
						Leg(
							b.Term("⟪Σ_{i<k} c(i) • e(i), z⟫_n"),
							"the form is symmetric, and it is the first argument that linearity is stated in",
							By(Sym, ring)),
						Leg(
							b.Term("Σ_{i<k} ⟪c(i) • e(i), z⟫_n"),
							"pairing against z carries a fold of vectors to the fold of the pairings",
							By(finite, IterateLeft, ring)),
						Leg(
							b.Term("Σ_{i<k} c(i) * ⟪e(i), z⟫_n"),
							"and each pairing gives up its coefficient",
							Congr(),
							Funext(),
							By(SmulLeft, ring)),
						FinalLeg(
							"and a fold whose every summand is the element it "+
								"starts from is that element, which is the ring's zero",
							By(vanishing, comm_ring.MonoidalAdd, ring, comm_ring.NeutralAdd, monoidal.EqNeutral)),
					))
				}))

			// Membership in a span is the span's defining condition read at
			// the vector: w is a combination, with coefficients c.
			coefficients, realizes := a.Unpack(
				a.Unfolded(a.Unfolded(member, set_basic.SetMemberDef), vec_space.VecSpanDef))
			a.Show(
				"and w is one of those combinations",
				By(realizes, combinations.At(coefficients)))
		}),
})}
