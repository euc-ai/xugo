// fold.go — a sum of vectors: how the vectors reach the fold, and how
// the fold reads one coordinate at a time.
//
// `iterate/monoidal` is carrier-free: it asks of an operation only that
// it commute, associate, and have a neutral element, and everything it
// proves is proved from those three. So a carrier reaches the whole
// mechanism through exactly two facts — that its operation folds, and
// which element it folds from — and once they are in hand every law of
// the mechanism instantiates there for the asking. That is why this
// chapter mints no sum of its own: a sum of vectors IS
// `iterated_op(vec_add, s, F)`, and the first two members below are the
// entire translation. Both are the pointwise laws re-read, in the order
// the mechanism needs them: the neutral element first, because
// `monoidal_op`'s identity conjunct speaks of `neutral_elem(op)` — the
// element the fold actually starts from — and not of `vec_zero`, so the
// chapter's unit law cannot engage it until the element the choice names
// is known to be the zero vector. `comm_ring`'s `NeutralAdd` /
// `MonoidalAdd` are the same two members at the ring's own addition.
//
// How a fold of vectors reads at one index is the mechanism speaking
// across TWO carriers, which is `monoidal.Homomorphic`. It reads there
// as a fold of scalars: evaluation at an index is a homomorphism from
// the vectors to the ring — it carries `vec_add` to `add` by the
// definition, and the zero vector to the ring's zero — and `IterateAt`
// is that law read at evaluation, with those two facts as its
// obligations and no induction of its own. The two folds in its
// statement are genuinely different terms, `iterated_op` at the carrier
// `num → A` on the left and at `A` on the right, which is what the law's
// second carrier letter is for. The first things a coordinatewise
// fold buys are the two halves of the standard basis: a combination of
// basis vectors has its coefficients as coordinates
// (`BasisCombinationAt`), and a vector is the combination with its own
// coordinates (`BasisExpansion`).

package vec_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// NeutralVecAdd — the element pointwise addition folds from is the zero
// vector.
//
// `neutral_elem op` is a Hilbert choice: it names SOME two-sided identity
// for op and says nothing about which. Nothing more is needed, because
// an identity is unique. Write z for the element chosen. Both z and the
// zero vector are two-sided identities — z by the definition, the zero
// vector by the chapter's unit law read on both sides — so testing the
// two against each other at `vec_add(z, vec_zero)` gives
// z = vec_zero.
var NeutralVecAdd = neutralVecAddThm{family.Add(registry.ProofEntry{
	Name: "NeutralVecAdd",
	Key:  "prop_4f665d3abdb04db0",
	Build: comm_ring.CommRing.Law("neutral_elem(vec_add) = vec_zero",
		func(a *Argument, ring Fact) {
			right := a.Have(
				"the zero vector is a right identity as well, by commutativity",
				"∀u:(num → A). u + vec_zero = u",
				By(Normalized, AddLeftZero, AddComm, ring))
			// Unfolding leaves the ε-term itself on the goal's left. Its
			// defining predicate demands an identity on both sides, and the
			// two unit laws supply exactly that at the zero vector.
			a.Do(Unfold(monoidal.NeutralElemDef))
			a.Show(
				"an identity is unique",
				By(AddLeftZero, right, ring))
		}),
})}

// MonoidalVecAdd — pointwise addition folds: it commutes, it associates,
// and the zero vector is its neutral element. With these three the
// mechanism's laws are available at vectors — the recursion over a
// range, the closure of a fold under a predicate, the delta sum — and
// no vector sum of this chapter's own is needed to state them. The
// third clause speaks of the element the choice names, `neutral_elem(vec_add)`:
// read it as the zero vector, and the zero vector is a left identity.
var MonoidalVecAdd = monoidalVecAddThm{family.Add(registry.ProofEntry{
	Name: "MonoidalVecAdd",
	Key:  "prop_2c4d80bcbdb49da3",
	Build: comm_ring.CommRing.Law("monoidal_op(vec_add)",
		func(a *Argument, ring Fact) {
			a.Do(Unfold(monoidal.MonoidalOpDef), SplitConjAll(
				Case(
					"commutativity",
					By(AddComm, ring)),
				Case(
					"associativity",
					By(AddAssoc, ring)),
				Case(
					"the element the fold starts from is the zero vector, a left identity",
					Simp(Fwd(NeutralVecAdd)),
					By(AddLeftZero, ring)),
			))
		}),
})}

// IterateAt — a fold of vectors is computed coordinatewise.
//
// The induction is not here. Evaluation at a fixed index is a monoid
// homomorphism from the vectors to the ring, and `monoidal.Homomorphic`
// carries a fold along one. What this chapter owes that law is four
// facts: that pointwise addition folds, that the ring's own addition
// does, and the two halves of the homomorphism — that evaluation fixes
// the element the fold starts from, the zero vector's entry at the
// index being the ring's zero, and that it crosses the operation, which
// is `vec_add`'s definition read at that one index. Nothing else about
// evaluation is used.
var IterateAt = iterateAtThm{family.Add(registry.ProofEntry{
	Name: "IterateAt",
	Key:  "prop_ffa4a06684e90508",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀s:set(num). ∀F:(num → num → A). ∀j:num.",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "(Σ_{i∈s} F(i))(j) = Σ_{i∈s} F(i, j)",
		},
		func(a *Argument, ring Fact, s *Expr[Set[Nat]], F *Arrow2[Nat, Nat, A],
			j *Expr[Nat], finite Fact) {
			// The map the transfer law is applied at. The goal states its
			// β-reduct, so no slot of the goal spells it and it is pinned by
			// name where the law is applied.
			evaluateAtJ := a.TermAs[Fun[Fun[Nat, A], A]]("λv:(num → A). v(j)")

			// The four facts the law asks of a homomorphism, in its own
			// words: that each operation folds — the two structure laws
			// read under the ring, where the law is applied — and the
			// two halves of the homomorphism. Its fifth demand, that the
			// index set be finite, is this statement's own hypothesis.
			fixesNeutral := a.Have(
				"evaluation at j carries the element the vector fold "+
					"starts from to the one the scalar fold starts from",
				"neutral_elem(vec_add, j) = neutral_elem(R.add)",
				By(Normalized, NeutralVecAdd, comm_ring.NeutralAdd, VecZeroDef, ring))
			crossesAddition := a.Have(
				"and it crosses the operation, an entry of a sum being the sum of the entries",
				"∀u v:(num → A).(u + v)(j) = u(j) + v(j)",
				Cite(VecAddDef))

			a.Show(
				"so the transfer law carries evaluation at j across the fold",
				By(
					MonoidalVecAdd.Read(ring),
					comm_ring.MonoidalAdd.Read(ring),
					fixesNeutral,
					crossesAddition,
					finite,
					Where(monoidal.Homomorphic, "h", evaluateAtJ)))
		}),
})}

// BasisCombinationAt — a combination of the first m basis vectors
// reads, at an index below m, its coefficient there: the coordinates of
// Σ_{i<m} c(i) • basis_vector(i) are the c(j).
//
// At a fixed j the fold reads coordinatewise: IterateAt carries the
// vector fold to the scalar fold of the j-th entries, the entry of
// c(i) • basis_vector(i) at j is c(i) when i = j and the ring's zero
// otherwise, and the delta sum keeps only the surviving term, which is
// c(j) because j lies in the range.
var BasisCombinationAt = basisCombinationAtThm{family.Add(registry.ProofEntry{
	Name: "BasisCombinationAt",
	Key:  "prop_f0cacce6df8031b",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀m j:num. ∀c:(num → A).",
			Hypotheses: []string{
				"j < m",
			},
			Conclusion: "(Σ_{i<m} c(i) • basis_vector(i))(j) = c(j)",
		},
		func(a *Argument, ring Fact, m, j *Expr[Nat], c *Arrow[Nat, A], below Fact) {
			// Stated as a Have rather than read at the ring: the case below
			// cites it beside a monoid law, and there the reading costs a
			// refutation the Have does not.
			monoid := a.Have(
				"the ring's multiplication is a commutative monoid",
				"comm_monoid(R.mul, R.one)",
				By(comm_ring.MulMonoid, ring))
			finite := a.Have(
				"the index range is finite",
				"finite({i:num | i < m})",
				By(num_segment.FiniteBelowStrict))
			inRange := a.Have(
				"j lies in the range",
				"j ∈ {i:num | i < m}",
				BySets(below))
			kronecker := a.Have(
				"at j each summand is the coefficient at its index, and zero off it",
				"∀i:num.(c(i) • basis_vector(i))(j) = COND(i = j, c(i), neutral_elem(R.add))",
				Derive(func(b *Argument) {
					b.Fix("i")
					b.Do(Unfold(VecScalarMulDef), Unfold(BasisVectorDef))
					b.Cases(b.Term("i = j"))
					b.When(
						"i = j: the basis entry is one, and the scalar is unchanged",
						func(d *Argument, eq Fact) {
							d.Show(
								"the scalar times one is the scalar",
								By(Normalized, eq, monoid, comm_monoid.RightIdentity))
						})
					b.Otherwise(
						"¬(i = j): the basis entry is zero, and the product vanishes to the neutral",
						func(d *Argument, neq Fact) {
							d.Show(
								"the scalar times zero is the ring's zero, the additive neutral",
								By(Normalized, neq, ring, comm_ring.MulRightZero, comm_ring.NeutralAdd))
						})
				}))
			a.Show(
				"read the fold at j coordinatewise, then collapse the delta sum",
				CalcEq(
					Leg(
						a.Term("Σ_{i<m} (c(i) • basis_vector(i))(j)"),
						"the vector fold at j is the scalar fold of the j-th entries",
						By(ring, finite, IterateAt)),
					Leg(
						a.Term("Σ_{i<m} COND(i = j, c(i), neutral_elem(R.add))"),
						"each entry is that Kronecker delta",
						Congr(),
						Funext(),
						By(kronecker)),
					Leg(
						a.Term("COND(j ∈ {i:num | i < m}, c(j), neutral_elem(R.add))"),
						"the delta sum keeps only the surviving term",
						// The value kept is c read at j, which the goal's
						// β-reduct does not spell, so Delta's summand binder is
						// pinned by name.
						By(comm_ring.MonoidalAdd.Read(ring), Where(monoidal.Delta, "f", c))),
					FinalLeg(
						"and j lies in the range, so that term is c(j)",
						By(inRange)),
				))
		}),
})}

// BasisExpansion — an m-vector is the fold of its coordinates scaling
// the standard basis vectors.
//
// Both sides are m-vectors — x by hypothesis, and the fold because each
// summand `x(i) • basis_vector(i)` is one for an index in the range (a
// scalar multiple of a basis vector inside its dimension) and a fold of
// m-vectors is an m-vector — so Extensionality reduces the equation to
// agreement on the active range. Below m the fold reads x(j) at j, which
// is BasisCombinationAt with the coordinates of x as the coefficients;
// that agreement uses no hypothesis. The membership hypothesis is spent
// once, in the framing.
var BasisExpansion = basisExpansionThm{family.Add(registry.ProofEntry{
	Name: "BasisExpansion",
	Key:  "prop_ca75462a5cf15d5b",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀m:num. ∀x:(num → A).",
			Hypotheses: []string{
				"vec⟨m⟩(x)",
			},
			Conclusion: "x = Σ_{i<m} x(i) • basis_vector(i)",
		},
		func(a *Argument, ring Fact, m *Expr[Nat], x *Arrow[Nat, A], member Fact) {
			// The fold, named for the one cite that takes a Term; the claims
			// below spell it out, as claim text must.
			fold := a.Term("Σ_{i<m} x(i) • basis_vector(i)")

			// The fold is an m-vector: each summand is one for an index in
			// the range, and a fold of m-vectors is an m-vector.
			summands := a.Have(
				"each summand is an m-vector on the range",
				"∀k:num. k ∈ {i:num | i < m} ⇒ vec⟨m⟩(x(k) • basis_vector(k))",
				Derive(func(b *Argument) {
					b.Fix("k")
					inRange := b.Assume()
					below := b.Have(
						"the index lies below m",
						"k < m",
						BySets(inRange))
					// Named rather than left to the apply rung: VecSmul's
					// antecedent is this membership, and the rung asks for the
					// fact that supplies it by name.
					basisMember := b.Have(
						"the basis vector at that index is an m-vector",
						"vec⟨m⟩(basis_vector(k))",
						By(below, VecBasisVector))
					b.Show(
						"so the scalar multiple of that basis vector lies in dimension m",
						By(ring, basisMember, VecSmul))
				}))
			foldMember := a.Have(
				"so the fold is an m-vector",
				"vec⟨m⟩(Σ_{i<m} x(i) • basis_vector(i))",
				By(ring, summands, VecIterate))

			agree := a.Have(
				"the fold agrees with x on the range, reading x's own coordinates there",
				"∀j:num. j < m ⇒ (Σ_{i<m} x(i) • basis_vector(i))(j) = x(j)",
				By(ring, BasisCombinationAt))

			// Extensionality is stated for ANY padding value, not under the
			// ring, so the ring's zero is supplied as its first witness.
			a.Show(
				"so the two m-vectors, agreeing on the range, are equal",
				By(member, foldMember, agree, At(Extensionality, a.Term("R.zero"), m, x, fold)))
		}),
})}
