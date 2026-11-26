// independence.go — what independence forbids, and the standard basis.
//
// The chapter's ring layer, in two halves that do not use each other.
// Negatively, independence is met by an argument walking along a family
// in one form: the first member that falls into the span of those
// before it is already a failure of it. Positively, the standard basis
// is the first family independence holds of: a combination of it has
// its coefficients as coordinates, which is its independence, and an
// n-vector is the combination with its own coordinates, which puts it
// in the span.

package basis

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// IndependentNotInEarlierSpan — in an independent family, no member
// lies in the span of the members before it.
//
// Suppose the member at t is the combination Σ_{i<t} c(i) • e(i). The
// coefficients d — c's below t, minus one at t, zero past it — combine
// the first k members to the zero vector: past t every summand is the
// zero scalar acting, which the fold does not see, so the fold runs no
// further than t; the fold up to t is the fold below t plus the summand
// at t; below t that fold is c's, which is the member itself, and the
// summand at t is its negation. Independence then makes every
// coefficient below k zero, the one at t among them, and that one is
// minus one. Negating both sides, one is zero — which the nontriviality
// hypothesis rules out, and must: over the one-element ring every family
// is independent and every vector is zero.
var IndependentNotInEarlierSpan = independentNotInEarlierSpanThm{family.Add(registry.ProofEntry{
	Name: "IndependentNotInEarlierSpan",
	Key:  "prop_6306bff1b77ac5d",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀k t:num. ∀e:(num → num → A).",
			Hypotheses: []string{
				"R.one ≠ R.zero",
				"vec_independent(k, e)",
				"t < k",
			},
			Conclusion: "e(t) ∉ vec_span(t, e)",
		},
		func(a *Argument, ring Fact, k, t *Expr[Nat], e *Arrow2[Nat, Nat, A],
			nontrivial, independent, below Fact) {
			// Suppose the member at t lies in the span of the members
			// before it. Membership in a span is the span's defining
			// condition read at the vector, so it hands over coefficients.
			notOutside := a.SupposeNot()
			inSpan := a.Have(
				"the member at t lies in the span of the members before it",
				"e(t) ∈ vec_span(t, e)",
				By(notOutside))
			_, realizes := a.Unpack(
				a.Unfolded(a.Unfolded(inSpan, set_basic.SetMemberDef), vec_space.VecSpanDef))

			// The coefficients of a vanishing combination: c's below t,
			// minus one at t, zero past it.
			d, dDef := a.LetAs[Fun[Nat, A]]("d", "λi:num. COND(i < t, c(i), COND(i = t, -R.one, R.zero))")

			// The fold mechanism at pointwise addition, read off the ring.
			folds := vec_space.MonoidalVecAdd.Read(ring)

			upToT := a.Have(
				"t lies below k, so the range up to t ends inside the range below k",
				"suc(t) ≤ k",
				By(below, nat_order.SucLessEqIffLessThan))
			silent := a.Have(
				"past t the coefficient is the ring's zero, whose action is the element the fold starts from",
				"∀j:num. suc(t) ≤ j ∧ j < k ⇒ d(j) • e(j) = neutral_elem(vec_add)",
				Derive(func(b *Argument) {
					b.Fix("j")
					past := b.Assume()
					neither := b.Have(
						"an index past t is neither below t nor t itself",
						"¬(j < t) ∧ ¬(j = t)",
						ByArith(past))
					b.Show(
						"so its coefficient is the ring's zero",
						By(dDef, neither, vec_space.NeutralVecAdd.Read(ring), vec_space.ZeroSmul.Read(ring)))
				}))
			agree := a.Have(
				"below t the coefficient is c's",
				"∀j:num. j ∈ {i:num | i < t} ⇒ d(j) • e(j) = c(j) • e(j)",
				BySets(dDef))
			atT := a.Have(
				"at t the coefficient is minus one, whose action is negation",
				"d(t) • e(t) = -e(t)",
				By(dDef, nat_order.LessThanIrrefl, vec_space.NegIsSmul.Read(ring)))
			belowT := a.Have(
				"so below t the fold is c's",
				"Σ_{i<t} d(i) • e(i) = Σ_{i<t} c(i) • e(i)",
				By(folds, agree, monoidal.Congruence))

			vanishes := a.Have(
				"so the first k members combine with the coefficients d to the zero vector",
				"Σ_{i<k} d(i) • e(i) = vec_zero",
				CalcEq(
					Leg(
						a.Term("Σ_{i<suc(t)} d(i) • e(i)"),
						"past t every summand is silent, so the fold runs no further than t",
						Symm(),
						By(folds, upToT, silent, monoidal.BelowTruncate)),
					Leg(
						a.Term("Σ_{i<t} d(i) • e(i) + d(t) • e(t)"),
						"the range up to t is the range below t with t laid in",
						By(folds, monoidal.BelowClauses)),
					Leg(
						a.Term("e(t) + -e(t)"),
						"below t the fold is c's, which is the member at t; at t the summand is its negation",
						By(belowT, realizes, atT)),
					FinalLeg(
						"and a vector plus its negation is the zero vector",
						By(vec_space.AddComm.Read(ring), vec_space.AddLeftNeg.Read(ring))),
				))

			// Independence, read by its definition, speaks of every
			// coefficient sequence, d among them.
			independence := a.Unfolded(independent, VecIndependentDef)
			minusOne := a.Have(
				"so every coefficient of d below k is zero, the one at t among them, and that one is minus one",
				"-R.one = R.zero",
				By(independence.At(d), vanishes, below, dDef, nat_order.LessThanIrrefl))

			// The ring's addition is a group, read off the ring.
			addGroup := abelian_group.Group.Read(comm_ring.AddGroup.Read(ring))
			oneIsZero := a.Have(
				"negating both sides, one is zero",
				"R.one = R.zero",
				CalcEq(
					Leg(
						a.Term("-(-R.one)"),
						"one is the negation of its negation",
						Symm(),
						By(group.InvInv.Read(addGroup))),
					Leg(
						a.Term("-R.zero"),
						"and minus one is zero",
						By(Normalized, minusOne)),
					FinalLeg(
						"and zero is its own negation",
						By(group.InvOne.Read(addGroup))),
				))
			a.Show(
				"which the ring's nontriviality forbids",
				By(oneIsZero, nontrivial))
		}),
})}

// ReplacementPivot — expand a member of an independent family in
// another family that agrees with it below that member's index, and
// some coefficient at or past the index is not zero.
//
// Were every coefficient from t on zero, the expansion of e(t) would
// stop before t — from t on every summand is the zero scalar acting,
// which the fold does not see — and below t the other family is e
// itself, so e(t) would be a combination of the members of e before it,
// which IndependentNotInEarlierSpan forbids. This is where a replacement
// argument finds the member to exchange: a nonzero coefficient, at an
// index not yet replaced.
var ReplacementPivot = replacementPivotThm{family.Add(registry.ProofEntry{
	Name: "ReplacementPivot",
	Key:  "prop_dc45ccd215445105",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀k m t:num. ∀e g:(num → num → A). ∀c:(num → A).",
			Hypotheses: []string{
				"R.one ≠ R.zero",
				"vec_independent(k, e)",
				"t < k",
				"t ≤ m",
				"∀i:num. i < t ⇒ g(i) = e(i)",
				"e(t) = Σ_{i<m} c(i) • g(i)",
			},
			Conclusion: "∃j:num. t ≤ j ∧ j < m ∧ c(j) ≠ R.zero",
		},
		func(a *Argument, ring Fact, k, m, t *Expr[Nat], e, g *Arrow2[Nat, Nat, A], c *Arrow[Nat, A],
			nontrivial, independent, below, within, agree, expansion Fact) {
			notInEarlierSpan := a.Have(
				"e(t) is not a combination of the members of e before it",
				"e(t) ∉ vec_span(t, e)",
				By(ring, nontrivial, independent, below, IndependentNotInEarlierSpan))
			silentFromT := a.SupposeNot()

			folds := vec_space.MonoidalVecAdd.Read(ring)
			silent := a.Have(
				"from t on every coefficient is zero, whose action is the element the fold starts from",
				"∀j:num. t ≤ j ∧ j < m ⇒ c(j) • g(j) = neutral_elem(vec_add)",
				Derive(func(b *Argument) {
					b.Fix("j")
					between := b.Assume()
					isZero := b.Have(
						"so its coefficient is zero",
						"c(j) = R.zero",
						By(silentFromT, between))
					b.Show(
						"and the zero scalar sends every vector to the element the fold starts from",
						By(Normalized, isZero, vec_space.ZeroSmul.Read(ring), vec_space.NeutralVecAdd.Read(ring)))
				}))
			sameBelow := a.Have(
				"below t the other family is e",
				"∀j:num. j ∈ {i:num | i < t} ⇒ c(j) • g(j) = c(j) • e(j)",
				Derive(func(b *Argument) {
					b.Fix("j")
					inRange := b.Assume()
					belowT := b.Have(
						"j lies below t",
						"j < t",
						BySets(inRange))
					same := b.Have(
						"where the two families agree",
						"g(j) = e(j)",
						By(belowT, agree))
					b.Show(
						"so the one member is the other",
						same.Rw(),
						Basic())
				}))
			stopsAtT := a.Have(
				"so the expansion of e(t) is a combination of e's members before t",
				"e(t) = Σ_{i<t} c(i) • e(i)",
				CalcEq(
					Leg(
						a.Term("Σ_{i<m} c(i) • g(i)"),
						"e(t)'s expansion",
						By(expansion)),
					Leg(
						a.Term("Σ_{i<t} c(i) • g(i)"),
						"from t on the summands are silent, so the fold stops before t",
						Symm(),
						By(folds, within, silent, monoidal.BelowTruncate)),
					FinalLeg(
						"and below t the other family is e",
						By(folds, sameBelow, monoidal.Congruence)),
				))
			inEarlierSpan := a.Have(
				"which puts e(t) in the span of those members",
				"e(t) ∈ vec_span(t, e)",
				stopsAtT.Rw(),
				By(vec_space.CombinationInSpan.Read(ring).At(t, e, c)))
			a.Show(
				"contradicting independence",
				By(notInEarlierSpan, inEarlierSpan))
		}),
})}

// StandardBasis — the first n standard basis vectors are a basis of the
// n-vectors.
//
// Independence is a coordinate reading. A combination of the first n
// basis vectors has its coefficient c(j) as its coordinate at any j
// below n, and the zero vector has zero there; so a combination that is
// the zero vector has every coefficient on the range zero.
//
// The span is the n-vectors, one inclusion each way. A combination of
// n-vectors is an n-vector, and each of the first n basis vectors is
// one; and an n-vector is the combination of the basis vectors with its
// own coordinates as coefficients, which is the basis expansion.
var StandardBasis = standardBasisThm{family.Add(registry.ProofEntry{
	Name: "StandardBasis",
	Key:  "prop_d92d017d7c7d32d5",
	Build: comm_ring.CommRing.Law("∀n:num. vec_basis(n, basis_vector, {u:(num → A) | vec⟨n⟩(u)})",
		func(a *Argument, ring Fact, n *Expr[Nat]) {
			// The definition's two conjuncts, each a fact in hand below;
			// opening the definition at the end, the close names them.
			independent := a.Have(
				"the first n basis vectors are independent: a combination "+
					"of them reads its coefficients as its coordinates",
				"vec_independent(n, basis_vector)",
				Derive(func(b *Argument) {
					b.Do(Unfold(VecIndependentDef))
					b.Fix("c")
					vanishes := b.Assume()
					b.Fix("j")
					below := b.Assume()
					b.Show(
						"at j the combination reads c(j), and the zero vector reads zero",
						CalcEq(
							Leg(
								b.Term("(Σ_{i<n} c(i) • basis_vector(i))(j)"),
								"the coordinate of the combination at j is its coefficient there",
								Symm(),
								By(ring, below, vec_space.BasisCombinationAt)),
							Leg(
								b.Term("vec_zero(j)"),
								"and the combination is the zero vector, read at the same index",
								Congr(),
								By(vanishes)),
							FinalLeg(
								"whose every coordinate is zero",
								By(vec_space.VecZeroDef)),
						))
				}))

			inside := a.Have(
				"everything the first n basis vectors span is an n-vector",
				"vec_span(n, basis_vector) ⊆ {u:(num → A) | vec⟨n⟩(u)}",
				Derive(func(b *Argument) {
					b.Do(Unfold(set_basic.SubsetDef))
					b.Fix("x")
					inSpan := b.Assume()
					members := b.Have(
						"each of the first n basis vectors is an n-vector",
						"∀i:num. i < n ⇒ vec⟨n⟩(basis_vector(i))",
						By(vec_space.VecBasisVector))
					isVector := b.Have(
						"so x is an n-vector, a span of n-vectors being made of them",
						"vec⟨n⟩(x)",
						By(ring, members, inSpan, vec_space.SpanVec))
					b.Show(
						"which is membership in the set of n-vectors",
						BySets(isVector))
				}))

			reaches := a.Have(
				"every n-vector is a combination of the first n basis vectors",
				"{u:(num → A) | vec⟨n⟩(u)} ⊆ vec_span(n, basis_vector)",
				Derive(func(b *Argument) {
					b.Do(Unfold(set_basic.SubsetDef))
					// x is fixed as a vector of the statement's dimension —
					// the letter N anchored to the binder n — and paired with
					// its membership, so the expansion's cite writes the
					// dimension off x instead of spelling it.
					x := b.VecFixAs[A, DimN]("x")
					inSet := b.Assume()
					isVector := b.Have(
						"x is an n-vector",
						"vec⟨n⟩(x)",
						BySets(inSet))
					xN := proof.Inhabit(x, isVector)
					basisVectors := b.TermAs[Fun2[Nat, Nat, A]]("basis_vector")
					combination := b.Have(
						"the combination of the basis vectors with x's coordinates lies in their span",
						"Σ_{i<n} x(i) • basis_vector(i) ∈ vec_span(n, basis_vector)",
						By(vec_space.CombinationInSpan.Read(ring).At(n, basisVectors, x)))
					expansion := b.Have(
						"and that combination is x",
						"Σ_{i<n} x(i) • basis_vector(i) = x",
						Symm(),
						By(vec_space.BasisExpansion.Read(ring).At(xN)))
					b.Show(
						"so x is in the span",
						expansion.Rw(),
						By(combination))
				}))

			span := a.Have(
				"so the span of the first n basis vectors is the n-vectors",
				"vec_span(n, basis_vector) = {u:(num → A) | vec⟨n⟩(u)}",
				By(inside, reaches, set_order.SubsetAntisym))
			a.Show(
				"independent, and spanning exactly the n-vectors",
				Unfold(VecBasisDef),
				By(independent, span))
		}),
})}
