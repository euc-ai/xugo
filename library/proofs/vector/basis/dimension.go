// dimension.go — the dimension: two bases of one set have one length,
// so the length a basis has is the set's dimension, and the n-vectors
// `{u | vec⟨n⟩(u)}` have dimension n; and there are at most n
// independent n-vectors.
//
// Its centre is the replacement theorem read twice. A basis of s lies in
// the span of any other basis of s, the two spans being s itself, so
// Steinitz bounds each length by the other. The standard basis then ties
// the chapter's dimension to the dimension predicate `vec⟨n⟩(·)` that
// vec_space started from.

package basis

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// BasisLengthUnique — two bases of one set have the same length.
//
// Each basis lies in the span of the other, both spans being the set;
// so Steinitz, read each way round, bounds each length by the other.
var BasisLengthUnique = basisLengthUniqueThm{family.Add(registry.ProofEntry{
	Name: "BasisLengthUnique",
	Key:  "prop_510722b4abf3a5c9",
	Build: field.Field.Law(
		Statement{
			Binders: "∀k m:num. ∀e f:(num → num → A). ∀s:set(num → A).",
			Hypotheses: []string{
				"vec_basis(k, e, s)",
				"vec_basis(m, f, s)",
			},
			Conclusion: "k = m",
		},
		func(a *Argument, fld Fact, k, m *Expr[Nat], e, f *Arrow2[Nat, Nat, A], s *Expr[Set[Fun[Nat, A]]],
			basisE, basisF Fact) {
			ring := field.Ring.Read(fld)
			eParts := a.Conjuncts(
				a.Unfolded(basisE, VecBasisDef),
				"e's first k members are independent",
				"e's span is s")
			fParts := a.Conjuncts(
				a.Unfolded(basisF, VecBasisDef),
				"f's first m members are independent",
				"f's span is s")
			sameSpan := a.Have(
				"so the two spans are one",
				"vec_span(k, e) = vec_span(m, f)",
				eParts[1].Rw(),
				fParts[1].Rw(),
				Basic())

			eInF := a.Have(
				"each of e's first k members lies in f's span",
				"∀i:num. i < k ⇒ e(i) ∈ vec_span(m, f)",
				Derive(func(b *Argument) {
					b.Fix("i")
					below := b.Assume()
					b.Show(
						"it lies in e's own span, which is f's",
						sameSpan.RwRev(),
						By(ring, below, vec_space.SpanMember))
				}))
			fInE := a.Have(
				"and each of f's first m lies in e's",
				"∀i:num. i < m ⇒ f(i) ∈ vec_span(k, e)",
				Derive(func(b *Argument) {
					b.Fix("i")
					below := b.Assume()
					b.Show(
						"it lies in f's own span, which is e's",
						sameSpan.Rw(),
						By(ring, below, vec_space.SpanMember))
				}))

			kAtMostM := a.Have(
				"so by replacement k is at most m",
				"k ≤ m",
				By(Steinitz.Read(fld).At(k, m, e, f), eParts[0], eInF))
			mAtMostK := a.Have(
				"and, the other way round, m at most k",
				"m ≤ k",
				By(Steinitz.Read(fld).At(m, k, f, e), fParts[0], fInE))
			a.Show(
				"so the two lengths are equal",
				ByArith(kAtMostM, mAtMostK))
		}),
})}

// DimBasis — a set with a basis of length k has dimension k: the
// dimension is well defined.
//
// The dimension is the length of SOME basis of s, chosen; s has one, so
// the choice is not vacuous, and the basis it picks has the length of
// the one in hand (BasisLengthUnique).
var DimBasis = dimBasisThm{family.Add(registry.ProofEntry{
	Name: "DimBasis",
	Key:  "prop_c971da2f83be893a",
	Build: field.Field.Law(
		Statement{
			Binders: "∀k:num. ∀e:(num → num → A). ∀s:set(num → A).",
			Hypotheses: []string{
				"vec_basis(k, e, s)",
			},
			Conclusion: "vec_dim(s) = k",
		},
		func(
			a *Argument,
			fld Fact,
			k *Expr[Nat],
			e *Arrow2[Nat, Nat, A],
			s *Expr[Set[Fun[Nat, A]]],
			basis Fact,
		) {
			chosen := a.Have(
				"s has a basis, so the dimension is a length at which it has one",
				"∃f:(num → num → A). vec_basis(vec_dim(s), f, s)",
				Unfold(VecDimDef),
				By(basis))
			f, pickedBasis := a.UnpackAs[Fun2[Nat, Nat, A]](chosen)
			dimension := a.TermAs[Nat]("vec_dim(s)")
			a.Show(
				"and two bases of s have one length",
				By(BasisLengthUnique.Read(fld).At(dimension, k, f, e, s), pickedBasis, basis))
		}),
})}

// DimVec — the n-vectors `{u | vec⟨n⟩(u)}` have dimension n.
//
// The first n standard basis vectors are a basis of them.
var DimVec = dimVecThm{family.Add(registry.ProofEntry{
	Name: "DimVec",
	Key:  "prop_12f9fb5190a502a9",
	Build: field.Field.Law("∀n:num. vec_dim({u:(num → A) | vec⟨n⟩(u)}) = n",
		func(a *Argument, fld Fact, n *Expr[Nat]) {
			ring := field.Ring.Read(fld)
			standard := a.Have(
				"the first n standard basis vectors are a basis of the n-vectors",
				"vec_basis(n, basis_vector, {u:(num → A) | vec⟨n⟩(u)})",
				By(StandardBasis.Read(ring).At(n)))
			a.Show(
				"so that is their dimension",
				By(fld, standard, DimBasis))
		}),
})}

// IndependentBound — there are at most n independent n-vectors.
//
// The first n standard basis vectors span the n-vectors, so k
// independent n-vectors lie in the span of n vectors, and replacement
// bounds k by n.
var IndependentBound = independentBoundThm{family.Add(registry.ProofEntry{
	Name: "IndependentBound",
	Key:  "prop_4fa22d4e30680819",
	Build: field.Field.Law(
		Statement{
			Binders: "∀n k:num. ∀e:(num → num → A).",
			Hypotheses: []string{
				"∀i:num. i < k ⇒ vec⟨n⟩(e(i))",
				"vec_independent(k, e)",
			},
			Conclusion: "k ≤ n",
		},
		func(a *Argument, fld Fact, n, k *Expr[Nat], e *Arrow2[Nat, Nat, A], vectors, independent Fact) {
			ring := field.Ring.Read(fld)
			standard := a.Have(
				"the first n standard basis vectors are a basis of the n-vectors",
				"vec_basis(n, basis_vector, {u:(num → A) | vec⟨n⟩(u)})",
				By(StandardBasis.Read(ring).At(n)))
			spans := a.Have(
				"so they span the n-vectors",
				"vec_span(n, basis_vector) = {u:(num → A) | vec⟨n⟩(u)}",
				By(a.Unfolded(standard, VecBasisDef)))
			inSpan := a.Have(
				"each of e's first k members lies in their span",
				"∀i:num. i < k ⇒ e(i) ∈ vec_span(n, basis_vector)",
				Derive(func(b *Argument) {
					b.Fix("i")
					below := b.Assume()
					isVector := b.Have(
						"it is an n-vector",
						"vec⟨n⟩(e(i))",
						By(below, vectors))
					b.Show(
						"and the span is the n-vectors",
						spans.Rw(),
						BySets(isVector))
				}))
			standardFamily := a.TermAs[Fun2[Nat, Nat, A]]("basis_vector")
			a.Show(
				"so by replacement there are at most n of them",
				By(Steinitz.Read(fld).At(k, n, e, standardFamily), independent, inSpan))
		}),
})}
