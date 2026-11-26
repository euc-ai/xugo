package sigma_algebra

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// SigmaFiniteOperations — a sigma algebra contains the empty set and is closed under
// binary unions, intersections and differences. A sequence taking two values gives
// the union; relative complements give the remaining operations.
var SigmaFiniteOperations = sigmaFiniteOperationsThm{family.Add(registry.ProofEntry{
	Name: "SigmaFiniteOperations",
	Key:  "prop_645f65a8171a9695",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)"},
		Conclusion: "∅ ∈ S ∧ (∀s t:set(A). s ∈ S ∧ t ∈ S ⇒ s ∪ t ∈ S ∧ s ∩ t ∈ S ∧ s ∖ t ∈ S)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], sigma Fact) {
		laws := a.Conjuncts(
			a.Unfolded(sigma, SigmaAlgebraOnDef),
			"Every measurable set lies in the carrier",
			"The carrier is measurable",
			"Relative complements are measurable",
			"Countable unions are measurable")
		inside, carrier, complements, countable := laws[0], laws[1], laws[2], laws[3]
		unions := a.Have(
			"Two values of a sequence give a binary union",
			"∀s t:set(A). s ∈ S ∧ t ∈ S ⇒ s ∪ t ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Set[A]]("s")
				b.FixAs[Set[A]]("t")
				members := b.Assume()
				q, qDef := b.LetAs[Fun[Nat, Set[A]]]("q", "λn:num. COND(n = 0, s, t)")
				terms := b.Have(
					"Each term is one of the two measurable sets",
					"∀n:num. q(n) ∈ S",
					By(qDef, members))
				union := b.Have(
					"The sequence has precisely the desired union",
					"⋃image(q, 𝕌) = s ∪ t",
					BySets(qDef, peano.SucNotZero.At(b.TermAs[Nat]("0"))))
				b.Show(
					"Countable union closure gives the binary union",
					By(Normalized, countable.At(q), terms, union))
			}))
		intersections := a.Have(
			"De Morgan gives binary intersections",
			"∀s t:set(A). s ∈ S ∧ t ∈ S ⇒ s ∩ t ∈ S",
			Derive(func(b *Argument) {
				s := b.FixAs[Set[A]]("s")
				t := b.FixAs[Set[A]]("t")
				members := b.Assume()
				deMorgan := b.Have(
					"Relative complements express the intersection",
					"s ∩ t = Ω ∖ ((Ω ∖ s) ∪ (Ω ∖ t))",
					BySets(inside, members))
				b.Show(
					"Complement the union of the two complements",
					By(
						members,
						complements.At(s),
						complements.At(t),
						unions.At(b.TermAs[Set[A]]("Ω ∖ s"), b.TermAs[Set[A]]("Ω ∖ t")),
						complements.At(b.TermAs[Set[A]]("(Ω ∖ s) ∪ (Ω ∖ t)")),
						deMorgan))
			}))
		a.Show(
			"The empty set and the three binary operations are measurable",
			SplitConj(
				Case(
					"The complement of the carrier is empty",
					By(Normalized, carrier, complements.At(Ω), set_algebra.DiffEqEmpty.At(Ω))),
				Case(
					"Difference is intersection with a relative complement",
					Derive(func(b *Argument) {
						s := b.FixAs[Set[A]]("s")
						t := b.FixAs[Set[A]]("t")
						members := b.Assume()
						difference := b.Have(
							"The relative complement removes exactly the points of t",
							"s ∖ t = s ∩ (Ω ∖ t)",
							BySets(inside, members))
						b.Show(
							"Union, intersection and difference stay in the sigma algebra",
							By(
								Normalized,
								members,
								unions.At(s, t),
								intersections.At(s, t),
								complements.At(t),
								intersections.At(s, b.TermAs[Set[A]]("Ω ∖ t")),
								difference))
					}))))
	}),
})}

// SigmaFiniteIntersection — a σ-algebra on Ω holds the intersection within Ω
// of finitely many of its sets. By induction on the finite index set: over no
// index the intersection within Ω is Ω itself, and one more index cuts it by
// one more set of the σ-algebra, which is closed under binary intersections.
var SigmaFiniteIntersection = sigmaFiniteIntersectionThm{family.Add(registry.ProofEntry{
	Name: "SigmaFiniteIntersection",
	Key:  "prop_16abf9bde0fcaddb",
	Reading: "The intersection is taken within Ω because the intersection over " +
		"an empty index set is the universal set: over M = ∅ the statement says Ω ∈ T.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀T:set(set(A)). ∀M:set(I). ∀E:(I → set(A)).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, T)",
			"finite(M)",
			"∀i:I. i ∈ M ⇒ E(i) ∈ T",
		},
		Conclusion: "Ω ∩ ⋂image(E, M) ∈ T",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		T *Expr[Set[Set[A]]],
		M *Expr[Set[I]],
		E *Arrow[I, Set[A]],
		sigma, finiteM, members Fact,
	) {
		a.Show(
			"a σ-algebra on Ω holds the intersection within Ω of finitely many of its sets",
			ByInduction(
				At(
					finite_set.FiniteInduct.Inst[I](),
					a.TermAs[Set[Set[I]]]("λN:set(I). (∀i:I. i ∈ N ⇒ E(i) ∈ T) ⇒ Ω ∩ ⋂image(E, N) ∈ T")),
				finiteM,
				members,
				Case(
					"over no index the intersection is Ω itself",
					Derive(func(b *Argument) {
						whole := b.Have(
							"the empty intersection leaves Ω",
							"Ω ∩ ⋂image(E, ∅) = Ω",
							BySets())
						b.Show(
							"and Ω lies in T",
							By(whole, sigma, SigmaAlgebraOnDef))
					})),
				Case(
					"one more index cuts the intersection by one more set of T",
					Derive(func(b *Argument) {
						x := b.FixAs[I]("x")
						b.FixAs[Set[I]]("s")
						hypothesis := b.Assume()
						inserted := b.Assume()
						rest := b.Have(
							"the intersection over s lies in T, by the induction hypothesis",
							"Ω ∩ ⋂image(E, s) ∈ T",
							BySets(inserted, hypothesis))
						split := b.Have(
							"the index x cuts it by E(x)",
							"Ω ∩ ⋂image(E, insert(x, s)) = E(x) ∩ (Ω ∩ ⋂image(E, s))",
							Simp(Fwd(set_image.ImageClauses), Fwd(set_algebra.IntersInsert)),
							// ⋂image(E, s) held as one set B, which the set driver would otherwise open.
							BySets(DenotedAs("B", b.TermAs[Set[A]]("⋂image(E, s)"))))
						b.Show(
							"T is closed under intersections",
							split.Rw(),
							By(inserted.At(x), rest, sigma, set_basic.InInsert, SigmaFiniteOperations.At(Ω, T)))
					}))))
	}),
})}
