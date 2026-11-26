// statements.go — sentence transfer and elementary embeddings of algebraically
// closed fields.

package algebraically_closed_field_transfer

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraically_closed_quantifier_elimination"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// CommonElimination — one quantifier-free formula is a quantifier-free
// equivalent of a given formula over the algebraically closed fields on A and
// over those on B. Quantifiers are eliminated once, in A × B, into which A and
// B inject by pairing with a chosen element of the other type, so the
// equivalent there is one over the fields on either side.
var CommonElimination = commonEliminationThm{family.Add(registry.ProofEntry{
	Name: "CommonElimination",
	Key:  "prop_a33ec1652391179",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
		},
		Conclusion: "∃ψ:fo_formula((num → num) → int). " +
			"    fo_quantifier_free_equivalent(algebraically_closed_field_on, " +
			"        «carrier», " +
			"        ring_formula_atom, " +
			"        integer_polynomial, " +
			"        integer_polynomial_vars, " +
			"        φ, " +
			"        ψ) ∧ " +
			"    fo_quantifier_free_equivalent(algebraically_closed_field_on, " +
			"        «carrier»⟨A:B⟩, " +
			"        ring_formula_atom, " +
			"        integer_polynomial, " +
			"        integer_polynomial_vars, " +
			"        φ, " +
			"        ψ)",
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], wf Fact) {
		ψ, eliminated := a.UnpackAs[Formula[IntegerPolynomial]](
			GroupPremises(
				wf,
				algebraically_closed_quantifier_elimination.QuantifierElimination.At[Prod[A, B]](φ)),
			"ψ")
		a.Take(ψ)
		a.Show(
			"pairing with a chosen element of the other type "+
				"injects A and B into A × B, where ψ is the equivalent",
			By(
				wf,
				eliminated,
				ring_formula.EliminationAlongInjection.At(φ, ψ, a.TermAs[Fun[A, Prod[A, B]]]("λa:A. (a, εb:B. ⊤)")),
				pairs.PairInjectiveLeft.At(a.TermAs[B]("εb:B. ⊤"), a.TermAs[Set[A]]("𝕌")),
				ring_formula.EliminationAlongInjection.At(φ, ψ, a.TermAs[Fun[B, Prod[A, B]]]("λb:B. (εa:A. ⊤, b)")),
				pairs.PairInjectiveRight.At(a.TermAs[A]("εa:A. ⊤"), a.TermAs[Set[B]]("𝕌"))))
	}),
})}

// SentenceTransfer — algebraically closed fields of the same characteristic
// satisfy the same sentences. A sentence φ has a quantifier-free equivalent ψ
// common to the algebraically closed fields on A and those on B, and fields of
// one characteristic agree on every closed quantifier-free formula at their
// zero environments, so SentenceTransferFromCommonEquivalent carries φ from F
// to G.
var SentenceTransfer = sentenceTransferThm{family.Add(registry.ProofEntry{
	Name: "SentenceTransfer",
	Key:  "prop_9ce1235e730263ea",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀G:field_ops(B). ∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"algebraically_closed_field_on(F)",
			"algebraically_closed_field_on(G)",
			"same_characteristic(F, G)",
			"polynomial_formula_closed(φ)",
		},
		Conclusion: "ring_formula_truth(F, φ) ⇔ ring_formula_truth(G, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		G *Expr[FieldOps[B]],
		φ *Expr[Formula[IntegerPolynomial]],
		closedF algebraic_closure.AlgebraicallyClosedFieldFact[on.F],
		closedG algebraic_closure.AlgebraicallyClosedFieldFact[on.G],
		same, sentence Fact,
	) {
		sentenceParts := a.Conjuncts(
			a.Unfolded(sentence, polynomial_formula.FormulaClosedDef),
			"φ is well formed",
			"φ has no free variables")
		ψ, common := a.UnpackAs[Formula[IntegerPolynomial]](
			GroupPremises(sentenceParts[0], CommonElimination.At[A, B](φ)),
			"ψ")
		equivalent := a.Conjuncts(
			common,
			"ψ is a quantifier-free equivalent of φ over the algebraically closed fields on A",
			"and over those on B")
		fieldF := algebraic_closure.FieldOn.Read(closedF)
		fieldG := algebraic_closure.FieldOn.Read(closedG)
		agree := a.Have(
			"F and G, of one characteristic, agree on every closed "+
				"quantifier-free formula at their zero environments",
			Statement{
				Binders: "∀χ:fo_formula((num → num) → int).",
				Hypotheses: []string{
					"fo_wf(integer_polynomial, χ)",
					"fo_qf(χ)",
					"fo_fv(integer_polynomial_vars, χ) = ∅",
				},
				Conclusion: "fo_eval(F.carrier, ring_formula_atom(F), λv:num. F.zero, χ) ⇔ " +
					"fo_eval(G.carrier, ring_formula_atom(G), λv:num. G.zero, χ)",
			},
			Derive(func(b *Argument) {
				χ := b.FixAs[Formula[IntegerPolynomial]]("χ")
				parts := b.Conjuncts(
					b.Assume(),
					"χ is well formed",
					"χ is quantifier-free",
					"χ has no free variables")
				closedχ := b.Have(
					"χ is a sentence",
					"polynomial_formula_closed(χ)",
					By(
						parts[0],
						parts[2],
						polynomial_formula.FormulaClosedDef,
						polynomial_formula.FormulaValidDef,
						polynomial_formula.FormulaVarsDef))
				b.Show(
					"the quantifier-free sentence χ holds in F exactly when it holds in G",
					By(
						fieldF,
						fieldG,
						same,
						closedχ,
						parts[1],
						ring_formula.RingFormulaTruthDef.At(F, χ),
						ring_formula.RingFormulaTruthDef.At(G, χ),
						ring_formula.RingFormulaEvalDef.At(F, b.TermAs[Fun[Nat, A]]("λv:num. F.zero"), χ),
						ring_formula.RingFormulaEvalDef.At(G, b.TermAs[Fun[Nat, B]]("λv:num. G.zero"), χ),
						ring_formula.QuantifierFreeSentenceTransfer.At(F, G, χ)))
			}))
		a.Show(
			"φ passes from F to G through their common quantifier-free equivalent",
			Simp(Fwd(ring_formula.RingFormulaTruthDef), Fwd(ring_formula.RingFormulaEvalDef)),
			By(
				equivalent[0],
				equivalent[1],
				closedF,
				closedG,
				a.Unfolded(sentenceParts[1], polynomial_formula.FormulaVarsDef),
				agree,
				first_order.SentenceTransferFromCommonEquivalent.At(
					a.TermAs[Set[FieldOps[A]]]("algebraically_closed_field_on"),
					a.TermAs[Fun2[FieldOps[A], A, Bool]]("«carrier»"),
					a.TermAs[Fun3[FieldOps[A], IntegerPolynomial, Fun[Nat, A], Bool]]("ring_formula_atom"),
					a.TermAs[Set[FieldOps[B]]]("algebraically_closed_field_on"),
					a.TermAs[Fun2[FieldOps[B], B, Bool]]("«carrier»⟨A:B⟩"),
					a.TermAs[Fun3[FieldOps[B], IntegerPolynomial, Fun[Nat, B], Bool]]("ring_formula_atom"),
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
					F,
					G,
					a.TermAs[Fun[Nat, A]]("λv:num. F.zero"),
					a.TermAs[Fun[Nat, B]]("λv:num. G.zero"),
					φ,
					ψ)))
	}),
})}

// EmbeddingElementary — a homomorphism of algebraically closed fields is
// elementary: a formula holds in the source at an environment exactly when it
// holds in the target at the environment carried along. The homomorphism, one
// to one as every homomorphism of fields is, embeds the ring atoms of the
// source in those of the target, and the formula has a quantifier-free
// equivalent common to the algebraically closed fields on A and those on B, so
// ElementaryFromCommonEquivalent carries it along.
var EmbeddingElementary = embeddingElementaryThm{family.Add(registry.ProofEntry{
	Name: "EmbeddingElementary",
	Key:  "prop_645ef62f00dc4b22",
	Reading: "The target environment is exactly i composed with the source " +
		"environment. This includes pulling existential witnesses back from an " +
		"extension; equal truth of parameter-free sentences alone would not imply it.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀G:field_ops(B). " +
			"∀i:(A → B). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"algebraically_closed_field_on(F)",
			"algebraically_closed_field_on(G)",
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"polynomial_formula_wf(φ)",
			"fo_env_ok(F.carrier, polynomial_formula_fv(φ), ρ)",
		},
		Conclusion: "ring_formula_eval(F, ρ, φ) ⇔ ring_formula_eval(G, λv:num. i(ρ(v)), φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		G *Expr[FieldOps[B]],
		i *Arrow[A, B],
		ρ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		closedF algebraic_closure.AlgebraicallyClosedFieldFact[on.F],
		closedG algebraic_closure.AlgebraicallyClosedFieldFact[on.G],
		hom, wf, legal Fact,
	) {
		fieldF := algebraic_closure.FieldOn.Read(closedF)
		fieldG := algebraic_closure.FieldOn.Read(closedG)
		injective := a.Have(
			"a homomorphism of fields is one-to-one",
			"injective_on(F.carrier, i)",
			By(fieldF, fieldG, hom, ring_homomorphism.FieldHomomorphismInjective.At(F, G, i)))
		embedding := a.Have(
			"so i embeds the ring atoms of F in those of G",
			"fo_atomic_embedding(F.carrier, "+
				"    G.carrier, "+
				"    ring_formula_atom(F), "+
				"    ring_formula_atom(G), "+
				"    integer_polynomial, "+
				"    integer_polynomial_vars, "+
				"    i)",
			By(hom, injective, ring_formula.RingAtomEmbedding.At(F, G, i)))
		ψ, common := a.UnpackAs[Formula[IntegerPolynomial]](
			GroupPremises(wf, CommonElimination.At[A, B](φ)),
			"ψ")
		equivalent := a.Conjuncts(
			common,
			"ψ is a quantifier-free equivalent of φ over the algebraically closed fields on A",
			"and over those on B")
		a.Show(
			"φ passes from F to G along the embedding of their "+
				"atoms, through their common quantifier-free equivalent",
			Simp(Fwd(ring_formula.RingFormulaEvalDef)),
			By(
				equivalent[0],
				equivalent[1],
				closedF,
				closedG,
				embedding,
				a.Unfolded(legal, polynomial_formula.FormulaVarsDef),
				first_order.ElementaryFromCommonEquivalent.At(
					a.TermAs[Set[FieldOps[A]]]("algebraically_closed_field_on"),
					a.TermAs[Fun2[FieldOps[A], A, Bool]]("«carrier»"),
					a.TermAs[Fun3[FieldOps[A], IntegerPolynomial, Fun[Nat, A], Bool]]("ring_formula_atom"),
					a.TermAs[Set[FieldOps[B]]]("algebraically_closed_field_on"),
					a.TermAs[Fun2[FieldOps[B], B, Bool]]("«carrier»⟨A:B⟩"),
					a.TermAs[Fun3[FieldOps[B], IntegerPolynomial, Fun[Nat, B], Bool]]("ring_formula_atom"),
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
					F,
					G,
					i,
					ρ,
					φ,
					ψ)))
	}),
})}
