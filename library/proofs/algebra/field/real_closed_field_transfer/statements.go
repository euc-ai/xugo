// statements.go — sentence transfer and elementary embeddings of real closed
// fields.

package real_closed_field_transfer

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_ring_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_quantifier_elimination"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// CommonElimination — one quantifier-free formula is a quantifier-free
// equivalent of a given formula over the real closed fields on A and over
// those on B, each with its order. Quantifiers are eliminated once, in A × B,
// into which A and B inject by pairing with a chosen element of the other
// type, so the equivalent there is one over the fields on either side.
var CommonElimination = commonEliminationThm{family.Add(registry.ProofEntry{
	Name: "CommonElimination",
	Key:  "prop_be1df7b1399ddd94",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
		},
		Conclusion: "∃ψ:fo_formula((num → num) → int). " +
			"    fo_quantifier_free_equivalent(«realClosed», " +
			"        «carrier», " +
			"        «negative», " +
			"        integer_polynomial, " +
			"        integer_polynomial_vars, " +
			"        φ, " +
			"        ψ) ∧ " +
			"    fo_quantifier_free_equivalent(«realClosed»⟨A:B⟩, " +
			"        «carrier»⟨A:B⟩, " +
			"        «negative»⟨A:B⟩, " +
			"        integer_polynomial, " +
			"        integer_polynomial_vars, " +
			"        φ, " +
			"        ψ)",
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], wf Fact) {
		ψ, eliminated := a.UnpackAs[Formula[IntegerPolynomial]](
			GroupPremises(
				wf,
				real_closed_quantifier_elimination.QuantifierElimination.At[Prod[A, B]](φ)),
			"ψ")
		a.Take(ψ)
		a.Show(
			"pairing with a chosen element of the other type "+
				"injects A and B into A × B, where ψ is the equivalent",
			By(
				wf,
				eliminated,
				ordered_ring_formula.EliminationAlongInjection.At(
					φ, ψ, a.TermAs[Fun[A, Prod[A, B]]]("λa:A. (a, εb:B. ⊤)")),
				pairs.PairInjectiveLeft.At(a.TermAs[B]("εb:B. ⊤"), a.TermAs[Set[A]]("𝕌")),
				ordered_ring_formula.EliminationAlongInjection.At(
					φ, ψ, a.TermAs[Fun[B, Prod[A, B]]]("λb:B. (εa:A. ⊤, b)")),
				pairs.PairInjectiveRight.At(a.TermAs[A]("εa:A. ⊤"), a.TermAs[Set[B]]("𝕌"))))
	}),
})}

// SentenceTransfer — any two real closed fields satisfy the same sentences. A
// sentence φ has a quantifier-free equivalent ψ common to the real closed
// fields on A and those on B, and any two ordered fields agree on every closed
// quantifier-free formula at their zero environments, so
// SentenceTransferFromCommonEquivalent carries φ from F to G.
var SentenceTransfer = sentenceTransferThm{family.Add(registry.ProofEntry{
	Name: "SentenceTransfer",
	Key:  "prop_1553db26aacfa877",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀G:field_ops(B). " +
			"∀ls:(B → B → bool). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"real_closed_field(G, ls)",
			"polynomial_formula_closed(φ)",
		},
		Conclusion: "ordered_ring_formula_truth(F, lt, φ) ⇔ ordered_ring_formula_truth(G, ls, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		G *Expr[FieldOps[B]],
		ls *Arrow2[B, B, Bool],
		φ *Expr[Formula[IntegerPolynomial]],
		closedF real_closed_field.RealClosedFieldFact[on.F],
		closedG real_closed_field.RealClosedFieldFact[on.G],
		sentence Fact,
	) {
		type modelA = Prod[FieldOps[A], Fun2[A, A, Bool]]
		type modelB = Prod[FieldOps[B], Fun2[B, B, Bool]]
		sentenceParts := a.Conjuncts(
			a.Unfolded(sentence, polynomial_formula.FormulaClosedDef),
			"φ is well formed",
			"φ has no free variables")
		ψ, common := a.UnpackAs[Formula[IntegerPolynomial]](
			GroupPremises(sentenceParts[0], CommonElimination.At[A, B](φ)),
			"ψ")
		equivalent := a.Conjuncts(
			common,
			"ψ is a quantifier-free equivalent of φ over the real closed fields on A",
			"and over those on B")
		orderedF := real_closed_field.OrderedFieldOn.Read(closedF)
		orderedG := real_closed_field.OrderedFieldOn.Read(closedG)
		agree := a.Have(
			"F and G, ordered fields, agree on every closed quantifier-free formula at their zero environments",
			Statement{
				Binders: "∀χ:fo_formula((num → num) → int).",
				Hypotheses: []string{
					"fo_wf(integer_polynomial, χ)",
					"fo_qf(χ)",
					"fo_fv(integer_polynomial_vars, χ) = ∅",
				},
				Conclusion: "fo_eval(F.carrier, ordered_ring_formula_atom(F, lt), λv:num. F.zero, χ) ⇔ " +
					"fo_eval(G.carrier, ordered_ring_formula_atom(G, ls), λv:num. G.zero, χ)",
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
					"any two ordered fields agree on the quantifier-free sentence χ",
					By(
						orderedF,
						orderedG,
						closedχ,
						parts[1],
						ordered_ring_formula.OrderedRingFormulaTruthDef.At(F, lt, χ),
						ordered_ring_formula.OrderedRingFormulaTruthDef.At(G, ls, χ),
						ordered_ring_formula.OrderedRingFormulaEvalDef.At(
							F, lt, b.TermAs[Fun[Nat, A]]("λv:num. F.zero"), χ),
						ordered_ring_formula.OrderedRingFormulaEvalDef.At(
							G, ls, b.TermAs[Fun[Nat, B]]("λv:num. G.zero"), χ),
						ordered_ring_formula.QuantifierFreeSentenceTransfer.At(F, lt, G, ls, χ)))
			}))
		a.Show(
			"φ passes from F to G through their common quantifier-free equivalent",
			Simp(
				Fwd(ordered_ring_formula.OrderedRingFormulaTruthDef),
				Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef)),
			By(
				equivalent[0],
				equivalent[1],
				closedF,
				closedG,
				a.Unfolded(sentenceParts[1], polynomial_formula.FormulaVarsDef),
				agree,
				a.Simplified(
					first_order.SentenceTransferFromCommonEquivalent.At(
						a.TermAs[Set[modelA]]("«realClosed»"),
						a.TermAs[Fun2[modelA, A, Bool]]("«carrier»"),
						a.TermAs[Fun3[modelA, IntegerPolynomial, Fun[Nat, A], Bool]]("«negative»"),
						a.TermAs[Set[modelB]]("«realClosed»⟨A:B⟩"),
						a.TermAs[Fun2[modelB, B, Bool]]("«carrier»⟨A:B⟩"),
						a.TermAs[Fun3[modelB, IntegerPolynomial, Fun[Nat, B], Bool]]("«negative»⟨A:B⟩"),
						a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
						a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
						a.TermAs[modelA]("(F, lt)"),
						a.TermAs[modelB]("(G, ls)"),
						a.TermAs[Fun[Nat, A]]("λv:num. F.zero"),
						a.TermAs[Fun[Nat, B]]("λv:num. G.zero"),
						φ,
						ψ),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd))))
	}),
})}

// EmbeddingElementary — a homomorphism of real closed fields is elementary: a
// formula holds in the source at an environment exactly when it holds in the
// target at the environment carried along. The homomorphism is an order
// embedding, so it embeds the ordered atoms of the source in those of the
// target, and the formula has a quantifier-free equivalent common to the real
// closed fields on A and those on B, so ElementaryFromCommonEquivalent carries
// it along.
var EmbeddingElementary = embeddingElementaryThm{family.Add(registry.ProofEntry{
	Name: "EmbeddingElementary",
	Key:  "prop_d73ab07fb6ded505",
	Reading: "The target environment is exactly i composed with the source " +
		"environment. This includes pulling existential witnesses back from an " +
		"extension; equal truth of parameter-free sentences alone would not imply it.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀G:field_ops(B). " +
			"∀ls:(B → B → bool). " +
			"∀i:(A → B). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"real_closed_field(G, ls)",
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"polynomial_formula_wf(φ)",
			"fo_env_ok(F.carrier, polynomial_formula_fv(φ), ρ)",
		},
		Conclusion: "ordered_ring_formula_eval(F, lt, ρ, φ) ⇔ " +
			"ordered_ring_formula_eval(G, ls, λv:num. i(ρ(v)), φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		G *Expr[FieldOps[B]],
		ls *Arrow2[B, B, Bool],
		i *Arrow[A, B],
		ρ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		closedF real_closed_field.RealClosedFieldFact[on.F],
		closedG real_closed_field.RealClosedFieldFact[on.G],
		hom, wf, legal Fact,
	) {
		type modelA = Prod[FieldOps[A], Fun2[A, A, Bool]]
		type modelB = Prod[FieldOps[B], Fun2[B, B, Bool]]
		orderedG := real_closed_field.OrderedFieldOn.Read(closedG)
		embedding := a.Have(
			"i is an order embedding of F into G",
			"ordered_field_embedding(F, lt, G, ls, i)",
			By(orderedG, hom, real_closed_field.HomomorphismOrderEmbedding.Read(closedF).At(G, ls, i)))
		atoms := a.Have(
			"so i embeds the ordered atoms of F in those of G",
			"fo_atomic_embedding(F.carrier, "+
				"    G.carrier, "+
				"    ordered_ring_formula_atom(F, lt), "+
				"    ordered_ring_formula_atom(G, ls), "+
				"    integer_polynomial, "+
				"    integer_polynomial_vars, "+
				"    i)",
			By(
				a.Unfolded(embedding, ordered_field.OrderedEmbeddingDef),
				ordered_ring_formula.OrderedAtomEmbedding.At(F, lt, G, ls, i)))
		ψ, common := a.UnpackAs[Formula[IntegerPolynomial]](
			GroupPremises(wf, CommonElimination.At[A, B](φ)),
			"ψ")
		equivalent := a.Conjuncts(
			common,
			"ψ is a quantifier-free equivalent of φ over the real closed fields on A",
			"and over those on B")
		a.Show(
			"φ passes from F to G along the embedding of their "+
				"atoms, through their common quantifier-free equivalent",
			Simp(Fwd(ordered_ring_formula.OrderedRingFormulaEvalDef)),
			By(
				equivalent[0],
				equivalent[1],
				closedF,
				closedG,
				atoms,
				a.Unfolded(legal, polynomial_formula.FormulaVarsDef),
				a.Simplified(
					first_order.ElementaryFromCommonEquivalent.At(
						a.TermAs[Set[modelA]]("«realClosed»"),
						a.TermAs[Fun2[modelA, A, Bool]]("«carrier»"),
						a.TermAs[Fun3[modelA, IntegerPolynomial, Fun[Nat, A], Bool]]("«negative»"),
						a.TermAs[Set[modelB]]("«realClosed»⟨A:B⟩"),
						a.TermAs[Fun2[modelB, B, Bool]]("«carrier»⟨A:B⟩"),
						a.TermAs[Fun3[modelB, IntegerPolynomial, Fun[Nat, B], Bool]]("«negative»⟨A:B⟩"),
						a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
						a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
						a.TermAs[modelA]("(F, lt)"),
						a.TermAs[modelB]("(G, ls)"),
						i,
						ρ,
						φ,
						ψ),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd))))
	}),
})}
