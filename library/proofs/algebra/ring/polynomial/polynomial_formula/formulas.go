// formulas.go — formulas whose atoms read a predicate off the value of their polynomial in a
// ring: such an atom, and so such a formula, depends only on its free variables; a ring
// homomorphism carrying one predicate to another embeds the atoms and preserves and reflects the
// quantifier-free formulas, and every formula when it is onto; and two rings whose predicates agree
// on the image of every integer agree on the closed quantifier-free formulas.

package polynomial_formula

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialAtomLocal — an atom that reads a predicate P off the value of its
// polynomial in a ring depends only on the polynomial's variables:
// environments that agree there evaluate the polynomial alike.
var PolynomialAtomLocal = polynomialAtomLocalThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAtomLocal",
	Key:  "prop_717a38012be345d7",
	Build: family.Theorem("∀R:ring_ops(A). ∀P:(A → bool). "+
		"    fo_atom_local(integer_polynomial, integer_polynomial_vars, «predicateAtoms»(R, P))",
		func(a *Argument, R *Expr[RingOps[A]], P *Expr[Set[A]]) {
			a.Show(
				"environments that agree on the variables of a polynomial evaluate it alike",
				By(first_order.AtomLocalDef, EvaluationCongruence))
		}),
})}

// PolynomialAtomEmbedding — a ring homomorphism i from R to S under which a
// predicate P on the carrier of R holds exactly where a predicate Q holds at
// the image embeds the atoms reading P off the value of a polynomial in R in
// those reading Q off its value in S: i carries the carrier of R into that of
// S, and the value of a valid polynomial at a legal environment to its value
// at the environment carried along.
var PolynomialAtomEmbedding = polynomialAtomEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAtomEmbedding",
	Key:  "prop_a9cb0a0ecc46fc82",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀i:(A → B). ∀P:(A → bool). ∀Q:(B → bool).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, i)",
			"∀x:A. x ∈ R.carrier ⇒ (P(x) ⇔ Q(i(x)))",
		},
		Conclusion: "fo_atomic_embedding(R.carrier, " +
			"    S.carrier, " +
			"    «predicateAtoms»(R, P), " +
			"    «predicateAtoms»(S, Q), " +
			"    integer_polynomial, " +
			"    integer_polynomial_vars, " +
			"    i)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		i *Arrow[A, B],
		P *Expr[Set[A]],
		Q *Expr[Set[B]],
		hom, carried Fact,
	) {
		ring := ring_homomorphism.Source.Read(hom)
		a.Do(Simp(Fwd(first_order.AtomicEmbeddingDef)))
		a.Do(SplitConj(
			Case(
				"the homomorphism carries the carrier of R into the carrier of S",
				By(ring_homomorphism.MapIn.Read(hom))),
			Case(
				"at a valid polynomial in a legal environment the two atoms agree",
				Derive(func(b *Argument) {
					p := b.FixAs[IntegerPolynomial]("p")
					env := b.FixAs[Fun[Nat, A]]("ρ")
					guards := b.Conjuncts(
						b.Assume(),
						"p is a valid polynomial",
						"ρ is carrier-valued on the variables of p")
					natural := b.Have(
						"the homomorphism carries the evaluation of p along",
						"i(integer_polynomial_eval(R, ρ, p)) = integer_polynomial_eval(S, λv:num. i(ρ(v)), p)",
						By(hom, guards[0], guards[1], EvaluationNatural.At(R, S, i, env, p)))
					inCarrier := b.Have(
						"the evaluation of p lies in the carrier of R",
						"integer_polynomial_eval(R, ρ, p) ∈ R.carrier",
						By(ring, guards[0], guards[1], EvaluationInCarrier.At(R, env, p)))
					b.Show(
						"P holds at the value of p exactly where Q holds "+
							"at its image, the value at the carried environment",
						By(Normalized, natural, inCarrier, carried))
				}))))
	}),
})}

// EnvironmentCongruence — the formulas whose atoms read a predicate P off the value of their
// polynomial in a ring R take one value at environments agreeing on their free variables: such an
// atom depends only on its polynomial's variables, and the first-order congruence theorem lifts
// that to every well-formed formula.
var EnvironmentCongruence = environmentCongruenceThm{family.Add(registry.ProofEntry{
	Name: "EnvironmentCongruence",
	Key:  "prop_1c5abf6280b40868",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀P:(A → bool). ∀ρ σ:(num → A). ∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
			"∀v:num. v ∈ polynomial_formula_fv(φ) ⇒ ρ(v) = σ(v)",
		},
		Conclusion: "fo_eval(R.carrier, «predicateAtoms»(R, P), ρ, φ) ⇔ " +
			"fo_eval(R.carrier, «predicateAtoms»(R, P), σ, φ)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		P *Expr[Set[A]],
		ρ, σ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		wf, agree Fact,
	) {
		a.Show(
			"the atoms depend only on the variables of their polynomials, "+
				"and the first-order congruence theorem lifts that to φ",
			By(
				a.Unfolded(wf, FormulaValidDef),
				a.Unfolded(agree, FormulaVarsDef),
				PolynomialAtomLocal.At(R, P),
				first_order.EvalCongruence.At(
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
					a.TermAs[Set[A]]("R.carrier"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, A], Bool]]("«predicateAtoms»(R, P)"),
					ρ, σ, φ)))
	}),
})}

// QuantifierFreeEmbedding — a ring homomorphism i from R to S under which a predicate P holds on
// the carrier of R exactly where a predicate Q holds at the image preserves and reflects the
// quantifier-free formulas read through P in R and through Q in S, at an environment legal on the
// free variables and the environment carried along: i embeds the atoms, and the first-order
// embedding theorem carries every quantifier-free formula across.
var QuantifierFreeEmbedding = quantifierFreeEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeEmbedding",
	Key:  "prop_ad0be8cabc8bfa67",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀i:(A → B). " +
			"∀P:(A → bool). " +
			"∀Q:(B → bool). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, i)",
			"∀x:A. x ∈ R.carrier ⇒ (P(x) ⇔ Q(i(x)))",
			"polynomial_formula_wf(φ)",
			"fo_qf(φ)",
			"fo_env_ok(R.carrier, polynomial_formula_fv(φ), ρ)",
		},
		Conclusion: "fo_eval(R.carrier, «predicateAtoms»(R, P), ρ, φ) ⇔ " +
			"fo_eval(S.carrier, «predicateAtoms»(S, Q), λv:num. i(ρ(v)), φ)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		i *Arrow[A, B],
		P *Expr[Set[A]],
		Q *Expr[Set[B]],
		ρ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		carried, wf, qf, envOk Fact,
	) {
		a.Show(
			"i embeds the atoms reading P in those reading Q, and "+
				"the first-order embedding theorem carries φ across",
			By(
				hom,
				carried,
				a.Unfolded(wf, FormulaValidDef),
				qf,
				a.Unfolded(envOk, FormulaVarsDef),
				PolynomialAtomEmbedding.At(R, S, i, P, Q),
				first_order.QuantifierFreeEmbedding.At(
					a.TermAs[Set[A]]("R.carrier"),
					a.TermAs[Set[B]]("S.carrier"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, A], Bool]]("«predicateAtoms»(R, P)"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, B], Bool]]("«predicateAtoms»(S, Q)"),
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
					i, ρ, φ)))
	}),
})}

// OntoInvariant — a ring homomorphism i from R onto the carrier of S under which a predicate P
// holds on the carrier of R exactly where a predicate Q holds at the image preserves every formula
// read through P in R and through Q in S, at an environment legal on the free variables and the
// environment carried along: i embeds the atoms, and as it is onto the carrier of S the
// first-order transfer theorem for onto embeddings carries every well-formed formula across.
var OntoInvariant = ontoInvariantThm{family.Add(registry.ProofEntry{
	Name: "OntoInvariant",
	Key:  "prop_b3c93f75eab415ac",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀i:(A → B). " +
			"∀P:(A → bool). " +
			"∀Q:(B → bool). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, i)",
			"∀x:A. x ∈ R.carrier ⇒ (P(x) ⇔ Q(i(x)))",
			"image(i, R.carrier) = S.carrier",
			"polynomial_formula_wf(φ)",
			"fo_env_ok(R.carrier, polynomial_formula_fv(φ), ρ)",
		},
		Conclusion: "fo_eval(R.carrier, «predicateAtoms»(R, P), ρ, φ) ⇔ " +
			"fo_eval(S.carrier, «predicateAtoms»(S, Q), λv:num. i(ρ(v)), φ)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		i *Arrow[A, B],
		P *Expr[Set[A]],
		Q *Expr[Set[B]],
		ρ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		carried, onto, wf, envOk Fact,
	) {
		a.Show(
			"i embeds the atoms reading P in those reading Q onto the carrier "+
				"of S, and the transfer theorem for onto embeddings carries φ across",
			By(
				hom,
				carried,
				onto,
				a.Unfolded(wf, FormulaValidDef),
				a.Unfolded(envOk, FormulaVarsDef),
				PolynomialAtomEmbedding.At(R, S, i, P, Q),
				first_order.OntoEmbedding.At(
					a.TermAs[Set[A]]("R.carrier"),
					a.TermAs[Set[B]]("S.carrier"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, A], Bool]]("«predicateAtoms»(R, P)"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, B], Bool]]("«predicateAtoms»(S, Q)"),
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
					i, ρ, φ)))
	}),
})}

// QuantifierFreeSentenceTransfer — two commutative rings R and S, read through predicates P and Q
// that agree on the image of every integer, agree on every closed quantifier-free formula, at any
// two environments. The atoms of such a formula are listed by valid polynomials in its free
// variables, of which it has none, so each atom is a polynomial with no variables, whose value in
// each ring is the image of its constant coefficient; interpretations that agree on the atoms of a
// quantifier-free formula agree on the formula.
var QuantifierFreeSentenceTransfer = quantifierFreeSentenceTransferThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeSentenceTransfer",
	Key:  "prop_461ea7e630e5cfcd",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀P:(A → bool). " +
			"∀Q:(B → bool). " +
			"∀ρ:(num → A). " +
			"∀σ:(num → B). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"comm_ring_on(S)",
			"∀z:int. P(integer_map(R, z)) ⇔ Q(integer_map(S, z))",
			"polynomial_formula_closed(φ)",
			"fo_qf(φ)",
		},
		Conclusion: "fo_eval(R.carrier, «predicateAtoms»(R, P), ρ, φ) ⇔ " +
			"fo_eval(S.carrier, «predicateAtoms»(S, Q), σ, φ)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		P *Expr[Set[A]],
		Q *Expr[Set[B]],
		ρ *Arrow[Nat, A],
		σ *Arrow[Nat, B],
		φ *Expr[Formula[IntegerPolynomial]],
		ringR comm_ring.CommRingFact[on.R],
		ringS comm_ring.CommRingFact[on.S],
		integers, closed, qf Fact,
	) {
		sentence := a.Conjuncts(
			a.Unfolded(closed, FormulaClosedDef),
			"φ is well formed",
			"φ has no free variable")
		_, listed := a.ObtainAs[list.List[IntegerPolynomial]](
			"the atoms of φ are listed by valid polynomials in its free variables",
			"∃L:list((num → num) → int). "+
				"    polynomial_list_over(polynomial_formula_fv(φ), L) ∧ "+
				"    fo_wf(λp:((num → num) → int). list_member(p, L), φ)",
			By(sentence[0], qf, AtomList.At(φ)))
		atoms := a.Conjuncts(
			listed,
			"L lists valid polynomials in the free variables of φ",
			"L holds every atom of φ")
		members := a.Unfolded(atoms[0], PolynomialListOverDef)
		agree := a.Have(
			"on a member p of L the atom holds in R exactly when it holds in S",
			Statement{
				Binders: "∀p:((num → num) → int).",
				Hypotheses: []string{
					"list_member(p, L)",
				},
				Conclusion: "P(integer_polynomial_eval(R, ρ, p)) ⇔ Q(integer_polynomial_eval(S, σ, p))",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[IntegerPolynomial]("p")
				member := b.Assume()
				noVariable := b.Have(
					"p has no variable, φ having none",
					"integer_polynomial_vars(p) = ∅",
					By(
						Normalized,
						member,
						members.At(p),
						sentence[1],
						set_order.SubsetEmpty.At(b.TermAs[Set[Nat]]("integer_polynomial_vars(p)"))))
				b.Show(
					"in each ring the atom's value is the image of its constant coefficient, where P and Q agree",
					By(
						Normalized,
						integers.At(b.TermAs[Int]("p(λi:num. 0)")),
						noVariable,
						ringR,
						ringS,
						VariableFreeEvaluation.At(R, ρ, p),
						VariableFreeEvaluation.At(S, σ, p)))
			}))
		a.Show(
			"the two interpretations agree on every atom of φ, so on φ",
			By(
				qf,
				atoms[1],
				agree,
				first_order.QuantifierFreeAtomAgreement.At(
					a.TermAs[Set[IntegerPolynomial]]("λq:((num → num) → int). list_member(q, L)"),
					a.TermAs[Set[A]]("R.carrier"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, A], Bool]]("«predicateAtoms»(R, P)"),
					ρ,
					a.TermAs[Set[B]]("S.carrier"),
					a.TermAs[Fun2[IntegerPolynomial, Fun[Nat, B], Bool]]("«predicateAtoms»(S, Q)"),
					σ,
					φ)))
	}),
})}
