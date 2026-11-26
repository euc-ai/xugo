// statements.go — the Lefschetz principle, the transfer from a family of
// models of every prime characteristic, and the stability results they rest
// on.

package lefschetz

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraically_closed_field_transfer"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_polynomial"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// _ClosureHost is the type the prime-characteristic models live on,
// set(prod(num, num → set(int))): the host on which
// algebraic_closure.AlgebraicClosureFieldOn builds the closure of a field
// whose elements are sets of integers. It is one fixed type because
// Lefschetz stability compares a field of characteristic zero with the
// models of every prime characteristic at a single type.
type _ClosureHost = Set[Prod[Nat, Fun[Nat, Set[Int]]]]

// AtomStability — a closed integer polynomial q vanishes in every field of
// characteristic zero exactly when its constant coefficient c is zero, and in
// a field of prime characteristic p exactly when p divides c; past the bound
// |c| a prime divides c only when c is zero, so the two atoms agree.
var AtomStability = atomStabilityThm{family.Add(registry.ProofEntry{
	Name: "AtomStability",
	Key:  "prop_ed3cbcc0f2f9c865",
	Build: family.Theorem(Statement{
		Binders: "∀q:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial_vars(q) = ∅",
		},
		Conclusion: "∃N:num. ∀F:field_ops(A). ∀G:field_ops(B). ∀p:num. ∀ρ:(num → A). ∀σ:(num → B). " +
			"    «zeroAndPast»(F, G, p, N) ⇒ (ring_formula_atom(F, q, ρ) ⇔ ring_formula_atom(G, q, σ))",
		Abbrev: Abbrev{
			{Name: "c", Text: "q(λi:num. 0)"},
		},
	}, func(a *Argument, q *Arrow[Fun[Nat, Nat], Int], noVariables Fact) {
		c := a.TermAs[Int]("«c»")
		bound := a.TermAs[Nat]("num_of_int(|«c»|)")
		a.Take(bound)
		F := a.FixAs[FieldOps[A]]("F")
		G := a.FixAs[FieldOps[B]]("G")
		p := a.FixAs[Nat]("p")
		ρ := a.FixAs[Fun[Nat, A]]("ρ")
		σ := a.FixAs[Fun[Nat, B]]("σ")
		fields := a.Conjuncts(
			a.Assume(),
			"F is a field",
			"F has characteristic zero",
			"G is a field",
			"G has characteristic p",
			"p exceeds the absolute value of the constant coefficient")
		valueF := a.Have(
			"in F the atom's polynomial, having no variable, "+
				"evaluates to the image of its constant coefficient",
			"integer_polynomial_eval(field_ring(F), ρ, q) = integer_map(field_ring(F), «c»)",
			By(
				fields[0],
				noVariables,
				field.RingOn,
				polynomial_formula.VariableFreeEvaluation.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"), ρ, q)))
		valueG := a.Have(
			"and so in G",
			"integer_polynomial_eval(field_ring(G), σ, q) = integer_map(field_ring(G), «c»)",
			By(
				fields[2],
				noVariables,
				field.RingOn,
				polynomial_formula.VariableFreeEvaluation.At(
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"), σ, q)))
		vanishF := a.Have(
			"in characteristic zero the coefficient vanishes in F only when it is zero",
			"integer_map(field_ring(F), «c») = F.zero ⇔ «c» = &0",
			ByArith(
				fields[0],
				fields[1],
				finite_field.IntegerMapKernel.At(F, a.TermAs[Nat]("0"), c),
				int_divides.IntDividesDef.At(a.TermAs[Int]("0"), c)))
		vanishG := a.Have(
			"in characteristic p the coefficient vanishes in G "+
				"when p divides it, which past |c| means it is zero",
			"integer_map(field_ring(G), «c») = G.zero ⇔ «c» = &0",
			ByArith(
				fields[2],
				fields[3],
				fields[4],
				finite_field.IntegerMapKernel.At(G, p, c),
				int_divides.IntDividesDef.At(a.TermAs[Int]("p"), c),
				int_divides.DivisorBoundedByDividend.At(a.TermAs[Int]("p"), c),
				int_embed.OfNumAbs.At(p),
				int_embed.NumOfIntSection.At(a.TermAs[Int]("|«c»|")),
				int_real_lift.AbsNonneg.At(c),
				int_embed.OfNumLt.At(bound, p)))
		a.Show(
			"both atoms say the constant coefficient is zero",
			Simp(Fwd(ring_formula.RingFormulaAtomDef)),
			By(Normalized, valueF, valueG, vanishF, vanishG))
	}),
})}

// QuantifierFreeStability — a closed quantifier-free sentence takes one truth
// value in every field of characteristic zero and every field of prime
// characteristic past some bound N. By induction on the sentence, at any pair
// of environments: an atom is a closed integer polynomial, whose vanishing is
// stable past some bound; a negation keeps its body's bound, a conjunction
// takes the sum of its conjuncts' bounds, and a quantifier-free sentence has
// no existential.
var QuantifierFreeStability = quantifierFreeStabilityThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeStability",
	Key:  "prop_f07c88a0195d9c63",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_closed(φ)",
			"fo_qf(φ)",
		},
		Conclusion: "∃N:num. ∀F:field_ops(A). ∀G:field_ops(B). ∀p:num. " +
			"    «zeroAndPast»(F, G, p, N) ⇒ (ring_formula_truth(F, φ) ⇔ ring_formula_truth(G, φ))",
		Abbrev: Abbrev{
			{Name: "stableAt", Text: "λθ:fo_formula((num → num) → int). " +
				"∃N:num. " +
				"∀F:field_ops(A). " +
				"∀G:field_ops(B). " +
				"∀p:num. " +
				"∀ρ:(num → A). " +
				"∀σ:(num → B). " +
				"    «zeroAndPast»(F, G, p, N) ⇒ (ring_formula_eval(F, ρ, θ) ⇔ ring_formula_eval(G, σ, θ))"},
			{Name: "stable", Text: "λθ:fo_formula((num → num) → int). " +
				"    fo_wf(integer_polynomial, θ) ∧ fo_qf(θ) ∧ fo_fv(integer_polynomial_vars, θ) = ∅ ⇒ " +
				"    «stableAt»(θ)"},
		},
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], sentence, quantifierFree Fact) {
		unfolded := a.Simplified(
			a.Unfolded(sentence, polynomial_formula.FormulaClosedDef),
			Fwd(polynomial_formula.FormulaValidDef),
			Fwd(polynomial_formula.FormulaVarsDef))
		stable := a.TermAs[Set[Formula[IntegerPolynomial]]]("«stable»")
		// Each Simp below unfolds the evaluation of a formula in F and in G at
		// once, and the recursion on formulas holds at each carrier type
		// separately, so it is read at A and at B.
		evalInF := first_order.EvalDef.Inst(TypeBinder.BindA[IntegerPolynomial](), TypeBinder.BindB[A]())
		evalInG := first_order.EvalDef.Inst(TypeBinder.BindA[IntegerPolynomial](), TypeBinder.BindB[B]())
		N, bound := a.ObtainAs[Nat](
			"past some bound the sentence takes one value in both fields, at any pair of environments",
			"«stableAt»(φ)",
			ByInduction(first_order.FormulaInduction.At(stable, φ), unfolded, quantifierFree,
				Case(
					"an atom is a closed integer polynomial, whose vanishing is stable past some bound",
					Derive(func(b *Argument) {
						b.FixAs[IntegerPolynomial]("q")
						atom := b.Simplified(
							b.Assume(),
							Fwd(first_order.WellFormedDef),
							Fwd(first_order.QuantifierFreeDef),
							Fwd(first_order.FreeVarsDef))
						b.Show(
							"the atom evaluates to the vanishing of its polynomial",
							Simp(Fwd(ring_formula.RingFormulaEvalDef), Fwd(evalInF), Fwd(evalInG)),
							By(atom, AtomStability))
					})),
				Case(
					"a negation keeps its body's bound: past it the bodies agree, so the negations do",
					Derive(func(b *Argument) {
						b.FixAs[Formula[IntegerPolynomial]]("ψ")
						inductive := b.Assume()
						body := b.Simplified(
							b.Assume(),
							Fwd(first_order.WellFormedDef),
							Fwd(first_order.QuantifierFreeDef),
							Fwd(first_order.FreeVarsDef))
						N, agree := b.ObtainAs[Nat](
							"the body's bound",
							"«stableAt»(ψ)",
							By(inductive, body))
						b.Take(N)
						F := b.FixAs[FieldOps[A]]("F")
						G := b.FixAs[FieldOps[B]]("G")
						p := b.FixAs[Nat]("p")
						ρ := b.FixAs[Fun[Nat, A]]("ρ")
						σ := b.FixAs[Fun[Nat, B]]("σ")
						fields := b.Assume()
						evaluations := b.Simplified(agree, Fwd(ring_formula.RingFormulaEvalDef))
						b.Show(
							"a negation is false exactly where its body is true",
							Simp(Fwd(ring_formula.RingFormulaEvalDef), Fwd(evalInF), Fwd(evalInG)),
							By(Normalized, evaluations.At(F, G, p, ρ, σ), fields))
					})),
				Case(
					"a conjunction takes the sum of its conjuncts' bounds, past which both conjuncts agree",
					Derive(func(b *Argument) {
						b.FixAs[Formula[IntegerPolynomial]]("ψ")
						b.FixAs[Formula[IntegerPolynomial]]("χ")
						inductiveψ := b.Assume()
						inductiveχ := b.Assume()
						conjuncts := b.Simplified(
							b.Assume(),
							Fwd(first_order.WellFormedDef),
							Fwd(first_order.QuantifierFreeDef),
							Fwd(first_order.FreeVarsDef),
							Fwd(set_algebra.UnionEqEmpty))
						_, agreeψ := b.ObtainAs[Nat](
							"the first conjunct's bound",
							"«stableAt»(ψ)",
							By(inductiveψ, conjuncts),
							Named("N₁"))
						_, agreeχ := b.ObtainAs[Nat](
							"the second conjunct's bound",
							"«stableAt»(χ)",
							By(inductiveχ, conjuncts),
							Named("N₂"))
						b.Take(b.TermAs[Nat]("N₁ + N₂"))
						F := b.FixAs[FieldOps[A]]("F")
						G := b.FixAs[FieldOps[B]]("G")
						p := b.FixAs[Nat]("p")
						ρ := b.FixAs[Fun[Nat, A]]("ρ")
						σ := b.FixAs[Fun[Nat, B]]("σ")
						fields := b.Assume()
						bounds := b.Have(
							"p exceeds both bounds",
							"N₁ < p ∧ N₂ < p",
							ByArith(fields))
						evaluationsψ := b.Simplified(agreeψ, Fwd(ring_formula.RingFormulaEvalDef))
						evaluationsχ := b.Simplified(agreeχ, Fwd(ring_formula.RingFormulaEvalDef))
						b.Show(
							"a conjunction is true exactly where both conjuncts are",
							Simp(Fwd(ring_formula.RingFormulaEvalDef), Fwd(evalInF), Fwd(evalInG)),
							By(evaluationsψ.At(F, G, p, ρ, σ), evaluationsχ.At(F, G, p, ρ, σ), fields, bounds))
					})),
				Case(
					"a quantifier-free sentence has no existential",
					By(first_order.QuantifierFreeDef))))
		a.Take(N)
		F := a.FixAs[FieldOps[A]]("F")
		G := a.FixAs[FieldOps[B]]("G")
		p := a.FixAs[Nat]("p")
		fields := a.Assume()
		a.Show(
			"truth is evaluation at the zero environment of each field",
			By(
				Normalized,
				bound.At(F, G, p, a.TermAs[Fun[Nat, A]]("λv:num. F.zero"), a.TermAs[Fun[Nat, B]]("λv:num. G.zero")),
				fields,
				ring_formula.RingFormulaTruthDef.At(F, φ),
				ring_formula.RingFormulaTruthDef.At(G, φ)))
	}),
})}

// LargeCharacteristicStability — a sentence takes one truth value in every
// algebraically closed field of characteristic zero and every algebraically
// closed field of prime characteristic past some bound N. The common
// quantifier-free equivalent ψ of the sentence φ over the algebraically
// closed fields on A and on B is itself a sentence; the bound is the one
// quantifier-free stability gives ψ, and each field agrees on φ and ψ at its
// zero environment.
var LargeCharacteristicStability = largeCharacteristicStabilityThm{family.Add(registry.ProofEntry{
	Name: "LargeCharacteristicStability",
	Key:  "prop_ecda720de58038a1",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_closed(φ)",
		},
		Conclusion: "∃N:num. ∀F:field_ops(A). ∀G:field_ops(B). ∀p:num. " +
			"    algebraically_closed_field_on(F) ∧ " +
			"    field_characteristic(F, 0) ∧ " +
			"    algebraically_closed_field_on(G) ∧ " +
			"    field_characteristic(G, p) ∧ " +
			"    N < p ⇒ " +
			"    (ring_formula_truth(F, φ) ⇔ ring_formula_truth(G, φ))",
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], sentence Fact) {
		sentenceParts := a.Conjuncts(
			a.Unfolded(sentence, polynomial_formula.FormulaClosedDef),
			"φ is well formed",
			"φ has no free variables")
		ψ, common := a.UnpackAs[Formula[IntegerPolynomial]](
			GroupPremises(sentenceParts[0], algebraically_closed_field_transfer.CommonElimination.At[A, B](φ)),
			"ψ")
		both := a.Conjuncts(
			common,
			"ψ is a quantifier-free equivalent of φ over the algebraically closed fields on A",
			"and over those on B")
		onA := a.Have(
			"so φ and ψ take one value in an algebraically closed "+
				"field on A at an environment legal on φ's free variables",
			Statement{
				Binders: "∀F:field_ops(A). ∀ρ:(num → A).",
				Hypotheses: []string{
					"algebraically_closed_field_on(F)",
					"fo_env_ok(F.carrier, polynomial_formula_fv(φ), ρ)",
				},
				Conclusion: "ring_formula_eval(F, ρ, φ) ⇔ ring_formula_eval(F, ρ, ψ)",
			},
			Simp(Fwd(ring_formula.RingFormulaEvalDef), Fwd(polynomial_formula.FormulaVarsDef)),
			By(first_order.EquivalentAgreement.Read(both[0])))
		onB := a.Have(
			"and in one on B",
			Statement{
				Binders: "∀G:field_ops(B). ∀σ:(num → B).",
				Hypotheses: []string{
					"algebraically_closed_field_on(G)",
					"fo_env_ok(G.carrier, polynomial_formula_fv(φ), σ)",
				},
				Conclusion: "ring_formula_eval(G, σ, φ) ⇔ ring_formula_eval(G, σ, ψ)",
			},
			Simp(Fwd(ring_formula.RingFormulaEvalDef), Fwd(polynomial_formula.FormulaVarsDef)),
			By(first_order.EquivalentAgreement.Read(both[1])))
		closedψ := a.Have(
			"ψ is a sentence: its free variables lie among those of φ, which has none",
			"polynomial_formula_closed(ψ)",
			By(
				first_order.EquivalentWellFormed.Read(both[0]),
				first_order.EquivalentSupport.Read(both[0]),
				sentenceParts[1],
				polynomial_formula.FormulaClosedDef,
				polynomial_formula.FormulaValidDef,
				polynomial_formula.FormulaVarsDef,
				set_order.SubsetEmpty))
		N, stable := a.ObtainAs[Nat](
			"quantifier-free stability bounds the characteristics in which ψ can change its truth value",
			"∃N:num. ∀F:field_ops(A). ∀G:field_ops(B). ∀p:num. "+
				"    «zeroAndPast»(F, G, p, N) ⇒ (ring_formula_truth(F, ψ) ⇔ ring_formula_truth(G, ψ))",
			By(closedψ, first_order.EquivalentQuantifierFree.Read(both[0]), QuantifierFreeStability))
		a.Take(N)
		F := a.FixAs[FieldOps[A]]("F")
		G := a.FixAs[FieldOps[B]]("G")
		p := a.FixAs[Nat]("p")
		fields := a.Conjuncts(
			a.Assume(),
			"F is algebraically closed",
			"F has characteristic zero",
			"G is algebraically closed",
			"G has characteristic p",
			"p exceeds N")
		a.Show(
			"φ passes from F to G through ψ",
			CalcEq(
				Leg(
					a.TermAs[Bool]("ring_formula_truth(F, ψ)"),
					"F is algebraically closed, so φ and ψ agree at its zero "+
						"environment, of which φ's empty support asks nothing",
					By(
						fields[0],
						onA.At(F, a.TermAs[Fun[Nat, A]]("λv:num. F.zero")),
						sentenceParts[1],
						first_order.EnvOKDef,
						set_basic.NotInEmpty,
						ring_formula.RingFormulaTruthDef.At(F, φ),
						ring_formula.RingFormulaTruthDef.At(F, ψ))),
				Leg(
					a.TermAs[Bool]("ring_formula_truth(G, ψ)"),
					"the quantifier-free ψ is stable from characteristic zero to p, which exceeds N",
					By(
						stable.At(F, G, p),
						algebraic_closure.FieldOn.Read(fields[0]),
						fields[1],
						algebraic_closure.FieldOn.Read(fields[2]),
						fields[3],
						fields[4])),
				FinalLeg(
					"G is algebraically closed, so ψ and φ agree at its zero environment",
					By(
						fields[2],
						onB.At(G, a.TermAs[Fun[Nat, B]]("λv:num. G.zero")),
						sentenceParts[1],
						first_order.EnvOKDef,
						set_basic.NotInEmpty,
						ring_formula.RingFormulaTruthDef.At(G, φ),
						ring_formula.RingFormulaTruthDef.At(G, ψ)))))
	}),
})}

// PrimeClosureLocallyFinite — every prime p has a locally finite
// algebraically closed field of characteristic p in the closure host. The
// integers modulo p form a field K of p elements, whose characteristic is p
// because p is a power of it. Its algebraic closure M receives K by a ring
// isomorphism onto a subfield, «closureEmbedding», a ↦ {(0, λn. a)}, which
// carries the vanishing of p from K to M; and M, algebraic over that finite
// subfield, is locally finite.
var PrimeClosureLocallyFinite = primeClosureLocallyFiniteThm{family.Add(registry.ProofEntry{
	Name: "PrimeClosureLocallyFinite",
	Key:  "prop_5e7188b91341ce09",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "∃F:field_ops(set(prod(num, num → set(int)))). " +
			"    algebraically_closed_field_on(F) ∧ field_characteristic(F, p) ∧ locally_finite_field(F)",
		Abbrev: Abbrev{
			{Name: "primeField", Text: "λn:num. " +
				"    ideal_quotient_field(int_ring, ideal_span(int_ring, {int_of_num(n)}))"},
			{Name: "closureEmbedding", Text: "(λa:set(int). {(0, λn:num. a)})"},
		},
	}, func(a *Argument, p *Expr[Nat], prime Fact) {
		K := a.TermAs[FieldOps[Set[Int]]]("«primeField»(p)")
		ringK := a.TermAs[module_record.RingOps[Set[Int]]]("field_ring(«primeField»(p))")
		carrierK := a.TermAs[Set[Set[Int]]]("«primeField»(p).carrier")
		primeField := a.Conjuncts(
			GroupPremises(prime, finite_field.PrimeFieldOn.At(p)),
			"the integers modulo p form a finite field K",
			"K has p elements")
		fieldK := a.Conjuncts(
			a.Unfolded(primeField[0], finite_field.FiniteFieldDef),
			"K is a field",
			"K is finite")
		charK := a.Have(
			"K has characteristic p, since p is a power of its characteristic",
			"ring_prime_characteristic(field_ring(«primeField»(p)), p)",
			Derive(func(b *Argument) {
				q, charQ := b.UnpackAs[Nat](
					GroupPremises(fieldK[0], fieldK[1], finite_field.FiniteFieldCharacteristic.At(K)), "q")
				e, power := b.UnpackAs[Nat](
					GroupPremises(fieldK[0], fieldK[1], charQ, finite_field.FiniteFieldSizePower.At(K, q)), "e")
				size := b.Have(
					"K has p elements and qᵉ elements, so p = qᵉ",
					"p = q ^ e",
					By(power, primeField[1], cardinality.HasSizeDef.At(carrierK, p)))
				b.Show(
					"qᵉ vanishes in K, and qᵉ is p",
					By(
						field.RingOn.At(K),
						fieldK[0],
						finite_field.PrimePowerVanishes.At(ringK, q, e),
						charQ,
						power,
						size,
						prime,
						finite_field.PrimeCharacteristicDef.At(ringK, p)))
			}))
		M, closure := a.UnpackAs[FieldOps[_ClosureHost]](
			GroupPremises(fieldK[0], algebraic_closure.AlgebraicClosureFieldOn.At(K)), "M")
		closed := a.Conjuncts(
			closure,
			"M is a field",
			"M is algebraically closed",
			"the image of K is a subfield of M",
			"K is isomorphic to that image",
			"M is algebraic over the image of K")
		embedding := a.Have(
			"the embedding of K is a ring homomorphism",
			"ring_homomorphism(field_ring(«primeField»(p)), "+
				"    restrict_ring(field_ring(M), image(«closureEmbedding», «primeField»(p).carrier)), "+
				"    «closureEmbedding»)",
			By(a.Unfolded(closed[3], ring_homomorphism.RingIsomorphismDef)))
		vanishM := a.Have(
			"p vanishes in M, the embedding carrying the p-fold sum of one in K to that of M",
			"monoid_pow(M.add, M.zero, M.one, p) = M.zero",
			By(
				ring_homomorphism.RingMapNumeral.Read(embedding).At(p),
				ring_homomorphism.MapZero.Read(embedding),
				charK,
				finite_field.PrimeCharacteristicDef.At(ringK, p)))
		ringM := a.TermAs[module_record.RingOps[_ClosureHost]]("field_ring(M)")
		characteristicM := a.Have(
			"M has characteristic p: p is positive and vanishes in M",
			"field_characteristic(M, p)",
			ByArith(
				finite_field.FieldCharacteristicDef.At(M, p),
				finite_field.PrimeCharacteristicDef.At(ringM, p),
				field.FieldRingDef.At(M),
				nat_prime.PrimeAtLeastTwo.At(p),
				prime,
				vanishM))
		embeddingK := a.TermAs[Fun[Set[Int], _ClosureHost]]("«closureEmbedding»")
		imageK := a.TermAs[Set[_ClosureHost]]("image(«closureEmbedding», «primeField»(p).carrier)")
		locallyFinite := a.Have(
			"M is algebraic over the image of K, a finite subfield, so M is locally finite",
			"locally_finite_field(M)",
			By(
				closed[2],
				closed[4],
				fieldK[1],
				finite_set.FiniteImage.At(embeddingK, carrierK),
				finite_field.AlgebraicOverFiniteLocallyFinite.Read(closed[0]).At(imageK)))
		a.Take(M)
		a.Show(
			"M is an algebraically closed field of characteristic p, and locally finite",
			By(
				algebraic_closure.AlgebraicallyClosedFieldOnIff,
				closed[0],
				closed[1],
				characteristicM,
				locallyFinite))
	}),
})}

// ComplexModel — the complex field is an algebraically closed field of
// characteristic zero: it is a field on its whole carrier, closed by the
// fundamental theorem of algebra, and its ring is complex_ring, which has
// characteristic zero.
var ComplexModel = complexModelThm{family.Add(registry.ProofEntry{
	Name: "ComplexModel",
	Key:  "prop_27c3fb4d9cda553b",
	Build: family.Theorem("algebraically_closed_field_on(complex_field_ops) ∧ "+
		"field_characteristic(complex_field_ops, 0)", func(a *Argument) {
		complexField := a.TermAs[FieldOps[complex_field.Complex]]("complex_field_ops")
		a.Do(SplitConj(
			Case(
				"ℂ is a field on its carrier, closed by the fundamental theorem of algebra",
				By(
					algebraic_closure.AlgebraicallyClosedFieldOnIff,
					complex_field.FieldOn,
					complex_polynomial.AlgebraicallyClosed)),
			Case(
				"ℂ has characteristic zero, its ring being complex_ring",
				By(
					finite_field.FieldCharacteristicDef.At(complexField, a.TermAs[Nat]("0")),
					complex_field.ComplexCharacteristicZero,
					field.FieldRingDef.At(complexField),
					complex_field.ComplexFieldOpsDef,
					complex_field.ComplexRingDef)),
		))
	}),
})}

// LefschetzPrinciple — a ring sentence holds over the complex numbers exactly
// when it holds in all sufficiently large prime characteristics: one stability
// bound N₀ compares the complex field with every algebraically closed field of
// prime characteristic above it, which carries complex truth forward; back, a
// prime above N₀ and the given bound has a model in the host, where the
// sentence holds and from which stability returns it to the complex field.
var LefschetzPrinciple = lefschetzPrincipleThm{family.Add(registry.ProofEntry{
	Name: "LefschetzPrinciple",
	Key:  "prop_a63f0b0e06402008",
	Reading: "The positive-characteristic models live in a fixed " +
		"sufficiently large host. Quantifying over models in an arbitrary " +
		"small host would make the right side vacuous and the equivalence false.",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_closed(φ)",
		},
		Conclusion: "ring_formula_truth(complex_field_ops, φ) ⇔ " +
			"∃N:num. ∀p:num. " +
			"    N < p ∧ nat_prime(p) ⇒ " +
			"    ∀F:field_ops(set(prod(num, num → set(int)))). " +
			"        algebraically_closed_field_on(F) ∧ field_characteristic(F, p) ⇒ ring_formula_truth(F, φ)",
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], sentence Fact) {
		// The stability bound N₀ for φ, read between the complex field and the host.
		N0, stable := a.UnpackAs[Nat](
			GroupPremises(sentence, LargeCharacteristicStability.At[complex_field.Complex, _ClosureHost](φ)),
			"N₀")
		a.Iff()
		a.Forward(
			"φ true over ℂ holds in every algebraically closed host field of prime characteristic past N₀",
			func(b *Argument, overComplex Fact) {
				b.Take(N0)
				b.Show(
					"the stability bound, at the complex model, carries φ to each of them",
					By(stable, ComplexModel, overComplex))
			})
		a.Backward(
			"φ true in every large prime characteristic is true over ℂ: test it at one prime past both bounds",
			func(b *Argument, eventually Fact) {
				_, beyond := b.UnpackAs[Nat](eventually, "N")
				p, prime := b.UnpackAs[Nat](nat_prime.EuclidBound.At(b.TermAs[Nat]("N + N₀")), "p")
				above := b.Have(
					"p exceeds both bounds",
					"N < p ∧ N₀ < p",
					ByArith(prime))
				F, model := b.UnpackAs[FieldOps[_ClosureHost]](
					GroupPremises(prime, PrimeClosureLocallyFinite.At(p)), "F")
				inF := b.Have(
					"φ holds in the comparison model F of characteristic p",
					"ring_formula_truth(F, φ)",
					By(beyond.At(p, F), prime, model, above))
				complexField := b.TermAs[FieldOps[complex_field.Complex]]("complex_field_ops")
				b.Show(
					"the stability bound, at the complex model and F, carries φ back to ℂ",
					By(stable.At(complexField, F, p), ComplexModel, model, above, inF))
			})
	}),
})}

// PrimeFamilyTransfer — a closed sentence true in an algebraically closed field of every prime
// characteristic is true in every algebraically closed field: in a prime characteristic p the
// field agrees with the model of characteristic p, the two having one characteristic; in
// characteristic zero, large characteristics stabilize the sentence past some bound
// (LargeCharacteristicStability), and the field agrees with the model of any prime beyond it.
var PrimeFamilyTransfer = primeFamilyTransferThm{family.Add(registry.ProofEntry{
	Name: "PrimeFamilyTransfer",
	Key:  "prop_fbbca4eecc65db4d",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"algebraically_closed_field_on(F)",
			"polynomial_formula_closed(φ)",
			"∀p:num. " +
				"    nat_prime(p) ⇒ " +
				"    ∃G:field_ops(B). " +
				"        algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ ring_formula_truth(G, φ)",
		},
		Conclusion: "ring_formula_truth(F, φ)",
	}, func(a *Argument, F *Expr[FieldOps[A]], φ *Expr[Formula[IntegerPolynomial]],
		closedF algebraic_closure.AlgebraicallyClosedFieldFact[on.F], sentence, models Fact) {
		fieldF := algebraic_closure.FieldOn.Read(closedF)
		a.Show(
			"split on F's characteristic",
			finite_field.FieldCharacteristicCases.Read(fieldF).AsFact().SplitDisj(
				LeftHolds(
					"in characteristic zero, F agrees with the model "+
						"of a prime characteristic past the stability bound",
					Given(func(b *Argument, characteristicZero Fact) {
						zero := b.Have(
							"F has characteristic 0",
							"field_characteristic(F, 0)",
							By(characteristicZero, finite_field.FieldCharacteristicDef.At(F, b.TermAs[Nat]("0"))))
						bound, beyond := b.UnpackAs[Nat](
							GroupPremises(sentence, LargeCharacteristicStability.At[A, B](φ)))
						p, prime := b.UnpackAs[Nat](nat_prime.EuclidBound.At(bound))
						G, model := b.UnpackAs[FieldOps[B]](GroupPremises(prime, models.At(p)))
						b.Show(
							"p exceeds the bound, so F and G agree on the sentence",
							By(beyond.At(F, G, p), closedF, zero, model, prime))
					})),
				RightHolds(
					"in a prime characteristic p, the sentence transfers from the model of characteristic p",
					Given(func(b *Argument, primeCharacteristic Fact) {
						p, characteristic := b.UnpackAs[Nat](primeCharacteristic)
						prime := b.Have(
							"p is prime",
							"nat_prime(p)",
							By(characteristic, finite_field.PrimeCharacteristicDef))
						positive := b.Have(
							"a prime is positive",
							"0 < p",
							ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p)))
						characteristicP := b.Have(
							"F has characteristic p",
							"field_characteristic(F, p)",
							By(positive, characteristic, finite_field.FieldCharacteristicDef.At(F, p)))
						G, model := b.UnpackAs[FieldOps[B]](GroupPremises(prime, models.At(p)))
						same := b.Have(
							"G and F send the same integers to zero",
							"same_characteristic(G, F)",
							By(
								model,
								fieldF,
								characteristicP,
								algebraic_closure.AlgebraicallyClosedFieldOnIff,
								finite_field.SameCharacteristicFromCharacteristic.At(G, F, p)))
						b.Show(
							"algebraically closed fields of one characteristic agree on a closed sentence",
							By(
								model,
								closedF,
								same,
								sentence,
								algebraically_closed_field_transfer.SentenceTransfer.At(G, F, φ)))
					}))))
	}),
})}
