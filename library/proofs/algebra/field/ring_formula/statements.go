package ring_formula

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// RingFormulaAtomDef — interpret a polynomial atom as equality to zero.
var RingFormulaAtomDef = ringFormulaAtomDefThm{family.Define(registry.DefEntry{
	Name:  "RingFormulaAtomDef",
	Const: "ring_formula_atom",
	Type:  "field_ops(A) → ((num → num) → int) → (num → A) → bool",
	Key:   "prop_ed809f15d77e88e8",
	Equations: []string{
		"∀F:field_ops(A). ∀p:((num → num) → int). ∀ρ:(num → A). " +
			"    ring_formula_atom(F, p, ρ) ⇔ integer_polynomial_eval(field_ring(F), ρ, p) = F.zero",
	},
})}

// RingFormulaEvalDef — interpret a ring formula using carrier-restricted quantifiers.
var RingFormulaEvalDef = ringFormulaEvalDefThm{family.Define(registry.DefEntry{
	Name:  "RingFormulaEvalDef",
	Const: "ring_formula_eval",
	Type:  "field_ops(A) → (num → A) → fo_formula((num → num) → int) → bool",
	Key:   "prop_a7253a26517c0cb",
	Equations: []string{
		"∀F:field_ops(A). ∀ρ:(num → A). ∀φ:fo_formula((num → num) → int). " +
			"    ring_formula_eval(F, ρ, φ) ⇔ fo_eval(F.carrier, ring_formula_atom(F), ρ, φ)",
	},
	Deps: []registry.EntryLike{RingFormulaAtomDef},
})}

// RingFormulaTruthDef — sentence truth at the zero environment.
var RingFormulaTruthDef = ringFormulaTruthDefThm{family.Define(registry.DefEntry{
	Name:  "RingFormulaTruthDef",
	Const: "ring_formula_truth",
	Type:  "field_ops(A) → fo_formula((num → num) → int) → bool",
	Key:   "prop_e283b6be67816e12",
	Equations: []string{
		"∀F:field_ops(A). ∀φ:fo_formula((num → num) → int). " +
			"    ring_formula_truth(F, φ) ⇔ ring_formula_eval(F, λv:num. F.zero, φ)",
	},
	Deps: []registry.EntryLike{RingFormulaEvalDef},
})}

// EnvironmentCongruence — only the free-variable environment affects ring-formula truth: a ring
// formula reads vanishing off the values of its polynomials, so the congruence of the formulas
// read through a predicate applies.
var EnvironmentCongruence = environmentCongruenceThm{family.Add(registry.ProofEntry{
	Name: "EnvironmentCongruence",
	Key:  "prop_9fa8274ad58fa9e0",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀ρ σ:(num → A). ∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
			"∀v:num. v ∈ polynomial_formula_fv(φ) ⇒ ρ(v) = σ(v)",
		},
		Conclusion: "ring_formula_eval(F, ρ, φ) ⇔ ring_formula_eval(F, σ, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		ρ, σ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		wf, agree Fact,
	) {
		a.Show(
			"the congruence of the formulas read through a predicate, at vanishing",
			Simp(Fwd(RingFormulaEvalDef)),
			Unfold(RingFormulaAtomDef),
			By(
				wf,
				agree,
				polynomial_formula.EnvironmentCongruence.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[Set[A]]("λx:A. x = F.zero"),
					ρ, σ, φ)))
	}),
})}

// ClosedEnvironment — a closed formula has the same truth value in every environment: truth is
// evaluation at the zero environment, and a closed formula has no free variable on which that
// environment and any other could disagree.
var ClosedEnvironment = closedEnvironmentThm{family.Add(registry.ProofEntry{
	Name: "ClosedEnvironment",
	Key:  "prop_a830b48a233a1443",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀ρ:(num → A). ∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_closed(φ)",
		},
		Conclusion: "ring_formula_eval(F, ρ, φ) ⇔ ring_formula_truth(F, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		ρ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		closed Fact,
	) {
		a.Show(
			"ρ and the zero environment agree on every free variable of φ, there being none",
			By(
				a.Unfolded(closed, polynomial_formula.FormulaClosedDef),
				EnvironmentCongruence.At(F, ρ, a.TermAs[Fun[Nat, A]]("λv:num. F.zero"), φ),
				set_basic.NotInEmpty,
				RingFormulaTruthDef))
	}),
})}

// RingAtomEmbedding — a homomorphism of the commutative rings of F and G, one-to-one on the
// carrier of F, embeds the ring atoms: a ring atom reads vanishing off the value of its
// polynomial, and the homomorphism, one-to-one and fixing zero, carries vanishing both ways, so
// the embedding of the atoms reading a predicate off a polynomial's value applies.
var RingAtomEmbedding = ringAtomEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "RingAtomEmbedding",
	Key:  "prop_3b4cb591daf8535",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀G:field_ops(B). ∀i:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"injective_on(F.carrier, i)",
		},
		Conclusion: "fo_atomic_embedding(F.carrier, " +
			"    G.carrier, " +
			"    ring_formula_atom(F), " +
			"    ring_formula_atom(G), " +
			"    integer_polynomial, " +
			"    integer_polynomial_vars, " +
			"    i)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		G *Expr[FieldOps[B]],
		i *Arrow[A, B],
		hom, injective Fact,
	) {
		a.Show(
			"the ring atoms read vanishing off the value of a polynomial, and i carries vanishing both ways",
			Unfold(RingFormulaAtomDef),
			By(
				hom,
				injective,
				ring_homomorphism.ZeroIffImageZero.Read(hom),
				polynomial_formula.PolynomialAtomEmbedding.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					i,
					a.TermAs[Set[A]]("λx:A. x = F.zero"),
					a.TermAs[Set[B]]("λy:B. y = G.zero"))))
	}),
})}

// QuantifierFreeEmbedding — a homomorphism of the commutative rings of F and G, one-to-one on the
// carrier of F, preserves and reflects quantifier-free truth: one-to-one and fixing zero, it
// carries vanishing both ways, so the embedding of the quantifier-free formulas read through a
// predicate applies.
var QuantifierFreeEmbedding = quantifierFreeEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeEmbedding",
	Key:  "prop_e8f954598679ffdd",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀G:field_ops(B). " +
			"∀i:(A → B). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"injective_on(F.carrier, i)",
			"polynomial_formula_wf(φ)",
			"fo_qf(φ)",
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
		hom, injective, wf, qf, envOk Fact,
	) {
		a.Show(
			"the embedding of the quantifier-free formulas read through a predicate, at vanishing",
			Simp(Fwd(RingFormulaEvalDef)),
			Unfold(RingFormulaAtomDef),
			By(
				hom,
				injective,
				ring_homomorphism.ZeroIffImageZero.Read(hom),
				wf,
				qf,
				envOk,
				polynomial_formula.QuantifierFreeEmbedding.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					i,
					a.TermAs[Set[A]]("λx:A. x = F.zero"),
					a.TermAs[Set[B]]("λy:B. y = G.zero"),
					ρ, φ)))
	}),
})}

// IsomorphismInvariant — an isomorphism of the commutative rings of F and G preserves every ring
// formula: one-to-one and fixing zero, it carries vanishing both ways, and it is onto the carrier
// of G, so the invariance of the formulas read through a predicate under onto homomorphisms
// applies.
var IsomorphismInvariant = isomorphismInvariantThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismInvariant",
	Key:  "prop_2316a50dd49dba3e",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀G:field_ops(B). " +
			"∀i:(A → B). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"ring_isomorphism(field_ring(F), field_ring(G), i)",
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
		iso, wf, envOk Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(iso, ring_homomorphism.RingIsomorphismDef),
			"i is a ring homomorphism",
			"i is injective on the carrier of F",
			"i carries the carrier of F onto the carrier of G")
		hom, injective, onto := parts[0], parts[1], parts[2]
		a.Show(
			"the invariance of the formulas read through a predicate under onto homomorphisms, at vanishing",
			Simp(Fwd(RingFormulaEvalDef)),
			Unfold(RingFormulaAtomDef),
			By(
				hom,
				injective,
				ring_homomorphism.ZeroIffImageZero.Read(hom),
				onto,
				wf,
				envOk,
				polynomial_formula.OntoInvariant.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					i,
					a.TermAs[Set[A]]("λx:A. x = F.zero"),
					a.TermAs[Set[B]]("λy:B. y = G.zero"),
					ρ, φ)))
	}),
})}

// TransportFieldInvariant — a formula holds in a field at an environment exactly
// when it holds, at the environment carried along, in the field's copy
// along a map one-to-one on its carrier: the map is an isomorphism of the
// field onto the copy, whose carrier is the image of the field's.
var TransportFieldInvariant = transportFieldInvariantThm{family.Add(registry.ProofEntry{
	Name: "TransportFieldInvariant",
	Key:  "prop_6039a387b8bbb31a",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀i:(A → B). ∀ρ:(num → A). ∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"field_on(F)",
			"injective_on(F.carrier, i)",
			"polynomial_formula_wf(φ)",
			"fo_env_ok(F.carrier, polynomial_formula_fv(φ), ρ)",
		},
		Conclusion: "ring_formula_eval(F, ρ, φ) ⇔ " +
			"ring_formula_eval(transport_field(i, F), λv:num. i(ρ(v)), φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		i *Arrow[A, B],
		ρ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		fieldF, injective, wf, legal Fact,
	) {
		isomorphism := a.Have(
			"i is an isomorphism of F onto its copy, whose carrier is the image of F's",
			"ring_isomorphism(field_ring(F), field_ring(transport_field(i, F)), i)",
			By(
				fieldF,
				injective,
				ring_homomorphism.RingIsomorphismDef,
				ring_transport.TransportFieldHomomorphism.At(i, F),
				ring_transport.TransportFieldDef))
		a.Show(
			"an isomorphism keeps the value of every formula at the carried environment",
			By(
				isomorphism,
				wf,
				legal,
				IsomorphismInvariant.At(F, a.TermAs[FieldOps[B]]("transport_field(i, F)"), i, ρ, φ)))
	}),
})}

// TransportAlgebraicallyClosed — the copy of an algebraically closed field
// along a map one-to-one on its carrier is algebraically closed. A
// polynomial q of positive degree over the copy is the image of a polynomial
// p over the field, which has the same degree; p has a root x, and i carries
// p's value at x to q's value at i(x).
var TransportAlgebraicallyClosed = transportAlgebraicallyClosedThm{family.Add(registry.ProofEntry{
	Name: "TransportAlgebraicallyClosed",
	Key:  "prop_ca830339c16489c3",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀i:(A → B).",
		Hypotheses: []string{
			"algebraically_closed_field_on(F)",
			"injective_on(F.carrier, i)",
		},
		Conclusion: "algebraically_closed_field_on(transport_field(i, F))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		i *Arrow[A, B],
		closed algebraic_closure.AlgebraicallyClosedFieldFact[on.F],
		injective Fact,
	) {
		fieldF := algebraic_closure.FieldOn.Read(closed)
		roots := algebraic_closure.PositiveDegreeRoot.Read(closed)
		carrier := a.TermAs[Set[A]]("F.carrier")
		zero := a.TermAs[A]("F.zero")
		copyF := a.TermAs[FieldOps[B]]("transport_field(i, F)")
		fieldCopy := a.Have(
			"the copy of F along i is a field",
			"field_on(transport_field(i, F))",
			By(fieldF, injective, ring_transport.TransportFieldOn.At(i, F)))
		embedding := a.Have(
			"i is a ring homomorphism from F to its copy",
			"ring_homomorphism(field_ring(F), field_ring(transport_field(i, F)), i)",
			By(fieldF, injective, ring_transport.TransportFieldHomomorphism.At(i, F)))
		// the polynomials i transports are read over a subfield of F, here F's carrier itself
		carrierSubfield := field.CarrierSubfield.Read(fieldF)
		closedCopy := a.Have(
			"every polynomial of positive degree over the copy has a root in the copy",
			"algebraically_closed_field(transport_field(i, F))",
			Unfold(algebraic_closure.AlgebraicallyClosedDef),
			Derive(func(b *Argument) {
				q := b.FixAs[Fun[Nat, B]]("q")
				given := b.Conjuncts(
					b.Assume(),
					"q is a polynomial over the image of F's carrier",
					"q has positive degree")
				p, pulled := b.UnpackAs[Fun[Nat, A]](
					GroupPremises(
						injective,
						comm_ring.ZeroIn.Read(field.RingOn.Read(fieldF)),
						given[0],
						polynomial.PolynomialPullBack.At(i, carrier, zero, q)),
					"p")
				image := b.Conjuncts(
					pulled,
					"p is a polynomial over F",
					"i carries p to q")
				pOver, pushed := image[0], image[1]
				carried := GroupPremises(
					fieldF,
					fieldCopy,
					embedding,
					carrierSubfield,
					pOver,
					algebraic_element.FieldEmbeddingPolynomials.At(F, copyF, i, carrier, p))
				positive := b.Have(
					"p has positive degree: i keeps degrees and carries p to q",
					"0 < polynomial_degree(F.zero, p)",
					By(Normalized, pushed, given[1], carried))
				values := b.Have(
					"i carries the value of p at each point of F to the value of its image at the image of the point",
					Statement{
						Binders:    "∀x:A.",
						Hypotheses: []string{"x ∈ F.carrier"},
						Conclusion: "i(polynomial_eval(p, x)) = " +
							"polynomial_eval(transport_binary_op(i, F.carrier, F.add), " +
							"    i(F.zero), " +
							"    transport_binary_op(i, F.carrier, F.mul), " +
							"    i(F.one), " +
							"    λn:num. i(p(n)), " +
							"    i(x))",
					},
					By(carried))
				x, root := b.UnpackAs[A](GroupPremises(pOver, positive, roots.At(p)), "x")
				b.Take(i.Apply(x))
				b.Show(
					"i(x) lies in the copy, and q's value there is i of p's value at x, i(F.zero), the copy's zero",
					By(pushed, root, set_image.FunInImage.At(i, carrier, x), values.At(x)))
			}))
		a.Show(
			"the copy is a field in which every polynomial of positive degree has a root",
			By(fieldCopy, closedCopy, algebraic_closure.AlgebraicallyClosedFieldOnIff))
	}),
})}

// EliminationAlongInjection — a quantifier-free equivalent over the
// algebraically closed fields on B is one over those on A, once A injects into
// B. An algebraically closed field on A has its copy on B along the injection:
// the copy is algebraically closed, and the injection, one-to-one, embeds the
// ring atoms of the field onto those of the copy, so
// first_order.EliminationAlongClassEmbedding carries the equivalent back.
var EliminationAlongInjection = eliminationAlongInjectionThm{family.Add(registry.ProofEntry{
	Name: "EliminationAlongInjection",
	Key:  "prop_e298234b55bb4e27",
	Build: family.Theorem(Statement{
		Binders: "∀φ ψ:fo_formula((num → num) → int). ∀i:(A → B).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
			"fo_quantifier_free_equivalent(algebraically_closed_field_on, " +
				"    «carrier»⟨A:B⟩, " +
				"    ring_formula_atom, " +
				"    integer_polynomial, " +
				"    integer_polynomial_vars, " +
				"    φ, " +
				"    ψ)",
			"injective_on(𝕌, i)",
		},
		Conclusion: "fo_quantifier_free_equivalent(algebraically_closed_field_on, " +
			"    «carrier», " +
			"    ring_formula_atom, " +
			"    integer_polynomial, " +
			"    integer_polynomial_vars, " +
			"    φ, " +
			"    ψ)",
	}, func(
		a *Argument,
		φ, ψ *Expr[Formula[IntegerPolynomial]],
		i *Arrow[A, B],
		wf, equivalent, injective Fact,
	) {
		copies := a.Have(
			"every algebraically closed field on A embeds onto "+
				"its copy along i, an algebraically closed field on B",
			Statement{
				Binders: "∀F:field_ops(A).",
				Hypotheses: []string{
					"algebraically_closed_field_on(F)",
				},
				Conclusion: "∃G:field_ops(B). ∃j:(A → B). " +
					"    algebraically_closed_field_on(G) ∧ " +
					"    fo_atomic_embedding(F.carrier, " +
					"        G.carrier, " +
					"        ring_formula_atom(F), " +
					"        ring_formula_atom(G), " +
					"        integer_polynomial, " +
					"        integer_polynomial_vars, " +
					"        j) ∧ " +
					"    image(j, F.carrier) = G.carrier",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				closed := b.Assume()
				carrier := b.TermAs[Set[A]]("F.carrier")
				copyF := b.TermAs[FieldOps[B]]("transport_field(i, F)")
				injectiveF := b.Have(
					"i is one-to-one on the carrier of F",
					"injective_on(F.carrier, i)",
					By(
						injective,
						functions.InjectiveOnSubset.At(i, carrier, b.TermAs[Set[A]]("𝕌")),
						set_order.SubsetUniv.At(carrier)))
				b.Take(copyF)
				b.Take(i)
				b.Show(
					"the copy is algebraically closed, and i embeds the ring atoms "+
						"of F in those of the copy, whose carrier is the image of F's",
					By(
						closed,
						injectiveF,
						TransportAlgebraicallyClosed.At(F, i),
						algebraic_closure.FieldOn.Read(closed),
						ring_transport.TransportFieldHomomorphism.At(i, F),
						RingAtomEmbedding.At(F, copyF, i),
						ring_transport.TransportFieldDef))
			}))
		a.Show(
			"each algebraically closed field on A embeds onto one on B, where ψ is equivalent to φ",
			By(
				a.Unfolded(wf, polynomial_formula.FormulaValidDef),
				equivalent,
				copies,
				first_order.EliminationAlongClassEmbedding.At(
					a.TermAs[Set[FieldOps[A]]]("algebraically_closed_field_on"),
					a.TermAs[Fun2[FieldOps[A], A, Bool]]("«carrier»"),
					a.TermAs[Fun3[FieldOps[A], IntegerPolynomial, Fun[Nat, A], Bool]]("ring_formula_atom"),
					a.TermAs[Set[FieldOps[B]]]("algebraically_closed_field_on"),
					a.TermAs[Fun2[FieldOps[B], B, Bool]]("«carrier»⟨A:B⟩"),
					a.TermAs[Fun3[FieldOps[B], IntegerPolynomial, Fun[Nat, B], Bool]]("ring_formula_atom"),
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
					φ,
					ψ)))
	}),
})}

// QuantifierFreeSentenceTransfer — fields of the same characteristic agree on closed
// quantifier-free ring formulas, read at the zero environments: the two fields send the same
// integers to zero, so the sentence transfer of the formulas read through a predicate applies at
// vanishing.
var QuantifierFreeSentenceTransfer = quantifierFreeSentenceTransferThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeSentenceTransfer",
	Key:  "prop_5dbc42b6e37f2b96",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀G:field_ops(B). ∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"field_on(F)",
			"field_on(G)",
			"same_characteristic(F, G)",
			"polynomial_formula_closed(φ)",
			"fo_qf(φ)",
		},
		Conclusion: "ring_formula_truth(F, φ) ⇔ ring_formula_truth(G, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		G *Expr[FieldOps[B]],
		φ *Expr[Formula[IntegerPolynomial]],
		isFieldF field.FieldFact[on.F],
		isFieldG field.FieldFact[on.G],
		same, closed, qf Fact,
	) {
		a.Show(
			"the sentence transfer of the formulas read through a predicate, at vanishing",
			Simp(Fwd(RingFormulaTruthDef), Fwd(RingFormulaEvalDef)),
			Unfold(RingFormulaAtomDef),
			By(
				field.RingOn.Read(isFieldF),
				field.RingOn.Read(isFieldG),
				a.Unfolded(same, finite_field.SameCharacteristicDef),
				closed,
				qf,
				polynomial_formula.QuantifierFreeSentenceTransfer.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					a.TermAs[Set[A]]("λx:A. x = F.zero"),
					a.TermAs[Set[B]]("λy:B. y = G.zero"),
					a.TermAs[Fun[Nat, A]]("λv:num. F.zero"),
					a.TermAs[Fun[Nat, B]]("λv:num. G.zero"),
					φ)))
	}),
})}
