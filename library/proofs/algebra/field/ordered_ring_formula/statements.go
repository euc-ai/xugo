package ordered_ring_formula

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// OrderedRingFormulaAtomDef — interpret an integer-polynomial atom as strict negativity.
var OrderedRingFormulaAtomDef = orderedRingFormulaAtomDefThm{family.Define(registry.DefEntry{
	Name:  "OrderedRingFormulaAtomDef",
	Const: "ordered_ring_formula_atom",
	Type:  "field_ops(A) → (A → A → bool) → ((num → num) → int) → (num → A) → bool",
	Key:   "prop_f6e3d239bcf9145d",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀p:((num → num) → int). ∀ρ:(num → A). " +
			"    ordered_ring_formula_atom(F, lt, p, ρ) ⇔ " +
			"    lt(integer_polynomial_eval(field_ring(F), ρ, p), F.zero)",
	},
})}

// OrderedRingFormulaEvalDef — interpret a formula in an ordered carrier field.
var OrderedRingFormulaEvalDef = orderedRingFormulaEvalDefThm{family.Define(registry.DefEntry{
	Name:  "OrderedRingFormulaEvalDef",
	Const: "ordered_ring_formula_eval",
	Type:  "field_ops(A) → (A → A → bool) → (num → A) → fo_formula((num → num) → int) → bool",
	Key:   "prop_ce1e86fca7ba4bac",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀φ:fo_formula((num → num) → int). " +
			"    ordered_ring_formula_eval(F, lt, ρ, φ) ⇔ " +
			"    fo_eval(F.carrier, ordered_ring_formula_atom(F, lt), ρ, φ)",
	},
	Deps: []registry.EntryLike{OrderedRingFormulaAtomDef},
})}

// OrderedRingFormulaTruthDef — sentence truth at the zero environment.
var OrderedRingFormulaTruthDef = orderedRingFormulaTruthDefThm{family.Define(registry.DefEntry{
	Name:  "OrderedRingFormulaTruthDef",
	Const: "ordered_ring_formula_truth",
	Type:  "field_ops(A) → (A → A → bool) → fo_formula((num → num) → int) → bool",
	Key:   "prop_1fd5daf57a6b05d4",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀φ:fo_formula((num → num) → int). " +
			"    ordered_ring_formula_truth(F, lt, φ) ⇔ ordered_ring_formula_eval(F, lt, λv:num. F.zero, φ)",
	},
	Deps: []registry.EntryLike{OrderedRingFormulaEvalDef},
})}

// EnvironmentCongruence — only the free-variable environment affects truth: an ordered formula
// reads negativity off the values of its polynomials, so the congruence of the formulas read
// through a predicate applies.
var EnvironmentCongruence = environmentCongruenceThm{family.Add(registry.ProofEntry{
	Name: "EnvironmentCongruence",
	Key:  "prop_37a84e8e6bdfa310",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀ρ σ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
			"∀v:num. v ∈ polynomial_formula_fv(φ) ⇒ ρ(v) = σ(v)",
		},
		Conclusion: "ordered_ring_formula_eval(F, lt, ρ, φ) ⇔ ordered_ring_formula_eval(F, lt, σ, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ρ, σ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		wf, agree Fact,
	) {
		a.Show(
			"the congruence of the formulas read through a predicate, at negativity",
			Simp(Fwd(OrderedRingFormulaEvalDef)),
			Unfold(OrderedRingFormulaAtomDef),
			By(
				wf,
				agree,
				polynomial_formula.EnvironmentCongruence.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[Set[A]]("λx:A. lt(x, F.zero)"),
					ρ, σ, φ)))
	}),
})}

// ClosedEnvironment — a closed formula has the same truth value in every environment:
// truth is evaluation at the zero environment, and a closed formula has no
// free variable on which that environment and any other could disagree.
var ClosedEnvironment = closedEnvironmentThm{family.Add(registry.ProofEntry{
	Name: "ClosedEnvironment",
	Key:  "prop_6418c80ffdb44354",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_closed(φ)",
		},
		Conclusion: "ordered_ring_formula_eval(F, lt, ρ, φ) ⇔ ordered_ring_formula_truth(F, lt, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ρ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		closed Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(closed, polynomial_formula.FormulaClosedDef),
			"φ is well formed",
			"φ has no free variable")
		wellFormed, noFreeVariable := parts[0], parts[1]
		a.Show(
			"ρ and the zero environment agree on every free variable of φ, there being none",
			By(
				wellFormed,
				noFreeVariable,
				EnvironmentCongruence.At(F, lt, ρ, a.TermAs[Fun[Nat, A]]("λv:num. F.zero"), φ),
				set_basic.NotInEmpty,
				OrderedRingFormulaTruthDef))
	}),
})}

// OrderedAtomEmbedding — a ring homomorphism that preserves and reflects the order embeds the
// ordered atoms, neither side an ordered field: an ordered atom reads negativity off the value of
// its polynomial, and the homomorphism, fixing zero, carries negativity both ways, so the
// embedding of the atoms reading a predicate off a polynomial's value applies.
var OrderedAtomEmbedding = orderedAtomEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "OrderedAtomEmbedding",
	Key:  "prop_3fbc9aed6dad159",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀G:field_ops(B). ∀ls:(B → B → bool). ∀i:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ (lt(x, y) ⇔ ls(i(x), i(y)))",
		},
		Conclusion: "fo_atomic_embedding(F.carrier, " +
			"    G.carrier, " +
			"    ordered_ring_formula_atom(F, lt), " +
			"    ordered_ring_formula_atom(G, ls), " +
			"    integer_polynomial, " +
			"    integer_polynomial_vars, " +
			"    i)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		G *Expr[FieldOps[B]],
		ls *Arrow2[B, B, Bool],
		i *Arrow[A, B],
		hom, order Fact,
	) {
		a.Show(
			"the ordered atoms read negativity off the value "+
				"of a polynomial, and i carries negativity both ways",
			Unfold(OrderedRingFormulaAtomDef),
			By(
				hom,
				order,
				ordered_field.NegativeIffImageNegative,
				polynomial_formula.PolynomialAtomEmbedding.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					i,
					a.TermAs[Set[A]]("λx:A. lt(x, F.zero)"),
					a.TermAs[Set[B]]("λy:B. ls(y, G.zero)"))))
	}),
})}

// QuantifierFreeEmbedding — a ring homomorphism that preserves and reflects the order preserves and
// reflects quantifier-free truth, neither side an ordered field: fixing zero, it carries negativity
// both ways, so the embedding of the quantifier-free formulas read through a predicate applies.
var QuantifierFreeEmbedding = quantifierFreeEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeEmbedding",
	Key:  "prop_d150cca698bd177c",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀G:field_ops(B). " +
			"∀ls:(B → B → bool). " +
			"∀i:(A → B). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ (lt(x, y) ⇔ ls(i(x), i(y)))",
			"polynomial_formula_wf(φ)",
			"fo_qf(φ)",
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
		hom, order, wf, qf, envOk Fact,
	) {
		a.Show(
			"the embedding of the quantifier-free formulas read through a predicate, at negativity",
			Simp(Fwd(OrderedRingFormulaEvalDef)),
			Unfold(OrderedRingFormulaAtomDef),
			By(
				hom,
				order,
				ordered_field.NegativeIffImageNegative,
				wf,
				qf,
				envOk,
				polynomial_formula.QuantifierFreeEmbedding.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					i,
					a.TermAs[Set[A]]("λx:A. lt(x, F.zero)"),
					a.TermAs[Set[B]]("λy:B. ls(y, G.zero)"),
					ρ, φ)))
	}),
})}

// OntoInvariant — a ring homomorphism onto the carrier of G that preserves and reflects the order
// preserves every formula, neither side an ordered field and the map not assumed one-to-one:
// fixing zero, it carries negativity both ways, so the invariance of the formulas read through a
// predicate under onto homomorphisms applies.
var OntoInvariant = ontoInvariantThm{family.Add(registry.ProofEntry{
	Name: "OntoInvariant",
	Key:  "prop_c4f9941b3dcf8ec6",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀G:field_ops(B). " +
			"∀ls:(B → B → bool). " +
			"∀i:(A → B). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ (lt(x, y) ⇔ ls(i(x), i(y)))",
			"image(i, F.carrier) = G.carrier",
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
		hom, order, onto, wf, envOk Fact,
	) {
		a.Show(
			"the invariance of the formulas read through a predicate under onto homomorphisms, at negativity",
			Simp(Fwd(OrderedRingFormulaEvalDef)),
			Unfold(OrderedRingFormulaAtomDef),
			By(
				hom,
				order,
				ordered_field.NegativeIffImageNegative,
				onto,
				wf,
				envOk,
				polynomial_formula.OntoInvariant.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					i,
					a.TermAs[Set[A]]("λx:A. lt(x, F.zero)"),
					a.TermAs[Set[B]]("λy:B. ls(y, G.zero)"),
					ρ, φ)))
	}),
})}

// TransportOrderedFieldInvariant — a formula holds in an ordered field at an
// environment exactly when it holds, at the environment carried along, in the
// field's copy along a map one-to-one on its carrier, ordered by the
// transported order: the map is an order embedding of the field onto the copy.
var TransportOrderedFieldInvariant = transportOrderedFieldInvariantThm{family.Add(registry.ProofEntry{
	Name: "TransportOrderedFieldInvariant",
	Key:  "prop_2681b4d3add940d3",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀i:(A → B). " +
			"∀ρ:(num → A). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"injective_on(F.carrier, i)",
			"polynomial_formula_wf(φ)",
			"fo_env_ok(F.carrier, polynomial_formula_fv(φ), ρ)",
		},
		Conclusion: "ordered_ring_formula_eval(F, lt, ρ, φ) ⇔ " +
			"ordered_ring_formula_eval(transport_field(i, F), " +
			"    transport_order(i, F.carrier, lt), " +
			"    λv:num. i(ρ(v)), " +
			"    φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		i *Arrow[A, B],
		ρ *Arrow[Nat, A],
		φ *Expr[Formula[IntegerPolynomial]],
		ordered, injective, wf, legal Fact,
	) {
		embedding := a.Have(
			"i embeds F, ordered by lt, into its copy, ordered by the transported order",
			"ordered_field_embedding(F, lt, transport_field(i, F), transport_order(i, F.carrier, lt), i)",
			By(ordered, injective, ordered_field.TransportOrderedField.At(F, lt, i)))
		a.Show(
			"the embedding is onto the copy, whose carrier is the "+
				"image of F's, so it keeps the value of every formula",
			By(
				a.Unfolded(embedding, ordered_field.OrderedEmbeddingDef),
				wf,
				legal,
				ring_transport.TransportFieldDef,
				OntoInvariant.At(
					F,
					lt,
					a.TermAs[FieldOps[B]]("transport_field(i, F)"),
					a.TermAs[Fun2[B, B, Bool]]("transport_order(i, F.carrier, lt)"),
					i,
					ρ,
					φ)))
	}),
})}

// TransportRealClosedField — the copy of a real closed field along a map
// one-to-one on its carrier, ordered by the transported order, is real
// closed. The map is an order embedding of the field into its copy; a
// polynomial over the copy that changes sign between a and b is the image of
// a polynomial p over the field, which changes sign between the preimages of
// a and b, so p has a root x between them, and i(x) is a root of q between a
// and b.
var TransportRealClosedField = transportRealClosedFieldThm{family.Add(registry.ProofEntry{
	Name: "TransportRealClosedField",
	Key:  "prop_3a191f0e2a78dd7",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀i:(A → B).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"injective_on(F.carrier, i)",
		},
		Conclusion: "real_closed_field(transport_field(i, F), transport_order(i, F.carrier, lt))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		i *Arrow[A, B],
		closed real_closed_field.RealClosedFieldFact[on.F],
		injective Fact,
	) {
		orderedF := real_closed_field.OrderedFieldOn.Read(closed)
		intermediate := real_closed_field.IntermediateValue.Read(closed).AsFact()
		fieldF := ordered_field.FieldOn.Read(orderedF)
		ringF := field.RingOn.Read(fieldF)
		carrier := a.TermAs[Set[A]]("F.carrier")
		zero := a.TermAs[A]("F.zero")
		copyF := a.TermAs[FieldOps[B]]("transport_field(i, F)")
		embedding := a.Have(
			"i embeds F, ordered by lt, into its copy, ordered by the transported order",
			"ordered_field_embedding(F, lt, transport_field(i, F), transport_order(i, F.carrier, lt), i)",
			By(orderedF, injective, ordered_field.TransportOrderedField.At(F, lt, i)))
		orderedCopy := a.Have(
			"the transported order orders the copy",
			"ordered_field_on(transport_field(i, F), transport_order(i, F.carrier, lt))",
			By(embedding, ordered_field.OrderedEmbeddingDef))
		homomorphism := a.Have(
			"i is a ring homomorphism from F to its copy",
			"ring_homomorphism(field_ring(F), field_ring(transport_field(i, F)), i)",
			By(embedding, ordered_field.OrderedEmbeddingDef))
		compares := a.Have(
			"i preserves and reflects the order",
			Statement{
				Binders: "∀x y:A.",
				Hypotheses: []string{
					"x ∈ F.carrier",
					"y ∈ F.carrier",
				},
				Conclusion: "lt(x, y) ⇔ transport_order(i, F.carrier, lt, i(x), i(y))",
			},
			By(embedding, ordered_field.OrderedEmbeddingDef))
		fieldCopy := ordered_field.FieldOn.Read(orderedCopy)
		carrierSubfield := field.CarrierSubfield.Read(fieldF)
		zeroIn := comm_ring.ZeroIn.Read(ringF)
		a.Show(
			"the copy is an ordered field with intermediate values",
			real_closed_field.RealClosedField.Intro(
				Case(
					"the transported order orders the copy",
					By(orderedCopy)),
				Case(
					"a polynomial over the copy that changes sign between two points has a root between them",
					Derive(func(b *Argument) {
						q := b.FixAs[Fun[Nat, B]]("q")
						left := b.FixAs[B]("a")
						right := b.FixAs[B]("b")
						given := b.Conjuncts(
							b.Assume(),
							"q is a polynomial over the copy",
							"a lies in the copy",
							"b lies in the copy",
							"a lies below b",
							"q is negative at a",
							"q is positive at b")
						p, pulled := b.UnpackAs[Fun[Nat, A]](
							GroupPremises(injective, zeroIn, given[0], polynomial.PolynomialPullBack.At(i, carrier, zero, q)),
							"p")
						image := b.Conjuncts(
							pulled,
							"p is a polynomial over F",
							"i carries p to q")
						s, sBack := b.ObtainAs[A](
							"a has a preimage s in F",
							"∃s:A. s ∈ F.carrier ∧ i(s) = a",
							By(Normalized, given[1], set_basic.InImage.At(i, carrier, left)))
						t, tBack := b.ObtainAs[A](
							"b has a preimage t in F",
							"∃t:A. t ∈ F.carrier ∧ i(t) = b",
							By(Normalized, given[2], set_basic.InImage.At(i, carrier, right)))
						below := b.Have(
							"s lies below t, i reflecting the order",
							"lt(s, t)",
							By(Normalized, given[3], sBack, tBack, compares.At(s, t)))
						values := b.Have(
							"i carries the value of p at each point of F to the value of q at its image",
							Statement{
								Binders:    "∀x:A.",
								Hypotheses: []string{"x ∈ F.carrier"},
								Conclusion: "i(polynomial_eval(p, x)) = " +
									"polynomial_eval(transport_binary_op(i, F.carrier, F.add), " +
									"    i(F.zero), " +
									"    transport_binary_op(i, F.carrier, F.mul), " +
									"    i(F.one), " +
									"    q, " +
									"    i(x))",
							},
							By(
								fieldF,
								fieldCopy,
								homomorphism,
								carrierSubfield,
								image[0],
								image[1],
								algebraic_element.FieldEmbeddingPolynomials.At(F, copyF, i, carrier, p)))
						negative := b.Have(
							"p is negative at s: i carries its value there to the value of q at a",
							"lt(polynomial_eval(p, s), F.zero)",
							By(
								image[0],
								given[4],
								sBack,
								zeroIn,
								polynomial_evaluation.EvalIn.Read(ringF).AsFact().At(p, s),
								compares.At(b.TermAs[A]("polynomial_eval(p, s)"), zero),
								values.At(s)))
						positive := b.Have(
							"p is positive at t: i carries its value there to the value of q at b",
							"lt(F.zero, polynomial_eval(p, t))",
							By(
								image[0],
								given[5],
								tBack,
								zeroIn,
								polynomial_evaluation.EvalIn.Read(ringF).AsFact().At(p, t),
								compares.At(zero, b.TermAs[A]("polynomial_eval(p, t)")),
								values.At(t)))
						x, root := b.UnpackAs[A](
							GroupPremises(image[0], sBack, tBack, below, negative, positive, intermediate.At(p, s, t)),
							"x")
						b.Take(i.Apply(x))
						b.Show(
							"i(x) lies in the copy between a and b, and q takes there the image of the value of p at x, zero",
							By(
								root,
								sBack,
								tBack,
								compares.At(s, x),
								compares.At(x, t),
								set_image.FunInImage.At(i, carrier, x),
								values.At(x)))
					}))))
	}),
})}

// EliminationAlongInjection — a quantifier-free equivalent over the real
// closed fields on B, each with its order, is one over those on A, once A
// injects into B. A real closed field on A has its copy on B along the
// injection, ordered by the transported order: the copy is real closed, and
// the injection, an order embedding, embeds the ordered atoms of the field
// onto those of the copy, so first_order.EliminationAlongClassEmbedding
// carries the equivalent back.
var EliminationAlongInjection = eliminationAlongInjectionThm{family.Add(registry.ProofEntry{
	Name: "EliminationAlongInjection",
	Key:  "prop_f4276cd03d31ad1b",
	Build: family.Theorem(Statement{
		Binders: "∀φ ψ:fo_formula((num → num) → int). ∀i:(A → B).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
			"fo_quantifier_free_equivalent(«realClosed»⟨A:B⟩, " +
				"    «carrier»⟨A:B⟩, " +
				"    «negative»⟨A:B⟩, " +
				"    integer_polynomial, " +
				"    integer_polynomial_vars, " +
				"    φ, " +
				"    ψ)",
			"injective_on(𝕌, i)",
		},
		Conclusion: "fo_quantifier_free_equivalent(«realClosed», " +
			"    «carrier», " +
			"    «negative», " +
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
		type sourceModel = Prod[FieldOps[A], Fun2[A, A, Bool]]
		type hostModel = Prod[FieldOps[B], Fun2[B, B, Bool]]
		copies := a.Have(
			"every real closed model on A embeds onto its copy along i, a real closed model on B",
			Statement{
				Binders: "∀M:prod(field_ops(A), A → A → bool).",
				Hypotheses: []string{
					"«realClosed»(M)",
				},
				Conclusion: "∃N:prod(field_ops(B), B → B → bool). ∃j:(A → B). " +
					"    «realClosed»(N) ∧ " +
					"    fo_atomic_embedding(«carrier»(M), " +
					"        «carrier»(N), " +
					"        «negative»(M), " +
					"        «negative»(N), " +
					"        integer_polynomial, " +
					"        integer_polynomial_vars, " +
					"        j) ∧ " +
					"    image(j, «carrier»(M)) = «carrier»(N)",
			},
			Derive(func(b *Argument) {
				b.FixAs[sourceModel]("M")
				closed := b.Assume()
				fieldM, orderM := b.TermAs[FieldOps[A]]("fst(M)"), b.TermAs[Fun2[A, A, Bool]]("snd(M)")
				carrierM := b.TermAs[Set[A]]("fst(M).carrier")
				copyField := b.TermAs[FieldOps[B]]("transport_field(i, fst(M))")
				copyOrder := b.TermAs[Fun2[B, B, Bool]]("transport_order(i, fst(M).carrier, snd(M))")
				injectiveM := b.Have(
					"i is one-to-one on the carrier of M's field",
					"injective_on(fst(M).carrier, i)",
					By(
						injective,
						functions.InjectiveOnSubset.At(i, carrierM, b.TermAs[Set[A]]("𝕌")),
						set_order.SubsetUniv.At(carrierM)))
				orderEmbedding := b.Have(
					"i embeds M's field, under M's order, into its copy, under the transported order",
					"ordered_field_embedding(fst(M), "+
						"    snd(M), "+
						"    transport_field(i, fst(M)), "+
						"    transport_order(i, fst(M).carrier, snd(M)), "+
						"    i)",
					By(
						real_closed_field.OrderedFieldOn.Read(closed),
						injectiveM,
						ordered_field.TransportOrderedField.At(fieldM, orderM, i)))
				b.Take(
					b.TermAs[hostModel]("(transport_field(i, fst(M)), transport_order(i, fst(M).carrier, snd(M)))"))
				b.Take(i)
				b.Show(
					"the copy is real closed, and i embeds the ordered atoms of "+
						"M in those of the copy, whose carrier is the image of M's",
					Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
					By(
						closed,
						injectiveM,
						TransportRealClosedField.At(fieldM, orderM, i),
						b.Unfolded(orderEmbedding, ordered_field.OrderedEmbeddingDef),
						OrderedAtomEmbedding.At(fieldM, orderM, copyField, copyOrder, i),
						ring_transport.TransportFieldDef))
			}))
		a.Show(
			"each real closed model on A embeds onto one on B, where ψ is equivalent to φ",
			By(
				a.Unfolded(wf, polynomial_formula.FormulaValidDef),
				equivalent,
				copies,
				first_order.EliminationAlongClassEmbedding.At(
					a.TermAs[Set[sourceModel]]("«realClosed»"),
					a.TermAs[Fun2[sourceModel, A, Bool]]("«carrier»"),
					a.TermAs[Fun3[sourceModel, IntegerPolynomial, Fun[Nat, A], Bool]]("«negative»"),
					a.TermAs[Set[hostModel]]("«realClosed»⟨A:B⟩"),
					a.TermAs[Fun2[hostModel, B, Bool]]("«carrier»⟨A:B⟩"),
					a.TermAs[Fun3[hostModel, IntegerPolynomial, Fun[Nat, B], Bool]]("«negative»⟨A:B⟩"),
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
					φ,
					ψ)))
	}),
})}

// QuantifierFreeSentenceTransfer — all ordered fields agree on closed quantifier-free
// ordered-ring formulas, read at the zero environments: an integer's image is negative in an
// ordered field exactly when the integer is, so the sentence transfer of the formulas read through
// a predicate applies at negativity.
var QuantifierFreeSentenceTransfer = quantifierFreeSentenceTransferThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeSentenceTransfer",
	Key:  "prop_88b166fba4f6240",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀G:field_ops(B). " +
			"∀ls:(B → B → bool). " +
			"∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"ordered_field_on(G, ls)",
			"polynomial_formula_closed(φ)",
			"fo_qf(φ)",
		},
		Conclusion: "ordered_ring_formula_truth(F, lt, φ) ⇔ ordered_ring_formula_truth(G, ls, φ)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		G *Expr[FieldOps[B]],
		ls *Arrow2[B, B, Bool],
		φ *Expr[Formula[IntegerPolynomial]],
		orderedF ordered_field.OrderedFieldFact[on.F],
		orderedG ordered_field.OrderedFieldFact[on.G],
		closed, qf Fact,
	) {
		ringF := field.RingOn.Read(ordered_field.FieldOn.Read(orderedF))
		ringG := field.RingOn.Read(ordered_field.FieldOn.Read(orderedG))
		zero := a.TermAs[Int]("&0")
		signs := a.Have(
			"an integer's image is negative in F exactly when it "+
				"is in G, both exactly when the integer is negative",
			"∀z:int. lt(integer_map(field_ring(F), z), F.zero) ⇔ ls(integer_map(field_ring(G), z), G.zero)",
			a.ForEach(func(z *Expr[Int]) Action {
				return By(
					characteristic_zero.IntegerMapHom.Read(ringF),
					characteristic_zero.IntegerMapHom.Read(ringG),
					ordered_field.IntegerOrderEmbedding.Read(orderedF).At(z, zero),
					ordered_field.IntegerOrderEmbedding.Read(orderedG).At(z, zero))
			}))
		a.Show(
			"the sentence transfer of the formulas read through a predicate, at negativity",
			Simp(Fwd(OrderedRingFormulaTruthDef), Fwd(OrderedRingFormulaEvalDef)),
			Unfold(OrderedRingFormulaAtomDef),
			By(
				ringF,
				ringG,
				signs,
				closed,
				qf,
				polynomial_formula.QuantifierFreeSentenceTransfer.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(F)"),
					a.TermAs[module_record.RingOps[B]]("field_ring(G)"),
					a.TermAs[Set[A]]("λx:A. lt(x, F.zero)"),
					a.TermAs[Set[B]]("λy:B. ls(y, G.zero)"),
					a.TermAs[Fun[Nat, A]]("λv:num. F.zero"),
					a.TermAs[Fun[Nat, B]]("λv:num. G.zero"),
					φ)))
	}),
})}
