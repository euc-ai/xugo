package first_order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

var FormulaData = family.DefineData(registry.DataEntry{
	Name: "Formula", Type: "fo_formula", Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "fo_atom", Args: []string{"A"}},
		{Name: "fo_not", Args: []string{"fo_formula(A)"}},
		{Name: "fo_and", Args: []string{"fo_formula(A)", "fo_formula(A)"}},
		{Name: "fo_exists", Args: []string{"num", "fo_formula(A)"}},
	},
	Principles: registry.DataPrinciples{
		Induction: "FormulaInduction",
		Recursion: "FormulaRecursion",
		Injective: "FormulaInjective",
		Distinct:  "FormulaDistinct",
	},
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		peano.SucNotZero,
		peano.SucInjective,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
})

// FormulaInduction — a property holding at every atom and preserved by negation,
// conjunction and named existential quantification holds of every formula.
var FormulaInduction = formulaInductionThm{FormulaData.Induct}

// EnvUpdateDef — updating one named variable leaves all other names unchanged.
var EnvUpdateDef = envUpdateDefThm{family.Define(registry.DefEntry{
	Name: "EnvUpdateDef", Const: "fo_update", Type: "(num → A) → num → A → num → A",
	Key: "prop_5eb4b3483d11e9e4",
	Equations: []string{
		"∀ρ:(num → A). ∀v:num. ∀a:A. ∀w:num. fo_update(ρ, v, a, w) = COND(w = v, a, ρ(w))",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// EnvOKDef — only variables in the specified support must be assigned carrier elements.
var EnvOKDef = envOKDefThm{family.Define(registry.DefEntry{
	Name: "EnvOKDef", Const: "fo_env_ok", Type: "set(A) → set(num) → (num → A) → bool",
	Key: "prop_1f392ce1175f120f",
	Equations: []string{
		"∀X:set(A). ∀U:set(num). ∀ρ:(num → A). fo_env_ok(X, U, ρ) ⇔ ∀v:num. v ∈ U ⇒ ρ(v) ∈ X",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// FreeVarsDef — free variables are the union of atomic supports with each quantified name removed.
var FreeVarsDef = freeVarsDefThm{family.Define(registry.DefEntry{
	Name: "FreeVarsDef", Const: "fo_fv", Type: "(A → set(num)) → fo_formula(A) → set(num)",
	Key: "prop_9aa2c4e93137fb5",
	Equations: []string{
		"∀S:(A → set(num)). ∀p:A. fo_fv(S, fo_atom(p)) = S(p)",
		"∀S:(A → set(num)). ∀φ:fo_formula(A). fo_fv(S, fo_not(φ)) = fo_fv(S, φ)",
		"∀S:(A → set(num)). ∀φ ψ:fo_formula(A). fo_fv(S, fo_and(φ, ψ)) = fo_fv(S, φ) ∪ fo_fv(S, ψ)",
		"∀S:(A → set(num)). ∀v:num. ∀φ:fo_formula(A). fo_fv(S, fo_exists(v, φ)) = fo_fv(S, φ) ∖ {v}",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// WellFormedDef — well-formed formulas have valid atoms.
var WellFormedDef = wellFormedDefThm{family.Define(registry.DefEntry{
	Name: "WellFormedDef", Const: "fo_wf", Type: "(A → bool) → fo_formula(A) → bool",
	Key: "prop_8237083b5d9cad1a",
	Equations: []string{
		"∀ok:(A → bool). ∀p:A. fo_wf(ok, fo_atom(p)) ⇔ ok(p)",
		"∀ok:(A → bool). ∀φ:fo_formula(A). fo_wf(ok, fo_not(φ)) ⇔ fo_wf(ok, φ)",
		"∀ok:(A → bool). ∀φ ψ:fo_formula(A). fo_wf(ok, fo_and(φ, ψ)) ⇔ fo_wf(ok, φ) ∧ fo_wf(ok, ψ)",
		"∀ok:(A → bool). ∀v:num. ∀φ:fo_formula(A). fo_wf(ok, fo_exists(v, φ)) ⇔ fo_wf(ok, φ)",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// QuantifierFreeDef — quantifier-free formulas contain no existential constructor.
var QuantifierFreeDef = quantifierFreeDefThm{family.Define(registry.DefEntry{
	Name: "QuantifierFreeDef", Const: "fo_qf", Type: "fo_formula(A) → bool",
	Key: "prop_d442f93ddf181170",
	Equations: []string{
		"∀p:A. fo_qf(fo_atom(p)) ⇔ ⊤",
		"∀φ:fo_formula(A). fo_qf(fo_not(φ)) ⇔ fo_qf(φ)",
		"∀φ ψ:fo_formula(A). fo_qf(fo_and(φ, ψ)) ⇔ fo_qf(φ) ∧ fo_qf(ψ)",
		"∀v:num. ∀φ:fo_formula(A). fo_qf(fo_exists(v, φ)) ⇔ ⊥",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// EvalDef — semantics use carrier-restricted quantification and ordinary named-variable shadowing.
var EvalDef = evalDefThm{family.Define(registry.DefEntry{
	Name:  "EvalDef",
	Const: "fo_eval",
	Type:  "set(B) → (A → (num → B) → bool) → (num → B) → fo_formula(A) → bool",
	Key:   "prop_f85158d72918287d",
	Equations: []string{
		"∀X:set(B). ∀e:(A → (num → B) → bool). ∀ρ:(num → B). ∀p:A. fo_eval(X, e, ρ, fo_atom(p)) ⇔ e(p, ρ)",
		"∀X:set(B). ∀e:(A → (num → B) → bool). ∀ρ:(num → B). ∀φ:fo_formula(A). " +
			"    fo_eval(X, e, ρ, fo_not(φ)) ⇔ ¬fo_eval(X, e, ρ, φ)",
		"∀X:set(B). ∀e:(A → (num → B) → bool). ∀ρ:(num → B). ∀φ ψ:fo_formula(A). " +
			"    fo_eval(X, e, ρ, fo_and(φ, ψ)) ⇔ fo_eval(X, e, ρ, φ) ∧ fo_eval(X, e, ρ, ψ)",
		"∀X:set(B). ∀e:(A → (num → B) → bool). ∀ρ:(num → B). ∀v:num. ∀φ:fo_formula(A). " +
			"    fo_eval(X, e, ρ, fo_exists(v, φ)) ⇔ ∃a:B. a ∈ X ∧ fo_eval(X, e, fo_update(ρ, v, a), φ)",
	},
	Deps: []registry.EntryLike{EnvUpdateDef, FormulaData.Recursion},
})}

// ForallDef — universal quantification is the usual derived connective.
var ForallDef = forallDefThm{family.Define(registry.DefEntry{
	Name: "ForallDef", Const: "fo_forall", Type: "num → fo_formula(A) → fo_formula(A)",
	Key:       "prop_282ab53877f7923a",
	Equations: []string{"∀v:num. ∀φ:fo_formula(A). fo_forall(v, φ) = fo_not(fo_exists(v, fo_not(φ)))"},
	Deps:      []registry.EntryLike{FormulaData.Recursion},
})}

// ImpliesDef — implication is expressed using negation and conjunction.
var ImpliesDef = impliesDefThm{family.Define(registry.DefEntry{
	Name: "ImpliesDef", Const: "fo_implies", Type: "fo_formula(A) → fo_formula(A) → fo_formula(A)",
	Key:       "prop_a049c51063c0bb9d",
	Equations: []string{"∀φ ψ:fo_formula(A). fo_implies(φ, ψ) = fo_not(fo_and(φ, fo_not(ψ)))"},
	Deps:      []registry.EntryLike{FormulaData.Recursion},
})}

// OrDef — disjunction is expressed using negation and conjunction.
var OrDef = orDefThm{family.Define(registry.DefEntry{
	Name: "OrDef", Const: "fo_or", Type: "fo_formula(A) → fo_formula(A) → fo_formula(A)",
	Key:       "prop_c1e8adbf40768fca",
	Equations: []string{"∀φ ψ:fo_formula(A). fo_or(φ, ψ) = fo_not(fo_and(fo_not(φ), fo_not(ψ)))"},
	Deps:      []registry.EntryLike{FormulaData.Recursion},
})}

// IffDef — the biconditional is the conjunction of the two implications.
var IffDef = iffDefThm{family.Define(registry.DefEntry{
	Name: "IffDef", Const: "fo_iff", Type: "fo_formula(A) → fo_formula(A) → fo_formula(A)",
	Key: "prop_b3cda95d525b6854",
	Equations: []string{
		"∀φ ψ:fo_formula(A). fo_iff(φ, ψ) = fo_and(fo_implies(φ, ψ), fo_implies(ψ, φ))",
	},
	Deps: []registry.EntryLike{ImpliesDef},
})}

// UpdateShadow — a later binding of the same name overrides the earlier one: the two
// environments agree at every name once the update is unfolded on both sides.
var UpdateShadow = updateShadowThm{family.Add(registry.ProofEntry{
	Name: "UpdateShadow",
	Key:  "prop_ad2cf0c0c62fea14",
	Build: family.Theorem("∀ρ:(num → A). ∀v:num. ∀a b:A. "+
		"    fo_update(fo_update(ρ, v, a), v, b) = fo_update(ρ, v, b)",
		func(arg *Argument, ρ *Arrow[Nat, A], v *Expr[Nat], a, b *Expr[A]) {
			arg.Do(
				Funext(),
				Unfold(EnvUpdateDef),
			)
		}),
})}

// UpdateCommute — updates at distinct names commute: unfolded at a name, the two nested case
// splits agree, since that name cannot be both u and v.
var UpdateCommute = updateCommuteThm{family.Add(registry.ProofEntry{
	Name: "UpdateCommute",
	Key:  "prop_af0a1cdd5db80664",
	Build: family.Theorem(Statement{
		Binders: "∀ρ:(num → A). ∀u v:num. ∀a b:A.",
		Hypotheses: []string{
			"u ≠ v",
		},
		Conclusion: "fo_update(fo_update(ρ, u, a), v, b) = fo_update(fo_update(ρ, v, b), u, a)",
	},
		func(arg *Argument, ρ *Arrow[Nat, A], u, v *Expr[Nat], a, b *Expr[A], distinct Fact) {
			arg.Do(
				Funext(),
				Unfold(EnvUpdateDef),
				By(distinct),
			)
		}),
})}

// FreeVarsFinite — finite atomic supports give finite formula support: by induction on the
// formula, since negation keeps the support, conjunction takes a union of two finite supports
// and an existential removes one name.
var FreeVarsFinite = freeVarsFiniteThm{family.Add(registry.ProofEntry{
	Name: "FreeVarsFinite",
	Key:  "prop_510467900d3f7504",
	Build: family.Theorem(Statement{
		Binders: "∀ok:(A → bool). ∀S:(A → set(num)). ∀φ:fo_formula(A).",
		Hypotheses: []string{
			"∀p:A. ok(p) ⇒ finite(S(p))",
			"fo_wf(ok, φ)",
		},
		Conclusion: "finite(fo_fv(S, φ))",
	},
		func(a *Argument, ok *Expr[Set[A]], S *Arrow2[A, Nat, Bool], φ *Expr[Formula[A]], atoms, wf Fact) {
			finiteSupport := a.TermAs[Set[Formula[A]]]("λψ:fo_formula(A). fo_wf(ok, ψ) ⇒ finite(fo_fv(S, ψ))")
			a.Show(
				"every well-formed formula has finite support, φ among them",
				ByInduction(FormulaInduction.At(finiteSupport, φ), wf,
					Case(
						"a valid atom's support is its declared support, which is finite",
						Simp(Fwd(WellFormedDef), Fwd(FreeVarsDef)),
						By(atoms)),
					Case(
						"a negation is well formed when its body is, and has the same support",
						Simp(Fwd(WellFormedDef), Fwd(FreeVarsDef)),
						Basic()),
					Case(
						"a conjunction's support is the union of its conjuncts' finite supports",
						Simp(Fwd(WellFormedDef), Fwd(FreeVarsDef)),
						By(finite_set.FiniteUnionImp)),
					Case(
						"an existential's support is its body's finite support with one name removed",
						Simp(Fwd(WellFormedDef), Fwd(FreeVarsDef)),
						By(finite_set.FiniteDiff))))
		}),
})}

// ExistsSupportBelow — an existential at the name k binds k: when the names of the body lie
// below k + 1, the names of the quantified formula, the body's without k, lie below k. A
// universal at k is read through ForallDef, as the negated existential at k of its negated body,
// and a negation keeps its body's names; so this member serves it too, and has no Forall twin.
var ExistsSupportBelow = existsSupportBelowThm{family.Add(registry.ProofEntry{
	Name: "ExistsSupportBelow",
	Key:  "prop_8bd6cdab5ce9f9e2",
	Build: family.Theorem(Statement{
		Binders: "∀S:(A → set(num)). ∀k:num. ∀φ:fo_formula(A).",
		Hypotheses: []string{
			"fo_fv(S, φ) ⊆ {v:num | v < k + 1}",
		},
		Conclusion: "fo_fv(S, fo_exists(k, φ)) ⊆ {v:num | v < k}",
	}, func(a *Argument, S *Arrow[A, Set[Nat]], k *Expr[Nat], φ *Expr[Formula[A]], bound Fact) {
		below := a.Have(
			"a name below k + 1 other than k lies below k",
			"∀v:num. v < k + 1 ∧ v ≠ k ⇒ v < k",
			ByArith())
		a.Show(
			"the quantifier removes k from the body's names, which lie below k + 1",
			Simp(Fwd(FreeVarsDef)),
			BySets(bound, below))
	}),
})}

// WellFormedMono — a formula valid for one atom predicate is valid for any weaker one: by
// induction on the formula, validity asking only that each atom satisfy the predicate.
var WellFormedMono = wellFormedMonoThm{family.Add(registry.ProofEntry{
	Name: "WellFormedMono",
	Key:  "prop_594f3c1b0f2e0e46",
	Build: family.Theorem(Statement{
		Binders: "∀ok ok':(A → bool). ∀φ:fo_formula(A).",
		Hypotheses: []string{
			"fo_wf(ok, φ)",
			"∀p:A. ok(p) ⇒ ok'(p)",
		},
		Conclusion: "fo_wf(ok', φ)",
	}, func(a *Argument, ok, okPrime *Expr[Set[A]], φ *Expr[Formula[A]], wf, weaker Fact) {
		valid := a.TermAs[Set[Formula[A]]]("λψ:fo_formula(A). fo_wf(ok, ψ) ⇒ fo_wf(ok', ψ)")
		a.Show(
			"every formula valid for ok is valid for ok', by induction on its shape",
			ByInduction(FormulaInduction.At(valid, φ), wf,
				Case(
					"an atom satisfying ok satisfies ok'",
					Simp(Fwd(WellFormedDef)),
					By(weaker)),
				Case(
					"a negation is valid with its body",
					Simp(Fwd(WellFormedDef)),
					Basic()),
				Case(
					"a conjunction is valid with both conjuncts",
					Simp(Fwd(WellFormedDef)),
					Derive(func(b *Argument) {
						b.FixAs[Formula[A]]("ψ")
						b.FixAs[Formula[A]]("χ")
						ihψ, ihχ := b.Assume(), b.Assume()
						both := b.Assume()
						b.Show(
							"each conjunct valid for ok is valid for ok'",
							By(ihψ, ihχ, both))
					})),
				Case(
					"an existential is valid with its body",
					Simp(Fwd(WellFormedDef)),
					Basic())))
	}),
})}

// EvalForall — the derived universal quantifier ranges over the carrier: the universal is
// the negated existential of the negation, and no carrier element refutes φ exactly when
// every carrier element satisfies it.
var EvalForall = evalForallThm{family.Add(registry.ProofEntry{
	Name: "EvalForall",
	Key:  "prop_2dc747d474c5a12d",
	Build: family.Theorem("∀X:set(B). "+
		"∀e:(A → (num → B) → bool). "+
		"∀ρ:(num → B). "+
		"∀v:num. "+
		"∀φ:fo_formula(A). "+
		"    fo_eval(X, e, ρ, fo_forall(v, φ)) ⇔ ∀a:B. a ∈ X ⇒ fo_eval(X, e, fo_update(ρ, v, a), φ)",
		func(
			a *Argument,
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			ρ *Arrow[Nat, B],
			v *Expr[Nat],
			φ *Expr[Formula[A]],
		) {
			a.Do(
				Simp(Fwd(ForallDef), Fwd(EvalDef)),
				Basic(),
			)
		}),
})}

// ExistsQuantifierBridge — an existential quantifier at the name s reads as an existential
// quantifier over the carrier, whatever the evaluator: a witness of the quantifier is a carrier
// value a whose update of σ at s satisfies the body, and such an update is carrier-valued, agrees
// with σ below s and reads a at s, so the hypothesis matches the body with what Q says of a.
var ExistsQuantifierBridge = existsQuantifierBridgeThm{family.Add(registry.ProofEntry{
	Name: "ExistsQuantifierBridge",
	Key:  "prop_8487261e796f498a",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(B). " +
			"∀e:(A → (num → B) → bool). " +
			"∀s:num. " +
			"∀σ:(num → B). " +
			"∀φ:fo_formula(A). " +
			"∀Q:(B → bool).",
		Hypotheses: []string{
			"fo_env_ok(X, 𝕌, σ)",
			"∀τ:(num → B). ∀a:B. " +
				"    fo_env_ok(X, 𝕌, τ) ∧ (∀v:num. v < s ⇒ τ(v) = σ(v)) ∧ a ∈ X ∧ τ(s) = a ⇒ " +
				"    (Q(a) ⇔ fo_eval(X, e, τ, φ))",
		},
		Conclusion: "(∃a:B. a ∈ X ∧ Q(a)) ⇔ fo_eval(X, e, σ, fo_exists(s, φ))",
	}, func(
		arg *Argument,
		X *Expr[Set[B]],
		e *Arrow2[A, Fun[Nat, B], Bool],
		s *Expr[Nat],
		σ *Arrow[Nat, B],
		φ *Expr[Formula[A]],
		Q *Arrow[B, Bool],
		env, body Fact,
	) {
		updated := arg.Have(
			"at a carrier value written at s, the body says what Q says of it",
			"∀a:B. a ∈ X ⇒ (Q(a) ⇔ fo_eval(X, e, fo_update(σ, s, a), φ))",
			Derive(func(b *Argument) {
				a := b.FixAs[B]("a")
				inCarrier := b.Assume()
				τ := b.TermAs[Fun[Nat, B]]("fo_update(σ, s, a)")
				legal := b.Have(
					"the updated environment is carrier-valued",
					"fo_env_ok(X, 𝕌, fo_update(σ, s, a))",
					By(
						env,
						inCarrier,
						EnvOKSubset.At(X, b.TermAs[Set[Nat]]("𝕌 ∖ {s}"), b.TermAs[Set[Nat]]("𝕌"), σ),
						set_order.SubsetUniv,
						EnvOKUpdate.At(X, b.TermAs[Set[Nat]]("𝕌"), σ, s, a)))
				reads := b.Have(
					"it agrees with σ below s and reads a at s",
					"(∀v:num. v < s ⇒ fo_update(σ, s, a, v) = σ(v)) ∧ fo_update(σ, s, a, s) = a",
					Simp(Fwd(EnvUpdateDef)),
					ByArith())
				b.Show(
					"so the hypothesis holds there",
					By(legal, reads, inCarrier, body.At(τ, a)))
			}))
		arg.Show(
			"a witness of the quantifier is a carrier value whose update of σ at s satisfies the body",
			Simp(Fwd(EvalDef)),
			By(updated))
	}),
})}

// ForallQuantifierBridge — a universal quantifier at the name s reads as a universal quantifier
// over the carrier, whatever the evaluator: the universal is the negated existential of the
// negated body (ForallDef), and ExistsQuantifierBridge, read at the negated body and at the
// carrier values Q fails at, says that existential holds exactly when Q fails at some carrier
// value.
var ForallQuantifierBridge = forallQuantifierBridgeThm{family.Add(registry.ProofEntry{
	Name: "ForallQuantifierBridge",
	Key:  "prop_3a77477a4ee777a6",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(B). " +
			"∀e:(A → (num → B) → bool). " +
			"∀s:num. " +
			"∀σ:(num → B). " +
			"∀φ:fo_formula(A). " +
			"∀Q:(B → bool).",
		Hypotheses: []string{
			"fo_env_ok(X, 𝕌, σ)",
			"∀τ:(num → B). ∀a:B. " +
				"    fo_env_ok(X, 𝕌, τ) ∧ (∀v:num. v < s ⇒ τ(v) = σ(v)) ∧ a ∈ X ∧ τ(s) = a ⇒ " +
				"    (Q(a) ⇔ fo_eval(X, e, τ, φ))",
		},
		Conclusion: "(∀a:B. a ∈ X ⇒ Q(a)) ⇔ fo_eval(X, e, σ, fo_forall(s, φ))",
	}, func(
		arg *Argument,
		X *Expr[Set[B]],
		e *Arrow2[A, Fun[Nat, B], Bool],
		s *Expr[Nat],
		σ *Arrow[Nat, B],
		φ *Expr[Formula[A]],
		Q *Arrow[B, Bool],
		env, body Fact,
	) {
		negated := arg.Have(
			"the negated body says what ¬Q says of the carrier value an environment reads at s",
			Statement{
				Binders: "∀τ:(num → B). ∀a:B.",
				Hypotheses: []string{
					"fo_env_ok(X, 𝕌, τ)",
					"∀v:num. v < s ⇒ τ(v) = σ(v)",
					"a ∈ X",
					"τ(s) = a",
				},
				Conclusion: "¬Q(a) ⇔ fo_eval(X, e, τ, fo_not(φ))",
			},
			Simp(Fwd(EvalDef)),
			By(Normalized, body))
		negatedBody := arg.TermAs[Formula[A]]("fo_not(φ)")
		failsAt := arg.TermAs[Set[B]]("λa:B. ¬Q(a)")
		failing := arg.Have(
			"Q fails at some carrier value exactly when the negated body holds at some update of σ at s",
			"(∃a:B. a ∈ X ∧ ¬Q(a)) ⇔ fo_eval(X, e, σ, fo_exists(s, fo_not(φ)))",
			By(env, negated, ExistsQuantifierBridge.At(X, e, s, σ, negatedBody, failsAt)))
		arg.Show(
			"the universal is the negated existential of the negated "+
				"body, so it holds exactly when Q fails at no carrier value",
			Simp(Fwd(ForallDef), Fwd(EvalDef)),
			By(arg.Simplified(failing, Fwd(EvalDef))))
	}),
})}

// OrSemantics — a disjunction holds exactly when one of its disjuncts does: the disjunction is
// the negated conjunction of the two negations, and not both disjuncts fail exactly when one
// of them holds.
var OrSemantics = orSemanticsThm{family.Add(registry.ProofEntry{
	Name: "OrSemantics",
	Key:  "prop_5e776ae5e7fdbf38",
	Build: family.Theorem("∀X:set(B). ∀e:(A → (num → B) → bool). ∀ρ:(num → B). ∀φ ψ:fo_formula(A). "+
		"    fo_eval(X, e, ρ, fo_or(φ, ψ)) ⇔ fo_eval(X, e, ρ, φ) ∨ fo_eval(X, e, ρ, ψ)",
		func(
			a *Argument,
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			ρ *Arrow[Nat, B],
			φ, ψ *Expr[Formula[A]],
		) {
			a.Do(
				Simp(Fwd(OrDef), Fwd(EvalDef)),
				Basic(),
			)
		}),
})}

// ImpliesSemantics — an implication holds exactly when its antecedent fails or its consequent
// holds: the implication is the negated conjunction of its antecedent with the negated
// consequent, which fails exactly when the antecedent holds and the consequent does not.
var ImpliesSemantics = impliesSemanticsThm{family.Add(registry.ProofEntry{
	Name: "ImpliesSemantics",
	Key:  "prop_3b757e4e5e80b358",
	Build: family.Theorem("∀X:set(B). ∀e:(A → (num → B) → bool). ∀ρ:(num → B). ∀φ ψ:fo_formula(A). "+
		"    fo_eval(X, e, ρ, fo_implies(φ, ψ)) ⇔ (fo_eval(X, e, ρ, φ) ⇒ fo_eval(X, e, ρ, ψ))",
		func(
			a *Argument,
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			ρ *Arrow[Nat, B],
			φ, ψ *Expr[Formula[A]],
		) {
			a.Do(
				Simp(Fwd(ImpliesDef), Fwd(EvalDef)),
				Basic(),
			)
		}),
})}

// IffSemantics — a biconditional holds exactly when its two sides agree: it is the conjunction of
// the two implications, which hold together exactly when the sides agree.
var IffSemantics = iffSemanticsThm{family.Add(registry.ProofEntry{
	Name: "IffSemantics",
	Key:  "prop_f9bbd5390ca53fcd",
	Build: family.Theorem("∀X:set(B). ∀e:(A → (num → B) → bool). ∀ρ:(num → B). ∀φ ψ:fo_formula(A). "+
		"    fo_eval(X, e, ρ, fo_iff(φ, ψ)) ⇔ (fo_eval(X, e, ρ, φ) ⇔ fo_eval(X, e, ρ, ψ))",
		func(
			a *Argument,
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			ρ *Arrow[Nat, B],
			φ, ψ *Expr[Formula[A]],
		) {
			a.Do(
				Simp(Fwd(IffDef), Fwd(EvalDef), Fwd(ImpliesSemantics)),
				Basic(),
			)
		}),
})}

// ConstantFormula — each truth value is the value, under every carrier,
// interpretation and environment, of a closed valid quantifier-free formula
// built on a valid atom p with no free variable: the conjunction of p with its
// negation is false everywhere, and the negation of that conjunction is true
// everywhere.
var ConstantFormula = constantFormulaThm{family.Add(registry.ProofEntry{
	Name: "ConstantFormula",
	Key:  "prop_5b01a8313da859d8",
	Build: family.Theorem(Statement{
		Binders: "∀ok:(A → bool). ∀S:(A → set(num)). ∀p:A. ∀b:bool.",
		Hypotheses: []string{
			"ok(p)",
			"S(p) = ∅",
		},
		Conclusion: "∃χ:fo_formula(A). " +
			"    fo_wf(ok, χ) ∧ " +
			"    fo_qf(χ) ∧ " +
			"    fo_fv(S, χ) = ∅ ∧ " +
			"    (∀X:set(B). ∀e:(A → (num → B) → bool). ∀ρ:(num → B). fo_eval(X, e, ρ, χ) ⇔ b)",
	}, func(
		a *Argument,
		ok *Expr[Set[A]],
		S *Arrow2[A, Nat, Bool],
		p *Expr[A],
		b *Expr[Bool],
		valid, closed Fact,
	) {
		evaluated := Simp(Fwd(WellFormedDef), Fwd(QuantifierFreeDef), Fwd(FreeVarsDef), Fwd(EvalDef))
		a.Cases(b)
		a.When(
			"a true value is the value of the negated contradiction",
			func(c *Argument, holds Fact) {
				c.Take(c.TermAs[Formula[A]]("fo_not(fo_and(fo_atom(p), fo_not(fo_atom(p))))"))
				c.Show(
					"which is valid and closed, and true everywhere",
					evaluated,
					BySets(valid, closed, holds))
			})
		a.Otherwise(
			"a false value is the value of the contradiction",
			func(c *Argument, fails Fact) {
				c.Take(c.TermAs[Formula[A]]("fo_and(fo_atom(p), fo_not(fo_atom(p)))"))
				c.Show(
					"which is valid and closed, and false everywhere",
					evaluated,
					BySets(valid, closed, fails))
			})
	}),
})}

// AtomLocalDef — an atomic interpretation depends only on the declared variable support.
var AtomLocalDef = atomLocalDefThm{family.Define(registry.DefEntry{
	Name:  "AtomLocalDef",
	Const: "fo_atom_local",
	Type:  "(A → bool) → (A → set(num)) → (A → (num → B) → bool) → bool",
	Key:   "prop_c2861c5e1bd02b56",
	Equations: []string{
		"∀ok:(A → bool). ∀S:(A → set(num)). ∀e:(A → (num → B) → bool). " +
			"    fo_atom_local(ok, S, e) ⇔ " +
			"    ∀p:A. ∀ρ σ:(num → B). ok(p) ∧ (∀v:num. v ∈ S(p) ⇒ ρ(v) = σ(v)) ⇒ (e(p, ρ) ⇔ e(p, σ))",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// EvalSimulation — a simulation between two interpretations gives every
// well-formed formula one value at related environments. The simulation is a
// relation R between their environments for each formula: related
// environments agree on a valid atom, a negation or a conjunction passes the
// relation to its parts, and at an existential every witness on either side
// is matched by one on the other with the updated environments related at the
// body. By induction on the formula, the environments left free in the
// induction hypothesis: the existential's two witnesses are carried across by
// the matching, and the body's values agree there.
var EvalSimulation = evalSimulationThm{family.Add(registry.ProofEntry{
	Name: "EvalSimulation",
	Key:  "prop_8c6024935d7edf64",
	Build: family.Theorem(Statement{
		Binders: "∀ok:(A → bool). " +
			"∀X:set(B). " +
			"∀e:(A → (num → B) → bool). " +
			"∀Y:set(C). " +
			"∀f:(A → (num → C) → bool). " +
			"∀R:(fo_formula(A) → (num → B) → (num → C) → bool). " +
			"∀ρ:(num → B). " +
			"∀σ:(num → C). " +
			"∀φ:fo_formula(A).",
		Hypotheses: []string{
			"∀p:A. ∀ρ:(num → B). ∀σ:(num → C). ok(p) ∧ R(fo_atom(p), ρ, σ) ⇒ (e(p, ρ) ⇔ f(p, σ))",
			"∀ψ:fo_formula(A). ∀ρ:(num → B). ∀σ:(num → C). R(fo_not(ψ), ρ, σ) ⇒ R(ψ, ρ, σ)",
			"∀ψ χ:fo_formula(A). ∀ρ:(num → B). ∀σ:(num → C). R(fo_and(ψ, χ), ρ, σ) ⇒ R(ψ, ρ, σ) ∧ R(χ, ρ, σ)",
			"∀v:num. ∀ψ:fo_formula(A). ∀ρ:(num → B). ∀σ:(num → C). " +
				"    R(fo_exists(v, ψ), ρ, σ) ⇒ " +
				"    (∀x:B. x ∈ X ⇒ ∃y:C. y ∈ Y ∧ R(ψ, fo_update(ρ, v, x), fo_update(σ, v, y))) ∧ " +
				"    (∀y:C. y ∈ Y ⇒ ∃x:B. x ∈ X ∧ R(ψ, fo_update(ρ, v, x), fo_update(σ, v, y)))",
			"fo_wf(ok, φ)",
			"R(φ, ρ, σ)",
		},
		Conclusion: "fo_eval(X, e, ρ, φ) ⇔ fo_eval(Y, f, σ, φ)",
	},
		func(
			a *Argument,
			ok *Expr[Set[A]],
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			Y *Expr[Set[C]],
			f *Arrow2[A, Fun[Nat, C], Bool],
			R *Expr[Fun3[Formula[A], Fun[Nat, B], Fun[Nat, C], Bool]],
			ρ *Arrow[Nat, B],
			σ *Arrow[Nat, C],
			φ *Expr[Formula[A]],
			atoms, negation, conjunction, existential, wf, related Fact,
		) {
			simulated := a.TermAs[Set[Formula[A]]](
				"λψ:fo_formula(A). ∀ρ:(num → B). ∀σ:(num → C). " +
					"    fo_wf(ok, ψ) ∧ R(ψ, ρ, σ) ⇒ (fo_eval(X, e, ρ, ψ) ⇔ fo_eval(Y, f, σ, ψ))")
			a.Show(
				"every well-formed formula takes one value at any two related environments",
				ByInduction(FormulaInduction.At(simulated, φ), wf, related,
					Case(
						"related environments give a valid atom one value",
						Derive(func(b *Argument) {
							p := b.FixAs[A]("p")
							ρ1, σ1 := b.FixAs[Fun[Nat, B]]("ρ'"), b.FixAs[Fun[Nat, C]]("σ'")
							guards := b.Simplified(b.Assume(), Fwd(WellFormedDef))
							b.Show(
								"the atom's two values agree",
								Simp(Fwd(EvalDef)),
								By(atoms.At(p, ρ1, σ1), guards))
						})),
					Case(
						"a negation relates its body, and negates its value",
						Derive(func(b *Argument) {
							ψ := b.FixAs[Formula[A]]("ψ")
							ih := b.Assume()
							ρ1, σ1 := b.FixAs[Fun[Nat, B]]("ρ'"), b.FixAs[Fun[Nat, C]]("σ'")
							guards := b.Simplified(b.Assume(), Fwd(WellFormedDef))
							b.Show(
								"the body takes one value at the two environments",
								Simp(Fwd(EvalDef)),
								By(Normalized, ih.At(ρ1, σ1), guards, negation.At(ψ, ρ1, σ1)))
						})),
					Case(
						"a conjunction relates both conjuncts",
						Derive(func(b *Argument) {
							ψ := b.FixAs[Formula[A]]("ψ")
							χ := b.FixAs[Formula[A]]("χ")
							ihψ, ihχ := b.Assume(), b.Assume()
							ρ1, σ1 := b.FixAs[Fun[Nat, B]]("ρ'"), b.FixAs[Fun[Nat, C]]("σ'")
							guards := b.Simplified(b.Assume(), Fwd(WellFormedDef))
							b.Show(
								"each conjunct takes one value at the two environments",
								Simp(Fwd(EvalDef)),
								By(Normalized, ihψ.At(ρ1, σ1), ihχ.At(ρ1, σ1), guards, conjunction.At(ψ, χ, ρ1, σ1)))
						})),
					Case(
						"at an existential, the matching carries a witness across in each direction",
						Derive(func(b *Argument) {
							v := b.FixAs[Nat]("v")
							ψ := b.FixAs[Formula[A]]("ψ")
							ih := b.Assume()
							ρ1, σ1 := b.FixAs[Fun[Nat, B]]("ρ'"), b.FixAs[Fun[Nat, C]]("σ'")
							guards := b.Conjuncts(
								b.Assume(),
								"the existential is well formed",
								"the two environments are related at the existential")
							wfBody := b.Simplified(guards[0], Fwd(WellFormedDef))
							matching := b.Conjuncts(
								GroupPremises(guards[1], existential.At(v, ψ, ρ1, σ1)),
								"every witness in X is matched by one in Y",
								"every witness in Y is matched by one in X")
							b.Show(
								"a witness on either side, matched on the other, gives the body one value there",
								Simp(Fwd(EvalDef)),
								By(ih, wfBody, matching[0], matching[1]))
						}))))
		}),
})}

// EvalCongruence — environments agreeing on free variables give the same truth
// value: agreement on a formula's support is a simulation of the
// interpretation with itself. Atomic locality gives a valid atom one value at
// agreeing environments, a negation and a conjunction pass agreement to their
// parts, whose supports lie in theirs, and at an existential each witness is
// matched by itself, since the two environments updated at the quantified name
// by one value still agree on the body's support.
var EvalCongruence = evalCongruenceThm{family.Add(registry.ProofEntry{
	Name: "EvalCongruence",
	Key:  "prop_d2c50e00c6ba045",
	Build: family.Theorem(Statement{
		Binders: "∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀X:set(B). " +
			"∀e:(A → (num → B) → bool). " +
			"∀ρ σ:(num → B). " +
			"∀φ:fo_formula(A).",
		Hypotheses: []string{
			"fo_atom_local(ok, S, e)",
			"fo_wf(ok, φ)",
			"∀v:num. v ∈ fo_fv(S, φ) ⇒ ρ(v) = σ(v)",
		},
		Conclusion: "fo_eval(X, e, ρ, φ) ⇔ fo_eval(X, e, σ, φ)",
	},
		func(
			a *Argument,
			ok *Expr[Set[A]],
			S *Arrow2[A, Nat, Bool],
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			ρ, σ *Arrow[Nat, B],
			φ *Expr[Formula[A]],
			local, wf, agree Fact,
		) {
			R, agreeing := a.LetAs[Fun3[Formula[A], Fun[Nat, B], Fun[Nat, B], Bool]](
				"R",
				"λψ:fo_formula(A). λρ:(num → B). λσ:(num → B). ∀w:num. w ∈ fo_fv(S, ψ) ⇒ ρ(w) = σ(w)")
			atoms := a.Have(
				"environments agreeing on a valid atom's support give it one value, by atomic locality",
				"∀p:A. ∀ρ σ:(num → B). ok(p) ∧ R(fo_atom(p), ρ, σ) ⇒ (e(p, ρ) ⇔ e(p, σ))",
				agreeing.Rw(),
				Simp(Fwd(FreeVarsDef)),
				By(local, AtomLocalDef))
			negation := a.Have(
				"a negation has the support of its body",
				"∀ψ:fo_formula(A). ∀ρ σ:(num → B). R(fo_not(ψ), ρ, σ) ⇒ R(ψ, ρ, σ)",
				agreeing.Rw(),
				Simp(Fwd(FreeVarsDef)),
				Basic())
			conjunction := a.Have(
				"a conjunction's support is the union of its conjuncts' supports",
				"∀ψ χ:fo_formula(A). ∀ρ σ:(num → B). R(fo_and(ψ, χ), ρ, σ) ⇒ R(ψ, ρ, σ) ∧ R(χ, ρ, σ)",
				agreeing.Rw(),
				Simp(Fwd(FreeVarsDef), Fwd(set_basic.ForallInUnion)),
				Basic())
			existential := a.Have(
				"at an existential, each witness is matched by itself",
				Statement{
					Binders: "∀v:num. ∀ψ:fo_formula(A). ∀ρ σ:(num → B).",
					Hypotheses: []string{
						"R(fo_exists(v, ψ), ρ, σ)",
					},
					Conclusion: "(∀x:B. x ∈ X ⇒ ∃y:B. y ∈ X ∧ R(ψ, fo_update(ρ, v, x), fo_update(σ, v, y))) ∧ " +
						"(∀y:B. y ∈ X ⇒ ∃x:B. x ∈ X ∧ R(ψ, fo_update(ρ, v, x), fo_update(σ, v, y)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("v")
					b.FixAs[Formula[A]]("ψ")
					b.FixAs[Fun[Nat, B]]("ρ'")
					b.FixAs[Fun[Nat, B]]("σ'")
					offName := b.Simplified(b.Assume(), Fwd(agreeing), Fwd(FreeVarsDef), Fwd(set_basic.InDiff))
					updatesAgree := b.Have(
						"updated at v by one value, the environments agree on the support "+
							"of ψ: at v both take the new value, elsewhere the old ones agree",
						"∀x:B. R(ψ, fo_update(ρ', v, x), fo_update(σ', v, x))",
						agreeing.Rw(),
						By(offName, EnvUpdateDef, set_basic.InSing))
					b.Show(
						"so each witness is matched by itself",
						SplitConj(
							Case(
								"a witness x for ρ' is matched by x for σ'",
								Derive(func(c *Argument) {
									x := c.FixAs[B]("x")
									inX := c.Assume()
									c.Take(x)
									c.Show(
										"x lies in X, and the two environments updated by x agree",
										By(inX, updatesAgree.At(x)))
								})),
							Case(
								"a witness y for σ' is matched by y for ρ'",
								Derive(func(c *Argument) {
									y := c.FixAs[B]("y")
									inX := c.Assume()
									c.Take(y)
									c.Show(
										"y lies in X, and the two environments updated by y agree",
										By(inX, updatesAgree.At(y)))
								}))))
				}))
			a.Show(
				"so φ takes one value at ρ and σ",
				By(
					EvalSimulation.At(ok, X, e, X, e, R, ρ, σ, φ),
					atoms,
					negation,
					conjunction,
					existential,
					wf,
					agree))
		}),
})}

// EnvOKUnion — an environment is legal on a union of supports exactly when it is legal on each
// part: unfolded, a name of the union is a name of one part, and a name of either part is a
// name of the union.
var EnvOKUnion = envOKUnionThm{family.Add(registry.ProofEntry{
	Name: "EnvOKUnion",
	Key:  "prop_3d225b0de5cc46b6",
	Build: family.Theorem("∀X:set(A). ∀U V:set(num). ∀ρ:(num → A). "+
		"    fo_env_ok(X, U ∪ V, ρ) ⇔ fo_env_ok(X, U, ρ) ∧ fo_env_ok(X, V, ρ)",
		func(a *Argument, X *Expr[Set[A]], U, V *Expr[Set[Nat]], ρ *Arrow[Nat, A]) {
			a.Do(Simp(Fwd(EnvOKDef), Fwd(set_basic.InUnion)))
			a.Iff()
			a.Forward(
				"legal on each part, hence on the union: a name of the union lies in one part",
				func(b *Argument, onEach Fact) {
					b.Show(
						"every name of the union is assigned a carrier element",
						By(onEach))
				})
			a.Backward(
				"legal on the union, hence on each part: a name of either part lies in the union",
				func(b *Argument, onUnion Fact) {
					b.Show(
						"every name of either part is assigned a carrier element",
						By(onUnion))
				})
		}),
})}

// EnvOKSubset — an environment legal on a support is legal on every part of it: a name of the
// part is a name of the whole, where the environment takes carrier values.
var EnvOKSubset = envOKSubsetThm{family.Add(registry.ProofEntry{
	Name: "EnvOKSubset",
	Key:  "prop_58ea02b6aea5d702",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(A). ∀U V:set(num). ∀ρ:(num → A).",
		Hypotheses: []string{
			"U ⊆ V",
			"fo_env_ok(X, V, ρ)",
		},
		Conclusion: "fo_env_ok(X, U, ρ)",
	},
		func(a *Argument, X *Expr[Set[A]], U, V *Expr[Set[Nat]], ρ *Arrow[Nat, A], part, legal Fact) {
			a.Show(
				"every name of U is a name of V, which ρ assigns a carrier element",
				By(part, legal, EnvOKDef, set_basic.SubsetDef))
		}),
})}

// EnvOKUpdate — an environment legal on a support away from v, updated at v by a carrier
// element, is legal on the whole support: at v the update takes that element, and at every
// other name of the support it keeps the old value.
var EnvOKUpdate = envOKUpdateThm{family.Add(registry.ProofEntry{
	Name: "EnvOKUpdate",
	Key:  "prop_3f971e230938655",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(A). ∀U:set(num). ∀ρ:(num → A). ∀v:num. ∀a:A.",
		Hypotheses: []string{
			"fo_env_ok(X, U ∖ {v}, ρ)",
			"a ∈ X",
		},
		Conclusion: "fo_env_ok(X, U, fo_update(ρ, v, a))",
	},
		func(
			arg *Argument,
			X *Expr[Set[A]],
			U *Expr[Set[Nat]],
			ρ *Arrow[Nat, A],
			v *Expr[Nat],
			a *Expr[A],
			legal, inCarrier Fact,
		) {
			arg.Show(
				"at v the update takes the value a, and every other name of U lies in U ∖ {v}",
				By(legal, inCarrier, EnvOKDef, EnvUpdateDef, set_basic.InDiff, set_basic.InSing))
		}),
})}

// EnvOKEmpty — every environment is legal on the empty support: legality asks for a carrier
// value at each name of the support, and no name lies in the empty set.
var EnvOKEmpty = envOKEmptyThm{family.Add(registry.ProofEntry{
	Name: "EnvOKEmpty",
	Key:  "prop_69f862c943e85a5a",
	Build: family.Theorem("∀X:set(A). ∀ρ:(num → A). fo_env_ok(X, ∅, ρ)",
		func(a *Argument, X *Expr[Set[A]], ρ *Arrow[Nat, A]) {
			a.Show(
				"no name lies in the empty support, so legality asks nothing of ρ",
				By(EnvOKDef.At(X, a.TermAs[Set[Nat]]("∅"), ρ), set_basic.NotInEmpty))
		}),
})}

// AllRangeDef — universally quantify a consecutive block of distinct names.
var AllRangeDef = allRangeDefThm{family.Define(registry.DefEntry{
	Name: "AllRangeDef", Const: "fo_all_range", Type: "num → num → fo_formula(A) → fo_formula(A)",
	Key: "prop_78c2208f51437983",
	Equations: []string{
		"∀s:num. ∀φ:fo_formula(A). fo_all_range(s, 0, φ) = φ",
		"∀s n:num. ∀φ:fo_formula(A). fo_all_range(s, suc(n), φ) = fo_forall(s + n, fo_all_range(s, n, φ))",
	},
	Deps: []registry.EntryLike{ForallDef, FormulaData.Recursion},
})}

// ExistsRangeDef — existentially quantify a consecutive block of distinct names.
var ExistsRangeDef = existsRangeDefThm{family.Define(registry.DefEntry{
	Name: "ExistsRangeDef", Const: "fo_exists_range", Type: "num → num → fo_formula(A) → fo_formula(A)",
	Key: "prop_2d8ed2300e8d94b4",
	Equations: []string{
		"∀s:num. ∀φ:fo_formula(A). fo_exists_range(s, 0, φ) = φ",
		"∀s n:num. ∀φ:fo_formula(A). " +
			"    fo_exists_range(s, suc(n), φ) = fo_exists(s + n, fo_exists_range(s, n, φ))",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// UpdateRangeDef — simultaneously update a consecutive variable block from a tuple.
var UpdateRangeDef = updateRangeDefThm{family.Define(registry.DefEntry{
	Name:  "UpdateRangeDef",
	Const: "fo_update_range",
	Type:  "(num → A) → num → num → (num → A) → num → A",
	Key:   "prop_81abb3f5944fdb45",
	Equations: []string{
		"∀ρ:(num → A). ∀s n:num. ∀x:(num → A). ∀v:num. " +
			"    fo_update_range(ρ, s, n, x, v) = COND(s ≤ v ∧ v < s + n, x(v - s), ρ(v))",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// UpdateRangeEmpty — a block of length zero leaves the environment unchanged: unfolded at a
// name, the block's range s ≤ w < s + 0 holds of no name.
var UpdateRangeEmpty = updateRangeEmptyThm{family.Add(registry.ProofEntry{
	Name: "UpdateRangeEmpty",
	Key:  "prop_5a62f5012d66d3eb",
	Build: family.Theorem("∀ρ:(num → A). ∀s:num. ∀x:(num → A). fo_update_range(ρ, s, 0, x) = ρ",
		func(a *Argument, ρ *Arrow[Nat, A], s *Expr[Nat], x *Arrow[Nat, A]) {
			a.Do(
				Funext(),
				Unfold(UpdateRangeDef),
				StripQuant(),
				CondRewrite(),
				ByArith(),
			)
		}),
})}

// UpdateRangeLast — a block of length n + 1 is the update of its last name s + n to the
// tuple's entry x(n), followed by the block of length n: unfolded at a name, the case splits
// agree, since s + n lies outside the shorter block and reads x(n) inside the longer one.
var UpdateRangeLast = updateRangeLastThm{family.Add(registry.ProofEntry{
	Name: "UpdateRangeLast",
	Key:  "prop_a5af332b219df8ce",
	Build: family.Theorem("∀ρ:(num → A). ∀s n:num. ∀x:(num → A). "+
		"    fo_update_range(fo_update(ρ, s + n, x(n)), s, n, x) = fo_update_range(ρ, s, suc(n), x)",
		func(a *Argument, ρ *Arrow[Nat, A], s, n *Expr[Nat], x *Arrow[Nat, A]) {
			a.Do(
				Funext(),
				Unfold(UpdateRangeDef),
				Unfold(EnvUpdateDef),
				StripQuant(),
				CondRewrite(),
				ByArith(),
			)
		}),
})}

// UpdateRangeExtend — updating the name s + n to a and then the block of length n from x is
// the block of length n + 1 from x extended by a, the tuple that follows x below n and takes
// the value a from n on: unfolded at a name, the case splits agree.
var UpdateRangeExtend = updateRangeExtendThm{family.Add(registry.ProofEntry{
	Name: "UpdateRangeExtend",
	Key:  "prop_7fd8258420c4e38d",
	Build: family.Theorem("∀ρ:(num → A). ∀s n:num. ∀a:A. ∀x:(num → A). "+
		"    fo_update_range(fo_update(ρ, s + n, a), s, n, x) = "+
		"    fo_update_range(ρ, s, suc(n), λi:num. COND(i < n, x(i), a))",
		func(arg *Argument, ρ *Arrow[Nat, A], s, n *Expr[Nat], a *Expr[A], x *Arrow[Nat, A]) {
			arg.Do(
				Funext(),
				Unfold(UpdateRangeDef),
				Unfold(EnvUpdateDef),
				StripQuant(),
				CondRewrite(),
				ByArith(),
			)
		}),
})}

// UpdateRangeEnvironment — substituting carrier values at a block of names keeps an environment
// carrier-valued: inside the block it reads the substituted values, outside it the old ones.
var UpdateRangeEnvironment = updateRangeEnvironmentThm{family.Add(registry.ProofEntry{
	Name: "UpdateRangeEnvironment",
	Key:  "prop_21fff41077fe6662",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(A). ∀ρ:(num → A). ∀s n:num. ∀x:(num → A).",
		Hypotheses: []string{
			"fo_env_ok(X, 𝕌, ρ)",
			"∀i:num. i < n ⇒ x(i) ∈ X",
		},
		Conclusion: "fo_env_ok(X, 𝕌, fo_update_range(ρ, s, n, x))",
	}, func(
		a *Argument,
		X *Expr[Set[A]],
		ρ *Arrow[Nat, A],
		s, n *Expr[Nat],
		x *Arrow[Nat, A],
		env, values Fact,
	) {
		old := a.Unfolded(env, EnvOKDef)
		a.Do(Unfold(EnvOKDef))
		v := a.FixAs[Nat]("v")
		a.Assume()
		a.Cases(a.Term("s ≤ v ∧ v < s + n"))
		a.When(
			"inside the block the environment reads x at v − s, which lies below n",
			func(b *Argument, inside Fact) {
				offset := b.Have(
					"v lies fewer than n past s",
					"v - s < n",
					ByArith(inside))
				b.Show(
					"x is carrier-valued there",
					By(Normalized, inside, offset, values, UpdateRangeDef.At(ρ, s, n, x, v)))
			})
		a.Otherwise(
			"outside the block the environment reads ρ, which is carrier-valued",
			func(b *Argument, outside Fact) {
				b.Show(
					"ρ is carrier-valued everywhere",
					By(outside, old, set_basic.InUniv, UpdateRangeDef.At(ρ, s, n, x, v)))
			})
	}),
})}

// UpdateRangeOutside — a range update leaves every name outside its block alone: unfolded at
// such a name, the block's range s ≤ v < s + n fails and the update reads the old environment.
var UpdateRangeOutside = updateRangeOutsideThm{family.Add(registry.ProofEntry{
	Name: "UpdateRangeOutside",
	Key:  "prop_54b513c5bf293341",
	Build: family.Theorem(Statement{
		Binders: "∀ρ:(num → A). ∀s n:num. ∀x:(num → A). ∀v:num.",
		Hypotheses: []string{
			"v < s ∨ s + n ≤ v",
		},
		Conclusion: "fo_update_range(ρ, s, n, x, v) = ρ(v)",
	},
		func(a *Argument, ρ *Arrow[Nat, A], s, n *Expr[Nat], x *Arrow[Nat, A], v *Expr[Nat], outside Fact) {
			a.Show(
				"v lies outside the range s ≤ v < s + n, so the update reads ρ at v",
				Simp(Fwd(UpdateRangeDef)),
				CondRewrite(),
				ByArith(outside))
		}),
})}

// UpdateRangeCopy — substituting into a block the values another environment ρ holds there
// makes the update read ρ on the block: at a name v of the block the update reads ρ at s plus
// v's offset from s, which is v.
var UpdateRangeCopy = updateRangeCopyThm{family.Add(registry.ProofEntry{
	Name: "UpdateRangeCopy",
	Key:  "prop_bf03a8cfaff0bbef",
	Build: family.Theorem(Statement{
		Binders: "∀σ:(num → A). ∀s n:num. ∀ρ:(num → A). ∀v:num.",
		Hypotheses: []string{
			"s ≤ v",
			"v < s + n",
		},
		Conclusion: "fo_update_range(σ, s, n, λi:num. ρ(s + i), v) = ρ(v)",
	},
		func(a *Argument, σ *Arrow[Nat, A], s, n *Expr[Nat], ρ *Arrow[Nat, A], v *Expr[Nat], inside Fact) {
			back := a.Have(
				"v is s plus its offset from s",
				"s + (v - s) = v",
				ByArith(inside))
			a.Show(
				"the update reads ρ at s plus the offset, which is v",
				Simp(Fwd(UpdateRangeDef)),
				By(Normalized, inside, back))
		}),
})}

// UpdateRangeCommute — range updates at disjoint blocks commute: unfolded at a name, the two
// nested case splits agree, since no name lies in both blocks.
var UpdateRangeCommute = updateRangeCommuteThm{family.Add(registry.ProofEntry{
	Name: "UpdateRangeCommute",
	Key:  "prop_ab5d116fe63ced2f",
	Build: family.Theorem(Statement{
		Binders: "∀ρ:(num → A). ∀s n t m:num. ∀x y:(num → A).",
		Hypotheses: []string{
			"s + n ≤ t ∨ t + m ≤ s",
		},
		Conclusion: "fo_update_range(fo_update_range(ρ, s, n, x), t, m, y) = " +
			"fo_update_range(fo_update_range(ρ, t, m, y), s, n, x)",
	},
		func(a *Argument, ρ *Arrow[Nat, A], s, n, t, m *Expr[Nat], x, y *Arrow[Nat, A], disjoint Fact) {
			a.Show(
				"at each name both sides read the same branch, the name lying in at most one of the blocks",
				Funext(),
				Simp(Fwd(UpdateRangeDef)),
				StripQuant(),
				CondRewrite(),
				ByArith(disjoint))
		}),
})}

// AllRangeSemantics — a universal name block quantifies a finite tuple simultaneously: by
// induction on the block length, the environment left free in the induction hypothesis. The
// block of length n + 1 is a universal at its last name s + n over the block of length n, so a
// carrier value at the outer name and a tuple for the inner block make one tuple of length
// n + 1, and UpdateRangeLast and UpdateRangeExtend identify the two environments they give.
var AllRangeSemantics = allRangeSemanticsThm{family.Add(registry.ProofEntry{
	Name: "AllRangeSemantics",
	Key:  "prop_528c436e9b7919be",
	Reading: "At length zero both sides reduce to the original formula. " +
		"An empty carrier with positive block length makes both sides true.",
	Build: family.Theorem("∀X:set(B). "+
		"∀e:(A → (num → B) → bool). "+
		"∀ρ:(num → B). "+
		"∀s n:num. "+
		"∀φ:fo_formula(A). "+
		"    fo_eval(X, e, ρ, fo_all_range(s, n, φ)) ⇔ "+
		"    ∀x:(num → B). (∀i:num. i < n ⇒ x(i) ∈ X) ⇒ fo_eval(X, e, fo_update_range(ρ, s, n, x), φ)",
		func(
			arg *Argument,
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			ρ *Arrow[Nat, B],
			s, n *Expr[Nat],
			φ *Expr[Formula[A]],
		) {
			blockQuantifies := arg.TermAs[Set[Nat]](
				"λn:num. ∀ρ:(num → B). " +
					"    fo_eval(X, e, ρ, fo_all_range(s, n, φ)) ⇔ " +
					"    ∀x:(num → B). (∀i:num. i < n ⇒ x(i) ∈ X) ⇒ fo_eval(X, e, fo_update_range(ρ, s, n, x), φ)")
			arg.Show(
				"every block length quantifies its tuple in every environment, n among them",
				ByInduction(peano.Induction.At(blockQuantifies, n),
					Case(
						"an empty block is the formula itself, and a tuple of length zero updates no name",
						Simp(Fwd(AllRangeDef), Fwd(UpdateRangeEmpty), Fwd(nat_order.LessThanZeroClause)),
						Basic()),
					Case(
						"a block of length m + 1 is a universal at s + m over the block of "+
							"length m, read by the induction hypothesis at each update at s + m",
						Derive(func(b *Argument) {
							m := b.FixAs[Nat]("m")
							ih := b.Assume()
							σ := b.FixAs[Fun[Nat, B]]("σ")
							b.Do(Simp(Fwd(AllRangeDef), Fwd(EvalForall), Fwd(ih)))
							b.Iff()
							b.Forward(
								"a tuple carrier-valued below m + 1 hands x(m) to the outer name and itself to the inner block",
								func(c *Argument, outer Fact) {
									x := c.FixAs[Fun[Nat, B]]("x")
									bounded := c.Simplified(c.Assume(), Fwd(nat_order.LessThanSucClause))
									c.Show(
										"the outer update at x(m) under the inner block is the block of length m + 1",
										By(outer.At(c.TermAs[B]("x(m)"), x), bounded, UpdateRangeLast.At(σ, s, m, x)))
								})
							b.Backward(
								"a carrier value a at the outer name and a tuple x for the inner block extend to one tuple",
								func(c *Argument, inner Fact) {
									a := c.FixAs[B]("a")
									aIn := c.Assume()
									x := c.FixAs[Fun[Nat, B]]("x")
									bounded := c.Assume()
									extended := c.Have(
										"x extended by a is carrier-valued below m + 1",
										"∀i:num. i < suc(m) ⇒ COND(i < m, x(i), a) ∈ X",
										By(bounded, aIn))
									c.Show(
										"the block of length m + 1 from the extended tuple is the outer update at a under the inner block",
										By(
											inner.At(c.TermAs[Fun[Nat, B]]("λi:num. COND(i < m, x(i), a)")),
											extended,
											UpdateRangeExtend.At(σ, s, m, a, x)))
								})
						}))))
		}),
})}

// ExistsRangeSemantics — an existential name block quantifies a finite tuple simultaneously: by
// induction on the block length, the environment left free in the induction hypothesis. The
// block of length n + 1 is an existential at its last name s + n over the block of length n, so
// a carrier value at the outer name and a tuple for the inner block make one tuple of length
// n + 1, and UpdateRangeExtend and UpdateRangeLast identify the two environments they give.
var ExistsRangeSemantics = existsRangeSemanticsThm{family.Add(registry.ProofEntry{
	Name: "ExistsRangeSemantics",
	Key:  "prop_7d73ec0bf1c76f85",
	Reading: "At length zero both sides reduce to the original formula; HOL function types " +
		"are inhabited. An empty carrier with positive block length makes both sides false.",
	Build: family.Theorem("∀X:set(B). "+
		"∀e:(A → (num → B) → bool). "+
		"∀ρ:(num → B). "+
		"∀s n:num. "+
		"∀φ:fo_formula(A). "+
		"    fo_eval(X, e, ρ, fo_exists_range(s, n, φ)) ⇔ "+
		"    ∃x:(num → B). (∀i:num. i < n ⇒ x(i) ∈ X) ∧ fo_eval(X, e, fo_update_range(ρ, s, n, x), φ)",
		func(
			arg *Argument,
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			ρ *Arrow[Nat, B],
			s, n *Expr[Nat],
			φ *Expr[Formula[A]],
		) {
			blockQuantifies := arg.TermAs[Set[Nat]](
				"λn:num. ∀ρ:(num → B). " +
					"    fo_eval(X, e, ρ, fo_exists_range(s, n, φ)) ⇔ " +
					"    ∃x:(num → B). (∀i:num. i < n ⇒ x(i) ∈ X) ∧ fo_eval(X, e, fo_update_range(ρ, s, n, x), φ)")
			arg.Show(
				"every block length quantifies its tuple in every environment, n among them",
				ByInduction(peano.Induction.At(blockQuantifies, n),
					Case(
						"an empty block is the formula itself, and a tuple of length zero updates no name",
						Simp(Fwd(ExistsRangeDef), Fwd(UpdateRangeEmpty), Fwd(nat_order.LessThanZeroClause)),
						Basic()),
					Case(
						"a block of length m + 1 is an existential at s + m over the block "+
							"of length m, read by the induction hypothesis at each update at s + m",
						Derive(func(b *Argument) {
							m := b.FixAs[Nat]("m")
							ih := b.Assume()
							σ := b.FixAs[Fun[Nat, B]]("σ")
							b.Do(Simp(Fwd(ExistsRangeDef), Fwd(EvalDef), Fwd(ih)))
							b.Iff()
							b.Forward(
								"a carrier value a at the outer name and a tuple x for the inner block extend to one tuple",
								func(c *Argument, outer Fact) {
									a, aFact := c.UnpackAs[B](outer, "a")
									atOuter := c.Conjuncts(
										aFact,
										"a lies in the carrier",
										"some tuple fills the inner block under the outer update at a")
									x, xFact := c.UnpackAs[Fun[Nat, B]](atOuter[1], "x")
									inner := c.Conjuncts(
										xFact,
										"x is carrier-valued below m",
										"φ holds at the outer update at a under the inner block from x")
									extended := c.Have(
										"x extended by a is carrier-valued below m + 1",
										"∀i:num. i < suc(m) ⇒ COND(i < m, x(i), a) ∈ X",
										By(inner[0], atOuter[0]))
									c.Take(c.TermAs[Fun[Nat, B]]("λi:num. COND(i < m, x(i), a)"))
									c.Show(
										"the block of length m + 1 from the extended tuple is the outer update at a under the inner block",
										By(extended, inner[1], UpdateRangeExtend.At(σ, s, m, a, x)))
								})
							b.Backward(
								"a tuple carrier-valued below m + 1 hands x(m) to the outer name and itself to the inner block",
								func(c *Argument, whole Fact) {
									x, xFact := c.UnpackAs[Fun[Nat, B]](whole, "x")
									parts := c.Conjuncts(
										xFact,
										"x is carrier-valued below m + 1",
										"φ holds at the block of length m + 1 from x")
									bounded := c.Simplified(parts[0], Fwd(nat_order.LessThanSucClause))
									c.Take(c.TermAs[B]("x(m)"))
									c.Show(
										"the outer update at x(m) under the inner block is the block of length m + 1",
										By(bounded, parts[1], UpdateRangeLast.At(σ, s, m, x)))
								})
						}))))
		}),
})}

// AllRangeFreeVars — universally quantifying a block of consecutive names leaves free exactly
// the free variables of the body outside the block: by induction on the length of the block,
// one more name, s + n, being quantified outside the block of n.
var AllRangeFreeVars = allRangeFreeVarsThm{family.Add(registry.ProofEntry{
	Name: "AllRangeFreeVars",
	Key:  "prop_39f9641f3dbb5d8",
	Build: family.Theorem(
		"∀S:(A → set(num)). ∀s n:num. ∀φ:fo_formula(A). "+
			"    fo_fv(S, fo_all_range(s, n, φ)) = fo_fv(S, φ) ∖ {v:num | s ≤ v ∧ v < s + n}",
		func(a *Argument, S *Arrow[A, Set[Nat]], s *Expr[Nat]) {
			a.Induct("n")
			a.Base(
				"a block of no names quantifies nothing",
				Simp(Fwd(AllRangeDef)),
				BySets(nat_arith.AddZero, nat_order.NotLessThan))
			a.Step(
				"one more name, s + n, is quantified outside the block of n",
				func(b *Argument, ih Fact) {
					b.FixAs[Formula[A]]("φ")
					block := b.Have(
						"the block of n + 1 names is the block of n with s + n",
						"∀v:num. s ≤ v ∧ v < s + suc(n) ⇔ (s ≤ v ∧ v < s + n) ∨ v = s + n",
						ByArith())
					b.Show(
						"removing the block of n and then s + n removes the block of n + 1",
						Simp(Fwd(AllRangeDef), Fwd(ForallDef), Fwd(FreeVarsDef), Fwd(ih)),
						BySets(block))
				})
		}),
})}

// ExistsRangeFreeVars — existentially quantifying a block of consecutive names leaves free
// exactly the free variables of the body outside the block: by induction on the length of the
// block, as for the universal block.
var ExistsRangeFreeVars = existsRangeFreeVarsThm{family.Add(registry.ProofEntry{
	Name: "ExistsRangeFreeVars",
	Key:  "prop_be75c4ec55f6e49a",
	Build: family.Theorem(
		"∀S:(A → set(num)). ∀s n:num. ∀φ:fo_formula(A). "+
			"    fo_fv(S, fo_exists_range(s, n, φ)) = fo_fv(S, φ) ∖ {v:num | s ≤ v ∧ v < s + n}",
		func(a *Argument, S *Arrow[A, Set[Nat]], s *Expr[Nat]) {
			a.Induct("n")
			a.Base(
				"a block of no names quantifies nothing",
				Simp(Fwd(ExistsRangeDef)),
				BySets(nat_arith.AddZero, nat_order.NotLessThan))
			a.Step(
				"one more name, s + n, is quantified outside the block of n",
				func(b *Argument, ih Fact) {
					b.FixAs[Formula[A]]("φ")
					block := b.Have(
						"the block of n + 1 names is the block of n with s + n",
						"∀v:num. s ≤ v ∧ v < s + suc(n) ⇔ (s ≤ v ∧ v < s + n) ∨ v = s + n",
						ByArith())
					b.Show(
						"removing the block of n and then s + n removes the block of n + 1",
						Simp(Fwd(ExistsRangeDef), Fwd(FreeVarsDef), Fwd(ih)),
						BySets(block))
				})
		}),
})}

// AllRangeSupportBelow — a universal block of n names at s binds them: when the names of the
// body lie below s + n, the names of the quantified formula, the body's without the block,
// lie below s.
var AllRangeSupportBelow = allRangeSupportBelowThm{family.Add(registry.ProofEntry{
	Name: "AllRangeSupportBelow",
	Key:  "prop_88f49a4cc84455e9",
	Build: family.Theorem(Statement{
		Binders: "∀S:(A → set(num)). ∀s n:num. ∀φ:fo_formula(A).",
		Hypotheses: []string{
			"fo_fv(S, φ) ⊆ {v:num | v < s + n}",
		},
		Conclusion: "fo_fv(S, fo_all_range(s, n, φ)) ⊆ {v:num | v < s}",
	}, func(a *Argument, S *Arrow[A, Set[Nat]], s, n *Expr[Nat], φ *Expr[Formula[A]], bound Fact) {
		below := a.Have(
			"a name below s + n outside the block from s lies below s",
			"∀v:num. v < s + n ∧ ¬(s ≤ v ∧ v < s + n) ⇒ v < s",
			ByArith())
		a.Show(
			"the block removes its names from the body's, which lie below s + n",
			Simp(Fwd(AllRangeFreeVars)),
			BySets(bound, below))
	}),
})}

// ExistsRangeSupportBelow — an existential block of n names at s binds them: when the names
// of the body lie below s + n, the names of the quantified formula, the body's without the
// block, lie below s.
var ExistsRangeSupportBelow = existsRangeSupportBelowThm{family.Add(registry.ProofEntry{
	Name: "ExistsRangeSupportBelow",
	Key:  "prop_a5e188104e084155",
	Build: family.Theorem(Statement{
		Binders: "∀S:(A → set(num)). ∀s n:num. ∀φ:fo_formula(A).",
		Hypotheses: []string{
			"fo_fv(S, φ) ⊆ {v:num | v < s + n}",
		},
		Conclusion: "fo_fv(S, fo_exists_range(s, n, φ)) ⊆ {v:num | v < s}",
	}, func(a *Argument, S *Arrow[A, Set[Nat]], s, n *Expr[Nat], φ *Expr[Formula[A]], bound Fact) {
		below := a.Have(
			"a name below s + n outside the block from s lies below s",
			"∀v:num. v < s + n ∧ ¬(s ≤ v ∧ v < s + n) ⇒ v < s",
			ByArith())
		a.Show(
			"the block removes its names from the body's, which lie below s + n",
			Simp(Fwd(ExistsRangeFreeVars)),
			BySets(bound, below))
	}),
})}

// AllRangeWellFormed — a universally quantified block is well formed exactly when its body is:
// quantifying a name changes no atom.
var AllRangeWellFormed = allRangeWellFormedThm{family.Add(registry.ProofEntry{
	Name: "AllRangeWellFormed",
	Key:  "prop_cefe4c716b7de57d",
	Build: family.Theorem(
		"∀ok:(A → bool). ∀s n:num. ∀φ:fo_formula(A). fo_wf(ok, fo_all_range(s, n, φ)) ⇔ fo_wf(ok, φ)",
		func(a *Argument, ok *Arrow[A, Bool], s *Expr[Nat]) {
			a.Induct("n")
			a.Base(
				"a block of no names is its body",
				Simp(Fwd(AllRangeDef)),
				Basic())
			a.Step(
				"one more quantified name keeps the atoms of the block of n",
				func(b *Argument, ih Fact) {
					b.Show(
						"a quantifier and its negations keep the body's atoms",
						Simp(Fwd(AllRangeDef), Fwd(ForallDef), Fwd(WellFormedDef)),
						By(ih))
				})
		}),
})}

// ExistsRangeWellFormed — an existentially quantified block is well formed exactly when its
// body is: quantifying a name changes no atom.
var ExistsRangeWellFormed = existsRangeWellFormedThm{family.Add(registry.ProofEntry{
	Name: "ExistsRangeWellFormed",
	Key:  "prop_d0de62a6f857d46e",
	Build: family.Theorem(
		"∀ok:(A → bool). ∀s n:num. ∀φ:fo_formula(A). fo_wf(ok, fo_exists_range(s, n, φ)) ⇔ fo_wf(ok, φ)",
		func(a *Argument, ok *Arrow[A, Bool], s *Expr[Nat]) {
			a.Induct("n")
			a.Base(
				"a block of no names is its body",
				Simp(Fwd(ExistsRangeDef)),
				Basic())
			a.Step(
				"one more quantified name keeps the atoms of the block of n",
				func(b *Argument, ih Fact) {
					b.Show(
						"a quantifier keeps the body's atoms",
						Simp(Fwd(ExistsRangeDef), Fwd(WellFormedDef)),
						By(ih))
				})
		}),
})}

// ConjoinDef — finite conjunction with an explicit formula for the empty conjunction.
var ConjoinDef = conjoinDefThm{family.Define(registry.DefEntry{
	Name:  "ConjoinDef",
	Const: "fo_conjoin",
	Type:  "fo_formula(A) → num → (num → fo_formula(A)) → fo_formula(A)",
	Key:   "prop_30c66a6b759768eb",
	Equations: []string{
		"∀t:fo_formula(A). ∀f:(num → fo_formula(A)). fo_conjoin(t, 0, f) = t",
		"∀t:fo_formula(A). ∀n:num. ∀f:(num → fo_formula(A)). " +
			"    fo_conjoin(t, suc(n), f) = fo_and(fo_conjoin(t, n, f), f(n))",
	},
	Deps: []registry.EntryLike{FormulaData.Recursion},
})}

// ConjoinSemantics — a finite conjunction with a true seed means bounded universal truth: by
// induction on the length. The empty conjunction is the seed, which is true, while no index
// lies below zero; one more conjunct adds the index n, and the indices below n + 1 are n and
// those below n.
var ConjoinSemantics = conjoinSemanticsThm{family.Add(registry.ProofEntry{
	Name: "ConjoinSemantics",
	Key:  "prop_b4594808c82ae3ef",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(B). " +
			"∀e:(A → (num → B) → bool). " +
			"∀ρ:(num → B). " +
			"∀t:fo_formula(A). " +
			"∀n:num. " +
			"∀f:(num → fo_formula(A)).",
		Hypotheses: []string{
			"fo_eval(X, e, ρ, t)",
		},
		Conclusion: "fo_eval(X, e, ρ, fo_conjoin(t, n, f)) ⇔ ∀i:num. i < n ⇒ fo_eval(X, e, ρ, f(i))",
	},
		func(
			a *Argument,
			X *Expr[Set[B]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			ρ *Arrow[Nat, B],
			t *Expr[Formula[A]],
			n *Expr[Nat],
			f *Arrow[Nat, Formula[A]],
			seed Fact,
		) {
			a.Induct(n)
			a.Base(
				"the empty conjunction is the seed, true by hypothesis, and no index lies below zero",
				Simp(Fwd(ConjoinDef), Fwd(nat_order.LessThanZeroClause)),
				By(seed))
			a.Step(
				"one more conjunct adds the index n, and the indices below n + 1 are n and those below n",
				func(b *Argument, ih Fact) {
					b.Show(
						"the conjunction over n + 1 indices is the one over n with f(n) adjoined",
						Simp(Fwd(ConjoinDef), Fwd(EvalDef), Fwd(ih)),
						By(nat_order.LessThanSucClause))
				})
		}),
})}

// ConjoinFreeVars — the free variables of a finite conjunction are those of its seed and of
// its conjuncts: by induction on the number of conjuncts, the conjunct f(n) adding its own.
var ConjoinFreeVars = conjoinFreeVarsThm{family.Add(registry.ProofEntry{
	Name: "ConjoinFreeVars",
	Key:  "prop_c3209b2e1db8969e",
	Build: family.Theorem(
		"∀S:(A → set(num)). ∀t:fo_formula(A). ∀n:num. ∀f:(num → fo_formula(A)). "+
			"    fo_fv(S, fo_conjoin(t, n, f)) = fo_fv(S, t) ∪ ⋃{fo_fv(S, f(i)) | i:num | i < n}",
		func(a *Argument, S *Arrow[A, Set[Nat]], t *Expr[Formula[A]]) {
			a.Induct("n")
			a.Base(
				"the empty conjunction is the seed, and no index lies below zero",
				Simp(Fwd(ConjoinDef)),
				BySets(nat_order.LessThanZeroClause))
			a.Step(
				"one more conjunct adds the free variables of f(n)",
				func(b *Argument, ih Fact) {
					b.FixAs[Fun[Nat, Formula[A]]]("f")
					b.Show(
						"the indices below n + 1 are n and those below n",
						Simp(Fwd(ConjoinDef), Fwd(FreeVarsDef), Fwd(ih)),
						BySets(nat_order.LessThanSucClause))
				})
		}),
})}

// ConjoinSupportBelow — a finite conjunction names what its base and its first n conjuncts
// name: when those lie below k, so do its names.
var ConjoinSupportBelow = conjoinSupportBelowThm{family.Add(registry.ProofEntry{
	Name: "ConjoinSupportBelow",
	Key:  "prop_dc0411e46788f1cb",
	Build: family.Theorem(Statement{
		Binders: "∀S:(A → set(num)). ∀t:fo_formula(A). ∀n k:num. ∀f:(num → fo_formula(A)).",
		Hypotheses: []string{
			"fo_fv(S, t) ⊆ {v:num | v < k}",
			"∀i:num. i < n ⇒ fo_fv(S, f(i)) ⊆ {v:num | v < k}",
		},
		Conclusion: "fo_fv(S, fo_conjoin(t, n, f)) ⊆ {v:num | v < k}",
	}, func(
		a *Argument,
		S *Arrow[A, Set[Nat]],
		t *Expr[Formula[A]],
		n, k *Expr[Nat],
		f *Arrow[Nat, Formula[A]],
		base, members Fact,
	) {
		a.Show(
			"the conjunction's names are its base's and its conjuncts' below n",
			Simp(Fwd(ConjoinFreeVars)),
			BySets(base, members))
	}),
})}

// ConjoinWellFormed — a finite conjunction is well formed exactly when its seed and each of its
// conjuncts are: by induction on the number of conjuncts.
var ConjoinWellFormed = conjoinWellFormedThm{family.Add(registry.ProofEntry{
	Name: "ConjoinWellFormed",
	Key:  "prop_2ab642b49198d30b",
	Build: family.Theorem(
		"∀ok:(A → bool). ∀t:fo_formula(A). ∀n:num. ∀f:(num → fo_formula(A)). "+
			"    fo_wf(ok, fo_conjoin(t, n, f)) ⇔ fo_wf(ok, t) ∧ (∀i:num. i < n ⇒ fo_wf(ok, f(i)))",
		func(a *Argument, ok *Arrow[A, Bool], t *Expr[Formula[A]]) {
			a.Induct("n")
			a.Base(
				"the empty conjunction is the seed, and no index lies below zero",
				Simp(Fwd(ConjoinDef)),
				By(nat_order.LessThanZeroClause))
			a.Step(
				"one more conjunct asks f(n) to be well formed",
				func(b *Argument, ih Fact) {
					b.FixAs[Fun[Nat, Formula[A]]]("f")
					b.Show(
						"the indices below n + 1 are n and those below n",
						Simp(Fwd(ConjoinDef), Fwd(WellFormedDef), Fwd(ih)),
						By(nat_order.LessThanSucClause))
				})
		}),
})}

// QuantifierFreeEquivalent — ψ is a quantifier-free equivalent of φ over a
// class of models, a structure of four parts: ψ is well formed and
// quantifier-free, its free variables are among φ's, and in every model of the
// class ψ agrees with φ at every environment legal on φ's free variables, one
// formula for every model. A proof reads each part off such a fact by its
// axiom below, and proves one by rewriting its goal by this definition.
var QuantifierFreeEquivalent = quantifierFreeEquivalentThm{family.DefineStructure(registry.DefEntry{
	Name:  "QuantifierFreeEquivalent",
	Const: "fo_quantifier_free_equivalent",
	Type: "(D → bool) → " +
		"(D → set(B)) → " +
		"(D → A → (num → B) → bool) → " +
		"(A → bool) → " +
		"(A → set(num)) → " +
		"fo_formula(A) → " +
		"fo_formula(A) → " +
		"bool",
	Key: "prop_b10ec810732d4b3",
	Equations: []string{
		"∀T:(D → bool). " +
			"∀K:(D → set(B)). " +
			"∀e:(D → A → (num → B) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀φ ψ:fo_formula(A). " +
			"    fo_quantifier_free_equivalent(T, K, e, ok, S, φ, ψ) ⇔ " +
			"    fo_wf(ok, ψ) ∧ " +
			"    fo_qf(ψ) ∧ " +
			"    fo_fv(S, ψ) ⊆ fo_fv(S, φ) ∧ " +
			"    (∀M:D. ∀ρ:(num → B). " +
			"        T(M) ∧ fo_env_ok(K(M), fo_fv(S, φ), ρ) ⇒ " +
			"        (fo_eval(K(M), e(M), ρ, φ) ⇔ fo_eval(K(M), e(M), ρ, ψ)))",
	},
	Deps: []registry.EntryLike{
		EnvOKDef,
		EvalDef,
		FormulaData.Recursion,
		FreeVarsDef,
		QuantifierFreeDef,
		WellFormedDef,
	},
})}

// EquivalentWellFormed — a quantifier-free equivalent is well formed.
var EquivalentWellFormed = equivalentWellFormedThm{family.Add(registry.ProofEntry{
	Name:  "EquivalentWellFormed",
	Key:   "prop_b56c3d4e7cbe9759",
	Build: QuantifierFreeEquivalent.Axiom("fo_wf(ok, ψ)"),
})}

// EquivalentQuantifierFree — a quantifier-free equivalent has no quantifier.
var EquivalentQuantifierFree = equivalentQuantifierFreeThm{family.Add(registry.ProofEntry{
	Name:  "EquivalentQuantifierFree",
	Key:   "prop_296261a94a8fc0da",
	Build: QuantifierFreeEquivalent.Axiom("fo_qf(ψ)"),
})}

// EquivalentSupport — the free variables of a quantifier-free equivalent are
// among those of the formula it is equivalent to.
var EquivalentSupport = equivalentSupportThm{family.Add(registry.ProofEntry{
	Name:  "EquivalentSupport",
	Key:   "prop_11e5d46667064100",
	Build: QuantifierFreeEquivalent.Axiom("fo_fv(S, ψ) ⊆ fo_fv(S, φ)"),
})}

// EquivalentAgreement — a quantifier-free equivalent takes the formula's value
// in every model of the class, at every environment legal on the formula's
// free variables.
var EquivalentAgreement = equivalentAgreementThm{family.Add(registry.ProofEntry{
	Name: "EquivalentAgreement",
	Key:  "prop_d4102567d9f349b2",
	Build: QuantifierFreeEquivalent.Axiom(Statement{
		Binders: "∀M:D. ∀ρ:(num → B).",
		Hypotheses: []string{
			"T(M)",
			"fo_env_ok(K(M), fo_fv(S, φ), ρ)",
		},
		Conclusion: "fo_eval(K(M), e(M), ρ, φ) ⇔ fo_eval(K(M), e(M), ρ, ψ)",
	}),
})}

// OneVariableEliminationDef — one existential over a well-formed quantifier-free
// body has a quantifier-free equivalent over the class, which leaves the
// quantified name free no more than the existential does.
var OneVariableEliminationDef = oneVariableEliminationDefThm{family.Define(registry.DefEntry{
	Name:  "OneVariableEliminationDef",
	Const: "fo_one_qe",
	Type: "(D → bool) → " +
		"(D → set(B)) → " +
		"(D → A → (num → B) → bool) → " +
		"(A → bool) → " +
		"(A → set(num)) → " +
		"bool",
	Key: "prop_e2ce8dc00b697312",
	Equations: []string{
		"∀T:(D → bool). " +
			"∀K:(D → set(B)). " +
			"∀e:(D → A → (num → B) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"    fo_one_qe(T, K, e, ok, S) ⇔ " +
			"    ∀φ:fo_formula(A). ∀v:num. " +
			"        fo_wf(ok, φ) ∧ fo_qf(φ) ⇒ " +
			"        ∃ψ:fo_formula(A). fo_quantifier_free_equivalent(T, K, e, ok, S, fo_exists(v, φ), ψ)",
	},
	Deps: []registry.EntryLike{
		FormulaData.Recursion,
		QuantifierFreeDef,
		QuantifierFreeEquivalent,
		WellFormedDef,
	},
})}

// QuantifierEliminationDef — every well-formed formula has a quantifier-free
// equivalent over the class.
var QuantifierEliminationDef = quantifierEliminationDefThm{family.Define(registry.DefEntry{
	Name:  "QuantifierEliminationDef",
	Const: "fo_has_qe",
	Type: "(D → bool) → " +
		"(D → set(B)) → " +
		"(D → A → (num → B) → bool) → " +
		"(A → bool) → " +
		"(A → set(num)) → " +
		"bool",
	Key: "prop_9b5cf9f425836235",
	Equations: []string{
		"∀T:(D → bool). " +
			"∀K:(D → set(B)). " +
			"∀e:(D → A → (num → B) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"    fo_has_qe(T, K, e, ok, S) ⇔ " +
			"    ∀φ:fo_formula(A). " +
			"        fo_wf(ok, φ) ⇒ ∃ψ:fo_formula(A). fo_quantifier_free_equivalent(T, K, e, ok, S, φ, ψ)",
	},
	Deps: []registry.EntryLike{QuantifierFreeEquivalent, WellFormedDef},
})}

// QuantifierEliminationFromOne — uniform one-variable elimination implies uniform full quantifier
// elimination: by induction on the formula, the equivalent of each formula chosen before any
// model or environment. An atom is its own equivalent, and a negation or a conjunction takes
// the negation or conjunction of its parts' equivalents. At an existential the body's
// equivalent is quantifier-free with support inside the body's, so one-variable elimination
// removes the quantifier from it; an environment legal off the quantified name, updated there
// by a carrier element, is legal on the body's support, where the body and its equivalent agree.
var QuantifierEliminationFromOne = quantifierEliminationFromOneThm{family.Add(registry.ProofEntry{
	Name: "QuantifierEliminationFromOne",
	Key:  "prop_c5b55c284c297867",
	Reading: "Atomic locality and finite support are not assumed. In both definitions the equivalent " +
		"is quantified before the model and the environment, every model lying on the one host type B, " +
		"so hypothesis and conclusion alike are elimination uniform in the model. The support inclusions " +
		"are load-bearing: an environment is guarded only on the support of the formula it evaluates.",
	Build: family.Theorem(Statement{
		Binders: "∀T:(D → bool). " +
			"∀K:(D → set(B)). " +
			"∀e:(D → A → (num → B) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)).",
		Hypotheses: []string{
			"fo_one_qe(T, K, e, ok, S)",
		},
		Conclusion: "fo_has_qe(T, K, e, ok, S)",
		Abbrev: Abbrev{
			{Name: "HasEquivalent", Text: "λφ:fo_formula(A). ∃ψ:fo_formula(A). " +
				"    fo_quantifier_free_equivalent(T, K, e, ok, S, φ, ψ)"},
		},
	},
		func(
			a *Argument,
			T *Expr[Set[D]],
			K *Arrow2[D, B, Bool],
			e *Expr[Fun3[D, A, Fun[Nat, B], Bool]],
			ok *Expr[Set[A]],
			S *Arrow2[A, Nat, Bool],
			one Fact,
		) {
			eliminates := a.Unfolded(one, OneVariableEliminationDef)
			a.Show(
				"every well-formed formula has an equivalent, chosen before the model and the environment",
				Unfold(QuantifierEliminationDef),
				ByInduction(FormulaInduction,
					Case(
						"an atom is its own equivalent",
						Derive(func(b *Argument) {
							b.FixAs[A]("p")
							valid := b.Assume()
							b.Take(b.TermAs[Formula[A]]("fo_atom(p)"))
							b.Show(
								"a valid atom is well formed and quantifier-free, with its own support and value",
								QuantifierFreeEquivalent.Intro(
									By(Normalized, valid, QuantifierFreeDef, set_order.SubsetRefl)))
						})),
					Case(
						"a negation takes the negation of its body's equivalent",
						Derive(func(b *Argument) {
							b.FixAs[Formula[A]]("φ")
							ih := b.Assume()
							wf := b.Simplified(b.Assume(), Fwd(WellFormedDef))
							_, equivalent := b.ObtainAs[Formula[A]](
								"the body φ has an equivalent ψ",
								"«HasEquivalent»(φ)",
								By(ih, wf))
							b.Take(b.TermAs[Formula[A]]("fo_not(ψ)"))
							b.Show(
								"negation keeps ψ well formed, quantifier-free and on φ's support, and negates both values",
								QuantifierFreeEquivalent.Intro(
									Simp(Fwd(WellFormedDef), Fwd(QuantifierFreeDef), Fwd(FreeVarsDef), Fwd(EvalDef)),
									By(Normalized, QuantifierFreeEquivalent.Parts(equivalent))))
						})),
					Case(
						"a conjunction takes the conjunction of its conjuncts' equivalents",
						Derive(func(b *Argument) {
							b.FixAs[Formula[A]]("φ₁")
							b.FixAs[Formula[A]]("φ₂")
							ih1, ih2 := b.Assume(), b.Assume()
							wf := b.Conjuncts(
								b.Simplified(b.Assume(), Fwd(WellFormedDef)),
								"φ₁ is well formed",
								"φ₂ is well formed")
							_, firstEquivalent := b.ObtainAs[Formula[A]](
								"the conjunct φ₁ has an equivalent ψ₁",
								"«HasEquivalent»(φ₁)",
								By(ih1, wf[0]),
								Named("ψ₁"))
							_, secondEquivalent := b.ObtainAs[Formula[A]](
								"the conjunct φ₂ has an equivalent ψ₂",
								"«HasEquivalent»(φ₂)",
								By(ih2, wf[1]),
								Named("ψ₂"))
							b.Take(b.TermAs[Formula[A]]("fo_and(ψ₁, ψ₂)"))
							b.Show(
								"the supports combine by union, and a guard on the union is a guard on each conjunct",
								QuantifierFreeEquivalent.Intro(
									Simp(Fwd(WellFormedDef), Fwd(QuantifierFreeDef), Fwd(FreeVarsDef), Fwd(EvalDef), Fwd(EnvOKUnion)),
									By(
										Normalized,
										QuantifierFreeEquivalent.Parts(firstEquivalent),
										QuantifierFreeEquivalent.Parts(secondEquivalent),
										set_basic.SubsetDef,
										set_basic.InUnion)))
						})),
					Case(
						"an existential eliminates its quantifier from its body's equivalent",
						Derive(func(b *Argument) {
							v := b.FixAs[Nat]("v")
							b.FixAs[Formula[A]]("φ")
							ih := b.Assume()
							wf := b.Simplified(b.Assume(), Fwd(WellFormedDef))
							ψ, equivalent := b.ObtainAs[Formula[A]](
								"the body φ has an equivalent ψ",
								"«HasEquivalent»(φ)",
								By(ih, wf))
							χ, eliminated := b.ObtainAs[Formula[A]](
								"one-variable elimination removes v from the existential of the quantifier-free ψ, giving χ",
								"∃χ:fo_formula(A). fo_quantifier_free_equivalent(T, K, e, ok, S, fo_exists(v, ψ), χ)",
								By(
									EquivalentWellFormed.Read(equivalent),
									EquivalentQuantifierFree.Read(equivalent),
									eliminates.At(ψ, v)))
							offV := b.Simplified(EquivalentSupport.Read(eliminated), Fwd(FreeVarsDef))
							agreesOffV := b.Simplified(EquivalentAgreement.Read(eliminated), Fwd(FreeVarsDef))
							removed := b.Have(
								"removing v keeps the support of ψ inside that of φ",
								"fo_fv(S, ψ) ∖ {v} ⊆ fo_fv(S, φ) ∖ {v}",
								BySets(EquivalentSupport.Read(equivalent)))
							agrees := b.Have(
								"χ agrees with the existential of φ at v in every model and environment legal off v",
								Statement{
									Binders: "∀M:D. ∀ρ:(num → B).",
									Hypotheses: []string{
										"T(M)",
										"fo_env_ok(K(M), fo_fv(S, φ) ∖ {v}, ρ)",
									},
									Conclusion: "fo_eval(K(M), e(M), ρ, fo_exists(v, φ)) ⇔ fo_eval(K(M), e(M), ρ, χ)",
								},
								Derive(func(c *Argument) {
									M := c.FixAs[D]("M")
									ρ := c.FixAs[Fun[Nat, B]]("ρ")
									guard := c.Conjuncts(
										c.Assume(),
										"M is a model",
										"ρ is legal on the support of φ off v")
									bodies := c.Have(
										"updated at v by a carrier element, ρ is legal on φ's support, where φ and ψ agree",
										Statement{
											Binders: "∀x:B.",
											Hypotheses: []string{
												"x ∈ K(M)",
											},
											Conclusion: "fo_eval(K(M), e(M), fo_update(ρ, v, x), φ) ⇔ " +
												"fo_eval(K(M), e(M), fo_update(ρ, v, x), ψ)",
										},
										Derive(func(d *Argument) {
											x := d.FixAs[B]("x")
											inCarrier := d.Assume()
											d.Show(
												"by the body's equivalence at the updated environment",
												By(
													EquivalentAgreement.Read(equivalent).At(M, d.TermAs[Fun[Nat, B]]("fo_update(ρ, v, x)")),
													guard[0],
													EnvOKUpdate.At(d.TermAs[Set[B]]("K(M)"), d.TermAs[Set[Nat]]("fo_fv(S, φ)"), ρ, v, x),
													guard[1],
													inCarrier))
										}))
									sameExistential := c.Have(
										"so the existentials of φ and of ψ at v agree",
										"fo_eval(K(M), e(M), ρ, fo_exists(v, φ)) ⇔ fo_eval(K(M), e(M), ρ, fo_exists(v, ψ))",
										Simp(Fwd(EvalDef)),
										By(bodies))
									c.Show(
										"ρ is legal on the smaller support of ψ off v, where the existential of ψ agrees with χ",
										By(
											sameExistential,
											agreesOffV.At(M, ρ),
											guard[0],
											EnvOKSubset.At(
												c.TermAs[Set[B]]("K(M)"),
												c.TermAs[Set[Nat]]("fo_fv(S, ψ) ∖ {v}"),
												c.TermAs[Set[Nat]]("fo_fv(S, φ) ∖ {v}"),
												ρ),
											removed,
											guard[1]))
								}))
							b.Take(χ)
							b.Show(
								"χ is well formed, quantifier-free, inside φ's support off v, and agrees with the existential",
								QuantifierFreeEquivalent.Intro(
									Simp(Fwd(FreeVarsDef)),
									By(
										EquivalentWellFormed.Read(eliminated),
										EquivalentQuantifierFree.Read(eliminated),
										offV,
										removed,
										agrees,
										set_order.SubsetTrans)))
						}))))
		}),
})}

// AtomicEmbeddingDef — a carrier map preserves and reflects valid atoms in every legal environment.
var AtomicEmbeddingDef = atomicEmbeddingDefThm{family.Define(registry.DefEntry{
	Name: "AtomicEmbeddingDef",
	Key:  "prop_6919006e7573fab7",
	Reading: "Injectivity is not an additional assumption here: the " +
		"contract is exactly carrier preservation and atomic preservation and " +
		"reflection. An equality atom may imply injectivity in a concrete theory.",
	Const: "fo_atomic_embedding",
	Type: "set(B) → " +
		"set(C) → " +
		"(A → (num → B) → bool) → " +
		"(A → (num → C) → bool) → " +
		"(A → bool) → " +
		"(A → set(num)) → " +
		"(B → C) → " +
		"bool",
	Equations: []string{
		"∀X:set(B). " +
			"∀Y:set(C). " +
			"∀e:(A → (num → B) → bool). " +
			"∀f:(A → (num → C) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀i:(B → C). " +
			"    fo_atomic_embedding(X, Y, e, f, ok, S, i) ⇔ " +
			"    (∀x:B. x ∈ X ⇒ i(x) ∈ Y) ∧ " +
			"    (∀p:A. ∀ρ:(num → B). ok(p) ∧ fo_env_ok(X, S(p), ρ) ⇒ (e(p, ρ) ⇔ f(p, λv:num. i(ρ(v)))))",
	},
	Deps: []registry.EntryLike{EnvOKDef, FormulaData.Recursion},
})}

// QuantifierFreeEmbedding — atomic preservation and reflection extend to
// quantifier-free formulas: relating a quantifier-free formula's legal
// environments to their images under i is a simulation. At an atom the support
// guard is the atomic clause's own guard; a negation and a conjunction pass the
// relation to their parts, the conjunction's guard splitting over the union of
// its conjuncts' supports; an existential is not quantifier-free, so no
// environments are related there.
var QuantifierFreeEmbedding = quantifierFreeEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeEmbedding",
	Key:  "prop_ccef96f55d03440a",
	Reading: "Neither atomic locality nor nonempty carriers is required, and i need " +
		"not be injective or onto Y: the atomic clause of fo_atomic_embedding is all the " +
		"statement asks. ρ is guarded only on the free variables of φ; quantifier-freeness " +
		"is load-bearing, since an existential needs the surjectivity OntoEmbedding assumes.",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(B). " +
			"∀Y:set(C). " +
			"∀e:(A → (num → B) → bool). " +
			"∀f:(A → (num → C) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀i:(B → C). " +
			"∀ρ:(num → B). " +
			"∀φ:fo_formula(A).",
		Hypotheses: []string{
			"fo_atomic_embedding(X, Y, e, f, ok, S, i)",
			"fo_wf(ok, φ)",
			"fo_qf(φ)",
			"fo_env_ok(X, fo_fv(S, φ), ρ)",
		},
		Conclusion: "fo_eval(X, e, ρ, φ) ⇔ fo_eval(Y, f, λv:num. i(ρ(v)), φ)",
	},
		func(
			a *Argument,
			X *Expr[Set[B]],
			Y *Expr[Set[C]],
			e *Arrow2[A, Fun[Nat, B], Bool],
			f *Arrow2[A, Fun[Nat, C], Bool],
			ok *Expr[Set[A]],
			S *Arrow2[A, Nat, Bool],
			i *Arrow[B, C],
			ρ *Arrow[Nat, B],
			φ *Expr[Formula[A]],
			embedding, wf, qf, legal Fact,
		) {
			carried := a.Have(
				"i preserves and reflects every valid atom in an environment legal on its support",
				"∀p:A. ∀τ:(num → B). ok(p) ∧ fo_env_ok(X, S(p), τ) ⇒ (e(p, τ) ⇔ f(p, λv:num. i(τ(v))))",
				By(a.Unfolded(embedding, AtomicEmbeddingDef)))
			R, imaged := a.LetAs[Fun3[Formula[A], Fun[Nat, B], Fun[Nat, C], Bool]](
				"R",
				"λψ:fo_formula(A). λτ:(num → B). λσ:(num → C). "+
					"    fo_qf(ψ) ∧ fo_env_ok(X, fo_fv(S, ψ), τ) ∧ σ = (λv:num. i(τ(v)))")
			atoms := a.Have(
				"i carries a valid atom across from an environment legal on its support to the image",
				"∀p:A. ∀τ:(num → B). ∀σ:(num → C). ok(p) ∧ R(fo_atom(p), τ, σ) ⇒ (e(p, τ) ⇔ f(p, σ))",
				imaged.Rw(),
				Derive(func(b *Argument) {
					p := b.FixAs[A]("p")
					τ := b.FixAs[Fun[Nat, B]]("τ")
					b.FixAs[Fun[Nat, C]]("σ")
					given := b.Conjuncts(
						b.Assume(),
						"p is valid",
						"an atom is quantifier-free",
						"τ is legal on the free variables of the atom",
						"σ is the image of τ")
					legalAtom := b.Simplified(given[2], Fwd(FreeVarsDef))
					b.Show(
						"the atom at τ is the atom at its image",
						given[3].Rw(),
						By(carried.At(p, τ), given[0], legalAtom))
				}))
			negation := a.Have(
				"a negation is quantifier-free with the support of its body",
				"∀ψ:fo_formula(A). ∀τ:(num → B). ∀σ:(num → C). R(fo_not(ψ), τ, σ) ⇒ R(ψ, τ, σ)",
				imaged.Rw(),
				Simp(Fwd(QuantifierFreeDef), Fwd(FreeVarsDef)),
				Basic())
			conjunction := a.Have(
				"a conjunction's guard splits over the union of its conjuncts' supports",
				"∀ψ χ:fo_formula(A). ∀τ:(num → B). ∀σ:(num → C). R(fo_and(ψ, χ), τ, σ) ⇒ R(ψ, τ, σ) ∧ R(χ, τ, σ)",
				imaged.Rw(),
				Simp(Fwd(QuantifierFreeDef), Fwd(FreeVarsDef), Fwd(EnvOKUnion)),
				Derive(func(b *Argument) {
					b.FixAs[Formula[A]]("ψ")
					b.FixAs[Formula[A]]("χ")
					b.FixAs[Fun[Nat, B]]("τ")
					b.FixAs[Fun[Nat, C]]("σ")
					guard := b.Assume()
					b.Show(
						"each conjunct keeps its part of the guard",
						By(guard))
				}))
			existential := a.Have(
				"an existential is not quantifier-free, so no environments are related there",
				Statement{
					Binders: "∀v:num. ∀ψ:fo_formula(A). ∀τ:(num → B). ∀σ:(num → C).",
					Hypotheses: []string{
						"R(fo_exists(v, ψ), τ, σ)",
					},
					Conclusion: "(∀x:B. x ∈ X ⇒ ∃y:C. y ∈ Y ∧ R(ψ, fo_update(τ, v, x), fo_update(σ, v, y))) ∧ " +
						"(∀y:C. y ∈ Y ⇒ ∃x:B. x ∈ X ∧ R(ψ, fo_update(τ, v, x), fo_update(σ, v, y)))",
				},
				Simp(Fwd(imaged), Fwd(QuantifierFreeDef)),
				Basic())
			related := a.Have(
				"ρ is related to its image at φ",
				"R(φ, ρ, λv:num. i(ρ(v)))",
				imaged.Rw(),
				By(qf, legal))
			a.Show(
				"so φ takes one value at ρ and at its image",
				By(
					EvalSimulation.At(ok, X, e, Y, f, R, ρ, a.TermAs[Fun[Nat, C]]("λv:num. i(ρ(v))"), φ),
					atoms,
					negation,
					conjunction,
					existential,
					wf,
					related))
		}),
})}

// QuantifierFreeAtomAgreement — two interpretations that agree on every valid atom agree on every
// valid quantifier-free formula: by induction on the formula, since a negation and a conjunction
// take their values from their parts, and a quantifier-free formula has no existential, where the
// carriers and the environments would enter.
var QuantifierFreeAtomAgreement = quantifierFreeAtomAgreementThm{family.Add(registry.ProofEntry{
	Name: "QuantifierFreeAtomAgreement",
	Key:  "prop_347debdc6d879955",
	Build: family.Theorem(Statement{
		Binders: "∀ok:(A → bool). " +
			"∀X:set(B). " +
			"∀e:(A → (num → B) → bool). " +
			"∀ρ:(num → B). " +
			"∀Y:set(C). " +
			"∀f:(A → (num → C) → bool). " +
			"∀σ:(num → C). " +
			"∀φ:fo_formula(A).",
		Hypotheses: []string{
			"fo_wf(ok, φ)",
			"fo_qf(φ)",
			"∀p:A. ok(p) ⇒ (e(p, ρ) ⇔ f(p, σ))",
		},
		Conclusion: "fo_eval(X, e, ρ, φ) ⇔ fo_eval(Y, f, σ, φ)",
	}, func(
		a *Argument,
		ok *Expr[Set[A]],
		X *Expr[Set[B]],
		e *Arrow2[A, Fun[Nat, B], Bool],
		ρ *Arrow[Nat, B],
		Y *Expr[Set[C]],
		f *Arrow2[A, Fun[Nat, C], Bool],
		σ *Arrow[Nat, C],
		φ *Expr[Formula[A]],
		wf, qf, agree Fact,
	) {
		agrees := a.TermAs[Set[Formula[A]]](
			"λψ:fo_formula(A). fo_wf(ok, ψ) ∧ fo_qf(ψ) ⇒ (fo_eval(X, e, ρ, ψ) ⇔ fo_eval(Y, f, σ, ψ))")
		a.Show(
			"every valid quantifier-free formula takes one value "+
				"under the two interpretations, by induction on its shape",
			ByInduction(FormulaInduction.At(agrees, φ), wf, qf,
				Case(
					"a valid atom takes the value the two interpretations agree on",
					Simp(Fwd(WellFormedDef), Fwd(EvalDef)),
					By(agree)),
				Case(
					"a negation negates the common value of its body",
					Simp(Fwd(WellFormedDef), Fwd(QuantifierFreeDef), Fwd(EvalDef)),
					Basic()),
				Case(
					"a conjunction is valid and quantifier-free with both conjuncts, and conjoins their common values",
					Simp(Fwd(WellFormedDef), Fwd(QuantifierFreeDef), Fwd(EvalDef)),
					Derive(func(b *Argument) {
						b.FixAs[Formula[A]]("ψ")
						b.FixAs[Formula[A]]("χ")
						ihψ, ihχ := b.Assume(), b.Assume()
						both := b.Assume()
						b.Show(
							"each conjunct takes one value under the two interpretations",
							By(Normalized, ihψ, ihχ, both))
					})),
				Case(
					"an existential is not quantifier-free",
					Simp(Fwd(WellFormedDef), Fwd(QuantifierFreeDef), Fwd(EvalDef)),
					Basic())))
	}),
})}

// OntoEmbedding — an atomic embedding onto the target carrier preserves and
// reflects every well-formed formula: relating a formula's legal environments
// to their images under i is a simulation. Atoms are carried across by the
// embedding, a negation and a conjunction pass the relation to their parts, and
// at an existential the embedding carries a witness across and its
// surjectivity onto Y carries one back.
var OntoEmbedding = ontoEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "OntoEmbedding",
	Key:  "prop_c7f90d0a7f0c10ee",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(B). " +
			"∀Y:set(C). " +
			"∀e:(A → (num → B) → bool). " +
			"∀f:(A → (num → C) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀i:(B → C). " +
			"∀ρ:(num → B). " +
			"∀φ:fo_formula(A).",
		Hypotheses: []string{
			"fo_atomic_embedding(X, Y, e, f, ok, S, i)",
			"image(i, X) = Y",
			"fo_wf(ok, φ)",
			"fo_env_ok(X, fo_fv(S, φ), ρ)",
		},
		Conclusion: "fo_eval(X, e, ρ, φ) ⇔ fo_eval(Y, f, λv:num. i(ρ(v)), φ)",
	}, func(
		a *Argument,
		X *Expr[Set[B]],
		Y *Expr[Set[C]],
		e *Arrow2[A, Fun[Nat, B], Bool],
		f *Arrow2[A, Fun[Nat, C], Bool],
		ok *Expr[Set[A]],
		S *Arrow2[A, Nat, Bool],
		i *Arrow[B, C],
		ρ *Arrow[Nat, B],
		φ *Expr[Formula[A]],
		embedding, onto, wf, envOk Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(embedding, AtomicEmbeddingDef),
			"i carries X into Y",
			"at a valid atom in a legal environment i carries the atom across")
		into, carried := parts[0], parts[1]
		R, imaged := a.LetAs[Fun3[Formula[A], Fun[Nat, B], Fun[Nat, C], Bool]](
			"R",
			"λψ:fo_formula(A). λτ:(num → B). λσ:(num → C). "+
				"    fo_env_ok(X, fo_fv(S, ψ), τ) ∧ σ = (λv:num. i(τ(v)))")
		atoms := a.Have(
			"i carries a valid atom across from an environment legal on its support to the image",
			"∀p:A. ∀τ:(num → B). ∀σ:(num → C). ok(p) ∧ R(fo_atom(p), τ, σ) ⇒ (e(p, τ) ⇔ f(p, σ))",
			imaged.Rw(),
			Derive(func(b *Argument) {
				p := b.FixAs[A]("p")
				τ := b.FixAs[Fun[Nat, B]]("τ")
				b.FixAs[Fun[Nat, C]]("σ")
				given := b.Conjuncts(
					b.Assume(),
					"p is valid",
					"τ is legal on the free variables of the atom",
					"σ is the image of τ")
				legalAtom := b.Simplified(given[1], Fwd(FreeVarsDef))
				b.Show(
					"the atom at τ is the atom at its image",
					given[2].Rw(),
					By(carried.At(p, τ), given[0], legalAtom))
			}))
		negation := a.Have(
			"a negation has the support of its body",
			"∀ψ:fo_formula(A). ∀τ:(num → B). ∀σ:(num → C). R(fo_not(ψ), τ, σ) ⇒ R(ψ, τ, σ)",
			imaged.Rw(),
			Simp(Fwd(FreeVarsDef)),
			Basic())
		conjunction := a.Have(
			"a conjunction's guard splits over the union of its conjuncts' supports",
			"∀ψ χ:fo_formula(A). ∀τ:(num → B). ∀σ:(num → C). R(fo_and(ψ, χ), τ, σ) ⇒ R(ψ, τ, σ) ∧ R(χ, τ, σ)",
			imaged.Rw(),
			Simp(Fwd(FreeVarsDef), Fwd(EnvOKUnion)),
			Derive(func(b *Argument) {
				b.FixAs[Formula[A]]("ψ")
				b.FixAs[Formula[A]]("χ")
				b.FixAs[Fun[Nat, B]]("τ")
				b.FixAs[Fun[Nat, C]]("σ")
				guard := b.Assume()
				b.Show(
					"each conjunct keeps its part of the guard",
					By(guard))
			}))
		ontoPoints := a.Have(
			"every point of Y is the image of a point of X",
			"∀y:C. y ∈ Y ⇒ ∃x:B. x ∈ X ∧ i(x) = y",
			By(Normalized, onto, set_basic.InImage))
		existential := a.Have(
			"at an existential, i carries a witness across and its surjectivity carries one back",
			Statement{
				Binders: "∀v:num. ∀ψ:fo_formula(A). ∀τ:(num → B). ∀σ:(num → C).",
				Hypotheses: []string{
					"R(fo_exists(v, ψ), τ, σ)",
				},
				Conclusion: "(∀x:B. x ∈ X ⇒ ∃y:C. y ∈ Y ∧ R(ψ, fo_update(τ, v, x), fo_update(σ, v, y))) ∧ " +
					"(∀y:C. y ∈ Y ⇒ ∃x:B. x ∈ X ∧ R(ψ, fo_update(τ, v, x), fo_update(σ, v, y)))",
			},
			imaged.Rw(),
			Derive(func(b *Argument) {
				v := b.FixAs[Nat]("v")
				b.FixAs[Formula[A]]("ψ")
				τ := b.FixAs[Fun[Nat, B]]("τ")
				b.FixAs[Fun[Nat, C]]("σ")
				given := b.Conjuncts(
					b.Assume(),
					"τ is legal on the free variables of the existential",
					"σ is the image of τ")
				offName := b.Simplified(given[0], Fwd(FreeVarsDef))
				matched := b.Have(
					"updated at v by a point x of X, τ stays legal on the "+
						"body's support, and its image is the image updated by i(x)",
					Statement{
						Binders: "∀x:B.",
						Hypotheses: []string{
							"x ∈ X",
						},
						Conclusion: "fo_env_ok(X, fo_fv(S, ψ), fo_update(τ, v, x)) ∧ " +
							"fo_update(λw:num. i(τ(w)), v, i(x)) = (λw:num. i(fo_update(τ, v, x, w)))",
					},
					Derive(func(c *Argument) {
						x := c.FixAs[B]("x")
						xIn := c.Assume()
						c.Show(
							"the update of a legal environment by a point of "+
								"X is legal, and the image commutes with the update",
							SplitConj(
								Case(
									"the update by a point of X is legal",
									By(EnvOKUpdate.At(X, c.TermAs[Set[Nat]]("fo_fv(S, ψ)"), τ, v, x), offName, xIn)),
								Case(
									"the image commutes with the update",
									Funext(),
									Unfold(EnvUpdateDef))))
					}))
				b.Show(
					"so a witness on either side is matched on the other",
					given[1].Rw(),
					SplitConj(
						Case(
							"a witness x in X is matched by i(x) in Y",
							Derive(func(c *Argument) {
								x := c.FixAs[B]("x")
								xIn := c.Assume()
								c.Take(c.TermAs[C]("i(x)"))
								c.Show(
									"i(x) lies in Y, and matches x",
									By(into, xIn, matched.At(x)))
							})),
						Case(
							"a witness y in Y is the image i(x) of a point x of X, which matches it",
							Derive(func(c *Argument) {
								y := c.FixAs[C]("y")
								yIn := c.Assume()
								x, preimage := c.UnpackAs[B](GroupPremises(yIn, ontoPoints.At(y)), "x")
								hit := c.Conjuncts(
									preimage,
									"x lies in X",
									"i(x) = y")
								c.Take(x)
								c.Show(
									"x lies in X, and i(x) = y matches it",
									hit[1].RwRev(),
									By(hit[0], matched.At(x)))
							}))))
			}))
		related := a.Have(
			"ρ is related to its image at φ",
			"R(φ, ρ, λv:num. i(ρ(v)))",
			imaged.Rw(),
			By(envOk))
		a.Show(
			"so φ takes one value at ρ and at its image",
			By(
				EvalSimulation.At(ok, X, e, Y, f, R, ρ, a.TermAs[Fun[Nat, C]]("λv:num. i(ρ(v))"), φ),
				atoms,
				negation,
				conjunction,
				existential,
				wf,
				related))
	}),
})}

// EliminationAlongEmbedding — an equivalent that serves a model serves every
// model embedded onto it: if ψ, well formed and with free variables
// among φ's, agrees with φ in Y at every environment legal on φ's free
// variables, and i embeds X atomically onto Y, then ψ agrees with φ in X at
// every such environment ρ. The embedding carries ρ to a legal environment of
// Y, where the two formulas agree, and the onto embedding carries the value
// of each formula from ρ to the carried environment.
var EliminationAlongEmbedding = eliminationAlongEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "EliminationAlongEmbedding",
	Key:  "prop_1c4685e2a6b2667",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(B). " +
			"∀Y:set(C). " +
			"∀e:(A → (num → B) → bool). " +
			"∀f:(A → (num → C) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀i:(B → C). " +
			"∀ρ:(num → B). " +
			"∀φ ψ:fo_formula(A).",
		Hypotheses: []string{
			"fo_atomic_embedding(X, Y, e, f, ok, S, i)",
			"image(i, X) = Y",
			"fo_wf(ok, φ)",
			"fo_wf(ok, ψ)",
			"fo_fv(S, ψ) ⊆ fo_fv(S, φ)",
			"∀σ:(num → C). fo_env_ok(Y, fo_fv(S, φ), σ) ⇒ (fo_eval(Y, f, σ, φ) ⇔ fo_eval(Y, f, σ, ψ))",
			"fo_env_ok(X, fo_fv(S, φ), ρ)",
		},
		Conclusion: "fo_eval(X, e, ρ, φ) ⇔ fo_eval(X, e, ρ, ψ)",
	}, func(
		a *Argument,
		X *Expr[Set[B]],
		Y *Expr[Set[C]],
		e *Arrow2[A, Fun[Nat, B], Bool],
		f *Arrow2[A, Fun[Nat, C], Bool],
		ok *Expr[Set[A]],
		S *Arrow2[A, Nat, Bool],
		i *Arrow[B, C],
		ρ *Arrow[Nat, B],
		φ, ψ *Expr[Formula[A]],
		embedding, onto, wfφ, wfψ, support, agree, legal Fact,
	) {
		into := a.Have(
			"i carries X into Y",
			"∀x:B. x ∈ X ⇒ i(x) ∈ Y",
			By(a.Unfolded(embedding, AtomicEmbeddingDef)))
		carried := a.TermAs[Fun[Nat, C]]("λv:num. i(ρ(v))")
		carriedLegal := a.Have(
			"i carries ρ to an environment legal on φ's free variables in Y",
			"fo_env_ok(Y, fo_fv(S, φ), λv:num. i(ρ(v)))",
			By(into, legal, EnvOKDef))
		legalψ := a.Have(
			"ρ is legal on the free variables of ψ, which are among φ's",
			"fo_env_ok(X, fo_fv(S, ψ), ρ)",
			By(
				support,
				legal,
				EnvOKSubset.At(X, a.TermAs[Set[Nat]]("fo_fv(S, ψ)"), a.TermAs[Set[Nat]]("fo_fv(S, φ)"), ρ)))
		a.Show(
			"φ at ρ is φ in Y at the carried environment, which is ψ there, which is ψ at ρ",
			CalcEq(
				Leg(
					a.TermAs[Bool]("fo_eval(Y, f, λv:num. i(ρ(v)), φ)"),
					"the onto embedding carries the value of φ",
					By(embedding, onto, wfφ, legal, OntoEmbedding.At(X, Y, e, f, ok, S, i, ρ, φ))),
				Leg(
					a.TermAs[Bool]("fo_eval(Y, f, λv:num. i(ρ(v)), ψ)"),
					"φ and ψ agree in Y at the carried environment, which is legal there",
					By(carriedLegal, agree.At(carried))),
				FinalLeg(
					"the onto embedding carries the value of ψ",
					By(embedding, onto, wfψ, legalψ, OntoEmbedding.At(X, Y, e, f, ok, S, i, ρ, ψ)))))
	}),
})}

// EliminationAlongClassEmbedding — a quantifier-free equivalent of a
// well-formed formula over the second of two classes of models is one over
// the first, when every model of the first embeds atomically onto a model of
// the second. ψ keeps its syntax; a model M of the first class embeds onto a
// model N of the second, where ψ agrees with φ, and EliminationAlongEmbedding
// carries that agreement back to M.
var EliminationAlongClassEmbedding = eliminationAlongClassEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "EliminationAlongClassEmbedding",
	Key:  "prop_54d2f350003703fa",
	Build: family.Theorem(Statement{
		Binders: "∀T₁:(D → bool). " +
			"∀K₁:(D → set(B)). " +
			"∀e₁:(D → A → (num → B) → bool). " +
			"∀T₂:(E → bool). " +
			"∀K₂:(E → set(C)). " +
			"∀e₂:(E → A → (num → C) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀φ ψ:fo_formula(A).",
		Hypotheses: []string{
			"fo_wf(ok, φ)",
			"fo_quantifier_free_equivalent(T₂, K₂, e₂, ok, S, φ, ψ)",
			"∀M:D. " +
				"    T₁(M) ⇒ " +
				"    ∃N:E. ∃i:(B → C). " +
				"        T₂(N) ∧ " +
				"        fo_atomic_embedding(K₁(M), K₂(N), e₁(M), e₂(N), ok, S, i) ∧ " +
				"        image(i, K₁(M)) = K₂(N)",
		},
		Conclusion: "fo_quantifier_free_equivalent(T₁, K₁, e₁, ok, S, φ, ψ)",
	},
		func(
			a *Argument,
			T1 *Expr[Set[D]],
			K1 *Arrow2[D, B, Bool],
			e1 *Expr[Fun3[D, A, Fun[Nat, B], Bool]],
			T2 *Expr[Set[E]],
			K2 *Arrow2[E, C, Bool],
			e2 *Expr[Fun3[E, A, Fun[Nat, C], Bool]],
			ok *Expr[Set[A]],
			S *Arrow2[A, Nat, Bool],
			φ, ψ *Expr[Formula[A]],
			wf, equivalent, embeds Fact,
		) {
			agrees := a.Have(
				"ψ agrees with φ in every model of the first class "+
					"at every environment legal on φ's free variables",
				Statement{
					Binders: "∀M:D. ∀ρ:(num → B).",
					Hypotheses: []string{
						"T₁(M)",
						"fo_env_ok(K₁(M), fo_fv(S, φ), ρ)",
					},
					Conclusion: "fo_eval(K₁(M), e₁(M), ρ, φ) ⇔ fo_eval(K₁(M), e₁(M), ρ, ψ)",
				},
				Derive(func(b *Argument) {
					M := b.FixAs[D]("M")
					ρ := b.FixAs[Fun[Nat, B]]("ρ")
					given := b.Conjuncts(
						b.Assume(),
						"M is a model of the first class",
						"ρ is legal on φ's free variables in M")
					_, i, embedded := b.Unpack2As[E, Fun[B, C]](GroupPremises(given[0], embeds.At(M)), "N", "i")
					modelAndEmbedding := b.Conjuncts(
						embedded,
						"N is a model of the second class",
						"i embeds the atoms of M in those of N",
						"i carries the carrier of M onto that of N")
					inN := b.Have(
						"φ and ψ agree in N at every environment legal on φ's free variables",
						Statement{
							Binders: "∀σ:(num → C).",
							Hypotheses: []string{
								"fo_env_ok(K₂(N), fo_fv(S, φ), σ)",
							},
							Conclusion: "fo_eval(K₂(N), e₂(N), σ, φ) ⇔ fo_eval(K₂(N), e₂(N), σ, ψ)",
						},
						By(modelAndEmbedding[0], EquivalentAgreement.Read(equivalent)))
					b.Show(
						"i embeds M onto N, where φ and ψ agree, so they agree in M",
						By(
							modelAndEmbedding[1],
							modelAndEmbedding[2],
							wf,
							EquivalentWellFormed.Read(equivalent),
							EquivalentSupport.Read(equivalent),
							inN,
							given[1],
							EliminationAlongEmbedding.At(
								b.TermAs[Set[B]]("K₁(M)"),
								b.TermAs[Set[C]]("K₂(N)"),
								b.TermAs[Fun2[A, Fun[Nat, B], Bool]]("e₁(M)"),
								b.TermAs[Fun2[A, Fun[Nat, C], Bool]]("e₂(N)"),
								ok,
								S,
								i,
								ρ,
								φ,
								ψ)))
				}))
			a.Show(
				"ψ keeps its syntax from the second class, and agrees with φ in the first",
				QuantifierFreeEquivalent.Intro(
					By(
						EquivalentWellFormed.Read(equivalent),
						EquivalentQuantifierFree.Read(equivalent),
						EquivalentSupport.Read(equivalent),
						agrees)))
		}),
})}

// ElementaryFromCommonEquivalent — a quantifier-free equivalent common to two
// classes of models makes every atomic embedding between their models
// elementary: φ at M is ψ at M, the embedding carries ψ's value from M to N,
// and ψ at N is φ at N. The support of ψ lies inside φ's, so ρ is legal on it
// in M; and i carries K₁(M) into K₂(N), so the mapped environment is legal on
// φ's support in N.
var ElementaryFromCommonEquivalent = elementaryFromCommonEquivalentThm{family.Add(registry.ProofEntry{
	Name: "ElementaryFromCommonEquivalent",
	Key:  "prop_3e57e311a216f4b6",
	Reading: "The two classes may live on different host types, so M and N need " +
		"share neither a carrier type nor a model type; ψ is one formula equivalent to " +
		"φ over both. Beyond the atomic embedding, i need be neither injective nor onto " +
		"K₂(N): the common equivalent does the work OntoEmbedding asks of surjectivity.",
	Build: family.Theorem(Statement{
		Binders: "∀T₁:(D → bool). " +
			"∀K₁:(D → set(B)). " +
			"∀e₁:(D → A → (num → B) → bool). " +
			"∀T₂:(E → bool). " +
			"∀K₂:(E → set(C)). " +
			"∀e₂:(E → A → (num → C) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀M:D. " +
			"∀N:E. " +
			"∀i:(B → C). " +
			"∀ρ:(num → B). " +
			"∀φ ψ:fo_formula(A).",
		Hypotheses: []string{
			"fo_quantifier_free_equivalent(T₁, K₁, e₁, ok, S, φ, ψ)",
			"fo_quantifier_free_equivalent(T₂, K₂, e₂, ok, S, φ, ψ)",
			"T₁(M)",
			"T₂(N)",
			"fo_atomic_embedding(K₁(M), K₂(N), e₁(M), e₂(N), ok, S, i)",
			"fo_env_ok(K₁(M), fo_fv(S, φ), ρ)",
		},
		Conclusion: "fo_eval(K₁(M), e₁(M), ρ, φ) ⇔ fo_eval(K₂(N), e₂(N), λv:num. i(ρ(v)), φ)",
	},
		func(
			a *Argument,
			T1 *Expr[Set[D]],
			K1 *Arrow2[D, B, Bool],
			e1 *Expr[Fun3[D, A, Fun[Nat, B], Bool]],
			T2 *Expr[Set[E]],
			K2 *Arrow2[E, C, Bool],
			e2 *Expr[Fun3[E, A, Fun[Nat, C], Bool]],
			ok *Expr[Set[A]],
			S *Arrow2[A, Nat, Bool],
			M *Expr[D],
			N *Expr[E],
			i *Arrow[B, C],
			ρ *Arrow[Nat, B],
			φ, ψ *Expr[Formula[A]],
			overFirst, overSecond, modelM, modelN, embedding, legal Fact,
		) {
			into := a.Have(
				"i carries K₁(M) into K₂(N)",
				"∀x:B. x ∈ K₁(M) ⇒ i(x) ∈ K₂(N)",
				By(a.Unfolded(embedding, AtomicEmbeddingDef)))
			mappedLegal := a.Have(
				"i carries ρ to an environment legal on φ's support in N",
				"fo_env_ok(K₂(N), fo_fv(S, φ), λv:num. i(ρ(v)))",
				By(into, legal, EnvOKDef))
			carrierM, carrierN := a.TermAs[Set[B]]("K₁(M)"), a.TermAs[Set[C]]("K₂(N)")
			transported := a.Have(
				"the embedding carries the value of the quantifier-free "+
					"ψ from M to N, ρ being legal on its support",
				"fo_eval(K₁(M), e₁(M), ρ, ψ) ⇔ fo_eval(K₂(N), e₂(N), λv:num. i(ρ(v)), ψ)",
				By(
					QuantifierFreeEmbedding.At(
						carrierM,
						carrierN,
						a.TermAs[Fun2[A, Fun[Nat, B], Bool]]("e₁(M)"),
						a.TermAs[Fun2[A, Fun[Nat, C], Bool]]("e₂(N)"),
						ok,
						S,
						i,
						ρ,
						ψ),
					embedding,
					EquivalentWellFormed.Read(overFirst),
					EquivalentQuantifierFree.Read(overFirst),
					EnvOKSubset.At(carrierM, a.TermAs[Set[Nat]]("fo_fv(S, ψ)"), a.TermAs[Set[Nat]]("fo_fv(S, φ)"), ρ),
					EquivalentSupport.Read(overFirst),
					legal))
			a.Show(
				"φ at M is ψ at M, which the embedding carries to ψ at N, which is φ at N",
				By(
					EquivalentAgreement.Read(overFirst).At(M, ρ),
					modelM,
					legal,
					transported,
					EquivalentAgreement.Read(overSecond).At(N, a.TermAs[Fun[Nat, C]]("λv:num. i(ρ(v))")),
					modelN,
					mappedLegal))
		}),
})}

// SentenceTransferFromCommonEquivalent — a quantifier-free equivalent common to
// two classes of models lifts agreement on closed quantifier-free formulas to
// all sentences: the support of ψ lies inside φ's empty one, so ψ is closed.
// Every environment is legal on the empty support, so φ at (M, ρ) is ψ at (M,
// ρ), which the agreement carries to ψ at (N, σ), which is φ at (N, σ).
var SentenceTransferFromCommonEquivalent = sentenceTransferFromCommonEquivalentThm{family.Add(registry.ProofEntry{
	Name: "SentenceTransferFromCommonEquivalent",
	Key:  "prop_63e63a0878a0bd64",
	Reading: "The two classes may live on different host types. The conclusion " +
		"compares the two specified environments. Environment independence is a " +
		"separate consequence of atomic locality; it is not assumed here. ρ and σ " +
		"need not take carrier values: φ has no free variable for a guard to constrain.",
	Build: family.Theorem(Statement{
		Binders: "∀T₁:(D → bool). " +
			"∀K₁:(D → set(B)). " +
			"∀e₁:(D → A → (num → B) → bool). " +
			"∀T₂:(E → bool). " +
			"∀K₂:(E → set(C)). " +
			"∀e₂:(E → A → (num → C) → bool). " +
			"∀ok:(A → bool). " +
			"∀S:(A → set(num)). " +
			"∀M:D. " +
			"∀N:E. " +
			"∀ρ:(num → B). " +
			"∀σ:(num → C). " +
			"∀φ ψ:fo_formula(A).",
		Hypotheses: []string{
			"fo_quantifier_free_equivalent(T₁, K₁, e₁, ok, S, φ, ψ)",
			"fo_quantifier_free_equivalent(T₂, K₂, e₂, ok, S, φ, ψ)",
			"T₁(M)",
			"T₂(N)",
			"fo_fv(S, φ) = ∅",
			"∀χ:fo_formula(A). " +
				"    fo_wf(ok, χ) ∧ fo_qf(χ) ∧ fo_fv(S, χ) = ∅ ⇒ " +
				"    (fo_eval(K₁(M), e₁(M), ρ, χ) ⇔ fo_eval(K₂(N), e₂(N), σ, χ))",
		},
		Conclusion: "fo_eval(K₁(M), e₁(M), ρ, φ) ⇔ fo_eval(K₂(N), e₂(N), σ, φ)",
	},
		func(
			a *Argument,
			T1 *Expr[Set[D]],
			K1 *Arrow2[D, B, Bool],
			e1 *Expr[Fun3[D, A, Fun[Nat, B], Bool]],
			T2 *Expr[Set[E]],
			K2 *Arrow2[E, C, Bool],
			e2 *Expr[Fun3[E, A, Fun[Nat, C], Bool]],
			ok *Expr[Set[A]],
			S *Arrow2[A, Nat, Bool],
			M *Expr[D],
			N *Expr[E],
			ρ *Arrow[Nat, B],
			σ *Arrow[Nat, C],
			φ, ψ *Expr[Formula[A]],
			overFirst, overSecond, modelM, modelN, closed, agree Fact,
		) {
			closedψ := a.Have(
				"ψ is closed, its support lying inside φ's empty one",
				"fo_fv(S, ψ) = ∅",
				By(
					Normalized,
					EquivalentSupport.Read(overFirst),
					closed,
					set_order.SubsetEmpty.At(a.TermAs[Set[Nat]]("fo_fv(S, ψ)"))))
			legalM := a.Have(
				"ρ is legal on φ's empty support",
				"fo_env_ok(K₁(M), fo_fv(S, φ), ρ)",
				By(Normalized, closed, EnvOKEmpty.At(a.TermAs[Set[B]]("K₁(M)"), ρ)))
			legalN := a.Have(
				"and so is σ",
				"fo_env_ok(K₂(N), fo_fv(S, φ), σ)",
				By(Normalized, closed, EnvOKEmpty.At(a.TermAs[Set[C]]("K₂(N)"), σ)))
			a.Show(
				"φ at (M, ρ) is ψ at (M, ρ), which the agreement carries to ψ at (N, σ), which is φ at (N, σ)",
				By(
					Normalized,
					EquivalentAgreement.Read(overFirst).At(M, ρ),
					modelM,
					legalM,
					agree.At(ψ),
					EquivalentWellFormed.Read(overFirst),
					EquivalentQuantifierFree.Read(overFirst),
					closedψ,
					EquivalentAgreement.Read(overSecond).At(N, σ),
					modelN,
					legalN))
		}),
})}
