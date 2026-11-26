package boolean_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// LocalSensitivityDef counts the coordinates whose flip changes the Boolean value at X.
var LocalSensitivityDef = localSensitivityDefThm{family.Define(registry.DefEntry{
	Name:  "LocalSensitivityDef",
	Key:   "prop_5aafbbf9e77e85b9",
	Const: "local_sensitivity",
	Type:  "set(A) → (set(A) → bool) → set(A) → num",
	Equations: []string{
		"∀U:set(A). ∀f:(set(A) → bool). ∀X:set(A). " +
			"    local_sensitivity(U, f, X) = card({i:A | i ∈ U ∧ f(X) ≠ f(set_toggle(i, X))})",
	},
})}

// SensitivityDef selects the largest local sensitivity attained on the cube of subsets of U.
var SensitivityDef = sensitivityDefThm{family.Define(registry.DefEntry{
	Name:  "SensitivityDef",
	Key:   "prop_a7c8c2c1bf6b0e77",
	Const: "sensitivity",
	Type:  "set(A) → (set(A) → bool) → num",
	Equations: []string{
		"∀U:set(A). ∀f:(set(A) → bool). " +
			"    sensitivity(U, f) = " +
			"    εm:num. " +
			"        (∃X:set(A). X ⊆ U ∧ local_sensitivity(U, f, X) = m) ∧ " +
			"        (∀X:set(A). X ⊆ U ⇒ local_sensitivity(U, f, X) ≤ m)",
	},
	Deps: []registry.EntryLike{LocalSensitivityDef},
})}

// LocalSensitivityLeCard bounds the count at any input by the number of available coordinates.
var LocalSensitivityLeCard = localSensitivityLeCardThm{family.Add(registry.ProofEntry{
	Name: "LocalSensitivityLeCard",
	Key:  "prop_c5f7a4ca35feee6",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀f:(set(A) → bool). ∀X:set(A).",
		Hypotheses: []string{"finite(U)"},
		Conclusion: "local_sensitivity(U, f, X) ≤ card(U)",
		Abbrev:     Abbrev{{Name: "Changes", Text: "{i:A | i ∈ U ∧ f(X) ≠ f(set_toggle(i, X))}"}},
	}, func(a *Argument, U *Expr[Set[A]], f *Arrow[Set[A], Bool], X *Expr[Set[A]], finite Fact) {
		within := a.Have(
			"every changing coordinate lies in U",
			"«Changes» ⊆ U",
			BySets())
		a.Show(
			"count the changing coordinates inside U",
			Simp(Fwd(LocalSensitivityDef)),
			By(finite, within, cardinality.CardSubset.At(a.TermAs[Set[A]]("«Changes»"), U)))
	}),
})}

// SensitivityMaximum shows that the choice in the definition is attained.
// The input U supplies a value even in dimension zero, and the dimension bounds every value.
var SensitivityMaximum = sensitivityMaximumThm{family.Add(registry.ProofEntry{
	Name: "SensitivityMaximum",
	Key:  "prop_2635f33ad063d154",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(U)"},
		Conclusion: "«Attained»(sensitivity(U, f)) ∧ " +
			"(∀X:set(A). X ⊆ U ⇒ local_sensitivity(U, f, X) ≤ sensitivity(U, f))",
		Abbrev: Abbrev{
			{Name: "Attained", Text: "λn:num. ∃X:set(A). X ⊆ U ∧ local_sensitivity(U, f, X) = n"},
		},
	}, func(a *Argument, U *Expr[Set[A]], f *Arrow[Set[A], Bool], finite Fact) {
		a.Have(
			"the attained values have a maximum",
			"∃m:num. «Attained»(m) ∧ (∀X:set(A). X ⊆ U ⇒ local_sensitivity(U, f, X) ≤ m)",
			Derive(func(b *Argument) {
				some := b.Have(
					"U supplies a first value",
					"∃n:num. «Attained»(n)",
					Witness(b.TermAs[Nat]("local_sensitivity(U, f, U)")),
					Witness(U),
					BySets())
				bounded := b.Have(
					"the coordinate count bounds the attained values",
					"∃M:num. ∀n:num. «Attained»(n) ⇒ n ≤ M",
					Witness(b.TermAs[Nat]("card(U)")),
					By(finite, At(LocalSensitivityLeCard, U, f)))
				b.Show(
					"take the maximum of this nonempty bounded set of natural numbers",
					By(some, bounded, nat_order.MaximumExists.At(b.TermAs[Set[Nat]]("«Attained»"))))
			}))
		a.Show(
			"sensitivity chooses such a maximum",
			Unfold(SensitivityDef))
	}),
})}

// SensitivityBounds applies the maximum's upper bound at the given input.
var SensitivityBounds = sensitivityBoundsThm{family.Add(registry.ProofEntry{
	Name: "SensitivityBounds",
	Key:  "prop_a4032198a1e6c8ef",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀f:(set(A) → bool). ∀X:set(A).",
		Hypotheses: []string{"finite(U)", "X ⊆ U"},
		Conclusion: "local_sensitivity(U, f, X) ≤ sensitivity(U, f)",
	}, func(a *Argument, U *Expr[Set[A]], f *Arrow[Set[A], Bool], X *Expr[Set[A]], finite, input Fact) {
		a.Show(
			"the maximum bounds the count at X",
			By(finite, input, SensitivityMaximum.At(U, f)))
	}),
})}

// SensitivityLeCard bounds the maximum by the number of coordinates, since it occurs at an input.
var SensitivityLeCard = sensitivityLeCardThm{family.Add(registry.ProofEntry{
	Name: "SensitivityLeCard",
	Key:  "prop_5101a32a8ac83e20",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(U)"},
		Conclusion: "sensitivity(U, f) ≤ card(U)",
	}, func(a *Argument, U *Expr[Set[A]], f *Arrow[Set[A], Bool], finite Fact) {
		a.Show(
			"the coordinate count bounds the value at a maximizing input",
			By(finite, SensitivityMaximum.At(U, f), At(LocalSensitivityLeCard, U, f)))
	}),
})}

// LocalSensitivityConstant counts zero changes at every input of a constant function.
var LocalSensitivityConstant = localSensitivityConstantThm{family.Add(registry.ProofEntry{
	Name: "LocalSensitivityConstant",
	Key:  "prop_4933458b16fd31c1",
	Build: family.Theorem("∀U X:set(A). ∀c:bool. local_sensitivity(U, λY:set(A). c, X) = 0",
		func(a *Argument, U, X *Expr[Set[A]], c *Expr[Bool]) {
			a.Do(Simp(Fwd(LocalSensitivityDef)))
			noChanges := a.Have(
				"a flip leaves the constant value unchanged",
				"{i:A | i ∈ U ∧ c ≠ c} = ∅",
				BySets())
			a.Show(
				"the empty set has cardinality zero",
				By(noChanges, cardinality.CardClauses.Inst[A]()))
		}),
})}

// SensitivityConstant evaluates a constant function at an input attaining its maximum.
var SensitivityConstant = sensitivityConstantThm{family.Add(registry.ProofEntry{
	Name: "SensitivityConstant",
	Key:  "prop_66cc5e9469adad47",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀c:bool.",
		Hypotheses: []string{"finite(U)"},
		Conclusion: "sensitivity(U, «Constant») = 0",
		Abbrev:     Abbrev{{Name: "Constant", Text: "λY:set(A). c"}},
	}, func(a *Argument, U *Expr[Set[A]], c *Expr[Bool], finite Fact) {
		X, achieves := a.ObtainAs[Set[A]](
			"choose an input attaining the maximum",
			"∃X:set(A). X ⊆ U ∧ local_sensitivity(U, «Constant», X) = sensitivity(U, «Constant»)",
			By(finite, SensitivityMaximum.At(U, a.TermAs[Fun[Set[A], Bool]]("«Constant»"))))
		a.Show(
			"the count there is zero",
			By(Normalized, achieves, LocalSensitivityConstant.At(U, X, c)))
	}),
})}

// SensitivityEmpty gives the sensitivity of every Boolean function on a cube with no coordinates.
var SensitivityEmpty = sensitivityEmptyThm{family.Add(registry.ProofEntry{
	Name: "SensitivityEmpty",
	Key:  "prop_b2948ea91df47bda",
	Build: family.Theorem("∀f:(set(A) → bool). sensitivity(∅, f) = 0",
		func(a *Argument, f *Arrow[Set[A], Bool]) {
			a.Show(
				"the coordinate count bounds sensitivity by zero",
				ByArith(
					finite_set.FiniteRules.Inst[A](),
					cardinality.CardClauses.Inst[A](),
					SensitivityLeCard.At(a.TermAs[Set[A]]("∅"), f)))
		}),
})}
