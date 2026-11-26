// carrier_lattice.go — partial orders and complete lattices on a set.

package order

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// PartialOrderOn — a partial order on a carrier is a preorder whose related pairs in both directions are equal.
var PartialOrderOn = partialOrderOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "PartialOrderOn",
	Key:     "prop_60243424b48f6b02",
	Const:   "partial_order_on",
	Subject: "c",
	Type:    "set(A) → (A → A → bool) → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). " +
			"    partial_order_on(c, R) ⇔ " +
			"    preorder_on(c, R) ∧ (∀x y:A. x ∈ c ∧ y ∈ c ⇒ R(x, y) ∧ R(y, x) ⇒ x = y)",
	},
	Deps: []registry.EntryLike{PreorderOn},
})}

// HasSupOnDef — a supremum on a carrier bounds a subset and is below every carrier point that bounds it.
var HasSupOnDef = hasSupOnDefThm{family.Define(registry.DefEntry{
	Name:  "HasSupOnDef",
	Key:   "prop_8372c1941a0e168e",
	Const: "has_sup_on",
	Type:  "set(A) → (A → A → bool) → set(A) → A → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). ∀s:set(A). ∀b:A. " +
			"    has_sup_on(c, R, s, b) ⇔ " +
			"    s ⊆ c ∧ b ∈ c ∧ upper_bound(R, s, b) ∧ (∀a:A. a ∈ c ∧ upper_bound(R, s, a) ⇒ R(b, a))",
	},
	Deps: []registry.EntryLike{UpperBoundDef},
})}

// HasInfOnDef — an infimum on a carrier bounds a subset below and is above every carrier point that bounds it below.
var HasInfOnDef = hasInfOnDefThm{family.Define(registry.DefEntry{
	Name:  "HasInfOnDef",
	Key:   "prop_cabd1c1a5a5ea73",
	Const: "has_inf_on",
	Type:  "set(A) → (A → A → bool) → set(A) → A → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). ∀s:set(A). ∀b:A. " +
			"    has_inf_on(c, R, s, b) ⇔ " +
			"    s ⊆ c ∧ b ∈ c ∧ lower_bound(R, s, b) ∧ (∀a:A. a ∈ c ∧ lower_bound(R, s, a) ⇒ R(a, b))",
	},
	Deps: []registry.EntryLike{LowerBoundDef},
})}

// CompleteLatticeOn — a complete lattice on a carrier has a supremum and an infimum in the carrier for each of its subsets.
var CompleteLatticeOn = completeLatticeOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "CompleteLatticeOn",
	Key:     "prop_6957962f626ec15",
	Const:   "complete_lattice_on",
	Subject: "c",
	Type:    "set(A) → (A → A → bool) → (set(A) → A) → (set(A) → A) → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). ∀sup inf:(set(A) → A). " +
			"    complete_lattice_on(c, R, sup, inf) ⇔ " +
			"    partial_order_on(c, R) ∧ " +
			"    (∀s:set(A). s ⊆ c ⇒ has_sup_on(c, R, s, sup(s))) ∧ " +
			"    (∀s:set(A). s ⊆ c ⇒ has_inf_on(c, R, s, inf(s)))",
	},
	Deps: []registry.EntryLike{PartialOrderOn, HasSupOnDef, HasInfOnDef},
})}

// PartialOrderOnPreorder — a partial order on a set is a preorder on that set.
var PartialOrderOnPreorder = partialOrderOnPreorderThm{family.Add(registry.ProofEntry{
	Name:  "PartialOrderOnPreorder",
	Key:   "prop_756c7e9644ae403f",
	Build: PartialOrderOn.Axiom("preorder_on(c, R)"),
})}

// AntisymmetricOn — two carrier points related in both directions are equal.
var AntisymmetricOn = antisymmetricOnThm{family.Add(registry.ProofEntry{
	Name: "AntisymmetricOn",
	Key:  "prop_e6b455d29933408a",
	Build: PartialOrderOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"R(x, y)",
			"R(y, x)",
		},
		Conclusion: "x = y",
	}),
})}

// CompleteLatticeOnPartialOrder — a complete lattice on a set is a partial order on that set.
var CompleteLatticeOnPartialOrder = completeLatticeOnPartialOrderThm{family.Add(registry.ProofEntry{
	Name:  "CompleteLatticeOnPartialOrder",
	Key:   "prop_d2e2032e2a210d89",
	Build: CompleteLatticeOn.Axiom("partial_order_on(c, R)"),
})}

// SupHasSupOn — the supplied supremum is the least upper bound of each subset of the carrier.
var SupHasSupOn = supHasSupOnThm{family.Add(registry.ProofEntry{
	Name: "SupHasSupOn",
	Key:  "prop_220a2b889d44c630",
	Build: CompleteLatticeOn.Axiom(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ c",
		},
		Conclusion: "has_sup_on(c, R, s, sup(s))",
	}),
})}

// InfHasInfOn — the supplied infimum is the greatest lower bound of each subset of the carrier.
var InfHasInfOn = infHasInfOnThm{family.Add(registry.ProofEntry{
	Name: "InfHasInfOn",
	Key:  "prop_7efab88c980539e",
	Build: CompleteLatticeOn.Axiom(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ c",
		},
		Conclusion: "has_inf_on(c, R, s, inf(s))",
	}),
})}

// CompleteLatticeOnDual — reversing a complete lattice exchanges its supremum and infimum: upper bounds become lower bounds.
var CompleteLatticeOnDual = completeLatticeOnDualThm{family.Add(registry.ProofEntry{
	Name: "CompleteLatticeOnDual",
	Key:  "prop_86082edc182afaa6",
	Build: CompleteLatticeOn.Law("complete_lattice_on(c, λx:A. λy:A. R(y, x), inf, sup)",
		func(a *Argument, lattice CompleteLatticeFact[on.C]) {
			partial := CompleteLatticeOnPartialOrder.Read(lattice)
			preorder := PartialOrderOnPreorder.Read(partial)
			a.Do(
				Simp(Fwd(CompleteLatticeOn)),
				SplitConjAll(
					Case(
						"the reversed relation is a partial order on the carrier",
						Simp(Fwd(PartialOrderOn), Fwd(PreorderOn)),
						SplitConjAll(
							Case(
								"reflexivity is unchanged",
								By(ReflexiveOn.Read(preorder))),
							Case(
								"transitivity follows along the reversed chain",
								By(TransitiveOn.Read(preorder))),
							Case(
								"antisymmetry uses the same two related points",
								By(AntisymmetricOn.Read(partial))),
						),
					),
					Case(
						"each original infimum is a supremum for the reversed relation",
						Cite(InfHasInfOn.Read(lattice)),
						Unfold(HasSupOnDef),
						Unfold(HasInfOnDef),
						Unfold(UpperBoundDef),
						Unfold(LowerBoundDef),
					),
					Case(
						"each original supremum is an infimum for the reversed relation",
						Cite(SupHasSupOn.Read(lattice)),
						Unfold(HasSupOnDef),
						Unfold(HasInfOnDef),
						Unfold(UpperBoundDef),
						Unfold(LowerBoundDef),
					),
				),
			)
		}),
})}
