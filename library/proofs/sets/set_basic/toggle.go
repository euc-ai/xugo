package set_basic

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// ToggleDef flips membership of one point in a set.
var ToggleDef = toggleDefThm{family.Define(registry.DefEntry{
	Name:      "ToggleDef",
	Key:       "prop_21702267a1602ce6",
	Const:     "set_toggle",
	Type:      "A → set(A) → set(A)",
	Equations: []string{"∀i:A. ∀X:set(A). set_toggle(i, X) = {j:A | j ∈ X ⇔ j ≠ i}"},
	Deps:      []registry.EntryLike{SetMemberDef, SetComprehensionDef, ComprehensionSpecDef},
})}

// InToggle reads membership after a flip. At i it is reversed and elsewhere it is preserved.
var InToggle = inToggleThm{family.Add(registry.ProofEntry{
	Name: "InToggle",
	Key:  "prop_b466b60b3b3ba4a9",
	Build: family.Theorem("∀i:A. ∀X:set(A). ∀j:A. j ∈ set_toggle(i, X) ⇔ (j ∈ X ⇔ j ≠ i)",
		Chain(Simp(Fwd(ToggleDef)), BySets())),
})}

// ToggleInvolution restores every membership bit by flipping the same point twice.
var ToggleInvolution = toggleInvolutionThm{family.Add(registry.ProofEntry{
	Name: "ToggleInvolution",
	Key:  "prop_fb0f5a511288028f",
	Build: family.Theorem("∀i:A. ∀X:set(A). set_toggle(i, set_toggle(i, X)) = X",
		Chain(Simp(Fwd(ToggleDef)), BySets())),
})}

// ToggleInjective: for a fixed set, flips at two points agree only when the points are equal.
var ToggleInjective = toggleInjectiveThm{family.Add(registry.ProofEntry{
	Name: "ToggleInjective",
	Key:  "prop_3a45f28cb598d20c",
	Build: family.Theorem(Statement{
		Binders:    "∀X:set(A). ∀i j:A.",
		Hypotheses: []string{"set_toggle(i, X) = set_toggle(j, X)"},
		Conclusion: "i = j",
	}, Chain(Simp(Fwd(ToggleDef)), BySets())),
})}

// ToggleWhenMember removes the chosen point when it is present.
var ToggleWhenMember = toggleWhenMemberThm{family.Add(registry.ProofEntry{
	Name: "ToggleWhenMember",
	Key:  "prop_7267002c77c7efdc",
	Build: family.Theorem(Statement{
		Binders:    "∀i:A. ∀X:set(A).",
		Hypotheses: []string{"i ∈ X"},
		Conclusion: "set_toggle(i, X) = delete(X, i)",
	}, Chain(Simp(Fwd(ToggleDef)), BySets())),
})}

// ToggleWhenAbsent inserts the chosen point when it is absent.
var ToggleWhenAbsent = toggleWhenAbsentThm{family.Add(registry.ProofEntry{
	Name: "ToggleWhenAbsent",
	Key:  "prop_86c8fe32eaeba944",
	Build: family.Theorem(Statement{
		Binders:    "∀i:A. ∀X:set(A).",
		Hypotheses: []string{"i ∉ X"},
		Conclusion: "set_toggle(i, X) = insert(i, X)",
	}, Chain(Simp(Fwd(ToggleDef)), BySets())),
})}

// ToggleInsertCommute: a flip at one point commutes with inserting another.
var ToggleInsertCommute = toggleInsertCommuteThm{family.Add(registry.ProofEntry{
	Name: "ToggleInsertCommute",
	Key:  "prop_ee382ddaef24766e",
	Build: family.Theorem(Statement{
		Binders:    "∀i j:A. ∀X:set(A).",
		Hypotheses: []string{"j ≠ i"},
		Conclusion: "set_toggle(j, insert(i, X)) = insert(i, set_toggle(j, X))",
	}, Chain(Simp(Fwd(ToggleDef)), BySets())),
})}
