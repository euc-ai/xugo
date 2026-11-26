// definitions.go — the chapter's definitional layer: a homotopy relative
// to a set, the homotopy of paths with their ends held, homotopy
// equivalences and contractible spaces.

package homotopy

import (
	"github.com/euc-ai/xugo/library/registry"
)

// HomotopicRelDef — `homotopic_rel(T, S, a, f, g)`: a continuous map H on
// the product of the space with the unit interval starts at f, ends at g,
// and holds each point of a in the space where f puts it. With a empty it
// is free homotopy.
var HomotopicRelDef = homotopicRelDefThm{family.Define(registry.DefEntry{
	Name:  "HomotopicRelDef",
	Key:   "prop_4fb058b1f83f21d0",
	Const: "homotopic_rel",
	Type:  "set(set(A)) → set(set(B)) → set(A) → (A → B) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀a:set(A). ∀f g:(A → B). " +
			"    homotopic_rel(T, S, a, f, g) ⇔ " +
			"    ∃H:(prod(A, real) → B). " +
			"        continuous_map(product_topology(T, subtopology(real_topology, ⟦&0, &1⟧)), S, H) ∧ " +
			"        (∀x:A. x ∈ ⋃T ⇒ H((x, &0)) = f(x) ∧ H((x, &1)) = g(x)) ∧ " +
			"        (∀x:A. ∀t:real. x ∈ a ∧ x ∈ ⋃T ∧ &0 ≤ t ∧ t ≤ &1 ⇒ H((x, t)) = f(x))",
	},
	Reading: "Neither map is asked to be continuous. Each is H at one end of the interval, so " +
		"each is continuous when T is a topology (SliceLeftContinuous); for an arbitrary family only H " +
		"is: on T = {{1}, {2}} a constant H is continuous on the product while the constant f is not, " +
		"{1, 2} not being a member of T. Only points of the space are read, of f and g and of a alike.",
})}

// PathHomotopicDef — `path_homotopic(T, g, h)`: two paths are homotopic
// with their two ends held.
var PathHomotopicDef = pathHomotopicDefThm{family.Define(registry.DefEntry{
	Name:     "PathHomotopicDef",
	Key:      "prop_a6ede7a869b0cf09",
	Const:    "path_homotopic",
	Type:     "set(set(A)) → (real → A) → (real → A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀g h:(real → A). " +
			"    path_homotopic(T, g, h) ⇔ " +
			"    homotopic_rel(subtopology(real_topology, ⟦&0, &1⟧), T, {&0, &1}, g, h)",
	},
	Reading: "Both maps are paths, each being the homotopy at one end, " +
		"and they share their two ends. Only their values on ⟦0, 1⟧ are read.",
	Deps: []registry.EntryLike{HomotopicRelDef},
})}

// HomotopyEquivalenceDef — `homotopy_equivalence(T, S, f, g)`: f and g
// are continuous maps between the two spaces whose two composites are
// homotopic to the identities. The inverse is named, as a chain homotopy
// equivalence names its own.
var HomotopyEquivalenceDef = homotopyEquivalenceDefThm{family.Define(registry.DefEntry{
	Name:  "HomotopyEquivalenceDef",
	Key:   "prop_4b0763c0dab67028",
	Const: "homotopy_equivalence",
	Type:  "set(set(A)) → set(set(B)) → (A → B) → (B → A) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀g:(B → A). " +
			"    homotopy_equivalence(T, S, f, g) ⇔ " +
			"    continuous_map(T, S, f) ∧ " +
			"    continuous_map(S, T, g) ∧ " +
			"    homotopic_rel(T, T, ∅, g ∘ f, λx:A. x) ∧ " +
			"    homotopic_rel(S, S, ∅, f ∘ g, λy:B. y)",
	},
	Deps: []registry.EntryLike{HomotopicRelDef},
})}

// ContractibleSpaceDef — `contractible_space(T)`: the identity of the
// space is homotopic to a constant map at one of its points.
var ContractibleSpaceDef = contractibleSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "ContractibleSpaceDef",
	Key:   "prop_a19fb2766bd139cd",
	Const: "contractible_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). contractible_space(T) ⇔ ∃c:A. c ∈ ⋃T ∧ homotopic_rel(T, T, ∅, λx:A. x, λx:A. c)",
	},
	Reading: "The empty space is not contractible: there is no point to contract it to.",
	Deps:    []registry.EntryLike{HomotopicRelDef},
})}
