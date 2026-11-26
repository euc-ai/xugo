// definitions.go — the chapter's definitional layer: the open sets of
// the real line, what it means for a set of reals to be an interval,
// and the four bounded intervals between two reals: ⟦a, b⟧, ⟬a, b⟭,
// ⟦a, b⟭ and ⟬a, b⟧.

package real_topology

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealTopologyDef — `real_topology`: the sets u of reals each of whose
// points x has a radius δ with every y within δ of x still in u. It is
// the family of open sets itself, so "u is open" is `u ∈
// real_topology` and no separate openness predicate is minted.
var RealTopologyDef = realTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "RealTopologyDef",
	Key:   "prop_6a2dd5bb314f1623",
	Const: "real_topology",
	Type:  "set(set(real))",
	Equations: []string{
		"real_topology = {u:set(real) | ∀x:real. x ∈ u ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∈ u}",
	},
	// The mints of the constants the definiens spells: the
	// comprehension and membership, `<`, real_abs, `-` and the
	// embedding `&`.
})}

// RealIntervalDef — `real_interval(s)`: s holds every real lying
// between two of its points. The empty set, a point, the rays and the
// line are intervals by this reading, open, closed and half-open ones
// alike.
var RealIntervalDef = realIntervalDefThm{family.Define(registry.DefEntry{
	Name:  "RealIntervalDef",
	Key:   "prop_efd193ae1d1c63df",
	Const: "real_interval",
	Type:  "set(real) → bool",
	Equations: []string{
		"∀s:set(real). real_interval(s) ⇔ ∀x y z:real. x ∈ s ∧ z ∈ s ∧ x ≤ y ∧ y ≤ z ⇒ y ∈ s",
	},
	// The mints of membership and `≤`.
})}

// RealClosedIntervalDef — `real_closed_interval(a, b)`, written `⟦a, b⟧`:
// the reals from a to b, both ends included. It is empty when b < a.
var RealClosedIntervalDef = realClosedIntervalDefThm{family.Define(registry.DefEntry{
	Name:      "RealClosedIntervalDef",
	Key:       "prop_c1cc3fc92907ef8",
	Const:     "real_closed_interval",
	Type:      "real → real → set(real)",
	Notation:  "⟦a, b⟧",
	Equations: []string{"∀a b:real. real_closed_interval(a, b) = {x:real | a ≤ x ∧ x ≤ b}"},
	// The closers read x ∈ ⟦a, b⟧ as a ≤ x ∧ x ≤ b.
	MembershipRead: true,
	// The mints of the comprehension and `≤`.
})}

// RealOpenIntervalDef — `real_open_interval(a, b)`, written `⟬a, b⟭`:
// the reals strictly between a and b. It is empty when b ≤ a. The
// tortoise shell brackets keep `(a, b)` the pair.
var RealOpenIntervalDef = realOpenIntervalDefThm{family.Define(registry.DefEntry{
	Name:      "RealOpenIntervalDef",
	Key:       "prop_b2ea370ba1c02908",
	Const:     "real_open_interval",
	Type:      "real → real → set(real)",
	Notation:  "⟬a, b⟭",
	Equations: []string{"∀a b:real. real_open_interval(a, b) = {x:real | a < x ∧ x < b}"},
	// The closers read x ∈ ⟬a, b⟭ as a < x ∧ x < b.
	MembershipRead: true,
	// The mints of the comprehension and `<`.
})}

// RealClosedOpenIntervalDef — `real_closed_open_interval(a, b)`, written
// `⟦a, b⟭`: the reals from a up to b, a included and b not.
var RealClosedOpenIntervalDef = realClosedOpenIntervalDefThm{family.Define(registry.DefEntry{
	Name:      "RealClosedOpenIntervalDef",
	Key:       "prop_11fe4931edbd14b3",
	Const:     "real_closed_open_interval",
	Type:      "real → real → set(real)",
	Notation:  "⟦a, b⟭",
	Equations: []string{"∀a b:real. real_closed_open_interval(a, b) = {x:real | a ≤ x ∧ x < b}"},
	// The closers read x ∈ ⟦a, b⟭ as a ≤ x ∧ x < b.
	MembershipRead: true,
	// The mints of the comprehension, `≤` and `<`.
})}

// RealOpenClosedIntervalDef — `real_open_closed_interval(a, b)`, written
// `⟬a, b⟧`: the reals above a up to b, b included and a not.
var RealOpenClosedIntervalDef = realOpenClosedIntervalDefThm{family.Define(registry.DefEntry{
	Name:      "RealOpenClosedIntervalDef",
	Key:       "prop_1d8cb648025f77a3",
	Const:     "real_open_closed_interval",
	Type:      "real → real → set(real)",
	Notation:  "⟬a, b⟧",
	Equations: []string{"∀a b:real. real_open_closed_interval(a, b) = {x:real | a < x ∧ x ≤ b}"},
	// The closers read x ∈ ⟬a, b⟧ as a < x ∧ x ≤ b.
	MembershipRead: true,
	// The mints of the comprehension, `≤` and `<`.
})}
