// definitions.go — the chapter's definitional layer: what it means for
// a map between two spaces to be continuous.

package continuous

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousMap — `continuous_map(T, S, f)`: f carries the space ⋃T
// into the space ⋃S, and the part of ⋃T that f sends into an open set
// of S is open in T. The preimage is cut to the space, since the map's
// domain type may hold points outside it; both topologies are
// spelled, the map crossing from one to the other.
var ContinuousMap = continuousMapThm{family.DefineStructure(registry.DefEntry{
	Name:    "ContinuousMap",
	Key:     "prop_d9ce7c038eb70b2e",
	Const:   "continuous_map",
	Subject: "f",
	Type:    "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). " +
			"    continuous_map(T, S, f) ⇔ " +
			"    (∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃S) ∧ (∀v:set(B). v ∈ S ⇒ preimage_on(⋃T, f, v) ∈ T)",
	},
})}

// HomeomorphicMap — `homeomorphic_map(T, S, f)`: f is continuous and has
// a continuous inverse on the two spaces — a map g back with g(f(x)) = x
// on ⋃T and f(g(y)) = y on ⋃S. Only the points of the spaces are asked
// to correspond, the types may hold more.
var HomeomorphicMap = homeomorphicMapThm{family.DefineStructure(registry.DefEntry{
	Name:    "HomeomorphicMap",
	Key:     "prop_b6bb223c2b13721d",
	Const:   "homeomorphic_map",
	Subject: "f",
	Type:    "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). " +
			"    homeomorphic_map(T, S, f) ⇔ " +
			"    continuous_map(T, S, f) ∧ " +
			"    ∃g:(B → A). " +
			"        continuous_map(S, T, g) ∧ (∀x:A. x ∈ ⋃T ⇒ g(f(x)) = x) ∧ (∀y:B. y ∈ ⋃S ⇒ f(g(y)) = y)",
	},
	Deps: []registry.EntryLike{ContinuousMap},
})}

// ContinuousMapAtDef — `continuous_map_at(T, S, f, x)`: x is a point of the
// first space carried into the second, and every open neighbourhood of
// f(x) receives an open neighbourhood of x.
var ContinuousMapAtDef = continuousMapAtDefThm{family.Define(registry.DefEntry{
	Name:  "ContinuousMapAtDef",
	Key:   "prop_a39999ef386d7aa1",
	Const: "continuous_map_at",
	Type:  "set(set(A)) → set(set(B)) → (A → B) → A → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀x:A. " +
			"    continuous_map_at(T, S, f, x) ⇔ " +
			"    x ∈ ⋃T ∧ " +
			"    f(x) ∈ ⋃S ∧ " +
			"    ∀v:set(B). v ∈ S ∧ f(x) ∈ v ⇒ ∃u:set(A). u ∈ T ∧ x ∈ u ∧ ∀y:A. y ∈ u ⇒ f(y) ∈ v",
	},
})}

// OpenMap — `open_map(T, S, f)`: the image of every open set is open.
// The map is not asked to be continuous.
var OpenMap = openMapThm{family.DefineStructure(registry.DefEntry{
	Name:    "OpenMap",
	Key:     "prop_10f13cc83fc97a00",
	Const:   "open_map",
	Subject: "f",
	Type:    "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). " +
			"    open_map(T, S, f) ⇔ ∀u:set(A). u ∈ T ⇒ image(f, u) ∈ S",
	},
})}

// ClosedMap — `closed_map(T, S, f)`: the image of every closed set is
// closed. The map is not asked to be continuous.
var ClosedMap = closedMapThm{family.DefineStructure(registry.DefEntry{
	Name:    "ClosedMap",
	Key:     "prop_633d4a0eb88fc440",
	Const:   "closed_map",
	Subject: "f",
	Type:    "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). " +
			"    closed_map(T, S, f) ⇔ ∀c:set(A). closed_in(T, c) ⇒ closed_in(S, image(f, c))",
	},
})}

// QuotientMap — `quotient_map(T, S, f)`: f carries the first space onto
// the second, and a subset of the second is open exactly when its
// preimage is.
var QuotientMap = quotientMapThm{family.DefineStructure(registry.DefEntry{
	Name:    "QuotientMap",
	Key:     "prop_60e4dbb4dff0b938",
	Const:   "quotient_map",
	Subject: "f",
	Type:    "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). " +
			"    quotient_map(T, S, f) ⇔ " +
			"    image(f, ⋃T) = ⋃S ∧ ∀v:set(B). v ⊆ ⋃S ⇒ (preimage_on(⋃T, f, v) ∈ T ⇔ v ∈ S)",
	},
})}

// QuotientTopologyDef — `quotient_topology(T, f)`: the subsets of the image
// of the space whose preimage is open — the finest topology on the image
// for which f is continuous.
var QuotientTopologyDef = quotientTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "QuotientTopologyDef",
	Key:   "prop_ed744de9412e5c19",
	Const: "quotient_topology",
	Type:  "set(set(A)) → (A → B) → set(set(B))",
	Equations: []string{
		"∀T:set(set(A)). ∀f:(A → B). " +
			"    quotient_topology(T, f) = {v:set(B) | v ⊆ image(f, ⋃T) ∧ preimage_on(⋃T, f, v) ∈ T}",
	},
})}

// HomeomorphicDef — `homeomorphic(T, S)`: some map is a homeomorphism of
// the first space onto the second.
var HomeomorphicDef = homeomorphicDefThm{family.Define(registry.DefEntry{
	Name:  "HomeomorphicDef",
	Key:   "prop_af3836b029c8eb64",
	Const: "homeomorphic",
	Type:  "set(set(A)) → set(set(B)) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). homeomorphic(T, S) ⇔ ∃f:(A → B). homeomorphic_map(T, S, f)",
	},
	Deps: []registry.EntryLike{HomeomorphicMap},
})}

// EmbeddingMap — `embedding_map(T, S, f)`: f is a homeomorphism of the
// first space onto its image, read as a subspace of the second.
var EmbeddingMap = embeddingMapThm{family.DefineStructure(registry.DefEntry{
	Name:    "EmbeddingMap",
	Key:     "prop_7e5e3505d04f415b",
	Const:   "embedding_map",
	Subject: "f",
	Type:    "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). " +
			"    embedding_map(T, S, f) ⇔ homeomorphic_map(T, subtopology(S, image(f, ⋃T)), f)",
	},
	Deps: []registry.EntryLike{HomeomorphicMap},
})}

// RetractOfDef — `retract_of(T, s)`: s lies in the space, and some
// continuous map of the space into the subspace s fixes every point of s.
// The topology is implicit under a law over it.
var RetractOfDef = retractOfDefThm{family.Define(registry.DefEntry{
	Name:     "RetractOfDef",
	Key:      "prop_2a1d48ed2bfff11c",
	Const:    "retract_of",
	Type:     "set(set(A)) → set(A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀s:set(A). " +
			"    retract_of(T, s) ⇔ " +
			"    s ⊆ ⋃T ∧ ∃r:(A → A). continuous_map(T, subtopology(T, s), r) ∧ ∀x:A. x ∈ s ⇒ r(x) = x",
	},
	Deps: []registry.EntryLike{ContinuousMap},
})}

// FixedPointPropertyDef — `fixed_point_property(T)`: every continuous map
// of the space into itself fixes a point of it. The empty space lacks it,
// having no point to fix.
var FixedPointPropertyDef = fixedPointPropertyDefThm{family.Define(registry.DefEntry{
	Name:  "FixedPointPropertyDef",
	Key:   "prop_b441adcbc587f3e8",
	Const: "fixed_point_property",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    fixed_point_property(T) ⇔ ∀f:(A → A). continuous_map(T, T, f) ⇒ ∃x:A. x ∈ ⋃T ∧ f(x) = x",
	},
	Deps: []registry.EntryLike{ContinuousMap},
})}
