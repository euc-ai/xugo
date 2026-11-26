// universe_algebra.go — the free algebra in the universe: the interface
// of the free algebra hosted by an injection, read at the universe
// embedding of the coefficient ring, so that no statement of the
// domain names the embedding. The algebra on a set of names, its ring
// record, its constants and variables, its module over the coefficient
// ring, evaluation into a ring, the map induced by a coefficient map and
// a map of the names into the algebra over a second ring, the
// multiplication that flattens a polynomial of polynomials, and the
// algebra maps over the coefficient ring.

package simplicial_ring

import (
	"github.com/euc-ai/xugo/library/registry"
)

// UniverseAlgebraDef — `universe_algebra(R, S)`: the free algebra over R
// on the names S in the universe, read through universe_embedding(R).
var UniverseAlgebraDef = universeAlgebraDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraDef",
	Key:   "prop_b3ab60ebb453e368",
	Const: "universe_algebra",
	Type:  "ring_ops(A) → set(U) → set(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(U). universe_algebra(R, S) = free_algebra(universe_embedding(R), R, S)",
	},
	Reading: "Read as a free algebra under cotangent_universe(R, 𝕌⟨A:U⟩), which makes the " +
		"embedding injective on the polynomials; without it the set is the image of an arbitrary " +
		"map. On the empty set of names it is the constants; over the zero ring it is one point.",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}

// UniverseAlgebraRingDef — `universe_algebra_ring(R, S)`: the free
// algebra over R on S in the universe as a ring record, the operations
// of the one ring on all of U and universe_algebra(R, S) as the carrier.
var UniverseAlgebraRingDef = universeAlgebraRingDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraRingDef",
	Key:   "prop_f089995908b3f301",
	Const: "universe_algebra_ring",
	Type:  "ring_ops(A) → set(U) → ring_ops(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(U). " +
			"    universe_algebra_ring(R, S) = free_algebra_ring(universe_embedding(R), R, S)",
	},
	Reading: "The operations do not read S: the records " +
		"for two sets of names differ in their carriers only.",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}

// UniverseAlgebraConstDef — `universe_algebra_const(R, a)`: the constant a
// in the universe.
var UniverseAlgebraConstDef = universeAlgebraConstDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraConstDef",
	Key:   "prop_cac448fba9073dd3",
	Const: "universe_algebra_const",
	Type:  "ring_ops(A) → A → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀a:A. " +
			"    universe_algebra_const(R, a) = free_algebra_const(universe_embedding(R), R, a)",
	},
	Reading: "No argument carries the host type: the slot it stands in " +
		"fixes it, as ε:(U → B) does in ε(universe_algebra_const(R, a)), and a " +
		"text where nothing else fixes it writes universe_algebra_const⟨U:U⟩(R, a).",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}

// UniverseAlgebraVarDef — `universe_algebra_var(R, x)`: the variable of
// the name x in the universe.
var UniverseAlgebraVarDef = universeAlgebraVarDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraVarDef",
	Key:   "prop_c5f50244907f8798",
	Const: "universe_algebra_var",
	Type:  "ring_ops(A) → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀x:U. universe_algebra_var(R, x) = free_algebra_var(universe_embedding(R), R, x)",
	},
	Reading: "The variable of a name is a member of the algebra and the name " +
		"itself need not be; over the zero ring every variable is the one point.",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}

// UniverseAlgebraModuleDef — `universe_algebra_module(R)`: the free
// algebra over R on all of U as a module over R, a scalar acting by the
// product with its constant.
var UniverseAlgebraModuleDef = universeAlgebraModuleDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraModuleDef",
	Key:   "prop_b3b50f3f7b6c169b",
	Const: "universe_algebra_module",
	Type:  "ring_ops(A) → module_ops(A, U)",
	Equations: []string{
		"∀R:ring_ops(A). universe_algebra_module(R) = free_algebra_module(universe_embedding(R), R)",
	},
	Reading: "Every universe_algebra(R, S) is a subset of its vectors, " +
		"so the free algebras on all sets of names are submodules of one module.",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}

// UniverseAlgebraEvalDef — `universe_algebra_eval(R, R', φ, θ, u)`: the
// member u of the free algebra over R in the universe evaluated in the
// ring R', each coefficient carried by φ and each name x given the value
// θ(x).
var UniverseAlgebraEvalDef = universeAlgebraEvalDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraEvalDef",
	Key:   "prop_8a4b1826c10f1caa",
	Const: "universe_algebra_eval",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → (U → B) → U → B",
	Equations: []string{
		"∀R:ring_ops(A). ∀R':ring_ops(B). ∀φ:(A → B). ∀θ:(U → B). ∀u:U. " +
			"    universe_algebra_eval(R, R', φ, θ, u) = " +
			"    free_algebra_eval(universe_embedding(R), R, R', φ, θ, u)",
	},
	Reading: "R' is any ring record, the free algebra over another coefficient " +
		"ring among them (universe_algebra_ring(R', T) at B = U), so an evaluation may " +
		"change the coefficient ring. The value is read on a member of the algebra only.",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}

// UniverseAlgebraMapDef — `universe_algebra_map(R, R', φ, h, u)`: the map
// from the free algebra over R in the universe to the free algebra over
// R' in the universe that carries the constant a to the constant φ(a)
// and the variable of the name x to the variable of the name h(x).
var UniverseAlgebraMapDef = universeAlgebraMapDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraMapDef",
	Key:   "prop_97e3c57b51409a02",
	Const: "universe_algebra_map",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → (U → U) → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀R':ring_ops(B). ∀φ:(A → B). ∀h:(U → U). ∀u:U. " +
			"    universe_algebra_map(R, R', φ, h, u) = " +
			"    free_algebra_map(universe_embedding(R), universe_embedding(R'), R, R', φ, h, u)",
	},
	Reading: "The two algebras are read through the universe embeddings of the two rings, " +
		"so with R' a ring on B and φ a ring map the map changes the coefficients from A to B in " +
		"the one host; at R' = R and φ = λa. a it is the map induced by a map of the names alone.",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}

// UniverseAlgebraMultDef — `universe_algebra_mult(R, u)`: the
// multiplication of the free algebra as a monad in the universe — u, a
// polynomial whose names are members of the free algebra over R in the
// universe, evaluated there with each name standing for itself.
var UniverseAlgebraMultDef = universeAlgebraMultDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraMultDef",
	Key:   "prop_61a4e071be0a96af",
	Const: "universe_algebra_mult",
	Type:  "ring_ops(A) → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀u:U. " +
			"    universe_algebra_mult(R, u) = free_algebra_mult(universe_embedding(R), R, u)",
	},
	Reading: "On the free algebra on universe_algebra(R, " +
		"S) as names its values lie in universe_algebra(R, S).",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}

// UniverseAlgebraHomomorphismDef — `universe_algebra_homomorphism(R, S, T,
// F)`: F is an algebra map over R from the free algebra over R on S to
// the free algebra over R on T, both in the universe — a ring
// homomorphism of the two that fixes every constant.
var UniverseAlgebraHomomorphismDef = universeAlgebraHomomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "UniverseAlgebraHomomorphismDef",
	Key:   "prop_973d7759bf02410d",
	Const: "universe_algebra_homomorphism",
	Type:  "ring_ops(A) → set(U) → set(U) → (U → U) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀S T:set(U). ∀F:(U → U). " +
			"    universe_algebra_homomorphism(R, S, T, F) ⇔ " +
			"    free_algebra_homomorphism(universe_embedding(R), " +
			"        universe_embedding(R), " +
			"        R, " +
			"        R, " +
			"        λa:A. a, " +
			"        S, " +
			"        T, " +
			"        F)",
	},
	Reading: "One coefficient ring on both sides; a map that also changes the " +
		"coefficients, over a ring map φ from R to R', is free_algebra_homomorphism at the " +
		"universe embeddings of the two rings. F is read on universe_algebra(R, S) only.",
	Deps: []registry.EntryLike{UniverseEmbeddingDef},
})}
