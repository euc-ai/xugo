package group_action

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// GroupAction — G acts on the set X by act: G is a group on its carrier,
// each element of G maps X into X, the identity fixes every point, and
// acting by a product is acting by its factors in turn.
var GroupAction = groupActionThm{family.DefineStructure(registry.DefEntry{
	Name:  "GroupAction",
	Key:   "prop_f637e4e1610b9270",
	Const: "group_action",
	Type:  "group_ops(A) → set(B) → (A → B → B) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀X:set(B). ∀act:(A → B → B). " +
			"    group_action(G, X, act) ⇔ " +
			"    group_on(G) ∧ " +
			"    (∀g:A. ∀x:B. g ∈ G.carrier ∧ x ∈ X ⇒ act(g, x) ∈ X) ∧ " +
			"    (∀x:B. x ∈ X ⇒ act(G.one, x) = x) ∧ " +
			"    (∀g h:A. ∀x:B. " +
			"        g ∈ G.carrier ∧ h ∈ G.carrier ∧ x ∈ X ⇒ act(G.mul(g, h), x) = act(g, act(h, x)))",
	},
})}

// GroupOrbitDef — the orbit of x: the points the elements of G move x to.
var GroupOrbitDef = groupOrbitDefThm{family.Define(registry.DefEntry{
	Name:  "GroupOrbitDef",
	Key:   "prop_a6f079d18473cd34",
	Const: "group_orbit",
	Type:  "group_ops(A) → (A → B → B) → B → set(B)",
	Equations: []string{
		"∀G:group_ops(A). ∀act:(A → B → B). ∀x:B. " +
			"    group_orbit(G, act, x) = image(λg:A. act(g, x), G.carrier)",
	},
})}

// GroupStabilizerDef — the stabilizer of x: the elements of G that fix x.
var GroupStabilizerDef = groupStabilizerDefThm{family.Define(registry.DefEntry{
	Name:  "GroupStabilizerDef",
	Key:   "prop_888929a8f5c50fc2",
	Const: "group_stabilizer",
	Type:  "group_ops(A) → (A → B → B) → B → set(A)",
	Equations: []string{
		"∀G:group_ops(A). ∀act:(A → B → B). ∀x:B. " +
			"    group_stabilizer(G, act, x) = {g:A | g ∈ G.carrier ∧ act(g, x) = x}",
	},
})}

// GroupFixedPointsDef — the points of X that the element g fixes.
var GroupFixedPointsDef = groupFixedPointsDefThm{family.Define(registry.DefEntry{
	Name:  "GroupFixedPointsDef",
	Key:   "prop_36444a67c5c7887c",
	Const: "group_fixed_points",
	Type:  "set(B) → (A → B → B) → A → set(B)",
	Equations: []string{
		"∀X:set(B). ∀act:(A → B → B). ∀g:A. group_fixed_points(X, act, g) = {x:B | x ∈ X ∧ act(g, x) = x}",
	},
})}

// GroupConjugateDef — the conjugate gSg⁻¹ of a set S by g: the image of S
// under x ↦ g * x * g⁻¹. The group acts on the subsets of its carrier by
// it (ConjugationAction).
var GroupConjugateDef = groupConjugateDefThm{family.Define(registry.DefEntry{
	Name:  "GroupConjugateDef",
	Key:   "prop_ffa9bc3cdc66765f",
	Const: "group_conjugate",
	Type:  "group_ops(A) → A → set(A) → set(A)",
	Equations: []string{
		"∀G:group_ops(A). ∀g:A. ∀S:set(A). " +
			"    group_conjugate(G, g, S) = image(λx:A. G.mul(G.mul(g, x), G.inv(g)), S)",
	},
})}

// GroupNormalizerDef — the normalizer of H: the elements of G whose
// conjugation carries H onto itself.
var GroupNormalizerDef = groupNormalizerDefThm{family.Define(registry.DefEntry{
	Name:  "GroupNormalizerDef",
	Key:   "prop_b0d85fd394c5c3c",
	Const: "group_normalizer",
	Type:  "group_ops(A) → set(A) → set(A)",
	Equations: []string{
		"∀G:group_ops(A). ∀H:set(A). " +
			"    group_normalizer(G, H) = {g:A | g ∈ G.carrier ∧ group_conjugate(G, g, H) = H}",
	},
	Deps: []registry.EntryLike{GroupConjugateDef},
})}
