// fixed_point.go — the fixed point property, carried across a
// homeomorphism and down to a retract.

package continuous

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// HomeomorphicFixedPoint — the fixed point property passes to a
// homeomorphic space.
var HomeomorphicFixedPoint = homeomorphicFixedPointThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphicFixedPoint",
	Key:  "prop_181f9a4031bbfe36",
	Reading: "No axiom on either family. An empty S forces ⋃T empty, where fixed_point_property(T) " +
		"fails, the identity having nothing to fix; so the hypotheses never meet the empty case.",
	Deps: []registry.EntryLike{
		FixedPointPropertyDef,
		HomeomorphicDef,
		HomeomorphismInverseMaps,
		Compose,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"homeomorphic(T, S)",
			"fixed_point_property(T)",
		},
		Conclusion: "fixed_point_property(S)",
	},
		"for h a homeomorphism of T onto S with inverse k and g a continuous self-map of S, k "+
			"∘ g ∘ h is a continuous self-map of T (Compose); its fixed point x gives k(g(h(x))) "+
			"= x, and applying h, which undoes k on ⋃S, g(h(x)) = h(x) (HomeomorphismInverseMaps)"),
})}

// RetractFixedPoint — the fixed point property passes to a retract.
var RetractFixedPoint = retractFixedPointThm{family.Add(registry.ProofEntry{
	Name: "RetractFixedPoint",
	Key:  "prop_4c8f20589b5ce504",
	Reading: "s ⊆ ⋃T, inside retract_of, makes the subspace's points " +
		"exactly s. s = ∅ forces ⋃T = ∅, against fixed_point_property(T).",
	Deps: []registry.EntryLike{FixedPointPropertyDef, RetractOfDef, Compose, IntoSubtopology},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"retract_of(T, s)",
			"fixed_point_property(T)",
		},
		Conclusion: "fixed_point_property(subtopology(T, s))",
	},
		"for r the retraction and f a continuous self-map of the subspace s, f ∘ r is "+
			"continuous from T into the subspace (Compose) and so into T (IntoSubtopology); "+
			"its fixed point x is f(r(x)), a point of s, so r(x) = x and f(x) = x"),
})}
