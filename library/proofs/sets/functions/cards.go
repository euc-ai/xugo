package functions

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var OverrideOnAgree = overrideOnAgreeThm{family.Add(registry.ProofEntry{
	Name: "OverrideOnAgree",
	Key:  "prop_27917b3de4f0237f",
	Build: family.Card(Statement{
		Binders:    "∀K:set(A). ∀v w z:(A → B).",
		Conclusion: "override_on(K, v, z) = override_on(K, w, z) ⇔ w ∈ agree_on(K, v)",
	},
		"Restriction to K with the other points pinned to z forgets exactly the values off "+
			"K. Unfold both definitions and compare the two maps pointwise, splitting on x ∈ K."),
})}

var OverrideOnOverride = overrideOnOverrideThm{family.Add(registry.ProofEntry{
	Name: "OverrideOnOverride",
	Key:  "prop_c83f0a19b11a06c4",
	Build: family.Card(Statement{
		Binders:    "∀K L:set(A). ∀f g h:(A → B).",
		Conclusion: "override_on(K, f, override_on(L, g, h)) = override_on(K ∪ L, override_on(K, f, g), h)",
	},
		"Two overrides compose to one on the union, the outer one winning "+
			"where they overlap: pointwise, split on x ∈ K and then on x ∈ L."),
})}
