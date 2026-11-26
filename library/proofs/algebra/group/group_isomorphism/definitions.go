// definitions.go — two groups on sets are isomorphic when some map is an
// isomorphism between them; the relation the isomorphism theorems and
// the series of the Jordan–Hölder chapter are stated with.

package group_isomorphism

import (
	"github.com/euc-ai/xugo/library/registry"
)

// GroupIsomorphicDef — two group records are isomorphic when a map
// between them is a group isomorphism.
var GroupIsomorphicDef = groupIsomorphicDefThm{family.Define(registry.DefEntry{
	Name: "GroupIsomorphicDef",
	Key:  "prop_29525fbd0f5f985",

	Const: "group_isomorphic",
	Type:  "group_ops(A) → group_ops(B) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀H:group_ops(B). group_isomorphic(G, H) ⇔ ∃f:(A → B). group_isomorphism(G, H, f)",
	},
})}
