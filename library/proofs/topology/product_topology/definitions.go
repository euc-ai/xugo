// definitions.go — the chapter's definitional layer: the topology on the
// product of two spaces, read pointwise through open rectangles as the
// topology of a distance is read through balls.

package product_topology

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ProductTopologyDef — `product_topology(T, S)`: a set of pairs is open
// when each of its points lies in a rectangle of two open sets inside it.
// Both topologies are spelled.
var ProductTopologyDef = productTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "ProductTopologyDef",
	Key:   "prop_17d63fb65976ab8c",
	Const: "product_topology",
	Type:  "set(set(A)) → set(set(B)) → set(set(prod(A, B)))",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). " +
			"    product_topology(T, S) = " +
			"    {w:set(prod(A, B)) | " +
			"        ∀p:prod(A, B). " +
			"            p ∈ w ⇒ " +
			"            ∃u:set(A). ∃v:set(B). u ∈ T ∧ v ∈ S ∧ p ∈ set_cross(u, v) ∧ set_cross(u, v) ⊆ w}",
	},
})}
