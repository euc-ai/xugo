package cyclic_group

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/registry"
)

// GroupElementOrderDef — the order of x in G: the least positive n at
// which x ^ n is the identity, and 0 when no positive power of x is.
var GroupElementOrderDef = groupElementOrderDefThm{family.Define(registry.DefEntry{
	Name:  "GroupElementOrderDef",
	Key:   "prop_f51a12f75535c975",
	Const: "group_element_order",
	Type:  "group_ops(A) → A → num",
	Equations: []string{"∀G:group_ops(A). ∀x:A. " +
		"    group_element_order(G, x) = " +
		"    COND(∃n:num. 0 < n ∧ monoid_pow(G.mul, G.one, x, n) = G.one, " +
		"        εe:num. " +
		"            0 < e ∧ " +
		"            monoid_pow(G.mul, G.one, x, e) = G.one ∧ " +
		"            (∀d:num. 0 < d ∧ monoid_pow(G.mul, G.one, x, d) = G.one ⇒ e ≤ d), " +
		"        0)"},
})}

// CyclicSubgroupDef — the subgroup x generates: its powers and the
// inverses of its powers.
var CyclicSubgroupDef = cyclicSubgroupDefThm{family.Define(registry.DefEntry{
	Name:  "CyclicSubgroupDef",
	Key:   "prop_513d9f4e4847e976",
	Const: "cyclic_subgroup",
	Type:  "group_ops(A) → A → set(A)",
	Equations: []string{"∀G:group_ops(A). ∀x:A. " +
		"    cyclic_subgroup(G, x) = " +
		"    {y:A | " +
		"        ∃n:num. y = monoid_pow(G.mul, G.one, x, n) ∨ y = G.inv(monoid_pow(G.mul, G.one, x, n))}"},
})}

// CyclicGroupDef — G is a group on its carrier, and one of its elements
// generates the whole carrier.
var CyclicGroupDef = cyclicGroupDefThm{family.Define(registry.DefEntry{
	Name:  "CyclicGroupDef",
	Key:   "prop_9dbefd15fb9d40ea",
	Const: "cyclic_group",
	Type:  "group_ops(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). " +
			"    cyclic_group(G) ⇔ group_on(G) ∧ (∃g:A. g ∈ G.carrier ∧ G.carrier = cyclic_subgroup(G, g))",
	},
	Deps: []registry.EntryLike{CyclicSubgroupDef},
})}
