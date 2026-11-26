// definitions.go — the Sylow p-subgroups: the predicate and the set of
// them, and the predicate read off as its two conditions and as a
// subgroup.

package sylow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/registry"
)

// SylowSubgroupDef — P is a Sylow p-subgroup of G: a p-subgroup whose index
// p does not divide. In a finite group, for 2 ≤ p, these are the subgroups of
// order p ^ e, e the multiplicity of p in the order of G (SylowOrder).
var SylowSubgroupDef = sylowSubgroupDefThm{family.Define(registry.DefEntry{
	Name:  "SylowSubgroupDef",
	Key:   "prop_9e2e06b67642bc25",
	Const: "sylow_subgroup",
	Type:  "group_ops(A) → num → set(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀p:num. ∀P:set(A). " +
			"    sylow_subgroup(G, p, P) ⇔ p_subgroup(G, p, P) ∧ ¬(p ∣ card(left_cosets(G.mul, G.carrier, P)))",
	},
})}

// SylowSubgroupsDef — `sylow_subgroups(G, p)`: the set of the Sylow
// p-subgroups of G, the set G acts on by conjugation and whose size Sylow
// III counts.
var SylowSubgroupsDef = sylowSubgroupsDefThm{family.Define(registry.DefEntry{
	Name:  "SylowSubgroupsDef",
	Key:   "prop_a6f0bd796fee6196",
	Const: "sylow_subgroups",
	Type:  "group_ops(A) → num → set(set(A))",
	Equations: []string{
		"∀G:group_ops(A). ∀p:num. sylow_subgroups(G, p) = {Q:set(A) | sylow_subgroup(G, p, Q)}",
	},
	// The closers read Q ∈ sylow_subgroups(G, p) as sylow_subgroup(G, p, Q).
	MembershipRead: true,
	Deps:           []registry.EntryLike{SylowSubgroupDef},
})}

// SylowSubgroupPSubgroup — a Sylow p-subgroup is a p-subgroup.
var SylowSubgroupPSubgroup = sylowSubgroupPSubgroupThm{family.Add(registry.ProofEntry{
	Name:  "SylowSubgroupPSubgroup",
	Key:   "prop_293ab73a1ab77b48",
	Build: SylowSubgroupDef.Entry().Conjunct("p_subgroup(G, p, P)"),
})}

// SylowSubgroupIndexNotDivisible — p does not divide the index of a Sylow
// p-subgroup.
var SylowSubgroupIndexNotDivisible = sylowSubgroupIndexNotDivisibleThm{family.Add(registry.ProofEntry{
	Name:  "SylowSubgroupIndexNotDivisible",
	Key:   "prop_1e283493da16001a",
	Build: SylowSubgroupDef.Entry().Conjunct("¬(p ∣ card(left_cosets(G.mul, G.carrier, P)))"),
})}

// SylowSubgroupSubgroup — a Sylow p-subgroup is a subgroup.
var SylowSubgroupSubgroup = sylowSubgroupSubgroupThm{family.Add(registry.ProofEntry{
	Name: "SylowSubgroupSubgroup",
	Key:  "prop_845784487233d2ed",
	Build: SylowSubgroupDef.Entry().Law("subgroup(G, P)",
		func(a *Argument, sylow Fact) {
			a.Show(
				"a Sylow p-subgroup is a p-subgroup, and a p-subgroup is a subgroup",
				By(finite_group.PSubgroupSubgroup.Read(SylowSubgroupPSubgroup.Read(sylow))))
		}),
})}
