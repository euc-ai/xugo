package polish_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

var ProductGroupPolish = productGroupPolishThm{family.Add(registry.ProofEntry{
	Name: "ProductGroupPolish",
	Key:  "prop_1363a1f7d45bac2f",
	Build: family.Card(
		Statement{
			Binders: "∀J:set(I). " +
				"∀z:(I → A). " +
				"∀G:(I → group_ops(A)). " +
				"∀T:(I → set(set(A))). " +
				"∀H:group_ops(I → A).",
			Hypotheses: []string{
				"countable(J)",
				"∀i:I. abelian_group_on(G(i)) ∧ z(i) = G(i).one",
				"∀i:I. i ∈ J ⇒ polish_abelian_group(G(i), T(i))",
				"H.carrier = indexed_functions(J, z, λi:I. G(i).carrier)",
				"H.one = z",
				"∀u v:(I → A). ∀i:I. u ∈ H.carrier ∧ v ∈ H.carrier ⇒ H.mul(u, v)(i) = G(i).mul(u(i), v(i))",
				"∀u:(I → A). ∀i:I. u ∈ H.carrier ⇒ H.inv(u)(i) = G(i).inv(u(i))",
			},
			Conclusion: "polish_abelian_group(H, indexed_product_topology(J, z, T))",
		},
		"CountableProductPolish supplies the space. The coordinate group operations are "+
			"continuous; inverse images of cylinders prove continuity of the product operations."),
	Deps: []registry.EntryLike{
		polish_space.CountableProductPolish,
		product_topology.IndexedProductCarrier,
	},
	Reading: "CountableProductPolish supplies the space. The coordinate group operations " +
		"are continuous; inverse images of cylinders prove continuity of the product operations.",
})}
