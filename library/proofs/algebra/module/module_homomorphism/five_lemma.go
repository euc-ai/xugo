// Five-term exact diagrams admit different vector host types at every vertex.

package module_homomorphism

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var FiveLemma = fiveLemmaThm{family.Add(registry.ProofEntry{
	Name: "FiveLemma",
	Key:  "prop_c30179ce051f4507",
	Reading: "Both rows run left to right and are exact at their three interior terms. All " +
		"ten vector host types may differ; squares need commute only on their source carriers. " +
		"The outside vertical maps need only surjectivity on the left and injectivity on the right.",
	Deps: []registry.EntryLike{
		ModuleHomomorphismDef,
		ModuleIsomorphismDef,
		ExactAtDef,
		HomZero,
		HomAdd,
		HomNeg,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M₁:module_ops(A, B). " +
			"∀M₂:module_ops(A, C). " +
			"∀M₃:module_ops(A, D). " +
			"∀M₄:module_ops(A, E). " +
			"∀M₅:module_ops(A, F). " +
			"∀N₁:module_ops(A, G). " +
			"∀N₂:module_ops(A, H). " +
			"∀N₃:module_ops(A, I). " +
			"∀N₄:module_ops(A, U). " +
			"∀N₅:module_ops(A, Z). " +
			"∀a₁:(B → C). " +
			"∀b₁:(G → H). " +
			"∀a₂:(C → D). " +
			"∀b₂:(H → I). " +
			"∀a₃:(D → E). " +
			"∀b₃:(I → U). " +
			"∀a₄:(E → F). " +
			"∀b₄:(U → Z). " +
			"∀u₁:(B → G). " +
			"∀u₂:(C → H). " +
			"∀u₃:(D → I). " +
			"∀u₄:(E → U). " +
			"∀u₅:(F → Z).",
		Hypotheses: []string{
			"module_homomorphism(R, M₁, M₂, a₁)",
			"module_homomorphism(R, N₁, N₂, b₁)",
			"module_homomorphism(R, M₂, M₃, a₂)",
			"module_homomorphism(R, N₂, N₃, b₂)",
			"module_homomorphism(R, M₃, M₄, a₃)",
			"module_homomorphism(R, N₃, N₄, b₃)",
			"module_homomorphism(R, M₄, M₅, a₄)",
			"module_homomorphism(R, N₄, N₅, b₄)",
			"module_homomorphism(R, M₁, N₁, u₁)",
			"module_homomorphism(R, M₂, N₂, u₂)",
			"module_homomorphism(R, M₃, N₃, u₃)",
			"module_homomorphism(R, M₄, N₄, u₄)",
			"module_homomorphism(R, M₅, N₅, u₅)",
			"exact_at(M₃.zero, M₁.carrier, M₂.carrier, a₁, a₂)",
			"exact_at(M₄.zero, M₂.carrier, M₃.carrier, a₂, a₃)",
			"exact_at(M₅.zero, M₃.carrier, M₄.carrier, a₃, a₄)",
			"exact_at(N₃.zero, N₁.carrier, N₂.carrier, b₁, b₂)",
			"exact_at(N₄.zero, N₂.carrier, N₃.carrier, b₂, b₃)",
			"exact_at(N₅.zero, N₃.carrier, N₄.carrier, b₃, b₄)",
			"∀x:B. x ∈ M₁.carrier ⇒ u₂(a₁(x)) = b₁(u₁(x))",
			"∀x:C. x ∈ M₂.carrier ⇒ u₃(a₂(x)) = b₂(u₂(x))",
			"∀x:D. x ∈ M₃.carrier ⇒ u₄(a₃(x)) = b₃(u₃(x))",
			"∀x:E. x ∈ M₄.carrier ⇒ u₅(a₄(x)) = b₄(u₄(x))",
			"image(u₁, M₁.carrier) = N₁.carrier",
			"module_isomorphism(R, M₂, N₂, u₂)",
			"module_isomorphism(R, M₄, N₄, u₄)",
			"injective_on(M₅.carrier, u₅)",
		},
		Conclusion: "module_isomorphism(R, M₃, N₃, u₃)",
	},
		"For injectivity, chase a vector killed by the middle map leftward using exactness, then "+
			"correct its lift with the surjective first vertical map. For surjectivity, lift the rightward "+
			"image with the fourth isomorphism, use injectivity at the fifth term to lift back through the "+
			"upper middle term, and correct the remaining difference with the second isomorphism."),
})}
