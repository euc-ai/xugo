// preorder_category.go — the category of a preorder on a set: the
// points of the set for objects, and one morphism from x to y exactly
// when x is below y, assembled from hom data in which each hom set
// holds at most the one datum ⊤. Two morphisms with the same ends are
// equal.

package preorder_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/registry"
)

// PreorderCategoryDef — `preorder_category(R, c)`: the objects of c,
// with the hom set from x to y holding ⊤ exactly when R(x, y).
var PreorderCategoryDef = preorderCategoryDefThm{family.Define(registry.DefEntry{
	Name:  "PreorderCategoryDef",
	Key:   "prop_be51e4f337374cb1",
	Const: "preorder_category",
	Type:  "(A → A → bool) → set(A) → category_ops(A, morphism_triple(A, bool))",
	Equations: []string{
		"∀R:(A → A → bool). ∀c:set(A). " +
			"    preorder_category(R, c) = " +
			"    category_from_hom(c, " +
			"        λx:A. λy:A. {u:bool | u ∧ R(x, y)}, " +
			"        λx:A. ⊤, " +
			"        λx:A. λy:A. λz:A. λv:bool. λu:bool. ⊤)",
	},
})}

// PreorderCategory — a preorder gives a category: reflexivity supplies
// identities, transitivity supplies composites, and every hom datum is ⊤.
var PreorderCategory = preorderCategoryThm{family.Add(registry.ProofEntry{
	Name: "PreorderCategory",
	Key:  "prop_4d8e57c0ee7f46f8",
	Build: family.Theorem(Statement{
		Binders: "∀R:(A → A → bool). ∀c:set(A).",
		Hypotheses: []string{
			"preorder(R)",
		},
		Conclusion: "category(preorder_category(R, c))",
	},
		func(a *Argument, R *Arrow2[A, A, Bool], c *Expr[Set[A]], preorder Fact) {
			a.Do(Simp(Fwd(PreorderCategoryDef)))
			homLaws := a.Have(
				"the Boolean hom data have identities, composition, and only the datum ⊤",
				"(∀x:A. x ∈ c ⇒ ⊤ ∈ {u:bool | u ∧ R(x, x)}) ∧ "+
					"(∀x y z:A. ∀u v:bool. "+
					"    x ∈ c ∧ y ∈ c ∧ z ∈ c ∧ u ∈ {p:bool | p ∧ R(x, y)} ∧ v ∈ {p:bool | p ∧ R(y, z)} ⇒ "+
					"    ⊤ ∈ {p:bool | p ∧ R(x, z)}) ∧ "+
					"(∀x y:A. ∀u:bool. x ∈ c ∧ y ∈ c ∧ u ∈ {p:bool | p ∧ R(x, y)} ⇒ ⊤ = u)",
				SplitConjAll(
					Case(
						"reflexivity places the identity in each endomorphism set",
						BySets(order.Reflexive.Read(preorder))),
					Case(
						"transitivity places a composite in its hom set",
						BySets(order.Transitive.Read(preorder))),
					Case(
						"every hom datum is ⊤",
						BySets()),
				))
			H := a.TermAs[Fun3[A, A, Bool, Bool]]("λx:A. λy:A. {u:bool | u ∧ R(x, y)}")
			e := a.TermAs[Fun[A, Bool]]("λx:A. ⊤")
			compose := a.TermAs[Fun[A, Fun[A, Fun3[A, Bool, Bool, Bool]]]](
				"λx:A. λy:A. λz:A. λv:bool. λu:bool. ⊤")
			a.Show(
				"the hom data assemble into the preorder category",
				By(homLaws, category.CategoryFromHom.At(c, H, e, compose)))
		}),
})}

// PreorderCategoryThin — two morphisms of a preorder category with the
// same ends are equal.
var PreorderCategoryThin = preorderCategoryThinThm{family.Add(registry.ProofEntry{
	Name: "PreorderCategoryThin",
	Key:  "prop_7347bc2d6264c230",
	Deps: []registry.EntryLike{
		PreorderCategoryDef,
		category.CategoryFromHomDef,
		category.MorphismTripleData.Ext,
	},
	Build: family.Card(Statement{
		Binders: "∀R:(A → A → bool). ∀c:set(A). ∀t t':morphism_triple(A, bool).",
		Hypotheses: []string{
			"t ∈ category_morphisms(preorder_category(R, c))",
			"t' ∈ category_morphisms(preorder_category(R, c))",
			"t.source = t'.source",
			"t.target = t'.target",
		},
		Conclusion: "t = t'",
	},
		"record extensionality: the frames agree, and both "+
			"data are ⊤, the only member of a nonempty hom set"),
})}
