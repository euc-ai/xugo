// component_classes.go — connected components as the equivalence
// classes of points in the underlying space.

package connected

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ComponentEquivalence — belonging to a point's connected component is
// an equivalence on the underlying space: every point belongs to its
// own component, and related points have the same component.
var ComponentEquivalence = componentEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "ComponentEquivalence",
	Key:  "prop_7e7311bcf77e81d1",
	Build: family.Instance(equivalence.EquivalenceOn,
		"∀T:set(set(A)). equivalence_on(⋃T, λx:A. λy:A. y ∈ connected_component(T, x))",
		Case(
			"every point of the space belongs to its own component",
			By(ComponentSelfIff)),
		Case(
			"related points have the same component, which contains the first point",
			Derive(func(a *Argument) {
				a.FixAs[A]("x")
				a.FixAs[A]("y")
				inside := a.Assume()
				related := a.Assume()
				same := a.Have(
					"the two components agree",
					"connected_component(T, y) = connected_component(T, x)",
					By(related, ComponentEq))
				a.Show(
					"self-membership gives the reverse relation",
					same.Rw(),
					By(inside, ComponentSelfIff))
			})),
		Case(
			"a point of the second component belongs to the equal first component",
			Derive(func(a *Argument) {
				a.FixAs[A]("x")
				a.FixAs[A]("y")
				a.FixAs[A]("z")
				a.Assume()
				links := a.Assume()
				same := a.Have(
					"the first link identifies the two components",
					"connected_component(T, y) = connected_component(T, x)",
					By(links, ComponentEq))
				a.Show(
					"the second link belongs to their common component",
					same.RwRev(),
					By(links))
			})),
	),
})}

// ComponentClass — the component of a point in the space is its class
// under component membership restricted to the space: every component
// already lies in that space.
var ComponentClass = componentClassThm{family.Add(registry.ProofEntry{
	Name: "ComponentClass",
	Key:  "prop_793b0c9b095e73f4",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "connected_component(T, x) = " +
			"equivalence_class(relation_on(⋃T, λu:A. λv:A. v ∈ connected_component(T, u)), x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A], inside Fact) {
			space := a.TermAs[Set[A]]("⋃T")
			relation := a.TermAs[Fun2[A, A, Bool]]("λu:A. λv:A. v ∈ connected_component(T, u)")
			a.Show(
				"restriction to the space preserves every point of the component",
				BySets(
					inside,
					equivalence.InClassOn.Inst[A]().At(space, relation, x),
					ComponentSubsetSpace.At(T, x)))
		}),
})}

// ComponentsQuotient — the components indexed by the space form its
// quotient under component membership: the two class maps agree at
// every point of their common domain.
var ComponentsQuotient = componentsQuotientThm{family.Add(registry.ProofEntry{
	Name: "ComponentsQuotient",
	Key:  "prop_fee3b22ef8979f93",
	Build: family.Theorem("∀T:set(set(A)). "+
		"    image(λx:A. connected_component(T, x), ⋃T) = "+
		"    quotient_on(⋃T, λx:A. λy:A. y ∈ connected_component(T, x))",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Show(
				"equal class maps have equal images of the space",
				Simp(Fwd(equivalence.QuotientOnDef)),
				By(At(ComponentClass, T), set_image.ImageCongruence))
		}),
})}
