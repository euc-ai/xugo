// component_classes.go — path components as equivalence classes of
// points in the underlying space.

package path_connected

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// PathComponentEquivalence — belonging to a point's path component is
// an equivalence on the underlying space: constant paths, reversal,
// and concatenation give its three laws.
var PathComponentEquivalence = pathComponentEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "PathComponentEquivalence",
	Key:  "prop_b42509dc0781580e",
	Build: family.Instance(equivalence.EquivalenceOn,
		"∀T:set(set(A)). equivalence_on(⋃T, λx:A. λy:A. y ∈ path_component(T, x))",
		Case(
			"every point of the space belongs to its own path component",
			By(PathComponentSelfIff)),
		Case(
			"reversing a path reverses component membership",
			By(PathComponentSym)),
		Case(
			"joining paths makes component membership transitive",
			By(PathComponentTrans)),
	),
})}

// PathComponentClass — the path component of a point in the space is
// its class under path-component membership restricted to the space:
// every path component already lies in that space.
var PathComponentClass = pathComponentClassThm{family.Add(registry.ProofEntry{
	Name: "PathComponentClass",
	Key:  "prop_23118339a0c340ad",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "path_component(T, x) = " +
			"equivalence_class(relation_on(⋃T, λu:A. λv:A. v ∈ path_component(T, u)), x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A], inside Fact) {
			space := a.TermAs[Set[A]]("⋃T")
			relation := a.TermAs[Fun2[A, A, Bool]]("λu:A. λv:A. v ∈ path_component(T, u)")
			a.Show(
				"restriction to the space preserves every point of the path component",
				BySets(
					inside,
					equivalence.InClassOn.Inst[A]().At(space, relation, x),
					PathComponentSubsetSpace.At(T, x)))
		}),
})}

// PathComponentsQuotient — the path components indexed by the space
// form its quotient under path-component membership: the two class
// maps agree at every point of their common domain.
var PathComponentsQuotient = pathComponentsQuotientThm{family.Add(registry.ProofEntry{
	Name: "PathComponentsQuotient",
	Key:  "prop_159928f0941ad92b",
	Build: family.Theorem("∀T:set(set(A)). "+
		"    image(λx:A. path_component(T, x), ⋃T) = quotient_on(⋃T, λx:A. λy:A. y ∈ path_component(T, x))",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Show(
				"equal class maps have equal images of the space",
				Simp(Fwd(equivalence.QuotientOnDef)),
				By(At(PathComponentClass, T), set_image.ImageCongruence))
		}),
})}

// PathComponentsCover — the path components cover the underlying
// space because they are the classes of an equivalence on that space.
var PathComponentsCover = pathComponentsCoverThm{family.Add(registry.ProofEntry{
	Name: "PathComponentsCover",
	Key:  "prop_2d210d876365e21c",
	Build: family.Theorem("∀T:set(set(A)). ⋃image(λx:A. path_component(T, x), ⋃T) = ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Do(Simp(Fwd(PathComponentsQuotient)))
			equiv := a.Have(
				"path-component membership is an equivalence on the space",
				"equivalence_on(⋃T, λx:A. λy:A. y ∈ path_component(T, x))",
				Cite(PathComponentEquivalence))
			a.Show(
				"the classes of the equivalence cover its carrier",
				Cite(equivalence.QuotientOnCovers.Read(equiv)))
		}),
})}
