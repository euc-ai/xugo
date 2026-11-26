// subsets.go — sums over the subsets of a set, the points of a cube, a
// subset being the coordinates that are set: the reindexing that reads a set
// of pairs with one second coordinate as a subset of the first coordinates
// (SubsetsSumCrossSingleton).

package real_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// SubsetsSumCrossSingleton — a sum over the sets of pairs of J × {b} is
// the sum over the subsets of J, each set Z of pairs read through its
// slice at b: taking the slice and crossing with {b} are mutually inverse
// (monoidal's Reindex).
var SubsetsSumCrossSingleton = subsetsSumCrossSingletonThm{family.Add(registry.ProofEntry{
	Name: "SubsetsSumCrossSingleton",
	Key:  "prop_c1736195cee09a45",
	Build: family.Theorem(
		"∀J:set(A). ∀b:B. ∀f:(set(A) → real). "+
			"    Σ_{Z∈{Z:set(prod(A, B)) | Z ⊆ set_cross(J, {b})}} f({a:A | (a, b) ∈ Z}) = "+
			"    Σ_{X∈{X:set(A) | X ⊆ J}} f(X)",
		func(a *Argument, J *Expr[Set[A]], b *Expr[B], f *Arrow[Set[A], Real]) {
			point := a.TermAs[Set[B]]("{b}")
			back := a.Have(
				"a subset X of J, crossed with {b}, lies in J × {b} and has X as its slice",
				"∀X:set(A). X ⊆ J ⇒ set_cross(X, {b}) ⊆ set_cross(J, {b}) ∧ {a:A | (a, b) ∈ set_cross(X, {b})} = X",
				Derive(func(d *Argument) {
					X := d.FixAs[Set[A]]()
					inJ := d.Assume()
					d.Do(SplitConj(
						Case(
							"the cross grows with its first factor",
							By(inJ, set_order.SubsetRefl.At(point), set_product.CrossSubsetIff.At(X, J, point, point))),
						Case(
							"a pair (a, b) is in the cross of X with {b} exactly when a is in X",
							Simp(Fwd(set_product.InCross)),
							BySets())))
				}))
			forth := a.Have(
				"a set Z of pairs of J × {b} has its slice in J and is the cross of that slice with {b}",
				Statement{
					Binders:    "∀Z:set(prod(A, B)).",
					Hypotheses: []string{"Z ⊆ set_cross(J, {b})"},
					Conclusion: "{a:A | (a, b) ∈ Z} ⊆ J ∧ set_cross({a:A | (a, b) ∈ Z}, {b}) = Z",
				},
				Derive(func(d *Argument) {
					d.FixAs[Set[Prod[A, B]]]()
					atB := d.Assume()
					d.Do(SplitConj(
						Case(
							"a pair of Z has its first component in J",
							BySets(atB, set_product.InCross)),
						Case(
							"and a pair of Z is its first component with b",
							BySets(atB, set_product.InCrossProjections, pairs.PairEta))))
				}))
			a.Show(
				"so the slice at b matches the sets of pairs of J × {b} with the subsets of J",
				Simp(Fwd(RealSumDef)),
				By(
					back,
					forth,
					real_ring.MonoidalAdd,
					monoidal.Reindex.At(
						a.TermAs[Op[Real]]("real_add"),
						a.TermAs[Set[Set[Prod[A, B]]]]("{Z:set(prod(A, B)) | Z ⊆ set_cross(J, {b})}"),
						a.TermAs[Set[Set[A]]]("{X:set(A) | X ⊆ J}"),
						a.TermAs[Fun[Set[Prod[A, B]], Real]]("λZ:set(prod(A, B)). f({a:A | (a, b) ∈ Z})"),
						f,
						a.TermAs[Fun[Set[Prod[A, B]], Set[A]]]("λZ:set(prod(A, B)). {a:A | (a, b) ∈ Z}"),
						a.TermAs[Fun[Set[A], Set[Prod[A, B]]]]("λX:set(A). set_cross(X, {b})"))))
		}),
})}
