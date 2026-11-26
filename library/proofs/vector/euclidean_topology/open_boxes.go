// Coordinatewise open boxes form a basis and admit finite compact-cover refinements.

package euclidean_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

var OpenBoxDef = openBoxDefThm{family.Define(registry.DefEntry{
	Name:  "OpenBoxDef",
	Key:   "prop_5084f33cc0ed978a",
	Const: "euclidean_open_box",
	Type:  "num → (num → real) → (num → real) → set(num → real)",
	Dim:   "n",
	Reading: "Only the first n coordinates of the bounds are read; " +
		"their tails are arbitrary. Points are zero-padded n-vectors. If " +
		"n=0 every box is the singleton zero vector, whatever its bounds.",
	Equations: []string{
		"∀n:num. ∀a b:(num → real). " +
			"    euclidean_open_box⟨n⟩(a, b) = " +
			"    {x:num → real | vec⟨n⟩(x) ∧ (∀i:num. i < n ⇒ a(i) < x(i) ∧ x(i) < b(i))}",
	},
})}

var OpenBoxOpen = openBoxOpenThm{family.Add(registry.ProofEntry{
	Name: "OpenBoxOpen",
	Key:  "prop_9933dcb837474029",
	Deps: []registry.EntryLike{OpenBoxDef, CoordinateContinuous, EuclideanTopology},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀a b:(num → real).",
		Hypotheses: []string{},
		Conclusion: "euclidean_open_box⟨n⟩(a, b) ∈ euclidean_topology(n)",
	}, "The box is the Euclidean carrier intersected with finitely many inverse images of "+
		"open real intervals under coordinate maps. These inverse images are open, as is their "+
		"finite intersection; the empty intersection at n=0 is the whole zero-dimensional carrier."),
})}

var OpenBoxIntersection = openBoxIntersectionThm{family.Add(registry.ProofEntry{
	Name: "OpenBoxIntersection",
	Key:  "prop_989e40bb190effd8",
	Deps: []registry.EntryLike{OpenBoxDef, real_sup_inf.RealMaxDef, real_sup_inf.RealMinDef},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀a b c d:(num → real).",
		Hypotheses: []string{},
		Conclusion: "euclidean_open_box⟨n⟩(a, b) ∩ euclidean_open_box⟨n⟩(c, d) = " +
			"euclidean_open_box⟨n⟩((λi:num. max(a(i), c(i))), (λi:num. min(b(i), d(i))))",
	}, "Membership in both boxes means satisfying both lower and both upper bounds in each "+
		"active coordinate. Their maximum lower bound and minimum upper bound state exactly these "+
		"inequalities. The formula includes disjoint boxes without a nonemptiness assumption."),
})}

// OpenBoxBasis — every open set of ℝⁿ contains an open coordinate box
// about each of its points: a ball of radius r about the point lies in the
// set, and the box of half-width h = r/(n + 1) about the point lies in the
// ball, since a vector whose n coordinates are at most h in size has norm
// at most n·h < r.
var OpenBoxBasis = openBoxBasisThm{family.Add(registry.ProofEntry{
	Name: "OpenBoxBasis",
	Key:  "prop_22c1263fee5c625d",
	Reading: "The bounds may be chosen with zero tails, but this is not imposed on the interface. " +
		"Only containment of the open box is claimed; its closure is not part of this statement.",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀U:set(num → real). ∀x:(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)", "x ∈ U"},
		Conclusion: "∃a b:(num → real). x ∈ euclidean_open_box⟨n⟩(a, b) ∧ euclidean_open_box⟨n⟩(a, b) ⊆ U",
	},
		func(
			arg *Argument,
			n *Expr[Nat],
			U *Expr[Set[Fun[Nat, Real]]],
			x *Vec[Real, DimN],
			open, member Fact,
		) {
			vector := arg.Have(
				"x, a point of the open set U, is an n-vector",
				"vec⟨n⟩(x)",
				By(open, member, OpenIff.At(n, U)))
			_, radius := arg.Obtain(
				"some ball about x lies in U",
				"∃r:real. &0 < r ∧ ∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < r ⇒ y ∈ U",
				By(open, member, OpenIff.At(n, U)))
			ball := arg.Conjuncts(
				radius,
				"the radius r is positive",
				"every n-vector within r of x lies in U")
			h, hDef := arg.LetAs[Real]("h", "r / (&n + &1)")
			a, aDef := arg.LetAs[Fun[Nat, Real]]("a", "λi:num. x(i) - h")
			b, bDef := arg.LetAs[Fun[Nat, Real]]("b", "λi:num. x(i) + h")
			centre := arg.Have(
				"x lies in the box: each coordinate x(i) lies strictly between x(i) - h and x(i) + h",
				"x ∈ euclidean_open_box⟨n⟩(a, b)",
				Unfold(OpenBoxDef),
				ByArith(aDef, bDef, hDef, ball[0], real_order_ring.NumNonneg.At(n), vector))
			inside := arg.Have(
				"the box lies in the ball of radius r about x, hence in U",
				"euclidean_open_box⟨n⟩(a, b) ⊆ U",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(c *Argument) {
					w := c.VecFixAs[Real, DimN]("w")
					box := c.Conjuncts(
						c.Unfolded(c.Assume(), OpenBoxDef),
						"w is an n-vector",
						"each coordinate of w below n lies between those of a and b")
					// The arithmetic close reads only ground facts, so VecSubDef is cited at
					// its points and its implicit subtraction is spelled.
					sub := c.TermAs[Op[Real]]("real_sub")
					coordinates := c.Have(
						"each coordinate of x - w below n is at most h in size",
						"∀i:num. i < n ⇒ |(x - w)(i)| ≤ h",
						c.ForEach(func(i *Expr[Nat]) Action {
							return ByArith(box[1].At(i), aDef, bDef, vec_space.VecSubDef.At(sub, x, w, i))
						}))
					near := c.Have(
						"by the coordinate norm bound x - w has norm at most n·h, "+
							"which is below r as h = r/(n + 1): w lies within r of x",
						"dist⟨n⟩(x, w) < r",
						ByArith(
							coordinates,
							euclidean.CoordinateNormBound.At(c.VecAs[Real, DimN]("x - w"), h),
							hDef,
							ball[0],
							euclidean.VecDistDef.At(x, w),
							real_order_ring.NumNonneg.At(n)))
					c.Show(
						"so w lies in U",
						By(ball[1].At(w), box[0], near))
				}))
			arg.Take(a)
			arg.Take(b)
			arg.Show(
				"the box about x of half-width h is the box asked for",
				By(centre, inside))
		}),
})}

var CompactOpenBoxCover = compactOpenBoxCoverThm{family.Add(registry.ProofEntry{
	Name: "CompactOpenBoxCover",
	Key:  "prop_416a75b8a6ab1e8f",
	Reading: "This provides a finite union surrounding a compact embedded " +
		"image without asserting that the boxes intersect the image in a good cover.",
	Deps: []registry.EntryLike{OpenBoxBasis, OpenBoxOpen, compact.CompactInDef},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀K U:set(num → real).",
		Hypotheses: []string{"compact_in(euclidean_topology(n), K)", "U ∈ euclidean_topology(n)", "K ⊆ U"},
		Conclusion: "∃C:set(set(num → real)). " +
			"    finite(C) ∧ " +
			"    K ⊆ ⋃C ∧ " +
			"    ⋃C ⊆ U ∧ " +
			"    (∀B:set(num → real). B ∈ C ⇒ ∃a b:(num → real). B = euclidean_open_box⟨n⟩(a, b))",
	},
		"The boxes contained in U form an open cover of K by OpenBoxBasis. Compactness supplies a "+
			"finite subcover; every selected box lies in U. If K is empty the empty family suffices."),
})}
