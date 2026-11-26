// properties.go — what a product inherits from its factors. Two Hausdorff
// spaces have a Hausdorff product, and a space is Hausdorff exactly when
// its diagonal is closed in its square; the graph of a continuous map into
// a Hausdorff space is closed. The tube lemma — an open set around a slice
// {x} × k with k compact holds a whole tube u × k — is what compactness
// passes through: the product of two compact sets is compact, so the
// product of two locally compact spaces is locally compact, and the
// projection along a compact factor is a closed map. Two spaces with
// countable bases have a product with one.

package product_topology

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Hausdorff products, diagonals and graphs
// ---------------------------------------------------------------------------

// HausdorffProduct — the product of two Hausdorff spaces is Hausdorff. Two
// distinct pairs of points differ in a coordinate, a pair being made of its
// two coordinates. Disjoint open sets about the two differing coordinates,
// each against an open set about the other coordinate of its pair, are
// disjoint open rectangles about the two pairs. No axiom enters.
var HausdorffProduct = hausdorffProductThm{family.Add(registry.ProofEntry{
	Name: "HausdorffProduct",
	Key:  "prop_e30b850a00a5c830",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"hausdorff(T)",
			"hausdorff(S)",
		},
		Conclusion: "hausdorff(product_topology(T, S))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], first, second Fact) {
			a.Do(Simp(Fwd(topological_space.HausdorffDef)), Simp(Fwd(ProductSpace)))
			p := a.FixAs[Prod[A, B]]("p")
			q := a.FixAs[Prod[A, B]]("q")
			points := a.Conjuncts(
				a.Assume(),
				"p is a pair of points",
				"so is q",
				"p and q are distinct")
			coordinates := a.Have(
				"the coordinates of p and q are points of the two spaces",
				"fst(p) ∈ ⋃T ∧ snd(p) ∈ ⋃S ∧ fst(q) ∈ ⋃T ∧ snd(q) ∈ ⋃S",
				BySets(points[0], points[1], set_product.InCrossProjections))
			a.Cases(a.Term("fst(p) = fst(q)"))
			a.Otherwise(
				"p and q differ in their first coordinates, which lie in disjoint open sets of T",
				func(b *Argument, differ Fact) {
					_, _, apart := b.Obtain2As[Set[A], Set[A]](
						"T is Hausdorff, so disjoint open sets u₁ and u₂ hold the first coordinates",
						"∃u₁ u₂:set(A). u₁ ∈ T ∧ u₂ ∈ T ∧ fst(p) ∈ u₁ ∧ fst(q) ∈ u₂ ∧ u₁ ∩ u₂ = ∅",
						By(first, differ, coordinates, topological_space.HausdorffDef))
					_, _, about := b.Obtain2As[Set[B], Set[B]](
						"open sets t₁ and t₂ of S hold the second coordinates",
						"∃t₁ t₂:set(B). t₁ ∈ S ∧ t₂ ∈ S ∧ snd(p) ∈ t₁ ∧ snd(q) ∈ t₂",
						BySets(coordinates))
					sides := b.Conjuncts(
						apart,
						"u₁ is open",
						"u₂ is open",
						"fst(p) lies in u₁",
						"fst(q) lies in u₂",
						"u₁ and u₂ are disjoint")
					others := b.Conjuncts(
						about,
						"t₁ is open",
						"t₂ is open",
						"snd(p) lies in t₁",
						"snd(q) lies in t₂")
					b.Take(b.TermAs[Set[Prod[A, B]]]("set_cross(u₁, t₁)"))
					b.Take(b.TermAs[Set[Prod[A, B]]]("set_cross(u₂, t₂)"))
					b.Do(SplitConjAll(
						Case(
							"the rectangle u₁ × t₁ is open",
							By(sides[0], others[0], RectangleOpen)),
						Case(
							"so is u₂ × t₂",
							By(sides[1], others[1], RectangleOpen)),
						Case(
							"p lies in u₁ × t₁",
							By(sides[2], others[2], set_product.InCrossProjections)),
						Case(
							"q lies in u₂ × t₂",
							By(sides[3], others[3], set_product.InCrossProjections)),
						Case(
							"the two rectangles are disjoint, their first sides being disjoint",
							BySets(sides[4], set_product.InCrossProjections)),
					))
				})
			a.When(
				"p and q agree in their first coordinates, so differ "+
					"in their second, which lie in disjoint open sets of S",
				func(b *Argument, same Fact) {
					differ := b.Have(
						"the second coordinates of p and q differ, a pair being made of its coordinates",
						"snd(p) ≠ snd(q)",
						By(points[2], same, pairs.PairEta.At(p), pairs.PairEta.At(q)))
					_, _, apart := b.Obtain2As[Set[B], Set[B]](
						"S is Hausdorff, so disjoint open sets v₁ and v₂ hold the second coordinates",
						"∃v₁ v₂:set(B). v₁ ∈ S ∧ v₂ ∈ S ∧ snd(p) ∈ v₁ ∧ snd(q) ∈ v₂ ∧ v₁ ∩ v₂ = ∅",
						By(second, differ, coordinates, topological_space.HausdorffDef))
					_, _, about := b.Obtain2As[Set[A], Set[A]](
						"open sets s₁ and s₂ of T hold the first coordinates",
						"∃s₁ s₂:set(A). s₁ ∈ T ∧ s₂ ∈ T ∧ fst(p) ∈ s₁ ∧ fst(q) ∈ s₂",
						BySets(coordinates))
					sides := b.Conjuncts(
						apart,
						"v₁ is open",
						"v₂ is open",
						"snd(p) lies in v₁",
						"snd(q) lies in v₂",
						"v₁ and v₂ are disjoint")
					others := b.Conjuncts(
						about,
						"s₁ is open",
						"s₂ is open",
						"fst(p) lies in s₁",
						"fst(q) lies in s₂")
					b.Take(b.TermAs[Set[Prod[A, B]]]("set_cross(s₁, v₁)"))
					b.Take(b.TermAs[Set[Prod[A, B]]]("set_cross(s₂, v₂)"))
					b.Do(SplitConjAll(
						Case(
							"the rectangle s₁ × v₁ is open",
							By(others[0], sides[0], RectangleOpen)),
						Case(
							"so is s₂ × v₂",
							By(others[1], sides[1], RectangleOpen)),
						Case(
							"p lies in s₁ × v₁",
							By(others[2], sides[2], set_product.InCrossProjections)),
						Case(
							"q lies in s₂ × v₂",
							By(others[3], sides[3], set_product.InCrossProjections)),
						Case(
							"the two rectangles are disjoint, their second sides being disjoint",
							BySets(sides[4], set_product.InCrossProjections)),
					))
				})
		}),
})}

// HausdorffIffDiagonalClosed — a space is Hausdorff exactly when its
// diagonal is closed in its square. A pair lies on the diagonal when its
// coordinates agree and lie in the space, so the diagonal lies in the
// square. An open rectangle u × v misses the diagonal exactly when u and v
// are disjoint, a common point z giving the diagonal point (z, z); so the
// complement of the diagonal is open, each of its points in an open
// rectangle inside it, exactly when two distinct points lie in disjoint
// open sets. No axiom enters.
var HausdorffIffDiagonalClosed = hausdorffIffDiagonalClosedThm{family.Add(registry.ProofEntry{
	Name: "HausdorffIffDiagonalClosed",
	Key:  "prop_ecce3d9aeb6da341",
	Build: family.Theorem("∀T:set(set(A)). "+
		"    hausdorff(T) ⇔ closed_in(product_topology(T, T), set_diagonal(⋃T))",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			space := a.TermAs[Set[A]]("⋃T")
			onDiagonal := At(set_product.InDiagonalProjections, space)
			a.Do(Simp(Fwd(topological_space.ClosedInDef), Fwd(ProductSpace)))
			a.Iff()
			a.Forward(
				"disjoint open sets about the coordinates of a point off "+
					"the diagonal are the sides of an open rectangle off it",
				func(b *Argument, hausdorff Fact) {
					separated := b.Have(
						"each point of the square off the diagonal lies in an open rectangle off the diagonal",
						Statement{
							Binders:    "∀p:prod(A, A).",
							Hypotheses: []string{"p ∈ set_cross(⋃T, ⋃T) ∖ set_diagonal(⋃T)"},
							Conclusion: "∃u v:set(A). " +
								"    u ∈ T ∧ v ∈ T ∧ p ∈ set_cross(u, v) ∧ set_cross(u, v) ⊆ set_cross(⋃T, ⋃T) ∖ set_diagonal(⋃T)",
						},
						Derive(func(c *Argument) {
							p := c.FixAs[Prod[A, A]]("p")
							off := c.Assume()
							distinct := c.Have(
								"the coordinates of p are distinct points of the space, p lying in the square off the diagonal",
								"fst(p) ∈ ⋃T ∧ snd(p) ∈ ⋃T ∧ fst(p) ≠ snd(p)",
								BySets(onDiagonal, off, set_product.InCrossProjections.At(space, space, p)))
							u, v, apart := c.Obtain2As[Set[A], Set[A]](
								"T is Hausdorff, so disjoint open sets u and v hold them",
								"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ fst(p) ∈ u ∧ snd(p) ∈ v ∧ u ∩ v = ∅",
								By(hausdorff, distinct, topological_space.HausdorffDef))
							offBox := c.Have(
								"a point q of u × v has its coordinates in the disjoint "+
									"u and v, so it lies in the square off the diagonal",
								"∀q:prod(A, A). q ∈ set_cross(u, v) ⇒ q ∈ set_cross(⋃T, ⋃T) ∖ set_diagonal(⋃T)",
								Derive(func(e *Argument) {
									q := e.FixAs[Prod[A, A]]("q")
									inBox := e.Assume()
									e.Show(
										"the coordinates of q lie in the open u and v, and differ as u and v are disjoint",
										BySets(
											onDiagonal,
											inBox,
											apart,
											set_product.InCrossProjections.At(u, v, q),
											set_product.InCrossProjections.At(space, space, q)))
								}))
							c.Take(u)
							c.Take(v)
							c.Show(
								"so the open rectangle u × v holds p and lies off the diagonal",
								BySets(offBox, apart, set_product.InCrossProjections.At(u, v, p)))
						}))
					b.Do(SplitConj(
						Case(
							"the complement of the diagonal is open, each of its points lying in an open rectangle inside it",
							By(separated, ProductOpenIff)),
						Case(
							"the diagonal lies in the square",
							By(set_product.DiagonalSubsetCross.At(space))),
					))
				})
			a.Backward(
				"an open rectangle about a pair of distinct points "+
					"inside the complement of the diagonal has disjoint sides",
				func(b *Argument, closed Fact) {
					b.Do(Simp(Fwd(topological_space.HausdorffDef)))
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					distinct := b.Assume()
					offDiagonal := b.Have(
						"(x, y) lies in the square off the diagonal, its coordinates being distinct points of the space",
						"(x, y) ∈ set_cross(⋃T, ⋃T) ∖ set_diagonal(⋃T)",
						BySets(
							distinct,
							set_product.InDiagonal.At(space, x, y),
							set_product.InCross.At(space, space, x, y)))
					u, v, rectangle := b.Obtain2As[Set[A], Set[A]](
						"the complement of the diagonal is open, so an open rectangle u × v about (x, y) lies inside it",
						"∃u v:set(A). "+
							"    u ∈ T ∧ "+
							"    v ∈ T ∧ "+
							"    (x, y) ∈ set_cross(u, v) ∧ "+
							"    set_cross(u, v) ⊆ set_cross(⋃T, ⋃T) ∖ set_diagonal(⋃T)",
						By(offDiagonal, closed, ProductOpenIff))
					apart := b.Have(
						"u and v have no common point z, else the diagonal "+
							"point (z, z) would lie in the rectangle off the diagonal",
						"∀z:A. z ∈ u ⇒ z ∉ v",
						Derive(func(c *Argument) {
							z := c.FixAs[A]("z")
							c.Show(
								"once z lies in the open u, (z, z) lies on the diagonal, so outside u × v, and z lies outside v",
								BySets(set_product.InDiagonal.At(space, z, z), rectangle, set_product.InCross.At(u, v, z, z)))
						}))
					b.Take(u)
					b.Take(v)
					b.Show(
						"u and v are disjoint open sets about x and y",
						BySets(apart, rectangle, set_product.InCross.At(u, v, x, y)))
				})
		}),
})}

// ClosedGraph — the graph of a continuous map into a Hausdorff space is
// closed. It is the preimage of the diagonal of S under the map g sending a
// pair p to (f(fst(p)), snd(p)): a pair of the product goes onto the
// diagonal exactly when its second coordinate is the value of f at its
// first, that value being a point of S since f carries ⋃T into ⋃S. The map
// g is continuous from the product to S × S, f paired with the identity;
// the diagonal of the Hausdorff S is closed in S × S; and the preimage of a
// closed set under a continuous map is closed. No axiom enters.
var ClosedGraph = closedGraphThm{family.Add(registry.ProofEntry{
	Name: "ClosedGraph",
	Key:  "prop_cee11db1b754c6f1",
	Build: continuous.ContinuousMap.Law(Statement{
		Hypotheses: []string{
			"hausdorff(S)",
		},
		Conclusion: "closed_in(product_topology(T, S), {(x, f(x)) | x:A | x ∈ ⋃T})",
		Abbrev: Abbrev{
			{Name: "graph", Text: "{(x, f(x)) | x:A | x ∈ ⋃T}"},
		},
	},
		func(a *Argument, fContinuous continuous.ContinuousMapFact[on.T, on.S], hausdorff Fact) {
			T := a.TermAs[Set[Set[A]]]("T")
			S := a.TermAs[Set[Set[B]]]("S")
			space := a.TermAs[Set[A]]("⋃T")
			target := a.TermAs[Set[B]]("⋃S")
			g, gDef := a.LetAs[Fun[Prod[A, B], Prod[B, B]]]("g", "λp:prod(A, B). (f(fst(p)), snd(p))")
			gContinuous := a.Have(
				"g is continuous from the product to S × S, f and the identity being continuous",
				"continuous_map(product_topology(T, S), product_topology(S, S), g)",
				By(
					gDef,
					fContinuous,
					ProductMapContinuous.At(T, S, S, S, a.TermAs[Fun[A, B]]("f"), a.TermAs[Fun[B, B]]("identity_map")),
					continuous.Identity.At(S),
					functions.IdentityApply))
			diagonalClosed := a.Have(
				"S is Hausdorff, so its diagonal is closed in S × S",
				"closed_in(product_topology(S, S), set_diagonal(⋃S))",
				By(hausdorff, HausdorffIffDiagonalClosed.At(S)))
			preimageClosed := a.Have(
				"so the preimage of the diagonal under g is closed in the "+
					"product, whose points are the pairs of points of the two spaces",
				"closed_in(product_topology(T, S), preimage_on(set_cross(⋃T, ⋃S), g, set_diagonal(⋃S)))",
				By(
					diagonalClosed,
					gContinuous,
					continuous.ClosedPreimage.At(
						a.TermAs[Set[Set[Prod[A, B]]]]("product_topology(T, S)"),
						a.TermAs[Set[Set[Prod[B, B]]]]("product_topology(S, S)"),
						g),
					ProductSpace.At(T, S)))
			graphIsPreimage := a.Have(
				"the graph is that preimage",
				"«graph» = preimage_on(set_cross(⋃T, ⋃S), g, set_diagonal(⋃S))",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[A, B]]("p")
					b.Show(
						"p is on the graph when fst(p) lies in the space and snd(p) is f(fst(p)), "+
							"a point of S: when p is in the product and g(p) on the diagonal",
						By(
							gDef,
							pairs.PairEta.At(p),
							pairs.PairEq,
							continuous.MapsInto.Read(fContinuous).At(b.TermAs[A]("fst(p)")),
							set_product.InCrossProjections.At(space, target, p),
							set_product.InDiagonal.At(target, b.TermAs[B]("f(fst(p))"), b.TermAs[B]("snd(p)"))))
				}))
			a.Show(
				"so the graph is closed in the product",
				graphIsPreimage.Rw(),
				By(preimageClosed))
		}),
})}

// ---------------------------------------------------------------------------
// Compactness and the tube lemma
// ---------------------------------------------------------------------------

// TubeLemma — an open set of the product around a slice over a compact
// set holds a tube around it: the open sets v over which some open u about
// x has u × v inside w cover k, a point y of k giving the open rectangle
// about (x, y) that w holds; finitely many of them do; meeting their sets
// u, by induction on that finite family, gives one open u about x serving
// them all, the whole space serving the empty family; and u × k lies in
// the rectangles u × v. No choice enters: the sets u are named by the
// family, never chosen from it.
var TubeLemma = tubeLemmaThm{family.Add(registry.ProofEntry{
	Name: "TubeLemma",
	Key:  "prop_1a8f348ceb7db386",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀k:set(B). ∀w:set(prod(A, B)). ∀x:A.",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(S, k)",
			"w ∈ product_topology(T, S)",
			"x ∈ ⋃T",
			"set_cross({x}, k) ⊆ w",
		},
		Conclusion: "∃u:set(A). u ∈ T ∧ x ∈ u ∧ set_cross(u, k) ⊆ w",
		Abbrev: Abbrev{
			{Name: "hasRectangle", Text: "λv:set(B). ∃u:set(A). u ∈ T ∧ x ∈ u ∧ set_cross(u, v) ⊆ w"},
			{Name: "rectangleSides", Text: "{v:set(B) | v ∈ S ∧ «hasRectangle»(v)}"},
		},
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology Fact,
			S *Expr[Set[Set[B]]],
			k *Expr[Set[B]],
			compactK Fact,
			w *Expr[Set[Prod[A, B]]],
			wOpen Fact,
			x *Expr[A],
			inSpace, slice Fact,
		) {
			subcover := a.Conjuncts(
				a.Unfolded(compactK, compact.CompactInDef),
				"k lies in the second space",
				"every open cover of k has a finite subcover")[1]

			covers := a.Have(
				"the family covers k: y in k gives (x, y) in the slice, "+
					"and an open rectangle about it inside w has y in its side",
				"∀y:B. y ∈ k ⇒ y ∈ ⋃«rectangleSides»",
				Derive(func(b *Argument) {
					b.FixAs[B]("y")
					yIn := b.Assume()
					inW := b.Have(
						"(x, y) lies in the slice, and so in w",
						"(x, y) ∈ w",
						BySets(yIn, slice, set_product.InCross))
					_, _, rectangle := b.Obtain2(
						"w is open, so an open rectangle u × v about (x, y) lies inside it",
						"∃u:set(A). ∃v:set(B). u ∈ T ∧ v ∈ S ∧ (x, y) ∈ set_cross(u, v) ∧ set_cross(u, v) ⊆ w",
						By(wOpen, inW, ProductOpenIff))
					b.Show(
						"x ∈ u and y ∈ v, so v is a member of the family holding y",
						BySets(rectangle, set_product.InCross))
				}))
			_, finiteSubcover := a.ObtainAs[Set[Set[B]]](
				"the family is an open cover of k, so by compactness finitely many of its members cover k",
				"∃d:set(set(B)). d ⊆ «rectangleSides» ∧ finite(d) ∧ k ⊆ ⋃d",
				BySets(subcover.At(a.TermAs[Set[Set[B]]]("«rectangleSides»")), covers))
			members := a.Have(
				"each member of d is a side of an open rectangle about x inside w",
				"∀v:set(B). v ∈ d ⇒ «hasRectangle»(v)",
				BySets(finiteSubcover))

			u, served := a.ObtainAs[Set[A]](
				"one open set about x serves every member of d, by induction on that finite family",
				"∃u:set(A). u ∈ T ∧ x ∈ u ∧ ∀v:set(B). v ∈ d ⇒ set_cross(u, v) ⊆ w",
				ByInduction(finite_set.FiniteInductFreshOn, finiteSubcover, members,
					Case(
						"with no member any open set about x serves, and the whole space is one",
						Derive(func(b *Argument) {
							b.Take(b.Term("⋃T"))
							b.Show(
								"⋃T is open and contains x, and the empty family asks nothing of it",
								BySets(inSpace, topological_space.SpaceOpen.Read(topology)))
						})),
					Case(
						"one more member v: the open set for v meets the one serving "+
							"the rest e, and a smaller set keeps each rectangle in w",
						Derive(func(b *Argument) {
							b.FixAs[Set[B]]("v")
							b.FixAs[Set[Set[B]]]("e")
							carried := b.Conjuncts(
								b.Assume(),
								"some open set about x serves e",
								"v is a new member",
								"e is finite",
								"v is a side of an open rectangle about x inside w",
								"every member of e is such a side")
							forRest, forNew := carried[0], carried[3]
							u1, servesRest := b.UnpackAs[Set[A]](forRest, "u₁")
							u2, servesNew := b.UnpackAs[Set[A]](forNew, "u₂")
							b.Take(b.Term("u₁ ∩ u₂"))
							b.Show(
								"u₁ ∩ u₂ is open, contains x, and serves v through u₂ and every member of e through u₁",
								BySets(
									servesRest,
									servesNew,
									At(topological_space.InterOpen.Read(topology), u1, u2),
									set_product.InCrossProjections))
						}))))

			a.Take(u)
			a.Show(
				"u is open, contains x, and u × k lies in the rectangles u × v, since the members v of d cover k",
				BySets(served, finiteSubcover, set_product.InCrossProjections))
		}),
})}

// CompactProduct — the product of two compact sets is compact. The
// rectangle lies in the product's points. Against an open cover c, the
// slice over a point x of k is compact, the continuous image of l, so
// finitely many members of c cover it; their union is open and holds a
// tube about the slice (TubeLemma). So the open sets u with u × l covered
// by finitely many members of c together cover k; finitely many of them
// do, and by induction on that finite family one finite subfamily of c
// covers all their tubes, hence the rectangle. No choice enters: the
// finite subfamilies are named by the family, never chosen from it.
var CompactProduct = compactProductThm{family.Add(registry.ProofEntry{
	Name: "CompactProduct",
	Key:  "prop_91b5caf9e8a0e9e4",
	Build: family.Sections(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀k:set(A). ∀l:set(B).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"compact_in(T, k)",
			"compact_in(S, l)",
		},
		Conclusion: "compact_in(product_topology(T, S), set_cross(k, l))",
		Abbrev: Abbrev{
			{Name: "finitelyCovered", Text: "λc:set(set(prod(A, B))). λu:set(A). ∃e:set(set(prod(A, B))). " +
				"    e ⊆ c ∧ finite(e) ∧ set_cross(u, l) ⊆ ⋃e"},
			{Name: "tubeBases", Text: "λc:set(set(prod(A, B))). {u:set(A) | u ∈ T ∧ «finitelyCovered»(c, u)}"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// An open cover of the slice over x covers, by finitely many of
			// its members, a whole tube about that slice.
			tubeAboutSlice := ctx.Lemma(Statement{
				Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀l:set(B). ∀c:set(set(prod(A, B))). ∀x:A.",
				Hypotheses: []string{
					"is_topology(T)",
					"is_topology(S)",
					"compact_in(S, l)",
					"c ⊆ product_topology(T, S)",
					"x ∈ ⋃T",
					"set_cross({x}, l) ⊆ ⋃c",
				},
				Conclusion: "∃u:set(A). u ∈ T ∧ x ∈ u ∧ «finitelyCovered»(c, u)",
			},
				func(
					a *Argument,
					T *Expr[Set[Set[A]]],
					topologyT Fact,
					S *Expr[Set[Set[B]]],
					topologyS Fact,
					l *Expr[Set[B]],
					compactL Fact,
					c *Expr[Set[Set[Prod[A, B]]]],
					cOpen Fact,
					x *Expr[A],
					inSpace, sliceCovered Fact,
				) {
					continuity := a.Have(
						"pairing with x is continuous from the second space to the product",
						"continuous_map(S, product_topology(T, S), λy:B. (x, y))",
						By(topologyS, inSpace, SliceRightContinuous.At(T, S, x)))
					sliceIsImage := a.Have(
						"the slice over x is the image of l under that pairing",
						"image(λy:B. (x, y), l) = set_cross({x}, l)",
						Simp(Fwd(set_basic.Extension)),
						Derive(func(b *Argument) {
							b.FixAs[Prod[A, B]]("p")
							b.Show(
								"a point of the slice is x paired with its second coordinate, a point of l",
								BySets(set_product.InCrossProjections, set_product.InCross, pairs.PairEta))
						}))
					sliceCompact := a.Have(
						"so the slice is compact, the continuous image of the compact set l",
						"compact_in(product_topology(T, S), set_cross({x}, l))",
						By(Normalized, compactL, sliceIsImage, continuous.ImageCompact.Read(continuity).At(l)))
					subcover := a.Conjuncts(
						a.Unfolded(sliceCompact, compact.CompactInDef),
						"the slice lies in the product's points",
						"every open cover of the slice has a finite subcover")[1]
					e, finitelyMany := a.ObtainAs[Set[Set[Prod[A, B]]]](
						"finitely many members of c cover the slice",
						"∃e:set(set(prod(A, B))). e ⊆ c ∧ finite(e) ∧ set_cross({x}, l) ⊆ ⋃e",
						By(subcover.At(c), cOpen, sliceCovered))
					productTopology := a.Have(
						"the product is a topology",
						"is_topology(product_topology(T, S))",
						By(topologyT, topologyS, ProductTopology.At(T, S)))
					unionOpen := a.Have(
						"so the union of those members, open sets of the product, is open",
						"⋃e ∈ product_topology(T, S)",
						BySets(finitelyMany, cOpen, topological_space.UnionsOpen.Read(productTopology).At(e)))
					tube := a.Have(
						"the union is open around the slice over the compact l, so it holds a tube about the slice",
						"∃u:set(A). u ∈ T ∧ x ∈ u ∧ set_cross(u, l) ⊆ ⋃e",
						By(
							topologyT,
							compactL,
							unionOpen,
							inSpace,
							finitelyMany,
							TubeLemma.At(T, S, l, a.TermAs[Set[Prod[A, B]]]("⋃e"), x)))
					a.Show(
						"that tube is covered by those finitely many members of c",
						By(tube, finitelyMany))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					T *Expr[Set[Set[A]]],
					topologyT Fact,
					S *Expr[Set[Set[B]]],
					topologyS Fact,
					k *Expr[Set[A]],
					compactK Fact,
					l *Expr[Set[B]],
					compactL Fact,
				) {
					compactnessK := a.Conjuncts(
						a.Unfolded(compactK, compact.CompactInDef),
						"k lies in the first space",
						"every open cover of k has a finite subcover")
					kInSpace, subcover := compactnessK[0], compactnessK[1]
					lInSpace := a.Conjuncts(
						a.Unfolded(compactL, compact.CompactInDef),
						"l lies in the second space",
						"every open cover of l has a finite subcover")[0]

					a.Do(
						Simp(Fwd(compact.CompactInDef)),
						SplitConj(
							Case(
								"the rectangle lies in the product's points, as k and l lie in the two spaces",
								Simp(Fwd(ProductSpace)),
								By(kInSpace, lInSpace, set_product.CrossSubsetIff)),
							Case(
								"an open cover c of the rectangle has a finite subcover",
								Derive(func(b *Argument) {
									c := b.FixAs[Set[Set[Prod[A, B]]]]("c")
									cover := b.Conjuncts(
										b.Assume(),
										"the members of c are open in the product",
										"c covers the rectangle")
									cOpen, cCovers := cover[0], cover[1]
									covers := b.Have(
										"the family covers k: the slice over a point x of k is covered by c, so it has its tube",
										"∀x:A. x ∈ k ⇒ x ∈ ⋃«tubeBases»(c)",
										Derive(func(g *Argument) {
											x := g.FixAs[A]("x")
											xIn := g.Assume()
											inSpace := g.Have(
												"x lies in the first space, as k does",
												"x ∈ ⋃T",
												BySets(xIn, kInSpace))
											sliceCovered := g.Have(
												"the slice over x lies in the rectangle, which c covers",
												"set_cross({x}, l) ⊆ ⋃c",
												BySets(xIn, cCovers, set_product.CrossSubsetIff.At(g.TermAs[Set[A]]("{x}"), k, l, l)))
											tube := g.Have(
												"so finitely many members of c cover a tube about the slice",
												"∃u:set(A). u ∈ T ∧ x ∈ u ∧ «finitelyCovered»(c, u)",
												By(topologyT, topologyS, compactL, cOpen, inSpace, sliceCovered, At(tubeAboutSlice, T, S, l, c, x)))
											g.Show(
												"the base of that tube is a member of the family holding x",
												By(tube, set_basic.InUnions.At(g.TermAs[Set[Set[A]]]("«tubeBases»(c)"), x)))
										}))
									_, finiteSubcover := b.ObtainAs[Set[Set[A]]](
										"the family is an open cover of k, so by compactness finitely many of its members cover k",
										"∃d:set(set(A)). d ⊆ «tubeBases»(c) ∧ finite(d) ∧ k ⊆ ⋃d",
										BySets(subcover.At(b.TermAs[Set[Set[A]]]("«tubeBases»(c)")), covers))
									members := b.Have(
										"the tube over each member of d is covered by finitely many members of c",
										"∀u:set(A). u ∈ d ⇒ «finitelyCovered»(c, u)",
										BySets(finiteSubcover))

									e, covered := b.ObtainAs[Set[Set[Prod[A, B]]]](
										"one finite subfamily of c covers the tubes over all of d, by induction on that finite family",
										"∃e:set(set(prod(A, B))). e ⊆ c ∧ finite(e) ∧ ∀u:set(A). u ∈ d ⇒ set_cross(u, l) ⊆ ⋃e",
										ByInduction(finite_set.FiniteInductFreshOn, finiteSubcover, members,
											Case(
												"with no tube to cover the empty subfamily serves",
												Derive(func(g *Argument) {
													g.Take(g.TermAs[Set[Set[Prod[A, B]]]]("∅"))
													g.Show(
														"∅ is a finite subfamily of c, and no member of the empty family asks anything",
														BySets(finite_set.FiniteRules))
												})),
											Case(
												"one more member u: the two finite subfamilies for u "+
													"and for the rest f unite to a finite subfamily of c",
												Derive(func(g *Argument) {
													g.FixAs[Set[A]]("u")
													g.FixAs[Set[Set[A]]]("f")
													carried := g.Conjuncts(
														g.Assume(),
														"a finite subfamily of c covers the tubes over f",
														"u is a new member",
														"f is finite",
														"a finite subfamily of c covers the tube over u",
														"so does one for every member of f")
													forRest, forNew := carried[0], carried[3]
													_, coversRest := g.UnpackAs[Set[Set[Prod[A, B]]]](forRest, "e₁")
													_, coversNew := g.UnpackAs[Set[Set[Prod[A, B]]]](forNew, "e₂")
													g.Take(g.Term("e₁ ∪ e₂"))
													g.Show(
														"e₁ ∪ e₂ lies in c, is finite, and covers the tube over u through e₂ and those over f through e₁",
														Simp(Fwd(set_basic.ForallInInsert)),
														BySets(coversRest, coversNew, finite_set.FiniteUnion))
												}))))

									b.Take(e)
									b.Show(
										"e is a finite subfamily of c, and the rectangle lies in the tubes over d, since d covers k",
										BySets(covered, finiteSubcover, set_product.InCrossProjections))
								})),
						))
				})
		}),
})}

// LocallyCompactProduct — the product of two locally compact spaces is
// locally compact. A point p of the product is a pair of points of the two
// spaces (ProductSpace), so its first coordinate has an open neighbourhood u
// inside a compact k and its second an open neighbourhood v inside a compact
// l. The rectangle u × v is open (RectangleOpen), holds p and lies in the
// rectangle k × l, which is compact (CompactProduct).
var LocallyCompactProduct = locallyCompactProductThm{family.Add(registry.ProofEntry{
	Name: "LocallyCompactProduct",
	Key:  "prop_ad2e241b76f937e0",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"locally_compact_space(T)",
			"locally_compact_space(S)",
		},
		Conclusion: "locally_compact_space(product_topology(T, S))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			topologyT topological_space.IsTopologyFact[on.T],
			topologyS topological_space.IsTopologyFact[on.S],
			locallyCompactT, locallyCompactS Fact,
		) {
			neighbourhoodsT := a.Unfolded(locallyCompactT, compact.LocallyCompactSpaceDef)
			neighbourhoodsS := a.Unfolded(locallyCompactS, compact.LocallyCompactSpaceDef)
			a.Do(Unfold(compact.LocallyCompactSpaceDef))
			p := a.FixAs[Prod[A, B]]("p")
			inSpace := a.Assume() // p is a point of the product
			coordinates := a.Have(
				"the coordinates of p are points of the two spaces, the points of the product being the pairs",
				"fst(p) ∈ ⋃T ∧ snd(p) ∈ ⋃S",
				By(
					Normalized,
					inSpace,
					ProductSpace.At(T, S),
					set_product.InCrossProjections.At(a.TermAs[Set[A]]("⋃T"), a.TermAs[Set[B]]("⋃S"), p)))
			u, k, aroundFirst := a.Obtain2As[Set[A], Set[A]](
				"the first coordinate has an open neighbourhood u inside a compact k",
				"∃u k:set(A). u ∈ T ∧ compact_in(T, k) ∧ fst(p) ∈ u ∧ u ⊆ k",
				By(neighbourhoodsT.At(a.TermAs[A]("fst(p)")), coordinates))
			v, l, aroundSecond := a.Obtain2As[Set[B], Set[B]](
				"the second coordinate has an open neighbourhood v inside a compact l",
				"∃v l:set(B). v ∈ S ∧ compact_in(S, l) ∧ snd(p) ∈ v ∧ v ⊆ l",
				By(neighbourhoodsS.At(a.TermAs[B]("snd(p)")), coordinates))
			a.Take(a.TermAs[Set[Prod[A, B]]]("set_cross(u, v)"))
			a.Take(a.TermAs[Set[Prod[A, B]]]("set_cross(k, l)"))
			a.Show(
				"the rectangle u × v is an open neighbourhood of p inside the compact rectangle k × l",
				SplitConjAll(
					Case(
						"u × v is open, a rectangle of open sets",
						By(aroundFirst, aroundSecond, RectangleOpen.At(T, S, u, v))),
					Case(
						"k × l is compact, a rectangle of compact sets",
						By(topologyT, topologyS, aroundFirst, aroundSecond, CompactProduct.At(T, S, k, l))),
					Case(
						"p lies in u × v, its coordinates lying in u and in v",
						By(aroundFirst, aroundSecond, set_product.InCrossProjections.At(u, v, p))),
					Case(
						"u × v lies in k × l, as u lies in k and v in l",
						By(aroundFirst, aroundSecond, set_product.CrossSubsetIff.At(u, k, v, l))),
				))
		}),
	Reading: "No separation is asked: the definition's neighbourhoods are an " +
		"open set inside a compact one, and rectangles of those are of the same kind.",
})}

// ProjectionClosedMap — the projection of a product onto its first factor
// is a closed map when the second factor is compact. A closed set c of the
// product lies in the pairs of points, so its projection lies in the first
// space, and the complement of c among the pairs is open. A point x of the
// first space that is the first coordinate of no point of c has its whole
// slice {x} × ⋃S in that complement, so the complement holds a tube
// u × ⋃S about the slice (TubeLemma); a point of c with its first
// coordinate in u would lie in the tube, so u is an open set about x
// missing the projection, and the complement of the projection is open
// point by point.
var ProjectionClosedMap = projectionClosedMapThm{family.Add(registry.ProofEntry{
	Name: "ProjectionClosedMap",
	Key:  "prop_59a142a2dae327ed",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(S, ⋃S)",
		},
		Conclusion: "closed_map(product_topology(T, S), T, fst)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			S *Expr[Set[Set[B]]],
			compactS Fact,
		) {
			first := a.TermAs[Set[A]]("⋃T")
			second := a.TermAs[Set[B]]("⋃S")
			a.Show(
				"the projection of every closed set of the product is closed",
				continuous.ClosedMap.Intro(Derive(func(b *Argument) {
					b.FixAs[Set[Prod[A, B]]]("c")
					closed := b.Assume()
					complement := b.TermAs[Set[Prod[A, B]]]("set_cross(⋃T, ⋃S) ∖ c")
					parts := b.Conjuncts(
						b.Simplified(b.Unfolded(closed, topological_space.ClosedInDef), Fwd(ProductSpace)),
						"c lies in the pairs of points of the two spaces",
						"its complement among the pairs is open")
					inside, complementOpen := parts[0], parts[1]

					neighbourhoods := b.Have(
						"each point of the first space outside the projection lies in an open set missing the projection",
						"∀x:A. x ∈ ⋃T ∖ image(fst, c) ⇒ ∃v:set(A). v ∈ T ∧ v ⊆ ⋃T ∖ image(fst, c) ∧ x ∈ v",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							outside := d.Assume()
							position := d.Conjuncts(
								d.Have(
									"x is a point of the first space and the first coordinate of no point of c",
									"x ∈ ⋃T ∧ ∀p:prod(A, B). p ∈ c ⇒ fst(p) ≠ x",
									BySets(outside)),
								"x is a point of the first space",
								"no point of c has first coordinate x")
							inSpace, offC := position[0], position[1]
							slice := d.Have(
								"the slice over x lies in the complement of c",
								"set_cross({x}, ⋃S) ⊆ set_cross(⋃T, ⋃S) ∖ c",
								Simp(Fwd(set_basic.SubsetDef)),
								Derive(func(e *Argument) {
									p := e.FixAs[Prod[A, B]]("p")
									inSlice := e.Assume()
									e.Show(
										"p has first coordinate x and its second in the second space, so it is a pair of points outside c",
										BySets(
											inSlice,
											offC,
											inSpace,
											set_product.InCrossProjections.At(e.TermAs[Set[A]]("{x}"), second, p),
											set_product.InCrossProjections.At(first, second, p)))
								}))
							u, tube := d.ObtainAs[Set[A]](
								"the complement of c is open about the slice over the compact "+
									"second space, so it holds a tube u × ⋃S about the slice",
								"∃u:set(A). u ∈ T ∧ x ∈ u ∧ set_cross(u, ⋃S) ⊆ set_cross(⋃T, ⋃S) ∖ c",
								By(topology, compactS, complementOpen, inSpace, slice, TubeLemma.At(T, S, second, complement, x)))
							misses := d.Have(
								"no point of c has its first coordinate in u, since such a point would lie in the tube, outside c",
								"∀p:prod(A, B). p ∈ c ⇒ fst(p) ∉ u",
								Derive(func(e *Argument) {
									p := e.FixAs[Prod[A, B]]("p")
									inC := e.Assume()
									e.Show(
										"p is a pair of points, so with its first coordinate in u it would lie in u × ⋃S, outside c",
										BySets(
											inC,
											inside,
											tube,
											set_product.InCrossProjections.At(first, second, p),
											set_product.InCrossProjections.At(u, second, p)))
								}))
							d.Take(u)
							d.Show(
								"u is an open set about x, inside the first space as an open set, and missing the projection",
								BySets(tube, misses))
						}))

					b.Show(
						"so the projection of c is closed",
						Simp(Fwd(topological_space.ClosedInDef)),
						SplitConj(
							Case(
								"the projection lies in the first space, as c lies in the pairs of points",
								BySets(inside, set_product.InCrossProjections)),
							Case(
								"its complement there is open, each of its points lying in an open set inside it",
								By(neighbourhoods, topological_space.OpenPointwise.Read(topology))),
						))
				})))
		}),
	Reading: "The second family need not be a topology: " +
		"compactness of ⋃S is read through covers by its members alone.",
})}

// ---------------------------------------------------------------------------
// Countable bases
// ---------------------------------------------------------------------------

// SecondCountableProduct — the product of two spaces with countable
// bases has one.
var SecondCountableProduct = secondCountableProductThm{family.Add(registry.ProofEntry{
	Name: "SecondCountableProduct",
	Key:  "prop_d9a21715a9387106",
	Deps: []registry.EntryLike{
		RectangleOpen,
		ProductOpenIff,
		cardinal.CountableProduct,
		cardinal.CountableImage,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"second_countable_space(T)",
			"second_countable_space(S)",
		},
		Conclusion: "second_countable_space(product_topology(T, S))",
	},
		"The rectangles of a member of each base are open (RectangleOpen) and countably many, "+
			"the image of a countable product (cardinal.CountableProduct, cardinal.CountableImage); "+
			"a point of an open set lies in a rectangle of open sets inside it (ProductOpenIff), "+
			"and in a rectangle of base members inside that. No axiom enters."),
})}
