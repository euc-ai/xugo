// maps.go — maps into, out of and between products. The projections are
// continuous and open; a map into a product is continuous exactly when its
// two components are; two continuous maps make a continuous map of the
// products; exchanging the factors is a homeomorphism; and pairing with a
// fixed coordinate is continuous.

package product_topology

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Projections and maps into a product
// ---------------------------------------------------------------------------

// FstContinuous — the first projection is continuous: a point of the product
// projects to a point of the first space, and the preimage of an open u is the
// rectangle of u against the second space, open point by point because a point
// of it lies in u × v for an open v about its second projection. Neither family
// need be a topology, so the second space itself is not at hand as that v.
var FstContinuous = fstContinuousThm{family.Add(registry.ProofEntry{
	Name: "FstContinuous",
	Key:  "prop_7d78400ba83e766",
	Build: family.Theorem("∀T:set(set(A)). ∀S:set(set(B)). "+
		"    continuous_map(product_topology(T, S), T, fst)",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]]) {
			pointsCarried := a.Have(
				"a point of the product projects to a point of the first space",
				"∀p:prod(A, B). p ∈ ⋃product_topology(T, S) ⇒ fst(p) ∈ ⋃T",
				Simp(Fwd(ProductSpace)),
				By(set_product.InCrossProjections))
			preimagesOpen := a.Have(
				"the preimage of an open set is open",
				"∀u:set(A). u ∈ T ⇒ preimage_on(⋃product_topology(T, S), fst, u) ∈ product_topology(T, S)",
				Derive(func(b *Argument) {
					u := b.FixAs[Set[A]]("u")
					open := b.Assume()
					rectangle := b.Have(
						"the preimage of u is the rectangle of u against the second space",
						"preimage_on(⋃product_topology(T, S), fst, u) = set_cross(u, ⋃S)",
						Simp(Fwd(ProductSpace)),
						Unfold(functions.PreimageOnDef),
						Simp(Fwd(set_basic.Extension)),
						Simp(Fwd(set_product.InCrossProjections)),
						BySets(open))
					b.Do(rectangle.Rw(), Simp(Fwd(ProductOpenIff)))
					b.FixAs[Prod[A, B]]("p")
					point := b.Assume()
					v, about := b.ObtainAs[Set[B]](
						"the second projection of p lies in an open v",
						"∃v:set(B). v ∈ S ∧ snd(p) ∈ v",
						BySets(point, set_product.InCrossProjections))
					inside := b.Have(
						"u × v lies inside the rectangle, since v lies inside the second space",
						"set_cross(u, v) ⊆ set_cross(u, ⋃S)",
						Simp(Fwd(set_product.InCrossProjections), Fwd(set_basic.SubsetDef)),
						BySets(about))
					b.Take(u)
					b.Take(v)
					b.Show(
						"u × v is an open rectangle about p inside u × ⋃S",
						By(open, point, about, inside, set_product.InCrossProjections))
				}))
			a.Show(
				"these are the two clauses of continuity",
				Unfold(continuous.ContinuousMap),
				By(pointsCarried, preimagesOpen))
		}),
})}

// SndContinuous — the second projection is continuous, by FstContinuous's
// argument on the other side.
var SndContinuous = sndContinuousThm{family.Add(registry.ProofEntry{
	Name: "SndContinuous",
	Key:  "prop_e916eecdb5ab847",
	Build: family.Theorem("∀T:set(set(A)). ∀S:set(set(B)). "+
		"    continuous_map(product_topology(T, S), S, snd)",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]]) {
			pointsCarried := a.Have(
				"a point of the product projects to a point of the second space",
				"∀p:prod(A, B). p ∈ ⋃product_topology(T, S) ⇒ snd(p) ∈ ⋃S",
				Simp(Fwd(ProductSpace)),
				By(set_product.InCrossProjections))
			preimagesOpen := a.Have(
				"the preimage of an open set is open",
				"∀v:set(B). v ∈ S ⇒ preimage_on(⋃product_topology(T, S), snd, v) ∈ product_topology(T, S)",
				Derive(func(b *Argument) {
					v := b.FixAs[Set[B]]("v")
					open := b.Assume()
					rectangle := b.Have(
						"the preimage of v is the rectangle of the first space against v",
						"preimage_on(⋃product_topology(T, S), snd, v) = set_cross(⋃T, v)",
						Simp(Fwd(ProductSpace)),
						Unfold(functions.PreimageOnDef),
						Simp(Fwd(set_basic.Extension)),
						Simp(Fwd(set_product.InCrossProjections)),
						BySets(open))
					b.Do(rectangle.Rw(), Simp(Fwd(ProductOpenIff)))
					b.FixAs[Prod[A, B]]("p")
					point := b.Assume()
					u, about := b.ObtainAs[Set[A]](
						"the first projection of p lies in an open u",
						"∃u:set(A). u ∈ T ∧ fst(p) ∈ u",
						BySets(point, set_product.InCrossProjections))
					inside := b.Have(
						"u × v lies inside the rectangle, since u lies inside the first space",
						"set_cross(u, v) ⊆ set_cross(⋃T, v)",
						Simp(Fwd(set_product.InCrossProjections), Fwd(set_basic.SubsetDef)),
						BySets(about))
					b.Take(u)
					b.Take(v)
					b.Show(
						"u × v is an open rectangle about p inside ⋃T × v",
						By(open, point, about, inside, set_product.InCrossProjections))
				}))
			a.Show(
				"these are the two clauses of continuity",
				Unfold(continuous.ContinuousMap),
				By(pointsCarried, preimagesOpen))
		}),
})}

// PairedContinuousIff — a map into a product is continuous exactly when
// its two components are. Forward, a component is the map followed by a
// projection. Backward, a value of the map is the pair of its components, a
// pair of points; and the preimage of an open w is open by the pointwise
// criterion in R: about a point x with h(x) in an open rectangle u × t inside
// w, the meet of the preimages of u and of t under the two components is open
// and lies in the preimage of w.
var PairedContinuousIff = pairedContinuousIffThm{family.Add(registry.ProofEntry{
	Name: "PairedContinuousIff",
	Key:  "prop_9bface2584868e51",
	Build: family.Theorem(Statement{
		Binders: "∀R:set(set(C)). ∀T:set(set(A)). ∀S:set(set(B)). ∀h:(C → prod(A, B)).",
		Hypotheses: []string{
			"is_topology(R)",
		},
		Conclusion: "continuous_map(R, product_topology(T, S), h) ⇔ " +
			"continuous_map(R, T, λz:C. fst(h(z))) ∧ continuous_map(R, S, λz:C. snd(h(z)))",
	},
		func(
			a *Argument,
			R *Expr[Set[Set[C]]],
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			h *Arrow[C, Prod[A, B]],
			topology topological_space.IsTopologyFact[on.R],
		) {
			a.Iff()
			a.Forward(
				"the components of a continuous map into the product are the map followed by the projections",
				func(b *Argument, continuity Fact) {
					first := b.Have(
						"h followed by the first projection is continuous",
						"continuous_map(R, T, fst ∘ h)",
						By(continuous.Compose.Read(continuity), FstContinuous))
					second := b.Have(
						"h followed by the second projection is continuous",
						"continuous_map(R, S, snd ∘ h)",
						By(continuous.Compose.Read(continuity), SndContinuous))
					b.Do(SplitConj(
						Case(
							"the first composite is the first component",
							By(first, functions.ComposeApply)),
						Case(
							"the second composite is the second component",
							By(second, functions.ComposeApply)),
					))
				})
			a.Backward(
				"a map with continuous components is continuous into the product",
				func(b *Argument, components Fact) {
					parts := b.Conjuncts(
						components,
						"the first component is continuous",
						"the second component is continuous")
					first, second := parts[0], parts[1]
					b.Show(
						"h is continuous into the product",
						continuous.ContinuousMap.Intro(
							Case(
								"a value of h is the pair of its components, a pair of points",
								Simp(Fwd(ProductSpace)),
								BySets(
									continuous.MapsInto.Read(first),
									continuous.MapsInto.Read(second),
									set_product.InCrossProjections)),
							Case(
								"the preimage of an open set w is open, by the pointwise criterion in R",
								Derive(func(c *Argument) {
									w := c.FixAs[Set[Prod[A, B]]]("w")
									open := c.Assume()
									neighbourhoods := c.Have(
										"each point of the preimage has an open set about it inside the preimage",
										"∀x:C. x ∈ preimage_on(⋃R, h, w) ⇒ ∃u:set(C). u ∈ R ∧ u ⊆ preimage_on(⋃R, h, w) ∧ x ∈ u",
										Derive(func(d *Argument) {
											d.FixAs[C]("x")
											point := d.Assume()
											_, _, rectangle := d.Obtain2As[Set[A], Set[B]](
												"the value h(x) lies in an open rectangle u × t inside w",
												"∃u:set(A). ∃t:set(B). u ∈ T ∧ t ∈ S ∧ h(x) ∈ set_cross(u, t) ∧ set_cross(u, t) ⊆ w",
												BySets(point, open, ProductOpenIff.At(T, S, w)))
											sides := d.Conjuncts(
												rectangle,
												"u is open",
												"t is open",
												"h(x) lies in u × t",
												"u × t lies inside w")
											d.Take(
												d.TermAs[Set[C]]("preimage_on(⋃R, λz:C. fst(h(z)), u) ∩ preimage_on(⋃R, λz:C. snd(h(z)), t)"))
											d.Do(SplitConjAll(
												Case(
													"the preimages of u and of t under the components are open, and so is their meet",
													By(
														sides[0],
														sides[1],
														topological_space.InterOpen.Read(topology),
														continuous.PreimageOpen.Read(first),
														continuous.PreimageOpen.Read(second))),
												Case(
													"a point of the meet goes into u × t, so into w",
													BySets(sides[3], set_product.InCrossProjections)),
												Case(
													"and x is such a point",
													BySets(point, sides[2], set_product.InCrossProjections)),
											))
										}))
									c.Show(
										"the pointwise criterion gives openness",
										By(neighbourhoods, topological_space.OpenPointwise.Read(topology)))
								})),
						))
				})
		}),
})}

// ProductMapContinuous — two continuous maps make a continuous map of
// the products. A pair of points goes to a pair of points. For a point p of
// the preimage of an open w, the value at p lies in an open rectangle u × v
// inside w, and the rectangle of the preimages of u under f and of v under g
// is an open rectangle about p inside the preimage. No axiom enters.
var ProductMapContinuous = productMapContinuousThm{family.Add(registry.ProofEntry{
	Name: "ProductMapContinuous",
	Key:  "prop_209e6f0791299059",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀U:set(set(C)). " +
			"∀V:set(set(D)). " +
			"∀f:(A → C). " +
			"∀g:(B → D).",
		Hypotheses: []string{
			"continuous_map(T, U, f)",
			"continuous_map(S, V, g)",
		},
		Conclusion: "continuous_map(product_topology(T, S), " +
			"    product_topology(U, V), " +
			"    λp:prod(A, B). (f(fst(p)), g(snd(p))))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			U *Expr[Set[Set[C]]],
			V *Expr[Set[Set[D]]],
			f *Arrow[A, C],
			g *Arrow[B, D],
			first, second Fact,
		) {
			a.Show(
				"the map of the products is continuous",
				continuous.ContinuousMap.Intro(
					Case(
						"a pair of points goes to a pair of points",
						Simp(Fwd(ProductSpace)),
						BySets(
							continuous.MapsInto.Read(first),
							continuous.MapsInto.Read(second),
							set_product.InCrossProjections,
							set_product.InCross)),
					Case(
						"the preimage of an open set w is open: an open rectangle about each of its points lies inside it",
						Derive(func(b *Argument) {
							w := b.FixAs[Set[Prod[C, D]]]("w")
							open := b.Assume()
							b.Do(Simp(Fwd(ProductOpenIff)))
							p := b.FixAs[Prod[A, B]]("p")
							point := b.Assume()
							u, v, rectangle := b.Obtain2As[Set[C], Set[D]](
								"the value at p lies in an open rectangle u × v inside w",
								"∃u:set(C). ∃v:set(D). "+
									"    u ∈ U ∧ v ∈ V ∧ (f(fst(p)), g(snd(p))) ∈ set_cross(u, v) ∧ set_cross(u, v) ⊆ w",
								BySets(open, point, ProductOpenIff.At(U, V, w)))
							sides := b.Conjuncts(
								rectangle,
								"u is open",
								"v is open",
								"the value at p lies in u × v",
								"u × v lies inside w")
							coordinates := b.Have(
								"the coordinates of p are points of the two spaces",
								"fst(p) ∈ ⋃T ∧ snd(p) ∈ ⋃S",
								BySets(b.Simplified(point, Fwd(ProductSpace)), set_product.InCrossProjections))
							left := b.TermAs[Set[A]]("preimage_on(⋃T, f, u)")
							right := b.TermAs[Set[B]]("preimage_on(⋃S, g, v)")
							b.Take(left)
							b.Take(right)
							b.Do(SplitConjAll(
								Case(
									"the preimage of u under f is open",
									By(sides[0], continuous.PreimageOpen.Read(first))),
								Case(
									"the preimage of v under g is open",
									By(sides[1], continuous.PreimageOpen.Read(second))),
								Case(
									"p lies in the rectangle of the two preimages",
									BySets(
										sides[2],
										coordinates,
										set_product.InCross.At(u, v, b.TermAs[C]("f(fst(p))"), b.TermAs[D]("g(snd(p))")),
										set_product.InCrossProjections.At(left, right, p))),
								Case(
									"a point of that rectangle goes into u × v, so into w",
									Simp(Fwd(ProductSpace), Fwd(set_basic.SubsetDef)),
									Derive(func(c *Argument) {
										q := c.FixAs[Prod[A, B]]("q")
										inside := c.Assume()
										c.Show(
											"its coordinates lie in the two spaces and are carried into u and into v",
											BySets(
												inside,
												sides[3],
												set_product.InCrossProjections.At(left, right, q),
												set_product.InCrossProjections.At(c.TermAs[Set[A]]("⋃T"), c.TermAs[Set[B]]("⋃S"), q),
												set_product.InCross.At(u, v, c.TermAs[C]("f(fst(q))"), c.TermAs[D]("g(snd(q))"))))
									})),
							))
						})),
				))
		}),
})}

// SliceRightContinuous — pairing with a fixed first coordinate is continuous:
// the pair is a point of the product, and the preimage of an open w is open by
// the pointwise criterion, for y with (x, y) in a rectangle u × v inside w has v
// about it, an open set inside the preimage since x lies in u.
var SliceRightContinuous = sliceRightContinuousThm{family.Add(registry.ProofEntry{
	Name: "SliceRightContinuous",
	Key:  "prop_ba28264ecbaf37c",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀x:A.",
		Hypotheses: []string{
			"is_topology(S)",
			"x ∈ ⋃T",
		},
		Conclusion: "continuous_map(S, product_topology(T, S), λy:B. (x, y))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], x *Expr[A], topology, xIn Fact) {
			pointsCarried := a.Have(
				"a point of the second space pairs to a point of the product",
				"∀y:B. y ∈ ⋃S ⇒ (x, y) ∈ ⋃product_topology(T, S)",
				Simp(Fwd(ProductSpace)),
				By(xIn, set_product.InCross))
			preimagesOpen := a.Have(
				"the preimage of an open set is open",
				"∀w:set(prod(A, B)). w ∈ product_topology(T, S) ⇒ preimage_on(⋃S, λz:B. (x, z), w) ∈ S",
				Derive(func(b *Argument) {
					w := b.FixAs[Set[Prod[A, B]]]("w")
					open := b.Assume()
					neighbourhoods := b.Have(
						"each point of the preimage has an open set about it inside the preimage",
						Statement{
							Binders: "∀y:B.",
							Hypotheses: []string{
								"y ∈ preimage_on(⋃S, λz:B. (x, z), w)",
							},
							Conclusion: "∃v:set(B). v ∈ S ∧ v ⊆ preimage_on(⋃S, λz:B. (x, z), w) ∧ y ∈ v",
						},
						Derive(func(c *Argument) {
							c.FixAs[B]("y")
							point := c.Assume()
							_, v, rectangle := c.Obtain2As[Set[A], Set[B]](
								"the pair lies in an open rectangle u × v inside w",
								"∃u:set(A). ∃v:set(B). u ∈ T ∧ v ∈ S ∧ (x, y) ∈ set_cross(u, v) ∧ set_cross(u, v) ⊆ w",
								BySets(point, open, ProductOpenIff.At(T, S, w)))
							sides := c.Have(
								"the coordinates of the pair lie in the two sides",
								"x ∈ u ∧ y ∈ v",
								By(rectangle, set_product.InCross))
							inside := c.Have(
								"a point of v lies in the second space and pairs into u × v, so into w",
								"v ⊆ preimage_on(⋃S, λz:B. (x, z), w)",
								BySets(rectangle, set_product.InCross))
							c.Take(v)
							c.Show(
								"v is an open set about y inside the preimage",
								By(inside, sides, rectangle))
						}))
					b.Show(
						"the pointwise criterion gives openness",
						By(neighbourhoods, topological_space.OpenPointwise.Read(topology)))
				}))
			a.Show(
				"these are the two clauses of continuity",
				Unfold(continuous.ContinuousMap),
				By(pointsCarried, preimagesOpen))
		}),
})}
