// compactness.go — the compact sets of ℝⁿ: a box ⟦a, b⟧ⁿ is compact, by
// induction on n, the box of ℝⁿ⁺¹ being the box of ℝⁿ times ⟦a, b⟧ with
// a coordinate appended; so a sequence of the unit cube, the box ⟦0, 1⟧ⁿ,
// has a subsequence converging in the cube, and a closed set within a
// bounded norm is compact (Heine–Borel); the norm is continuous, so the
// closed unit ball and the unit sphere, cut out by the norm, are closed,
// hence compact; and the sphere Sⁿ bounds the ball D^(n + 1), what lies
// inside it being the open unit ball.

package euclidean_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// BoxAppendCoordinate — the box ⟦a, b⟧ⁿ⁺¹ is the box ⟦a, b⟧ⁿ times ⟦a, b⟧
// with the second factor appended as the coordinate n. Appending t in
// ⟦a, b⟧ to a point x of the n-box gives an (n + 1)-vector whose
// coordinate n is t and whose others are x's. Conversely a point u of the
// (n + 1)-box is appended from u with its coordinate n cleared, a point
// of the n-box, and from u(n).
var BoxAppendCoordinate = boxAppendCoordinateThm{family.Add(registry.ProofEntry{
	Name: "BoxAppendCoordinate",
	Key:  "prop_34d9f070f0d9c1b1",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀a b:real.",
		Conclusion: "«box»(n + 1) = " +
			"image(λp:prod(num → real, real). «append»(fst(p), snd(p)), set_cross(«box»(n), ⟦a, b⟧))",
		Abbrev: Abbrev{
			{Name: "box", Text: "λm:num. {u:(num → real) | vec⟨m⟩(u) ∧ ∀i:num. i < m ⇒ a ≤ u(i) ∧ u(i) ≤ b}"},
		},
	},
		func(arg *Argument, n *Expr[Nat], a, b *Expr[Real]) {
			type point = Fun[Nat, Real]
			type pair = Prod[point, Real]
			appended := arg.Have(
				"appending a coordinate of ⟦a, b⟧ to a point of the n-box gives a point of the (n + 1)-box",
				Statement{
					Binders: "∀x:(num → real). ∀t:real.",
					Hypotheses: []string{
						"vec⟨n⟩(x)",
						"∀i:num. i < n ⇒ a ≤ x(i) ∧ x(i) ≤ b",
						"a ≤ t",
						"t ≤ b",
					},
					Conclusion: "vec⟨n + 1⟩(«append»(x, t)) ∧ " +
						"∀i:num. i < n + 1 ⇒ a ≤ «append»(x, t)(i) ∧ «append»(x, t)(i) ≤ b",
				},
				Derive(func(c *Argument) {
					x := c.VecFixAs[Real, DimN]("x")
					t := c.FixAs[Real]("t")
					parts := c.Conjuncts(
						c.Assume(),
						"x is an n-vector",
						"the coordinates of x lie in ⟦a, b⟧",
						"t is at least a",
						"and at most b")
					coordinates := c.Have(
						"its coordinate n is t and its others are those of x",
						"∀i:num. i < n + 1 ⇒ a ≤ «append»(x, t)(i) ∧ «append»(x, t)(i) ≤ b",
						Derive(func(d *Argument) {
							i := d.FixAs[Nat]("i")
							below := d.Assume()
							d.Cases(d.Term("i = n"))
							d.When(
								"the coordinate n is t",
								func(e *Argument, last Fact) {
									e.Show(
										"which lies in ⟦a, b⟧",
										By(last, parts[2], parts[3]))
								})
							d.Otherwise(
								"a coordinate below n is that of x",
								func(e *Argument, earlier Fact) {
									e.Show(
										"which lies in ⟦a, b⟧",
										ByArith(earlier, below, parts[1].At(i)))
								})
						}))
					c.Show(
						"and an n-vector with a coordinate appended is an (n + 1)-vector",
						By(coordinates, AppendCoordinateVec.At(proof.Inhabit(x, parts[0]), t)))
				}))
			into := arg.Have(
				"so the image lies in the (n + 1)-box",
				"image(λp:prod(num → real, real). «append»(fst(p), snd(p)), set_cross(«box»(n), ⟦a, b⟧)) ⊆ "+
					"«box»(n + 1)",
				Simp(Fwd(set_image.ImageSubsetIff)),
				Derive(func(c *Argument) {
					c.FixAs[pair]("p")
					c.Show(
						"the parts of a point of the product are a point of the n-box and a point of ⟦a, b⟧",
						By(
							appended.At(c.TermAs[point]("fst(p)"), c.TermAs[Real]("snd(p)")),
							set_product.InCrossProjections))
				}))
			onto := arg.Have(
				"every point of the (n + 1)-box is appended from a point of the n-box",
				"«box»(n + 1) ⊆ "+
					"image(λp:prod(num → real, real). «append»(fst(p), snd(p)), set_cross(«box»(n), ⟦a, b⟧))",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(c *Argument) {
					c.FixAs[point]("u")
					parts := c.Conjuncts(
						c.Assume(),
						"u is an (n + 1)-vector",
						"the coordinates of u lie in ⟦a, b⟧")
					bounds := c.Have(
						"clearing the coordinate n of u keeps its coordinates below n in ⟦a, b⟧",
						"∀i:num. i < n ⇒ a ≤ «append»(u, &0)(i) ∧ «append»(u, &0)(i) ≤ b",
						c.ForEach(func(i *Expr[Nat]) Action { return ByArith(parts[1].At(i)) }))
					cleared := c.Have(
						"and leaves an n-vector",
						"vec⟨n⟩(«append»(u, &0))",
						Unfold(vec_space.VecDef),
						Derive(func(d *Argument) {
							i := d.FixAs[Nat]("i")
							past := d.Assume()
							d.Cases(d.Term("i = n"))
							d.When(
								"the coordinate n is cleared",
								func(e *Argument, at Fact) {
									e.Show(
										"so it is zero",
										By(at))
								})
							d.Otherwise(
								"a coordinate past n is that of u",
								func(e *Argument, beyond Fact) {
									e.Show(
										"which is zero, u being an (n + 1)-vector",
										ByArith(beyond, past, parts[0].At(i)))
								})
						}))
					restored := c.Have(
						"appending u(n) to u with its coordinate n cleared gives u back",
						"«append»(«append»(u, &0), u(n)) = u",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[Nat]("i")
							d.Cases(d.Term("i = n"))
							d.When(
								"the coordinate n is u(n) again",
								func(e *Argument, at Fact) {
									e.Show(
										"on both sides",
										By(Normalized, at))
								})
							d.Otherwise(
								"the others were never touched",
								func(e *Argument, off Fact) {
									e.Show(
										"on both sides",
										By(off))
								})
						}))
					c.Show(
						"so u is the image of u with its coordinate n cleared and of u(n)",
						Simp(Fwd(set_basic.InImage)),
						Witness(c.TermAs[pair]("(«append»(u, &0), u(n))")),
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd), Fwd(set_product.InCross)),
						ByArith(bounds, cleared, restored, parts[1].At(n)))
				}))
			arg.Show(
				"so the two sets are equal",
				By(onto, into, set_order.SubsetAntisym))
		}),
})}

// BoxCompact — a box ⟦a, b⟧ⁿ is compact in ℝⁿ, by induction on n. In ℝ⁰
// every point is the zero vector, so the box is finite. The box of ℝⁿ⁺¹
// is the box of ℝⁿ times ⟦a, b⟧ with the coordinate n appended; the
// product of the two is compact, the closed interval being compact on the
// line, and appending is continuous, so its image is compact.
var BoxCompact = boxCompactThm{family.Add(registry.ProofEntry{
	Name: "BoxCompact",
	Key:  "prop_a32b63f4da919b2e",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀a b:real.",
		Conclusion: "compact_in(euclidean_topology(n), «box»(n))",
		Abbrev: Abbrev{
			{Name: "box", Text: "λm:num. {u:(num → real) | vec⟨m⟩(u) ∧ ∀i:num. i < m ⇒ a ≤ u(i) ∧ u(i) ≤ b}"},
		},
	},
		func(arg *Argument, n *Expr[Nat], a, b *Expr[Real]) {
			arg.Induct(n)
			arg.Base(
				"in ℝ⁰ every point is the zero vector, so the box is finite",
				func(c *Argument) {
					origin := c.Have(
						"a 0-vector is the zero vector",
						"«box»(0) ⊆ {vec_zero}",
						BySets(vec_space.VecDimZero))
					finite := c.Have(
						"so the box is finite",
						"finite(«box»(0))",
						By(origin, finite_set.FiniteSubset, finite_set.FiniteSing))
					inSpace := c.Have(
						"and it lies in ℝ⁰",
						"«box»(0) ⊆ ⋃euclidean_topology(0)",
						BySets(EuclideanSpace.At(c.TermAs[Nat]("0"))))
					c.Show(
						"a finite set of points of the space is compact",
						By(finite, inSpace, compact.FiniteCompact))
				})
			arg.Step(
				"the box of ℝⁿ⁺¹ is the image of the box of ℝⁿ times ⟦a, b⟧ under appending a coordinate",
				func(c *Argument, ih Fact) {
					cross := c.Have(
						"the box of ℝⁿ times ⟦a, b⟧ is compact in ℝⁿ × ℝ",
						"compact_in(product_topology(euclidean_topology(n), real_topology), set_cross(«box»(n), ⟦a, b⟧))",
						By(
							ih,
							product_topology.CompactProduct,
							EuclideanTopology.At(n),
							real_topology.RealTopology,
							real_topology.ClosedIntervalCompact.At(a, b)))
					image := c.Have(
						"and the box of ℝⁿ⁺¹ is its image under appending",
						"«box»(n + 1) = "+
							"image(λp:prod(num → real, real). «append»(fst(p), snd(p)), set_cross(«box»(n), ⟦a, b⟧))",
						Cite(BoxAppendCoordinate, n, a, b))
					c.Show(
						"with suc(n) written n + 1, the box of ℝⁿ⁺¹ is that image, compact as appending is continuous",
						Simp(Fwd(nat_arith.Add1)),
						image.Rw(),
						By(cross, continuous.ImageCompact, AppendCoordinateContinuous.At(n)))
				})
		}),
})}

// CubeSubsequence — a sequence of the unit cube has a subsequence
// converging to a point of the cube. The cube is the box ⟦0, 1⟧ⁿ, which is
// compact, and the open sets of ℝⁿ are those of the metric space of the
// n-vectors under the distance, in which a compact set is sequentially
// compact.
var CubeSubsequence = cubeSubsequenceThm{family.Add(registry.ProofEntry{
	Name: "CubeSubsequence",
	Key:  "prop_f725bf33b11c89d6",
	Reading: "Only the bounds 0 and 1 on each coordinate are read, no continuity. " +
		"At n = 0 the cube is the zero vector and the identity reindexing serves.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x:(num → num → real).",
		Hypotheses: []string{
			"∀k:num. x(k) ∈ unit_cube(n)",
		},
		Conclusion: "∃σ:(num → num). ∃l:(num → real). " +
			"    (∀j:num. σ(j) < σ(j + 1)) ∧ " +
			"    l ∈ unit_cube(n) ∧ " +
			"    metric_converges_to({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩, x ∘ σ, l)",
	},
		func(a *Argument, n *Expr[Nat], x *Arrow2[Nat, Nat, Real], inCube Fact) {
			type point = Fun[Nat, Real]
			compact := a.Have(
				"the cube is the box ⟦0, 1⟧ⁿ, compact in ℝⁿ, the metric topology of the n-vectors",
				"compact_in(metric_topology({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩), unit_cube(n))",
				Unfold(UnitCubeDef),
				By(BoxCompact.At(n, a.TermAs[Real]("&0"), a.TermAs[Real]("&1")), EuclideanTopologyDef.At(n)))
			a.Show(
				"a compact set of the metric space of the n-vectors is sequentially compact",
				By(
					inCube,
					compact,
					euclidean.EuclideanMetric.At(n),
					complete_metric.CompactImpSequential.At(
						a.TermAs[Set[point]]("{u:(num → real) | vec⟨n⟩(u)}"),
						a.TermAs[Fun2[point, point, Real]]("vec_dist⟨n⟩"),
						a.TermAs[Set[point]]("unit_cube(n)"))))
		}),
})}

// HeineBorel — a closed set of ℝⁿ whose points have norm at most B is
// compact. A coordinate is at most the norm in size, so the set lies in
// the box ⟦−B, B⟧ⁿ, which is compact, and a closed set inside a compact
// set is compact.
var HeineBorel = heineBorelThm{family.Add(registry.ProofEntry{
	Name: "HeineBorel",
	Key:  "prop_18fcfe7499afbe15",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀k:set(num → real). ∀B:real.",
		Hypotheses: []string{
			"closed_in(euclidean_topology(n), k)",
			"∀x:(num → real). x ∈ k ⇒ ‖x‖_n ≤ B",
		},
		Conclusion: "compact_in(euclidean_topology(n), k)",
	},
		func(a *Argument, n *Expr[Nat], k *Expr[Set[Fun[Nat, Real]]], B *Expr[Real], closed, bounded Fact) {
			inBox := a.Have(
				"k lies in the box ⟦−B, B⟧ⁿ",
				"k ⊆ {u:(num → real) | vec⟨n⟩(u) ∧ ∀i:num. i < n ⇒ -B ≤ u(i) ∧ u(i) ≤ B}",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.VecFixAs[Real, DimN]("x")
					xIn := b.Assume()
					vector := b.Have(
						"x, a point of a closed set of ℝⁿ, is an n-vector",
						"vec⟨n⟩(x)",
						BySets(closed, xIn, topological_space.ClosedInDef, EuclideanSpace.At(n)))
					coordinates := b.Have(
						"each coordinate of x is at most ‖x‖ ≤ B in size",
						"∀i:num. i < n ⇒ -B ≤ x(i) ∧ x(i) ≤ B",
						b.ForEach(func(i *Expr[Nat]) Action {
							return ByArith(xIn, bounded.At(x), euclidean.ComponentLeNorm.At(i, x))
						}))
					b.Show(
						"so x lies in the box",
						By(vector, coordinates))
				}))
			a.Show(
				"a closed set inside the compact box is compact",
				By(closed, inBox, BoxCompact.At(n, a.TermAs[Real]("-B"), B), compact.ClosedSubsetCompact))
		}),
})}

// CompactIffClosedBounded — the compact sets of ℝⁿ are its closed sets
// whose points have bounded norm: Heine–Borel and its converse. A closed
// set whose points have norm at most B is compact (HeineBorel).
// Conversely ℝⁿ is Hausdorff, so a compact set is closed; and the norm is
// continuous, so the norms of the points of a compact set form a compact
// set of reals, which is bounded.
var CompactIffClosedBounded = compactIffClosedBoundedThm{family.Add(registry.ProofEntry{
	Name: "CompactIffClosedBounded",
	Key:  "prop_cc8061bac059e611",
	Build: family.Theorem(
		"∀n:num. ∀k:set(num → real). "+
			"    compact_in(euclidean_topology(n), k) ⇔ "+
			"    closed_in(euclidean_topology(n), k) ∧ ∃B:real. ∀x:(num → real). x ∈ k ⇒ ‖x‖_n ≤ B",
		func(a *Argument, n *Expr[Nat], k *Expr[Set[Fun[Nat, Real]]]) {
			a.Iff()
			a.Forward(
				"a compact set of ℝⁿ is closed and bounded",
				func(b *Argument, isCompact Fact) {
					b.Do(SplitConj(
						Case(
							"k is closed, as a compact set of the Hausdorff space ℝⁿ",
							By(isCompact, compact.CompactClosed, EuclideanHausdorff.At(n), EuclideanTopology.At(n))),
						Case(
							"k is bounded, the norms of its points being a bounded set of reals",
							Derive(func(c *Argument) {
								norms := c.TermAs[Set[Real]]("image(λx:(num → real). ‖x‖_n, k)")
								normsCompact := c.Have(
									"the norm is continuous, so the norms of the points of k form a compact set of reals",
									"compact_in(real_topology, image(λx:(num → real). ‖x‖_n, k))",
									By(isCompact, continuous.ImageCompact, NormContinuous.At(n)))
								B, bound := c.UnpackAs[Real](
									GroupPremises(normsCompact, real_topology.CompactBounded.At(norms)),
									"B")
								c.Take(B)
								c.Show(
									"the norm of a point of k is one of them, at most its absolute value, at most B",
									ByArith(bound, set_image.FunInImage))
							})),
					))
				})
			a.Backward(
				"a closed set whose points have norm at most some B is compact, by Heine–Borel",
				func(b *Argument, closedBounded Fact) {
					b.Show(
						"k is compact",
						By(closedBounded, HeineBorel))
				})
		}),
})}

// NormContinuous — the norm is a continuous real function on ℝⁿ: x is y
// plus x − y, so ‖x‖ ≤ ‖y‖ + dist(x, y) by the triangle inequality, and
// symmetrically, so two norms differ by at most the distance between the
// vectors and δ = ε serves at every point.
var NormContinuous = normContinuousThm{family.Add(registry.ProofEntry{
	Name: "NormContinuous",
	Key:  "prop_9e7ebdbac8e85b27",
	Build: family.Theorem(
		"∀n:num. continuous_map(euclidean_topology(n), real_topology, λx:(num → real). ‖x‖_n)",
		func(a *Argument, n *Expr[Nat]) {
			gap := a.Have(
				"the norms of two vectors differ by at most their distance",
				"∀x y:(num → real). dist(‖x‖_n, ‖y‖_n) ≤ dist⟨n⟩(x, y)",
				Derive(func(b *Argument) {
					x := b.VecFixAs[Real, DimN]("x")
					y := b.VecFixAs[Real, DimN]("y")
					sums := vec_space.AddSubCancel.Read(real_ring.CommRing)
					b.Show(
						"x is y + (x − y) and y is x + (y − x), so each norm is at most the other plus the distance",
						ByArith(
							sums.At(y, x),
							sums.At(x, y),
							euclidean.NormTriangle.At(y, b.VecAs[Real, DimN]("x - y")),
							euclidean.NormTriangle.At(x, b.VecAs[Real, DimN]("y - x")),
							euclidean.VecDistDef.At(x, y),
							euclidean.VecDistDef.At(y, x),
							euclidean.DistSym.At(x, y),
							real_sgn_abs.RealDistDef))
				}))
			near := a.Have(
				"within ε of x in ℝⁿ the norm is within ε of ‖x‖",
				Statement{
					Binders: "∀x:(num → real). ∀ε:real.",
					Hypotheses: []string{
						"vec⟨n⟩(x)",
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ (∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < δ ⇒ dist(‖x‖_n, ‖y‖_n) < ε)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[Fun[Nat, Real]]("x")
					eps := b.FixAs[Real]("ε")
					given := b.Assume()
					b.Take(eps)
					b.Show(
						"δ = ε serves",
						ByArith(gap.At(x), given))
				}))
			a.Show(
				"which is continuity between the metric topologies of ℝⁿ and of the line",
				Simp(Fwd(EuclideanTopologyDef), Fwd(real_topology.RealTopologyMetric)),
				By(near, metric_space.ContinuousMapIff, real_topology.RealMetric, set_basic.InUniv))
		}),
})}

// BallCompact — the closed unit ball Dⁿ is compact. It is the set of
// points of ℝⁿ whose norm lies in ⟦0, 1⟧, the preimage of a closed
// interval under the continuous norm, so it is closed; and its points
// have norm at most 1.
var BallCompact = ballCompactThm{family.Add(registry.ProofEntry{
	Name: "BallCompact",
	Key:  "prop_c3be8bf720f3387a",
	Build: family.Theorem(
		"∀n:num. compact_in(euclidean_topology(n), euclidean_ball(n))",
		func(a *Argument, n *Expr[Nat]) {
			preimage := a.Have(
				"the ball is the set of points of ℝⁿ whose norm lies in ⟦0, 1⟧",
				"euclidean_ball(n) = preimage_on(⋃euclidean_topology(n), λx:(num → real). ‖x‖_n, ⟦&0, &1⟧)",
				BySets(EuclideanBallDef.At(n), EuclideanSpace.At(n), euclidean.NormNonneg))
			closed := a.Have(
				"so it is closed, the norm being continuous",
				"closed_in(euclidean_topology(n), euclidean_ball(n))",
				preimage.Rw(),
				By(
					NormContinuous.At(n),
					continuous.ClosedPreimage.At(
						a.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)"),
						a.TermAs[Set[Set[Real]]]("real_topology"),
						a.TermAs[Fun[Fun[Nat, Real], Real]]("λx:(num → real). ‖x‖_n")),
					real_topology.ClosedIntervalClosed.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1"))))
			a.Show(
				"and its points have norm at most 1",
				BySets(
					closed,
					HeineBorel.At(n, a.TermAs[Set[Fun[Nat, Real]]]("euclidean_ball(n)"), a.TermAs[Real]("&1")),
					EuclideanBallDef.At(n)))
		}),
})}

// SphereSubsetBall — the unit sphere Sⁿ lies in the closed unit ball
// D^(n + 1): a vector of norm 1 has norm at most 1.
var SphereSubsetBall = sphereSubsetBallThm{family.Add(registry.ProofEntry{
	Name: "SphereSubsetBall",
	Key:  "prop_a1af5ff4252e3ba2",
	Build: family.Theorem(
		"∀n:num. euclidean_sphere(n) ⊆ euclidean_ball(n + 1)",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"a vector of norm 1 has norm at most 1",
				BySets(
					EuclideanSphereDef.At(n),
					EuclideanBallDef.At(a.TermAs[Nat]("n + 1")),
					real_order_ring.LessEqRefl))
		}),
})}

// BallMinusSphere — what the closed unit ball D^(n + 1) holds besides the
// sphere Sⁿ is the open unit ball: a norm at most 1 and other than 1 is
// below 1.
var BallMinusSphere = ballMinusSphereThm{family.Add(registry.ProofEntry{
	Name: "BallMinusSphere",
	Key:  "prop_aca5225afe012f4a",
	Build: family.Theorem(
		"∀n:num. "+
			"    euclidean_ball(n + 1) ∖ euclidean_sphere(n) = "+
			"    {u:(num → real) | vec⟨n + 1⟩(u) ∧ ‖u‖_(n + 1) < &1}",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"a norm at most 1 and other than 1 is below 1",
				BySets(
					EuclideanBallDef.At(a.TermAs[Nat]("n + 1")),
					EuclideanSphereDef.At(n),
					real_order_ring.LessThanSplit))
		}),
})}

// SphereCompact — the unit sphere Sⁿ is compact. It is the set of points
// of ℝⁿ⁺¹ of norm exactly 1, the preimage of the closed interval ⟦1, 1⟧
// under the continuous norm, so it is closed; and it lies in the compact
// ball D^(n + 1).
var SphereCompact = sphereCompactThm{family.Add(registry.ProofEntry{
	Name: "SphereCompact",
	Key:  "prop_b0ccfd5b12f1308c",
	Build: family.Theorem(
		"∀n:num. compact_in(euclidean_topology(n + 1), euclidean_sphere(n))",
		func(a *Argument, n *Expr[Nat]) {
			preimage := a.Have(
				"the sphere is the set of points of ℝⁿ⁺¹ whose norm lies in ⟦1, 1⟧",
				"euclidean_sphere(n) = "+
					"preimage_on(⋃euclidean_topology(n + 1), λx:(num → real). ‖x‖_(n + 1), ⟦&1, &1⟧)",
				BySets(
					EuclideanSphereDef.At(n),
					EuclideanSpace.At(a.TermAs[Nat]("n + 1")),
					real_construction.LessEqAntisym))
			closed := a.Have(
				"so it is closed, the norm being continuous",
				"closed_in(euclidean_topology(n + 1), euclidean_sphere(n))",
				preimage.Rw(),
				By(
					NormContinuous.At(a.TermAs[Nat]("n + 1")),
					continuous.ClosedPreimage.At(
						a.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n + 1)"),
						a.TermAs[Set[Set[Real]]]("real_topology"),
						a.TermAs[Fun[Fun[Nat, Real], Real]]("λx:(num → real). ‖x‖_(n + 1)")),
					real_topology.ClosedIntervalClosed.At(a.TermAs[Real]("&1"), a.TermAs[Real]("&1"))))
			a.Show(
				"a closed set inside the compact ball is compact",
				By(
					closed,
					SphereSubsetBall.At(n),
					BallCompact.At(a.TermAs[Nat]("n + 1")),
					compact.ClosedSubsetCompact))
		}),
})}
