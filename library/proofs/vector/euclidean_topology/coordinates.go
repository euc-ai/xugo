// coordinates.go — a map into ℝⁿ read by its coordinates: each
// coordinate is a continuous real function on ℝⁿ, a map from a space into
// ℝⁿ is continuous exactly when its n coordinates are, and so appending a
// coordinate is continuous from ℝⁿ × ℝ to ℝⁿ⁺¹; the unit cube, cut out of
// ℝⁿ by its coordinates, is closed, and holds the zero vector.

package euclidean_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// CoordinateContinuous — a coordinate below n is a continuous real
// function on ℝⁿ: the gap between two coordinates is at most the distance
// between the vectors, so δ = ε serves at every point.
var CoordinateContinuous = coordinateContinuousThm{family.Add(registry.ProofEntry{
	Name: "CoordinateContinuous",
	Key:  "prop_4d9ce801361b1735",
	Build: family.Theorem(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i < n",
		},
		Conclusion: "continuous_map(euclidean_topology(n), real_topology, λx:(num → real). x(i))",
	}, func(a *Argument, n, i *Expr[Nat], below Fact) {
		gap := a.Have(
			"a coordinate gap is at most the distance",
			"∀x y:(num → real). dist(x(i), y(i)) ≤ dist⟨n⟩(x, y)",
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, Real]]("x")
				b.FixAs[Fun[Nat, Real]]("y")
				b.Show(
					"the coordinate i of x - y is at most its norm",
					By(
						below,
						euclidean.ComponentLeNorm.At(i, b.VecAt[Real](n, "x - y")),
						vec_space.VecSubDef,
						euclidean.VecDistDef,
						real_sgn_abs.RealDistDef))
			}))
		near := a.Have(
			"within ε of x in ℝⁿ the coordinate is within ε of x(i)",
			Statement{
				Binders: "∀x:(num → real). ∀ε:real.",
				Hypotheses: []string{
					"vec⟨n⟩(x)",
					"&0 < ε",
				},
				Conclusion: "∃δ:real. " +
					"    &0 < δ ∧ (∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < δ ⇒ dist(x(i), y(i)) < ε)",
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

// ContinuousIffCoordinates — a map from a space into ℝⁿ is continuous
// exactly when it takes its values in ℝⁿ and each of its n coordinates is
// a continuous real function. Forward, a coordinate of the map is the
// coordinate map after it (CoordinateContinuous). Backward, a point x of
// the preimage of an open v has the ball of some radius r about f(x)
// inside v. The points of the space whose n coordinates lie within
// r/(n + 1) of those of f(x) are the space met with n coordinate
// preimages of open intervals, finitely many open sets, so they form an
// open set about x; and f carries it into the ball, each coordinate of
// the difference being at most r/(n + 1) in size, so the distance at
// most n·r/(n + 1) < r (euclidean.CoordinateNormBound).
var ContinuousIffCoordinates = continuousIffCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "ContinuousIffCoordinates",
	Key:  "prop_422066816a38dd61",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀f:(A → num → real).",
		Hypotheses: []string{
			"is_topology(T)",
		},
		Conclusion: "continuous_map(T, euclidean_topology(n), f) ⇔ " +
			"(∀x:A. x ∈ ⋃T ⇒ vec⟨n⟩(f(x))) ∧ (∀i:num. i < n ⇒ continuous_map(T, real_topology, λx:A. f(x)(i)))",
		Abbrev: Abbrev{
			{Name: "radius", Text: "r / (&n + &1)"},
			{Name: "coordinateNear", Text: "λi:num. " +
				"    preimage_on(⋃T, λz:A. f(z)(i), {t:real | |t - f(x)(i)| < «radius»})"},
			{Name: "neighbourhoods", Text: "insert(⋃T, image(«coordinateNear», {i:num | i < n}))"},
		},
	}, func(
		a *Argument,
		n *Expr[Nat],
		T *Expr[Set[Set[A]]],
		f *Arrow[A, Fun[Nat, Real]],
		topology Fact,
	) {
		type point = Fun[Nat, Real]
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		a.Iff()
		a.Forward(
			"a continuous map into ℝⁿ takes its values there, "+
				"and its coordinates are the coordinate maps after it",
			func(b *Argument, continuity Fact) {
				values := b.Have(
					"f carries the points of the space to n-vectors",
					"∀x:A. x ∈ ⋃T ⇒ vec⟨n⟩(f(x))",
					BySets(continuous.MapsInto.Read(continuity), EuclideanSpace.At(n)))
				coordinates := b.Have(
					"the coordinate i of f is the coordinate map at i after f",
					"∀i:num. i < n ⇒ continuous_map(T, real_topology, λx:A. f(x)(i))",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						below := c.Assume()
						c.Show(
							"a composite of continuous maps is continuous",
							By(
								below,
								continuous.Compose.Read(continuity).At(line, c.TermAs[Fun[point, Real]]("λx:(num → real). x(i)")),
								CoordinateContinuous.At(n, i),
								functions.ComposeApply))
					}))
				b.Show(
					"both hold",
					By(values, coordinates))
			})
		a.Backward(
			"about a point of the preimage of an open set, the points "+
				"whose coordinates stay near form an open set inside it",
			func(b *Argument, coordinatewise Fact) {
				parts := b.Conjuncts(
					coordinatewise,
					"f takes its values in ℝⁿ",
					"each coordinate below n is continuous")
				values, coordinates := parts[0], parts[1]
				intoSpace := b.Have(
					"f carries the space into ℝⁿ",
					"∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃euclidean_topology(n)",
					BySets(values, EuclideanSpace.At(n)))
				preimagesOpen := b.Have(
					"the preimage of an open set of ℝⁿ is open",
					"∀v:set(num → real). v ∈ euclidean_topology(n) ⇒ preimage_on(⋃T, f, v) ∈ T",
					Derive(func(c *Argument) {
						v := c.FixAs[Set[point]]("v")
						vOpen := c.Assume()
						local := c.Have(
							"each point of the preimage lies in an open set inside it",
							"∀x:A. x ∈ preimage_on(⋃T, f, v) ⇒ ∃u:set(A). u ∈ T ∧ u ⊆ preimage_on(⋃T, f, v) ∧ x ∈ u",
							Derive(func(d *Argument) {
								d.FixAs[A]("x")
								at := d.Conjuncts(
									d.Have(
										"x is a point of the space whose image lies in v",
										"x ∈ ⋃T ∧ f(x) ∈ v",
										BySets(d.Assume())),
									"x is a point of the space",
									"f(x) lies in v")
								_, ball := d.ObtainAs[Real](
									"v holds the ball of some radius r about f(x)",
									"∃r:real. &0 < r ∧ (∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(f(x), y) < r ⇒ y ∈ v)",
									By(vOpen, at[1], OpenIff.At(n, v)))
								radius := d.Conjuncts(
									ball,
									"r is positive",
									"the ball of radius r about f(x) lies in v")
								rho := d.TermAs[Real]("«radius»")
								fx := d.TermAs[point]("f(x)")
								nearOpen := d.Have(
									"the points of the space whose coordinate i lies within r/(n + 1) of that of f(x) form an open set",
									"∀i:num. i < n ⇒ «coordinateNear»(i) ∈ T",
									Derive(func(e *Argument) {
										i := e.FixAs[Nat]("i")
										below := e.Assume()
										e.Show(
											"the preimage of an open interval under the continuous coordinate i",
											By(
												coordinates.At(i),
												below,
												continuous.ContinuousMap,
												real_topology.BallOpen.At(e.TermAs[Real]("f(x)(i)"), rho)))
									}))
								finitelyMany := d.Have(
									"the space and the n coordinate neighbourhoods are finitely many sets, at least one",
									"finite(«neighbourhoods») ∧ ¬(«neighbourhoods» = ∅)",
									Simp(Fwd(finite_set.FiniteInsert), Fwd(set_algebra.InsertNotEmpty)),
									By(finite_set.FiniteImage, num_segment.FiniteBelowStrict.At(n)))
								allOpen := d.Have(
									"each of them is open, the space too",
									"«neighbourhoods» ⊆ T",
									Simp(Fwd(set_order.InsertSubset), Fwd(set_image.ImageSubsetIff)),
									By(nearOpen, topological_space.SpaceOpen.Read(topology)))
								meetOpen := d.Have(
									"so they meet in an open set",
									"⋂«neighbourhoods» ∈ T",
									By(finitelyMany, allOpen, topological_space.IntersOpen.Read(topology)))
								centre := d.Have(
									"each coordinate of f(x) lies within r/(n + 1) of itself",
									"∀i:num. |f(x)(i) - f(x)(i)| < «radius»",
									ByArith(radius[0], real_sgn_abs.AbsOfZero, real_ring.SubRefl))
								xIn := d.Have(
									"x lies in the meet",
									"x ∈ ⋂«neighbourhoods»",
									Simp(Fwd(set_algebra.IntersInsert), Fwd(set_image.IntersImage)),
									BySets(at[0], centre))
								estimate := d.Have(
									"a point of the space whose n coordinates lie within r/(n + 1) of those of f(x) has its image in v",
									"∀y:A. y ∈ ⋃T ∧ (∀i:num. i < n ⇒ |f(y)(i) - f(x)(i)| < «radius») ⇒ f(y) ∈ v",
									Derive(func(e *Argument) {
										y := e.FixAs[A]("y")
										nearby := e.Conjuncts(
											e.Assume(),
											"y is a point of the space",
											"the n coordinates of f(y) lie within r/(n + 1) of those of f(x)")
										fy := e.TermAs[point]("f(y)")
										gaps := e.Have(
											"every coordinate of f(y) - f(x) is at most r/(n + 1) in size",
											"∀i:num. i < n ⇒ |(f(y) - f(x))(i)| ≤ «radius»",
											Derive(func(g *Argument) {
												i := g.FixAs[Nat]("i")
												below := g.Assume()
												g.Show(
													"its coordinate i is the gap between f(y)(i) and f(x)(i)",
													ByArith(nearby[1].At(i), below, vec_space.VecSubDef.At(g.TermAs[Op[Real]]("real_sub"), fy, fx, i)))
											}))
										bound := e.Have(
											"so f(y) - f(x) has norm at most n·r/(n + 1)",
											"‖f(y) - f(x)‖_n ≤ &n * «radius»",
											By(gaps, euclidean.CoordinateNormBound.At(e.VecAt[Real](n, "f(y) - f(x)"), rho)))
										close := e.Have(
											"which puts f(y) within r of f(x)",
											"dist⟨n⟩(f(x), f(y)) < r",
											ByArith(
												bound,
												radius[0],
												real_order_ring.NumNonneg.At(n),
												euclidean.DistSym.At(e.VecAt[Real](n, "f(x)"), e.VecAt[Real](n, "f(y)")),
												euclidean.VecDistDef.At(e.VecAt[Real](n, "f(y)"), e.VecAt[Real](n, "f(x)"))))
										e.Show(
											"so f(y) lies in the ball about f(x), inside v",
											By(values.At(y), nearby[0], radius[1].At(fy), close))
									}))
								inside := d.Have(
									"the meet lies in the preimage",
									"⋂«neighbourhoods» ⊆ preimage_on(⋃T, f, v)",
									Simp(Fwd(set_algebra.IntersInsert), Fwd(set_image.IntersImage)),
									BySets(estimate))
								d.Take(d.TermAs[Set[A]]("⋂«neighbourhoods»"))
								d.Show(
									"the meet is an open set about x inside the preimage",
									By(meetOpen, inside, xIn))
							}))
						c.Show(
							"so the preimage is open, by the pointwise criterion",
							By(topological_space.OpenPointwise.Read(topology), local))
					}))
				b.Show(
					"which is continuity",
					By(continuous.ContinuousMap, intoSpace, preimagesOpen))
			})
	}),
})}

// AppendCoordinateVec — appending a coordinate at n to an n-vector gives an
// (n + 1)-vector: past n both are zero.
var AppendCoordinateVec = appendCoordinateVecThm{family.Add(registry.ProofEntry{
	Name: "AppendCoordinateVec",
	Key:  "prop_3bfe0aef2e766df1",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀a:(num → real). ∀t:real.",
		Hypotheses: []string{
			"vec⟨n⟩(a)",
		},
		Conclusion: "vec⟨n + 1⟩(«append»(a, t))",
	}, func(arg *Argument, n *Expr[Nat], a *Expr[Fun[Nat, Real]], t *Expr[Real], short Fact) {
		arg.Show(
			"past n both are zero",
			Unfold(vec_space.VecDef),
			arg.ForEach(func(i *Expr[Nat]) Action { return ByArith(short.At(i)) }))
	}),
})}

// AppendCoordinateContinuous — appending a coordinate is continuous, from
// ℝⁿ × ℝ to ℝⁿ⁺¹: the map takes its values in ℝⁿ⁺¹, its coordinate n is
// the second projection and its coordinate i below n is the coordinate i
// of the first, so each coordinate is continuous, and a map into ℝⁿ⁺¹
// with continuous coordinates is continuous (ContinuousIffCoordinates).
var AppendCoordinateContinuous = appendCoordinateContinuousThm{family.Add(registry.ProofEntry{
	Name: "AppendCoordinateContinuous",
	Key:  "prop_c496f674077117e4",
	Build: family.Theorem(
		"∀n:num. "+
			"    continuous_map(product_topology(euclidean_topology(n), real_topology), "+
			"        euclidean_topology(n + 1), "+
			"        λp:prod(num → real, real). «append»(fst(p), snd(p)))",
		func(a *Argument, n *Expr[Nat]) {
			type point = Fun[Nat, Real]
			type pair = Prod[point, Real]
			space := a.TermAs[Set[Set[point]]]("euclidean_topology(n)")
			line := a.TermAs[Set[Set[Real]]]("real_topology")
			product := a.TermAs[Set[Set[pair]]]("product_topology(euclidean_topology(n), real_topology)")
			topology := a.Have(
				"the product of ℝⁿ and the line is a space",
				"is_topology(product_topology(euclidean_topology(n), real_topology))",
				By(
					product_topology.ProductTopology.At(space, line),
					EuclideanTopology.At(n),
					real_topology.RealTopology))
			values := a.Have(
				"the map carries the product's points to (n + 1)-vectors",
				Statement{
					Binders: "∀p:prod(num → real, real).",
					Hypotheses: []string{
						"p ∈ ⋃product_topology(euclidean_topology(n), real_topology)",
					},
					Conclusion: "vec⟨n + 1⟩(«append»(fst(p), snd(p)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[pair]("p")
					inProduct := b.Assume()
					inSpace := b.Have(
						"its first part is a point of ℝⁿ",
						"fst(p) ∈ ⋃euclidean_topology(n)",
						BySets(inProduct, product_topology.ProductSpace.At(space, line), set_product.InCrossProjections))
					first := b.Have(
						"so it is an n-vector",
						"vec⟨n⟩(fst(p))",
						BySets(inSpace, EuclideanSpace.At(n)))
					b.Show(
						"and appending keeps it a vector",
						By(
							first,
							AppendCoordinateVec.At(proof.Inhabit(b.VecAt[Real](n, "fst(p)"), first), b.TermAs[Real]("snd(p)"))))
				}))
			coordinates := a.Have(
				"each coordinate below n + 1 is continuous",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i < n + 1",
					},
					Conclusion: "continuous_map(product_topology(euclidean_topology(n), real_topology), " +
						"    real_topology, " +
						"    λp:prod(num → real, real). COND(i = n, snd(p), fst(p)(i)))",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					below := b.Assume()
					b.Cases(b.Term("i = n"))
					b.When(
						"the coordinate n is the second projection",
						func(c *Argument, last Fact) {
							c.Show(
								"which is continuous",
								last.Rw(),
								Cite(product_topology.SndContinuous))
						})
					b.Otherwise(
						"a coordinate below n is that coordinate of the first projection",
						func(c *Argument, earlier Fact) {
							inside := c.Have(
								"i is below n",
								"i < n",
								ByArith(below, earlier))
							c.Show(
								"the coordinate map at i after the first projection",
								By(
									earlier,
									inside,
									continuous.Compose.At(
										product,
										space,
										c.TermAs[Fun[pair, point]]("fst"),
										line,
										c.TermAs[Fun[point, Real]]("λx:(num → real). x(i)")),
									product_topology.FstContinuous.At(space, line),
									CoordinateContinuous.At(n, i),
									functions.ComposeApply))
						})
				}))
			a.Show(
				"so the map is continuous, coordinate by coordinate",
				By(
					topology,
					values,
					coordinates,
					ContinuousIffCoordinates.At(
						a.TermAs[Nat]("n + 1"),
						product,
						a.TermAs[Fun2[pair, Nat, Real]]("λp:prod(num → real, real). «append»(fst(p), snd(p))"))))
		}),
})}

// CubeClosed — the unit cube is closed in ℝⁿ: it is ℝⁿ met with the n
// slabs 0 ≤ x(i) ≤ 1, each the preimage of the closed interval ⟦0, 1⟧
// under a continuous coordinate, and an intersection of closed sets is
// closed.
var CubeClosed = cubeClosedThm{family.Add(registry.ProofEntry{
	Name: "CubeClosed",
	Key:  "prop_2ac5821335cec6e1",
	Build: family.Theorem(
		"∀n:num. closed_in(euclidean_topology(n), unit_cube(n))",
		func(a *Argument, n *Expr[Nat]) {
			type point = Fun[Nat, Real]
			space := a.TermAs[Set[Set[point]]]("euclidean_topology(n)")
			line := a.TermAs[Set[Set[Real]]]("real_topology")
			coordinates := a.Have(
				"the points of ℝⁿ whose coordinate i lies in ⟦0, 1⟧ form a closed set",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i < n",
					},
					Conclusion: "closed_in(euclidean_topology(n), " +
						"    preimage_on(⋃euclidean_topology(n), λx:(num → real). x(i), ⟦&0, &1⟧))",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					below := b.Assume()
					b.Show(
						"a coordinate is continuous, and ⟦0, 1⟧ is closed",
						By(
							below,
							CoordinateContinuous.At(n, i),
							continuous.ClosedPreimage.At(space, line, b.TermAs[Fun[point, Real]]("λx:(num → real). x(i)")),
							real_topology.ClosedIntervalClosed.At(b.TermAs[Real]("&0"), b.TermAs[Real]("&1"))))
				}))
			closedSlabs := a.Have(
				"ℝⁿ and the n slabs 0 ≤ x(i) ≤ 1 are closed",
				Statement{
					Binders: "∀c:(num → real) → bool.",
					Hypotheses: []string{
						"c ∈ " +
							"insert(⋃euclidean_topology(n), " +
							"    image(λi:num. preimage_on(⋃euclidean_topology(n), λx:(num → real). x(i), ⟦&0, &1⟧), " +
							"        {i:num | i < n}))",
					},
					Conclusion: "closed_in(euclidean_topology(n), c)",
				},
				Simp(Fwd(set_basic.ForallInInsert), Fwd(set_image.ForallInImage)),
				By(coordinates, topological_space.SpaceClosed, EuclideanTopology.At(n)))
			cubeIsMeet := a.Have(
				"the unit cube is their intersection",
				"unit_cube(n) = "+
					"⋂insert(⋃euclidean_topology(n), "+
					"    image(λi:num. preimage_on(⋃euclidean_topology(n), λx:(num → real). x(i), ⟦&0, &1⟧), "+
					"        {i:num | i < n}))",
				Simp(
					Fwd(set_algebra.IntersInsert),
					Fwd(set_image.IntersImage),
					Fwd(real_topology.RealClosedIntervalDef)),
				BySets(UnitCubeDef.At(n), EuclideanSpace.At(n)))
			a.Show(
				"so the unit cube is closed in ℝⁿ",
				cubeIsMeet.Rw(),
				By(
					closedSlabs,
					set_algebra.InsertNotEmpty,
					topological_space.IntersClosed,
					EuclideanTopology.At(n)))
		}),
})}

// CubeNonempty — the unit cube is not empty: it holds the zero vector,
// whose coordinates 0 lie in ⟦0, 1⟧.
var CubeNonempty = cubeNonemptyThm{family.Add(registry.ProofEntry{
	Name: "CubeNonempty",
	Key:  "prop_8a9cbca40969449",
	Build: family.Theorem(
		"∀n:num. unit_cube(n) ≠ ∅",
		func(a *Argument, n *Expr[Nat]) {
			bounds := a.Have(
				"zero lies in ⟦0, 1⟧",
				"&0 ≤ &0 ∧ &0 ≤ &1",
				ByArith())
			origin := a.Have(
				"the zero tuple lies in the unit cube",
				"(λi:num. &0) ∈ unit_cube(n)",
				BySets(UnitCubeDef.At(n), vec_space.VecDef, bounds))
			a.Show(
				"so the unit cube is not empty",
				By(Normalized, origin, set_basic.MemberNotEmpty))
		}),
})}
