// path_component.go — the path component of a point, the points a path
// joins to it. A constant map is a path and a path run backwards is one,
// so with the joining of paths the relation is an equivalence and the
// path components partition the space; each is path-connected, the
// largest path-connected set about its point, and lies in the point's
// connected component. Where every point has a base of path-connected
// open neighbourhoods the path components are open, so they are the
// connected components, and a connected space is path-connected. The
// product of two path-connected sets is path-connected, the pair of a path
// in each being a path in the product.

package path_connected

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Constant and reversed paths
// ---------------------------------------------------------------------------

// PathConstant — the constant map at a point of the space is a path: the
// unit interval, a subspace of the line, is a topology, and a constant map
// from a topology to a point of the space is continuous.
var PathConstant = pathConstantThm{family.Add(registry.ProofEntry{
	Name: "PathConstant",
	Key:  "prop_ed0e376d09a4981a",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "path_in(T, λt:real. x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A], inSpace Fact) {
			a.Do(Unfold(PathInDef))
			a.Show(
				"the unit interval is a topology, a subspace of the line, and "+
					"a constant map from it to a point of the space is continuous",
				By(
					inSpace,
					continuous.Constant,
					topological_space.SubtopologyTopology.Read(real_topology.RealTopology)))
		}),
})}

// PathReverse — a path run backwards is a path: t ↦ 1 − t is a polynomial,
// so continuous on the line, and it keeps ⟦0, 1⟧ in itself, so it is
// continuous from the unit interval to itself; the path after it is
// continuous by composition.
var PathReverse = pathReverseThm{family.Add(registry.ProofEntry{
	Name: "PathReverse",
	Key:  "prop_632e7fa9fe8a0a35",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "path_in(T, λt:real. g(&1 - t))",
		Abbrev: Abbrev{
			{Name: "reversal", Text: "λt:real. &1 - t"},
		},
	},
		func(a *Argument, T *Expr[Set[Set[A]]], g *Arrow[Real, A], path Fact) {
			reversal := a.TermAs[Fun[Real, Real]]("«reversal»")
			onLine := a.Have(
				"t ↦ 1 − t, the constant 1 less the identity, is a polynomial, so continuous on the line",
				"continuous_map(real_topology, real_topology, «reversal»)",
				By(
					real_continuous.PolynomialFunctionContinuous.At(reversal),
					real_polynomial.Sub.At(
						a.TermAs[Fun[Real, Real]]("λt:real. &1"),
						a.TermAs[Fun[Real, Real]]("λt:real. t")),
					real_polynomial.Const,
					real_polynomial.Id))
			staysInside := a.Have(
				"t ↦ 1 − t keeps the points of the unit interval in it",
				"∀x:real. x ∈ ⋃subtopology(real_topology, ⟦&0, &1⟧) ⇒ &1 - x ∈ ⟦&0, &1⟧",
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					inSubspace := b.Assume()
					inUnit := b.Have(
						"a point of the subspace lies between 0 and 1",
						"&0 ≤ x ∧ x ≤ &1",
						BySets(
							inSubspace,
							topological_space.SubtopologySpace.At(
								b.TermAs[Set[Set[Real]]]("real_topology"),
								b.TermAs[Set[Real]]("⟦&0, &1⟧"))))
					b.Show(
						"so does 1 − x",
						ByArith(inUnit))
				}))
			reflect := a.Have(
				"so t ↦ 1 − t is continuous from the unit interval into itself",
				"continuous_map(subtopology(real_topology, ⟦&0, &1⟧), "+
					"    subtopology(real_topology, ⟦&0, &1⟧), "+
					"    «reversal»)",
				By(continuous.FromSubtopology.Read(onLine), staysInside, continuous.IntoSubtopology))
			composite := a.Have(
				"g after it is continuous from the unit interval into the space, by composition",
				"continuous_map(subtopology(real_topology, ⟦&0, &1⟧), T, g ∘ «reversal»)",
				By(path, PathInDef, continuous.Compose.Read(reflect)))
			a.Show(
				"and g after t ↦ 1 − t is g run backwards",
				By(composite, PathInDef, functions.ComposeApply))
		}),
})}

// ---------------------------------------------------------------------------
// Path components
// ---------------------------------------------------------------------------

// PathComponentSubsetSpace — a path component lies in the space: its
// points are the ends g(1) of paths, values of a continuous map from the
// unit interval at one of its points.
var PathComponentSubsetSpace = pathComponentSubsetSpaceThm{family.Add(registry.ProofEntry{
	Name: "PathComponentSubsetSpace",
	Key:  "prop_b6b29cc04e592da",
	Build: family.Theorem("∀T:set(set(A)). ∀x:A. path_component(T, x) ⊆ ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A]) {
			a.Do(Simp(Fwd(set_basic.SubsetDef)))
			a.FixAs[A]("y")
			joined := a.Assume()
			_, path := a.UnpackAs[Fun[Real, A]](a.Unfolded(joined, PathComponentDef), "g")
			parts := a.Conjuncts(
				path,
				"g is a path",
				"it starts at x",
				"it ends at y")
			one := a.TermAs[Real]("&1")
			a.Show(
				"y = g(1) is the value of the continuous g at a point of ⟦0, 1⟧, so a point of the space",
				ByArith(
					parts[2],
					continuous.MapsInto.Read(a.Unfolded(parts[0], PathInDef)).At(one),
					UnitIntervalPoints.At(one)))
		}),
})}

// PathComponentSelfIff — a point lies in its own path component exactly
// when it is a point of the space: a path component lies in the space,
// and the constant path joins a point of the space to itself.
var PathComponentSelfIff = pathComponentSelfIffThm{family.Add(registry.ProofEntry{
	Name: "PathComponentSelfIff",
	Key:  "prop_11ec4bc3602f484c",
	Build: family.Theorem("∀T:set(set(A)). ∀x:A. x ∈ path_component(T, x) ⇔ x ∈ ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A]) {
			a.Iff()
			a.Forward(
				"a path component lies in the space",
				func(b *Argument, own Fact) {
					b.Show(
						"so x, a point of its own, is a point of the space",
						By(own, PathComponentSubsetSpace.At(T, x), set_basic.SubsetDef))
				})
			a.Backward(
				"the constant path at x joins x to itself",
				func(b *Argument, inSpace Fact) {
					b.Show(
						"so x lies in its own path component",
						Simp(Fwd(PathComponentDef)),
						BySets(inSpace, PathConstant.At(T, x)))
				})
		}),
})}

// PathComponentSym — if a path joins x to y, one joins y to x: the path
// run backwards.
var PathComponentSym = pathComponentSymThm{family.Add(registry.ProofEntry{
	Name: "PathComponentSym",
	Key:  "prop_5d423a3e1c4f5fc9",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀x y:A.",
		Hypotheses: []string{
			"y ∈ path_component(T, x)",
		},
		Conclusion: "x ∈ path_component(T, y)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], x, y *Expr[A], joined Fact) {
			g, path := a.UnpackAs[Fun[Real, A]](a.Unfolded(joined, PathComponentDef), "g")
			parts := a.Conjuncts(
				path,
				"g is a path",
				"it starts at x",
				"it ends at y")
			ends := a.Have(
				"run backwards, g starts at g(1) = y and ends at g(0) = x",
				"g(&1 - &0) = y ∧ g(&1 - &1) = x",
				By(parts[1], parts[2], real_ring.SubRightZero, real_ring.SubRefl))
			a.Show(
				"so g run backwards is a path from y to x",
				Simp(Fwd(PathComponentDef)),
				BySets(PathReverse.At(T, g), parts[0], ends))
		}),
})}

// PathComponentTrans — paths from x to y and from y to z give one from
// x to z: the second joined to the first.
var PathComponentTrans = pathComponentTransThm{family.Add(registry.ProofEntry{
	Name: "PathComponentTrans",
	Key:  "prop_f5a1b55f31b1abec",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀x y z:A.",
		Hypotheses: []string{
			"y ∈ path_component(T, x)",
			"z ∈ path_component(T, y)",
		},
		Conclusion: "z ∈ path_component(T, x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], x, y, z *Expr[A], toY, toZ Fact) {
			g, first := a.UnpackAs[Fun[Real, A]](a.Unfolded(toY, PathComponentDef), "g")
			gParts := a.Conjuncts(
				first,
				"g is a path",
				"it starts at x",
				"it ends at y")
			h, second := a.UnpackAs[Fun[Real, A]](a.Unfolded(toZ, PathComponentDef), "h")
			hParts := a.Conjuncts(
				second,
				"h is a path",
				"it starts at y",
				"it ends at z")
			meet := a.Have(
				"g ends where h begins, at y",
				"g(&1) = h(&0)",
				By(Normalized, gParts[2], hParts[1]))
			a.Show(
				"so the joined path, a path from g(0) = x to h(1) = z, puts z in the path component of x",
				Simp(Fwd(PathComponentDef)),
				BySets(
					PathJoin.At(T, g, h),
					gParts[0],
					hParts[0],
					meet,
					PathJoinEnds.At(
						g, h, a.TermAs[Fun[Real, A]]("λt:real. COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1))")),
					gParts[1],
					hParts[2]))
		}),
})}

// PathComponentEq — a point of x's path component has x's path component:
// a point joined to it is joined to x through it, and a point joined to x
// is joined to it through x.
var PathComponentEq = pathComponentEqThm{family.Add(registry.ProofEntry{
	Name: "PathComponentEq",
	Key:  "prop_ff9809cdabb4ea0a",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀x y:A.",
		Hypotheses: []string{
			"y ∈ path_component(T, x)",
		},
		Conclusion: "path_component(T, y) = path_component(T, x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], x, y *Expr[A], joined Fact) {
			a.Show(
				"a path joins x to y and y back to x, so a point joined to either is joined to the other",
				BySets(joined, PathComponentSym.At(T, x, y), PathComponentTrans))
		}),
})}

// PathImageSubsetComponent — the values of a path lie in the path
// component of its start: the value g(t) is reached from g(0) by the path
// run up to time t, s ↦ g(t · s), the path after a map of the line that
// keeps ⟦0, 1⟧ in itself.
var PathImageSubsetComponent = pathImageSubsetComponentThm{family.Add(registry.ProofEntry{
	Name: "PathImageSubsetComponent",
	Key:  "prop_51a7d00b7a4f17b1",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "image(g, ⟦&0, &1⟧) ⊆ path_component(T, g(&0))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], g *Arrow[Real, A], path Fact) {
			a.Do(Simp(Fwd(set_image.ImageSubsetIff)))
			t := a.FixAs[Real]("t")
			tIn := a.Assume()
			onLine := a.Have(
				"s ↦ t · s, a multiple of the identity, is a polynomial, so continuous on the line",
				"continuous_map(real_topology, real_topology, λs:real. t * s)",
				By(
					real_continuous.PolynomialFunctionContinuous.At(a.TermAs[Fun[Real, Real]]("λs:real. t * s")),
					real_polynomial.ScalarLeft.At(a.TermAs[Fun[Real, Real]]("λs:real. s"), t),
					real_polynomial.Id))
			bounded := a.Have(
				"for s in ⟦0, 1⟧, t · s lies in ⟦0, 1⟧, as t does",
				"∀s:real. s ∈ ⟦&0, &1⟧ ⇒ &0 ≤ t * s ∧ t * s ≤ &1",
				ByArith(tIn))
			runUpToT := a.Have(
				"so g run up to time t, s ↦ g(t · s), is a path",
				"path_in(T, λs:real. g(t * s))",
				By(PathReparametrise, path, onLine, bounded, PathInDef))
			ends := a.Have(
				"it runs from g(t · 0) = g(0) to g(t · 1) = g(t)",
				"g(t * &0) = g(&0) ∧ g(t * &1) = g(t)",
				ByArith())
			a.Show(
				"so g(t) lies in the path component of g(0)",
				Simp(Fwd(PathComponentDef)),
				BySets(runUpToT, ends))
		}),
})}

// PathComponentPathConnected — a path component is path-connected: two of
// its points y, z are joined through x by a path from y to z, whose values
// lie in the path component of its start y, which is that of x.
var PathComponentPathConnected = pathComponentPathConnectedThm{family.Add(registry.ProofEntry{
	Name: "PathComponentPathConnected",
	Key:  "prop_91bacb12c93dc8eb",
	Build: family.Theorem("∀T:set(set(A)). ∀x:A. path_connected_in(T, path_component(T, x))",
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A]) {
			a.Do(
				Simp(Fwd(PathConnectedInDef)),
				SplitConj(
					Case(
						"the path component lies in the space",
						Cite(PathComponentSubsetSpace)),
					Case(
						"two of its points y, z are joined by a path whose values stay in it",
						Derive(func(b *Argument) {
							y := b.FixAs[A]("y")
							z := b.FixAs[A]("z")
							ends := b.Conjuncts(
								b.Assume(),
								"y lies in the path component of x",
								"so does z")
							toZ := b.Have(
								"a path from y to x followed by one from x to z joins y to z",
								"z ∈ path_component(T, y)",
								By(ends[0], ends[1], PathComponentSym.At(T, x, y), PathComponentTrans.At(T, y, x, z)))
							g, joined := b.UnpackAs[Fun[Real, A]](b.Unfolded(toZ, PathComponentDef), "g")
							path := b.Conjuncts(
								joined,
								"g is a path",
								"it starts at y",
								"it ends at z")
							b.Take(g)
							b.Show(
								"g is a path from y to z whose values lie in the path component of g(0) = y, which is that of x",
								By(
									path[0],
									path[1],
									path[2],
									PathImageSubsetComponent.At(T, g),
									ends[0],
									PathComponentEq.At(T, x, y)))
						})),
				))
		}),
})}

// PathComponentMaximal — a path-connected set holding x lies in x's
// path component: each of its points is joined to x by a path in it.
var PathComponentMaximal = pathComponentMaximalThm{family.Add(registry.ProofEntry{
	Name: "PathComponentMaximal",
	Key:  "prop_2aaf42f5e3247494",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A). ∀x:A.",
		Hypotheses: []string{
			"path_connected_in(T, s)",
			"x ∈ s",
		},
		Conclusion: "s ⊆ path_component(T, x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], x *Expr[A], pathConnected, xIn Fact) {
			joins := a.Unfolded(pathConnected, PathConnectedInDef)
			a.Show(
				"a point y of s is joined to x by a path in s, which puts y in the path component of x",
				Simp(Fwd(set_basic.SubsetDef), Fwd(PathComponentDef)),
				BySets(joins, xIn))
		}),
})}

// PathComponentSubsetComponent — a path component lies in the connected
// component: holding a point it holds x, since a path joins x to the point
// and back, and it is path-connected, so a connected set holding x.
var PathComponentSubsetComponent = pathComponentSubsetComponentThm{family.Add(registry.ProofEntry{
	Name: "PathComponentSubsetComponent",
	Key:  "prop_2f8c9da224bbac85",
	Build: family.Theorem("∀T:set(set(A)). ∀x:A. path_component(T, x) ⊆ connected_component(T, x)",
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A]) {
			a.Do(Simp(Fwd(set_basic.SubsetDef)))
			y := a.FixAs[A]("y")
			yIn := a.Assume()
			own := a.Have(
				"x lies in its own path component: a path joins x to y, and one y back to x",
				"x ∈ path_component(T, x)",
				By(yIn, PathComponentSym.At(T, x, y), PathComponentTrans.At(T, x, y, x)))
			a.Show(
				"the path component, path-connected so connected, "+
					"holds x, so lies in the component of x, and y with it",
				By(
					own,
					yIn,
					PathComponentPathConnected.At(T, x),
					PathConnectedConnected,
					connected.ComponentMaximal,
					set_basic.SubsetDef))
		}),
})}

// PathConnectedIffOneComponent — a space is path-connected exactly when
// the path component of each of its points is the whole space: a
// path-connected space holding x lies in x's path component, which lies in
// the space; and a space with a point is that point's path component,
// path-connected, while an empty space is path-connected outright.
var PathConnectedIffOneComponent = pathConnectedIffOneComponentThm{family.Add(registry.ProofEntry{
	Name: "PathConnectedIffOneComponent",
	Key:  "prop_e263bb1919bbb6ca",
	Build: family.Theorem("∀T:set(set(A)). "+
		"    path_connected_in(T, ⋃T) ⇔ ∀x:A. x ∈ ⋃T ⇒ path_component(T, x) = ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Iff()
			a.Forward(
				"in a path-connected space each point's path component is the whole space",
				func(b *Argument, pathConnected Fact) {
					x := b.FixAs[A]("x")
					inSpace := b.Assume()
					b.Show(
						"the space is a path-connected set holding x, so it "+
							"lies in x's path component, which lies in the space",
						By(
							PathComponentMaximal.At(T, b.TermAs[Set[A]]("⋃T"), x),
							PathComponentSubsetSpace.At(T, x),
							set_order.SubsetAntisym,
							pathConnected,
							inSpace))
				})
			a.Backward(
				"a space that is the path component of each of its points is path-connected",
				func(b *Argument, oneComponent Fact) {
					b.Cases(b.Term("⋃T = ∅"))
					b.When(
						"an empty space is path-connected: no two points are left to join",
						func(c *Argument, empty Fact) {
							c.Show(
								"the space lies in itself, and holds no points",
								BySets(empty, PathConnectedInDef))
						})
					b.Otherwise(
						"a space with a point is that point's path component",
						func(c *Argument, nonEmpty Fact) {
							x, inSpace := c.ObtainAs[A](
								"a point x of the space",
								"∃x:A. x ∈ ⋃T",
								By(nonEmpty, set_basic.MemberNotEmpty))
							c.Show(
								"the space is x's path component, which is path-connected",
								By(Normalized, oneComponent.At(x), inSpace, PathComponentPathConnected.At(T, x)))
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// Locally path-connected spaces
// ---------------------------------------------------------------------------

// LocallyPathConnectedImpLocallyConnected — a locally path-connected
// space is locally connected: the path-connected open neighbourhood inside
// an open set about a point is a connected one.
var LocallyPathConnectedImpLocallyConnected = locallyPathConnectedImpLocallyConnectedThm{family.Add(registry.ProofEntry{
	Name: "LocallyPathConnectedImpLocallyConnected",
	Key:  "prop_e13e182fffec329",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"locally_path_connected_space(T)",
		},
		Conclusion: "locally_connected_space(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], locally Fact) {
			neighbourhoods := a.Unfolded(locally, LocallyPathConnectedSpaceDef)
			a.Show(
				"an open set about a point holds a path-connected open neighbourhood of it, which is connected",
				Unfold(connected.LocallyConnectedSpaceDef),
				By(neighbourhoods, PathConnectedConnected))
		}),
})}

// LocallyPathConnectedComponentOpen — in a locally path-connected space
// every path component is open. A point y of x's path component is a point
// of the space, and the space is open, so some path-connected open v holds
// y; v lies in y's path component, which is x's. So each point of the path
// component lies in an open set inside it, and the path component is open
// by the pointwise criterion.
var LocallyPathConnectedComponentOpen = locallyPathConnectedComponentOpenThm{family.Add(registry.ProofEntry{
	Name: "LocallyPathConnectedComponentOpen",
	Key:  "prop_ef09f569876ce7b9",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"locally_path_connected_space(T)",
		},
		Conclusion: "path_component(x) ∈ T",
	},
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], x *Expr[A], locally Fact) {
			T := a.TermAs[Set[Set[A]]]("T")
			neighbourhoods := a.Unfolded(locally, LocallyPathConnectedSpaceDef)
			near := a.Have(
				"each point of the path component lies in an open set inside it",
				"∀y:A. y ∈ path_component(x) ⇒ ∃v:set(A). v ∈ T ∧ v ⊆ path_component(x) ∧ y ∈ v",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					inComponent := b.Assume()
					v, around := b.ObtainAs[Set[A]](
						"y is a point of the open space, so some path-connected open v holds y",
						"∃v:set(A). v ∈ T ∧ path_connected_in(v) ∧ y ∈ v ∧ v ⊆ ⋃T",
						BySets(
							neighbourhoods.At(b.TermAs[Set[A]]("⋃T"), y),
							topological_space.SpaceOpen.Read(topology),
							inComponent,
							PathComponentSubsetSpace.At(T, x)))
					b.Take(v)
					b.Show(
						"v is a path-connected set holding y, so it lies in y's path component, which is x's",
						By(Normalized, around, inComponent, PathComponentMaximal.At(T, v, y), PathComponentEq.At(T, x, y)))
				}))
			a.Show(
				"so the path component is open, by the pointwise criterion",
				By(topological_space.OpenPointwise.Read(topology), near))
		}),
})}

// LocallyPathConnectedComponentsAgree — in a locally path-connected
// space the path components are the connected components. The path
// component of x is open, and so is the path component of each point of
// the space outside it, which misses it; so the rest of the space is open
// and the path component is closed. The connected component of x,
// connected, then lies in the path component or misses it: it meets it at
// x when x is a point of the space, and is empty when x is not. The other
// inclusion holds in any space.
var LocallyPathConnectedComponentsAgree = locallyPathConnectedComponentsAgreeThm{family.Add(registry.ProofEntry{
	Name: "LocallyPathConnectedComponentsAgree",
	Key:  "prop_4c6f2a36e17f3cea",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"locally_path_connected_space(T)",
		},
		Conclusion: "path_component(x) = connected_component(x)",
	},
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], x *Expr[A], locally Fact) {
			T := a.TermAs[Set[Set[A]]]("T")
			componentsOpen := LocallyPathConnectedComponentOpen.Read(topology)
			rest := a.Have(
				"a point z of the space outside x's path component has "+
					"an open set about it outside it: its own path component",
				"∀z:A. z ∈ ⋃T ∖ path_component(x) ⇒ ∃v:set(A). v ∈ T ∧ v ⊆ ⋃T ∖ path_component(x) ∧ z ∈ v",
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					outside := b.Assume()
					b.Take(b.TermAs[Set[A]]("path_component(z)"))
					b.Show(
						"the path component of z is open, lies in the rest of the space, and holds z",
						SplitConjAll(
							Case(
								"it is open, the space being locally path-connected",
								By(locally, componentsOpen.At(z))),
							Case(
								"it lies in the space and misses x's path component, since a point of both would join z to x",
								BySets(outside, PathComponentSubsetSpace.At(T, z), PathComponentSym, PathComponentTrans)),
							Case(
								"it holds z, a point of the space",
								BySets(outside, PathComponentSelfIff))))
				}))
			closed := a.Have(
				"so the rest of the space is open, by the pointwise criterion, and x's path component is closed",
				"closed_in(path_component(x))",
				By(
					rest,
					topological_space.OpenPointwise.Read(topology),
					topological_space.ClosedInDef,
					PathComponentSubsetSpace))
			split := a.Have(
				"the connected component of x, a connected set, lies "+
					"in the open and closed path component or misses it",
				"connected_component(x) ⊆ path_component(x) ∨ connected_component(x) ∩ path_component(x) = ∅",
				By(
					locally,
					closed,
					connected.ConnectedClopen.At(
						T,
						a.TermAs[Set[A]]("connected_component(x)"),
						a.TermAs[Set[A]]("path_component(x)")),
					connected.ComponentConnected.At(T, x),
					componentsOpen.At(x)))
			a.Show(
				"the path component lies in the connected one, and they meet "+
					"at x when x is a point of the space; else both are empty",
				BySets(
					split,
					PathComponentSubsetComponent.At(T, x),
					PathComponentSelfIff.At(T, x),
					connected.ComponentEmptyIff.At(T, x)))
		}),
})}

// ConnectedLocallyPathConnected — a connected locally path-connected
// space is path-connected: the connected component of each point is the
// whole space, and in a locally path-connected space it is the point's path
// component.
var ConnectedLocallyPathConnected = connectedLocallyPathConnectedThm{family.Add(registry.ProofEntry{
	Name: "ConnectedLocallyPathConnected",
	Key:  "prop_250895f4bef11a67",
	Build: topological_space.IsTopology.Law(Statement{
		Hypotheses: []string{
			"locally_path_connected_space(T)",
			"connected_in(⋃T)",
		},
		Conclusion: "path_connected_in(⋃T)",
	},
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], locally, connectedSpace Fact) {
			T := a.TermAs[Set[Set[A]]]("T")
			a.Show(
				"each point's path component is its connected component, which is the whole connected space",
				By(
					locally,
					connectedSpace,
					PathConnectedIffOneComponent.At(T),
					connected.ConnectedIffOneComponent.At(T),
					LocallyPathConnectedComponentsAgree.Read(topology)))
		}),
})}

// ---------------------------------------------------------------------------
// Products
// ---------------------------------------------------------------------------

// PathConnectedProduct — the product of two path-connected sets is
// path-connected: two points of the rectangle are joined by the pair of a
// path in k between their first coordinates and a path in l between their
// second, continuous into the product because its components are.
var PathConnectedProduct = pathConnectedProductThm{family.Add(registry.ProofEntry{
	Name: "PathConnectedProduct",
	Key:  "prop_89dc896a2759d954",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀k:set(A). ∀l:set(B).",
		Hypotheses: []string{
			"path_connected_in(T, k)",
			"path_connected_in(S, l)",
		},
		Conclusion: "path_connected_in(product_topology(T, S), set_cross(k, l))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			k *Expr[Set[A]],
			l *Expr[Set[B]],
			kConnected, lConnected Fact,
		) {
			kParts := a.Conjuncts(
				a.Unfolded(kConnected, PathConnectedInDef),
				"k lies in the first space",
				"a path in k joins any two points of k")
			lParts := a.Conjuncts(
				a.Unfolded(lConnected, PathConnectedInDef),
				"l lies in the second space",
				"a path in l joins any two points of l")
			a.Do(
				Simp(Fwd(PathConnectedInDef)),
				SplitConj(
					Case(
						"the rectangle lies in the points of the product, the rectangle of the two spaces' points",
						By(
							Normalized,
							kParts[0],
							lParts[0],
							product_topology.ProductSpace.At(T, S),
							set_product.CrossSubsetIff.At(k, a.TermAs[Set[A]]("⋃T"), l, a.TermAs[Set[B]]("⋃S")))),
					Case(
						"two points (x₁, y₁), (x₂, y₂) of the rectangle are "+
							"joined by the pair of a path in k and a path in l",
						Simp(Fwd(pairs.ForallPair), Fwd(set_product.InCross)),
						Derive(func(b *Argument) {
							x1 := b.FixAs[A]("x₁")
							y1 := b.FixAs[B]("y₁")
							x2 := b.FixAs[A]("x₂")
							y2 := b.FixAs[B]("y₂")
							ends := b.Conjuncts(
								b.Assume(),
								"x₁ lies in k",
								"y₁ lies in l",
								"x₂ lies in k",
								"y₂ lies in l")
							g, first := b.UnpackAs[Fun[Real, A]](GroupPremises(ends[0], ends[2], kParts[1].At(x1, x2)), "g")
							gParts := b.Conjuncts(
								first,
								"g is a path",
								"its values lie in k",
								"it starts at x₁",
								"it ends at x₂")
							h, second := b.UnpackAs[Fun[Real, B]](GroupPremises(ends[1], ends[3], lParts[1].At(y1, y2)), "h")
							hParts := b.Conjuncts(
								second,
								"h is a path",
								"its values lie in l",
								"it starts at y₁",
								"it ends at y₂")
							unitTopology := b.Have(
								"the unit interval, a subspace of the line, is a topology",
								"is_topology(subtopology(real_topology, ⟦&0, &1⟧))",
								Cite(topological_space.SubtopologyTopology.Read(real_topology.RealTopology)))
							b.Take(b.TermAs[Fun[Real, Prod[A, B]]]("λt:real. (g(t), h(t))"))
							b.Show(
								"t ↦ (g(t), h(t)) is a path in the rectangle from (x₁, y₁) to (x₂, y₂)",
								SplitConjAll(
									Case(
										"it is continuous from the unit interval into the product, as its components g and h are",
										Simp(
											Fwd(PathInDef),
											Fwd(unitTopology),
											Fwd(product_topology.PairedContinuousIff),
											Fwd(pairs.Fst),
											Fwd(pairs.Snd)),
										By(gParts[0], hParts[0], PathInDef.At(T, g), PathInDef.At(S, h))),
									Case(
										"its values pair a value of g, in k, with a value of h, in l",
										BySets(gParts[1], hParts[1], set_product.InCross)),
									Case(
										"it starts at (g(0), h(0)) = (x₁, y₁)",
										By(Normalized, gParts[2], hParts[2])),
									Case(
										"it ends at (g(1), h(1)) = (x₂, y₂)",
										By(Normalized, gParts[3], hParts[3]))))
						})),
				))
		}),
})}
