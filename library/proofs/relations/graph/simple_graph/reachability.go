package simple_graph

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// InComponent reads membership in the component of u: z lies in it
// exactly when u and z are vertices and u reaches z.
var InComponent = inComponentThm{family.Add(registry.ProofEntry{
	Name: "InComponent",
	Key:  "prop_aca1743ee4fe8be8",
	Build: family.Theorem("∀V:set(A). ∀R:(A → A → bool). ∀u z:A. "+
		"    z ∈ graph_component(V, R, u) ⇔ u ∈ V ∧ z ∈ V ∧ graph_reachable(V, R, u, z)",
		func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], u, z *Expr[A]) {
			reaches := a.TermAs[Fun2[A, A, Bool]]("graph_reachable(V, R)")
			a.Show(
				"the component is the class of u under reachability restricted to V",
				Simp(Fwd(ComponentDef)),
				By(equivalence.InClassOn.At(V, reaches, u, z)))
		}),
})}

// ComponentInComponents says the component of a vertex is one of the
// components of the graph.
var ComponentInComponents = componentInComponentsThm{family.Add(registry.ProofEntry{
	Name: "ComponentInComponents",
	Key:  "prop_57ab1c61508bc979",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀u:A.",
		Hypotheses: []string{"u ∈ V"},
		Conclusion: "graph_component(V, R, u) ∈ graph_components(V, R)",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], u *Expr[A], inU Fact) {
		reaches := a.TermAs[Fun2[A, A, Bool]]("graph_reachable(V, R)")
		a.Show(
			"the class of a point of V belongs to the quotient of V",
			Simp(Fwd(ComponentDef), Fwd(ComponentsDef)),
			By(inU, equivalence.ClassInQuotientOn.At(V, reaches, u)))
	}),
})}

// AdjacentReachable makes an adjacency a one-step walk in V.
var AdjacentReachable = adjacentReachableThm{family.Add(registry.ProofEntry{
	Name: "AdjacentReachable",
	Key:  "prop_83b2240ab01953c0",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀u v:A.",
		Hypotheses: []string{"u ∈ V", "v ∈ V", "R(u, v)"},
		Conclusion: "graph_reachable(V, R, u, v)",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		u, v *Expr[A],
		inU, inV, adjacent Fact,
	) {
		restricted := a.TermAs[Fun2[A, A, Bool]]("relation_on(V, R)")
		step := a.Have(
			"the adjacency lies in the restricted relation",
			"relation_on(V, R, u, v)",
			By(inU, inV, adjacent, equivalence.RelationOnDef.At(V, R, u, v)))
		a.Show(
			"one adjacency belongs to the transitive closure",
			Unfold(ReachableDef),
			Unfold(closure.ReflexiveTransitiveClosureDef),
			By(step, closure.TransitiveClosureRules.At(restricted)))
	}),
})}

// ReachableReflexive says every point reaches itself, by the walk with no
// steps.
var ReachableReflexive = reachableReflexiveThm{family.Add(registry.ProofEntry{
	Name: "ReachableReflexive",
	Key:  "prop_eeea2115e74e94c3",
	Build: family.Theorem("∀V:set(A). ∀R:(A → A → bool). ∀u:A. graph_reachable(V, R, u, u)",
		func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], u *Expr[A]) {
			a.Show(
				"the empty walk is the equality disjunct of the reflexive–transitive closure",
				Simp(Fwd(ReachableDef), Fwd(closure.ReflexiveTransitiveClosureDef)),
				Basic())
		}),
})}

// ReachableTransitive says two walks that meet make one: the
// reflexive–transitive closure of the adjacency on V is transitive.
var ReachableTransitive = reachableTransitiveThm{family.Add(registry.ProofEntry{
	Name: "ReachableTransitive",
	Key:  "prop_baf434f039a1b9fa",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀x y z:A.",
		Hypotheses: []string{"graph_reachable(V, R, x, y)", "graph_reachable(V, R, y, z)"},
		Conclusion: "graph_reachable(V, R, x, z)",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], x, y, z *Expr[A], first, second Fact) {
		adjacency := a.TermAs[Fun2[A, A, Bool]]("relation_on(V, R)")
		a.Show(
			"the two stretches of the closure of the adjacency on V compose",
			By(
				first,
				second,
				ReachableDef,
				closure.ReflexiveTransitiveClosureTransitive.At(adjacency, x, y, z)))
	}),
})}

// ReachablePreserves is walk induction: a property that every adjacency
// between vertices carries from its first vertex to its second holds at
// the end of every walk that starts where it holds.
var ReachablePreserves = reachablePreservesThm{family.Add(registry.ProofEntry{
	Name: "ReachablePreserves",
	Key:  "prop_7661e1f2958d7718",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(A). ∀R:(A → A → bool). ∀P:(A → bool). ∀u v:A.",
		Hypotheses: []string{
			"∀x y:A. x ∈ V ∧ y ∈ V ∧ R(x, y) ∧ P(x) ⇒ P(y)",
			"graph_reachable(V, R, u, v)",
			"P(u)",
		},
		Conclusion: "P(v)",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		P *Expr[Set[A]],
		u, v *Expr[A],
		stepPreserves, reaches, start Fact,
	) {
		adjacency := a.TermAs[Fun2[A, A, Bool]]("relation_on(V, R)")
		a.Show(
			"every step of the adjacency on V carries P, so P reaches the end of the closure",
			By(
				stepPreserves,
				reaches,
				start,
				ReachableDef,
				equivalence.RelationOnDef,
				closure.ReflexiveTransitiveClosurePreserves.At(adjacency, P, u, v)))
	}),
})}

// ConnectedCut — a connected graph has an adjacency leaving every
// nonempty proper subset S of its vertices: a walk inside V from a vertex
// of S to a vertex outside it cannot keep every step in S.
var ConnectedCut = connectedCutThm{family.Add(registry.ProofEntry{
	Name: "ConnectedCut",
	Key:  "prop_c49cd1fbca0e2805",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀S:set(A).",
		Hypotheses: []string{"graph_connected(V, R)", "S ⊆ V", "S ≠ ∅", "S ≠ V"},
		Conclusion: "∃x y:A. x ∈ S ∧ y ∈ V ∧ y ∉ S ∧ R(x, y)",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		S *Expr[Set[A]],
		connected, sub, nonempty, proper Fact,
	) {
		u, v, apart := a.Obtain2As[A, A](
			"a vertex in S and a vertex of V outside it",
			"∃u v:A. u ∈ S ∧ v ∈ V ∧ v ∉ S",
			BySets(nonempty, proper, sub))
		walks := a.Unfolded(connected, ConnectedDef)
		walk := a.Have(
			"connectivity joins them by a walk inside V",
			"graph_reachable(V, R, u, v)",
			BySets(apart, sub, walks.At(u, v)))
		none := a.SupposeNot()
		stays := a.Have(
			"with no such adjacency, every step from a vertex of S ends in S",
			"∀x y:A. x ∈ V ∧ y ∈ V ∧ R(x, y) ∧ x ∈ S ⇒ y ∈ S",
			By(none))
		a.Show(
			"and S, which holds u, would hold v at the end of the walk",
			By(stays, apart, walk, ReachablePreserves.At(V, R, a.TermAs[Set[A]]("λx:A. x ∈ S"), u, v)))
	}),
})}

// ConnectedVerticesFinite — a connected graph with finitely many edges
// has finitely many vertices: a vertex with another vertex beside it
// starts a walk, whose first step puts it on an edge, so either V lies in
// the union of the finitely many edges, each a pair, or it has one vertex.
var ConnectedVerticesFinite = connectedVerticesFiniteThm{family.Add(registry.ProofEntry{
	Name: "ConnectedVerticesFinite",
	Key:  "prop_14f5905f46fe48f",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"graph_connected(V, R)", "finite(graph_edges(V, R))"},
		Conclusion: "finite(V)",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], connected, finiteEdges Fact) {
		walks := a.Unfolded(connected, ConnectedDef)
		restricted := a.TermAs[Fun2[A, A, Bool]]("relation_on(V, R)")
		touched := a.Have(
			"a vertex with another vertex beside it lies on an edge",
			"∀x y:A. x ∈ V ∧ y ∈ V ∧ x ≠ y ⇒ x ∈ ⋃graph_edges(V, R)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				y := b.FixAs[A]()
				distinct := b.Assume()
				reaches := b.Have(
					"connectivity supplies a walk from x to y",
					"graph_reachable(V, R, x, y)",
					By(distinct, walks.At(x, y)))
				walk := b.Unfolded(reaches, ReachableDef)
				positive := b.Have(
					"distinct endpoints require a walk with a step",
					"transitive_closure(relation_on(V, R), x, y)",
					By(distinct, b.Unfolded(walk, closure.ReflexiveTransitiveClosureDef)))
				z, step := b.ObtainAs[A](
					"take the first step of the walk",
					"∃z:A. relation_on(V, R, x, z)",
					By(Normalized, positive, closure.CasesRight.At(restricted, x, y)))
				edge := b.Have(
					"the first step is an edge at x",
					"{x, z} ∈ graph_edges(V, R)",
					Unfold(EdgesDef),
					BySets(step, equivalence.RelationOnDef.At(V, R, x, z)))
				b.Show(
					"and x lies on it",
					BySets(edge))
			}))
		a.Cases(a.TermAs[Bool]("V ⊆ ⋃graph_edges(V, R)"))
		a.When(
			"every vertex lies on an edge",
			func(b *Argument, covered Fact) {
				finiteEach := b.Have(
					"each edge is a pair of vertices, a finite set",
					"∀e:set(A). e ∈ graph_edges(V, R) ⇒ finite(e)",
					Unfold(EdgesDef),
					By(finite_set.FiniteInsert, finite_set.FiniteSing))
				b.Show(
					"finitely many finite edges have a finite union, and V lies in it",
					By(
						finiteEdges,
						finiteEach,
						covered,
						finite_set.FiniteFiniteUnions.At(b.TermAs[Set[Set[A]]]("graph_edges(V, R)")),
						finite_set.FiniteSubset.At(V, b.TermAs[Set[A]]("⋃graph_edges(V, R)"))))
			})
		a.Otherwise(
			"some vertex lies on no edge",
			func(b *Argument, uncovered Fact) {
				_, lone := b.Obtain(
					"take a vertex p of V on no edge",
					"∃p:A. p ∈ V ∧ p ∉ ⋃graph_edges(V, R)",
					BySets(uncovered))
				single := b.Have(
					"p is the only vertex: a second one would put p on an edge",
					"V ⊆ {p}",
					BySets(touched, lone))
				b.Show(
					"and a set with at most one point is finite",
					By(single, finite_set.FiniteSubset, finite_set.FiniteSing))
			})
	}),
})}

// ReachableEquivalence makes reachability an equivalence on the vertex
// set. Symmetry of adjacency lets any walk be read in reverse.
var ReachableEquivalence = reachableEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "ReachableEquivalence",
	Key:  "prop_8b14e39337cf449f",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"symmetric_on(V, R)"},
		Conclusion: "equivalence_on(V, graph_reachable(V, R))",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], symmetric Fact) {
		a.Show(
			"reachability is the reflexive–transitive closure of the "+
				"restricted adjacency, which symmetry makes an equivalence on V",
			Unfold(ReachableDef),
			By(symmetric, closure.ReflexiveTransitiveClosureEquivalenceOn.At(V, R)))
	}),
})}

// AdjacentInComponent puts adjacent vertices in one component, the
// component of the first.
var AdjacentInComponent = adjacentInComponentThm{family.Add(registry.ProofEntry{
	Name: "AdjacentInComponent",
	Key:  "prop_3aac00d7265f53f4",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀u v:A.",
		Hypotheses: []string{"u ∈ V", "v ∈ V", "R(u, v)"},
		Conclusion: "∃C:set(A). C ∈ graph_components(V, R) ∧ u ∈ C ∧ v ∈ C",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		u, v *Expr[A],
		inU, inV, adjacent Fact,
	) {
		component := a.TermAs[Set[A]]("graph_component(V, R, u)")
		walk := a.Have(
			"the edge gives a walk from u to v",
			"graph_reachable(V, R, u, v)",
			By(inU, inV, adjacent, AdjacentReachable.At(V, R, u, v)))
		a.Take(component)
		a.Do(SplitConjAll(
			Case(
				"the component of u is one of the components",
				By(inU, ComponentInComponents.At(V, R, u))),
			Case(
				"the component contains its starting point, which u reaches by the empty walk",
				By(inU, ReachableReflexive.At(V, R, u), InComponent.At(V, R, u, u))),
			Case(
				"the component contains its neighbour",
				By(inU, inV, walk, InComponent.At(V, R, u, v))),
		))
	}),
})}

// ComponentsPartition says the components cover V and distinct
// components are disjoint.
var ComponentsPartition = componentsPartitionThm{family.Add(registry.ProofEntry{
	Name: "ComponentsPartition",
	Key:  "prop_257cc086c71e24c0",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"symmetric_on(V, R)"},
		Conclusion: "⋃graph_components(V, R) = V ∧ " +
			"(∀C D:set(A). C ∈ graph_components(V, R) ∧ D ∈ graph_components(V, R) ⇒ C = D ∨ disjoint(C, D))",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], symmetric Fact) {
		equiv := a.Have(
			"reachability is an equivalence on the vertex set",
			"equivalence_on(V, graph_reachable(V, R))",
			By(symmetric, ReachableEquivalence.At(V, R)))
		a.Do(Simp(Fwd(ComponentsDef)), SplitConj(
			Case(
				"the classes of an equivalence cover the carrier",
				Cite(equivalence.QuotientOnCovers.Read(equiv))),
			Case(
				"distinct classes of an equivalence cannot intersect",
				Cite(equivalence.QuotientOnDisjointOrEqual.Read(equiv))),
		))
	}),
})}

// ConnectedIffSingleComponent characterizes connectivity of a nonempty
// graph by its sole component being the whole carrier.
var ConnectedIffSingleComponent = connectedIffSingleComponentThm{family.Add(registry.ProofEntry{
	Name: "ConnectedIffSingleComponent",
	Key:  "prop_8ed4b877338233b3",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"V ≠ ∅"},
		Conclusion: "graph_connected(V, R) ⇔ graph_components(V, R) = {V}",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], nonempty Fact) {
		reaches := a.TermAs[Fun2[A, A, Bool]]("graph_reachable(V, R)")
		a.Iff()
		a.Forward(
			"in a connected graph every component is the whole carrier",
			func(b *Argument, connected Fact) {
				walks := b.Unfolded(connected, ConnectedDef)
				all := b.Have(
					"each vertex has V as its component",
					"∀u:A. u ∈ V ⇒ graph_component(V, R, u) = V",
					b.ForEach(func(u *Expr[A]) Action {
						return Derive(func(c *Argument) {
							inU := c.Assume()
							c.Show(
								"a point lies in the component exactly when it is a vertex",
								BySets(inU, walks.At(u), At(InComponent, V, R, u)))
						})
					}))
				allComponents := b.Have(
					"every component equals the entire vertex set",
					"∀C:set(A). C ∈ graph_components(V, R) ⇒ C = V",
					b.ForEach(func(C *Expr[Set[A]]) Action {
						return Derive(func(c *Argument) {
							component := c.Assume()
							u, represents := c.ObtainAs[A](
								"choose a vertex representing the component",
								"∃u:A. C = graph_component(V, R, u) ∧ u ∈ V",
								Simp(Fwd(ComponentDef)),
								By(component, ComponentsDef.At(V, R), equivalence.InQuotientOn.At(V, reaches, C)))
							c.Show(
								"the representative has V as its component",
								By(Normalized, represents, all.At(u)))
						})
					}))
				u, vertex := b.ObtainAs[A](
					"choose a vertex",
					"∃u:A. u ∈ V",
					BySets(nonempty))
				containsV := b.Have(
					"V is the component of this vertex",
					"V ∈ graph_components(V, R)",
					By(Normalized, vertex, all.At(u), ComponentInComponents.At(V, R, u)))
				b.Show(
					"V is the only component",
					BySets(containsV, allComponents))
			})
		a.Backward(
			"with a single component, every vertex can reach all of V",
			func(b *Argument, only Fact) {
				b.Do(Unfold(ConnectedDef))
				u := b.FixAs[A]("u")
				v := b.FixAs[A]("v")
				vertices := b.Assume()
				component := b.Have(
					"the single component is V",
					"graph_component(V, R, u) = V",
					BySets(only, vertices, ComponentInComponents.At(V, R, u)))
				b.Show(
					"v lies in the component of u and is therefore reachable from u",
					By(Normalized, component, vertices, InComponent.At(V, R, u, v)))
			})
	}),
})}

// ConnectedEdgelessSingleton says an edgeless nonempty graph can only
// be connected when it consists of one vertex.
var ConnectedEdgelessSingleton = connectedEdgelessSingletonThm{family.Add(registry.ProofEntry{
	Name: "ConnectedEdgelessSingleton",
	Key:  "prop_7b583675340c48ce",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"V ≠ ∅", "graph_connected(V, R)", "graph_edges(V, R) = ∅"},
		Conclusion: "∃u:A. V = {u}",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], nonempty, connected, edgeless Fact) {
		u, vertex := a.ObtainAs[A](
			"choose a vertex of the nonempty graph",
			"∃u:A. u ∈ V",
			BySets(nonempty))
		walks := a.Unfolded(connected, ConnectedDef)
		restricted := a.TermAs[Fun2[A, A, Bool]]("relation_on(V, R)")
		only := a.Have(
			"every vertex is u",
			"∀w:A. w ∈ V ⇒ w = u",
			a.ForEach(func(w *Expr[A]) Action {
				return Derive(func(b *Argument) {
					inW := b.Assume()
					distinct := b.SupposeNot()
					reaches := b.Have(
						"connectivity supplies a walk from u to w",
						"graph_reachable(V, R, u, w)",
						By(vertex, inW, walks.At(u, w)))
					walk := b.Unfolded(reaches, ReachableDef)
					positive := b.Have(
						"distinct endpoints require a positive-length walk",
						"transitive_closure(relation_on(V, R), u, w)",
						By(distinct, b.Unfolded(walk, closure.ReflexiveTransitiveClosureDef)))
					z, step := b.ObtainAs[A](
						"take the first adjacency of the walk",
						"∃z:A. relation_on(V, R, u, z)",
						By(Normalized, positive, closure.CasesRight.At(restricted, u, w)))
					edge := b.Have(
						"the first step supplies an edge in the graph",
						"{u, z} ∈ graph_edges(V, R)",
						Unfold(EdgesDef),
						BySets(step, equivalence.RelationOnDef.At(V, R, u, z)))
					b.Show(
						"the edge contradicts edgelessness",
						BySets(edge, edgeless))
				})
			}))
		a.Take(u)
		a.Show(
			"the vertex set consists of its chosen vertex",
			BySets(only, vertex))
	}),
})}

// ComponentConnected says the component of u is connected under any
// adjacency S that contains the graph's: two of its vertices are joined
// through u by a walk in V, and each step of that walk stays in the
// component, where S joins its endpoints too.
var ComponentConnected = componentConnectedThm{family.Add(registry.ProofEntry{
	Name: "ComponentConnected",
	Key:  "prop_fc6e9296b65fdf1",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(A). ∀R S:(A → A → bool). ∀u:A.",
		Hypotheses: []string{
			"symmetric_on(V, R)",
			"u ∈ V",
			"∀i j:A. i ∈ V ∧ j ∈ V ∧ R(i, j) ⇒ S(i, j)",
		},
		Conclusion: "graph_connected(graph_component(V, R, u), S)",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R, S *Arrow2[A, A, Bool],
		u *Expr[A],
		symmetric, inU, included Fact,
	) {
		W := a.TermAs[Set[A]]("graph_component(V, R, u)")
		equivalent := a.Have(
			"walks along a symmetric adjacency can be reversed",
			"equivalence_on(V, graph_reachable(V, R))",
			By(symmetric, ReachableEquivalence.At(V, R)))
		walks := a.Have(
			"two vertices of the component are joined by a walk confined to it",
			Statement{
				Binders:    "∀x y:A.",
				Hypotheses: []string{"x ∈ graph_component(V, R, u)", "y ∈ graph_component(V, R, u)"},
				Conclusion: "graph_reachable(graph_component(V, R, u), S, x, y)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				y := b.FixAs[A]()
				inComponent := b.Assume()
				fromU := b.Have(
					"both vertices are reachable from u",
					"x ∈ V ∧ y ∈ V ∧ graph_reachable(V, R, u, x) ∧ graph_reachable(V, R, u, y)",
					By(inComponent, InComponent.At(V, R, u, x), InComponent.At(V, R, u, y)))
				toU := b.Have(
					"reverse the walk from u to x",
					"graph_reachable(V, R, x, u)",
					By(inU, fromU, At(equivalence.SymmetricOn.Read(equivalent), u, x)))
				walk := b.Have(
					"join the two walks at u",
					"graph_reachable(V, R, x, y)",
					By(fromU, toU, ReachableTransitive.At(V, R, x, u, y)))
				start := b.Have(
					"the empty walk starts in the component",
					"x ∈ graph_component(V, R, u) ∧ graph_reachable(graph_component(V, R, u), S, x, x)",
					By(inComponent, ReachableReflexive.At(W, S, x)))
				extends := b.Have(
					"each ambient adjacency continues the walk inside the component",
					Statement{
						Binders: "∀i j:A.",
						Hypotheses: []string{
							"i ∈ V",
							"j ∈ V",
							"R(i, j)",
							"i ∈ graph_component(V, R, u) ∧ graph_reachable(graph_component(V, R, u), S, x, i)",
						},
						Conclusion: "j ∈ graph_component(V, R, u) ∧ graph_reachable(graph_component(V, R, u), S, x, j)",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[A]()
						j := c.FixAs[A]()
						continuation := c.Assume()
						atI := c.Have(
							"the current vertex is reachable from u",
							"graph_reachable(V, R, u, i)",
							By(continuation, InComponent.At(V, R, u, i)))
						atJ := c.Have(
							"one more step makes the next vertex reachable from u",
							"graph_reachable(V, R, u, j)",
							By(continuation, atI, AdjacentReachable.At(V, R, i, j), ReachableTransitive.At(V, R, u, i, j)))
						inJ := c.Have(
							"the next vertex is in the component",
							"j ∈ graph_component(V, R, u)",
							By(inU, continuation, atJ, InComponent.At(V, R, u, j)))
						step := c.Have(
							"the original adjacency is available inside the component",
							"graph_reachable(graph_component(V, R, u), S, i, j)",
							By(continuation, inJ, included.At(i, j), AdjacentReachable.At(W, S, i, j)))
						c.Show(
							"continue the walk in the component by that adjacency",
							By(continuation, inJ, step, ReachableTransitive.At(W, S, x, i, j)))
					}))
				invariant := b.TermAs[Set[A]](
					"λz:A. z ∈ graph_component(V, R, u) ∧ graph_reachable(graph_component(V, R, u), S, x, z)")
				b.Show(
					"the walk remains confined through its last vertex",
					By(extends, walk, start, ReachablePreserves.At(V, R, invariant, x, y)))
			}))
		a.Show(
			"every pair in the component is connected inside it",
			By(walks, ConnectedDef.At(W, S)))
	}),
})}
