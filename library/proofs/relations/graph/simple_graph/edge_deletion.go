package simple_graph

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// DeleteEdgeSymmetric keeps adjacency symmetric on V when an undirected
// edge is deleted: the test that the pair is not the edge reads the same
// in both orders.
var DeleteEdgeSymmetric = deleteEdgeSymmetricThm{family.Add(registry.ProofEntry{
	Name: "DeleteEdgeSymmetric",
	Key:  "prop_9cfc96c5faf3a099",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀e:set(A).",
		Hypotheses: []string{"symmetric_on(V, R)"},
		Conclusion: "symmetric_on(V, graph_delete_edge(R, e))",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], e *Expr[Set[A]], symmetric Fact) {
		symmetry := a.Unfolded(symmetric, equivalence.SymmetricOnDef)
		a.Show(
			"the unordered pair test reads the same in both orders",
			Simp(Fwd(equivalence.SymmetricOnDef), Fwd(DeleteEdgeDef)),
			BySets(symmetry))
	}),
})}

// DeleteEdgeConnectedIff replaces the deleted edge by the walk between its
// endpoints, so every original walk survives the deletion.
var DeleteEdgeConnectedIff = deleteEdgeConnectedIffThm{family.Add(registry.ProofEntry{
	Name: "DeleteEdgeConnectedIff",
	Key:  "prop_11c6c67a15cc07f3",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(A). ∀R:(A → A → bool). ∀u v:A.",
		Hypotheses: []string{
			"symmetric_on(V, «remaining»)",
			"graph_connected(V, R)",
			"u ∈ V",
			"v ∈ V",
		},
		Conclusion: "graph_connected(V, «remaining») ⇔ graph_reachable(V, «remaining», u, v)",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		u, v *Expr[A],
		symmetric, connected, inU, inV Fact,
	) {
		pair := a.TermAs[Set[A]]("{u, v}")
		deleted := a.TermAs[Fun2[A, A, Bool]]("«remaining»")
		a.Iff()
		a.Forward(
			"connectivity joins the endpoints of the deleted edge",
			func(b *Argument, connectedAfter Fact) {
				b.Show(
					"both endpoints are vertices",
					By(connectedAfter, inU, inV, ConnectedDef.At(V, deleted)))
			})
		a.Backward(
			"the replacement walk allows every original walk to survive the deletion",
			func(b *Argument, replacement Fact) {
				equivalent := b.Have(
					"reachability after deletion is an equivalence on the vertices",
					"equivalence_on(V, graph_reachable(V, «remaining»))",
					By(symmetric, ReachableEquivalence.At(V, deleted)))
				replaceStep := b.Have(
					"every original adjacency can be replaced by a walk after deletion",
					"∀x y:A. x ∈ V ∧ y ∈ V ∧ R(x, y) ⇒ graph_reachable(V, «remaining», x, y)",
					Derive(func(c *Argument) {
						x := c.FixAs[A]()
						y := c.FixAs[A]()
						step := c.Assume()
						c.Cases(c.Term("{x, y} = {u, v}"))
						c.When(
							"the deleted edge has the same endpoints in one orientation",
							func(d *Argument, same Fact) {
								orientation := d.Have(
									"the pair equality determines the two possible orientations",
									"(x = u ∧ y = v) ∨ (x = v ∧ y = u)",
									BySets(same))
								d.Show(
									"the replacement walk can be traversed in either direction",
									By(inU, inV, orientation, replacement, At(equivalence.SymmetricOn.Read(equivalent), u, v)))
							})
						c.Otherwise(
							"the original adjacency survives deletion",
							func(d *Argument, other Fact) {
								d.Show(
									"one surviving adjacency gives a walk",
									By(other, step, DeleteEdgeDef.At(R, pair, x, y), AdjacentReachable.At(V, deleted, x, y)))
							})
					}))
				b.Do(Simp(Fwd(ConnectedDef)))
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				vertices := b.Assume()
				reachFromX := b.TermAs[Set[A]]("λz:A. graph_reachable(V, «remaining», x, z)")
				extends := b.Have(
					"after deletion a walk can be extended across any original adjacency",
					Statement{
						Binders: "∀i j:A.",
						Hypotheses: []string{
							"i ∈ V",
							"j ∈ V",
							"R(i, j)",
							"graph_reachable(V, «remaining», x, i)",
						},
						Conclusion: "graph_reachable(V, «remaining», x, j)",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[A]()
						j := c.FixAs[A]()
						extension := c.Assume()
						c.Show(
							"append the replacement for the original adjacency",
							By(
								vertices,
								extension,
								replaceStep.At(i, j),
								At(equivalence.TransitiveOn.Read(equivalent), x, i, j)))
					}))
				walk := b.Have(
					"connectivity supplies an original walk",
					"graph_reachable(V, R, x, y)",
					By(connected, vertices, ConnectedDef.At(V, R)))
				b.Show(
					"the walk stays replaceable at every step, from the empty walk at x on",
					By(
						extends,
						walk,
						ReachableReflexive.At(V, deleted, x),
						ReachablePreserves.At(V, R, reachFromX, x, y)))
			})
	}),
})}

// BridgeComponents splits V at a bridge: walk induction keeps every
// vertex on the side of the endpoint that reaches it.
var BridgeComponents = bridgeComponentsThm{family.Add(registry.ProofEntry{
	Name: "BridgeComponents",
	Key:  "prop_81bc155d42fb5170",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(A). ∀R:(A → A → bool). ∀u v:A.",
		Hypotheses: []string{
			"symmetric_on(V, «remaining»)",
			"graph_connected(V, R)",
			"u ∈ V",
			"v ∈ V",
			"¬graph_reachable(V, «remaining», u, v)",
		},
		Conclusion: "«componentOfU» ∪ «componentOfV» = V ∧ " +
			"«componentOfU» ∩ «componentOfV» = ∅ ∧ " +
			"u ∈ «componentOfU» ∧ " +
			"v ∈ «componentOfV» ∧ " +
			"(∀x y:A. x ∈ «componentOfU» ∧ y ∈ «componentOfV» ∧ R(x, y) ⇒ {x, y} = {u, v})",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		u, v *Expr[A],
		symmetric, connected, inU, inV, cut Fact,
	) {
		pair := a.TermAs[Set[A]]("{u, v}")
		deleted := a.TermAs[Fun2[A, A, Bool]]("«remaining»")
		equivalent := a.Have(
			"reachability after deletion is an equivalence on V",
			"equivalence_on(V, graph_reachable(V, «remaining»))",
			By(symmetric, ReachableEquivalence.At(V, deleted)))
		stayU := ReachableReflexive.At(V, deleted, u)
		stayV := ReachableReflexive.At(V, deleted, v)
		staysInUnion := a.Have(
			"both sides of the cut together are closed under the original adjacency",
			Statement{
				Binders: "∀x y:A.",
				Hypotheses: []string{
					"x ∈ V", "y ∈ V", "R(x, y)",
					"graph_reachable(V, «remaining», u, x) ∨ graph_reachable(V, «remaining», v, x)",
				},
				Conclusion: "graph_reachable(V, «remaining», u, y) ∨ graph_reachable(V, «remaining», v, y)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				y := b.FixAs[A]()
				step := b.Assume()
				b.Cases(b.Term("{x, y} = {u, v}"))
				b.When(
					"taking the bridge ends at one of its endpoints",
					func(c *Argument, bridge Fact) {
						end := c.Have(
							"y is one of the bridge endpoints",
							"y = u ∨ y = v",
							BySets(bridge))
						c.Show(
							"one of the two empty walks reaches y",
							By(end, stayU, stayV))
					})
				b.Otherwise(
					"a surviving edge stays on its current side of the cut",
					func(c *Argument, surviving Fact) {
						walk := c.Have(
							"the surviving edge is a walk after deletion",
							"graph_reachable(V, «remaining», x, y)",
							By(step, surviving, DeleteEdgeDef.At(R, pair, x, y), AdjacentReachable.At(V, deleted, x, y)))
						c.Show(
							"extend whichever endpoint already reaches x",
							By(
								step,
								walk,
								ReachableTransitive.At(V, deleted, u, x, y),
								ReachableTransitive.At(V, deleted, v, x, y)))
					})
			}))
		covered := a.Have(
			"every vertex is reachable from one of the endpoints after deletion",
			"∀x:A. x ∈ V ⇒ graph_reachable(V, «remaining», u, x) ∨ graph_reachable(V, «remaining», v, x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				inX := b.Assume()
				walk := b.Have(
					"the original graph connects u to x",
					"graph_reachable(V, R, u, x)",
					By(connected, inU, inX, ConnectedDef.At(V, R)))
				onEitherSide := b.TermAs[Set[A]](
					"λz:A. graph_reachable(V, «remaining», u, z) ∨ graph_reachable(V, «remaining», v, z)")
				startsOnASide := b.Have(
					"the walk starts on one of the two sides, at u itself",
					"graph_reachable(V, «remaining», u, u) ∨ graph_reachable(V, «remaining», v, u)",
					By(stayU))
				b.Show(
					"walk induction keeps x on one of the two sides",
					By(staysInUnion, walk, startsOnASide, ReachablePreserves.At(V, R, onEitherSide, u, x)))
			}))
		separated := a.Have(
			"a common vertex would provide a replacement walk between u and v",
			"∀x:A. x ∈ V ⇒ ¬(graph_reachable(V, «remaining», u, x) ∧ graph_reachable(V, «remaining», v, x))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				inX := b.Assume()
				b.Show(
					"reverse the second walk and join it to the first",
					By(
						cut,
						inV,
						inX,
						At(equivalence.SymmetricOn.Read(equivalent), v, x),
						ReachableTransitive.At(V, deleted, u, x, v)))
			}))
		a.Do(SplitConjAll(
			Case(
				"the two components cover V",
				BySets(inU, inV, covered, At(InComponent, V, deleted, u), At(InComponent, V, deleted, v))),
			Case(
				"the two components have no common vertex",
				BySets(inU, inV, separated, At(InComponent, V, deleted, u), At(InComponent, V, deleted, v))),
			Case(
				"the first endpoint lies in its component",
				By(inU, stayU, InComponent.At(V, deleted, u, u))),
			Case(
				"the second endpoint lies in its component",
				By(inV, stayV, InComponent.At(V, deleted, v, v))),
			Case(
				"an edge across the two components cannot survive deletion",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					y := b.FixAs[A]()
					across := b.Assume()
					survives := b.SupposeNot()
					endpoints := b.Have(
						"x and y are reached from opposite endpoints",
						"x ∈ V ∧ y ∈ V ∧ graph_reachable(V, «remaining», u, x) ∧ graph_reachable(V, «remaining», v, y)",
						By(across, InComponent.At(V, deleted, u, x), InComponent.At(V, deleted, v, y)))
					walk := b.Have(
						"a surviving crossing would be a walk after deletion",
						"graph_reachable(V, «remaining», x, y)",
						By(
							across,
							endpoints,
							survives,
							DeleteEdgeDef.At(R, pair, x, y),
							AdjacentReachable.At(V, deleted, x, y)))
					b.Show(
						"a walk across the cut would put y in both components",
						By(endpoints, walk, separated.At(y), ReachableTransitive.At(V, deleted, u, x, y)))
				})),
		))
	}),
})}

// BridgeCutCounts counts vertices and edges across a partition whose
// only crossing edge is {u, v}.
var BridgeCutCounts = bridgeCutCountsThm{family.Add(registry.ProofEntry{
	Name: "BridgeCutCounts",
	Key:  "prop_9c327ac7f8ac037d",
	Build: family.Sections(Statement{
		Binders: "∀V U W:set(A). ∀R:(A → A → bool). ∀u v:A.",
		Hypotheses: []string{
			"finite(V)",
			"symmetric_on(V, R)",
			"U ∪ W = V",
			"U ∩ W = ∅",
			"u ∈ U",
			"v ∈ W",
			"R(u, v)",
			"∀x y:A. x ∈ U ∧ y ∈ W ∧ R(x, y) ⇒ {x, y} = {u, v}",
		},
		Conclusion: "card(V) = card(U) + card(W) ∧ " +
			"card(graph_edges(V, R)) = card(graph_edges(U, R)) + card(graph_edges(W, R)) + 1",
		Abbrev: Abbrev{
			{Name: "internalEdges", Text: "graph_edges(U, R) ∪ graph_edges(W, R)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		partOfCarrier := ctx.Lemma(Statement{
			Binders:    "∀S V:set(A). ∀R:(A → A → bool).",
			Hypotheses: []string{"S ⊆ V", "finite(V)"},
			Conclusion: "finite(S) ∧ finite(graph_edges(S, R)) ∧ graph_edges(S, R) ⊆ graph_edges(V, R)",
		}, func(a *Argument, S, V *Expr[Set[A]], R *Arrow2[A, A, Bool], below, finiteV Fact) {
			finiteS := a.Have(
				"a part of a finite carrier is finite",
				"finite(S)",
				By(below, finiteV, finite_set.FiniteSubset.At(S, V)))
			a.Show(
				"so are its edges, and they are edges on V",
				By(finiteS, below, EdgesFinite.At(S, R), EdgesMonotone.At(S, V, R)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			V, U, W *Expr[Set[A]],
			R *Arrow2[A, A, Bool],
			u, v *Expr[A],
			finiteV, symmetric, partition, apart, inU, inW, bridge, onlyCross Fact,
		) {
			edgesU := a.TermAs[Set[Set[A]]]("graph_edges(U, R)")
			edgesW := a.TermAs[Set[Set[A]]]("graph_edges(W, R)")
			insideEdges := a.TermAs[Set[Set[A]]]("«internalEdges»")
			crossing := a.TermAs[Set[A]]("{u, v}")
			sideU := a.Conjuncts(
				a.Have(
					"U is a part of the finite carrier V",
					"finite(U) ∧ finite(graph_edges(U, R)) ∧ graph_edges(U, R) ⊆ graph_edges(V, R)",
					BySets(partition, finiteV, At(partOfCarrier, U, V, R))),
				"U is finite",
				"the edges on U are finite",
				"the edges on U are edges on V")
			sideW := a.Conjuncts(
				a.Have(
					"W is a part of the finite carrier V",
					"finite(W) ∧ finite(graph_edges(W, R)) ∧ graph_edges(W, R) ⊆ graph_edges(V, R)",
					BySets(partition, finiteV, At(partOfCarrier, W, V, R))),
				"W is finite",
				"the edges on W are finite",
				"the edges on W are edges on V")

			endpointsInside := a.Have(
				"each edge is a nonempty subset of its carrier",
				"∀S:set(A). ∀e:set(A). e ∈ graph_edges(S, R) ⇒ e ⊆ S ∧ e ≠ ∅",
				Unfold(EdgesDef),
				BySets())
			disjointEdges := a.Have(
				"a nonempty edge cannot lie in both sides of the partition",
				"graph_edges(U, R) ∩ graph_edges(W, R) = ∅",
				BySets(apart, endpointsInside.At(U), endpointsInside.At(W)))
			bridgeNew := a.Have(
				"the crossing edge is internal to neither side",
				"{u, v} ∉ «internalEdges»",
				BySets(apart, inU, inW, endpointsInside.At(U, crossing), endpointsInside.At(W, crossing)))

			bridgeInV := a.Have(
				"u and v form an edge on V",
				"{u, v} ∈ graph_edges(V, R)",
				Unfold(EdgesDef),
				BySets(partition, inU, inW, bridge))
			decomposition := a.Have(
				"every edge on V is either internal or the one crossing edge",
				"graph_edges(V, R) = insert({u, v}, «internalEdges»)",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("e")
					b.Iff()
					b.Forward(
						"classify an edge by the sides of its endpoints",
						func(c *Argument, edge Fact) {
							x, y, endpoints := c.Obtain2As[A, A](
								"write e using adjacent endpoints",
								"∃x y:A. x ∈ V ∧ y ∈ V ∧ R(x, y) ∧ e = {x, y}",
								BySets(c.Unfolded(edge, EdgesDef)))
							notBothU := c.Unless(
								c.Term("x ∈ U ∧ y ∈ U"),
								"when both endpoints lie in U",
								Given(func(d *Argument, both Fact) {
									d.Show(
										"the edge lies in the internal edges on U",
										Simp(Fwd(EdgesDef)),
										BySets(endpoints, both))
								}))
							notBothW := c.Unless(
								c.Term("x ∈ W ∧ y ∈ W"),
								"when both endpoints lie in W",
								Given(func(d *Argument, both Fact) {
									d.Show(
										"the edge lies in the internal edges on W",
										Simp(Fwd(EdgesDef)),
										BySets(endpoints, both))
								}))
							notForward := c.Unless(
								c.Term("x ∈ U ∧ y ∈ W"),
								"when the endpoints cross from U to W",
								Given(func(d *Argument, sides Fact) {
									d.Show(
										"the crossing edge is {u, v}",
										BySets(sides, endpoints, onlyCross.At(x, y)))
								}))
							reverseSides := c.Have(
								"the endpoints cross from W to U",
								"x ∈ W ∧ y ∈ U",
								BySets(partition, endpoints, notBothU, notBothW, notForward))
							reverseStep := c.Have(
								"reverse the adjacency",
								"R(y, x)",
								By(endpoints, symmetric, equivalence.SymmetricOnDef))
							c.Show(
								"in the reverse orientation the crossing edge is still {u, v}",
								BySets(reverseSides, reverseStep, endpoints, onlyCross.At(y, x)))
						})
					b.Backward(
						"every internal edge and the crossing edge lie in V",
						func(c *Argument, belongs Fact) {
							internal := c.Unless(
								c.Term("e = {u, v}"),
								"the crossing edge lies in V",
								Given(func(d *Argument, isBridge Fact) {
									d.Show(
										"use the edge between u and v",
										By(Normalized, isBridge, bridgeInV))
								}))
							c.Show(
								"every internal edge belongs to the original edge set",
								BySets(belongs, internal, sideU[2], sideW[2]))
						})
				}))
			finiteInternal := a.Have(
				"the union of the internal edge sets is finite",
				"finite(«internalEdges»)",
				By(sideU[1], sideW[1], finite_set.FiniteUnionImp.At(edgesU, edgesW)))
			internalCount := a.Have(
				"the two internal edge sets contribute their sizes",
				"card(«internalEdges») = card(graph_edges(U, R)) + card(graph_edges(W, R))",
				By(sideU[1], sideW[1], disjointEdges, cardinality.CardUnion.At(edgesU, edgesW)))
			a.Do(SplitConj(
				Case(
					"the two disjoint sides account for all vertices",
					By(Normalized, partition, apart, sideU[0], sideW[0], cardinality.CardUnion.At(U, W))),
				Case(
					"the internal edges and the crossing edge account for all edges",
					ByArith(
						decomposition,
						internalCount,
						finiteInternal,
						bridgeNew,
						cardinality.InsertCountsOneMore.At(insideEdges, crossing))),
			))
		})
	}),
})}
