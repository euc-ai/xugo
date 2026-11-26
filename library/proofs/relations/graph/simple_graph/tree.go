package simple_graph

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// GraphTree says a tree is a nonempty, connected simple graph that
// disconnects when any edge is deleted.
var GraphTree = graphTreeThm{family.DefineStructure(registry.DefEntry{
	Name:    "GraphTree",
	Key:     "prop_c5a5459218779fdd",
	Const:   "graph_tree",
	Subject: "V",
	Type:    "set(A) → (A → A → bool) → bool",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). " +
			"    graph_tree(V, R) ⇔ " +
			"    simple_graph_on(V, R) ∧ " +
			"    V ≠ ∅ ∧ " +
			"    graph_connected(V, R) ∧ " +
			"    (∀e:set(A). e ∈ graph_edges(V, R) ⇒ ¬graph_connected(V, graph_delete_edge(R, e)))",
	},
	Deps: []registry.EntryLike{SimpleGraphOn, EdgesDef, ConnectedDef, DeleteEdgeDef},
})}

// TreeSimple says a tree is a simple graph.
var TreeSimple = treeSimpleThm{family.Add(registry.ProofEntry{
	Name:  "TreeSimple",
	Key:   "prop_9daf4e6dbcf54d49",
	Build: GraphTree.Axiom("simple_graph_on(V, R)"),
})}

// TreeNonempty says a tree has a vertex.
var TreeNonempty = treeNonemptyThm{family.Add(registry.ProofEntry{
	Name:  "TreeNonempty",
	Key:   "prop_e7624f9b4559355f",
	Build: GraphTree.Axiom("V ≠ ∅"),
})}

// TreeConnected says a tree is connected.
var TreeConnected = treeConnectedThm{family.Add(registry.ProofEntry{
	Name:  "TreeConnected",
	Key:   "prop_13a008bb78d92071",
	Build: GraphTree.Axiom("graph_connected(V, R)"),
})}

// TreeEdgeDisconnects says every edge of a tree is a bridge: deleting it
// disconnects the tree.
var TreeEdgeDisconnects = treeEdgeDisconnectsThm{family.Add(registry.ProofEntry{
	Name: "TreeEdgeDisconnects",
	Key:  "prop_9848982e2b9153b3",
	Build: GraphTree.Axiom(Statement{
		Binders:    "∀e:set(A).",
		Hypotheses: []string{"e ∈ graph_edges(V, R)"},
		Conclusion: "¬graph_connected(V, graph_delete_edge(R, e))",
	}),
})}

// TreeEdgeSeparates says the endpoints of a tree edge are unreachable
// from each other once that edge is deleted.
var TreeEdgeSeparates = treeEdgeSeparatesThm{family.Add(registry.ProofEntry{
	Name: "TreeEdgeSeparates",
	Key:  "prop_fb6077a2646b7ef0",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀u v:A.",
		Hypotheses: []string{"graph_tree(V, R)", "u ∈ V", "v ∈ V", "R(u, v)"},
		Conclusion: "¬graph_reachable(V, «remaining», u, v)",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		u, v *Expr[A],
		tree, inU, inV, adjacent Fact,
	) {
		pair := a.TermAs[Set[A]]("{u, v}")
		edge := a.Have(
			"the pair of adjacent vertices u and v is an edge",
			"{u, v} ∈ graph_edges(V, R)",
			Simp(Fwd(EdgesDef)),
			BySets(inU, inV, adjacent))
		symmetricAfter := a.Have(
			"deletion keeps adjacency symmetric on V",
			"symmetric_on(V, «remaining»)",
			By(Symmetric.Read(TreeSimple.Read(tree)), DeleteEdgeSymmetric.At(V, R, pair)))
		disconnected := a.Have(
			"deleting the edge disconnects the tree",
			"¬graph_connected(V, «remaining»)",
			By(edge, TreeEdgeDisconnects.Read(tree).At(pair)))
		a.Show(
			"a replacement walk would keep the graph connected",
			By(
				disconnected,
				symmetricAfter,
				TreeConnected.Read(tree),
				inU,
				inV,
				DeleteEdgeConnectedIff.At(V, R, u, v)))
	}),
})}

// ConnectedInducedSubtree says a nonempty connected induced subgraph of
// a tree is a tree.
var ConnectedInducedSubtree = connectedInducedSubtreeThm{family.Add(registry.ProofEntry{
	Name: "ConnectedInducedSubtree",
	Key:  "prop_ba899e19741795d4",
	Build: family.Theorem(Statement{
		Binders:    "∀V W:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"graph_tree(V, R)", "W ⊆ V", "W ≠ ∅", "graph_connected(W, R)"},
		Conclusion: "graph_tree(W, R)",
	}, func(
		a *Argument,
		V, W *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		tree, subset, nonempty, connected Fact,
	) {
		simple := TreeSimple.Read(tree)
		symmetry := a.Unfolded(Symmetric.Read(simple), equivalence.SymmetricOnDef)
		a.Do(GraphTree.Intro(
			Case(
				"symmetry and looplessness restrict to W",
				Simp(Fwd(SimpleGraphOn), Fwd(equivalence.SymmetricOnDef)),
				BySets(subset, symmetry, Loopless.Read(simple))),
			Case(
				"W is nonempty",
				By(nonempty)),
			Case(
				"the induced subgraph is connected by hypothesis",
				By(connected)),
			Case(
				"a replacement walk in W would also be a replacement walk in V",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("e")
					edge := b.Assume()
					u, v, endpoints := b.Obtain2As[A, A](
						"the edge has adjacent endpoints in W",
						"∃u v:A. u ∈ W ∧ v ∈ W ∧ R(u, v) ∧ e = {u, v}",
						BySets(b.Unfolded(edge, EdgesDef)))
					parts := b.Conjuncts(
						endpoints,
						"first endpoint in W",
						"second endpoint in W",
						"adjacency",
						"edge pair")
					b.Do(parts[3].Rw())
					deleted := b.TermAs[Fun2[A, A, Bool]]("«remaining»")
					inV := b.Have(
						"the endpoints also belong to V",
						"u ∈ V ∧ v ∈ V",
						BySets(subset, parts[0], parts[1]))
					separated := b.Have(
						"the original tree has no replacement walk for that edge",
						"¬graph_reachable(V, «remaining», u, v)",
						By(tree, inV, parts[2], TreeEdgeSeparates.At(V, R, u, v)))
					connectedAfter := b.SupposeNot()
					replacement := b.Have(
						"connectivity after deletion would join the endpoints in W",
						"graph_reachable(W, «remaining», u, v)",
						By(connectedAfter, parts[0], parts[1], ConnectedDef.At(W, deleted)))
					smaller := b.TermAs[Fun2[A, A, Bool]]("relation_on(W, «remaining»)")
					larger := b.TermAs[Fun2[A, A, Bool]]("relation_on(V, «remaining»)")
					inclusion := b.Have(
						"a step between vertices of W is a step between vertices of V",
						"∀x y:A. relation_on(W, «remaining», x, y) ⇒ relation_on(V, «remaining», x, y)",
						Simp(Fwd(equivalence.RelationOnDef)),
						BySets(subset))
					b.Show(
						"a walk confined to W also lies in V",
						By(
							separated,
							replacement,
							inclusion,
							ReachableDef,
							closure.ReflexiveTransitiveClosureMonotone.At(smaller, larger, u, v)))
				})),
		))
	}),
})}

// TreeSplitsAtEdge cuts a finite tree at an edge uv: the components of u
// and of v once uv is deleted are trees on proper subsets of V, they share
// out the vertices, and their edges are all the edges of the tree but uv.
var TreeSplitsAtEdge = treeSplitsAtEdgeThm{family.Add(registry.ProofEntry{
	Name: "TreeSplitsAtEdge",
	Key:  "prop_aa6a6e9c843e2abd",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀u v:A.",
		Hypotheses: []string{"finite(V)", "graph_tree(V, R)", "u ∈ V", "v ∈ V", "R(u, v)"},
		Conclusion: "graph_tree(«componentOfU», R) ∧ " +
			"graph_tree(«componentOfV», R) ∧ " +
			"«componentOfU» ⊊ V ∧ " +
			"«componentOfV» ⊊ V ∧ " +
			"card(V) = card(«componentOfU») + card(«componentOfV») ∧ " +
			"card(graph_edges(V, R)) = " +
			"card(graph_edges(«componentOfU», R)) + card(graph_edges(«componentOfV», R)) + 1",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		u, v *Expr[A],
		finiteV, tree, inU, inV, adjacent Fact,
	) {
		symmetric := Symmetric.Read(TreeSimple.Read(tree))
		pair := a.TermAs[Set[A]]("{u, v}")
		deleted := a.TermAs[Fun2[A, A, Bool]]("«remaining»")
		U := a.TermAs[Set[A]]("«componentOfU»")
		W := a.TermAs[Set[A]]("«componentOfV»")
		symmetricAfter := a.Have(
			"deletion keeps adjacency symmetric on V",
			"symmetric_on(V, «remaining»)",
			By(symmetric, DeleteEdgeSymmetric.At(V, R, pair)))
		separated := a.Have(
			"the endpoints cannot be joined after deletion",
			"¬graph_reachable(V, «remaining», u, v)",
			By(tree, inU, inV, adjacent, TreeEdgeSeparates.At(V, R, u, v)))
		cut := a.Have(
			"the two components partition the tree and their only crossing edge is uv",
			"«componentOfU» ∪ «componentOfV» = V ∧ "+
				"«componentOfU» ∩ «componentOfV» = ∅ ∧ "+
				"u ∈ «componentOfU» ∧ "+
				"v ∈ «componentOfV» ∧ "+
				"(∀x y:A. x ∈ «componentOfU» ∧ y ∈ «componentOfV» ∧ R(x, y) ⇒ {x, y} = {u, v})",
			By(symmetricAfter, TreeConnected.Read(tree), inU, inV, separated, BridgeComponents.At(V, R, u, v)))
		parts := a.Conjuncts(
			cut,
			"components cover V",
			"components are disjoint",
			"u in its component",
			"v in its component",
			"only crossing edge")
		strict := a.Have(
			"both sides are nonempty proper subsets of V",
			"«componentOfU» ⊊ V ∧ «componentOfV» ⊊ V ∧ «componentOfU» ≠ ∅ ∧ «componentOfV» ≠ ∅",
			BySets(parts[0], parts[1], parts[2], parts[3]))
		inside := a.Have(
			"both sides lie in V",
			"«componentOfU» ⊆ V ∧ «componentOfV» ⊆ V",
			BySets(parts[0]))
		kept := a.Have(
			"every surviving adjacency is an original adjacency",
			"∀i j:A. i ∈ V ∧ j ∈ V ∧ «remaining»(i, j) ⇒ R(i, j)",
			Derive(func(b *Argument) {
				i := b.FixAs[A]()
				j := b.FixAs[A]()
				step := b.Assume()
				b.Show(
					"survival requires the original adjacency",
					By(step, DeleteEdgeDef.At(R, pair, i, j)))
			}))
		bothConnected := a.Have(
			"walks within either component remain available in the induced subgraph",
			"graph_connected(«componentOfU», R) ∧ graph_connected(«componentOfV», R)",
			By(
				symmetricAfter,
				inU,
				inV,
				kept,
				ComponentConnected.At(V, deleted, R, u),
				ComponentConnected.At(V, deleted, R, v)))
		bothTrees := a.Have(
			"a nonempty connected induced subgraph of a tree is a tree",
			"graph_tree(«componentOfU», R) ∧ graph_tree(«componentOfV», R)",
			By(
				tree,
				inside,
				strict,
				bothConnected,
				ConnectedInducedSubtree.At(V, U, R),
				ConnectedInducedSubtree.At(V, W, R)))
		counts := a.Have(
			"the cut shares out the vertices and leaves exactly one crossing edge",
			"card(V) = card(«componentOfU») + card(«componentOfV») ∧ "+
				"card(graph_edges(V, R)) = "+
				"card(graph_edges(«componentOfU», R)) + card(graph_edges(«componentOfV», R)) + 1",
			By(finiteV, symmetric, cut, adjacent, BridgeCutCounts.At(V, U, W, R, u, v)))
		a.Show(
			"the two sides are smaller trees accounting for every vertex and every edge but uv",
			By(bothTrees, strict, counts))
	}),
})}

// TreeEdgeCount counts the edges of a finite tree by cutting it at an
// edge and applying strong induction to the two resulting subtrees.
var TreeEdgeCount = treeEdgeCountThm{family.Add(registry.ProofEntry{
	Name: "TreeEdgeCount",
	Key:  "prop_6916dce022269280",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"finite(V)", "graph_tree(V, R)"},
		Conclusion: "card(graph_edges(V, R)) + 1 = card(V)",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], finiteV, treeV Fact) {
		countsAtSize := a.TermAs[Set[Nat]](
			"λn:num. ∀S:set(A). " +
				"    finite(S) ∧ graph_tree(S, R) ∧ card(S) = n ⇒ card(graph_edges(S, R)) + 1 = card(S)")
		atSizeV := a.Have(
			"strong induction counts the edges of every tree of size card(V)",
			Statement{
				Binders:    "∀S:set(A).",
				Hypotheses: []string{"finite(S)", "graph_tree(S, R)", "card(S) = card(V)"},
				Conclusion: "card(graph_edges(S, R)) + 1 = card(S)",
			},
			ByInduction(nat_order.StrongInduction.At(countsAtSize, a.TermAs[Nat]("card(V)")),
				Case(
					"each tree either has a single vertex or splits across a bridge",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						smaller := b.Assume()
						S := b.FixAs[Set[A]]("S")
						given := b.Conjuncts(
							b.Assume(),
							"the carrier is finite",
							"the graph is a tree",
							"the carrier has size n")
						b.Cases(b.Term("graph_edges(S, R) = ∅"))
						b.When(
							"a connected edgeless tree has one vertex",
							func(c *Argument, edgeless Fact) {
								u, singleton := c.ObtainAs[A](
									"name its only vertex",
									"∃u:A. S = {u}",
									By(
										TreeNonempty.Read(given[1]),
										TreeConnected.Read(given[1]),
										edgeless,
										ConnectedEdgelessSingleton.At(S, R)))
								edgeCount := c.Have(
									"the empty edge set has size zero",
									"card(graph_edges(S, R)) = 0",
									By(edgeless, cardinality.CardClauses.Inst[Set[A]]()))
								vertexCount := c.Have(
									"the singleton vertex set has size one",
									"card(S) = 1",
									By(Normalized, singleton, cardinality.CardSing.At(u)))
								c.Show(
									"zero edges plus one gives the number of vertices",
									ByArith(edgeCount, vertexCount))
							})
						b.Otherwise(
							"deleting an edge cuts the tree into two smaller trees",
							func(c *Argument, hasEdges Fact) {
								edges := c.TermAs[Set[Set[A]]]("graph_edges(S, R)")
								_, edge := c.ObtainAs[Set[A]](
									"choose an edge of the tree",
									"∃e:set(A). e ∈ graph_edges(S, R)",
									By(hasEdges, set_basic.MemberNotEmpty.At(edges)))
								u, v, endpoints := c.Obtain2As[A, A](
									"name its two adjacent endpoints",
									"∃u v:A. u ∈ S ∧ v ∈ S ∧ R(u, v)",
									BySets(c.Unfolded(edge, EdgesDef)))
								U, componentU := c.LetAs[Set[A]]("U", "graph_component(S, «remaining», u)")
								W, componentW := c.LetAs[Set[A]]("W", "graph_component(S, «remaining», v)")
								split := c.Conjuncts(
									c.Have(
										"cutting the edge leaves two smaller trees that share out the vertices and every edge but uv",
										"graph_tree(U, R) ∧ "+
											"graph_tree(W, R) ∧ "+
											"U ⊊ S ∧ "+
											"W ⊊ S ∧ "+
											"card(S) = card(U) + card(W) ∧ "+
											"card(graph_edges(S, R)) = card(graph_edges(U, R)) + card(graph_edges(W, R)) + 1",
										By(
											Normalized,
											given[0],
											given[1],
											endpoints,
											componentU,
											componentW,
											TreeSplitsAtEdge.At(S, R, u, v))),
									"the side of u is a tree",
									"the side of v is a tree",
									"the side of u is a proper subset",
									"the side of v is a proper subset",
									"the vertices split between the sides",
									"the edges split between the sides but for uv")
								subtreeCounts := c.Have(
									"the induction hypothesis counts each tree on a proper subset of S",
									"∀T:set(A). T ⊊ S ∧ graph_tree(T, R) ⇒ card(graph_edges(T, R)) + 1 = card(T)",
									Derive(func(d *Argument) {
										T := d.FixAs[Set[A]]()
										smallerTree := d.Assume()
										subset := d.Have(
											"a proper subset is a subset",
											"T ⊆ S",
											BySets(smallerTree))
										finiteT := d.Have(
											"the subset of a finite carrier is finite",
											"finite(T)",
											By(given[0], subset, finite_set.FiniteSubset.At(T, S)))
										decreases := d.Have(
											"proper inclusion strictly decreases the number of vertices",
											"card(T) < n",
											By(Normalized, given[0], smallerTree, given[2], cardinality.CardPsubset.At(T, S)))
										d.Show(
											"the smaller tree satisfies the count",
											By(finiteT, smallerTree, decreases, smaller.At(d.TermAs[Nat]("card(T)"), T)))
									}))
								left := c.Have(
									"the side of u has one fewer edge than vertices",
									"card(graph_edges(U, R)) + 1 = card(U)",
									By(split[0], split[2], subtreeCounts.At(U)))
								right := c.Have(
									"the side of v has one fewer edge than vertices",
									"card(graph_edges(W, R)) + 1 = card(W)",
									By(split[1], split[3], subtreeCounts.At(W)))
								c.Show(
									"putting the edge back adds one edge",
									ByArith(split[4], split[5], left, right))
							})
					}))))
		a.Show(
			"apply the count at size card(V) to V itself",
			By(finiteV, treeV, atSizeV.At(V)))
	}),
})}
