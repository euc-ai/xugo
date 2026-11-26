package simple_graph

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// EdgesSubset says every edge is a set of vertices: both of its
// endpoints lie in V, whatever the adjacency.
var EdgesSubset = edgesSubsetThm{family.Add(registry.ProofEntry{
	Name: "EdgesSubset",
	Key:  "prop_27ec8b3d5d3db560",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool). ∀e:set(A).",
		Hypotheses: []string{"e ∈ graph_edges(V, R)"},
		Conclusion: "e ⊆ V",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], e *Expr[Set[A]], edge Fact) {
		a.Show(
			"an edge is the pair of its endpoints, and both endpoints are vertices",
			BySets(a.Unfolded(edge, EdgesDef)))
	}),
})}

// EdgeSize says every edge of a simple graph has two elements: a loop is
// no edge, so its endpoints are distinct.
var EdgeSize = edgeSizeThm{family.Add(registry.ProofEntry{
	Name: "EdgeSize",
	Key:  "prop_7fbe393de7396d02",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(A). ∀R:(A → A → bool). ∀e:set(A).",
		Hypotheses: []string{
			"simple_graph_on(V, R)",
			"e ∈ graph_edges(V, R)",
		},
		Conclusion: "has_size(e, 2)",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], e *Expr[Set[A]], simple, edge Fact) {
		u, v, endpoints := a.Obtain2As[A, A](
			"an edge has adjacent endpoints in V",
			"∃u v:A. u ∈ V ∧ v ∈ V ∧ R(u, v) ∧ e = {u, v}",
			BySets(a.Unfolded(edge, EdgesDef)))
		distinct := a.Have(
			"a loop cannot be an edge",
			"u ≠ v",
			By(endpoints, simple, Loopless.At(V, R, u)))
		a.Show(
			"distinct endpoints make a set of size two",
			By(Normalized, endpoints, distinct, cardinality.HasSizePair.At(u, v)))
	}),
})}

// EdgesFinite embeds the edges in the powerset of the finite vertex set.
var EdgesFinite = edgesFiniteThm{family.Add(registry.ProofEntry{
	Name: "EdgesFinite",
	Key:  "prop_65a7d5012088a7a5",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"finite(V)"},
		Conclusion: "finite(graph_edges(V, R))",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], finiteV Fact) {
		edges := a.TermAs[Set[Set[A]]]("graph_edges(V, R)")
		powerset := a.TermAs[Set[Set[A]]]("{e:set(A) | e ⊆ V}")
		subset := a.Have(
			"each edge belongs to the powerset of V",
			"graph_edges(V, R) ⊆ {e:set(A) | e ⊆ V}",
			BySets(At(EdgesSubset, V, R)))
		a.Show(
			"the powerset is finite, so its subset of edges is finite",
			By(
				subset,
				finiteV,
				finite_set.FinitePowerset.At(V),
				finite_set.FiniteSubset.Inst[Set[A]]().At(edges, powerset)))
	}),
})}

// EdgesMonotone says an edge between vertices of a subset S of V is an
// edge on V: the same endpoints lie in V.
var EdgesMonotone = edgesMonotoneThm{family.Add(registry.ProofEntry{
	Name: "EdgesMonotone",
	Key:  "prop_edc5d9192839e21f",
	Build: family.Theorem(Statement{
		Binders:    "∀S V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"S ⊆ V"},
		Conclusion: "graph_edges(S, R) ⊆ graph_edges(V, R)",
	}, func(a *Argument, S, V *Expr[Set[A]], R *Arrow2[A, A, Bool], below Fact) {
		a.Do(Unfold(EdgesDef), Simp(Fwd(set_basic.SubsetDef)))
		a.FixAs[Set[A]]("e")
		edge := a.Assume()
		_, _, endpoints := a.Obtain2As[A, A](
			"take endpoints from S",
			"∃x y:A. x ∈ S ∧ y ∈ S ∧ R(x, y) ∧ e = {x, y}",
			BySets(edge))
		a.Show(
			"the same endpoints belong to V",
			BySets(below, endpoints))
	}),
})}

// IncidentEdges gives the bijection w ↦ {v, w} from neighbours of v to
// edges containing v.
var IncidentEdges = incidentEdgesThm{family.Add(registry.ProofEntry{
	Name: "IncidentEdges",
	Key:  "prop_afbaa6c4fd03ea7b",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(A). ∀R:(A → A → bool). ∀v:A.",
		Hypotheses: []string{
			"symmetric_on(V, R)",
			"v ∈ V",
		},
		Conclusion: "injective_on(graph_neighbours(V, R, v), λw:A. {v, w}) ∧ " +
			"image(λw:A. {v, w}, graph_neighbours(V, R, v)) = {e:set(A) | e ∈ graph_edges(V, R) ∧ v ∈ e}",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], v *Expr[A], symmetric, inV Fact) {
		a.Do(SplitConj(
			Case(
				"a pair with one fixed endpoint determines its other endpoint",
				Unfold(functions.InjectiveOnDef),
				BySets()),
			Case(
				"orient every incident edge from v towards its other endpoint",
				Unfold(NeighboursDef),
				Unfold(EdgesDef),
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("e")
					b.Iff()
					b.Forward(
						"a neighbour gives an edge at v",
						func(c *Argument, fromNeighbour Fact) {
							_, other := c.ObtainAs[A](
								"take the neighbour paired with v",
								"∃w:A. w ∈ V ∧ R(v, w) ∧ e = {v, w}",
								BySets(fromNeighbour))
							c.Show(
								"the pair is an edge containing v",
								BySets(inV, other))
						})
					b.Backward(
						"an edge at v gives a neighbour",
						func(c *Argument, incident Fact) {
							_, _, endpoints := c.Obtain2As[A, A](
								"take an orientation of the given edge",
								"∃x y:A. x ∈ V ∧ y ∈ V ∧ R(x, y) ∧ e = {x, y}",
								BySets(incident))
							notFirst := c.Unless(
								c.Term("v = x"),
								"if v is first, y is its neighbour",
								Given(func(d *Argument, first Fact) {
									d.Show(
										"y maps to this edge",
										BySets(endpoints, first))
								}))
							second := c.Have(
								"otherwise v is the second endpoint",
								"v = y",
								BySets(incident, endpoints, notFirst))
							reverse := c.Have(
								"reverse the adjacency",
								"R(y, x)",
								By(endpoints, symmetric, equivalence.SymmetricOnDef))
							c.Show(
								"x maps to this edge",
								BySets(endpoints, second, reverse))
						})
				})),
		))
	}),
})}

// DegreeIncidence counts the incident edges using their distinct other endpoints.
var DegreeIncidence = degreeIncidenceThm{family.Add(registry.ProofEntry{
	Name: "DegreeIncidence",
	Key:  "prop_17f9bbf3cd34ae97",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(A). ∀R:(A → A → bool). ∀v:A.",
		Hypotheses: []string{
			"symmetric_on(V, R)",
			"finite(V)",
			"v ∈ V",
		},
		Conclusion: "graph_degree(V, R, v) = card({e:set(A) | e ∈ graph_edges(V, R) ∧ v ∈ e})",
	}, func(
		a *Argument,
		V *Expr[Set[A]],
		R *Arrow2[A, A, Bool],
		v *Expr[A],
		symmetric, finiteV, inV Fact,
	) {
		neighbours := a.TermAs[Set[A]]("graph_neighbours(V, R, v)")
		pairWithV := a.TermAs[Fun[A, Set[A]]]("λw:A. {v, w}")
		subset := a.Have(
			"every neighbour is a vertex",
			"graph_neighbours(V, R, v) ⊆ V",
			Unfold(NeighboursDef),
			BySets())
		a.Show(
			"the neighbours form a finite subset of V, and the injective endpoint map preserves their number",
			Unfold(DegreeDef),
			By(
				symmetric,
				inV,
				IncidentEdges.At(V, R, v),
				subset,
				finiteV,
				finite_set.FiniteSubset.At(neighbours, V),
				cardinality.CardImageInj.At(pairWithV, neighbours)))
	}),
})}

// Handshake counts vertex-edge incidences by their vertices and by
// their edges. Each edge contributes twice.
var Handshake = handshakeThm{family.Add(registry.ProofEntry{
	Name: "Handshake",
	Key:  "prop_4082f231a60dc0a2",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{
			"simple_graph_on(V, R)",
			"finite(V)",
		},
		Conclusion: "Σ_{v∈V} graph_degree(V, R, v) = 2 * card(graph_edges(V, R))",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], simple, finiteV Fact) {
		E := a.TermAs[Set[Set[A]]]("graph_edges(V, R)")
		incidence := a.TermAs[Fun2[A, Set[A], Bool]]("λv:A. λe:set(A). v ∈ e")
		finiteE := a.Have(
			"the edge set is finite",
			"finite(graph_edges(V, R))",
			By(finiteV, EdgesFinite.At(V, R)))

		byVertex := a.Have(
			"the incidences at a vertex are counted by its degree",
			"∀v:A. v ∈ V ⇒ graph_degree(V, R, v) = card({e:set(A) | e ∈ graph_edges(V, R) ∧ v ∈ e})",
			By(simple, Symmetric.At(V, R), finiteV, At(DegreeIncidence, V, R)))
		byEdge := a.Have(
			"the incidences at an edge are precisely its two endpoints",
			"∀e:set(A). e ∈ graph_edges(V, R) ⇒ card({v:A | v ∈ V ∧ v ∈ e}) = 2",
			a.ForEach(func(e *Expr[Set[A]]) Action {
				return Derive(func(b *Argument) {
					edge := b.Assume()
					endpoints := b.Have(
						"the edge lies in V, so restricting it to V leaves it intact",
						"{v:A | v ∈ V ∧ v ∈ e} = e",
						BySets(edge, EdgesSubset.At(V, R, e)))
					b.Show(
						"the edge of a simple graph has two endpoints",
						endpoints.Rw(),
						By(simple, edge, EdgeSize.At(V, R, e), cardinality.HasSizeDef.At(e, b.TermAs[Nat]("2"))))
				})
			}))

		a.Show(
			"sum the same incidences in the two orders",
			CalcEq(
				Leg(
					a.Term("Σ_{v∈V} card({e:set(A) | e ∈ graph_edges(V, R) ∧ v ∈ e})"),
					"replace the degrees by their incidence counts",
					By(byVertex, nat_sum.Congruence.Inst[A]())),
				Leg(
					a.Term("Σ_{e∈graph_edges(V, R)} card({v:A | v ∈ V ∧ v ∈ e})"),
					"exchange the two sums of incidences",
					By(finiteV, finiteE, nat_sum.DoubleCounting.At(V, E, incidence))),
				Leg(
					a.Term("Σ_{e∈graph_edges(V, R)} 2"),
					"every edge contributes twice",
					By(byEdge, nat_sum.Congruence.Inst[Set[A]]())),
				FinalLeg(
					"sum the constant two over the edges",
					By(finiteE, nat_sum.SumConst.At(E, a.TermAs[Nat]("2")), nat_arith.MulSym)),
			))
	}),
})}

// EvenOddDegreeCount follows from the even degree sum: the odd summands
// supply exactly the odd-degree vertices.
var EvenOddDegreeCount = evenOddDegreeCountThm{family.Add(registry.ProofEntry{
	Name: "EvenOddDegreeCount",
	Key:  "prop_590c35959692acca",
	Build: family.Theorem(Statement{
		Binders:    "∀V:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{"simple_graph_on(V, R)", "finite(V)"},
		Conclusion: "nat_even(card({v:A | v ∈ V ∧ nat_odd(graph_degree(V, R, v))}))",
	}, func(a *Argument, V *Expr[Set[A]], R *Arrow2[A, A, Bool], simple, finiteV Fact) {
		degree := a.TermAs[Fun[A, Nat]]("graph_degree(V, R)")
		odd := a.TermAs[Set[A]]("λv:A. nat_odd(graph_degree(V, R, v))")
		edgeCount := a.TermAs[Nat]("card(graph_edges(V, R))")
		degreeSum := a.TermAs[Nat]("Σ_{v∈V} graph_degree(V, R, v)")
		oddCount := a.TermAs[Nat]("card({v:A | v ∈ V ∧ nat_odd(graph_degree(V, R, v))})")
		evenSum := a.Have(
			"the sum of the degrees is a double",
			"nat_even(Σ_{v∈V} graph_degree(V, R, v))",
			By(simple, finiteV, Handshake.At(V, R), nat_parity.EvenDouble.At(edgeCount)))
		sameParity := a.Have(
			"the odd vertices are precisely the odd summands",
			"nat_odd(Σ_{v∈V} graph_degree(V, R, v)) ⇔ "+
				"nat_odd(card({v:A | v ∈ V ∧ nat_odd(graph_degree(V, R, v))}))",
			By(finiteV, nat_sum.OddSumIffOddCount.At(V, degree, odd)))
		a.Show(
			"the count of odd-degree vertices is even",
			By(
				evenSum,
				sameParity,
				nat_parity.EvenIffNotOdd.At(degreeSum),
				nat_parity.EvenIffNotOdd.At(oddCount)))
	}),
})}
