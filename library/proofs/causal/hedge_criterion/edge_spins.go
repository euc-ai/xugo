// edge_spins.go — fair spins on the edges of a connected graph. A vertex
// carries the product of the signs of the edges at it, its spin. The edge
// set is read as a connected graph of simple_graph (edgeSetConnectedGraph),
// and a product over the vertices exchanges with a product over the edges
// (incidenceProductSwap). Averaged over the spins, the product of the spins
// of a set of vertices vanishes unless the set is empty or all of the graph
// (connectedSpinAverage); one track of spins keeps two terms of a product
// of binomials over the vertices (singleTrackExpansion), and independent
// tracks, added one at a time (trackSumSplit), keep one term more for each
// track (spinTrackExpansion).

package hedge_criterion

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/simple_graph"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// edgeSetConnectedGraph — a finite set of edges with both ends in F that
// joins any two vertices of F by a chain makes F a connected graph with
// finitely many edges, two vertices adjacent when an edge joins them in
// either order. An adjacency joins two vertices of F, so a chain is a walk
// in F; and an edge of the graph is the set of the two ends of a pair of
// Ed, of which there are finitely many.
var edgeSetConnectedGraph = edgeSetConnectedGraphThm{family.Add(registry.ProofEntry{
	Name: "edgeSetConnectedGraph",
	Key:  "prop_d8cc2eb869811a11",
	Build: family.Theorem(Statement{
		Binders: "∀F:set(I). ∀Ed:set(prod(I, I)).",
		Hypotheses: []string{
			"finite(Ed)",
			"∀e:prod(I, I). e ∈ Ed ⇒ fst(e) ∈ F ∧ snd(e) ∈ F",
			"∀u v:I. u ∈ F ∧ v ∈ F ⇒ reflexive_transitive_closure(«adjacent», u, v)",
		},
		Conclusion: "graph_connected(F, «adjacent») ∧ finite(graph_edges(F, «adjacent»))",
	}, func(a *Argument, F *Expr[Set[I]], Ed *Expr[Set[Prod[I, I]]], finiteEd, ends, chains Fact) {
		adjacent := a.TermAs[Fun2[I, I, Bool]]("«adjacent»")
		restricted := a.TermAs[Fun2[I, I, Bool]]("relation_on(F, «adjacent»)")
		inside := a.Have(
			"an edge joins two vertices of F, so its adjacency is one of the graph on F",
			"∀x y:I. «adjacent»(x, y) ⇒ relation_on(F, «adjacent», x, y)",
			By(ends, equivalence.RelationOnDef, pairs.Fst, pairs.Snd))
		connectedGraph := a.Have(
			"a chain of edges between two vertices of F is a walk in F",
			"graph_connected(F, «adjacent»)",
			Unfold(simple_graph.ConnectedDef),
			Derive(func(b *Argument) {
				u := b.FixAs[I]("u")
				v := b.FixAs[I]("v")
				vertices := b.Assume()
				b.Show(
					"every step of the chain is an adjacency of the graph on F",
					Simp(Fwd(simple_graph.ReachableDef)),
					By(
						vertices,
						chains.At(u, v),
						inside,
						closure.ReflexiveTransitiveClosureMonotone.At(adjacent, restricted, u, v)))
			}))
		endsOf := a.TermAs[Fun[Prod[I, I], Set[I]]]("λe:prod(I, I). {fst(e), snd(e)}")
		edgeSets := a.TermAs[Set[Set[I]]]("graph_edges(F, «adjacent»)")
		endSets := a.TermAs[Set[Set[I]]]("image(λe:prod(I, I). {fst(e), snd(e)}, Ed)")
		covered := a.Have(
			"an edge of the graph is the set of the two ends of a pair of Ed",
			"graph_edges(F, «adjacent») ⊆ image(λe:prod(I, I). {fst(e), snd(e)}, Ed)",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				b.FixAs[Set[I]]("s")
				edge := b.Assume()
				u, v, joined := b.Unpack2As[I, I](b.Unfolded(edge, simple_graph.EdgesDef), "u", "v")
				b.Show(
					"and {u, v} is the set of the ends of (u, v) or of (v, u), whichever lies in Ed",
					By(
						joined,
						set_image.FunInImage.At(endsOf, Ed, b.TermAs[Prod[I, I]]("(u, v)")),
						set_image.FunInImage.At(endsOf, Ed, b.TermAs[Prod[I, I]]("(v, u)")),
						pairs.Fst,
						pairs.Snd,
						set_algebra.InsertComm.At(b.TermAs[Set[I]]("∅"), u, v)))
			}))
		a.Show(
			"so the graph is connected and its edges are among finitely many sets",
			By(
				connectedGraph,
				finiteEd,
				covered,
				finite_set.FiniteImage.At(endsOf, Ed),
				finite_set.FiniteSubset.At(edgeSets, endSets)))
	}),
})}

// incidenceProductSwap — over a finite set of edges, the product over
// the vertices of S of the products over the edges at each vertex is the
// product over the edges of the products over each edge's ends in S. S
// may be infinite: only its vertices on some edge matter, they are among
// the endpoints of the finitely many edges, and over them the two
// products exchange, each inner index set read as a condition on the
// other one.
var incidenceProductSwap = incidenceProductSwapThm{family.Add(registry.ProofEntry{
	Name: "incidenceProductSwap",
	Key:  "prop_2d64ac80b22302e9",
	Build: family.Theorem(Statement{
		Binders:    "∀Ed:set(prod(I, I)). ∀S:set(I). ∀f:(prod(I, I) → real).",
		Hypotheses: []string{"finite(Ed)"},
		Conclusion: "Π_{v∈S} Π_{e∈«edgesAt»(v)} f(e) = Π_{e∈Ed} Π_{v∈«ends»(e)} f(e)",
	}, func(
		a *Argument,
		Ed *Expr[Set[Prod[I, I]]],
		S *Expr[Set[I]],
		f *Arrow[Prod[I, I], Real],
		finiteEd Fact,
	) {
		T, tDef := a.LetAs[Set[I]](
			"T", "{v:I | v ∈ S ∧ (∃e:prod(I, I). e ∈ Ed ∧ (fst(e) = v ∨ snd(e) = v))}")
		endpoints := a.TermAs[Set[I]]("image(λe:prod(I, I). fst(e), Ed) ∪ image(λe:prod(I, I). snd(e), Ed)")
		finiteT := a.Have(
			"the vertices of S on an edge are among the endpoints of the finitely many edges",
			"finite(T)",
			BySets(
				finiteEd,
				tDef,
				finite_set.FiniteSubset.At(T, endpoints),
				finite_set.FiniteUnionImp,
				finite_set.FiniteImage))
		inside := a.Have(
			"and they are vertices of S",
			"T ⊆ S",
			BySets(tDef))
		silent := a.Have(
			"a vertex of S on no edge has an empty star, whose product is 1",
			"∀x:I. x ∈ S ∧ x ∉ T ⇒ Π_{e∈«edgesAt»(x)} f(e) = &1",
			Unfold(real_product.RealProductDef),
			BySets(tDef, monoidal.EqNeutral.Read(real_ring.MonoidalMul), real_ring.NeutralMul))
		overEdges := a.Have(
			"the product over a star is the product over all the edges, silenced off the star",
			"∀v:I. Π_{e∈«edgesAt»(v)} f(e) = Π_{e∈Ed} COND(fst(e) = v ∨ snd(e) = v, f(e), &1)",
			a.ForEach(func(_ *Expr[I]) Action {
				return By(real_product.Restrict)
			}))
		overEnds := a.Have(
			"for an edge of Ed, the product over T silenced off its ends is the product over its ends in S",
			"∀e:prod(I, I). e ∈ Ed ⇒ Π_{v∈T} COND(fst(e) = v ∨ snd(e) = v, f(e), &1) = Π_{v∈«ends»(e)} f(e)",
			Derive(func(b *Argument) {
				b.FixAs[Prod[I, I]]()
				eIn := b.Assume()
				sameEnds := b.Have(
					"an end of an edge of Ed that lies in S lies in T",
					"«ends»(e) = {v:I | v ∈ T ∧ (fst(e) = v ∨ snd(e) = v)}",
					BySets(tDef, eIn))
				b.Show(
					"and the product over the ends in T is the silenced product over T",
					sameEnds.Rw(),
					By(real_product.Restrict))
			}))
		a.Show(
			"restrict to T, read each star over all the edges, exchange, and read each edge over its ends",
			CalcEq(
				Leg(
					a.TermAs[Real]("Π_{v∈T} Π_{e∈«edgesAt»(v)} f(e)"),
					"the vertices of S outside T contribute 1",
					By(silent, inside, real_product.Superset)),
				Leg(
					a.TermAs[Real]("Π_{v∈T} Π_{e∈Ed} COND(fst(e) = v ∨ snd(e) = v, f(e), &1)"),
					"each star's product is read over all of Ed",
					Simp(Fwd(overEdges))),
				Leg(
					a.TermAs[Real]("Π_{e∈Ed} Π_{v∈T} COND(fst(e) = v ∨ snd(e) = v, f(e), &1)"),
					"the products over the finite sets T and Ed exchange",
					By(finiteT, finiteEd, real_product.Swap)),
				FinalLeg(
					"each edge's product over T is the product over its ends in S",
					By(overEnds, real_product.Congruence))))
	}),
})}

// connectedSpinAverage — fair spins on the edges of a connected graph
// average the product of the vertex terms of S to 0 unless S is empty or
// everything. The summand is the product over the edges of each edge's
// sign, once for each of its ends in S. With S empty or all of F every
// edge has no end or both its ends in S, its factor is 1, and the sum
// counts the sets of edges. Otherwise some edge has exactly one end in
// S, toggling its spin negates the summand, and the sum vanishes.
var connectedSpinAverage = connectedSpinAverageThm{family.Add(registry.ProofEntry{
	Name: "connectedSpinAverage",
	Key:  "prop_e0825c9aed1ab39d",
	Reading: "σ is the set of edges whose spin is −1. An edge is an ordered pair, " +
		"and a pair listed in both orders carries two spins. No loops: a loop would be " +
		"counted once at its vertex. Connectivity, both ends in F and S ⊆ F are each " +
		"load-bearing: two vertices with no edge and S one of them give 1 on the left " +
		"and 0 on the right. With F one vertex there is no edge and both sets S give 1.",
	Build: family.Theorem(Statement{
		Binders: "∀F:set(I). ∀Ed:set(prod(I, I)). ∀S:set(I).",
		Hypotheses: []string{
			"finite(Ed)",
			"∀e:prod(I, I). e ∈ Ed ⇒ fst(e) ∈ F ∧ snd(e) ∈ F ∧ fst(e) ≠ snd(e)",
			"∀u v:I. u ∈ F ∧ v ∈ F ⇒ reflexive_transitive_closure(«adjacent», u, v)",
			"S ⊆ F",
		},
		Conclusion: "Σ_{σ∈{σ:set(prod(I, I)) | σ ⊆ Ed}} Π_{v∈S} «spin»(σ, v) = " +
			"COND(S = ∅ ∨ S = F, &(2 ^ card(Ed)), &0)",
		Abbrev: Abbrev{
			{Name: "summand", Text: "λσ:set(prod(I, I)). Π_{v∈S} «spin»(σ, v)"},
			{Name: "factor", Text: "λσ:set(prod(I, I)). λe:prod(I, I). Π_{v∈«ends»(e)} «sgn»(e ∈ σ)"},
		},
	}, func(
		a *Argument,
		F *Expr[Set[I]],
		Ed *Expr[Set[Prod[I, I]]],
		S *Expr[Set[I]],
		finiteEd, edges, connected, sub Fact,
	) {
		exchange := a.Have(
			"the summand is the product of the edges' factors, an edge's sign once for each of its ends in S",
			"∀σ:set(prod(I, I)). «summand»(σ) = Π_{e∈Ed} «factor»(σ, e)",
			By(finiteEd, incidenceProductSwap))
		a.Cases(a.TermAs[Bool]("S = ∅ ∨ S = F"))
		a.When(
			"S is empty or all of F: every summand is 1, and the sum counts the sets of edges",
			func(b *Argument, full Fact) {
				square := b.Have(
					"an edge has no end in S or both, and its factor is 1 or the square of its sign",
					"∀σ:set(prod(I, I)). ∀e:prod(I, I). e ∈ Ed ⇒ «factor»(σ, e) = &1",
					Derive(func(d *Argument) {
						d.FixAs[Set[Prod[I, I]]]()
						e := d.FixAs[Prod[I, I]]()
						eIn := d.Assume()
						ends := d.Have(
							"with S empty the edge has no end in S, with S = F both of its ends",
							"«ends»(e) = ∅ ∨ «ends»(e) = {fst(e), snd(e)}",
							BySets(edges.At(e), eIn, full))
						d.Do(ends.SplitDisj(
							LeftHolds(
								"the edge has no end in S",
								Given(func(g *Argument, none Fact) {
									g.Show(
										"and the empty product is 1",
										By(none, real_product.ProductClauses))
								})),
							RightHolds(
								"the edge has both its ends in S",
								Given(func(g *Argument, both Fact) {
									g.Show(
										"they are distinct, and the factor is the sign times itself",
										both.Rw(),
										Simp(
											Fwd(real_product.ProductClauses),
											Fwd(finite_set.FiniteRules),
											Fwd(set_basic.InSing),
											Fwd(set_basic.NotInEmpty)),
										ByArith(edges.At(e), eIn))
								}))))
					}))
				unit := b.Have(
					"so every summand, the product of these factors, is 1",
					"∀σ:set(prod(I, I)). «summand»(σ) = &1",
					b.ForEach(func(σ *Expr[Set[Prod[I, I]]]) Action {
						return By(
							square.At(σ),
							exchange.At(σ),
							monoidal.EqNeutral.Read(real_ring.MonoidalMul),
							real_ring.NeutralMul,
							real_product.RealProductDef)
					}))
				subsets := b.TermAs[Set[Set[Prod[I, I]]]]("{σ:set(prod(I, I)) | σ ⊆ Ed}")
				b.Show(
					"and the sum of 1 over the sets of edges is their number, 2 ^ card(Ed)",
					By(
						finiteEd,
						unit,
						full,
						real_sum.Congruence.At(
							subsets,
							b.TermAs[Fun[Set[Prod[I, I]], Real]]("«summand»"),
							b.TermAs[Fun[Set[Prod[I, I]], Real]]("λσ:set(prod(I, I)). &1")),
						real_sum.CardAsSum.At(subsets),
						finite_set.FinitePowerset.At(Ed),
						cardinality.CardPowerset.At(Ed)))
			})
		a.Otherwise(
			"S is neither: an edge has exactly one end in S, and toggling its spin negates the summand",
			func(b *Argument, proper Fact) {
				adjacent := b.TermAs[Fun2[I, I, Bool]]("«adjacent»")
				neither := b.Have(
					"S is not empty and not all of F",
					"S ≠ ∅ ∧ S ≠ F",
					By(Normalized, proper))
				_, _, cut := b.Obtain2As[I, I](
					"the edges make F a connected graph, so an edge of "+
						"Ed joins a vertex x of S to a vertex y of F outside S",
					"∃x y:I. x ∈ S ∧ y ∈ F ∧ y ∉ S ∧ ((x, y) ∈ Ed ∨ (y, x) ∈ Ed)",
					By(
						finiteEd,
						edges,
						connected,
						sub,
						neither,
						edgeSetConnectedGraph.At(F, Ed),
						simple_graph.ConnectedCut.At(F, adjacent, S)))
				c, crossing := b.ObtainAs[Prod[I, I]](
					"that edge, (x, y) or (y, x), has exactly one end in S",
					"∃c:prod(I, I). c ∈ Ed ∧ ((fst(c) ∈ S ∧ snd(c) ∉ S) ∨ (snd(c) ∈ S ∧ fst(c) ∉ S))",
					By(cut, pairs.Fst, pairs.Snd))
				_, single := b.ObtainAs[I](
					"the ends of that edge in S are a single vertex",
					"∃a:I. «ends»(c) = {a}",
					BySets(crossing))
				split := b.Have(
					"the summand is the sign of c times the factors of the other edges",
					"∀σ:set(prod(I, I)). «summand»(σ) = «sgn»(c ∈ σ) * Π_{e∈delete(Ed, c)} «factor»(σ, e)",
					Derive(func(d *Argument) {
						σ := d.FixAs[Set[Prod[I, I]]]()
						own := d.Have(
							"the factor of c, a product over its one end in S, is its sign",
							"«factor»(σ, c) = «sgn»(c ∈ σ)",
							By(single, real_product.Sing))
						d.Show(
							"and c splits off the product over the edges",
							By(
								finiteEd,
								exchange.At(σ),
								own,
								crossing,
								real_product.Delete.At(Ed, d.TermAs[Fun[Prod[I, I], Real]]("«factor»(σ)"), c)))
					}))
				odd := b.Have(
					"toggling the spin of c negates the summand",
					"∀σ:set(prod(I, I)). «summand»(set_toggle(c, σ)) = -«summand»(σ)",
					Derive(func(d *Argument) {
						σ := d.FixAs[Set[Prod[I, I]]]()
						others := d.Have(
							"the toggle leaves the spin of every other edge, so the other factors agree",
							"Π_{e∈delete(Ed, c)} «factor»(set_toggle(c, σ), e) = Π_{e∈delete(Ed, c)} «factor»(σ, e)",
							By(
								monoidal.Congruence.Read(real_ring.MonoidalMul).At(
									d.TermAs[Set[Prod[I, I]]]("delete(Ed, c)"),
									d.TermAs[Fun[Prod[I, I], Real]]("«factor»(set_toggle(c, σ))"),
									d.TermAs[Fun[Prod[I, I], Real]]("«factor»(σ)")),
								set_basic.InToggle,
								set_basic.InDelete,
								real_product.RealProductDef))
						d.Show(
							"and reverses the spin of c itself",
							ByArith(
								split.At(d.TermAs[Set[Prod[I, I]]]("set_toggle(c, σ)")),
								split.At(σ),
								others,
								set_basic.InToggle.At(c, σ, c)))
					}))
				b.Show(
					"so the sum over the sets of edges vanishes",
					By(
						proper,
						odd,
						crossing,
						real_sum.SubsetsSumToggleOdd.At(Ed, c, b.TermAs[Fun[Set[Prod[I, I]], Real]]("«summand»"))))
			})
	}),
})}

// singleTrackExpansion — averaged over fair spins on the edges of a connected
// graph, the product over G of c(v) + t(v) · spin(v) keeps the product of c
// and, when G is all of F, the product of t. The product of binomials expands
// over the subsets S of G that take the spin term
// (real_product.ProductOfBinomials); the sum over the spins goes inside, where
// connectedSpinAverage leaves S = ∅ and S = F; and S = F is a subset of G only
// when G = F.
var singleTrackExpansion = singleTrackExpansionThm{family.Add(registry.ProofEntry{
	Name: "singleTrackExpansion",
	Key:  "prop_f3aa2aeb463aa5fe",
	Build: family.Theorem(Statement{
		Binders: "∀F G:set(I). ∀Ed:set(prod(I, I)). ∀c t:(I → real).",
		Hypotheses: []string{
			"finite(Ed)",
			"∀e:prod(I, I). e ∈ Ed ⇒ fst(e) ∈ F ∧ snd(e) ∈ F ∧ fst(e) ≠ snd(e)",
			"∀u v:I. u ∈ F ∧ v ∈ F ⇒ reflexive_transitive_closure(«adjacent», u, v)",
			"F ≠ ∅",
			"G ⊆ F",
		},
		Conclusion: "Σ_{σ∈{σ:set(prod(I, I)) | σ ⊆ Ed}} Π_{v∈G} (c(v) + t(v) * «spin»(σ, v)) = " +
			"&(2 ^ card(Ed)) * (Π_{v∈G} c(v) + COND(G = F, Π_{v∈F} t(v), &0))",
		Abbrev: Abbrev{
			{Name: "configs", Text: "{σ:set(prod(I, I)) | σ ⊆ Ed}"},
			{Name: "subsets", Text: "{S:set(I) | S ⊆ G}"},
			{Name: "weight", Text: "λS:set(I). (Π_{v∈G ∖ S} c(v)) * Π_{v∈S} t(v)"},
		},
	}, func(
		a *Argument,
		F, G *Expr[Set[I]],
		Ed *Expr[Set[Prod[I, I]]],
		c, t *Arrow[I, Real],
		finiteEd, edges, connected, nonempty, sub Fact,
	) {
		finiteG := a.Have(
			"the edges connect F, so F is finite, and G with it",
			"finite(G)",
			By(
				finiteEd,
				edges,
				connected,
				sub,
				edgeSetConnectedGraph.At(F, Ed),
				simple_graph.ConnectedVerticesFinite.At(
					F, a.TermAs[Fun2[I, I, Bool]]("«adjacent»")),
				finite_set.FiniteSubset.At(G, F)))
		finiteConfigs := a.Have(
			"there are finitely many sets of edges",
			"finite(«configs»)",
			By(finiteEd, finite_set.FinitePowerset))
		finiteSubsets := a.Have(
			"and finitely many subsets of G",
			"finite(«subsets»)",
			By(finiteG, finite_set.FinitePowerset))
		expand := a.Have(
			"at each σ the product of binomials expands over the subsets S of G that take the spin term",
			"∀σ:set(prod(I, I)). "+
				"    Π_{v∈G} (c(v) + t(v) * «spin»(σ, v)) = Σ_{S∈«subsets»} «weight»(S) * Π_{v∈S} «spin»(σ, v)",
			Derive(func(b *Argument) {
				b.FixAs[Set[Prod[I, I]]]()
				b.Do(Simp(Fwd(real_product.ProductOfBinomials)))
				regroup := b.Have(
					"over S the factors t(v) leave the product of the spin terms and join the weight",
					Statement{
						Binders:    "∀S:set(I).",
						Hypotheses: []string{"S ⊆ G"},
						Conclusion: "(Π_{v∈G ∖ S} c(v)) * Π_{v∈S} (t(v) * «spin»(σ, v)) = " +
							"«weight»(S) * Π_{v∈S} «spin»(σ, v)",
					},
					Derive(func(d *Argument) {
						d.FixAs[Set[I]]()
						inG := d.Assume()
						factor := d.Have(
							"a finite product of products is the product of the two products",
							"Π_{v∈S} (t(v) * «spin»(σ, v)) = (Π_{v∈S} t(v)) * Π_{v∈S} «spin»(σ, v)",
							By(finiteG, inG, finite_set.FiniteSubset, real_product.Pointwise))
						d.Show(
							"and multiplication is associative",
							By(factor, real_construction.MulAssoc))
					}))
				b.Show(
					"so the two sums over the subsets of G agree term by term",
					By(regroup, real_sum.Congruence))
			}))
		value := a.Have(
			"the spins average the term of S to 0 unless S is ∅, which "+
				"leaves the product of c, or F, which leaves that of t",
			Statement{
				Binders:    "∀S:set(I).",
				Hypotheses: []string{"S ⊆ G"},
				Conclusion: "«weight»(S) * Σ_{σ∈«configs»} Π_{v∈S} «spin»(σ, v) = " +
					"COND(S = ∅, &(2 ^ card(Ed)) * Π_{v∈G} c(v), &0) + COND(S = F, &(2 ^ card(Ed)) * Π_{v∈F} t(v), &0)",
			},
			Derive(func(b *Argument) {
				S := b.FixAs[Set[I]]()
				inG := b.Assume()
				inF := b.Have(
					"S lies in F, as G does",
					"S ⊆ F",
					BySets(sub, inG))
				average := b.Have(
					"the spins of a connected graph average the vertex terms of S to 0 unless S is empty or all of F",
					"Σ_{σ∈«configs»} Π_{v∈S} «spin»(σ, v) = COND(S = ∅ ∨ S = F, &(2 ^ card(Ed)), &0)",
					By(finiteEd, edges, connected, inF, connectedSpinAverage.At(F, Ed, S)))
				b.Do(average.Rw())
				notFull := b.Unless(
					b.TermAs[Bool]("S = F"),
					"at S = F, which is not empty, the set G is F too, no "+
						"factor c remains and the weight is the product of t over F",
					Given(func(d *Argument, full Fact) {
						whole := d.Have(
							"G lies between S and F",
							"G = F",
							BySets(full, sub, inG))
						d.Do(
							whole.Rw(),
							full.Rw(),
							Simp(Fwd(set_algebra.DiffEqEmpty), Fwd(real_product.ProductClauses), Fwd(nonempty)),
							ByArith())
					}))
				notEmpty := b.Unless(
					b.TermAs[Bool]("S = ∅"),
					"at S = ∅, which is not F, the weight is the product of c over G",
					Given(func(d *Argument, empty Fact) {
						d.Do(
							empty.Rw(),
							Simp(Fwd(set_algebra.DiffEmpty), Fwd(real_product.ProductClauses)),
							ByArith())
					}))
				b.Show(
					"at any other S the average is 0",
					ByArith(notFull, notEmpty))
			}))
		fullIn := a.Have(
			"F is a subset of G only when G is F",
			"F ∈ «subsets» ⇔ G = F",
			BySets(sub))
		a.Show(
			"take the sum over the spins inside the expansion: the subsets ∅ and F are all that is left",
			CalcEq(
				Leg(
					a.TermAs[Real]("Σ_{σ∈«configs»} Σ_{S∈«subsets»} «weight»(S) * Π_{v∈S} «spin»(σ, v)"),
					"expand the product at each set of edges",
					Simp(Fwd(expand))),
				Leg(
					a.TermAs[Real]("Σ_{S∈«subsets»} Σ_{σ∈«configs»} «weight»(S) * Π_{v∈S} «spin»(σ, v)"),
					"exchange the two finite sums",
					By(finiteSubsets, finiteConfigs, real_sum.Swap)),
				Leg(
					a.TermAs[Real](
						"Σ_{S∈«subsets»} (COND(S = ∅, &(2 ^ card(Ed)) * Π_{v∈G} c(v), &0) + COND(S = F, &(2 ^ card(Ed)) * Π_{v∈F} t(v), &0))"),
					"the weight leaves the inner sum, which is the average of the spins at S",
					Simp(Rev(real_sum.ScalarLeft)),
					By(value, real_sum.Congruence)),
				Leg(
					a.TermAs[Real](
						"COND(∅ ∈ «subsets», &(2 ^ card(Ed)) * Π_{v∈G} c(v), &0) + "+
							"COND(F ∈ «subsets», &(2 ^ card(Ed)) * Π_{v∈F} t(v), &0)"),
					"each of the two terms is carried by one subset",
					Simp(Rev(real_sum.Add), Fwd(real_sum.Delta), Fwd(finiteSubsets)),
					Basic()),
				FinalLeg(
					"∅ is a subset of G, and F is one exactly when G = F",
					fullIn.Rw(),
					ByArith(set_order.EmptySubset))))
	}),
})}

// trackSumSplit — a set of spins that is Y over the tracks Θ together
// with Z at a new track θ gives, at a vertex, the term of θ read on Z
// plus the sum over Θ read on Y: a pair at θ is in Y ∪ Z only through Z,
// and a pair at a track of Θ only through Y.
var trackSumSplit = trackSumSplitThm{family.Add(registry.ProofEntry{
	Name: "trackSumSplit",
	Key:  "prop_41efe28b41e9e89a",
	Build: family.Theorem(Statement{
		Binders: "∀Ed:set(prod(I, I)). " +
			"∀Θ:set(C). " +
			"∀θ:C. " +
			"∀Y Z:set(prod(prod(I, I), C)). " +
			"∀t:(C → real). " +
			"∀v:I.",
		Hypotheses: []string{
			"finite(Θ)",
			"θ ∉ Θ",
			"Y ⊆ set_cross(Ed, Θ)",
			"Z ⊆ set_cross(Ed, {θ})",
		},
		Conclusion: "Σ_{τ∈insert(θ, Θ)} t(τ) * «trackSpin»(Y ∪ Z, τ, v) = " +
			"t(θ) * «trackSpin»(Z, θ, v) + Σ_{τ∈Θ} t(τ) * «trackSpin»(Y, τ, v)",
	}, func(
		a *Argument,
		Ed *Expr[Set[Prod[I, I]]],
		Θ *Expr[Set[C]],
		θ *Expr[C],
		Y, Z *Expr[Set[Prod[Prod[I, I], C]]],
		t *Arrow[C, Real],
		v *Expr[I],
		finiteΘ, fresh, oldPairs, newPairs Fact,
	) {
		newTrack := a.Have(
			"a pair at θ is in Y ∪ Z only through Z",
			"∀e:prod(I, I). (e, θ) ∈ Y ∪ Z ⇔ (e, θ) ∈ Z",
			BySets(fresh, oldPairs, set_product.InCross))
		oldTracks := a.Have(
			"at a track of Θ the spin of Y ∪ Z is the spin of Y",
			"∀τ:C. τ ∈ Θ ⇒ t(τ) * «trackSpin»(Y ∪ Z, τ, v) = t(τ) * «trackSpin»(Y, τ, v)",
			Derive(func(b *Argument) {
				b.FixAs[C]()
				old := b.Assume()
				only := b.Have(
					"a pair at a track of Θ is in Y ∪ Z only through Y",
					"∀e:prod(I, I). (e, τ) ∈ Y ∪ Z ⇔ (e, τ) ∈ Y",
					BySets(fresh, old, newPairs, set_product.InCross))
				b.Show(
					"so the two products of signs have the same factors",
					Simp(Fwd(only)),
					Refl())
			}))
		oldSum := a.Have(
			"so the sum over Θ reads Y alone",
			"Σ_{τ∈Θ} t(τ) * «trackSpin»(Y ∪ Z, τ, v) = Σ_{τ∈Θ} t(τ) * «trackSpin»(Y, τ, v)",
			By(oldTracks, real_sum.Congruence))
		a.Show(
			"split off the term at θ and read each part on its own set of spins",
			CalcEq(
				Leg(
					a.TermAs[Real]("t(θ) * «trackSpin»(Y ∪ Z, θ, v) + Σ_{τ∈Θ} t(τ) * «trackSpin»(Y ∪ Z, τ, v)"),
					"θ is not in Θ, so the sum over insert(θ, Θ) is the term at θ plus the sum over Θ",
					Simp(Fwd(real_sum.Clauses), Fwd(finiteΘ), Fwd(fresh)),
					Basic()),
				Leg(
					a.TermAs[Real]("t(θ) * «trackSpin»(Z, θ, v) + Σ_{τ∈Θ} t(τ) * «trackSpin»(Y ∪ Z, τ, v)"),
					"the term at θ reads Z",
					Simp(Fwd(newTrack))),
				FinalLeg(
					"and the sum over Θ reads Y",
					By(oldSum))))
	}),
})}

// spinTrackExpansion — averaged over independent tracks of fair spins on the
// edges of a connected graph, the product over G of c(v) plus the sum over the
// tracks of t(v, θ) · spin(v, θ) keeps the product of c and, when G is all of
// F, for each track the product of its t. Induct on the tracks. The spins of a
// new track θ split off the sum (real_sum.SubsetsSumDisjointUnion); with the
// other spins fixed each factor is the old factor plus the term of θ
// (trackSumSplit), the spins at θ are the subsets of Ed
// (real_sum.SubsetsSumCrossSingleton), and singleTrackExpansion averages them.
// The old factors then sum by the induction hypothesis.
var spinTrackExpansion = spinTrackExpansionThm{family.Add(registry.ProofEntry{
	Name: "spinTrackExpansion",
	Key:  "prop_d81ba1e836125fa4",
	Reading: "σ is the set of pairs of an edge and a track whose spin is −1: each " +
		"track θ carries its own spin on every edge. F ≠ ∅ is load-bearing once there is a " +
		"track: with F empty the left side is 1 and the right side 1 + card(Θ). So are G ⊆ " +
		"F and connectivity, as in connectedSpinAverage. The second term is there only " +
		"when the product runs over all of F. With no track the sum is the product of c.",
	Build: family.Theorem(Statement{
		Binders: "∀F G:set(I). ∀Ed:set(prod(I, I)). ∀Θ:set(C). ∀c:(I → real). ∀t:(I → C → real).",
		Hypotheses: []string{
			"finite(Ed)",
			"∀e:prod(I, I). e ∈ Ed ⇒ fst(e) ∈ F ∧ snd(e) ∈ F ∧ fst(e) ≠ snd(e)",
			"∀u v:I. u ∈ F ∧ v ∈ F ⇒ reflexive_transitive_closure(«adjacent», u, v)",
			"finite(Θ)",
			"F ≠ ∅",
			"G ⊆ F",
		},
		Conclusion: "Σ_{σ∈«configs»(Θ)} Π_{v∈G} (c(v) + Σ_{θ∈Θ} t(v, θ) * «trackSpin»(σ, θ, v)) = " +
			"&(2 ^ (card(Ed) * card(Θ))) * (Π_{v∈G} c(v) + COND(G = F, Σ_{θ∈Θ} Π_{v∈F} t(v, θ), &0))",
		Abbrev: Abbrev{
			{Name: "configs", Text: "λK:set(C). {σ:set(prod(prod(I, I), C)) | σ ⊆ set_cross(Ed, K)}"},
			{Name: "factor", Text: "λK:set(C). λσ:set(prod(prod(I, I), C)). λv:I. " +
				"    c(v) + Σ_{τ∈K} t(v, τ) * «trackSpin»(σ, τ, v)"},
		},
	}, func(
		a *Argument,
		F, G *Expr[Set[I]],
		Ed *Expr[Set[Prod[I, I]]],
		Θ *Expr[Set[C]],
		c *Arrow[I, Real],
		t *Arrow2[I, C, Real],
		finiteEd, edges, connected, finiteΘ, nonempty, sub Fact,
	) {
		a.Show(
			"by induction on the finite set of tracks",
			ByInduction(finite_set.FiniteInductFresh.Inst[C](), finiteΘ,
				Case(
					"with no track the only set of spins is the empty one, and each factor is c(v)",
					Derive(func(b *Argument) {
						noPairs := b.Have(
							"no pair has a track",
							"set_cross(Ed, ∅⟨A:C⟩) = ∅",
							By(set_product.CrossEmptyIff.At(Ed, b.TermAs[Set[C]]("∅"))))
						b.Show(
							"the sum is its one term at ∅, the product of c, and 2 ^ 0 is 1",
							noPairs.Rw(),
							Simp(
								Fwd(finite_set.PowersetClauses),
								Fwd(real_sum.Clauses),
								Fwd(cardinality.CardClauses),
								Fwd(finite_set.FiniteRules),
								Fwd(set_basic.NotInEmpty),
								Fwd(real_ring.AddRightId)),
							ByArith())
					})),
				Case(
					"one more track θ beside the tracks T: its spins split off the sum and average as one track does",
					Derive(func(b *Argument) {
						θ := b.FixAs[C]("θ")
						T := b.FixAs[Set[C]]("T")
						parts := b.Conjuncts(
							b.Assume(),
							"the expansion holds over the tracks T",
							"θ is not one of them",
							"and T is finite")
						ih, fresh, finiteT := parts[0], parts[1], parts[2]
						split := b.Have(
							"the pairs over insert(θ, T) are the pairs over T and the pairs at θ",
							"set_cross(Ed, insert(θ, T)) = set_cross(Ed, T) ∪ set_cross(Ed, {θ})",
							BySets(set_product.InCrossProjections))
						apart := b.Have(
							"and no pair is both, θ being new",
							"disjoint(set_cross(Ed, T), set_cross(Ed, {θ}))",
							BySets(fresh, set_product.InCrossProjections))
						finiteOld := b.Have(
							"there are finitely many pairs over T",
							"finite(set_cross(Ed, T))",
							By(finiteT, finiteEd, finite_set.FiniteProduct))
						finiteNew := b.Have(
							"and finitely many pairs at θ",
							"finite(set_cross(Ed, {θ}))",
							By(finiteEd, finite_set.FiniteProduct, finite_set.FiniteSing))
						factorAt := b.Have(
							"at Y ∪ Z a factor is the factor over T at Y plus the term of the track θ, which reads Z",
							Statement{
								Binders: "∀Y Z:set(prod(prod(I, I), C)).",
								Hypotheses: []string{
									"Y ⊆ set_cross(Ed, T)",
									"Z ⊆ set_cross(Ed, {θ})",
								},
								Conclusion: "Π_{v∈G} «factor»(insert(θ, T), Y ∪ Z, v) = " +
									"Π_{v∈G} («factor»(T, Y, v) + t(v, θ) * «trackSpin»(Z, θ, v))",
							},
							Derive(func(d *Argument) {
								Y := d.FixAs[Set[Prod[Prod[I, I], C]]]()
								Z := d.FixAs[Set[Prod[Prod[I, I], C]]]()
								bothIn := d.Assume()
								perVertex := d.Have(
									"at each vertex the sum over the tracks splits off its term at θ",
									"∀v:I. «factor»(insert(θ, T), Y ∪ Z, v) = «factor»(T, Y, v) + t(v, θ) * «trackSpin»(Z, θ, v)",
									Derive(func(e *Argument) {
										v := e.FixAs[I]()
										e.Show(
											"the term at θ reads Z and the sum over T reads Y",
											ByArith(
												finiteT,
												fresh,
												bothIn,
												trackSumSplit.At(Ed, T, θ, Y, Z, e.TermAs[Fun[C, Real]]("t(v)"), v)))
									}))
								d.Show(
									"so the two products have the same factors",
									Simp(Fwd(perVertex)),
									Refl())
							}))
						inner := b.Have(
							"with the spins Y of the old tracks fixed, the spins at θ average as the spins of one track do",
							Statement{
								Binders:    "∀Y:set(prod(prod(I, I), C)).",
								Hypotheses: []string{"Y ⊆ set_cross(Ed, T)"},
								Conclusion: "Σ_{Z∈«configs»({θ})} Π_{v∈G} «factor»(insert(θ, T), Y ∪ Z, v) = " +
									"&(2 ^ card(Ed)) * (Π_{v∈G} «factor»(T, Y, v) + COND(G = F, Π_{v∈F} t(v, θ), &0))",
							},
							Derive(func(d *Argument) {
								d.FixAs[Set[Prod[Prod[I, I], C]]]()
								oldPairs := d.Assume()
								d.Show(
									"read each set Z of spins at θ as the set of its edges",
									CalcEq(
										Leg(
											d.TermAs[Real]("Σ_{Z∈«configs»({θ})} Π_{v∈G} («factor»(T, Y, v) + t(v, θ) * «trackSpin»(Z, θ, v))"),
											"split each factor at Y ∪ Z",
											By(oldPairs, factorAt, real_sum.Congruence)),
										Leg(
											d.TermAs[Real](
												"Σ_{σ∈{σ:set(prod(I, I)) | σ ⊆ Ed}} Π_{v∈G} («factor»(T, Y, v) + t(v, θ) * «spin»(σ, v))"),
											"a set of pairs at θ is the set of its edges",
											By(real_sum.SubsetsSumCrossSingleton.At(
												Ed,
												θ,
												d.TermAs[Fun[Set[Prod[I, I]], Real]](
													"λσ:set(prod(I, I)). Π_{v∈G} («factor»(T, Y, v) + t(v, θ) * «spin»(σ, v))")))),
										FinalLeg(
											"one track keeps the product of the old factors and, over all of F, the product of its t",
											By(
												finiteEd,
												edges,
												connected,
												nonempty,
												sub,
												singleTrackExpansion.At(
													F,
													G,
													Ed,
													d.TermAs[Fun[I, Real]]("λv:I. «factor»(T, Y, v)"),
													d.TermAs[Fun[I, Real]]("λv:I. t(v, θ)"))))))
							}))
						finiteCube := b.Have(
							"there are finitely many sets of spins over T",
							"finite(«configs»(T))",
							By(finiteOld, finite_set.FinitePowerset))
						count := b.Have(
							"one for each choice of a spin at each pair",
							"card(«configs»(T)) = 2 ^ (card(Ed) * card(T))",
							By(
								finiteT,
								finiteEd,
								finiteOld,
								cardinality.CardPowerset.At(b.TermAs[Set[Prod[Prod[I, I], C]]]("set_cross(Ed, T)")),
								cardinality.CardProduct.At(Ed, T)))
						power := b.Have(
							"one more track is card(Ed) more spins",
							"&(2 ^ (card(Ed) * suc(card(T)))) = &(2 ^ card(Ed)) * &(2 ^ (card(Ed) * card(T)))",
							ByArith(
								nat_arith.PowAdd.At(
									b.TermAs[Nat]("2"), b.TermAs[Nat]("card(Ed)"), b.TermAs[Nat]("card(Ed) * card(T)")),
								real_construction.OfNumMul.At(
									b.TermAs[Nat]("2 ^ card(Ed)"), b.TermAs[Nat]("2 ^ (card(Ed) * card(T))"))))
						b.Show(
							"sum over the spins at θ first, then over the spins of the old tracks",
							CalcEq(
								Leg(
									b.TermAs[Real]("Σ_{Y∈«configs»(T)} Σ_{Z∈«configs»({θ})} Π_{v∈G} «factor»(insert(θ, T), Y ∪ Z, v)"),
									"a set of spins over insert(θ, T) is one over T together with one at θ",
									split.Rw(),
									By(finiteOld, finiteNew, apart, real_sum.SubsetsSumDisjointUnion)),
								Leg(
									b.TermAs[Real](
										"Σ_{Y∈«configs»(T)} &(2 ^ card(Ed)) * "+
											"(Π_{v∈G} «factor»(T, Y, v) + COND(G = F, Π_{v∈F} t(v, θ), &0))"),
									"average over the spins at θ",
									By(inner, real_sum.Congruence)),
								Leg(
									b.TermAs[Real](
										"&(2 ^ card(Ed)) * "+
											"(&(2 ^ (card(Ed) * card(T))) * (Π_{v∈G} c(v) + COND(G = F, Σ_{τ∈T} Π_{v∈F} t(v, τ), &0)) + "+
											"    &(2 ^ (card(Ed) * card(T))) * COND(G = F, Π_{v∈F} t(v, θ), &0))"),
									"the old factors sum by the induction hypothesis, and the "+
										"product of t at θ is counted once for each set of spins over T",
									Simp(Rev(real_sum.ScalarLeft), Rev(real_sum.Add), Rev(real_sum.Const), Fwd(finiteCube)),
									ih.Rw(),
									count.Rw()),
								FinalLeg(
									"the track θ adds its product of t to the sum over T and card(Ed) to the exponent",
									Simp(Fwd(real_sum.Clauses), Fwd(cardinality.CardClauses)),
									power.Rw(),
									ByArith())))
					}))))
	}),
})}
