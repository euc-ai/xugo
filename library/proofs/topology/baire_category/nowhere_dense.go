// nowhere_dense.go — what nowhere density and meagerness give: the union
// of two nowhere dense sets is nowhere dense, a closed set is nowhere dense
// when its interior is empty, the closure of a nowhere dense set is
// nowhere dense, the complement of a closed nowhere dense set is open and
// dense, a meager set lies in the union of an increasing sequence of
// closed nowhere dense sets, a continuous open map pulls a meager set back
// to a meager set, and the diagonal of a Hausdorff space without isolated
// points is closed and nowhere dense in its square.

package baire_category

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// NowhereDenseUnion — The union of two nowhere dense sets is nowhere dense:
// the closure of c ∪ d is the union of the two closures, so its interior u,
// with the closure of c taken away, is an open set inside the closure of d
// and is empty; u then lies inside the closure of c, and is empty as well.
var NowhereDenseUnion = nowhereDenseUnionThm{family.Add(registry.ProofEntry{
	Name: "NowhereDenseUnion",
	Key:  "prop_5fb5213aa4c0e308",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀c d:set(A).",
		Hypotheses: []string{
			"is_topology(T)",
			"nowhere_dense(T, c)",
			"nowhere_dense(T, d)",
		},
		Conclusion: "nowhere_dense(T, c ∪ d)",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		c, d *Expr[Set[A]],
		topology topological_space.IsTopologyFact[on.T],
		cNowhereDense, dNowhereDense Fact,
	) {
		cNDParts := a.Conjuncts(
			a.Unfolded(cNowhereDense, NowhereDenseDef),
			"c lies in the carrier",
			"its closure has empty interior",
		)
		cInSpace, cEmptyInterior := cNDParts[0], cNDParts[1]

		dNDParts := a.Conjuncts(
			a.Unfolded(dNowhereDense, NowhereDenseDef),
			"d lies in the carrier",
			"its closure has empty interior",
		)
		dInSpace, dEmptyInterior := dNDParts[0], dNDParts[1]

		unionInSpace := a.Have(
			"c ∪ d lies in the carrier",
			"c ∪ d ⊆ ⋃T",
			By(cInSpace, dInSpace, set_order.UnionSubset),
		)

		closureC := a.TermAs[Set[A]]("closure(T, c)")
		closureD := a.TermAs[Set[A]]("closure(T, d)")
		u, uDef := a.LetAs[Set[A]]("u", "interior(T, closure(T, c ∪ d))")
		uOpen := a.Have(
			"u is open in T",
			"u ∈ T",
			By(
				Normalized,
				uDef,
				topological_space.InteriorOpen.Read(topology).At(a.TermAs[Set[A]]("closure(T, c ∪ d)"))),
		)
		uInClosures := a.Have(
			"u lies in the closure of c ∪ d, which is the union of the two closures",
			"u ⊆ closure(T, c) ∪ closure(T, d)",
			By(
				Normalized,
				uDef,
				cInSpace,
				dInSpace,
				topological_space.ClosureUnion.Read(topology).At(c, d),
				topological_space.InteriorSubset.At(T, a.TermAs[Set[A]]("closure(T, c ∪ d)")),
			),
		)

		uMinusOpen := a.Have(
			"u ∖ closure(T, c) is open in T, the open u with the closed closure of c taken away",
			"u ∖ closure(T, c) ∈ T",
			By(
				cInSpace,
				topological_space.ClosureClosed.Read(topology).At(c),
				topological_space.DiffOpen.Read(topology).At(a.MemberOf[on.T](u, uOpen), closureC)),
		)
		uMinusInClosureD := a.Have(
			"u ∖ closure(T, c) lies inside the closure of d",
			"u ∖ closure(T, c) ⊆ closure(T, d)",
			BySets(uInClosures),
		)
		uMinusEmpty := a.Have(
			"the open set u ∖ closure(T, c) inside closure(T, d) lies in its empty interior",
			"u ∖ closure(T, c) ⊆ ∅",
			By(
				Normalized,
				uMinusOpen,
				uMinusInClosureD,
				dEmptyInterior,
				topological_space.InteriorMaximal.At(T, closureD, a.TermAs[Set[A]]("u ∖ closure(T, c)")),
			),
		)
		uInClosureC := a.Have(
			"hence u lies inside the closure of c",
			"u ⊆ closure(T, c)",
			BySets(uMinusEmpty),
		)

		uEmpty := a.Have(
			"u lies in the empty interior of closure(T, c), so u is empty",
			"u = ∅",
			By(
				Normalized,
				cEmptyInterior,
				uOpen,
				uInClosureC,
				topological_space.InteriorMaximal.At(T, closureC, u),
				set_order.SubsetEmpty.At(u),
			),
		)

		a.Show(
			"c ∪ d is nowhere dense in T",
			Unfold(NowhereDenseDef),
			By(Normalized, uDef, unionInSpace, uEmpty),
		)
	}),
	Reading: "Neither set is assumed closed. Iterated, a finite union of " +
		"nowhere dense sets is nowhere dense; a countable union need not be, " +
		"as the rationals in the reals show, and meagerness names that gap.",
})}

// ClosedNowhereDenseIffEmptyInterior — a closed set is nowhere dense
// exactly when its interior is empty: it lies in the space, and it is its
// own closure. No axiom of the topology enters, so T is spelled.
var ClosedNowhereDenseIffEmptyInterior = closedNowhereDenseIffEmptyInteriorThm{family.Add(registry.ProofEntry{
	Name: "ClosedNowhereDenseIffEmptyInterior",
	Key:  "prop_82f805935e157cd0",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀c:set(A).",
		Hypotheses: []string{
			"closed_in(T, c)",
		},
		Conclusion: "nowhere_dense(T, c) ⇔ interior(T, c) = ∅",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], c *Expr[Set[A]], closed Fact) {
			a.Show(
				"c lies in the space and is its own closure",
				By(
					closed,
					topological_space.ClosedInDef.At(T, c),
					topological_space.ClosureOfClosed.At(T, c),
					NowhereDenseDef.At(T, c)))
		}),
})}

// ClosureNowhereDense — the closure of a nowhere dense set is nowhere
// dense: it is closed, and its interior is empty because the set is
// nowhere dense, which for a closed set is nowhere density
// (ClosedNowhereDenseIffEmptyInterior).
var ClosureNowhereDense = closureNowhereDenseThm{family.Add(registry.ProofEntry{
	Name: "ClosureNowhereDense",
	Key:  "prop_e828eab1f5582523",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"nowhere_dense(s)",
		},
		Conclusion: "nowhere_dense(closure(s))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			s *Expr[Set[A]],
			nowhereDense Fact,
		) {
			given := a.Conjuncts(
				a.Unfolded(nowhereDense, NowhereDenseDef),
				"s lies in the space",
				"the interior of its closure is empty")
			a.Show(
				"the closure of s is closed, s lying in the space, and its interior is empty",
				By(
					given[0],
					given[1],
					topological_space.ClosureClosed.Read(topology).At(s),
					ClosedNowhereDenseIffEmptyInterior.At(T, a.TermAs[Set[A]]("closure(s)"))))
		}),
})}

// ClosedNowhereDenseComplement — the complement in the space of a closed
// nowhere dense set is open and dense. It is open because the set is
// closed. A closed nowhere dense set has empty interior
// (ClosedNowhereDenseIffEmptyInterior); and the interior of a set is the
// space with the closure of its complement taken away, so that closure is
// the whole space.
var ClosedNowhereDenseComplement = closedNowhereDenseComplementThm{family.Add(registry.ProofEntry{
	Name: "ClosedNowhereDenseComplement",
	Key:  "prop_14d85ef7d6261d0b",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀c:set(A).",
		Hypotheses: []string{
			"closed_in(c)",
			"nowhere_dense(c)",
		},
		Conclusion: "⋃T ∖ c ∈ T ∧ closure(⋃T ∖ c) = ⋃T",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			c *Expr[Set[A]],
			closed, nowhereDense Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(closed, topological_space.ClosedInDef),
				"c lies in the space",
				"its complement in the space is open")
			noInterior := a.Have(
				"c is closed and nowhere dense, so its interior is empty",
				"interior(c) = ∅",
				By(closed, nowhereDense, ClosedNowhereDenseIffEmptyInterior.At(T, c)))
			complement := a.TermAs[Set[A]]("⋃T ∖ c")
			a.Do(SplitConj(
				Case(
					"the complement of the closed c is open",
					By(parts[1])),
				Case(
					"its closure lies in the space and holds every point of it, the interior of c being empty",
					BySets(
						parts[0],
						noInterior,
						topological_space.InteriorClosureComplement.Read(topology).At(c),
						topological_space.ClosureSubsetSpace.Read(topology).At(complement))),
			))
		}),
})}

// MeagerClosedCover — a meager set lies in the union of an increasing
// sequence of closed nowhere dense sets. It lies in the union of nowhere
// dense sets a(n), and the closure of each is closed and nowhere dense
// (ClosureNowhereDense); G(n), the union of the closures of a(0), …,
// a(n), is then closed and nowhere dense (NowhereDenseUnion), holds a(n),
// and grows one step at a time, and so from m to every n ≥ m
// (order.IncreasingFromSteps).
var MeagerClosedCover = meagerClosedCoverThm{family.Add(registry.ProofEntry{
	Name: "MeagerClosedCover",
	Key:  "prop_c0dde6d4cefe638f",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"meager(s)",
		},
		Conclusion: "∃G:(num → set(A)). " +
			"    (∀n:num. closed_in(G(n)) ∧ nowhere_dense(G(n))) ∧ " +
			"    (∀m n:num. m ≤ n ⇒ G(m) ⊆ G(n)) ∧ " +
			"    s ⊆ ⋃image(G, 𝕌)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			s *Expr[Set[A]],
			meager Fact,
		) {
			_, covered := a.ObtainAs[Fun[Nat, Set[A]]](
				"s lies in the union of nowhere dense sets a(n)",
				"∃a:(num → set(A)). (∀n:num. nowhere_dense(a(n))) ∧ s ⊆ ⋃image(a, 𝕌)",
				By(meager, MeagerDef.At(T, s)))
			cover := a.Conjuncts(
				covered,
				"each a(n) is nowhere dense",
				"s lies in their union")
			closures := a.Have(
				"the closure of each a(n) is a closed nowhere dense set holding it",
				"∀n:num. closed_in(closure(a(n))) ∧ nowhere_dense(closure(a(n))) ∧ a(n) ⊆ closure(a(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					piece := b.TermAs[Set[A]]("a(n)")
					b.Do(SplitConjAll(
						Case(
							"a(n) is nowhere dense, so it lies in the space, and the closure of a set in the space is closed",
							By(
								cover[0].At(n),
								NowhereDenseDef.At(T, piece),
								topological_space.ClosureClosed.Read(topology).At(piece))),
						Case(
							"the closure of a nowhere dense set is nowhere dense",
							By(cover[0].At(n), ClosureNowhereDense.Read(topology).At(piece))),
						Case(
							"and it holds a(n)",
							By(topological_space.SubsetClosure.At(T, piece))),
					))
				}))
			G, recursion := a.ObtainAs[Fun[Nat, Set[A]]](
				"recursion: G(0) is the closure of a(0), and G(n + 1) adjoins the closure of a(n + 1) to G(n)",
				"∃G:(num → set(A)). G(0) = closure(a(0)) ∧ ∀n:num. G(n + 1) = G(n) ∪ closure(a(n + 1))",
				By(
					peano.Recursion.At(
						a.TermAs[Fun2[Set[A], Nat, Set[A]]]("λu:set(A). λn:num. u ∪ closure(a(n + 1))"),
						a.TermAs[Set[A]]("closure(a(0))")),
					nat_arith.Add1))
			steps := a.Conjuncts(
				recursion,
				"G(0) is the closure of a(0)",
				"each G(n + 1) adjoins the closure of a(n + 1) to G(n)")
			zero := a.TermAs[Nat]("0")
			closedNowhereDense := a.Have(
				"every G(n) is closed and nowhere dense",
				"∀n:num. closed_in(G(n)) ∧ nowhere_dense(G(n))",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"G(0) is the closure of a(0)",
						By(Normalized, steps[0], closures.At(zero)))
					b.Step(
						"G(n + 1) is the union of G(n) and the closure of a(n + 1), two closed nowhere dense sets",
						func(c *Argument, ih Fact) {
							n := c.TermAs[Nat]("n")
							last := c.TermAs[Set[A]]("G(n)")
							adjoined := c.TermAs[Set[A]]("closure(a(n + 1))")
							c.Do(Simp(Fwd(nat_arith.Add1)))
							c.Show(
								"two closed nowhere dense sets unite to one",
								By(
									steps[1].At(n),
									closures.At(c.TermAs[Nat]("n + 1")),
									ih,
									topological_space.UnionClosed.Read(topology).At(last, adjoined),
									NowhereDenseUnion.Read(topology).At(last, adjoined)))
						})
				}))
			increasing := a.Have(
				"each G(n + 1) holds G(n), adjoining a set to it, so G(m) lies in G(n) whenever m ≤ n",
				"∀m n:num. m ≤ n ⇒ G(m) ⊆ G(n)",
				BySets(steps[1], At(order.IncreasingFromSteps, G)))
			holds := a.Have(
				"each a(n) lies in G(n), which holds the closure of a(n)",
				"∀n:num. a(n) ⊆ G(n)",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"a(0) lies in its closure, which is G(0)",
						BySets(steps[0], closures.At(zero)))
					b.Step(
						"a(n + 1) lies in its closure, which G(n + 1) adjoins",
						func(c *Argument, _ Fact) {
							n := c.TermAs[Nat]("n")
							c.Show(
								"the closure of a(n + 1) lies in G(n + 1)",
								BySets(steps[1].At(n), nat_arith.Add1.At(n), closures.At(c.TermAs[Nat]("n + 1"))))
						})
				}))
			inUnion := a.Have(
				"so s, which lies in the union of the a(n), lies in the union of the G(n)",
				"s ⊆ ⋃image(G, 𝕌)",
				BySets(cover[1], holds))
			a.Take(G)
			a.Show(
				"G is a sequence of closed nowhere dense sets, growing with n, whose union holds s",
				By(closedNowhereDense, increasing, inUnion))
		}),
})}

// OpenMapMeagerPreimage — a continuous open map pulls a meager set back
// to a meager set. The meager s lies in the union of closed nowhere dense
// sets G(n) (MeagerClosedCover), so the preimage of s lies in the union of
// the preimages of the G(n). Each of them is closed, f being continuous,
// and its interior u is empty: u is open and f carries it into G(n), so
// the image of u, open because f is, lies in the interior of G(n), which
// is empty. Closed with empty interior, each preimage is nowhere dense
// (ClosedNowhereDenseIffEmptyInterior).
var OpenMapMeagerPreimage = openMapMeagerPreimageThm{family.Add(registry.ProofEntry{
	Name: "OpenMapMeagerPreimage",
	Key:  "prop_a77a9d28b97cee31",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀s:set(B).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"continuous_map(T, S, f)",
			"open_map(T, S, f)",
			"meager(S, s)",
		},
		Conclusion: "meager(T, preimage_on(⋃T, f, s))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			f *Arrow[A, B],
			s *Expr[Set[B]],
			topologyT topological_space.IsTopologyFact[on.T],
			topologyS topological_space.IsTopologyFact[on.S],
			fContinuous continuous.ContinuousMapFact[on.T, on.S],
			fOpen continuous.OpenMapFact[on.T, on.S],
			meager Fact,
		) {
			_, covered := a.ObtainAs[Fun[Nat, Set[B]]](
				"s lies in the union of closed nowhere dense sets G(n)",
				"∃G:(num → set(B)). (∀n:num. closed_in(S, G(n)) ∧ nowhere_dense(S, G(n))) ∧ s ⊆ ⋃image(G, 𝕌)",
				By(meager, MeagerClosedCover.Read(topologyS).At(s)))
			cover := a.Conjuncts(
				covered,
				"each G(n) is closed and nowhere dense",
				"s lies in their union")
			preimages := a.Have(
				"the preimage of each G(n) is closed with empty interior, and so nowhere dense",
				"∀n:num. nowhere_dense(T, preimage_on(⋃T, f, G(n)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					pullback := b.TermAs[Set[A]]("preimage_on(⋃T, f, G(n))")
					closed := b.Have(
						"f is continuous, so it pulls the closed G(n) back to a closed set",
						"closed_in(T, preimage_on(⋃T, f, G(n)))",
						By(fContinuous, cover[0].At(n), continuous.ClosedPreimage))
					noInterior := b.Have(
						"the preimage has no interior point",
						"interior(T, preimage_on(⋃T, f, G(n))) = ∅",
						Derive(func(c *Argument) {
							_, uDef := c.LetAs[Set[A]]("u", "interior(T, preimage_on(⋃T, f, G(n)))")
							coverSet := c.TermAs[Set[B]]("G(n)")
							imageOpen := c.Have(
								"u is open, an interior, so its image under the open map f is open",
								"image(f, u) ∈ S",
								By(
									uDef,
									fOpen,
									topological_space.InteriorOpen.Read(topologyT).At(pullback),
									continuous.OpenMap.At(T, S, f)))
							imageInside := c.Have(
								"u lies in the preimage of G(n), so f carries it into G(n)",
								"image(f, u) ⊆ G(n)",
								BySets(uDef, topological_space.InteriorSubset.At(T, pullback)))
							c.Show(
								"the open image of u lies in the interior of G(n), which is empty, so u has no point",
								BySets(
									imageOpen,
									imageInside,
									cover[0].At(n),
									ClosedNowhereDenseIffEmptyInterior.At(S, coverSet),
									topological_space.InteriorMaximal.At(S, coverSet, c.TermAs[Set[B]]("image(f, u)"))))
						}))
					b.Show(
						"closed with empty interior, the preimage is nowhere dense",
						By(closed, noInterior, ClosedNowhereDenseIffEmptyInterior.At(T, pullback)))
				}))
			a.Do(Unfold(MeagerDef))
			a.Take(a.TermAs[Fun[Nat, Set[A]]]("λn:num. preimage_on(⋃T, f, G(n))"))
			a.Show(
				"the preimages of the G(n) are nowhere dense and cover the preimage of s",
				BySets(preimages, cover[1]))
		}),
	Reading: "No surjectivity is needed: an open map carries a nonempty open " +
		"set to a nonempty open set. The preimage is taken on the carrier of T.",
})}

// DiagonalClosedNowhereDense — in a Hausdorff space without isolated
// points, the diagonal is closed and nowhere dense in the square. It is
// closed because the space is Hausdorff. An interior point p of it lies in
// an open rectangle u × v inside the diagonal, so fst(p) lies in the open
// v; fst(p) is not isolated, so v holds a point z other than it, and the
// pair (fst(p), z) lies in the rectangle yet off the diagonal.
var DiagonalClosedNowhereDense = diagonalClosedNowhereDenseThm{family.Add(registry.ProofEntry{
	Name: "DiagonalClosedNowhereDense",
	Key:  "prop_3f00ce8af0494420",
	Build: topological_space.IsTopology.Law(Statement{
		Hypotheses: []string{
			"hausdorff(T)",
			"∀x:A. x ∈ ⋃T ⇒ {x} ∉ T",
		},
		Conclusion: "closed_in(product_topology(T, T), «Δ») ∧ nowhere_dense(product_topology(T, T), «Δ»)",
		Abbrev: Abbrev{
			{Name: "Δ", Text: "set_diagonal(⋃T)"},
		},
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			hausdorff, noIsolated Fact,
		) {
			square := a.TermAs[Set[Set[Prod[A, A]]]]("product_topology(T, T)")
			space := a.TermAs[Set[A]]("⋃T")
			diag := a.TermAs[Set[Prod[A, A]]]("«Δ»")

			squareTopology := a.Have(
				"the square is a topology",
				"is_topology(product_topology(T, T))",
				By(product_topology.ProductTopology.At(T, T), topology))
			diagClosed := a.Have(
				"T is Hausdorff, so the diagonal is closed in the square",
				"closed_in(product_topology(T, T), «Δ»)",
				By(hausdorff, product_topology.HausdorffIffDiagonalClosed.At(T)))

			interior := a.TermAs[Set[Prod[A, A]]]("interior(product_topology(T, T), «Δ»)")
			noInterior := a.Have(
				"the diagonal has empty interior in the square",
				"interior(product_topology(T, T), «Δ») = ∅",
				Derive(func(b *Argument) {
					nonEmpty := b.SupposeNot()
					p, inInterior := b.ObtainAs[Prod[A, A]](
						"choose an interior point p of the diagonal",
						"∃p:prod(A, A). p ∈ interior(product_topology(T, T), «Δ»)",
						By(nonEmpty, set_basic.MemberNotEmpty.At(interior)))
					interiorOpen := b.Have(
						"the interior is open in the square",
						"interior(product_topology(T, T), «Δ») ∈ product_topology(T, T)",
						By(topological_space.InteriorOpen.Read(squareTopology).At(diag)))
					u, v, box := b.Obtain2As[Set[A], Set[A]](
						"an open rectangle u × v lies about p inside the interior",
						"∃u v:set(A). "+
							"    u ∈ T ∧ v ∈ T ∧ p ∈ set_cross(u, v) ∧ set_cross(u, v) ⊆ interior(product_topology(T, T), «Δ»)",
						By(product_topology.ProductOpenIff.At(T, T, interior), interiorOpen, inInterior))
					boxParts := b.Conjuncts(
						box,
						"u is open",
						"v is open",
						"p lies in u × v",
						"u × v lies in the interior")
					x := b.TermAs[A]("fst(p)")
					coordinate := b.Have(
						"p lies on the diagonal: its coordinates agree, so fst(p) is a point of ⋃T in u and in v",
						"fst(p) ∈ ⋃T ∧ fst(p) ∈ u ∧ fst(p) ∈ v",
						BySets(
							inInterior,
							boxParts[2],
							set_product.InDiagonalProjections.At(space, p),
							topological_space.InteriorSubset.At(square, diag),
							set_product.InCrossProjections.At(u, v, p)))
					notSingleton := b.Have(
						"v is open and fst(p) is not isolated, so v is not the singleton of fst(p)",
						"v ≠ {fst(p)}",
						By(Normalized, noIsolated.At(x), coordinate, boxParts[1]))
					z, other := b.ObtainAs[A](
						"so v holds a point z other than fst(p)",
						"∃z:A. z ∈ v ∧ z ≠ fst(p)",
						BySets(notSingleton, coordinate))
					b.Show(
						"(fst(p), z) lies in u × v, inside the diagonal, yet its coordinates differ",
						BySets(
							other,
							coordinate,
							boxParts[3],
							topological_space.InteriorSubset.At(square, diag),
							set_product.InCross.At(u, v, x, z),
							set_product.InDiagonal.At(space, x, z)))
				}))

			nowhereDense := a.Have(
				"closed with empty interior, the diagonal is nowhere dense",
				"nowhere_dense(product_topology(T, T), «Δ»)",
				By(diagClosed, noInterior, ClosedNowhereDenseIffEmptyInterior.At(square, diag)))
			a.Show(
				"the diagonal is closed and nowhere dense in the square",
				By(diagClosed, nowhereDense))
		}),
})}
