// continuous.go — continuous maps between spaces: composition and the
// identity; continuity read through the induced topology and through
// closed sets; pasting on two closed sets and on an open cover; what a
// continuous map preserves, compact and connected sets, a Lindelöf space
// carried onto the second space, and the closure of a set, carried into
// the closure of its image; constant maps, maps agreeing on the space, and
// continuity from and into a subspace; and continuity read on a base, into
// a generated topology and point by point.

package continuous

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure's axioms
// ---------------------------------------------------------------------------

// MapsInto — a continuous map carries the points of its space into the
// points of the target.
var MapsInto = mapsIntoThm{family.Add(registry.ProofEntry{
	Name: "MapsInto",
	Key:  "prop_cef0a39a091c2f65",
	Build: ContinuousMap.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "f(x) ∈ ⋃S",
	}),
})}

// PreimageOpen — the preimage in the space of an open set of the target
// is open.
var PreimageOpen = preimageOpenThm{family.Add(registry.ProofEntry{
	Name: "PreimageOpen",
	Key:  "prop_18cdf8fcfdac242b",
	Build: ContinuousMap.Axiom(Statement{
		Binders: "∀v:set(B).",
		Hypotheses: []string{
			"v ∈ S",
		},
		Conclusion: "preimage_on(⋃T, f, v) ∈ T",
	}),
})}

// ---------------------------------------------------------------------------
// Composition and the identity
// ---------------------------------------------------------------------------

// Compose — the composite of two continuous maps is continuous. Both
// clauses pass through the middle space: a point of ⋃T goes to ⋃S
// under f and on to ⋃R under g, and the preimage under g ∘ f of an
// open set of R is f's preimage of g's preimage, which g's continuity
// makes open in S and f's then makes open in T.
var Compose = composeThm{family.Add(registry.ProofEntry{
	Name: "Compose",
	Key:  "prop_37d0c730ec763f70",
	Build: ContinuousMap.Law(Statement{
		Binders: "∀R:set(set(C)). ∀g:(B → C).",
		Hypotheses: []string{
			"continuous_map(S, R, g)",
		},
		Conclusion: "continuous_map(T, R, g ∘ f)",
	},
		func(a *Argument, _ ContinuousMapFact[on.T, on.S], R *Expr[Set[Set[C]]], g *Arrow[B, C], _ Fact) {
			// Unfolding continuity deposits the two clauses of each map;
			// unfolding the composite (`∘` is the constant `o`) reads it
			// pointwise, so the goal's clauses speak of g(f(x)).
			a.Do(Unfold(ContinuousMap), Unfold(functions.ComposeApply))
			fMaps := a.Hyp("∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃S")
			gMaps := a.Hyp("∀y:B. y ∈ ⋃S ⇒ g(y) ∈ ⋃R")
			fPreimage := a.Hyp("∀v:set(B). v ∈ S ⇒ preimage_on(⋃T, f, v) ∈ T")
			gPreimage := a.Hyp("∀v:set(C). v ∈ R ⇒ preimage_on(⋃S, g, v) ∈ S")
			a.Do(SplitConj(
				Case(
					"a point of ⋃T goes to ⋃S under f and on to ⋃R under g",
					By(fMaps, gMaps)),
				Case(
					"the preimage under g ∘ f of an open set w of R is "+
						"open in T: it is f's preimage of g's preimage of w",
					Derive(func(b *Argument) {
						b.Fix("w")
						wOpen := b.Assume()
						inner := b.Have(
							"the preimage under g of w is open in S",
							"preimage_on(⋃S, g, w) ∈ S",
							By(gPreimage, wOpen))
						compositePreimage := b.Have(
							"the composite's preimage is f's preimage of that set, the "+
								"inner cut to ⋃S costing nothing as f carries ⋃T into ⋃S",
							"preimage_on(⋃T, λx:A. g(f(x)), w) = preimage_on(⋃T, f, preimage_on(⋃S, g, w))",
							BySets(fMaps))
						b.Show(
							"f's preimage of an open set of S is open in T",
							By(fPreimage, inner, compositePreimage))
					})),
			))
		}),
})}

// Identity — the identity map is continuous from a space to itself. The
// mapping clause is immediate, and the preimage of an open set v under
// the identity is v itself: the cut to ⋃T loses nothing, since a member
// of T lies in ⋃T.
var Identity = identityThm{family.Add(registry.ProofEntry{
	Name: "Identity",
	Key:  "prop_57d22609ea22329d",
	Build: family.Theorem("∀T:set(set(A)). continuous_map(T, T, identity_map)",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			// Unfolding continuity and the identity (`identity_map`, whose definition
			// is functions.IdentityApply) settles the mapping clause
			// outright — a point of ⋃T is a point of ⋃T — and leaves the
			// clause on preimages.
			a.Do(Unfold(ContinuousMap), Unfold(functions.IdentityApply))
			a.Fix("v")
			vOpen := a.Assume()
			within := a.Have(
				"an open set lies in the space, as every member of a family lies inside its union",
				"v ⊆ ⋃T",
				By(vOpen, set_order.MemberSubsetUnions))
			preimageIsV := a.Have(
				"so the preimage of v under the identity, cut to the space, is v",
				"preimage_on(⋃T, λx:A. x, v) = v",
				BySets(within))
			a.Show(
				"which is open in T",
				By(Normalized, preimageIsV, vOpen))
		}),
})}

// ---------------------------------------------------------------------------
// Equivalent readings of continuity
// ---------------------------------------------------------------------------

// ContinuousIffInduced — continuity means that the map carries the source
// carrier into the target carrier and every induced open set is source-open.
var ContinuousIffInduced = continuousIffInducedThm{family.Add(registry.ProofEntry{
	Name: "ContinuousIffInduced",
	Key:  "prop_b655df6338191d9b",
	Build: family.Theorem("∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). "+
		"    continuous_map(T, S, f) ⇔ image(f, ⋃T) ⊆ ⋃S ∧ induced_topology(⋃T, S, f) ⊆ T",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], f *Arrow[A, B]) {
			a.Do(
				Unfold(ContinuousMap),
				Unfold(topological_space.InducedTopologyDef),
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(set_image.ForallInImage)),
				Basic(),
			)
		}),
})}

// ClosedPreimage — continuity read through closed sets: a map is
// continuous iff it carries the space into the space and the preimage of
// every closed set is closed. Both directions turn on one identity, read
// at the set each needs: once f carries ⋃T into ⋃S, the part of ⋃T that
// f does not send into a set is the part it sends into that set's
// complement in ⋃S, so taking the complement in the space and taking the
// preimage commute. The open-set
// reading and the closed-set reading are then dual, a closed set being a
// set of the space whose complement there is open.
var ClosedPreimage = closedPreimageThm{family.Add(registry.ProofEntry{
	Name: "ClosedPreimage",
	Key:  "prop_7e0df4882a402aec",
	Build: family.Theorem(
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). "+
			"    continuous_map(T, S, f) ⇔ "+
			"    (∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃S) ∧ "+
			"    (∀c:set(B). closed_in(S, c) ⇒ closed_in(T, preimage_on(⋃T, f, c)))",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], f *Arrow[A, B]) {
			a.Iff()

			a.Forward(
				"the preimage of a closed set c is closed: its "+
					"complement in ⋃T is the preimage of the open set ⋃S ∖ c",
				func(b *Argument, continuous Fact) {
					// Continuity's two clauses: the first is the goal's mapping
					// clause; the clause on closed sets is the work.
					clauses := b.Conjuncts(
						b.Unfolded(continuous, ContinuousMap),
						"f carries the space into the space",
						"and the preimage of an open set is open")
					fMaps, openPullsBack := clauses[0], clauses[1]
					b.Do(SplitConj(
						Case(
							"f carries the space into the space, as continuity states",
							By(fMaps)),
						Case(
							"and the preimage of a closed set c is closed",
							Derive(func(b *Argument) {
								b.Fix("c")
								b.Assume() // closed_in(S, c), opened by the unfold below
								// A closed set lies in the space with an open complement
								// there; the goal asks the same of its preimage.
								b.Do(Unfold(topological_space.ClosedInDef))
								complementOpen := b.Hyp("⋃S ∖ c ∈ S")

								open := b.Have(
									"the preimage of the complement of c is open in T",
									"preimage_on(⋃T, f, ⋃S ∖ c) ∈ T",
									By(openPullsBack, complementOpen))
								commuted := b.Have(
									"and it is the complement in ⋃T of the preimage of c",
									"⋃T ∖ preimage_on(⋃T, f, c) = preimage_on(⋃T, f, ⋃S ∖ c)",
									BySets(fMaps))
								within := b.Have(
									"the preimage of c is cut to the space",
									"preimage_on(⋃T, f, c) ⊆ ⋃T",
									BySets())
								b.Show(
									"so the preimage of c lies in the space and its complement there is open",
									By(within, commuted, open))
							})),
					))
				})

			a.Backward(
				"the preimage of an open set v is open: it lies in the space, "+
					"and its complement there is the closed preimage of ⋃S ∖ v",
				func(b *Argument, closedReading Fact) {
					// Continuity's two clauses: the first is given; the clause on
					// open sets is the work.
					clauses := b.Conjuncts(
						closedReading,
						"f carries the space into the space",
						"and the preimage of a closed set is closed")
					fMaps, closedPullsBack := clauses[0], clauses[1]
					b.Do(Unfold(ContinuousMap), SplitConj(
						Case(
							"f carries the space into the space, as given",
							By(fMaps)),
						Case(
							"and the preimage of an open set v is open",
							Derive(func(b *Argument) {
								b.Fix("v")
								vOpen := b.Assume()

								complementClosed := b.Have(
									"the complement of v in the space is closed, v being open",
									"closed_in(S, ⋃S ∖ v)",
									By(topological_space.OpenClosedComplement, vOpen))
								commuted := b.Have(
									"the complement in ⋃T of the preimage of v is the preimage of that complement",
									"⋃T ∖ preimage_on(⋃T, f, v) = preimage_on(⋃T, f, ⋃S ∖ v)",
									BySets(fMaps))
								preimageComplementClosed := b.Have(
									"which is closed in T, as the preimage of a closed set",
									"closed_in(T, ⋃T ∖ preimage_on(⋃T, f, v))",
									commuted.Rw(),
									By(closedPullsBack, complementClosed))
								within := b.Have(
									"the preimage of v is cut to the space",
									"preimage_on(⋃T, f, v) ⊆ ⋃T",
									BySets())
								b.Show(
									"so the preimage of v is open: a set of the space whose complement there is closed",
									By(topological_space.OpenClosedComplement, within, preimageComplementClosed))
							})),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Pasting on closed sets
// ---------------------------------------------------------------------------

// ClosedPasting — the pasting lemma: a map continuous on each of two
// closed sets covering the space is continuous. Continuity is read
// through closed sets. A point of the space lies in c or in d, where f
// carries it into the second space. The preimage of a closed set e is its
// part in c united with its part in d; a part is closed in its subspace,
// f being continuous there, so closed in the space, the subspace being
// closed; and the union of two closed sets is closed.
var ClosedPasting = closedPastingThm{family.Add(registry.ProofEntry{
	Name: "ClosedPasting",
	Key:  "prop_e76d54716a874658",
	Build: family.Sections(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀c d:set(A). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"closed_in(T, c)",
			"closed_in(T, d)",
			"⋃T ⊆ c ∪ d",
			"continuous_map(subtopology(T, c), S, f)",
			"continuous_map(subtopology(T, d), S, f)",
		},
		Conclusion: "continuous_map(T, S, f)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A map continuous on a closed subspace pulls a closed set back to
			// a set closed in the whole space.
			closedPiece := ctx.Lemma(Statement{
				Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀c:set(A). ∀f:(A → B). ∀e:set(B).",
				Hypotheses: []string{
					"is_topology(T)",
					"closed_in(T, c)",
					"continuous_map(subtopology(T, c), S, f)",
					"closed_in(S, e)",
				},
				Conclusion: "closed_in(T, preimage_on(⋃T ∩ c, f, e))",
			},
				func(
					a *Argument,
					T *Expr[Set[Set[A]]],
					topology topological_space.IsTopologyFact[on.T],
					S *Expr[Set[Set[B]]],
					c *Expr[Set[A]],
					cClosed Fact,
					f *Arrow[A, B],
					onC Fact,
					e *Expr[Set[B]],
					eClosed Fact,
				) {
					inSubspace := a.Have(
						"the preimage of e in the subspace is closed there, f being continuous on it",
						"closed_in(subtopology(T, c), preimage_on(⋃subtopology(T, c), f, e))",
						By(ClosedPreimage, onC, eClosed))
					a.Show(
						"so it is closed in the space, the subspace being closed; its points are those of the space in c",
						Simp(Rev(topological_space.SubtopologySpace)),
						By(topological_space.ClosedInClosedSubtopology.Read(topology), cClosed, inSubspace))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					T *Expr[Set[Set[A]]],
					topology topological_space.IsTopologyFact[on.T],
					S *Expr[Set[Set[B]]],
					c, d *Expr[Set[A]],
					f *Arrow[A, B],
					cClosed, dClosed, covers, onC, onD Fact,
				) {
					mapsOnC := a.Have(
						"f carries the points of the space in c into the second space",
						"∀x:A. x ∈ ⋃T ∩ c ⇒ f(x) ∈ ⋃S",
						By(MapsInto.Read(onC), topological_space.SubtopologySpace))
					mapsOnD := a.Have(
						"and the points of the space in d",
						"∀x:A. x ∈ ⋃T ∩ d ⇒ f(x) ∈ ⋃S",
						By(MapsInto.Read(onD), topological_space.SubtopologySpace))
					maps := a.Have(
						"so f carries the space into the second space, every point lying in c or in d",
						"∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃S",
						BySets(mapsOnC, mapsOnD, covers))
					closedPullsBack := a.Have(
						"and the preimage of a closed set is closed",
						"∀e:set(B). closed_in(S, e) ⇒ closed_in(T, preimage_on(⋃T, f, e))",
						Derive(func(b *Argument) {
							e := b.FixAs[Set[B]]("e")
							eClosed := b.Assume()
							pieceC := b.Have(
								"its part in c is closed in the space",
								"closed_in(T, preimage_on(⋃T ∩ c, f, e))",
								By(At(closedPiece, T, S, c, f, e), topology, cClosed, onC, eClosed))
							pieceD := b.Have(
								"and so is its part in d",
								"closed_in(T, preimage_on(⋃T ∩ d, f, e))",
								By(At(closedPiece, T, S, d, f, e), topology, dClosed, onD, eClosed))
							parts := b.Have(
								"a point of the space lies in c or in d, so the preimage is the union of the two parts",
								"preimage_on(⋃T, f, e) = preimage_on(⋃T ∩ c, f, e) ∪ preimage_on(⋃T ∩ d, f, e)",
								BySets(covers))
							b.Show(
								"which is closed, as a union of two closed sets",
								parts.Rw(),
								By(topological_space.UnionClosed.Read(topology), pieceC, pieceD))
						}))
					a.Show(
						"so f is continuous, read through closed sets",
						By(ClosedPreimage, maps, closedPullsBack))
				})
		}),
})}

// ---------------------------------------------------------------------------
// What continuous maps preserve
// ---------------------------------------------------------------------------

// ImageCompact — the continuous image of a compact set is compact.
//
// Pull an open cover c of the image back along f. The preimages of its
// sets are open in T, f being continuous, and they cover k, c covering
// the image; so compactness of k picks finitely many of them. Each of
// those is the preimage of some set of c, and the finitely many sets so
// named cover the image: a point f(x) with x in k lies in the set whose
// preimage holds x. No topology axiom enters — the two definitions,
// finiteness carried along an image, and membership are the whole
// proof.
var ImageCompact = imageCompactThm{family.Add(registry.ProofEntry{
	Name: "ImageCompact",
	Key:  "prop_37b99692fa71635",
	Build: ContinuousMap.Law(Statement{
		Binders: "∀k:set(A).",
		Hypotheses: []string{
			"compact_in(k)",
		},
		Conclusion: "compact_in(S, image(f, k))",
		Abbrev: Abbrev{
			{Name: "preimageOf", Text: "λv:set(B). preimage_on(⋃T, f, v)"},
		},
	},
		func(a *Argument, _ ContinuousMapFact[on.T, on.S], k *Expr[Set[A]], _ Fact) {
			// The hypothesis and the goal read through the two definitions:
			// f carries the space T into the space S and pulls open sets
			// back to open sets; k lies in the space T and every open
			// cover of it has a finite subcover.
			a.Do(Unfold(compact.CompactInDef), Unfold(ContinuousMap))
			carries := a.Hyp("∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃S")
			preimageOpen := a.Hyp("∀v:set(B). v ∈ S ⇒ preimage_on(⋃T, f, v) ∈ T")
			inSpace := a.Hyp("k ⊆ ⋃T")
			subcover := a.Hyp("∀c:set(set(A)). c ⊆ T ∧ k ⊆ ⋃c ⇒ ∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ k ⊆ ⋃d")

			a.Do(SplitConj(
				Case(
					"the image lies in the space S, f carrying the points of T there",
					BySets(carries, inSpace)),
				Case(
					"an open cover of the image has a finite subcover",
					Derive(func(b *Argument) {
						c := b.FixAs[Set[Set[B]]]()
						cover := b.Conjuncts(
							b.Assume(),
							"the members of c are open",
							"c covers the image")
						open, covers := cover[0], cover[1]

						// The cover pulled back: the preimages of the sets of c.
						preimage := b.TermAs[Fun[Set[B], Set[A]]]("«preimageOf»")
						preimages := b.TermAs[Set[Set[A]]]("image(«preimageOf», c)")

						preimagesOpen := b.Have(
							"each set of the cover pulls back to an open set, the cover lying in S",
							"image(«preimageOf», c) ⊆ T",
							Simp(Fwd(set_image.ImageSubsetIff)),
							BySets(preimageOpen, open))
						preimagesCoverK := b.Have(
							"and they cover k: a point of k lies in the space, and its value in some set of c",
							"k ⊆ ⋃image(«preimageOf», c)",
							BySets(inSpace, covers))

						d, finiteSubcover := b.ObtainAs[Set[Set[A]]](
							"compactness of k at the preimage family: finitely many preimages already cover k",
							"∃d:set(set(A)). d ⊆ image(«preimageOf», c) ∧ finite(d) ∧ k ⊆ ⋃d",
							By(subcover.At(preimages), preimagesOpen, preimagesCoverK))
						e, drawnFrom := b.Obtain(
							"a finite subfamily of the preimages is the family of preimages of finitely many sets of c",
							"∃e:set(set(B)). finite(e) ∧ d = image(«preimageOf», e) ∧ e ⊆ c",
							By(finiteSubcover, finite_set.FiniteSubsetImage.At(preimage, c, d)))
						coveredByE := b.Have(
							"the preimages of those sets are the finite subcover, so they cover k",
							"k ⊆ ⋃image(«preimageOf», e)",
							By(Normalized, drawnFrom, finiteSubcover))

						b.Take(e)
						b.Do(SplitConj(
							Case(
								"e is a finite subfamily of the cover",
								By(drawnFrom)),
							Case(
								"and covers the image: f(x) lies in the set of e whose preimage holds x",
								BySets(coveredByE)),
						))
					})),
			))
		}),
})}

// ImageConnected — the continuous image of a connected set is
// connected. The image lies in the space ⋃S because k lies in ⋃T and f
// carries one into the other. Two open sets u, v of S that cover the
// image and each meet it pull back to two open sets of T, the
// preimages of u and v cut to ⋃T, which cover k and each meet k; k
// being connected, they share a point of k, and f sends it to a point
// of the image in both u and v.
var ImageConnected = imageConnectedThm{family.Add(registry.ProofEntry{
	Name: "ImageConnected",
	Key:  "prop_1b03a305ebc56849",
	Build: ContinuousMap.Law(Statement{
		Binders: "∀k:set(A).",
		Hypotheses: []string{
			"connected_in(k)",
		},
		Conclusion: "connected_in(S, image(f, k))",
	},
		func(a *Argument, _ ContinuousMapFact[on.T, on.S], k *Expr[Set[A]], _ Fact) {
			// Unfolding both definitions deposits the two clauses of
			// continuity and the two clauses of k's connectedness as
			// hypotheses, and states the goal as the two clauses for
			// the image.
			a.Do(Unfold(ContinuousMap), Unfold(connected.ConnectedInDef))
			fMaps := a.Hyp("∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃S")
			fPreimage := a.Hyp("∀v:set(B). v ∈ S ⇒ preimage_on(⋃T, f, v) ∈ T")
			kInSpace := a.Hyp("k ⊆ ⋃T")
			kConnected := a.Hyp(Statement{
				Binders: "∀u v:set(A).",
				Hypotheses: []string{
					"u ∈ T",
					"v ∈ T",
					"k ⊆ u ∪ v",
					"¬(k ∩ u = ∅)",
					"¬(k ∩ v = ∅)",
				},
				Conclusion: "¬(k ∩ u ∩ v = ∅)",
			})
			a.Do(SplitConjAll(
				Case(
					"the image lies in the space ⋃S: k lies in ⋃T, which f carries into ⋃S",
					BySets(fMaps, kInSpace)),
				Case(
					"two open sets of S that cover the image and each meet it share a point of it",
					Derive(func(b *Argument) {
						b.Fix()
						b.Fix()
						// The five antecedents of the goal's clause, one
						// fact: u and v are open in S, they cover the
						// image, and each meets it.
						separates := b.Assume()

						// The two open sets pulled back along f, cut to
						// the space: k's connectedness is applied at these.
						U := b.Let("U", b.Term("preimage_on(⋃T, f, u)"))
						V := b.Let("V", b.Term("preimage_on(⋃T, f, v)"))

						preimageUOpen := b.Have(
							"the preimage of u is open in T",
							"U ∈ T",
							By(Normalized, U, fPreimage, separates))
						preimageVOpen := b.Have(
							"the preimage of v is open in T",
							"V ∈ T",
							By(Normalized, V, fPreimage, separates))
						kCovered := b.Have(
							"the preimages cover k: a point of k lies in ⋃T and its image in u or in v",
							"k ⊆ U ∪ V",
							BySets(U, V, kInSpace, separates))
						kMeetsU := b.Have(
							"k meets the preimage of u: a point of the image in u is f(x) for some x ∈ k",
							"¬(k ∩ U = ∅)",
							BySets(U, kInSpace, separates))
						kMeetsV := b.Have(
							"and k meets the preimage of v likewise",
							"¬(k ∩ V = ∅)",
							BySets(V, kInSpace, separates))
						sharesPoint := b.Have(
							"k is connected, so the two preimages share a point of k",
							"¬(k ∩ U ∩ V = ∅)",
							By(kConnected, preimageUOpen, preimageVOpen, kCovered, kMeetsU, kMeetsV))
						b.Show(
							"f sends that point to a point of the image in both u and v",
							BySets(U, V, sharesPoint))
					})),
			))
		}),
})}

// ImageLindelof — a continuous image of a Lindelöf space is Lindelöf.
//
// ImageCompact's argument with countable for finite. Pull an open cover c
// of the second space back along f: the preimages of its sets are open, f
// being continuous, and they cover the first space, f carrying each point
// into a set of c. Countably many of them, d, already do. f carries each
// member of d into the set of c it is the preimage of, and one such set is
// chosen for every member of d; the chosen sets are countably many, the
// image of d under the choice, and they cover the image of the first space,
// which is the second.
var ImageLindelof = imageLindelofThm{family.Add(registry.ProofEntry{
	Name: "ImageLindelof",
	Key:  "prop_94999366d523c466",
	Build: ContinuousMap.Law(Statement{
		Hypotheses: []string{
			"lindelof_space(T)",
			"image(f, ⋃T) = ⋃S",
		},
		Conclusion: "lindelof_space(S)",
		Abbrev: Abbrev{
			{Name: "preimageOf", Text: "λv:set(B). preimage_on(⋃T, f, v)"},
		},
	},
		func(a *Argument, continuous ContinuousMapFact[on.T, on.S], lindelof, onto Fact) {
			subcover := a.Unfolded(lindelof, countability.LindelofSpaceDef)
			a.Do(Unfold(countability.LindelofSpaceDef))
			a.FixAs[Set[Set[B]]]("c")
			cover := a.Conjuncts(
				a.Assume(),
				"the members of c are open",
				"c covers the space")
			open, covers := cover[0], cover[1]

			// The cover pulled back: the preimages of the sets of c.
			preimages := a.TermAs[Set[Set[A]]]("image(«preimageOf», c)")
			preimagesOpen := a.Have(
				"each set of the cover pulls back to an open set, the cover lying in S",
				"image(«preimageOf», c) ⊆ T",
				Simp(Fwd(set_image.ImageSubsetIff)),
				BySets(PreimageOpen.Read(continuous), open))
			preimagesCover := a.Have(
				"and the preimages cover the space: f carries a point x into ⋃S, so into a set of c",
				"⋃T ⊆ ⋃image(«preimageOf», c)",
				BySets(MapsInto.Read(continuous), covers))
			_, countableSubcover := a.Obtain(
				"T being Lindelöf, countably many of the preimages already cover the space",
				"∃d:set(set(A)). d ⊆ image(«preimageOf», c) ∧ countable(d) ∧ ⋃T ⊆ ⋃d",
				By(subcover.At(preimages), preimagesOpen, preimagesCover))
			parts := a.Conjuncts(
				countableSubcover,
				"the members of d are preimages of sets of c",
				"d is countable",
				"d covers the space")
			drawn, countableD, coversT := parts[0], parts[1], parts[2]

			carried := a.Have(
				"f carries each member of d into a set of c, the one it is the preimage of",
				"∀w:set(A). w ∈ d ⇒ ∃v:set(B). v ∈ c ∧ image(f, w) ⊆ v",
				BySets(drawn))
			_, chosen := a.Obtain(
				"choose such a set q(w) of c for every member w of d",
				"∃q:(set(A) → set(B)). ∀w:set(A). w ∈ d ⇒ q(w) ∈ c ∧ image(f, w) ⊆ q(w)",
				By(carried))

			a.Take(a.TermAs[Set[Set[B]]]("image(q, d)"))
			a.Do(SplitConjAll(
				Case(
					"the chosen sets are sets of c",
					BySets(chosen)),
				Case(
					"they are countably many, the image of the countable d under q",
					By(countableD, cardinal.CountableImage)),
				Case(
					"they cover ⋃S, the image of the space: f(x) lies in q(w) for a member w of d holding x",
					onto.RwRev(),
					BySets(chosen, coversT)),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Constants, restrictions and subspaces
// ---------------------------------------------------------------------------

// Constant — a constant map to a point of the second space is
// continuous: every point of the first space goes to that point, and the
// preimage of an open set is the whole first space or nothing, as the set
// holds the point or not. Both are open, which is where the first space
// has to be a topology.
var Constant = constantThm{family.Add(registry.ProofEntry{
	Name: "Constant",
	Key:  "prop_5205a70a460ac30f",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀c:B.",
		Hypotheses: []string{
			"is_topology(T)",
			"c ∈ ⋃S",
		},
		Conclusion: "continuous_map(T, S, λx:A. c)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			S *Expr[Set[Set[B]]],
			c *Expr[B],
			inSpace Fact,
		) {
			a.Do(Unfold(ContinuousMap), SplitConj(
				Case(
					"every point of the space goes to c, a point of the second space",
					By(inSpace)),
				Case(
					"the preimage of an open set v is open, as c lies in v or not",
					Derive(func(b *Argument) {
						b.FixAs[Set[B]]("v")
						b.Assume() // v ∈ S: the argument asks nothing of v
						b.Cases(b.Term("c ∈ v"))
						b.When(
							"where c lies in v, the preimage is the whole space",
							func(b *Argument, cInV Fact) {
								preimageIsSpace := b.Have(
									"every point of the space goes into v",
									"preimage_on(⋃T, λx:A. c, v) = ⋃T",
									BySets(cInV))
								b.Show(
									"and the space is open",
									By(Normalized, preimageIsSpace, topological_space.SpaceOpen.Read(topology)))
							})
						b.Otherwise(
							"where c lies outside v, the preimage is empty",
							func(b *Argument, cOutsideV Fact) {
								preimageIsEmpty := b.Have(
									"no point goes into v",
									"preimage_on(⋃T, λx:A. c, v) = ∅",
									BySets(cOutsideV))
								b.Show(
									"and the empty set is open",
									By(Normalized, preimageIsEmpty, topological_space.EmptyOpen.Read(topology)))
							})
					})),
			))
		}),
})}

// Eq — a map agreeing on the space with a continuous map is continuous:
// its values remain in the target space, and its restricted preimages
// are the same open sets.
var Eq = eqThm{family.Add(registry.ProofEntry{
	Name: "Eq",
	Key:  "prop_b25f8663a52f5dae",
	Build: ContinuousMap.Law(Statement{
		Binders: "∀g:(A → B).",
		Hypotheses: []string{
			"∀x:A. x ∈ ⋃T ⇒ f(x) = g(x)",
		},
		Conclusion: "continuous_map(T, S, g)",
	},
		func(a *Argument, continuous ContinuousMapFact[on.T, on.S], g *Arrow[A, B], agree Fact) {
			a.Do(Simp(Fwd(ContinuousMap)), SplitConj(
				Case(
					"g carries every point of the source space into the target space",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						xIn := b.Assume()
						b.Show(
							"g lies in the target space because it has the value f at x",
							By(xIn, agree.At(x), MapsInto.Read(continuous).At(x)))
					})),
				Case(
					"the preimage under g of an open set is the open preimage under f",
					Derive(func(b *Argument) {
						v := b.FixAs[Set[B]]("v")
						vOpen := b.Assume()
						preimages := b.Have(
							"agreement on the source space gives equal restricted preimages",
							"preimage_on(⋃T, f, v) = preimage_on(⋃T, g, v)",
							BySets(agree))
						b.Show(
							"the common preimage is open",
							By(preimages, PreimageOpen.Read(continuous).At(b.MemberOf[on.S](v, vOpen))))
					})),
			))
		}),
})}

// FromSubtopology — a continuous map is continuous on every subspace.
// The subspace's points are the points of the space in s, which f
// carries into the second space; and the preimage in the subspace of an
// open set is the trace on s of its preimage in the space, open in the
// subspace as the trace of an open set. No axiom of either space enters.
var FromSubtopology = fromSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "FromSubtopology",
	Key:  "prop_f1f2de20b9f3f8cf",
	Build: ContinuousMap.Law("∀s:set(A). continuous_map(subtopology(T, s), S, f)",
		func(a *Argument, continuous ContinuousMapFact[on.T, on.S], s *Expr[Set[A]]) {
			a.Show(
				"f is continuous on the subspace",
				ContinuousMap.Intro(
					Case(
						"a point of the subspace is a point of the space in s, which f carries into the second space",
						BySets(MapsInto.Read(continuous), topological_space.SubtopologySpace)),
					Case(
						"the preimage in the subspace of an open set v is open "+
							"there, the subspace's points being those of the space in s",
						Simp(Fwd(topological_space.SubtopologySpace)),
						Derive(func(b *Argument) {
							b.Fix("v")
							vOpen := b.Assume()
							trace := b.Have(
								"it is the trace on s of the preimage of v in the space",
								"preimage_on(⋃T ∩ s, f, v) = preimage_on(⋃T, f, v) ∩ s",
								BySets())
							b.Show(
								"the trace on s of an open set of the space, the preimage of v in the space being open",
								trace.Rw(),
								By(topological_space.TraceOpen, PreimageOpen.Read(continuous), vOpen))
						}))))
		}),
})}

// IntoSubtopology — a map is continuous into a subspace exactly when it
// is continuous into the space and takes its values in the subset. The
// subspace's points are the points of the second space in t, and its
// open sets are the traces u ∩ t of the open sets of the second space;
// where the values of f lie in t, the preimage of a trace u ∩ t is the
// preimage of u. So the open sets pulled back are the same in both
// readings. No axiom of either space enters.
var IntoSubtopology = intoSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "IntoSubtopology",
	Key:  "prop_592d37e0a9fc6604",
	Build: family.Theorem("∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀t:set(B). "+
		"    continuous_map(T, subtopology(S, t), f) ⇔ continuous_map(T, S, f) ∧ (∀x:A. x ∈ ⋃T ⇒ f(x) ∈ t)",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], f *Arrow[A, B], t *Expr[Set[B]]) {
			a.Iff()

			a.Forward(
				"continuity into the subspace is continuity into the space, with values in t",
				func(b *Argument, intoSubspace Fact) {
					values := b.Have(
						"f carries the space into the subspace's points, the points of S in t",
						"∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃S ∩ t",
						By(MapsInto.Read(intoSubspace), topological_space.SubtopologySpace))
					b.Do(SplitConj(
						Case(
							"f is continuous into S",
							ContinuousMap.Intro(
								Case(
									"f carries the space into ⋃S",
									BySets(values)),
								Case(
									"the preimage of an open set v of S is the preimage of the open trace v ∩ t",
									Derive(func(c *Argument) {
										c.Fix("v")
										vOpen := c.Assume()
										trace := c.Have(
											"the values of f lying in t, v ∩ t and v have one preimage",
											"preimage_on(⋃T, f, v ∩ t) = preimage_on(⋃T, f, v)",
											BySets(values))
										c.Show(
											"which is open, v ∩ t being open in the subspace",
											trace.RwRev(),
											By(PreimageOpen.Read(intoSubspace), topological_space.TraceOpen, vOpen))
									})))),
						Case(
							"and the values of f lie in t",
							BySets(values)),
					))
				})

			a.Backward(
				"continuity into the space with values in t is continuity into the subspace",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"f is continuous into S",
						"and its values lie in t")
					continuous, valuesInT := parts[0], parts[1]
					b.Show(
						"f is continuous into the subspace",
						ContinuousMap.Intro(
							Case(
								"f carries the space into the points of S in t, the subspace's points",
								BySets(MapsInto.Read(continuous), valuesInT, topological_space.SubtopologySpace)),
							Case(
								"the preimage of an open set v of the subspace is open",
								Derive(func(c *Argument) {
									c.Fix("v")
									vOpen := c.Assume()
									_, trace := c.Obtain(
										"v is the trace on t of an open set u of S",
										"∃u:set(B). v = u ∩ t ∧ u ∈ S",
										By(vOpen, topological_space.OpenInSubtopology))
									same := c.Have(
										"the values of f lying in t, v and u have one preimage",
										"preimage_on(⋃T, f, v) = preimage_on(⋃T, f, u)",
										BySets(valuesInT, trace))
									c.Show(
										"the preimage of the open set u, which is open",
										same.Rw(),
										By(PreimageOpen.Read(continuous), trace))
								})),
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Continuity read on a base, at a point, and on an open cover
// ---------------------------------------------------------------------------

// ContinuousOnBase — continuity is checked on a base of the second
// space. Forward, a member of the base is open, so its preimage is.
// Backward, the preimage of an open set v is open by the pointwise
// criterion in the first space: a point x of it has f(x) in v, so in a
// member w of the base inside v, and the preimage of w is an open set
// about x inside the preimage of v. The first space's axioms enter
// through that criterion.
var ContinuousOnBase = continuousOnBaseThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnBase",
	Key:  "prop_6a8875f6f11557ba",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S b:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"topology_base(S, b)",
		},
		Conclusion: "continuous_map(T, S, f) ⇔ " +
			"(∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃S) ∧ (∀v:set(B). v ∈ b ⇒ preimage_on(⋃T, f, v) ∈ T)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			S, b *Expr[Set[Set[B]]],
			base Fact,
			f *Arrow[A, B],
		) {
			// A base is a family of open sets among which every point of an
			// open set finds one about it inside the open set.
			baseParts := a.Conjuncts(
				a.Unfolded(base, topological_space.TopologyBaseDef),
				"the members of the base are open",
				"every point of an open set lies in a member of the base inside it")
			baseOpen, refines := baseParts[0], baseParts[1]
			a.Iff()

			a.Forward(
				"a continuous map pulls the members of the base back to open sets, as they are open",
				func(c *Argument, continuous Fact) {
					c.Do(SplitConj(
						Case(
							"f carries the space into the second space",
							By(MapsInto.Read(continuous))),
						Case(
							"the preimage of a member of the base is open, the member being open",
							BySets(PreimageOpen.Read(continuous), baseOpen)),
					))
				})

			a.Backward(
				"a map that pulls the members of the base back to open sets pulls every open set back to one",
				func(c *Argument, given Fact) {
					parts := c.Conjuncts(
						given,
						"f carries the space into the second space",
						"and pulls the members of the base back to open sets")
					maps, membersPullBack := parts[0], parts[1]
					c.Show(
						"f is continuous",
						ContinuousMap.Intro(
							Case(
								"f carries the space into the second space, as given",
								By(maps)),
							Case(
								"the preimage of an open set v is open: each of its points has an open neighbourhood inside it",
								Derive(func(d *Argument) {
									d.Fix("v")
									vOpen := d.Assume()
									neighbourhoods := d.Have(
										"each point x of the preimage of v lies in an open set inside it",
										"∀x:A. x ∈ preimage_on(⋃T, f, v) ⇒ ∃u:set(A). u ∈ T ∧ u ⊆ preimage_on(⋃T, f, v) ∧ x ∈ u",
										Derive(func(e *Argument) {
											e.Fix("x")
											xIn := e.Assume()
											_, member := e.Obtain(
												"f(x) lies in the open set v, so in a member w of the base inside v",
												"∃w:set(B). w ∈ b ∧ f(x) ∈ w ∧ w ⊆ v",
												BySets(refines, xIn, vOpen))
											e.Take(e.Term("preimage_on(⋃T, f, w)"))
											e.Show(
												"the preimage of w is open, holds x and lies in the preimage of v",
												BySets(membersPullBack, xIn, member))
										}))
									d.Show(
										"so the preimage of v is open, by the pointwise criterion",
										By(neighbourhoods, topological_space.OpenPointwise.Read(topology)))
								})),
						))
				})
		}),
})}

// ContinuousIntoGenerated — continuity into a generated topology is
// checked on the generating family. Forward, the generated topology
// holds b and has the points of b. Backward, the subsets of ⋃b whose
// preimage is open form the topology coinduced on ⋃b by f, a topology as
// the first space is one; it holds b, so it holds the topology b
// generates, and every open set of that has an open preimage.
var ContinuousIntoGenerated = continuousIntoGeneratedThm{family.Add(registry.ProofEntry{
	Name: "ContinuousIntoGenerated",
	Key:  "prop_5e6a5d3755860806",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀b:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
		},
		Conclusion: "continuous_map(T, topology_generated(b), f) ⇔ " +
			"(∀x:A. x ∈ ⋃T ⇒ f(x) ∈ ⋃b) ∧ (∀v:set(B). v ∈ b ⇒ preimage_on(⋃T, f, v) ∈ T)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			b *Expr[Set[Set[B]]],
			f *Arrow[A, B],
		) {
			a.Iff()

			a.Forward(
				"the generated topology has the points of b and holds b",
				func(c *Argument, continuous Fact) {
					c.Do(SplitConj(
						Case(
							"f carries the space into ⋃b, the points of the generated topology",
							By(MapsInto.Read(continuous), topological_space.GeneratedSpace)),
						Case(
							"the preimage of a member of b is open, b lying in the generated topology",
							BySets(PreimageOpen.Read(continuous), topological_space.GeneratedContains)),
					))
				})

			a.Backward(
				"the topology coinduced on ⋃b holds b, so it holds the generated topology",
				func(c *Argument, given Fact) {
					parts := c.Conjuncts(
						given,
						"f carries the space into ⋃b",
						"and pulls the members of b back to open sets")
					maps, membersPullBack := parts[0], parts[1]
					bInside := c.Have(
						"b lies in the topology coinduced on ⋃b: a member lies inside ⋃b and has an open preimage",
						"b ⊆ coinduced_topology(⋃b, T, f)",
						Derive(func(d *Argument) {
							d.Do(Unfold(set_basic.SubsetDef))
							d.Fix("v")
							vIn := d.Assume()
							d.Show(
								"v lies inside ⋃b, and its preimage is open",
								Simp(Fwd(topological_space.CoinducedTopologyDef)),
								By(membersPullBack, vIn, set_order.MemberSubsetUnions))
						}))
					generatedInside := c.Have(
						"so the generated topology lies in it, the coinduced topology being a topology",
						"topology_generated(b) ⊆ coinduced_topology(⋃b, T, f)",
						By(topological_space.GeneratedMinimal, topological_space.CoinducedTopology, topology, bInside))
					c.Show(
						"f is continuous into the generated topology",
						ContinuousMap.Intro(
							Case(
								"f carries the space into ⋃b, the points of the generated topology",
								By(maps, topological_space.GeneratedSpace)),
							Case(
								"the preimage of an open set v of the generated topology is open, v lying in the coinduced one",
								Derive(func(d *Argument) {
									d.Fix("v")
									vOpen := d.Assume()
									d.Show(
										"a member of the coinduced topology has an open preimage",
										BySets(vOpen, generatedInside, topological_space.CoinducedTopologyDef))
								})),
						))
				})
		}),
})}

// ContinuousIffAt — a map is continuous exactly when it is continuous
// at each point of the space. Forward, the preimage of an open set about
// f(x) is an open set about x that f carries into it. Backward, the
// preimage of an open set v is open by the pointwise criterion in the
// first space: f, continuous at a point x of it, carries an open set about
// x into v, and that set lies in the space, so inside the preimage. The
// first space's axioms enter through that criterion.
var ContinuousIffAt = continuousIffAtThm{family.Add(registry.ProofEntry{
	Name: "ContinuousIffAt",
	Key:  "prop_4bd24a3f0fba1fc4",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
		},
		Conclusion: "continuous_map(T, S, f) ⇔ ∀x:A. x ∈ ⋃T ⇒ continuous_map_at(T, S, f, x)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			S *Expr[Set[Set[B]]],
			f *Arrow[A, B],
		) {
			a.Iff()

			a.Forward(
				"a continuous map is continuous at each point of the space",
				func(b *Argument, continuous Fact) {
					b.FixAs[A]("x")
					xIn := b.Assume()
					b.Show(
						"f is continuous at x",
						Simp(Fwd(ContinuousMapAtDef)),
						SplitConjAll(
							Case(
								"x is a point of the space",
								By(xIn)),
							Case(
								"which f carries into the second space",
								By(xIn, MapsInto.Read(continuous))),
							Case(
								"and an open set v about f(x) receives the preimage of v, an open set about x",
								Derive(func(c *Argument) {
									v := c.FixAs[Set[B]]("v")
									vAbout := c.Assume()
									c.Take(c.TermAs[Set[A]]("preimage_on(⋃T, f, v)"))
									c.Show(
										"the preimage of v is open, holds x, and is carried into v",
										BySets(At(PreimageOpen.Read(continuous), v), xIn, vAbout))
								})),
						))
				})

			a.Backward(
				"a map continuous at each point of the space is continuous",
				func(b *Argument, atEach Fact) {
					local := b.Unfolded(atEach, ContinuousMapAtDef)
					b.Show(
						"f is continuous",
						ContinuousMap.Intro(
							Case(
								"f carries the space into the second space, as it does at each point",
								By(local)),
							Case(
								"the preimage of an open set v is open: each of its points has an open neighbourhood inside it",
								Derive(func(c *Argument) {
									c.FixAs[Set[B]]("v")
									vOpen := c.Assume()
									neighbourhoods := c.Have(
										"each point x of the preimage of v lies in an open set inside it",
										"∀x:A. x ∈ preimage_on(⋃T, f, v) ⇒ ∃u:set(A). u ∈ T ∧ u ⊆ preimage_on(⋃T, f, v) ∧ x ∈ u",
										Derive(func(d *Argument) {
											d.FixAs[A]("x")
											xIn := d.Assume()
											point := d.Have(
												"x is a point of the space that f sends into v",
												"x ∈ ⋃T ∧ f(x) ∈ v",
												BySets(xIn))
											u, around := d.ObtainAs[Set[A]](
												"f, continuous at x, carries an open set u about x into v",
												"∃u:set(A). u ∈ T ∧ x ∈ u ∧ ∀y:A. y ∈ u ⇒ f(y) ∈ v",
												By(local, point, vOpen))
											d.Take(u)
											d.Show(
												"u is open, holds x, and lies in the preimage of v, an open set lying in the space",
												BySets(around))
										}))
									c.Show(
										"so the preimage of v is open, by the pointwise criterion",
										By(neighbourhoods, topological_space.OpenPointwise.Read(topology)))
								})),
						))
				})
		}),
})}

// OpenPasting — a map continuous on each member of an open cover is
// continuous. A point of the space lies in a member u of the cover, and f
// carries the points of that subspace into the second space. The preimage
// of an open set v is open by the pointwise criterion: a point x of it lies
// in a member u of the cover, and the preimage of v in the subspace u is
// open there, so open in the space as u is, holds x and lies inside the
// preimage of v.
var OpenPasting = openPastingThm{family.Add(registry.ProofEntry{
	Name: "OpenPasting",
	Key:  "prop_2416eca4dfc501cc",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀c:set(set(A)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"c ⊆ T",
			"⋃T ⊆ ⋃c",
			"∀u:set(A). u ∈ c ⇒ continuous_map(subtopology(T, u), S, f)",
		},
		Conclusion: "continuous_map(T, S, f)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			S *Expr[Set[Set[B]]],
			c *Expr[Set[Set[A]]],
			f *Arrow[A, B],
			cOpen, covers, pieces Fact,
		) {
			a.Show(
				"f is continuous",
				ContinuousMap.Intro(
					Case(
						"a point x of the space lies in a member u of the cover, on whose subspace f carries it into ⋃S",
						Derive(func(b *Argument) {
							b.Fix("x")
							xIn := b.Assume()
							_, member := b.Obtain(
								"x lies in a member u of the cover",
								"∃u:set(A). u ∈ c ∧ x ∈ u",
								BySets(covers, xIn))
							onU := b.Have(
								"f is continuous on the subspace u",
								"continuous_map(subtopology(T, u), S, f)",
								By(pieces, member))
							b.Show(
								"x is a point of that subspace, so f carries it into the second space",
								BySets(MapsInto.Read(onU), topological_space.SubtopologySpace, xIn, member))
						})),
					Case(
						"the preimage of an open set v is open: each of its points has an open neighbourhood inside it",
						Derive(func(b *Argument) {
							b.Fix("v")
							vOpen := b.Assume()
							neighbourhoods := b.Have(
								"each point x of the preimage of v lies in an open set inside it",
								"∀x:A. x ∈ preimage_on(⋃T, f, v) ⇒ ∃w:set(A). w ∈ T ∧ w ⊆ preimage_on(⋃T, f, v) ∧ x ∈ w",
								Derive(func(d *Argument) {
									d.Fix("x")
									xIn := d.Assume()
									_, member := d.Obtain(
										"x lies in a member u of the cover, an open set",
										"∃u:set(A). u ∈ c ∧ u ∈ T ∧ x ∈ u",
										BySets(covers, cOpen, xIn))
									onU := d.Have(
										"f is continuous on the subspace u",
										"continuous_map(subtopology(T, u), S, f)",
										By(pieces, member))
									partOpen := d.Have(
										"the preimage of v in the subspace u is open there, so open in the space, u being open",
										"preimage_on(⋃T ∩ u, f, v) ∈ T",
										Simp(Rev(topological_space.SubtopologySpace)),
										By(topological_space.OpenInOpenSubtopology.Read(topology), PreimageOpen.Read(onU), vOpen, member))
									d.Take(d.Term("preimage_on(⋃T ∩ u, f, v)"))
									d.Show(
										"that preimage is open, holds x and lies in the preimage of v",
										BySets(partOpen, xIn, member))
								}))
							b.Show(
								"so the preimage of v is open, by the pointwise criterion",
								By(neighbourhoods, topological_space.OpenPointwise.Read(topology)))
						})),
				))
		}),
})}

// FiniteClosedPasting — a map continuous on each of finitely many closed
// sets covering the space is continuous.
var FiniteClosedPasting = finiteClosedPastingThm{family.Add(registry.ProofEntry{
	Name: "FiniteClosedPasting",
	Key:  "prop_7dcc38b20b4d6c47",
	Reading: "is_topology(T) is load-bearing: a finite union of closed sets is closed. " +
		"With k empty the space is empty and ∅ ∈ T makes every map continuous. S needs no axiom.",
	Deps: []registry.EntryLike{ClosedPasting, topological_space.UnionClosed},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀k:set(set(A)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"finite(k)",
			"∀c:set(A). c ∈ k ⇒ closed_in(T, c)",
			"⋃T ⊆ ⋃k",
			"∀c:set(A). c ∈ k ⇒ continuous_map(subtopology(T, c), S, f)",
		},
		Conclusion: "continuous_map(T, S, f)",
	},
		"induction on the finite family, pasting one closed piece at a time (ClosedPasting) onto "+
			"the subspace on the union of the others, a finite union of closed sets being closed "+
			"(UnionClosed); when k is empty the space is empty and every map on it is continuous"),
})}

// ImageClosureSubset — a continuous map carries the closure of a set
// into the closure of its image. The closure of the image is closed, so
// its preimage is closed; that preimage holds s, f carrying s into its
// image, so it holds the closure of s, the least closed set around s. The
// second space's axioms make the closure of the image closed; the first
// space's are not used.
var ImageClosureSubset = imageClosureSubsetThm{family.Add(registry.ProofEntry{
	Name: "ImageClosureSubset",
	Key:  "prop_54128f5d4fb1fa4a",
	Build: ContinuousMap.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"is_topology(S)",
			"s ⊆ ⋃T",
		},
		Conclusion: "image(f, closure(T, s)) ⊆ closure(S, image(f, s))",
		Abbrev: Abbrev{
			{Name: "closureOfImage", Text: "closure(S, image(f, s))"},
		},
	},
		func(
			a *Argument,
			continuous ContinuousMapFact[on.T, on.S],
			s *Expr[Set[A]],
			topology topological_space.IsTopologyFact[on.S],
			inSpace Fact,
		) {
			imageInSpace := a.Have(
				"the image of s lies in the second space, f carrying the first there",
				"image(f, s) ⊆ ⋃S",
				BySets(MapsInto.Read(continuous), inSpace))
			pulledBack := a.Have(
				"the closure of the image is closed, so f pulls it back to a closed set",
				"closed_in(T, preimage_on(⋃T, f, «closureOfImage»))",
				By(ClosedPreimage, continuous, topological_space.ClosureClosed.Read(topology), imageInSpace))
			sInside := a.Have(
				"which holds s, f carrying s into its image and the image lying in its closure",
				"s ⊆ preimage_on(⋃T, f, «closureOfImage»)",
				BySets(
					inSpace,
					topological_space.SubsetClosure.At(
						a.TermAs[Set[Set[B]]]("S"),
						a.TermAs[Set[B]]("image(f, s)"))))
			closureInside := a.Have(
				"so it holds the closure of s, the least closed set around s",
				"closure(T, s) ⊆ preimage_on(⋃T, f, «closureOfImage»)",
				By(topological_space.ClosureMinimal, pulledBack, sInside))
			a.Show(
				"f carries the closure of s into the closure of its image",
				BySets(closureInside))
		}),
})}
