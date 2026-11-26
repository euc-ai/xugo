// homeomorphism.go — homeomorphisms: the structure's two axioms; agreement,
// inverse and composite, and the relation of being homeomorphic; when a
// continuous bijection is one — when it carries closed sets to closed
// sets, and in particular when its domain is compact and its target
// Hausdorff, since then every closed set is compact, its image compact,
// and so closed; what a homeomorphism preserves; embeddings; retracts,
// closed in a Hausdorff space, connected or compact with the space.

package continuous

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure's axioms
// ---------------------------------------------------------------------------

// HomeomorphismContinuous — a homeomorphism is continuous.
var HomeomorphismContinuous = homeomorphismContinuousThm{family.Add(registry.ProofEntry{
	Name:  "HomeomorphismContinuous",
	Key:   "prop_7e1d3a857c3bc8d8",
	Build: HomeomorphicMap.Axiom("continuous_map(T, S, f)"),
})}

// HomeomorphismInverseMaps — a homeomorphism has a continuous inverse on the
// two spaces, each undoing the other on its space.
var HomeomorphismInverseMaps = homeomorphismInverseMapsThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphismInverseMaps",
	Key:  "prop_59dd981395818b12",
	Build: HomeomorphicMap.Axiom(
		"∃g:(B → A). " +
			"    continuous_map(S, T, g) ∧ (∀x:A. x ∈ ⋃T ⇒ g(f(x)) = x) ∧ (∀y:B. y ∈ ⋃S ⇒ f(g(y)) = y)"),
})}

// ---------------------------------------------------------------------------
// Closed bijections
// ---------------------------------------------------------------------------

// ClosedBijectionHomeomorphism — a continuous bijection of the spaces that
// carries closed sets to closed sets is a homeomorphism. Its inverse is
// the chosen inverse inverse_on(⋃T, f): it undoes f because f is
// one-to-one, and f undoes it because every point of the second space is
// a value. It keeps to the first space, and it pulls a closed set c back
// to the image of c under f, closed by hypothesis; so it is continuous,
// read through closed sets. No axiom of either space enters.
var ClosedBijectionHomeomorphism = closedBijectionHomeomorphismThm{family.Add(registry.ProofEntry{
	Name: "ClosedBijectionHomeomorphism",
	Key:  "prop_47cb6b1647245256",
	Build: ContinuousMap.Law(Statement{
		Hypotheses: []string{
			"∀c:set(A). closed_in(T, c) ⇒ closed_in(S, image(f, c))",
			"image(f, ⋃T) = ⋃S",
			"injective_on(⋃T, f)",
		},
		Conclusion: "homeomorphic_map(T, S, f)",
	},
		func(a *Argument, continuous ContinuousMapFact[on.T, on.S], closedMap, onto, injective Fact) {
			leftInverse := a.Have(
				"the chosen inverse undoes f on the first space, f being one-to-one there",
				"∀x:A. x ∈ ⋃T ⇒ inverse_on(⋃T, f, f(x)) = x",
				By(functions.InverseOnLeft, injective))
			rightInverse := a.Have(
				"and f undoes the chosen inverse on the second space, every point there being a value of f",
				"∀y:B. y ∈ ⋃S ⇒ f(inverse_on(⋃T, f, y)) = y",
				onto.RwRev(),
				Cite(functions.InverseOnRight))
			inverseContinuous := a.Have(
				"the chosen inverse is continuous, read through closed sets",
				"continuous_map(S, T, inverse_on(⋃T, f))",
				Simp(Fwd(ClosedPreimage)),
				SplitConj(
					Case(
						"it carries the second space into the first, every point there being a value of f",
						onto.RwRev(),
						Cite(functions.InverseOnIn)),
					Case(
						"and it pulls a closed set c back to the image of c under f, closed by hypothesis",
						Derive(func(b *Argument) {
							b.FixAs[Set[A]]("c")
							cClosed := b.Assume()
							inSpace := b.Have(
								"c lies in the first space, being closed there",
								"c ⊆ ⋃T",
								By(cClosed, topological_space.ClosedInDef))
							preimage := b.Have(
								"the chosen inverse pulls c back to its image under f, the two maps undoing each other",
								"preimage_on(⋃S, inverse_on(⋃T, f), c) = image(f, c)",
								BySets(leftInverse, rightInverse, MapsInto.Read(continuous), inSpace))
							b.Show(
								"which is closed, f carrying closed sets to closed sets",
								preimage.Rw(),
								By(closedMap, cClosed))
						})),
				))
			a.Show(
				"f is a homeomorphism",
				HomeomorphicMap.Intro(
					Case(
						"f is continuous",
						By(continuous)),
					Case(
						"and the chosen inverse is its continuous inverse",
						Witness(a.TermAs[Fun[B, A]]("inverse_on(⋃T, f)")),
						By(inverseContinuous, leftInverse, rightInverse)),
				))
		}),
})}

// ---------------------------------------------------------------------------
// From a compact space to a Hausdorff space
// ---------------------------------------------------------------------------

// CompactHausdorffClosedMap — a continuous map from a compact space to a
// Hausdorff space carries closed sets to closed sets: a closed set of the
// compact space is compact, its image is compact, and a compact set of a
// Hausdorff space is closed, the one step where an axiom of the second
// space enters.
var CompactHausdorffClosedMap = compactHausdorffClosedMapThm{family.Add(registry.ProofEntry{
	Name: "CompactHausdorffClosedMap",
	Key:  "prop_e225d3dc3dc5f91",
	Build: ContinuousMap.Law(Statement{
		Binders: "∀c:set(A).",
		Hypotheses: []string{
			"is_topology(S)",
			"hausdorff(S)",
			"compact_in(T, ⋃T)",
			"closed_in(T, c)",
		},
		Conclusion: "closed_in(S, image(f, c))",
	},
		func(
			a *Argument,
			continuous ContinuousMapFact[on.T, on.S],
			c *Expr[Set[A]],
			topology topological_space.IsTopologyFact[on.S],
			hausdorff, compactSpace, cClosed Fact,
		) {
			cCompact := a.Have(
				"c is compact, a closed part of the compact space",
				"compact_in(T, c)",
				By(cClosed, compactSpace, compact.ClosedSubsetCompact, topological_space.ClosedInDef))
			a.Show(
				"its image is compact, hence closed in the Hausdorff second space",
				By(compact.CompactClosed.Read(topology), hausdorff, ImageCompact.Read(continuous).At(c), cCompact))
		}),
})}

// CompactHausdorffHomeomorphism — a continuous bijection from a compact
// space onto a Hausdorff space is a homeomorphism: it carries closed sets
// to closed sets, and a continuous bijection that does is one. At the
// identity map it says a compact Hausdorff topology has no strictly
// coarser Hausdorff topology and no strictly finer compact one on the
// same points.
var CompactHausdorffHomeomorphism = compactHausdorffHomeomorphismThm{family.Add(registry.ProofEntry{
	Name: "CompactHausdorffHomeomorphism",
	Key:  "prop_ba589ec45a52e724",
	Build: ContinuousMap.Law(Statement{
		Hypotheses: []string{
			"is_topology(S)",
			"hausdorff(S)",
			"compact_in(T, ⋃T)",
			"image(f, ⋃T) = ⋃S",
			"injective_on(⋃T, f)",
		},
		Conclusion: "homeomorphic_map(T, S, f)",
	},
		func(
			a *Argument,
			continuous ContinuousMapFact[on.T, on.S],
			topology topological_space.IsTopologyFact[on.S],
			hausdorff, compactSpace, onto, injective Fact,
		) {
			a.Show(
				"f is a bijection carrying closed sets to closed sets, from a compact space to a Hausdorff one",
				By(
					ClosedBijectionHomeomorphism.Read(continuous),
					CompactHausdorffClosedMap.Read(continuous),
					topology,
					hausdorff,
					compactSpace,
					onto,
					injective))
		}),
})}

// ---------------------------------------------------------------------------
// Homeomorphisms: agreement, inverse, composite, and the relation between spaces
// ---------------------------------------------------------------------------

// HomeomorphismEq — a map agreeing on the space with a homeomorphism is a
// homeomorphism: it is continuous by Eq, and the homeomorphism's inverse
// undoes it on both spaces, since the two maps take one value at every
// point of the source space.
var HomeomorphismEq = homeomorphismEqThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphismEq",
	Key:  "prop_1698d676f0e7fe06",
	Build: HomeomorphicMap.Law(Statement{
		Binders: "∀g:(A → B).",
		Hypotheses: []string{
			"∀x:A. x ∈ ⋃T ⇒ f(x) = g(x)",
		},
		Conclusion: "homeomorphic_map(T, S, g)",
	},
		func(a *Argument, homeomorphism HomeomorphicMapFact[on.T, on.S], g *Arrow[A, B], agree Fact) {
			continuous := HomeomorphismContinuous.Read(homeomorphism)
			h, inverse := a.UnpackAs[Fun[B, A]](HomeomorphismInverseMaps.Read(homeomorphism), "h")
			laws := a.Conjuncts(
				inverse,
				"h is continuous",
				"h undoes f on the source space",
				"f undoes h on the target space")
			a.Do(Simp(Fwd(HomeomorphicMap)), SplitConj(
				Case(
					"g is continuous, as it agrees with f on the source space",
					By(agree, Eq.Read(continuous).At(g))),
				Case(
					"h is a continuous inverse of g",
					Witness(h),
					SplitConjAll(
						Case(
							"h is continuous",
							By(laws[0])),
						Case(
							"h undoes g on the source space",
							Derive(func(b *Argument) {
								x := b.FixAs[A]("x")
								inSource := b.Assume()
								// g(x) sits under h, so the agreement is turned to replace it by f(x).
								value := b.Have(
									"at a point of the source space g takes the value of f",
									"f(x) = g(x)",
									By(inSource, agree.At(x)))
								b.Show(
									"so h undoes g there as it undoes f",
									value.RwRev(),
									By(inSource, laws[1].At(x)))
							})),
						Case(
							"g undoes h on the target space",
							Derive(func(b *Argument) {
								y := b.FixAs[B]("y")
								inTarget := b.Assume()
								b.Show(
									"h carries y into the source space, where g takes the value of f",
									By(
										Normalized,
										inTarget,
										laws[2].At(y),
										MapsInto.Read(laws[0]).At(y),
										agree.At(b.TermAs[A]("h(y)"))))
							})),
					)),
			))
		}),
})}

// HomeomorphismInverse — the carrier inverse of a homeomorphism is a
// homeomorphism in the reverse direction, with both inverse equations.
// The continuous inverse g that a homeomorphism has makes f a bijection
// of the two spaces' points, and g, undoing f, is the chosen inverse
// inverse_on(⋃T, f) at every point of the second space; so the chosen
// inverse is continuous, as a map agreeing there with g. f is in turn its
// continuous inverse: the chosen inverse undoes f because f is one-to-one,
// and f undoes it because every point of the second space is a value.
var HomeomorphismInverse = homeomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphismInverse",
	Key:  "prop_50abe11f29658ad8",
	Build: HomeomorphicMap.Law("homeomorphic_map(S, T, inverse_on(⋃T, f)) ∧ "+
		"(∀x:A. x ∈ ⋃T ⇒ inverse_on(⋃T, f, f(x)) = x) ∧ "+
		"(∀y:B. y ∈ ⋃S ⇒ f(inverse_on(⋃T, f, y)) = y)",
		func(a *Argument, homeomorphism HomeomorphicMapFact[on.T, on.S]) {
			continuous := HomeomorphismContinuous.Read(homeomorphism)
			_, inverse := a.UnpackAs[Fun[B, A]](HomeomorphismInverseMaps.Read(homeomorphism), "g")
			laws := a.Conjuncts(
				inverse,
				"g is continuous",
				"g undoes f on the first space",
				"f undoes g on the second space")
			gContinuous, undoesF, undoesG := laws[0], laws[1], laws[2]
			bijection := a.Conjuncts(
				a.Have(
					"f is a bijection of the two spaces' points, with a two-sided inverse keeping to them",
					"injective_on(⋃T, f) ∧ image(f, ⋃T) = ⋃S",
					By(
						functions.TwoSidedInverseBijection,
						undoesF,
						undoesG,
						MapsInto.Read(continuous),
						MapsInto.Read(gContinuous))),
				"f is one-to-one on the first space",
				"and onto the second")
			injective, onto := bijection[0], bijection[1]
			agree := a.Have(
				"g, undoing f, is the chosen inverse at each point "+
					"of the second space, every such point a value of f",
				"∀y:B. y ∈ ⋃S ⇒ g(y) = inverse_on(⋃T, f, y)",
				onto.RwRev(),
				By(functions.InverseOnUnique, undoesF))
			leftInverse := a.Have(
				"the chosen inverse undoes f on the first space, f being one-to-one there",
				"∀x:A. x ∈ ⋃T ⇒ inverse_on(⋃T, f, f(x)) = x",
				By(functions.InverseOnLeft, injective))
			rightInverse := a.Have(
				"and f undoes the chosen inverse on the second space, every point there being a value of f",
				"∀y:B. y ∈ ⋃S ⇒ f(inverse_on(⋃T, f, y)) = y",
				onto.RwRev(),
				Cite(functions.InverseOnRight))
			a.Do(SplitConjAll(
				Case(
					"the chosen inverse is a homeomorphism of the second space onto the first",
					HomeomorphicMap.Intro(
						Case(
							"it is continuous, agreeing on the second space with the continuous g",
							By(Eq.Read(gContinuous), agree)),
						Case(
							"and f is its continuous inverse",
							Witness(a.TermAs[Fun[A, B]]("f")),
							By(continuous, leftInverse, rightInverse)),
					)),
				Case(
					"the chosen inverse undoes f on the first space",
					By(leftInverse)),
				Case(
					"and f undoes it on the second",
					By(rightInverse)),
			))
		}),
})}

// HomeomorphismIdentity — the identity is a homeomorphism of a space
// onto itself: it is continuous, and it is its own continuous inverse.
var HomeomorphismIdentity = homeomorphismIdentityThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphismIdentity",
	Key:  "prop_1a23dccbcc791715",
	Build: family.Theorem("∀T:set(set(A)). homeomorphic_map(T, T, identity_map)",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			identity := a.TermAs[Fun[A, A]]("identity_map")
			a.Show(
				"the identity is a homeomorphism",
				HomeomorphicMap.Intro(
					Case(
						"the identity is continuous",
						Cite(Identity)),
					Case(
						"and it is its own continuous inverse, undoing itself at every point",
						Witness(identity),
						By(Identity, functions.IdentityApply)),
				))
		}),
})}

// HomeomorphismCompose — homeomorphisms compose. The composite is
// continuous, and the composite h ∘ k of the two inverses, in the other
// order, is its continuous inverse. A point x of the first space goes by
// f to a point of the middle space, where k undoes g, and then h undoes
// f; a point z of the last space goes by k to a point of the middle
// space, where f undoes h, and then g undoes k.
var HomeomorphismCompose = homeomorphismComposeThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphismCompose",
	Key:  "prop_a607c8e7143788e6",
	Build: HomeomorphicMap.Law(Statement{
		Binders: "∀R:set(set(C)). ∀g:(B → C).",
		Hypotheses: []string{
			"homeomorphic_map(S, R, g)",
		},
		Conclusion: "homeomorphic_map(T, R, g ∘ f)",
	},
		func(
			a *Argument,
			first HomeomorphicMapFact[on.T, on.S],
			R *Expr[Set[Set[C]]],
			g *Arrow[B, C],
			second Fact,
		) {
			fContinuous := HomeomorphismContinuous.Read(first)
			gContinuous := HomeomorphismContinuous.Read(second)
			_, fInverse := a.UnpackAs[Fun[B, A]](HomeomorphismInverseMaps.Read(first), "h")
			fLaws := a.Conjuncts(
				fInverse,
				"h is continuous",
				"h undoes f on the first space",
				"f undoes h on the middle space")
			hContinuous, hUndoesF, fUndoesH := fLaws[0], fLaws[1], fLaws[2]
			_, gInverse := a.UnpackAs[Fun[C, B]](HomeomorphismInverseMaps.Read(second), "k")
			gLaws := a.Conjuncts(
				gInverse,
				"k is continuous",
				"k undoes g on the middle space",
				"g undoes k on the last space")
			kContinuous, kUndoesG, gUndoesK := gLaws[0], gLaws[1], gLaws[2]
			a.Show(
				"the composite is a homeomorphism",
				HomeomorphicMap.Intro(
					Case(
						"g ∘ f is continuous, a composite of continuous maps",
						By(Compose.Read(fContinuous), gContinuous)),
					Case(
						"and h ∘ k is its continuous inverse",
						Witness(a.TermAs[Fun[C, A]]("h ∘ k")),
						SplitConjAll(
							Case(
								"h ∘ k is continuous, a composite of continuous maps",
								By(Compose.Read(kContinuous), hContinuous)),
							Case(
								"h ∘ k undoes g ∘ f on the first space",
								Simp(Fwd(functions.ComposeApply)),
								Derive(func(b *Argument) {
									x := b.FixAs[A]("x")
									xIn := b.Assume()
									b.Show(
										"f carries x into the middle space, where k undoes g; then h undoes f",
										By(
											Normalized,
											xIn,
											hUndoesF.At(x),
											kUndoesG.At(b.TermAs[B]("f(x)")),
											MapsInto.Read(fContinuous).At(x)))
								})),
							Case(
								"and g ∘ f undoes h ∘ k on the last space",
								Simp(Fwd(functions.ComposeApply)),
								Derive(func(b *Argument) {
									z := b.FixAs[C]("z")
									zIn := b.Assume()
									b.Show(
										"k carries z into the middle space, where f undoes h; then g undoes k",
										By(
											Normalized,
											zIn,
											gUndoesK.At(z),
											fUndoesH.At(b.TermAs[B]("k(z)")),
											MapsInto.Read(kContinuous).At(z)))
								})),
						)),
				))
		}),
})}

// HomeomorphismIffOpenBijection — a homeomorphism is exactly a continuous
// open bijection of the two spaces. A homeomorphism's continuous inverse g
// makes it a bijection, and the image of an open set u under it is the
// preimage of u under g, open as g is continuous. Conversely the chosen
// inverse inverse_on(⋃T, f) of a continuous open bijection pulls an open
// set u back to its image under f, open as f is open; so it is continuous,
// read through open sets as ClosedBijectionHomeomorphism reads it through
// closed ones. No axiom of either space enters.
var HomeomorphismIffOpenBijection = homeomorphismIffOpenBijectionThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphismIffOpenBijection",
	Key:  "prop_18d102b8d17c8c7",
	Build: family.Theorem("∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). "+
		"    homeomorphic_map(T, S, f) ⇔ "+
		"    continuous_map(T, S, f) ∧ open_map(T, S, f) ∧ image(f, ⋃T) = ⋃S ∧ injective_on(⋃T, f)",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], f *Arrow[A, B]) {
			a.Iff()

			a.Forward(
				"a homeomorphism is a continuous open bijection",
				func(b *Argument, homeomorphism Fact) {
					continuous := HomeomorphismContinuous.Read(homeomorphism)
					_, inverse := b.UnpackAs[Fun[B, A]](HomeomorphismInverseMaps.Read(homeomorphism), "g")
					laws := b.Conjuncts(
						inverse,
						"g is continuous",
						"g undoes f on the first space",
						"f undoes g on the second space")
					gContinuous, undoesF, undoesG := laws[0], laws[1], laws[2]
					bijection := b.Have(
						"f is a bijection of the two spaces' points, with a two-sided inverse keeping to them",
						"injective_on(⋃T, f) ∧ image(f, ⋃T) = ⋃S",
						By(
							functions.TwoSidedInverseBijection,
							undoesF,
							undoesG,
							MapsInto.Read(continuous),
							MapsInto.Read(gContinuous)))
					b.Do(SplitConjAll(
						Case(
							"f is continuous",
							By(continuous)),
						Case(
							"f is open: the image of an open set u is its preimage under the continuous g",
							OpenMap.Intro(Derive(func(c *Argument) {
								c.FixAs[Set[A]]("u")
								uOpen := c.Assume()
								inSpace := c.Have(
									"u lies in the first space, being open there",
									"u ⊆ ⋃T",
									By(uOpen, set_order.MemberSubsetUnions))
								image := c.Have(
									"the image of u under f is its preimage under g, the two maps undoing each other",
									"image(f, u) = preimage_on(⋃S, g, u)",
									BySets(undoesF, undoesG, MapsInto.Read(continuous), inSpace))
								c.Show(
									"which is open, g being continuous",
									image.Rw(),
									By(PreimageOpen.Read(gContinuous), uOpen))
							}))),
						Case(
							"f carries the first space onto the second",
							By(bijection)),
						Case(
							"and is one-to-one on it",
							By(bijection)),
					))
				})

			a.Backward(
				"a continuous open bijection is a homeomorphism, its chosen inverse continuous",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"f is continuous",
						"f is open",
						"f carries the first space onto the second",
						"and is one-to-one on it")
					continuous, open, onto, injective := parts[0], parts[1], parts[2], parts[3]
					leftInverse := b.Have(
						"the chosen inverse undoes f on the first space, f being one-to-one there",
						"∀x:A. x ∈ ⋃T ⇒ inverse_on(⋃T, f, f(x)) = x",
						By(functions.InverseOnLeft, injective))
					rightInverse := b.Have(
						"and f undoes the chosen inverse on the second space, every point there being a value of f",
						"∀y:B. y ∈ ⋃S ⇒ f(inverse_on(⋃T, f, y)) = y",
						onto.RwRev(),
						Cite(functions.InverseOnRight))
					inverseContinuous := b.Have(
						"the chosen inverse is continuous",
						"continuous_map(S, T, inverse_on(⋃T, f))",
						ContinuousMap.Intro(
							Case(
								"it carries the second space into the first, every point there being a value of f",
								onto.RwRev(),
								Cite(functions.InverseOnIn)),
							Case(
								"and it pulls an open set u back to the image of u under f, open as f is open",
								Derive(func(c *Argument) {
									c.FixAs[Set[A]]("u")
									uOpen := c.Assume()
									inSpace := c.Have(
										"u lies in the first space, being open there",
										"u ⊆ ⋃T",
										By(uOpen, set_order.MemberSubsetUnions))
									preimage := c.Have(
										"the chosen inverse pulls u back to its image under f, the two maps undoing each other",
										"preimage_on(⋃S, inverse_on(⋃T, f), u) = image(f, u)",
										BySets(leftInverse, rightInverse, MapsInto.Read(continuous), inSpace))
									c.Show(
										"which is open, f being open",
										preimage.Rw(),
										By(OpenMap, open, uOpen))
								})),
						))
					b.Show(
						"f is a homeomorphism",
						HomeomorphicMap.Intro(
							Case(
								"f is continuous",
								By(continuous)),
							Case(
								"and the chosen inverse is its continuous inverse",
								Witness(b.TermAs[Fun[B, A]]("inverse_on(⋃T, f)")),
								By(inverseContinuous, leftInverse, rightInverse)),
						))
				})
		}),
})}

// HomeomorphismSubtopologies — a homeomorphism restricts to a
// homeomorphism of a subspace onto its image. The continuous inverse g
// carries the image of s back into s, since it undoes f at each point of
// s, a point of the space. So f, continuous on the subspace on s with its
// values in the image, is continuous into the subspace on the image, and
// g, continuous on that subspace with its values in s, is continuous into
// the subspace on s; the two inverse laws hold on the subspaces as on the
// spaces.
var HomeomorphismSubtopologies = homeomorphismSubtopologiesThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphismSubtopologies",
	Key:  "prop_c2a6bd0e11d0fd54",
	Build: HomeomorphicMap.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "homeomorphic_map(subtopology(T, s), subtopology(S, image(f, s)), f)",
	},
		func(a *Argument, homeomorphism HomeomorphicMapFact[on.T, on.S], s *Expr[Set[A]], inSpace Fact) {
			continuous := HomeomorphismContinuous.Read(homeomorphism)
			g, inverse := a.UnpackAs[Fun[B, A]](HomeomorphismInverseMaps.Read(homeomorphism), "g")
			laws := a.Conjuncts(
				inverse,
				"g is continuous",
				"g undoes f on the first space",
				"f undoes g on the second space")
			gContinuous, undoesF, undoesG := laws[0], laws[1], laws[2]
			backInS := a.Have(
				"g carries the image of s back into s, undoing f at each point of s, a point of the first space",
				"∀y:B. y ∈ image(f, s) ⇒ g(y) ∈ s",
				Simp(Fwd(set_image.ForallInImage)),
				By(undoesF, inSpace, set_basic.SubsetDef))
			// Continuity into a subspace is continuity into the space with values
			// in the subset, and a subspace's points are the points of its space in
			// the subset: each case reads its goal so before it closes.
			a.Show(
				"f restricts to a homeomorphism of the subspace on s onto the subspace on its image",
				HomeomorphicMap.Intro(
					Case(
						"f is continuous on the subspace on s, with its values in the image of s",
						Simp(Fwd(IntoSubtopology)),
						Simp(Fwd(topological_space.SubtopologySpace)),
						By(FromSubtopology.Read(continuous), set_image.FunInImage, set_basic.InInter)),
					Case(
						"and g is its continuous inverse",
						Witness(g),
						SplitConjAll(
							Case(
								"g is continuous on the subspace on the image, with its values in s",
								Simp(Fwd(IntoSubtopology)),
								Simp(Fwd(topological_space.SubtopologySpace)),
								By(FromSubtopology.Read(gContinuous), backInS, set_basic.InInter)),
							Case(
								"g undoes f on the subspace on s",
								Simp(Fwd(topological_space.SubtopologySpace)),
								By(undoesF, set_basic.InInter)),
							Case(
								"and f undoes g on the subspace on the image",
								Simp(Fwd(topological_space.SubtopologySpace)),
								By(undoesG, set_basic.InInter)),
						)),
				))
		}),
})}

// HomeomorphicRefl — a space is homeomorphic to itself, by the identity.
var HomeomorphicRefl = homeomorphicReflThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphicRefl",
	Key:  "prop_29801fdb94be94d",
	Build: family.Theorem("∀T:set(set(A)). homeomorphic(T, T)",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Show(
				"the identity is a homeomorphism of the space onto itself",
				Simp(Fwd(HomeomorphicDef)),
				Witness(a.TermAs[Fun[A, A]]("identity_map")),
				Cite(HomeomorphismIdentity))
		}),
})}

// HomeomorphicSym — being homeomorphic is symmetric: the carrier inverse
// of a homeomorphism is a homeomorphism back.
var HomeomorphicSym = homeomorphicSymThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphicSym",
	Key:  "prop_3c9537d02db05215",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"homeomorphic(T, S)",
		},
		Conclusion: "homeomorphic(S, T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], homeomorphicTS Fact) {
			_, homeomorphism := a.UnpackAs[Fun[A, B]](a.Unfolded(homeomorphicTS, HomeomorphicDef), "f")
			a.Show(
				"the carrier inverse of f is a homeomorphism of the second space onto the first",
				Simp(Fwd(HomeomorphicDef)),
				Witness(a.TermAs[Fun[B, A]]("inverse_on(⋃T, f)")),
				By(HomeomorphismInverse.Read(homeomorphism)))
		}),
})}

// HomeomorphicTrans — being homeomorphic is transitive: homeomorphisms
// compose.
var HomeomorphicTrans = homeomorphicTransThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphicTrans",
	Key:  "prop_4b3971528a268f1a",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀R:set(set(C)).",
		Hypotheses: []string{
			"homeomorphic(T, S)",
			"homeomorphic(S, R)",
		},
		Conclusion: "homeomorphic(T, R)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			R *Expr[Set[Set[C]]],
			homeomorphicTS, homeomorphicSR Fact,
		) {
			_, first := a.UnpackAs[Fun[A, B]](a.Unfolded(homeomorphicTS, HomeomorphicDef), "f")
			_, second := a.UnpackAs[Fun[B, C]](a.Unfolded(homeomorphicSR, HomeomorphicDef), "g")
			a.Show(
				"the composite g ∘ f of the two homeomorphisms is one",
				Simp(Fwd(HomeomorphicDef)),
				Witness(a.TermAs[Fun[A, C]]("g ∘ f")),
				By(HomeomorphismCompose.Read(first), second))
		}),
})}

// ---------------------------------------------------------------------------
// What a homeomorphism preserves
// ---------------------------------------------------------------------------

// HausdorffInjectivePreimage — a space with a continuous one-to-one map
// into a Hausdorff space is Hausdorff. Two distinct points of the first
// space have distinct values, points of the second; disjoint open sets
// about the values pull back to disjoint open sets about the points. No
// axiom of either space enters.
var HausdorffInjectivePreimage = hausdorffInjectivePreimageThm{family.Add(registry.ProofEntry{
	Name: "HausdorffInjectivePreimage",
	Key:  "prop_bfd23e9ed83ba468",
	Build: ContinuousMap.Law(Statement{
		Hypotheses: []string{
			"hausdorff(S)",
			"injective_on(⋃T, f)",
		},
		Conclusion: "hausdorff(T)",
	},
		func(a *Argument, continuous ContinuousMapFact[on.T, on.S], hausdorff, injective Fact) {
			separates := a.Unfolded(hausdorff, topological_space.HausdorffDef)
			// Two distinct points of the first space are to be held by disjoint
			// open sets of it.
			a.Do(Simp(Fwd(topological_space.HausdorffDef)))
			a.FixAs[A]("x")
			a.FixAs[A]("y")
			distinct := a.Assume()
			values := a.Have(
				"f carries x and y to distinct points of the second space, being one-to-one on the first",
				"f(x) ∈ ⋃S ∧ f(y) ∈ ⋃S ∧ f(x) ≠ f(y)",
				By(distinct, injective, MapsInto.Read(continuous), functions.InjectiveOnDef))
			u, v, apart := a.Obtain2As[Set[B], Set[B]](
				"so disjoint open sets u and v of the second space hold f(x) and f(y)",
				"∃u v:set(B). u ∈ S ∧ v ∈ S ∧ f(x) ∈ u ∧ f(y) ∈ v ∧ u ∩ v = ∅",
				By(separates, values))
			a.Take(a.TermAs[Set[A]]("preimage_on(⋃T, f, u)"))
			a.Take(a.TermAs[Set[A]]("preimage_on(⋃T, f, v)"))
			a.Show(
				"the preimages of u and v are open, hold x and y, and are disjoint as u and v are",
				BySets(At(PreimageOpen.Read(continuous), u), At(PreimageOpen.Read(continuous), v), distinct, apart))
		}),
})}

// HomeomorphicHausdorff — of two homeomorphic spaces one is Hausdorff
// exactly when the other is. A homeomorphism f and its continuous inverse
// g undo each other, so each is one-to-one on its space, and a space with
// a continuous one-to-one map into a Hausdorff space is Hausdorff: through
// g one way and through f the other.
var HomeomorphicHausdorff = homeomorphicHausdorffThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphicHausdorff",
	Key:  "prop_6a9d66d08f1eb4b4",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"homeomorphic(T, S)",
		},
		Conclusion: "hausdorff(T) ⇔ hausdorff(S)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], homeomorphicTS Fact) {
			_, homeomorphism := a.UnpackAs[Fun[A, B]](a.Unfolded(homeomorphicTS, HomeomorphicDef), "f")
			_, inverse := a.UnpackAs[Fun[B, A]](HomeomorphismInverseMaps.Read(homeomorphism), "g")
			laws := a.Conjuncts(
				inverse,
				"g is continuous",
				"g undoes f on the first space",
				"f undoes g on the second space")
			gContinuous, undoesF, undoesG := laws[0], laws[1], laws[2]
			a.Iff()

			a.Forward(
				"a Hausdorff first space makes the second Hausdorff, through g",
				func(b *Argument, hausdorffT Fact) {
					b.Show(
						"g is continuous, and one-to-one on the second space as f undoes it there",
						By(
							HausdorffInjectivePreimage.Read(gContinuous),
							hausdorffT,
							undoesG,
							functions.InjectiveOnLeftInverse))
				})

			a.Backward(
				"a Hausdorff second space makes the first Hausdorff, through f",
				func(b *Argument, hausdorffS Fact) {
					b.Show(
						"f is continuous, and one-to-one on the first space as g undoes it there",
						By(
							HausdorffInjectivePreimage.Read(HomeomorphismContinuous.Read(homeomorphism)),
							hausdorffS,
							undoesF,
							functions.InjectiveOnLeftInverse))
				})
		}),
})}

// HomeomorphicCompact — of two homeomorphic spaces one is compact
// exactly when the other is. A homeomorphism f of the first space onto the
// second is continuous and onto, so the second space is the continuous
// image of the first, and the continuous image of a compact set is
// compact; the spaces being homeomorphic the other way too
// (HomeomorphicSym), the same holds through a homeomorphism g back.
var HomeomorphicCompact = homeomorphicCompactThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphicCompact",
	Key:  "prop_66535afdc5043f7",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"homeomorphic(T, S)",
		},
		Conclusion: "compact_in(T, ⋃T) ⇔ compact_in(S, ⋃S)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], homeomorphicTS Fact) {
			f, fHomeomorphism := a.UnpackAs[Fun[A, B]](a.Unfolded(homeomorphicTS, HomeomorphicDef), "f")
			g, gHomeomorphism := a.UnpackAs[Fun[B, A]](
				a.Unfolded(GroupPremises(homeomorphicTS, HomeomorphicSym.At(T, S)), HomeomorphicDef), "g")
			fOnto := a.Have(
				"f carries the first space onto the second, a homeomorphism being a bijection",
				"image(f, ⋃T) = ⋃S",
				By(HomeomorphismIffOpenBijection.At(T, S, f), fHomeomorphism))
			gOnto := a.Have(
				"and g the second onto the first",
				"image(g, ⋃S) = ⋃T",
				By(HomeomorphismIffOpenBijection.At(S, T, g), gHomeomorphism))
			a.Iff()

			a.Forward(
				"a compact first space makes the second compact",
				func(b *Argument, compactT Fact) {
					b.Show(
						"the second space is the image of the compact first under the continuous f",
						fOnto.RwRev(),
						By(ImageCompact.Read(HomeomorphismContinuous.Read(fHomeomorphism)), compactT))
				})

			a.Backward(
				"a compact second space makes the first compact",
				func(b *Argument, compactS Fact) {
					b.Show(
						"the first space is the image of the compact second under the continuous g",
						gOnto.RwRev(),
						By(ImageCompact.Read(HomeomorphismContinuous.Read(gHomeomorphism)), compactS))
				})
		}),
})}

// HomeomorphicConnected — of two homeomorphic spaces one is connected
// exactly when the other is: as for compactness, each space is the image
// of the other under a continuous map onto it, a homeomorphism f one way
// and, the spaces being homeomorphic the other way too (HomeomorphicSym),
// a homeomorphism g back; and the continuous image of a connected set is
// connected.
var HomeomorphicConnected = homeomorphicConnectedThm{family.Add(registry.ProofEntry{
	Name: "HomeomorphicConnected",
	Key:  "prop_181a60fe969e49b8",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)).",
		Hypotheses: []string{
			"homeomorphic(T, S)",
		},
		Conclusion: "connected_in(T, ⋃T) ⇔ connected_in(S, ⋃S)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], homeomorphicTS Fact) {
			f, fHomeomorphism := a.UnpackAs[Fun[A, B]](a.Unfolded(homeomorphicTS, HomeomorphicDef), "f")
			g, gHomeomorphism := a.UnpackAs[Fun[B, A]](
				a.Unfolded(GroupPremises(homeomorphicTS, HomeomorphicSym.At(T, S)), HomeomorphicDef), "g")
			fOnto := a.Have(
				"f carries the first space onto the second, a homeomorphism being a bijection",
				"image(f, ⋃T) = ⋃S",
				By(HomeomorphismIffOpenBijection.At(T, S, f), fHomeomorphism))
			gOnto := a.Have(
				"and g the second onto the first",
				"image(g, ⋃S) = ⋃T",
				By(HomeomorphismIffOpenBijection.At(S, T, g), gHomeomorphism))
			a.Iff()

			a.Forward(
				"a connected first space makes the second connected",
				func(b *Argument, connectedT Fact) {
					b.Show(
						"the second space is the image of the connected first under the continuous f",
						fOnto.RwRev(),
						By(ImageConnected.Read(HomeomorphismContinuous.Read(fHomeomorphism)), connectedT))
				})

			a.Backward(
				"a connected second space makes the first connected",
				func(b *Argument, connectedS Fact) {
					b.Show(
						"the first space is the image of the connected second under the continuous g",
						gOnto.RwRev(),
						By(ImageConnected.Read(HomeomorphismContinuous.Read(gHomeomorphism)), connectedS))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Embeddings
// ---------------------------------------------------------------------------

// EmbeddingImpContinuous — an embedding is continuous: a homeomorphism
// onto the image is continuous into the subspace on the image, and a map
// continuous into a subspace is continuous into the space.
var EmbeddingImpContinuous = embeddingImpContinuousThm{family.Add(registry.ProofEntry{
	Name: "EmbeddingImpContinuous",
	Key:  "prop_c1b4c455f016efa2",
	Build: EmbeddingMap.Law("continuous_map(T, S, f)",
		func(a *Argument, embedding EmbeddingMapFact[on.T, on.S]) {
			ontoImage := a.Unfolded(embedding, EmbeddingMap)
			a.Show(
				"f is continuous into the subspace on its image, hence into the second space",
				By(HomeomorphismContinuous.Read(ontoImage), IntoSubtopology))
		}),
})}

// CompactHausdorffEmbedding — a continuous one-to-one map of a compact
// space into a Hausdorff space is an embedding. Into the subspace of the
// second space on its image f is continuous, its values lying in the
// image, and onto, the image lying in the second space; that subspace is
// a Hausdorff topology, so f is a continuous bijection from a compact
// space onto a Hausdorff space, a homeomorphism.
var CompactHausdorffEmbedding = compactHausdorffEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "CompactHausdorffEmbedding",
	Key:  "prop_c387e47926fbb6ae",
	Build: ContinuousMap.Law(Statement{
		Hypotheses: []string{
			"is_topology(S)",
			"hausdorff(S)",
			"compact_in(T, ⋃T)",
			"injective_on(⋃T, f)",
		},
		Conclusion: "embedding_map(T, S, f)",
	},
		func(
			a *Argument,
			continuous ContinuousMapFact[on.T, on.S],
			topology topological_space.IsTopologyFact[on.S],
			hausdorff, compactSpace, injective Fact,
		) {
			intoImage := a.Have(
				"f is continuous into the subspace on its image, where its values lie",
				"continuous_map(T, subtopology(S, image(f, ⋃T)), f)",
				By(IntoSubtopology, continuous, set_image.FunInImage))
			onto := a.Have(
				"and onto that subspace, whose points are the points of the second space in the image",
				"image(f, ⋃T) = ⋃subtopology(S, image(f, ⋃T))",
				Simp(Fwd(topological_space.SubtopologySpace)),
				BySets(MapsInto.Read(continuous)))
			a.Show(
				"f is a homeomorphism onto the subspace on its image, a Hausdorff topology",
				EmbeddingMap.Intro(
					By(
						CompactHausdorffHomeomorphism.Read(intoImage),
						topological_space.SubtopologyTopology.Read(topology),
						topological_space.HausdorffSubtopology,
						hausdorff,
						compactSpace,
						onto,
						injective)))
		}),
})}

// ---------------------------------------------------------------------------
// Retracts
// ---------------------------------------------------------------------------

// RetractClosed — a retract of a Hausdorff space is closed. Let r be a
// continuous map of the space into the subspace on s that fixes each point
// of s. A point x of the space outside s differs from its value r(x), a
// point of s, so disjoint open sets u and v hold x and r(x). The points of
// the space that r carries into v ∩ s, an open set of the subspace, form an
// open set, and its meet with u is an open set about x outside s: a point y
// of s in it would be its own value r(y), so in v as well as in u. So the
// complement of s is open, each of its points lying in an open set inside it.
var RetractClosed = retractClosedThm{family.Add(registry.ProofEntry{
	Name: "RetractClosed",
	Key:  "prop_e7ab9063c96e984b",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"hausdorff(T)",
			"retract_of(s)",
		},
		Conclusion: "closed_in(s)",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			s *Expr[Set[A]],
			hausdorff, retract Fact,
		) {
			T := a.TermAs[Set[Set[A]]]("T")
			parts := a.Conjuncts(
				a.Unfolded(retract, RetractOfDef),
				"s lies in the space",
				"and a continuous map of the space into the subspace on s fixes each point of s")
			inSpace := parts[0]
			_, retraction := a.UnpackAs[Fun[A, A]](parts[1], "r")
			properties := a.Conjuncts(
				retraction,
				"r is continuous into the subspace on s",
				"r fixes each point of s")
			continuous, fixes := properties[0], properties[1]

			neighbourhoods := a.Have(
				"each point of the space outside s lies in an open set outside s",
				"∀x:A. x ∈ ⋃T ∖ s ⇒ ∃w:set(A). w ∈ T ∧ w ⊆ ⋃T ∖ s ∧ x ∈ w",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					outside := b.Assume()
					intoS := b.Have(
						"r carries x into s, the points of the subspace being those of the space in s",
						"r(x) ∈ s",
						BySets(outside, MapsInto.Read(continuous).At(x), topological_space.SubtopologySpace.At(T, s)))
					distinct := b.Have(
						"so x and r(x) are distinct points of the space, x lying outside s",
						"x ∈ ⋃T ∧ r(x) ∈ ⋃T ∧ x ≠ r(x)",
						BySets(outside, intoS, inSpace))
					_, v, apart := b.Obtain2As[Set[A], Set[A]](
						"T being Hausdorff, disjoint open sets u and v hold x and r(x)",
						"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ r(x) ∈ v ∧ u ∩ v = ∅",
						By(hausdorff, distinct, topological_space.HausdorffDef))
					pullback := b.Have(
						"the points of the space that r carries into v ∩ s "+
							"form an open set, v ∩ s being open in the subspace",
						"preimage_on(⋃T, r, v ∩ s) ∈ T",
						By(apart, PreimageOpen.Read(continuous), topological_space.TraceOpen.At(T, s, v)))
					b.Take(b.TermAs[Set[A]]("u ∩ preimage_on(⋃T, r, v ∩ s)"))
					b.Do(SplitConjAll(
						Case(
							"u meets that set in an open set",
							By(apart, pullback, topological_space.InterOpen.Read(topology))),
						Case(
							"which lies outside s: a point y of s in it is its own value r(y), so lies in v as well as in u",
							BySets(fixes, apart)),
						Case(
							"and holds x, r(x) lying in v ∩ s",
							BySets(outside, intoS, apart)),
					))
				}))
			a.Show(
				"s lies in the space, and its complement is open, "+
					"each of its points lying in an open set inside it",
				By(
					inSpace,
					neighbourhoods,
					topological_space.ClosedInDef,
					topological_space.OpenPointwise.Read(topology)))
		}),
})}
