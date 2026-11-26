// subtopology.go — the topology a subset of the space inherits: each
// open set cut down to the subset; and connectedness and compactness,
// which a subset of the subspace has there exactly when it has them in
// the whole space.

package topological_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The subspace topology
// ---------------------------------------------------------------------------

// SubtopologySpace — the space of the subspace topology on s is the
// part of s inside the space: its open sets are the open sets of T cut
// to s, and their union is the union of T cut to s. No axiom enters,
// so the family is spelled.
var SubtopologySpace = subtopologySpaceThm{family.Add(registry.ProofEntry{
	Name: "SubtopologySpace",
	Key:  "prop_3db5dfeffae42bdb",
	Build: family.Theorem("∀T:set(set(A)). ∀s:set(A). ⋃subtopology(T, s) = ⋃T ∩ s",
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]]) {
			a.Show(
				"a point of an open set cut to s is a point of the space in s, and conversely",
				Unfold(SubtopologyDef),
				BySets())
		}),
})}

// TraceOpen — the trace u ∩ s of an open set u is open in the subspace:
// it is the image of u under the cut. No axiom enters, so the family is
// spelled.
var TraceOpen = traceOpenThm{family.Add(registry.ProofEntry{
	Name: "TraceOpen",
	Key:  "prop_c67593a328fdae7c",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s u:set(A).",
		Hypotheses: []string{
			"u ∈ T",
		},
		Conclusion: "u ∩ s ∈ subtopology(T, s)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, u *Expr[Set[A]], open Fact) {
			cut := a.TermAs[Fun[Set[A], Set[A]]]("λw:set(A). w ∩ s")
			a.Show(
				"the subspace's open sets are the images of the open sets under the cut",
				Unfold(SubtopologyDef),
				By(set_image.FunInImage.At(cut, T, u), open))
		}),
})}

// OpenInSubtopology — a set is open in the subspace exactly when it is
// the trace of an open set: the subspace topology read member by member.
// No axiom enters, so the family is spelled.
var OpenInSubtopology = openInSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "OpenInSubtopology",
	Key:  "prop_66b0c183b381bbe9",
	Build: family.Theorem("∀T:set(set(A)). ∀s t:set(A). "+
		"    t ∈ subtopology(T, s) ⇔ ∃u:set(A). t = u ∩ s ∧ u ∈ T",
		func(a *Argument, T *Expr[Set[Set[A]]], s, t *Expr[Set[A]]) {
			// InImage pinned at sets of sets: Go's Simp does not adapt a
			// rule's type letters.
			a.Show(
				"membership in an image is being the image of a member",
				Unfold(SubtopologyDef),
				Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[A]](), TypeBinder.BindB[Set[A]]()))),
				Basic())
		}),
})}

// SubtopologyInduced — the subspace topology is induced by the identity
// on the part of the subset lying in the original space. Every original
// open lies in that space, so its restricted preimage is its trace.
var SubtopologyInduced = subtopologyInducedThm{family.Add(registry.ProofEntry{
	Name: "SubtopologyInduced",
	Key:  "prop_b43bd57dc04f6df8",
	Build: family.Theorem("∀T:set(set(A)). ∀s:set(A). "+
		"    subtopology(T, s) = induced_topology(⋃T ∩ s, T, identity_map)",
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]]) {
			agree := a.Have(
				"traces are restricted identity preimages on each original open",
				"∀u:set(A). u ∈ T ⇒ u ∩ s = preimage_on(⋃T ∩ s, identity_map, u)",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("u")
					open := b.Assume()
					b.Show(
						"an original open already lies in the space",
						Unfold(functions.PreimageOnDef),
						Unfold(functions.IdentityApply),
						BySets(open))
				}))
			cut := a.TermAs[Fun[Set[A], Set[A]]]("λu:set(A). u ∩ s")
			pullback := a.TermAs[Fun[Set[A], Set[A]]]("preimage_on(⋃T ∩ s, identity_map)")
			a.Show(
				"equal images on the original opens give equal topologies",
				Unfold(SubtopologyDef),
				Unfold(InducedTopologyDef),
				By(agree, set_image.ImageCongruence.At(cut, pullback, T)))
		}),
})}

// SubtopologyTopology — a subspace inherits a topology by the restricted
// identity map from its original topology.
var SubtopologyTopology = subtopologyTopologyThm{family.Add(registry.ProofEntry{
	Name: "SubtopologyTopology",
	Key:  "prop_279cf798e156cf83",
	Build: IsTopology.Law("∀s:set(A). is_topology(subtopology(s))",
		func(a *Argument, T *Expr[Set[Set[A]]], topology IsTopologyFact[on.T], s *Expr[Set[A]]) {
			a.Show(
				"the identity induces the subspace topology",
				Simp(Fwd(SubtopologyInduced)),
				By(
					topology,
					InducedTopology.At(T, a.TermAs[Set[A]]("⋃T ∩ s"), a.TermAs[Fun[A, A]]("identity_map"))))
		}),
})}

// ClosedInSubtopology — the closed sets of the subspace are the traces of
// the closed sets of T, as its open sets are the traces of the open ones.
// Read through the definitions, c is closed in the subspace when it lies
// in the subspace's points ⋃T ∩ s and its complement there is the trace
// u ∩ s of an open u. Forward, c is then the trace of ⋃T ∖ u, closed as
// the complement of an open set; backward, the complement of the trace
// d ∩ s of a closed d is the trace of the open ⋃T ∖ d. No axiom enters,
// so T is spelled.
var ClosedInSubtopology = closedInSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "ClosedInSubtopology",
	Key:  "prop_59f8f761d72273bb",
	Build: family.Theorem("∀T:set(set(A)). ∀s c:set(A). "+
		"    closed_in(subtopology(T, s), c) ⇔ ∃d:set(A). closed_in(T, d) ∧ c = d ∩ s",
		func(a *Argument, T *Expr[Set[Set[A]]], s, c *Expr[Set[A]]) {
			a.Iff()

			a.Forward(
				"c is the trace of the complement of an open set, and that complement is closed",
				func(b *Argument, closed Fact) {
					opened := b.Simplified(closed, Fwd(ClosedInDef), Fwd(SubtopologySpace), Fwd(OpenInSubtopology))
					parts := b.Conjuncts(
						opened,
						"the complement of c in the subspace's points is the trace of an open set u",
						"c lies in the subspace's points")
					_, trace := b.Unpack(parts[0])
					traceParts := b.Conjuncts(
						trace,
						"the complement of c there is u ∩ s",
						"u is open")
					b.Take(b.TermAs[Set[A]]("⋃T ∖ u"))
					traced := b.Have(
						"c is the trace of the complement of u in the space",
						"c = (⋃T ∖ u) ∩ s",
						BySets(traceParts[0], parts[1]))
					b.Show(
						"the complement of the open set u in the space is closed",
						By(OpenClosedComplement, traceParts[1], traced))
				})

			a.Backward(
				"the complement of the trace of a closed set d is the trace of the open complement of d",
				func(b *Argument, traced Fact) {
					_, closedTrace := b.Unpack(traced)
					parts := b.Conjuncts(
						closedTrace,
						"d is closed",
						"c is the trace of d")
					dParts := b.Conjuncts(
						b.Unfolded(parts[0], ClosedInDef),
						"d lies in the space",
						"the complement of d in the space is open")
					within := b.Have(
						"c lies in the subspace's points",
						"c ⊆ ⋃T ∩ s",
						BySets(parts[1], dParts[0]))
					complement := b.Have(
						"the complement of c in the subspace's points is the trace of the complement of d",
						"(⋃T ∩ s) ∖ c = (⋃T ∖ d) ∩ s",
						BySets(parts[1]))
					b.Show(
						"so c is closed in the subspace: its complement there is the trace of an open set",
						Simp(Fwd(ClosedInDef), Fwd(SubtopologySpace), Fwd(OpenInSubtopology)),
						By(complement, dParts[1], within))
				})
		}),
})}

// ---------------------------------------------------------------------------
// More on the subspace
// ---------------------------------------------------------------------------

// SubtopologySelf — the subspace on the whole space is the space: an open
// set lies in the space, so cutting it to the space changes nothing, and
// the image of T under the cut is T. No axiom enters.
var SubtopologySelf = subtopologySelfThm{family.Add(registry.ProofEntry{
	Name: "SubtopologySelf",
	Key:  "prop_c13e83f9eb979e11",
	Build: family.Theorem("∀T:set(set(A)). subtopology(T, ⋃T) = T",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			cut := a.TermAs[Fun[Set[A], Set[A]]]("λu:set(A). u ∩ ⋃T")
			identity := a.TermAs[Fun[Set[A], Set[A]]]("λu:set(A). u")
			unchanged := a.Have(
				"an open set lies in the space, so cutting it to the space leaves it as it is",
				"∀u:set(A). u ∈ T ⇒ u ∩ ⋃T = u",
				BySets())
			a.Show(
				"the cut agrees with the identity on T, so the image of T under it is T",
				Unfold(SubtopologyDef),
				By(unchanged, set_image.ImageCongruence.At(cut, identity, T), set_image.ImageIdentity))
		}),
})}

// SubtopologySubtopology — a subspace of a subspace is the subspace on
// the meet: the image of an image is the image under the composite, and
// cutting to s and then to t is cutting to s ∩ t. No axiom enters.
var SubtopologySubtopology = subtopologySubtopologyThm{family.Add(registry.ProofEntry{
	Name: "SubtopologySubtopology",
	Key:  "prop_cf910efd67264c56",
	Build: family.Theorem("∀T:set(set(A)). ∀s t:set(A). "+
		"    subtopology(subtopology(T, s), t) = subtopology(T, s ∩ t)",
		func(a *Argument, T *Expr[Set[Set[A]]], s, t *Expr[Set[A]]) {
			a.Show(
				"the two cuts in turn are one cut, to s and then to t, which is the cut to s ∩ t",
				// ↦ image(λu. u ∩ t, image(λu. u ∩ s, T)) = image(λu. u ∩ (s ∩ t), T)
				Unfold(SubtopologyDef),
				// ↦ image((λu. u ∩ t) ∘ (λu. u ∩ s), T) = …
				Simp(Rev(set_image.ImageCompose)),
				// ↦ image(λx. x ∩ s ∩ t, T) = …
				Unfold(functions.ComposeApply),
				// ↦ … = image(λu. u ∩ s ∩ t, T), the same cut
				Simp(Fwd(set_algebra.InterAssoc)),
				Refl())
		}),
})}

// OpenInOpenSubtopology — the open sets of an open subspace are the
// open sets inside it: a trace u ∩ s on the open s is the meet of two
// open sets, and an open set inside s is its own trace on s.
var OpenInOpenSubtopology = openInOpenSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "OpenInOpenSubtopology",
	Key:  "prop_e937e6439e91e14d",
	Build: IsTopology.Law(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ∈ T",
		},
		Conclusion: "t ∈ subtopology(T, s) ⇔ t ∈ T ∧ t ⊆ s",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			s, t *Expr[Set[A]],
			sOpen Fact,
		) {
			a.Iff()

			a.Forward(
				"a trace on the open set s is a meet of two open sets, and lies inside s",
				func(b *Argument, inSubspace Fact) {
					u, trace := b.ObtainAs[Set[A]](
						"t is the trace of an open set u",
						"∃u:set(A). t = u ∩ s ∧ u ∈ T",
						By(inSubspace, OpenInSubtopology))
					parts := b.Conjuncts(
						trace,
						"t is u ∩ s",
						"u is open")
					b.Do(parts[0].Rw())
					b.Show(
						"u ∩ s is the meet of the open sets u and s, and lies inside s",
						By(InterOpen.Read(topology), parts[1], sOpen, set_order.InterSubset.At(s, u)))
				})

			a.Backward(
				"an open set inside s is its own trace on s",
				func(b *Argument, openInside Fact) {
					parts := b.Conjuncts(
						openInside,
						"t is open",
						"t lies inside s")
					b.Show(
						"the trace t ∩ s of the open set t is open in the subspace, and it is t itself, t lying inside s",
						By(Normalized, TraceOpen.At(T, s, t), parts[0], set_order.SubsetInterAbsorption.At(t, s), parts[1]))
				})
		}),
})}

// ClosedInClosedSubtopology — the closed sets of a closed subspace are
// the closed sets inside it: a closed set of the subspace is the trace
// d ∩ s of a closed d, the meet of two closed sets, and a closed set
// inside s is its own trace on s.
var ClosedInClosedSubtopology = closedInClosedSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "ClosedInClosedSubtopology",
	Key:  "prop_caf380d6e3de49b8",
	Build: IsTopology.Law(Statement{
		Binders: "∀s c:set(A).",
		Hypotheses: []string{
			"closed_in(T, s)",
		},
		Conclusion: "closed_in(subtopology(T, s), c) ⇔ closed_in(T, c) ∧ c ⊆ s",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			s, c *Expr[Set[A]],
			sClosed Fact,
		) {
			a.Iff()

			a.Forward(
				"a closed set of the subspace is the trace of a closed set, a meet of two closed sets inside s",
				func(b *Argument, closedThere Fact) {
					d, traced := b.ObtainAs[Set[A]](
						"c is the trace of a closed set d",
						"∃d:set(A). closed_in(T, d) ∧ c = d ∩ s",
						By(closedThere, ClosedInSubtopology))
					parts := b.Conjuncts(
						traced,
						"d is closed",
						"c is d ∩ s")
					b.Do(parts[1].Rw())
					b.Show(
						"d ∩ s is the meet of the closed sets d and s, and lies inside s",
						By(InterClosed.Read(topology), parts[0], sClosed, set_order.InterSubset.At(s, d)))
				})

			a.Backward(
				"a closed set inside s is its own trace on s",
				func(b *Argument, closedInside Fact) {
					parts := b.Conjuncts(
						closedInside,
						"c is closed",
						"c lies inside s")
					b.Show(
						"c, lying inside s, is the trace c ∩ s of the closed set c",
						By(ClosedInSubtopology.At(T, s, c), parts[0], set_order.SubsetInterAbsorption.At(c, s), parts[1]))
				})
		}),
})}

// ClosedInSubtopologyInsideClosed — a set closed in the subspace s is
// closed in the space once it lies inside a closed set d of the space
// that lies inside s: it is the trace e ∩ s of a closed set e, and since
// it lies in d ⊆ s it is the meet e ∩ d of two closed sets.
var ClosedInSubtopologyInsideClosed = closedInSubtopologyInsideClosedThm{family.Add(registry.ProofEntry{
	Name: "ClosedInSubtopologyInsideClosed",
	Key:  "prop_88952eda2916a74f",
	Build: IsTopology.Law(Statement{
		Binders: "∀s c d:set(A).",
		Hypotheses: []string{
			"closed_in(subtopology(T, s), c)",
			"closed_in(T, d)",
			"c ⊆ d",
			"d ⊆ s",
		},
		Conclusion: "closed_in(T, c)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			s, c, d *Expr[Set[A]],
			closedThere, dClosed, cInD, dInS Fact,
		) {
			e, traced := a.ObtainAs[Set[A]](
				"c is the trace of a closed set e",
				"∃e:set(A). closed_in(T, e) ∧ c = e ∩ s",
				By(closedThere, ClosedInSubtopology))
			parts := a.Conjuncts(
				traced,
				"e is closed",
				"c is e ∩ s")
			meet := a.Have(
				"c lies in d, which lies in s, so c is e ∩ d",
				"c = e ∩ d",
				BySets(parts[1], cInD, dInS))
			a.Do(meet.Rw())
			a.Show(
				"e ∩ d is the meet of the closed sets e and d",
				By(InterClosed.Read(topology).At(e, d), parts[0], dClosed))
		}),
})}

// ClosureSubtopology — the closure in a subspace is the closure in the
// space, cut to the subspace.
var ClosureSubtopology = closureSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "ClosureSubtopology",
	Key:  "prop_8c3d1b3cf7f87f54",
	Deps: []registry.EntryLike{ClosedInSubtopology, ClosureClosed, ClosureMinimal, SubsetClosure},
	Build: family.Card(IsTopology.Statement(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
			"t ⊆ s",
		},
		Conclusion: "closure(subtopology(T, s), t) = closure(T, t) ∩ s",
	}),
		"The closed sets of the subspace are the traces of the closed sets of T "+
			"(ClosedInSubtopology). The trace of the closure of t is one around t, so the "+
			"subspace closure lies in it (ClosureClosed, ClosureMinimal at the subspace); a "+
			"closed d of T whose trace is around t is around t, since t lies in s, so around "+
			"its closure (ClosureMinimal), and the trace of that closure lies in the trace of d."),
})}

// HausdorffSubtopology — a subspace of a Hausdorff space is Hausdorff:
// two distinct points of the subspace are points of the space, so
// disjoint open sets u and v hold them, and the traces u ∩ s and v ∩ s
// are disjoint open sets of the subspace holding them. No axiom enters.
var HausdorffSubtopology = hausdorffSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "HausdorffSubtopology",
	Key:  "prop_efddc4416179a51c",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"hausdorff(T)",
		},
		Conclusion: "hausdorff(subtopology(T, s))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], separated Fact) {
			// Hausdorff unfolded on the goal and on the hypothesis: two
			// distinct points, and disjoint open sets about each — of the
			// subspace in the goal, of the space in the hypothesis.
			a.Do(Unfold(HausdorffDef))
			a.Fix("x")
			a.Fix("y")
			distinct := a.Assume()
			points := a.Have(
				"x and y are points of the space lying in s, the points of the subspace",
				"x ∈ ⋃T ∧ x ∈ s ∧ y ∈ ⋃T ∧ y ∈ s",
				BySets(distinct, SubtopologySpace.At(T, s)))
			u, v, apart := a.Obtain2As[Set[A], Set[A]](
				"x and y are distinct points of the space, so disjoint open sets u and v hold them",
				"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅",
				By(separated, distinct, points))
			a.Take(a.TermAs[Set[A]]("u ∩ s"))
			a.Take(a.TermAs[Set[A]]("v ∩ s"))
			a.Show(
				"the traces u ∩ s and v ∩ s are open in the subspace, hold x and y, and are disjoint",
				BySets(TraceOpen.At(T, s, u), TraceOpen.At(T, s, v), points, apart))
		}),
})}
