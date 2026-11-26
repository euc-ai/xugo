// connected.go — connected sets: a family of them sharing a point unites
// to one, the closure of one is one, and one lies on one side of a set
// both open and closed; the connected component of a point, the union of
// the connected sets holding it — the largest of them, closed, and the
// same for every point it holds; connectedness of a subset of a
// subspace, which is its connectedness in the whole space; and locally
// connected spaces, exactly those whose open subspaces have open
// components.

package connected

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ConnectedUnions — connected sets sharing a point unite to a connected
// set. Two open sets covering the union and each meeting it hold the
// common point on one side; a member meeting the other side meets both,
// and its connectedness gives a point of it in both.
var ConnectedUnions = connectedUnionsThm{family.Add(registry.ProofEntry{
	Name: "ConnectedUnions",
	Key:  "prop_4b0f8477a39a1455",
	Reading: "No axiom. f = ∅ is vacuous twice over: ⋂∅ = 𝕌 is not empty, and ⋃∅ = ∅ is " +
		"connected. The common point is needed only to put one member across both open sets.",
	Build: family.Theorem(Statement{
		Binders: "∀T f:set(set(A)).",
		Hypotheses: []string{
			"∀s:set(A). s ∈ f ⇒ connected_in(T, s)",
			"¬(⋂f = ∅)",
		},
		Conclusion: "connected_in(T, ⋃f)",
	},
		func(a *Argument, T, f *Expr[Set[Set[A]]], each, common Fact) {
			_, holdsP := a.ObtainAs[A](
				"a point p every member holds",
				"∃p:A. ∀s:set(A). s ∈ f ⇒ p ∈ s",
				BySets(common))
			// each member lies in the space, and no two open sets split it
			members := a.Unfolded(each, ConnectedInDef)
			a.Do(Unfold(ConnectedInDef), SplitConj(
				Case(
					"the union lies in the space, as each member does",
					By(members, set_order.UnionsSubset)),
				Case(
					"two open sets covering the union and each meeting it share a point of it",
					Derive(func(b *Argument) {
						b.FixAs[Set[A]]("u")
						b.FixAs[Set[A]]("v")
						split := b.Assume() // u and v open, covering ⋃f, each meeting it
						parts := b.Conjuncts(
							split,
							"u is open",
							"v is open",
							"u and v cover the union",
							"u meets it",
							"v meets it")
						uOpen, vOpen, covered, uMeets, vMeets := parts[0], parts[1], parts[2], parts[3], parts[4]
						meetsBoth := b.Have(
							"a member meeting both u and v meets them at a common point, being connected",
							"∀s:set(A). s ∈ f ∧ ¬(s ∩ u = ∅) ∧ ¬(s ∩ v = ∅) ⇒ ¬(s ∩ u ∩ v = ∅)",
							Derive(func(c *Argument) {
								s := c.FixAs[Set[A]]("s")
								member := c.Assume() // s a member meeting u and v
								sCovered := c.Have(
									"s lies in the union, so u and v cover it",
									"s ⊆ u ∪ v",
									BySets(member, covered))
								c.Show(
									"so u and v, being open, cannot split s",
									By(members.At(s), uOpen, vOpen, sCovered, member))
							}))
						b.Show(
							"p lies in u or in v, and a member meeting the other of the two meets both",
							BySets(holdsP, meetsBoth, covered, uMeets, vMeets))
					})),
			))
		}),
})}

// ConnectedClosure — the closure of a connected set is connected: it is
// the set between s and its closure that is the closure itself.
var ConnectedClosure = connectedClosureThm{family.Add(registry.ProofEntry{
	Name: "ConnectedClosure",
	Key:  "prop_2e6e0f7c0868a7a4",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"connected_in(s)",
		},
		Conclusion: "connected_in(closure(s))",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			s *Expr[Set[A]],
			connected Fact,
		) {
			a.Show(
				"s lies in its closure, so the closure lies between s and the closure of s",
				By(
					ConnectedIntermediateClosure.Read(topology).At(s, a.TermAs[Set[A]]("closure(s)")),
					connected,
					topological_space.SubsetClosure,
					set_order.SubsetRefl))
		}),
})}

// ConnectedClopen — a connected set lies inside, or misses, any set both
// open and closed: t and its complement in the space are open, cover c and
// share no point, so c cannot meet both.
var ConnectedClopen = connectedClopenThm{family.Add(registry.ProofEntry{
	Name: "ConnectedClopen",
	Key:  "prop_dbe28bb99edeb123",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀c t:set(A).",
		Hypotheses: []string{
			"connected_in(T, c)",
			"t ∈ T",
			"closed_in(T, t)",
		},
		Conclusion: "c ⊆ t ∨ c ∩ t = ∅",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], c, t *Expr[Set[A]], connected, open, closed Fact) {
			parts := a.Conjuncts(
				a.Unfolded(connected, ConnectedInDef),
				"c lies in the space",
				"and no two open sets split it")
			inSpace, unsplit := parts[0], parts[1]
			complementOpen := a.Conjuncts(
				a.Unfolded(closed, topological_space.ClosedInDef),
				"t lies in the space",
				"and its complement there is open")[1]
			covered := a.Have(
				"t and its complement in the space cover c",
				"c ⊆ t ∪ (⋃T ∖ t)",
				BySets(inSpace))
			disjoint := a.Have(
				"and share no point of it",
				"c ∩ t ∩ (⋃T ∖ t) = ∅",
				BySets())
			missesOne := a.Have(
				"so c, being connected, misses one of the two",
				"c ∩ t = ∅ ∨ c ∩ (⋃T ∖ t) = ∅",
				By(unsplit.At(t, a.TermAs[Set[A]]("⋃T ∖ t")), open, complementOpen, covered, disjoint))
			a.Show(
				"missing the complement, c lies in t, as it lies in the space",
				BySets(missesOne, inSpace))
		}),
})}

// ComponentConnected — the component of a point is connected: it is the
// union of the connected sets holding x, which share x. When there are
// none the family is empty, its intersection is the whole type and still
// holds x, and its union is the empty set.
var ComponentConnected = componentConnectedThm{family.Add(registry.ProofEntry{
	Name: "ComponentConnected",
	Key:  "prop_300842930850a2e3",
	Build: family.Theorem("∀T:set(set(A)). ∀x:A. connected_in(T, connected_component(T, x))",
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A]) {
			a.Show(
				"the component unites connected sets that all hold x",
				Unfold(ConnectedComponentDef),
				BySets(ConnectedUnions.At(T, a.TermAs[Set[Set[A]]]("{s:set(A) | connected_in(T, s) ∧ x ∈ s}"))))
		}),
})}

// ComponentMaximal — a connected set holding x lies in x's component: it
// is one of the sets the component unites.
var ComponentMaximal = componentMaximalThm{family.Add(registry.ProofEntry{
	Name: "ComponentMaximal",
	Key:  "prop_3c729918e5c45b84",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A). ∀x:A.",
		Hypotheses: []string{
			"connected_in(T, s)",
			"x ∈ s",
		},
		Conclusion: "s ⊆ connected_component(T, x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], x *Expr[A], connected, holdsX Fact) {
			a.Show(
				"s is a connected set holding x, so a member of the family the component unites",
				Unfold(ConnectedComponentDef),
				By(connected, holdsX, set_order.MemberSubsetUnions))
		}),
})}

// ComponentEq — the component of a point of x's component is x's
// component: the components partition the space. x's component is a
// connected set holding y, so it lies in y's; then y's holds x, and being
// connected lies in x's.
var ComponentEq = componentEqThm{family.Add(registry.ProofEntry{
	Name: "ComponentEq",
	Key:  "prop_67e5a755e55f6f2",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀x y:A.",
		Hypotheses: []string{
			"y ∈ connected_component(T, x)",
		},
		Conclusion: "connected_component(T, y) = connected_component(T, x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], x, y *Expr[A], inComponent Fact) {
			componentX := a.TermAs[Set[A]]("connected_component(T, x)")
			componentY := a.TermAs[Set[A]]("connected_component(T, y)")
			widens := a.Have(
				"x's component is a connected set holding y, so it lies in y's",
				"connected_component(T, x) ⊆ connected_component(T, y)",
				By(ComponentMaximal.At(T, componentX, y), ComponentConnected.At(T, x), inComponent))
			holdsX := a.Have(
				"x lies in its own component, which is not empty",
				"x ∈ connected_component(T, x)",
				BySets(inComponent, ConnectedComponentDef))
			a.Show(
				"so y's component holds x, and being connected lies in x's",
				BySets(ComponentMaximal.At(T, componentY, x), ComponentConnected.At(T, y), holdsX, widens))
		}),
})}

// ComponentClosed — a component is closed. For x in the space the
// closure of x's component is a connected set holding x, so it lies in
// the component, which is then its own closure. For x outside the space
// the component is empty.
var ComponentClosed = componentClosedThm{family.Add(registry.ProofEntry{
	Name: "ComponentClosed",
	Key:  "prop_39c702acdd333395",
	Build: topological_space.IsTopology.Law("∀x:A. closed_in(connected_component(x))",
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], x *Expr[A]) {
			T := a.TermAs[Set[Set[A]]]("T")
			component := a.TermAs[Set[A]]("connected_component(x)")
			a.Cases(a.Term("x ∈ ⋃T"))
			a.When(
				"x is a point of the space: its component is its own closure",
				func(b *Argument, inSpace Fact) {
					closureConnected := b.Have(
						"the closure of the component is connected",
						"connected_in(closure(connected_component(x)))",
						By(ConnectedClosure.Read(topology).At(component), ComponentConnected.At(T, x)))
					inside := b.Have(
						"and holds x, so it lies in the component",
						"closure(connected_component(x)) ⊆ connected_component(x)",
						BySets(
							ComponentMaximal.At(T, b.TermAs[Set[A]]("closure(connected_component(x))"), x),
							closureConnected,
							ComponentSelfIff.At(T, x),
							inSpace,
							topological_space.SubsetClosure.At(T, component)))
					b.Show(
						"so the component, lying in the space and equal to its closure, is closed",
						BySets(
							topological_space.ClosedIffClosure.Read(topology).At(component),
							ComponentSubsetSpace.At(T, x),
							topological_space.SubsetClosure.At(T, component),
							inside))
				})
			a.Otherwise(
				"x is not a point of the space: its component is empty",
				func(b *Argument, outside Fact) {
					empty := b.Have(
						"the component of a point outside the space is empty",
						"connected_component(x) = ∅",
						By(ComponentEmptyIff.At(T, x), outside))
					b.Show(
						"and the empty set is closed",
						empty.Rw(),
						Cite(topological_space.EmptyClosed.Read(topology)))
				})
		}),
})}

// ConnectedInSubtopology — a subset k of s is connected in the subspace
// s exactly when it is connected in the whole space. The open sets of the
// subspace are the traces u ∩ s of the open sets u of T, and its points
// are the points of the space in s. Since k lies in s, cutting open sets
// down to s changes nothing k can see: two traces cover k, meet it, or
// share a point of it exactly when the open sets they are cut from do.
// So two open sets of T splitting k would split it through their traces,
// and two open sets of the subspace splitting k would split it through
// open sets of T they are traces of.
var ConnectedInSubtopology = connectedInSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "ConnectedInSubtopology",
	Key:  "prop_f900fb84cb766677",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s k:set(A).",
		Hypotheses: []string{
			"k ⊆ s",
		},
		Conclusion: "connected_in(subtopology(T, s), k) ⇔ connected_in(T, k)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, k *Expr[Set[A]], inside Fact) {
			a.Iff()
			a.Forward(
				"connected in the subspace: open sets of T splitting k would split it through their traces",
				func(b *Argument, connectedInSubspace Fact) {
					parts := b.Conjuncts(
						b.Unfolded(connectedInSubspace, ConnectedInDef),
						"k lies in the subspace",
						"and no two open sets of the subspace split it")
					inSubspace, unsplitInSubspace := parts[0], parts[1]
					b.Do(Unfold(ConnectedInDef), SplitConj(
						Case(
							"k lies in the space, whose part in s is the space of the subspace",
							BySets(inSubspace, topological_space.SubtopologySpace.At(T, s))),
						Case(
							"no two open sets of T split k",
							Derive(func(c *Argument) {
								u := c.FixAs[Set[A]]("u")
								v := c.FixAs[Set[A]]("v")
								split := c.Assume() // u and v open in T, covering k, each meeting it
								uTrace := c.Have(
									"u ∩ s is open in the subspace",
									"u ∩ s ∈ subtopology(T, s)",
									By(topological_space.TraceOpen.At(T, s, u), split))
								vTrace := c.Have(
									"and so is v ∩ s",
									"v ∩ s ∈ subtopology(T, s)",
									By(topological_space.TraceOpen.At(T, s, v), split))
								traceSplit := c.Have(
									"the traces still cover k and each still meets it, since k lies in s",
									"k ⊆ (u ∩ s) ∪ (v ∩ s) ∧ ¬(k ∩ (u ∩ s) = ∅) ∧ ¬(k ∩ (v ∩ s) = ∅)",
									BySets(inside, split))
								traceMeet := c.Have(
									"so the traces share a point of k",
									"¬(k ∩ (u ∩ s) ∩ (v ∩ s) = ∅)",
									By(
										unsplitInSubspace.At(c.TermAs[Set[A]]("u ∩ s"), c.TermAs[Set[A]]("v ∩ s")),
										uTrace,
										vTrace,
										traceSplit))
								c.Show(
									"and that point lies in u and in v",
									BySets(traceMeet))
							})),
					))
				})
			a.Backward(
				"connected in T: open sets of the subspace splitting k would split it through open sets of T",
				func(b *Argument, connected Fact) {
					parts := b.Conjuncts(
						b.Unfolded(connected, ConnectedInDef),
						"k lies in the space",
						"and no two open sets of T split it")
					inSpace, unsplit := parts[0], parts[1]
					b.Do(Unfold(ConnectedInDef), SplitConj(
						Case(
							"k lies in the space and in s, the space of the subspace",
							BySets(inside, inSpace, topological_space.SubtopologySpace.At(T, s))),
						Case(
							"no two open sets of the subspace split k",
							Derive(func(c *Argument) {
								c.FixAs[Set[A]]("u")
								c.FixAs[Set[A]]("v")
								split := c.Assume() // u and v open in the subspace, covering k, each meeting it
								p, uIsTrace := c.ObtainAs[Set[A]](
									"u is the trace of an open set p of T",
									"∃p:set(A). u = p ∩ s ∧ p ∈ T",
									Simp(Rev(topological_space.OpenInSubtopology)),
									By(split))
								q, vIsTrace := c.ObtainAs[Set[A]](
									"and v the trace of an open set q",
									"∃q:set(A). v = q ∩ s ∧ q ∈ T",
									Simp(Rev(topological_space.OpenInSubtopology)),
									By(split))
								sourceSplit := c.Have(
									"p and q cover k and each meets it, as they contain u and v",
									"k ⊆ p ∪ q ∧ ¬(k ∩ p = ∅) ∧ ¬(k ∩ q = ∅)",
									BySets(uIsTrace, vIsTrace, split))
								sourceMeet := c.Have(
									"so p and q share a point of k",
									"¬(k ∩ p ∩ q = ∅)",
									By(unsplit.At(p, q), uIsTrace, vIsTrace, sourceSplit))
								c.Show(
									"and that point, lying in s, lies in the traces u and v",
									BySets(sourceMeet, inside, uIsTrace, vIsTrace))
							})),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Small connected sets, and connectedness of the space
// ---------------------------------------------------------------------------

// EmptyConnected — the empty set is connected: it lies in every space,
// and no open set meets it, so no two open sets split it.
var EmptyConnected = emptyConnectedThm{family.Add(registry.ProofEntry{
	Name: "EmptyConnected",
	Key:  "prop_289051b4ef5e7867",
	Build: family.Theorem("∀T:set(set(A)). connected_in(T, ∅)",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Show(
				"the empty set lies in the space, and no open set meets it",
				Unfold(ConnectedInDef),
				BySets())
		}),
})}

// SingletonConnected — a point of the space is a connected set: two open
// sets each meeting {x} both hold x.
var SingletonConnected = singletonConnectedThm{family.Add(registry.ProofEntry{
	Name: "SingletonConnected",
	Key:  "prop_ab41218512fd82a5",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "connected_in(T, {x})",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A], inSpace Fact) {
			a.Show(
				"{x} lies in the space, and two open sets each meeting it both hold x",
				Unfold(ConnectedInDef),
				BySets(inSpace))
		}),
})}

// ConnectedUnion — two connected sets sharing a point unite to a
// connected set: the pair {s, t} is a family of connected sets with
// intersection s ∩ t and union s ∪ t.
var ConnectedUnion = connectedUnionThm{family.Add(registry.ProofEntry{
	Name: "ConnectedUnion",
	Key:  "prop_c695d24ddb3f0578",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s t:set(A).",
		Hypotheses: []string{
			"connected_in(T, s)",
			"connected_in(T, t)",
			"¬(s ∩ t = ∅)",
		},
		Conclusion: "connected_in(T, s ∪ t)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, t *Expr[Set[A]], sConnected, tConnected, meet Fact) {
			both := a.Have(
				"both members of the pair {s, t} are connected",
				"∀r:set(A). r ∈ {s, t} ⇒ connected_in(T, r)",
				Simp(Fwd(set_basic.ForallInInsert), Fwd(set_basic.NotInEmpty)),
				By(sConnected, tConnected))
			common := a.Have(
				"and they share a point, their intersection being s ∩ t",
				"¬(⋂{s, t} = ∅)",
				By(meet, set_algebra.IntersPair))
			a.Show(
				"so the union of the pair, which is s ∪ t, is connected",
				Simp(Rev(set_algebra.UnionsPair)),
				By(ConnectedUnions, both, common))
		}),
})}

// ConnectedIntermediateClosure — a set between a connected set and its
// closure is connected. An open set meeting t meets s, a point of t
// being a point of the closure of s; so two open sets covering t and
// each meeting it cover s and each meet it, and the point of s they
// share is a point of t.
var ConnectedIntermediateClosure = connectedIntermediateClosureThm{family.Add(registry.ProofEntry{
	Name: "ConnectedIntermediateClosure",
	Key:  "prop_699bd4a12429c877",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"connected_in(s)",
			"s ⊆ t",
			"t ⊆ closure(s)",
		},
		Conclusion: "connected_in(t)",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			s, t *Expr[Set[A]],
			connected, sInT, tInClosure Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(connected, ConnectedInDef),
				"s lies in the space",
				"and no two open sets split it")
			inSpace, unsplit := parts[0], parts[1]
			nearS := a.Have(
				"an open set meeting t meets s, t lying in the closure of s",
				"∀w:set(A). w ∈ T ∧ ¬(t ∩ w = ∅) ⇒ ¬(s ∩ w = ∅)",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("w")
					meets := b.Assume() // w open and meeting t
					x, xIn := b.ObtainAs[A](
						"a point x of t in w",
						"∃x:A. x ∈ t ∧ x ∈ w",
						BySets(meets))
					b.Show(
						"x lies in the closure of s and in the open set w, so w meets s",
						BySets(topological_space.ClosurePointwise.Read(topology).At(s, x), inSpace, tInClosure, xIn, meets))
				}))
			a.Do(Unfold(ConnectedInDef), SplitConj(
				Case(
					"t lies in the space, as every point of the closure of s does",
					BySets(topological_space.ClosurePointwise.Read(topology), inSpace, tInClosure)),
				Case(
					"two open sets covering t and each meeting it share a point of it",
					Derive(func(b *Argument) {
						u := b.FixAs[Set[A]]("u")
						v := b.FixAs[Set[A]]("v")
						split := b.Assume() // u and v open, covering t, each meeting it
						b.Show(
							"they cover s and each meet it, so share a point of s, which lies in t",
							BySets(unsplit.At(u, v), nearS, sInT, split))
					})),
			))
		}),
})}

// ConnectedIffNoClopen — a space is connected exactly when no set both
// open and closed lies strictly between the empty set and the space.
// Forward, the connected space lies inside or misses such a set, which
// lies in it. Backward, two open sets covering the space, each meeting it
// and sharing no point of it, are each other's complements there, so the
// first is closed as well as open, yet neither empty nor the space.
var ConnectedIffNoClopen = connectedIffNoClopenThm{family.Add(registry.ProofEntry{
	Name: "ConnectedIffNoClopen",
	Key:  "prop_8ce502414c365860",
	Build: family.Theorem("∀T:set(set(A)). "+
		"    connected_in(T, ⋃T) ⇔ ∀t:set(A). t ∈ T ∧ closed_in(T, t) ⇒ t = ∅ ∨ t = ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Iff()
			a.Forward(
				"a connected space lies inside or misses each set both open and closed",
				func(b *Argument, connected Fact) {
					t := b.FixAs[Set[A]]("t")
					clopen := b.Assume() // t open and closed
					sides := b.Have(
						"the space lies in t or misses it",
						"⋃T ⊆ t ∨ ⋃T ∩ t = ∅",
						By(ConnectedClopen.At(T, b.TermAs[Set[A]]("⋃T"), t), connected, clopen))
					b.Show(
						"and t, being open, lies in the space",
						BySets(sides, clopen))
				})
			a.Backward(
				"with no proper nonempty set both open and closed, no two open sets split the space",
				func(b *Argument, noClopen Fact) {
					b.Do(Unfold(ConnectedInDef), SplitConj(
						Case(
							"the space lies in itself",
							BySets()),
						Case(
							"two open sets covering the space and each meeting it share a point of it",
							Derive(func(c *Argument) {
								u := c.FixAs[Set[A]]("u")
								c.FixAs[Set[A]]("v")
								split := c.Assume() // u and v open, covering the space, each meeting it
								parts := c.Conjuncts(
									split,
									"u is open",
									"v is open",
									"u and v cover the space",
									"u meets the space",
									"v meets the space")
								uOpen, vOpen, covered, uMeets, vMeets := parts[0], parts[1], parts[2], parts[3], parts[4]
								disjoint := c.SupposeNot() // u and v share no point of the space
								complement := c.Have(
									"then v is the complement of u in the space",
									"⋃T ∖ u = v",
									BySets(disjoint, covered, vOpen))
								uClosed := c.Have(
									"so u, an open set of the space, is closed as well",
									"closed_in(T, u)",
									Unfold(topological_space.ClosedInDef),
									By(complement, uOpen, vOpen, set_order.MemberSubsetUnions))
								trivial := c.Have(
									"so u is empty or the whole space",
									"u = ∅ ∨ u = ⋃T",
									By(noClopen.At(u), uOpen, uClosed))
								c.Show(
									"u meets the space, so it is the space, where v meets it",
									BySets(trivial, disjoint, uMeets, vMeets))
							})),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The components of a space
// ---------------------------------------------------------------------------

// ComponentSubsetSpace — a component lies in the space: it is a union of
// connected sets, and a connected set lies in the space.
var ComponentSubsetSpace = componentSubsetSpaceThm{family.Add(registry.ProofEntry{
	Name: "ComponentSubsetSpace",
	Key:  "prop_dc401201453beba2",
	Build: family.Theorem("∀T:set(set(A)). ∀x:A. connected_component(T, x) ⊆ ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A]) {
			a.Show(
				"the component is a union of connected sets, each of which lies in the space",
				Unfold(ConnectedComponentDef),
				By(ConnectedInDef, set_order.UnionsSubset))
		}),
})}

// ComponentSelfIff — a point lies in its own component exactly when it
// is a point of the space: the component lies in the space, and the
// singleton of a point of the space is a connected set holding it.
var ComponentSelfIff = componentSelfIffThm{family.Add(registry.ProofEntry{
	Name: "ComponentSelfIff",
	Key:  "prop_20525d2af6c18018",
	Build: family.Theorem("∀T:set(set(A)). ∀x:A. x ∈ connected_component(T, x) ⇔ x ∈ ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A]) {
			a.Iff()
			a.Forward(
				"a point of its component is a point of the space",
				func(b *Argument, inComponent Fact) {
					b.Show(
						"the component lies in the space",
						BySets(inComponent, ComponentSubsetSpace.At(T, x)))
				})
			a.Backward(
				"a point of the space lies in its component",
				func(b *Argument, inSpace Fact) {
					b.Show(
						"{x} is one of the connected sets holding x that the component unites",
						Unfold(ConnectedComponentDef),
						BySets(inSpace, SingletonConnected.At(T, x)))
				})
		}),
})}

// ComponentEmptyIff — a point's component is empty exactly when the point
// is not a point of the space: a point of the component puts the point
// in a connected set, hence in its own component, which a point outside
// the space is not in.
var ComponentEmptyIff = componentEmptyIffThm{family.Add(registry.ProofEntry{
	Name: "ComponentEmptyIff",
	Key:  "prop_5a2d25e69366b715",
	Build: family.Theorem("∀T:set(set(A)). ∀x:A. connected_component(T, x) = ∅ ⇔ x ∉ ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]], x *Expr[A]) {
			a.Show(
				"a point lies in its own component exactly when it lies "+
					"in the space, and a component with a point holds its own",
				BySets(ComponentSelfIff.At(T, x), ConnectedComponentDef))
		}),
})}

// ComponentsCover — the components of the points of the space cover it.
var ComponentsCover = componentsCoverThm{family.Add(registry.ProofEntry{
	Name: "ComponentsCover",
	Key:  "prop_db1aa50c1a3bab41",
	Build: family.Theorem("∀T:set(set(A)). ⋃image(λx:A. connected_component(T, x), ⋃T) = ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Do(Simp(Fwd(ComponentsQuotient)))
			equiv := a.Have(
				"component membership is an equivalence on the space",
				"equivalence_on(⋃T, λx:A. λy:A. y ∈ connected_component(T, x))",
				Cite(ComponentEquivalence))
			a.Show(
				"the classes of the equivalence cover its carrier",
				Cite(equivalence.QuotientOnCovers.Read(equiv)))
		}),
})}

// ComponentsDisjoint — two components are equal or disjoint: a point
// common to the two has each of them as its own component.
var ComponentsDisjoint = componentsDisjointThm{family.Add(registry.ProofEntry{
	Name: "ComponentsDisjoint",
	Key:  "prop_2196025d8933f1b8",
	Build: family.Theorem("∀T:set(set(A)). ∀x y:A. "+
		"    connected_component(T, x) = connected_component(T, y) ∨ "+
		"    connected_component(T, x) ∩ connected_component(T, y) = ∅",
		func(a *Argument, T *Expr[Set[Set[A]]], x, y *Expr[A]) {
			a.Show(
				"a point common to the two components has each of them as its own component",
				BySets(ComponentEq))
		}),
})}

// ConnectedIffOneComponent — a space is connected exactly when the
// component of each of its points is the whole space. Forward, the space
// is a connected set holding the point, so it lies in the point's
// component, which lies in the space. Backward, an empty space is
// connected, and a space with a point is that point's component.
var ConnectedIffOneComponent = connectedIffOneComponentThm{family.Add(registry.ProofEntry{
	Name: "ConnectedIffOneComponent",
	Key:  "prop_cf61e3a7412736e2",
	Build: family.Theorem("∀T:set(set(A)). "+
		"    connected_in(T, ⋃T) ⇔ ∀x:A. x ∈ ⋃T ⇒ connected_component(T, x) = ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Iff()
			a.Forward(
				"in a connected space each point's component is the whole space",
				func(b *Argument, connected Fact) {
					x := b.FixAs[A]("x")
					inSpace := b.Assume() // x a point of the space
					b.Show(
						"the space is a connected set holding x, so it lies in x's component, which lies in the space",
						By(
							ComponentMaximal.At(T, b.TermAs[Set[A]]("⋃T"), x),
							ComponentSubsetSpace.At(T, x),
							set_order.SubsetAntisym,
							connected,
							inSpace))
				})
			a.Backward(
				"a space that is the component of each of its points is connected",
				func(b *Argument, oneComponent Fact) {
					b.Cases(b.Term("⋃T = ∅"))
					b.When(
						"an empty space is connected",
						func(c *Argument, empty Fact) {
							c.Show(
								"the empty set is connected",
								empty.Rw(),
								Cite(EmptyConnected))
						})
					b.Otherwise(
						"a space with a point is that point's component",
						func(c *Argument, nonEmpty Fact) {
							x, inSpace := c.ObtainAs[A](
								"a point x of the space",
								"∃x:A. x ∈ ⋃T",
								By(nonEmpty, set_basic.MemberNotEmpty))
							c.Show(
								"the space is x's component, which is connected",
								By(Normalized, oneComponent.At(x), inSpace, ComponentConnected.At(T, x)))
						})
				})
		}),
})}

// FiniteComponentsOpen — where a space has finitely many components,
// each is open. For x in the space, the components cover the space and
// each is x's or misses it, so the complement of x's component in the
// space is the union of the others: finitely many closed sets, whose
// union is closed. A set in the space with a closed complement there is
// open. For x outside the space the component is empty.
var FiniteComponentsOpen = finiteComponentsOpenThm{family.Add(registry.ProofEntry{
	Name: "FiniteComponentsOpen",
	Key:  "prop_ba6ccfb511eba3f7",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"finite(image(λy:A. connected_component(T, y), ⋃T))",
		},
		Conclusion: "connected_component(x) ∈ T",
	},
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], x *Expr[A], finitelyMany Fact) {
			T := a.TermAs[Set[Set[A]]]("T")
			component := a.TermAs[Set[A]]("connected_component(x)")
			a.Cases(a.Term("x ∈ ⋃T"))
			a.When(
				"x is a point of the space: the other components make up the rest of the space",
				func(b *Argument, inSpace Fact) {
					closedUnions := b.Have(
						"a finite union of closed sets is closed",
						"∀f:set(set(A)). finite(f) ∧ (∀c:set(A). c ∈ f ⇒ closed_in(c)) ⇒ closed_in(⋃f)",
						ByInduction(finite_set.FiniteInduct,
							Case(
								"the empty family unites to the empty set, which is closed",
								By(set_algebra.UnionsEmpty, topological_space.EmptyClosed.Read(topology))),
							Case(
								"one more closed set joins the closed union of those already there",
								Derive(func(e *Argument) {
									added := e.FixAs[Set[A]]("d")
									e.FixAs[Set[Set[A]]]("g")
									carried := e.Assume() // the union of g is closed when its members are
									members := e.Assume() // every member of insert(d, g) is closed
									e.Show(
										"the union of insert(d, g) is d ∪ ⋃g, both closed",
										Simp(Fwd(set_algebra.UnionsInsert)),
										By(
											topological_space.UnionClosed.Read(topology).At(added, e.TermAs[Set[A]]("⋃g")),
											carried,
											members,
											set_basic.InInsert))
								}))))
					_, familyDef := b.LetAs[Set[Set[A]]]("F", "image(λy:A. connected_component(T, y), ⋃T)")
					cover := b.Have(
						"the components cover the space",
						"⋃F = ⋃T",
						By(Normalized, familyDef, ComponentsCover.At(T)))
					members := b.Have(
						"each component is closed, and is x's or misses it",
						"∀c:set(A). c ∈ F ⇒ closed_in(c) ∧ (c = connected_component(x) ∨ c ∩ connected_component(x) = ∅)",
						Derive(func(c *Argument) {
							c.FixAs[Set[A]]("c")
							isComponent := c.Assume() // c a component
							y, yComponent := c.ObtainAs[A](
								"c is the component of a point y of the space",
								"∃y:A. y ∈ ⋃T ∧ c = connected_component(y)",
								BySets(familyDef, isComponent))
							c.Show(
								"the component of y is closed, and is x's or misses it",
								By(Normalized, yComponent, ComponentClosed.Read(topology).At(y), ComponentsDisjoint.At(T, y, x)))
						}))
					outside := b.Have(
						"a point of the space outside x's component lies in another component",
						"⋃T ∖ connected_component(x) ⊆ ⋃delete(F, connected_component(x))",
						BySets(cover))
					inside := b.Have(
						"and a point of another component lies in the space, outside x's",
						"⋃delete(F, connected_component(x)) ⊆ ⋃T ∖ connected_component(x)",
						BySets(members, cover))
					complement := b.Have(
						"so the complement of x's component in the space is the union of the others",
						"⋃T ∖ connected_component(x) = ⋃delete(F, connected_component(x))",
						By(outside, inside, set_order.SubsetAntisym))
					othersClosed := b.Have(
						"the others are finitely many closed sets, so their union is closed",
						"closed_in(⋃delete(F, connected_component(x)))",
						BySets(
							closedUnions.At(b.TermAs[Set[Set[A]]]("delete(F, connected_component(x))")),
							finitelyMany,
							members,
							finite_set.FiniteDelete))
					b.Show(
						"x's component lies in the space with a closed complement there, so it is open",
						By(
							Normalized,
							topological_space.OpenClosedComplement.At(T, component),
							ComponentSubsetSpace.At(T, x),
							complement,
							othersClosed))
				})
			a.Otherwise(
				"x is not a point of the space: its component is empty, and open",
				func(b *Argument, outside Fact) {
					empty := b.Have(
						"the component of a point outside the space is empty",
						"connected_component(x) = ∅",
						By(ComponentEmptyIff.At(T, x), outside))
					b.Show(
						"and the empty set is open",
						empty.Rw(),
						Cite(topological_space.EmptyOpen.Read(topology)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Locally connected spaces
// ---------------------------------------------------------------------------

// LocallyConnectedComponentOpen — in a locally connected space every
// component is open. A point y of x's component is a point of the space,
// and the space is open, so some connected open v holds y; v lies in y's
// component, which is x's. So each point of the component lies in an
// open set inside it, and the component is open by the pointwise
// criterion.
var LocallyConnectedComponentOpen = locallyConnectedComponentOpenThm{family.Add(registry.ProofEntry{
	Name: "LocallyConnectedComponentOpen",
	Key:  "prop_f2c92a036e08bd7a",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"locally_connected_space(T)",
		},
		Conclusion: "connected_component(x) ∈ T",
	},
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], x *Expr[A], locally Fact) {
			T := a.TermAs[Set[Set[A]]]("T")
			neighbourhoods := a.Unfolded(locally, LocallyConnectedSpaceDef)
			near := a.Have(
				"each point of the component lies in an open set inside it",
				"∀y:A. y ∈ connected_component(x) ⇒ ∃v:set(A). v ∈ T ∧ v ⊆ connected_component(x) ∧ y ∈ v",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					inComponent := b.Assume()
					v, around := b.ObtainAs[Set[A]](
						"y is a point of the open space, so some connected open v holds y",
						"∃v:set(A). v ∈ T ∧ connected_in(v) ∧ y ∈ v ∧ v ⊆ ⋃T",
						BySets(
							neighbourhoods.At(b.TermAs[Set[A]]("⋃T"), y),
							topological_space.SpaceOpen.Read(topology),
							inComponent,
							ComponentSubsetSpace.At(T, x)))
					b.Take(v)
					b.Show(
						"v is a connected set holding y, so it lies in y's component, which is x's",
						By(Normalized, around, inComponent, ComponentMaximal.At(T, v, y), ComponentEq.At(T, x, y)))
				}))
			a.Show(
				"so the component is open, by the pointwise criterion",
				By(topological_space.OpenPointwise.Read(topology), near))
		}),
})}

// LocallyConnectedOpenSubtopology — an open subspace of a locally
// connected space is locally connected. An open set w of the subspace u is
// an open set of T inside u, so a point of w has a connected open v of T
// about it inside w. Lying in u, v is open in the subspace and connected
// there.
var LocallyConnectedOpenSubtopology = locallyConnectedOpenSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "LocallyConnectedOpenSubtopology",
	Key:  "prop_ba4939f940f91f7a",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀u:set(A).",
		Hypotheses: []string{
			"locally_connected_space(T)",
			"u ∈ T",
		},
		Conclusion: "locally_connected_space(subtopology(T, u))",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			u *Expr[Set[A]],
			locally, open Fact,
		) {
			T := a.TermAs[Set[Set[A]]]("T")
			uOpen := a.MemberOf[on.T](u, open)
			neighbourhoods := a.Unfolded(locally, LocallyConnectedSpaceDef)
			a.Do(Unfold(LocallyConnectedSpaceDef))
			w := a.FixAs[Set[A]]("w")
			y := a.FixAs[A]("y")
			point := a.Assume() // w open in the subspace, y ∈ w
			wOpen := a.Have(
				"an open set of the open subspace is an open set of T inside u",
				"w ∈ T ∧ w ⊆ u",
				By(point, topological_space.OpenInOpenSubtopology.Read(topology).At(uOpen, w)))
			v, around := a.ObtainAs[Set[A]](
				"so some connected open v of T holds y inside w",
				"∃v:set(A). v ∈ T ∧ connected_in(v) ∧ y ∈ v ∧ v ⊆ w",
				By(neighbourhoods.At(w, y), wOpen, point))
			a.Take(v)
			a.Show(
				"v lies in u, so it is open in the subspace and connected there",
				By(
					around,
					wOpen,
					set_order.SubsetTrans.At(v, w, u),
					topological_space.OpenInOpenSubtopology.Read(topology).At(uOpen, v),
					ConnectedInSubtopology.At(T, u, v)))
		}),
})}

// LocallyConnectedIffComponentsOpen — a space is locally connected
// exactly when the components of its open subspaces are open. Forward, an
// open subspace is a topology and locally connected, so its components are
// open in it, and an open set of an open subspace is open in T. Backward,
// for x in an open u, x's component in the subspace u is open by
// hypothesis; it holds x, a point of the subspace, and lies in u, where
// the subspace's points lie; and connected in the subspace, it is
// connected in T. So it is a connected open neighbourhood of x inside u.
var LocallyConnectedIffComponentsOpen = locallyConnectedIffComponentsOpenThm{family.Add(registry.ProofEntry{
	Name: "LocallyConnectedIffComponentsOpen",
	Key:  "prop_c06faa4ddf2ce317",
	Build: topological_space.IsTopology.Law(
		"locally_connected_space(T) ⇔ "+
			"∀u:set(A). ∀x:A. u ∈ T ⇒ connected_component(subtopology(T, u), x) ∈ T",
		func(a *Argument, topology topological_space.IsTopologyFact[on.T]) {
			T := a.TermAs[Set[Set[A]]]("T")
			a.Iff()
			a.Forward(
				"the components of an open subspace of a locally connected space are open",
				func(b *Argument, locally Fact) {
					u := b.FixAs[Set[A]]("u")
					x := b.FixAs[A]("x")
					uOpen := b.MemberOf[on.T](u, b.Assume())
					component := b.TermAs[Set[A]]("connected_component(subtopology(T, u), x)")
					subspace := b.Have(
						"the subspace u is a topology",
						"is_topology(subtopology(T, u))",
						By(topological_space.SubtopologyTopology.Read(topology).At(u)))
					openThere := b.Have(
						"the subspace u is locally connected, so x's component in it is open in it",
						"connected_component(subtopology(T, u), x) ∈ subtopology(T, u)",
						By(
							LocallyConnectedComponentOpen.Read(subspace).At(x),
							LocallyConnectedOpenSubtopology.Read(topology).At(uOpen),
							locally))
					b.Show(
						"an open set of an open subspace is open in T",
						By(openThere, topological_space.OpenInOpenSubtopology.Read(topology).At(uOpen, component)))
				})
			a.Backward(
				"x's component in an open u about x is a connected open neighbourhood of x inside u",
				func(b *Argument, componentsOpen Fact) {
					b.Do(Unfold(LocallyConnectedSpaceDef))
					u := b.FixAs[Set[A]]("u")
					x := b.FixAs[A]("x")
					point := b.Assume() // u ∈ T, x ∈ u
					subspace := b.TermAs[Set[Set[A]]]("subtopology(T, u)")
					component := b.TermAs[Set[A]]("connected_component(subtopology(T, u), x)")
					holdsX := b.Have(
						"x is a point of the subspace, so it lies in its component there",
						"x ∈ connected_component(subtopology(T, u), x)",
						BySets(point, ComponentSelfIff.At(subspace, x), topological_space.SubtopologySpace.At(T, u)))
					b.Take(component)
					b.Show(
						"the component is open by hypothesis, lies in the subspace's "+
							"points and so in u, and is connected in the subspace, so in T",
						BySets(
							componentsOpen.At(u, x),
							point,
							holdsX,
							ComponentSubsetSpace.At(subspace, x),
							topological_space.SubtopologySpace.At(T, u),
							ComponentConnected.At(subspace, x),
							ConnectedInSubtopology.At(T, u, component)))
				})
		}),
})}
