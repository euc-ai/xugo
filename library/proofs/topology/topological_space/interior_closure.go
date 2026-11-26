// interior_closure.go — the largest open set inside a set and the
// smallest closed set around one: what each is by its definition
// alone, and what the axioms add.

package topological_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Interior
// ---------------------------------------------------------------------------

// InteriorSubset — the interior of s lies inside s: it is a union of
// sets inside s. No axiom enters, so the family is spelled.
var InteriorSubset = interiorSubsetThm{family.Add(registry.ProofEntry{
	Name: "InteriorSubset",
	Key:  "prop_ebff82ead7ff3396",
	Build: family.Theorem("∀T:set(set(A)). ∀s:set(A). interior(T, s) ⊆ s",
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]]) {
			a.Show(
				"each open set inside s lies inside s, so their union does",
				Unfold(InteriorDef),
				BySets())
		}),
})}

// InteriorMaximal — an open set inside s lies inside the interior of s:
// it is one of the sets the interior unites.
var InteriorMaximal = interiorMaximalThm{family.Add(registry.ProofEntry{
	Name: "InteriorMaximal",
	Key:  "prop_80ebc803b380bbce",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s u:set(A).",
		Hypotheses: []string{
			"u ∈ T",
			"u ⊆ s",
		},
		Conclusion: "u ⊆ interior(T, s)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, u *Expr[Set[A]], _ Fact) {
			// Unfolding the interior reads the assumption as its two clauses.
			a.Do(Unfold(InteriorDef))
			open := a.Hyp("u ∈ T")
			inside := a.Hyp("u ⊆ s")
			member := a.Have(
				"u is one of the open sets inside s",
				"u ∈ {v:set(A) | v ∈ T ∧ v ⊆ s}",
				BySets(open, inside))
			a.Show(
				"and a member of a family lies inside its union",
				BySets(member))
		}),
})}

// InteriorOfOpen — an open set is its own interior: the interior lies
// inside it, and it lies inside its interior, being open and inside
// itself.
var InteriorOfOpen = interiorOfOpenThm{family.Add(registry.ProofEntry{
	Name: "InteriorOfOpen",
	Key:  "prop_3d689bdf00eddd65",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀u:set(A).",
		Hypotheses: []string{
			"u ∈ T",
		},
		Conclusion: "interior(T, u) = u",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], u *Expr[Set[A]], open Fact) {
			a.Show(
				"the two inclusions, the second because u is open and inside itself",
				By(
					set_order.SubsetAntisym,
					At(InteriorSubset, T, u),
					At(InteriorMaximal, T, u, u),
					open,
					At(set_order.SubsetRefl, u)))
		}),
})}

// InteriorOpen — the interior of any set is open, which is what makes
// it the largest OPEN set inside s: it is the union of the open sets
// inside s, and those form a subfamily of T, whose union the union
// axiom makes open.
var InteriorOpen = interiorOpenThm{family.Add(registry.ProofEntry{
	Name: "InteriorOpen",
	Key:  "prop_1086745d77b7f331",
	Build: IsTopology.Law("∀s:set(A). interior(s) ∈ T",
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]]) {
			a.Do(Unfold(InteriorDef))
			subfamily := a.Have(
				"the open sets inside s form a subfamily of T",
				"{u:set(A) | u ∈ T ∧ u ⊆ s} ⊆ T",
				BySets())
			a.Show(
				"so their union is open, by the union axiom",
				By(UnionsOpen, subfamily, topology))
		}),
})}

// InteriorPointwise — a point lies in the interior of s exactly when
// some open set inside s holds it: the interior's definition read at a
// point, its conjuncts in the definition's own order (the membership
// condition, then the point).
var InteriorPointwise = interiorPointwiseThm{family.Add(registry.ProofEntry{
	Name: "InteriorPointwise",
	Key:  "prop_befb3eaba9357a06",
	Build: family.Theorem("∀T:set(set(A)). ∀s:set(A). ∀x:A. "+
		"    x ∈ interior(T, s) ⇔ ∃u:set(A). u ∈ T ∧ u ⊆ s ∧ x ∈ u",
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], x *Expr[A]) {
			a.Show(
				"a point of a union of open sets inside s is a point of one of them",
				Unfold(InteriorDef),
				BySets())
		}),
})}

// ---------------------------------------------------------------------------
// Closure
// ---------------------------------------------------------------------------

// SubsetClosure — a set lies inside its closure: every closed set
// around it does contain it, so their intersection does.
var SubsetClosure = subsetClosureThm{family.Add(registry.ProofEntry{
	Name: "SubsetClosure",
	Key:  "prop_d8d44965af42d69",
	Build: family.Theorem("∀T:set(set(A)). ∀s:set(A). s ⊆ closure(T, s)",
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]]) {
			a.Show(
				"s lies inside each closed set around it, so inside their intersection",
				Unfold(ClosureDef),
				BySets())
		}),
})}

// ClosureMinimal — a closed set around s contains the closure of s: it
// is one of the sets the closure intersects.
var ClosureMinimal = closureMinimalThm{family.Add(registry.ProofEntry{
	Name: "ClosureMinimal",
	Key:  "prop_eb5d0b0aa73d323e",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s c:set(A).",
		Hypotheses: []string{
			"closed_in(T, c)",
			"s ⊆ c",
		},
		Conclusion: "closure(T, s) ⊆ c",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, c *Expr[Set[A]], _ Fact) {
			// Unfolding the closure reads the assumption as its two clauses.
			a.Do(Unfold(ClosureDef))
			closed := a.Hyp("closed_in(T, c)")
			around := a.Hyp("s ⊆ c")
			member := a.Have(
				"c is one of the closed sets around s",
				"c ∈ {d:set(A) | closed_in(T, d) ∧ s ⊆ d}",
				BySets(closed, around))
			a.Show(
				"and the intersection of a family lies inside each member",
				By(member, set_order.IntersSubsetStrong, At(set_order.SubsetRefl, c)))
		}),
})}

// ClosureOfClosed — a closed set is its own closure: it lies inside its
// closure, and its closure lies inside it, being closed and around
// itself.
var ClosureOfClosed = closureOfClosedThm{family.Add(registry.ProofEntry{
	Name: "ClosureOfClosed",
	Key:  "prop_7083dc103d159c26",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀c:set(A).",
		Hypotheses: []string{
			"closed_in(T, c)",
		},
		Conclusion: "closure(T, c) = c",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], c *Expr[Set[A]], closed Fact) {
			a.Show(
				"the two inclusions, the first because c is closed and around itself",
				By(
					set_order.SubsetAntisym,
					At(ClosureMinimal, T, c, c),
					closed,
					At(set_order.SubsetRefl, c),
					At(SubsetClosure, T, c)))
		}),
})}

// ClosureClosed — the closure of a set inside the space is closed, which
// is what makes it the smallest CLOSED set around s: it is the
// intersection of the closed sets around s, and a non-empty family of
// closed sets meets in a closed set. The family is non-empty because the
// space itself is a closed set around s, and that is where the premise
// s ⊆ ⋃T enters: for s outside the space no closed set contains it, the
// family is empty, and its intersection is the whole type, which is not
// closed.
var ClosureClosed = closureClosedThm{family.Add(registry.ProofEntry{
	Name: "ClosureClosed",
	Key:  "prop_f078fe0105d60308",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "closed_in(closure(s))",
	},
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]], inSpace Fact) {
			a.Do(Unfold(ClosureDef))
			spaceAround := a.Have(
				"the space is closed and contains s, so it is one of the closed sets around s",
				"⋃T ∈ {c:set(A) | closed_in(c) ∧ s ⊆ c}",
				BySets(inSpace, SpaceClosed.Read(topology)))
			nonEmpty := a.Have(
				"hence the family of closed sets around s is non-empty",
				"¬({c:set(A) | closed_in(c) ∧ s ⊆ c} = ∅)",
				BySets(spaceAround))
			members := a.Have(
				"and every member of the family is closed",
				"∀c:set(A). c ∈ {d:set(A) | closed_in(d) ∧ s ⊆ d} ⇒ closed_in(c)",
				BySets())
			a.Show(
				"so the family meets in a closed set",
				By(IntersClosed, nonEmpty, members, topology))
		}),
})}

// ClosurePointwise — the closure read at a point: a point of the space
// lies in the closure of s exactly when every open neighbourhood of it
// meets s. Both directions pass through complements in the space: an
// open set missing s leaves a closed set around s, which then contains
// the closure — as the space itself does, s lying in it — and a closed
// set around s missing the point leaves an open neighbourhood of it that
// misses s.
var ClosurePointwise = closurePointwiseThm{family.Add(registry.ProofEntry{
	Name: "ClosurePointwise",
	Key:  "prop_9f1fc6b4f65c0132",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A). ∀x:A.",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "x ∈ closure(s) ⇔ x ∈ ⋃T ∧ (∀u:set(A). u ∈ T ∧ x ∈ u ⇒ ¬(u ∩ s = ∅))",
	},
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]], x *Expr[A], inSpace Fact) {
			a.Iff()

			a.Forward(
				"a point of the closure lies in every closed set around s: "+
					"in the space, and in the complement of any open set missing s",
				func(b *Argument, inClosure Fact) {
					b.Do(SplitConj(
						Case(
							"x lies in the space, as the closure does",
							BySets(inClosure, ClosureSubsetSpace.Read(topology).At(s), inSpace)),
						Case(
							"every open set holding x meets s",
							Derive(func(d *Argument) {
								d.Fix()
								neighbourhood := d.Assume()
								misses := d.SupposeNot()
								complementClosed := d.Have(
									"the complement of the open set u in the space is closed",
									"closed_in(⋃T ∖ u)",
									By(OpenClosedComplement, neighbourhood))
								around := d.Have(
									"and it contains s, which lies in the space and misses u",
									"s ⊆ ⋃T ∖ u",
									BySets(misses, inSpace))
								inside := d.Have(
									"so it contains the closure of s",
									"closure(s) ⊆ ⋃T ∖ u",
									By(ClosureMinimal, complementClosed, around))
								d.Show(
									"so x, a point of the closure, lies outside u, which holds it",
									BySets(inClosure, inside, neighbourhood))
							})),
					))
				})

			a.Backward(
				"a point of the space whose every open neighbourhood meets "+
					"s lies in every closed set around s, hence in the closure",
				func(b *Argument, near Fact) {
					every := b.Have(
						"every closed set c around s holds x: otherwise ⋃T "+
							"∖ c would be an open set holding x and missing s",
						"∀c:set(A). closed_in(c) ∧ s ⊆ c ⇒ x ∈ c",
						Derive(func(d *Argument) {
							d.Fix()
							around := d.Assume()
							outside := d.SupposeNot()
							open := d.Have(
								"the complement of c in the space is open, c being closed",
								"⋃T ∖ c ∈ T",
								By(ClosedInDef, around))
							holds := d.Have(
								"it holds x, a point of the space outside c",
								"x ∈ ⋃T ∖ c",
								BySets(near, outside))
							misses := d.Have(
								"and it misses s, which lies in c",
								"(⋃T ∖ c) ∩ s = ∅",
								BySets(around))
							d.Show(
								"so ⋃T ∖ c is an open set holding x and missing s, against the hypothesis",
								By(near, open, holds, misses))
						}))
					b.Show(
						"so x lies in the intersection of the closed sets around s, which is the closure of s",
						Unfold(ClosureDef),
						BySets(every))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Interior and closure are dual
// ---------------------------------------------------------------------------

// InteriorClosureDual — closure and interior are dual through
// complements in the space. Read at a point: the point lies in the
// closure of s when it lies in the space and every open set holding it
// meets s, and outside the interior of ⋃T ∖ s when no open set holding
// it lies inside ⋃T ∖ s. The two conditions agree because an open set
// lies in the space, and for a set in the space missing s and lying
// inside the complement of s are the same.
var InteriorClosureDual = interiorClosureDualThm{family.Add(registry.ProofEntry{
	Name: "InteriorClosureDual",
	Key:  "prop_7cc4e2f488f3a107",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "closure(s) = ⋃T ∖ interior(⋃T ∖ s)",
	},
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]], inSpace Fact) {
			missesIsInside := a.Have(
				"an open set lies in the space, so it misses s exactly when it lies inside the complement of s",
				"∀u:set(A). u ∈ T ⇒ (u ∩ s = ∅ ⇔ u ⊆ ⋃T ∖ s)",
				BySets())

			// The equation point by point; at a point x, each side reads
			// through its pointwise law, the closure's holding for s inside
			// the space.
			a.Do(Simp(Fwd(set_basic.Extension)))
			a.Fix()
			a.Do(Simp(Fwd(set_basic.InDiff), Fwd(InteriorPointwise), Fwd(ClosurePointwise.Read(topology))))
			a.Iff()

			a.Forward(
				"a point of the space whose every open neighbourhood meets s has none inside the complement of s",
				func(b *Argument, meetsEvery Fact) {
					b.Show(
						"an open set inside the complement of s misses s",
						By(meetsEvery, missesIsInside))
				})

			a.Backward(
				"a point of the space with no open neighbourhood inside "+
					"the complement of s has every open neighbourhood meeting s",
				func(b *Argument, noneInside Fact) {
					b.Show(
						"an open neighbourhood missing s would lie inside the complement of s",
						By(noneInside, missesIsInside))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The algebra of interior and closure
// ---------------------------------------------------------------------------

// InteriorSubsetSpace — an interior lies in the space: it is a union of
// members of T. No axiom enters, so the family is spelled.
var InteriorSubsetSpace = interiorSubsetSpaceThm{family.Add(registry.ProofEntry{
	Name: "InteriorSubsetSpace",
	Key:  "prop_9d18f76dc0a330ec",
	Build: family.Theorem("∀T:set(set(A)). ∀s:set(A). interior(T, s) ⊆ ⋃T",
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]]) {
			a.Show(
				"each open set inside s is a member of T, so their union lies in the union of T",
				Unfold(InteriorDef),
				BySets())
		}),
})}

// InteriorMono — a larger set has a larger interior: an open set inside
// s is inside t, so the interior of t unites every set the interior of s
// does. No axiom enters.
var InteriorMono = interiorMonoThm{family.Add(registry.ProofEntry{
	Name: "InteriorMono",
	Key:  "prop_9dde4588295029b7",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ t",
		},
		Conclusion: "interior(T, s) ⊆ interior(T, t)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, t *Expr[Set[A]], inside Fact) {
			a.Show(
				"each open set inside s lies inside t, so the union "+
					"over the first family lies in the union over the second",
				Unfold(InteriorDef),
				BySets(inside))
		}),
})}

// OpenIffInterior — a set is open exactly when it is its own interior.
var OpenIffInterior = openIffInteriorThm{family.Add(registry.ProofEntry{
	Name: "OpenIffInterior",
	Key:  "prop_c242f74a4429539d",
	Build: IsTopology.Law("∀s:set(A). s ∈ T ⇔ interior(s) = s",
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]]) {
			T := a.TermAs[Set[Set[A]]]("T")
			a.Iff()
			a.Forward(
				"an open set is its own interior",
				func(b *Argument, open Fact) {
					b.Show(
						"the interior of an open set is unchanged",
						By(open, InteriorOfOpen.At(T, s)))
				})
			a.Backward(
				"a fixed point is open because every interior is open",
				func(b *Argument, fixed Fact) {
					b.Show(
						"the set equals an open interior",
						By(Normalized, fixed, InteriorOpen.Read(topology).At(s)))
				})
		}),
})}

// ClosureMono — a larger set has a larger closure: a closed set around t
// is one around s, so the closure of s is an intersection over more sets.
var ClosureMono = closureMonoThm{family.Add(registry.ProofEntry{
	Name: "ClosureMono",
	Key:  "prop_a6f65ab7f1b21f3f",
	Reading: "No axiom and no s ⊆ ⋃T: a closed set around t is around s, so the " +
		"intersection over fewer sets is larger — true even where a closure is the whole type.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ t",
		},
		Conclusion: "closure(T, s) ⊆ closure(T, t)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, t *Expr[Set[A]], inside Fact) {
			a.Show(
				"each closed set around t is around s, so the intersection "+
					"over the first family lies in the one over the second",
				Unfold(ClosureDef),
				BySets(inside))
		}),
})}

// ClosureSubsetSpace — the closure of a subset of the space lies in the
// space: the space is a closed set around s, so it contains the closure.
var ClosureSubsetSpace = closureSubsetSpaceThm{family.Add(registry.ProofEntry{
	Name: "ClosureSubsetSpace",
	Key:  "prop_d5d58afadabc6cb9",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "closure(s) ⊆ ⋃T",
	},
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]], inSpace Fact) {
			a.Show(
				"the space is closed and contains s, so it contains the closure of s",
				By(ClosureMinimal, SpaceClosed.Read(topology), inSpace))
		}),
})}

// ClosureEmpty — the closure of the empty set is empty.
var ClosureEmpty = closureEmptyThm{family.Add(registry.ProofEntry{
	Name: "ClosureEmpty",
	Key:  "prop_c91bd8ae057ead9b",
	Deps: []registry.EntryLike{EmptyClosed, ClosureOfClosed},
	Build: family.Card(IsTopology.Statement("closure(∅) = ∅"),
		"The empty set is closed (EmptyClosed) and a closed set is its own closure (ClosureOfClosed)."),
})}

// ClosureIdempotent — the closure of a closure is the closure: the generic
// closure-operator law applies on the subsets of the space.
var ClosureIdempotent = closureIdempotentThm{family.Add(registry.ProofEntry{
	Name: "ClosureIdempotent",
	Key:  "prop_6d6498092dcdf148",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "closure(closure(s)) = closure(s)",
	},
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]], inSpace Fact) {
			closure := Read(ClosureOperator, topology)
			a.Show(
				"closure operators are idempotent on their carrier",
				BySets(order.ClosureIdempotent.Read(closure), inSpace))
		}),
})}

// ClosedIffClosure — a set is closed exactly when it lies in the space
// and is its own closure.
var ClosedIffClosure = closedIffClosureThm{family.Add(registry.ProofEntry{
	Name: "ClosedIffClosure",
	Key:  "prop_98439a4b89ae4ac4",
	Build: IsTopology.Law("∀s:set(A). closed_in(s) ⇔ s ⊆ ⋃T ∧ closure(s) = s",
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]]) {
			a.Iff()
			a.Forward(
				"a closed set lies in the space and equals its closure",
				func(b *Argument, closed Fact) {
					b.Show(
						"closedness supplies both the carrier condition and the fixed-point equation",
						By(closed, ClosedInDef, ClosureOfClosed))
				})
			a.Backward(
				"a fixed point in the space is closed because its closure is closed",
				func(b *Argument, fixed Fact) {
					parts := b.Conjuncts(
						fixed,
						"the set lies in the space",
						"the set equals its closure")
					b.Show(
						"the fixed-point equation transfers closedness from the closure",
						By(Normalized, ClosureClosed.Read(topology), parts[1], parts[0]))
				})
		}),
})}

// ClosureUnion — the closure of a union is the union of the closures:
// each closure lies in the closure of the union, as the closure is
// monotone, and the union of the two closures is a closed set around
// s ∪ t, so it holds the closure of s ∪ t.
var ClosureUnion = closureUnionThm{family.Add(registry.ProofEntry{
	Name: "ClosureUnion",
	Key:  "prop_21e1ca907353438a",
	Build: IsTopology.Law(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
			"t ⊆ ⋃T",
		},
		Conclusion: "closure(s ∪ t) = closure(s) ∪ closure(t)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			s, t *Expr[Set[A]],
			sInSpace, tInSpace Fact,
		) {
			union := a.TermAs[Set[A]]("s ∪ t")
			closures := a.TermAs[Set[A]]("closure(s) ∪ closure(t)")
			inside := a.Have(
				"each closure lies in the closure of the union",
				"closure(s) ∪ closure(t) ⊆ closure(s ∪ t)",
				BySets(ClosureMono.At(T, s, union), ClosureMono.At(T, t, union)))
			closed := a.Have(
				"the union of the two closures is closed",
				"closed_in(closure(s) ∪ closure(t))",
				By(ClosureClosed.Read(topology), UnionClosed.Read(topology), sInSpace, tInSpace))
			a.Show(
				"it is a closed set around s ∪ t, so it holds the closure of s ∪ t, and the two are equal",
				BySets(
					closed,
					inside,
					ClosureMinimal.At(T, union, closures),
					SubsetClosure.At(T, s),
					SubsetClosure.At(T, t)))
		}),
})}

// InteriorClosureComplement — the interior of a subset of the space is
// the complement of the closure of its complement: the duality read at
// the complement of s, whose own complement in the space is s again,
// makes the closure of the complement the complement of the interior,
// and the interior lies in the space, so taking the complement once more
// returns it.
var InteriorClosureComplement = interiorClosureComplementThm{family.Add(registry.ProofEntry{
	Name: "InteriorClosureComplement",
	Key:  "prop_cec3352322c61047",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "interior(s) = ⋃T ∖ closure(⋃T ∖ s)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			s *Expr[Set[A]],
			inSpace Fact,
		) {
			space := a.TermAs[Set[A]]("⋃T")
			complement := a.TermAs[Set[A]]("⋃T ∖ s")
			twice := a.Have(
				"s lies in the space, so it is the complement there of its complement",
				"⋃T ∖ (⋃T ∖ s) = s",
				BySets(inSpace))
			dual := a.Have(
				"the duality at the complement of s, a subset of the "+
					"space: its closure is the complement of the interior of s",
				"closure(⋃T ∖ s) = ⋃T ∖ interior(s)",
				By(
					Normalized,
					InteriorClosureDual.Read(topology).At(complement),
					set_order.SubsetDiff.At(space, s),
					twice))
			a.Show(
				"so the complement of that closure is the interior of s, which lies in the space",
				BySets(dual, InteriorSubsetSpace.At(T, s)))
		}),
})}

// OpenInterClosure — an open set meets a closure inside the closure of
// its meet with the set.
var OpenInterClosure = openInterClosureThm{family.Add(registry.ProofEntry{
	Name: "OpenInterClosure",
	Key:  "prop_d7dddd693b0d558e",
	Deps: []registry.EntryLike{ClosurePointwise, InterOpen},
	Build: family.Card(IsTopology.Statement(Statement{
		Binders: "∀u s:set(A).",
		Hypotheses: []string{
			"u ∈ T",
			"s ⊆ ⋃T",
		},
		Conclusion: "u ∩ closure(s) ⊆ closure(u ∩ s)",
	}),
		"By ClosurePointwise at both closures: an open w about a point of u ∩ closure(s) "+
			"meets u in an open set about the point (InterOpen), which meets s, so w meets u ∩ s."),
})}

// DenseMeetsOpen — a subset of the space is dense exactly when it meets
// every non-empty open set. Both directions read the closure at a point.
// Forward, a point of a non-empty open set lies in the space, so in the
// closure, and the open set is a neighbourhood of it, which meets s.
// Backward, an open set holding a point is non-empty, so it meets s:
// every point of the space is then in the closure, and the closure lies
// in the space.
var DenseMeetsOpen = denseMeetsOpenThm{family.Add(registry.ProofEntry{
	Name: "DenseMeetsOpen",
	Key:  "prop_6051c9e0fe69e79e",
	Build: IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
		},
		Conclusion: "closure(s) = ⋃T ⇔ ∀u:set(A). u ∈ T ∧ ¬(u = ∅) ⇒ ¬(u ∩ s = ∅)",
	},
		func(a *Argument, topology IsTopologyFact[on.T], s *Expr[Set[A]], inSpace Fact) {
			a.Iff()

			a.Forward(
				"a dense set meets every non-empty open set: a point of "+
					"the open set lies in the closure, and the open set holds it",
				func(b *Argument, dense Fact) {
					b.Fix()
					parts := b.Conjuncts(
						b.Assume(),
						"u is open",
						"u is non-empty")
					x, xIn := b.ObtainAs[A](
						"u has a point x",
						"∃x:A. x ∈ u",
						By(parts[1], set_basic.MemberNotEmpty))
					inClosure := b.Have(
						"x lies in the space, so in the closure of s",
						"x ∈ closure(s)",
						BySets(dense, parts[0], xIn))
					b.Show(
						"u is an open set holding x, a point of the closure, so it meets s",
						By(ClosurePointwise.Read(topology).At(s, x), inSpace, inClosure, parts[0], xIn))
				})

			a.Backward(
				"a set meeting every non-empty open set is dense: each point "+
					"of the space lies in its closure, which lies in the space",
				func(b *Argument, meets Fact) {
					neighbourhoods := b.Have(
						"an open set holding a point is non-empty, so it meets s",
						"∀u:set(A). ∀x:A. u ∈ T ∧ x ∈ u ⇒ ¬(u ∩ s = ∅)",
						BySets(meets))
					covers := b.Have(
						"so every point of the space lies in the closure of s",
						"∀x:A. x ∈ ⋃T ⇒ x ∈ closure(s)",
						b.ForEach(func(x *Expr[A]) Action {
							return By(ClosurePointwise.Read(topology).At(s, x), inSpace, neighbourhoods)
						}))
					b.Show(
						"the closure lies in the space, and the space in the closure",
						BySets(covers, ClosureSubsetSpace.Read(topology).At(s), inSpace))
				})
		}),
})}
