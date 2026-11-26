// countability.go — how the four countability properties stand to each
// other and to subspaces. A countable base gives a countable base at each
// point, a countable dense set (one point from each non-empty member) and a
// countable subcover of every open cover (one member of the cover around
// each member of the base that fits inside one); a compact space has the
// last too. A regular space with that last property is normal.

package countability

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/separation"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// From a countable base
// ---------------------------------------------------------------------------

// SecondCountableImpSeparable — a space with a countable base has a
// countable dense set: a point picked from each non-empty member of the
// base. The picked points are countably many, the image of a part of a
// countable family; they lie in the space, each in its member of the
// base, an open set; and they meet every non-empty open set, which
// holds a member of the base about one of its points. A set of points
// of the space meeting every non-empty open set is dense
// (topological_space.DenseMeetsOpen). The empty member is left out: the
// point picked from it is arbitrary, possibly outside the space.
var SecondCountableImpSeparable = secondCountableImpSeparableThm{family.Add(registry.ProofEntry{
	Name: "SecondCountableImpSeparable",
	Key:  "prop_881b8c2d325a6a07",
	Build: topological_space.IsTopology.Law(Statement{
		Hypotheses: []string{
			"second_countable_space(T)",
		},
		Conclusion: "separable_space(T)",
	},
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], secondCountable Fact) {
			_, base := a.UnpackAs[Set[Set[A]]](a.Unfolded(secondCountable, SecondCountableSpaceDef), "b")
			given := a.Conjuncts(
				base,
				"b is countable",
				"b is a base of the topology")
			countableBase, isBase := given[0], given[1]
			basis := a.Conjuncts(
				a.Unfolded(isBase, topological_space.TopologyBaseDef),
				"the members of b are open",
				"a point of an open set lies in a member of b inside the open set")
			open, around := basis[0], basis[1]
			_, pDef := a.LetAs[Fun[Set[A], A]]("p", "λv:set(A). εx:A. x ∈ v")
			c, cDef := a.LetAs[Set[A]]("c", "image(p, b ∖ {∅})")

			picked := a.Have(
				"a non-empty set holds the point p picks from it",
				"∀v:set(A). v ≠ ∅ ⇒ p(v) ∈ v",
				By(pDef, set_basic.MemberNotEmpty))
			fewer := a.Have(
				"the non-empty members of b are countably many, as b is",
				"countable(b ∖ {∅})",
				By(countableBase, cardinal.CountableSubset, set_order.SubsetDiff))
			countableC := a.Have(
				"so c, their image under p, is countable",
				"countable(c)",
				cDef.Rw(),
				By(fewer, cardinal.CountableImage))
			inSpace := a.Have(
				"c lies in the space: p(v) lies in v, an open set",
				"c ⊆ ⋃T",
				cDef.Rw(),
				Simp(Fwd(set_image.ImageSubsetIff)),
				a.ForEach(func(v *Expr[Set[A]]) Action { return BySets(picked.At(v), open) }))
			meets := a.Have(
				"c meets every non-empty open set",
				"∀u:set(A). u ∈ T ∧ u ≠ ∅ ⇒ u ∩ c ≠ ∅",
				Derive(func(a *Argument) {
					u := a.FixAs[Set[A]]("u")
					assumed := a.Conjuncts(
						a.Assume(),
						"u is open",
						"u is non-empty")
					uOpen, uNonEmpty := assumed[0], assumed[1]
					x, xIn := a.ObtainAs[A](
						"u holds a point x",
						"∃x:A. x ∈ u",
						By(uNonEmpty, set_basic.MemberNotEmpty))
					v, vAround := a.ObtainAs[Set[A]](
						"the base gives a member v of b holding x inside u",
						"∃v:set(A). v ∈ b ∧ x ∈ v ∧ v ⊆ u",
						By(around.At(u, x), uOpen, xIn))
					a.Show(
						"v holds x, so p(v) lies in v, inside u, and in c",
						BySets(picked.At(v), cDef, vAround))
				}))

			a.Do(Unfold(SeparableSpaceDef))
			a.Take(c)
			a.Show(
				"c is a countable set of points of the space meeting every non-empty open set, so dense",
				By(countableC, inSpace, topological_space.DenseMeetsOpen.Read(topology).At(c), meets))
		}),
})}

// SecondCountableImpLindelof — a space with a countable base is
// Lindelöf. Given an open cover, keep the members of the base that fit
// inside some member of the cover, and choose one member of the cover
// around each. The members kept are countably many, a part of the base,
// so the chosen members are too, the image of a countable set. They
// cover the space: a point lies in a member of the cover, an open set,
// so in a member of the base inside it, which is then kept, and the
// member chosen around that one holds the point. No axiom of a topology
// is read: T is any family of sets.
var SecondCountableImpLindelof = secondCountableImpLindelofThm{family.Add(registry.ProofEntry{
	Name: "SecondCountableImpLindelof",
	Key:  "prop_381e13ea2ff16197",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"second_countable_space(T)",
		},
		Conclusion: "lindelof_space(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], secondCountable Fact) {
			_, base := a.UnpackAs[Set[Set[A]]](a.Unfolded(secondCountable, SecondCountableSpaceDef), "b")
			given := a.Conjuncts(
				base,
				"b is countable",
				"b is a base of the topology")
			countableBase, isBase := given[0], given[1]
			basis := a.Conjuncts(
				a.Unfolded(isBase, topological_space.TopologyBaseDef),
				"the members of b are open",
				"a point of an open set lies in a member of b inside the open set")
			around := basis[1]

			a.Do(Unfold(LindelofSpaceDef))
			a.FixAs[Set[Set[A]]]("c")
			cover := a.Conjuncts(
				a.Assume(),
				"the members of c are open",
				"c covers the space")
			open, covers := cover[0], cover[1]
			_, qDef := a.LetAs[Fun[Set[A], Set[A]]]("q", "λv:set(A). εw:set(A). w ∈ c ∧ v ⊆ w")
			_, fitDef := a.LetAs[Set[Set[A]]]("b'", "{v:set(A) | v ∈ b ∧ (∃w:set(A). w ∈ c ∧ v ⊆ w)}")
			d, dDef := a.LetAs[Set[Set[A]]]("d", "image(q, b')")

			chosen := a.Have(
				"q(v) is a member of c containing v, wherever c has one containing v",
				"∀v:set(A). (∃w:set(A). w ∈ c ∧ v ⊆ w) ⇒ q(v) ∈ c ∧ v ⊆ q(v)",
				By(HilbertDenoted, qDef))
			within := a.Have(
				"the members of b' are members of b",
				"b' ⊆ b",
				BySets(fitDef))
			countableD := a.Have(
				"so d, the image under q of a part of the countable b, is countable",
				"countable(d)",
				dDef.Rw(),
				By(countableBase, within, cardinal.CountableSubset, cardinal.CountableImage))
			inCover := a.Have(
				"d is a part of c: q(v) is a member of c for every v in b'",
				"d ⊆ c",
				dDef.Rw(),
				Simp(Fwd(set_image.ImageSubsetIff)),
				a.ForEach(func(v *Expr[Set[A]]) Action { return BySets(chosen.At(v), fitDef) }))
			coversD := a.Have(
				"d covers the space",
				"⋃T ⊆ ⋃d",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(a *Argument) {
					x := a.FixAs[A]("x")
					xIn := a.Assume()
					w, wIn := a.ObtainAs[Set[A]](
						"x lies in a member w of the cover",
						"∃w:set(A). w ∈ c ∧ x ∈ w",
						BySets(xIn, covers))
					v, vAround := a.ObtainAs[Set[A]](
						"w is open, so the base gives a member v of b holding x inside w",
						"∃v:set(A). v ∈ b ∧ x ∈ v ∧ v ⊆ w",
						By(around.At(w, x), wIn, open, set_basic.SubsetDef))
					a.Show(
						"v fits inside w, so v lies in b', and x lies in q(v), a member of d",
						dDef.Rw(),
						BySets(chosen.At(v), fitDef, wIn, vAround))
				}))

			a.Take(d)
			a.Show(
				"d is a countable part of c covering the space",
				By(inCover, countableD, coversD))
		}),
})}

// SecondCountableSubtopology — a subspace of a space with a countable
// base has one.
var SecondCountableSubtopology = secondCountableSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "SecondCountableSubtopology",
	Key:  "prop_b7c6003159b61339",
	Deps: []registry.EntryLike{topological_space.SubtopologyBase, cardinal.CountableImage},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"second_countable_space(T)",
		},
		Conclusion: "second_countable_space(subtopology(T, s))",
	},
		"The traces of the base form a base of the subspace (SubtopologyBase), "+
			"countable as an image (CountableImage). No axiom enters."),
})}

// ---------------------------------------------------------------------------
// Lindelöf spaces
// ---------------------------------------------------------------------------

// CompactImpLindelof — a compact space is Lindelöf.
var CompactImpLindelof = compactImpLindelofThm{family.Add(registry.ProofEntry{
	Name: "CompactImpLindelof",
	Key:  "prop_ea2411c15e963691",
	Deps: []registry.EntryLike{cardinal.FiniteCountable},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"compact_in(T, ⋃T)",
		},
		Conclusion: "lindelof_space(T)",
	},
		"A finite subcover is a countable one (FiniteCountable). No axiom enters."),
})}

// RegularLindelofNormal — a regular Lindelöf space is normal.
var RegularLindelofNormal = regularLindelofNormalThm{family.Add(registry.ProofEntry{
	Name: "RegularLindelofNormal",
	Key:  "prop_b6a8ad3cf40af51e",
	Deps: []registry.EntryLike{
		separation.RegularIffClosedNeighbourhoods,
		cardinal.CountableCover,
		topological_space.UnionClosed,
		topological_space.ClosureClosed,
		topological_space.UnionsOpen,
	},
	Build: family.Card(topological_space.IsTopology.Statement(Statement{
		Hypotheses: []string{
			"regular_space(T)",
			"lindelof_space(T)",
		},
		Conclusion: "normal_space(T)",
	}),
		"For disjoint closed s and t, each point of s has an open neighbourhood whose closure "+
			"misses t (RegularIffClosedNeighbourhoods); those with the complement of s cover the "+
			"space, so countably many, u(n), cover s, and likewise v(n) cover t with closures "+
			"missing s. Removing from u(n) the closures of v(0) to v(n), and from v(n) those of "+
			"u(0) to u(n), leaves open sets (finitely many closed sets unite to a closed set) still "+
			"covering s and t; the two unions are disjoint. The sequences come from CountableCover."),
})}

// SecondCountableOpenCover — a countable open cover by second countable
// subspaces supplies a countable base for the whole space.
var SecondCountableOpenCover = secondCountableOpenCoverThm{family.Add(registry.ProofEntry{
	Name: "SecondCountableOpenCover",
	Key:  "prop_f7d2ba0eafc31b24",
	Deps: []registry.EntryLike{
		cardinal.CountableImage,
		cardinal.CountableUnions,
		topological_space.OpenInSubtopology,
	},
	Build: family.Card(topological_space.IsTopology.Statement(Statement{
		Binders: "∀C:set(set(A)).",
		Hypotheses: []string{
			"countable(C)",
			"C ⊆ T",
			"⋃T ⊆ ⋃C",
			"∀U:set(A). U ∈ C ⇒ second_countable_space(subtopology(T, U))",
		},
		Conclusion: "second_countable_space(T)",
	}),
		"Choose a countable base in each U. Since U is open, its base members are "+
			"open in T (topological_space.OpenInSubtopology); their union refines each "+
			"neighbourhood at each point and is countable by cardinal.CountableImage "+
			"and cardinal.CountableUnions. The empty cover applies to the empty space."),
})}

// LindelofCountableCover — a space covered by countably many Lindelöf
// subspaces is Lindelöf; the subspaces need not be open.
var LindelofCountableCover = lindelofCountableCoverThm{family.Add(registry.ProofEntry{
	Name: "LindelofCountableCover",
	Key:  "prop_1b27d996ec557aff",
	Deps: []registry.EntryLike{
		cardinal.CountableImage,
		cardinal.CountableUnions,
		topological_space.OpenInSubtopology,
	},
	Build: family.Card(topological_space.IsTopology.Statement(Statement{
		Binders: "∀C:set(set(A)).",
		Hypotheses: []string{
			"countable(C)",
			"⋃T ⊆ ⋃C",
			"∀S:set(A). S ∈ C ⇒ S ⊆ ⋃T ∧ lindelof_space(subtopology(T, S))",
		},
		Conclusion: "lindelof_space(T)",
	}),
		"Trace an open cover on each S (topological_space.OpenInSubtopology), choose a countable "+
			"subcover there, and choose one original open set for every retained trace. The "+
			"resulting countable union of countable families covers the space "+
			"(cardinal.CountableImage, cardinal.CountableUnions). Empty subspaces require no choices."),
})}
