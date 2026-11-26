// compact.go — compact sets: what compactness survives (a closed part,
// a union of two), its reading by closed sets with the finite
// intersection property, the limit point an infinite subset of one has,
// and the compact sets of a discrete space; compact sets in a Hausdorff
// space: a point outside one has an open neighbourhood missing it, so the
// set is closed, and two disjoint ones lie in disjoint open sets;
// compactness of a subset of a subspace, which is its compactness in the
// whole space; and locally compact spaces, with their closed subspaces
// and, Hausdorff, their open ones.

package compact

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosedSubsetCompact — a closed set inside a compact set is compact: it
// is its own meet with the compact set, and a compact set meets a closed
// set in a compact set (CompactInterClosed).
var ClosedSubsetCompact = closedSubsetCompactThm{family.Add(registry.ProofEntry{
	Name: "ClosedSubsetCompact",
	Key:  "prop_17ec7513b5fc70cd",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀k c:set(A).",
		Hypotheses: []string{
			"compact_in(T, k)",
			"closed_in(T, c)",
			"c ⊆ k",
		},
		Conclusion: "compact_in(T, c)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], k, c *Expr[Set[A]], compactK, closedC, inside Fact) {
			meet := a.Have(
				"c lies inside k, so it is its own meet with k",
				"k ∩ c = c",
				BySets(inside))
			a.Show(
				"and the meet of the compact k with the closed c is compact",
				By(Normalized, meet, compactK, closedC, CompactInterClosed.At(T, k, c)))
		}),
})}

// CompactUnion — two compact sets unite to a compact set: an open cover of
// s ∪ t covers each of them, and the two finite subcovers together are a
// finite subcover of s ∪ t.
var CompactUnion = compactUnionThm{family.Add(registry.ProofEntry{
	Name: "CompactUnion",
	Key:  "prop_4d3084c96bc87251",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s t:set(A).",
		Hypotheses: []string{
			"compact_in(T, s)",
			"compact_in(T, t)",
		},
		Conclusion: "compact_in(T, s ∪ t)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, t *Expr[Set[A]], compactS, compactT Fact) {
			sParts := a.Conjuncts(
				a.Unfolded(compactS, CompactInDef),
				"s lies in the space",
				"and every open cover of s has a finite subcover")
			tParts := a.Conjuncts(
				a.Unfolded(compactT, CompactInDef),
				"t lies in the space",
				"and every open cover of t has a finite subcover")
			a.Do(Unfold(CompactInDef), SplitConj(
				Case(
					"s ∪ t lies in the space, as s and t do",
					BySets(sParts[0], tParts[0])),
				Case(
					"every open cover of s ∪ t has a finite subcover",
					Derive(func(b *Argument) {
						c := b.FixAs[Set[Set[A]]]("c")
						covering := b.Assume() // c is a family of open sets covering s ∪ t
						eachCovered := b.Have(
							"c covers s and t, both lying in s ∪ t",
							"s ⊆ ⋃c ∧ t ⊆ ⋃c",
							BySets(covering))
						d1, sCovered := b.ObtainAs[Set[Set[A]]](
							"by compactness of s, finitely many members d₁ of c cover s",
							"∃d₁:set(set(A)). d₁ ⊆ c ∧ finite(d₁) ∧ s ⊆ ⋃d₁",
							By(covering, eachCovered, sParts[1].At(c)))
						d2, tCovered := b.ObtainAs[Set[Set[A]]](
							"by compactness of t, finitely many members d₂ of c cover t",
							"∃d₂:set(set(A)). d₂ ⊆ c ∧ finite(d₂) ∧ t ⊆ ⋃d₂",
							By(covering, eachCovered, tParts[1].At(c)))
						b.Take(b.TermAs[Set[Set[A]]]("d₁ ∪ d₂"))
						b.Show(
							"d₁ ∪ d₂ is a finite subfamily of c covering s ∪ t",
							BySets(sCovered, tCovered, finite_set.FiniteUnionImp.At(d1, d2)))
					})),
			))
		}),
})}

// CompactFip — compactness read by closed sets: k is compact exactly when
// every family of closed sets each finitely many of which meet k in a
// point has a point of k in common.
//
// Both directions pass to complements in the space. The complements of
// a closed family f with no point of k in common are open and cover k;
// finitely many of them do, the complements of finitely many members g
// of f, and k then meets nothing of ⋂g. Conversely the complements of an
// open cover c of k are closed with no point of k in common, so finitely
// many of them already have none — the complements of finitely many
// members d of c, which cover k.
var CompactFip = compactFipThm{family.Add(registry.ProofEntry{
	Name: "CompactFip",
	Key:  "prop_92eb172fdb9aa077",
	Reading: "True for an arbitrary family T: the complement of a set u ∈ T in " +
		"⋃T is closed by closed_in alone. The instance g = ∅ reads ¬(k ∩ 𝕌 = ∅), " +
		"so a non-empty k is asked of the family side; for k = ∅ both sides hold.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀k:set(A).",
		Conclusion: "compact_in(T, k) ⇔ " +
			"k ⊆ ⋃T ∧ " +
			"∀f:set(set(A)). " +
			"    (∀c:set(A). c ∈ f ⇒ closed_in(T, c)) ∧ " +
			"    (∀g:set(set(A)). finite(g) ∧ g ⊆ f ⇒ ¬(k ∩ ⋂g = ∅)) ⇒ " +
			"    ¬(k ∩ ⋂f = ∅)",
		Abbrev: Abbrev{
			{Name: "complementsOfF", Text: "image(λu:set(A). ⋃T ∖ u, f)"},
			{Name: "complementsOfG", Text: "image(λu:set(A). ⋃T ∖ u, g)"},
			{Name: "complementsOfC", Text: "image(λu:set(A). ⋃T ∖ u, c)"},
			{Name: "complementsOfD", Text: "image(λu:set(A). ⋃T ∖ u, d)"},
		},
	},
		func(a *Argument, T *Expr[Set[Set[A]]], k *Expr[Set[A]]) {
			// Taking the complement in the space, which carries closed sets
			// to open ones and back.
			complement := a.TermAs[Fun[Set[A], Set[A]]]("λu:set(A). ⋃T ∖ u")

			a.Iff()
			a.Forward(
				"compact: the complements of a closed family with no point of "+
					"k in common would be an open cover of k with no finite subcover",
				func(b *Argument, compact Fact) {
					parts := b.Conjuncts(
						b.Unfolded(compact, CompactInDef),
						"k lies in the space",
						"and every open cover of k has a finite subcover")
					b.Do(SplitConj(
						Case(
							"k lies in the space",
							By(parts[0])),
						Case(
							"a closed family each finitely many of which meet k has a point of k in common",
							Derive(func(inner *Argument) {
								f := inner.FixAs[Set[Set[A]]]("f")
								given := inner.Conjuncts(
									inner.Assume(),
									"the members of f are closed",
									"and each finitely many of them meet k")
								closedF, meetsK := given[0], given[1]
								missing := inner.SupposeNot() // k ∩ ⋂f = ∅
								complementsOpen := inner.Have(
									"the complements of the members of f are open",
									"«complementsOfF» ⊆ T",
									By(closedF, set_image.ImageSubsetIff, topological_space.ClosedInDef))
								complementsCover := inner.Have(
									"and they cover k: a point of k lies in the space, and outside some member of f",
									"k ⊆ ⋃«complementsOfF»",
									Simp(Fwd(set_image.UnionsImage)),
									BySets(missing, parts[0]))
								e, few := inner.ObtainAs[Set[Set[A]]](
									"by compactness of k, finitely many of them, e, cover k",
									"∃e:set(set(A)). e ⊆ «complementsOfF» ∧ finite(e) ∧ k ⊆ ⋃e",
									By(complementsOpen, complementsCover, parts[1].At(inner.TermAs[Set[Set[A]]]("«complementsOfF»"))))
								g, fromG := inner.ObtainAs[Set[Set[A]]](
									"they are the complements of finitely many members g of f",
									"∃g:set(set(A)). finite(g) ∧ e = image(λu:set(A). ⋃T ∖ u, g) ∧ g ⊆ f",
									By(finite_set.FiniteSubsetImage.At(complement, f, e), few))
								gParts := inner.Conjuncts(
									fromG,
									"g is finite",
									"e is the family of complements of the members of g",
									"g lies in f")
								coveredByG := inner.Have(
									"so the complements of the members of g cover k",
									"k ⊆ ⋃«complementsOfG»",
									gParts[1].RwRev(),
									By(few))
								missesMeet := inner.Have(
									"so each point of k lies outside some member of g, and k meets nothing of ⋂g",
									"k ∩ ⋂g = ∅",
									BySets(inner.Simplified(coveredByG, Fwd(set_image.UnionsImage))))
								inner.Show(
									"which the finitely many members g of f forbid",
									By(Normalized, missesMeet, meetsK.At(g), gParts[0], gParts[2]))
							})),
					))
				})
			a.Backward(
				"the finite intersection property: the complements of an open cover "+
					"of k are closed with no common point in k, so finitely many have none",
				func(b *Argument, intersecting Fact) {
					parts := b.Conjuncts(
						intersecting,
						"k lies in the space",
						"and a closed family each finitely many of which meet k has a point of k in common")
					b.Do(Unfold(CompactInDef), SplitConj(
						Case(
							"k lies in the space",
							By(parts[0])),
						Case(
							"every open cover of k has a finite subcover",
							Derive(func(inner *Argument) {
								cover := inner.FixAs[Set[Set[A]]]("c")
								covering := inner.Assume() // c is a family of open sets covering k
								complementsClosed := inner.Have(
									"the complements of the members of c are closed",
									"∀b:set(A). b ∈ «complementsOfC» ⇒ closed_in(T, b)",
									Simp(Fwd(set_image.ForallInImage)),
									By(covering, topological_space.OpenClosedComplement, set_basic.SubsetDef))
								missesMeet := inner.Have(
									"and k meets nothing of their intersection, each point of k lying in a member of c",
									"k ∩ ⋂«complementsOfC» = ∅",
									Simp(Fwd(set_image.IntersImage)),
									BySets(covering))
								g, few := inner.ObtainAs[Set[Set[A]]](
									"so finitely many of them, g, already have no point of k in common",
									"∃g:set(set(A)). finite(g) ∧ g ⊆ «complementsOfC» ∧ k ∩ ⋂g = ∅",
									By(complementsClosed, parts[1].At(inner.TermAs[Set[Set[A]]]("«complementsOfC»")), missesMeet))
								d, fromD := inner.ObtainAs[Set[Set[A]]](
									"they are the complements of finitely many members d of c",
									"∃d:set(set(A)). finite(d) ∧ g = image(λu:set(A). ⋃T ∖ u, d) ∧ d ⊆ c",
									By(finite_set.FiniteSubsetImage.At(complement, cover, g), few))
								dParts := inner.Conjuncts(
									fromD,
									"d is finite",
									"g is the family of complements of the members of d",
									"d lies in c")
								missesComplementsOfD := inner.Have(
									"so k meets nothing of the intersection of the complements of the members of d",
									"k ∩ ⋂«complementsOfD» = ∅",
									dParts[1].RwRev(),
									By(few))
								inner.Take(d)
								inner.Show(
									"d is a finite subfamily of c covering k: a point of k lies "+
										"in the space, outside the complement of some member of d",
									BySets(
										dParts[0],
										dParts[2],
										inner.Simplified(missesComplementsOfD, Fwd(set_image.IntersImage)),
										parts[0]))
							})),
					))
				})
		}),
})}

// PointCompactSeparation — in a Hausdorff space, a point outside a compact
// set and the set lie in disjoint open sets.
//
// The open sets that some open neighbourhood of x misses cover k: a
// point y of k lies in the space and differs from x, so the Hausdorff
// property puts x and y in disjoint open sets, and the one holding y is
// such a set. Compactness of k picks finitely many of them covering k;
// their union v is open and holds k, and
// topological_space.SeparatedFromFiniteUnion meets the neighbourhoods of x
// missing each of them in one open set u around x missing v. No choice
// function enters: the separating neighbourhoods are named by the family,
// never chosen from it.
var PointCompactSeparation = pointCompactSeparationThm{family.Add(registry.ProofEntry{
	Name: "PointCompactSeparation",
	Key:  "prop_8da08b93d057bd30",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀k:set(A). ∀x:A.",
		Hypotheses: []string{
			"hausdorff(T)",
			"compact_in(k)",
			"x ∈ ⋃T",
			"x ∉ k",
		},
		Conclusion: "∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ k ⊆ v ∧ u ∩ v = ∅",
		Abbrev: Abbrev{
			{Name: "separatedFromX", Text: "{v:set(A) | v ∈ T ∧ ∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ v = ∅}"},
		},
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			k *Expr[Set[A]],
			x *Expr[A],
			_ Fact,
		) {
			// The two definitions deposit their clauses: distinct points of
			// the space lie in disjoint open sets; k lies in the space and
			// every open cover of it has a finite subcover.
			a.Do(Unfold(topological_space.HausdorffDef), Unfold(CompactInDef))
			outside := a.Hyp("x ∉ k")
			inSpace := a.Hyp("x ∈ ⋃T")
			separates := a.Hyp(Statement{
				Binders: "∀y z:A.",
				Hypotheses: []string{
					"y ∈ ⋃T",
					"z ∈ ⋃T",
					"y ≠ z",
				},
				Conclusion: "∃u v:set(A). u ∈ T ∧ v ∈ T ∧ y ∈ u ∧ z ∈ v ∧ u ∩ v = ∅",
			})
			kInSpace := a.Hyp("k ⊆ ⋃T")
			subcover := a.Hyp("∀c:set(set(A)). c ⊆ T ∧ k ⊆ ⋃c ⇒ ∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ k ⊆ ⋃d")

			// The open sets that some open neighbourhood of x misses.
			familyOpen := a.Have(
				"the family is made of open sets",
				"«separatedFromX» ⊆ T",
				BySets())
			pointwise := a.Have(
				"a point y of k is in the space and differs from x, so "+
					"the Hausdorff property puts y in a member of the family",
				"∀y:A. y ∈ k ⇒ y ∈ ⋃«separatedFromX»",
				Derive(func(b *Argument) {
					y := b.FixAs[A]()
					yIn := b.Assume()
					yInSpace := b.Have(
						"y lies in the space, as k does",
						"y ∈ ⋃T",
						BySets(yIn, kInSpace))
					_, _, disjoint := b.Obtain2(
						"x and y are distinct points of the space, so open sets w ∋ x and v ∋ y are disjoint",
						"∃w v:set(A). w ∈ T ∧ v ∈ T ∧ x ∈ w ∧ y ∈ v ∧ w ∩ v = ∅",
						By(outside, separates.At(x, y), yInSpace, inSpace, yIn))
					b.Show(
						"so v is a member of the family holding y",
						BySets(disjoint))
				}))
			familyCoversK := a.Have(
				"so the family covers k",
				"k ⊆ ⋃«separatedFromX»",
				BySets(pointwise))
			d, finiteSubcover := a.ObtainAs[Set[Set[A]]](
				"compactness of k at that cover: finitely many of its members already cover k",
				"∃d:set(set(A)). d ⊆ «separatedFromX» ∧ finite(d) ∧ k ⊆ ⋃d",
				By(familyOpen, familyCoversK, subcover.At(a.TermAs[Set[Set[A]]]("«separatedFromX»"))))
			separatedD := a.Have(
				"each member of d is one of the family, so an open neighbourhood of x misses it",
				"∀v:set(A). v ∈ d ⇒ ∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ v = ∅",
				BySets(finiteSubcover))
			u, uSeparates := a.Obtain(
				"so one open neighbourhood u of x misses the union of d",
				"∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ ⋃d = ∅",
				By(
					topological_space.SeparatedFromFiniteUnion.Read(topology).At(x, d),
					inSpace,
					finiteSubcover,
					separatedD))

			a.Take(u)
			a.Take(a.TermAs[Set[A]]("⋃d"))
			a.Show(
				"u is open and holds x, the union of d is open and holds k, and the two are disjoint",
				BySets(uSeparates, finiteSubcover, topological_space.UnionsOpen.Read(topology).At(d)))
		}),
})}

// SeparatedFromCompact — in a Hausdorff space, a point outside a compact
// set has an open neighbourhood disjoint from it: the open set around the
// point that PointCompactSeparation keeps apart from an open set holding
// the compact set.
var SeparatedFromCompact = separatedFromCompactThm{family.Add(registry.ProofEntry{
	Name: "SeparatedFromCompact",
	Key:  "prop_19d5e9d6bc544f81",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀k:set(A). ∀x:A.",
		Hypotheses: []string{
			"hausdorff(T)",
			"compact_in(k)",
			"x ∈ ⋃T",
			"x ∉ k",
		},
		Conclusion: "∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ k = ∅",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			k *Expr[Set[A]],
			x *Expr[A],
			assumptions Fact,
		) {
			u, _, apart := a.Obtain2(
				"x and k lie in disjoint open sets u ∋ x and v ⊇ k",
				"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ k ⊆ v ∧ u ∩ v = ∅",
				By(PointCompactSeparation, topology, assumptions))
			a.Take(u)
			a.Show(
				"u is open, holds x, and misses k, which lies in v",
				BySets(apart))
		}),
})}

// SetSeparatedFromFiniteUnion — a set of the space with an open set
// around it disjoint from each of finitely many sets has one disjoint
// from their union: the meet of the finitely many open sets. By induction
// on the family, as topological_space.SeparatedFromFiniteUnion for a
// point. At the empty family the whole space serves, s lying in it.
// Across insert(w, e), the open set holding s that misses the new member
// w meets the one the induction hypothesis gives for the rest e.
var SetSeparatedFromFiniteUnion = setSeparatedFromFiniteUnionThm{family.Add(registry.ProofEntry{
	Name: "SetSeparatedFromFiniteUnion",
	Key:  "prop_2ecf437b069a9120",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s:set(A). ∀d:set(set(A)).",
		Hypotheses: []string{
			"s ⊆ ⋃T",
			"finite(d)",
			"∀w:set(A). w ∈ d ⇒ ∃v:set(A). v ∈ T ∧ s ⊆ v ∧ v ∩ w = ∅",
		},
		Conclusion: "∃v:set(A). v ∈ T ∧ s ⊆ v ∧ v ∩ ⋃d = ∅",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			s *Expr[Set[A]],
			d *Expr[Set[Set[A]]],
			inSpace, finite, keptApart Fact,
		) {
			a.Show(
				"the induction carries the property to d, which is finite and kept apart from s member by member",
				ByInduction(finite_set.FiniteInduct, finite, Generalizing(keptApart),
					Case(
						"at ∅ the whole space serves: it is open, holds s, and the empty family unites to nothing",
						Derive(func(b *Argument) {
							b.Assume() // every member of ∅ is kept apart from s, vacuously
							b.Take(b.TermAs[Set[A]]("⋃T"))
							b.Show(
								"⋃T is open, holds s, and meets ⋃∅ = ∅ in nothing",
								By(
									Normalized,
									inSpace,
									topological_space.SpaceOpen.Read(topology),
									set_algebra.UnionsEmpty,
									set_algebra.InterEmpty))
						})),
					Case(
						"one more set w: the open set keeping s from w meets the one keeping s from the rest e",
						Derive(func(b *Argument) {
							w := b.FixAs[Set[A]]("w")
							b.FixAs[Set[Set[A]]]("e")
							carried := b.Assume()      // the induction hypothesis: e kept apart member by member ⇒ e kept apart
							separatedAll := b.Assume() // every member of insert(w, e) is kept apart from s

							v2, v2Separates := b.ObtainAs[Set[A]](
								"w is a member of insert(w, e), so some open v₂ ⊇ s misses w",
								"∃v₂:set(A). v₂ ∈ T ∧ s ⊆ v₂ ∧ v₂ ∩ w = ∅",
								BySets(separatedAll.At(w)))
							rest := b.Have(
								"and e is a subfamily of insert(w, e), so its members are kept apart from s too",
								"∀z:set(A). z ∈ e ⇒ ∃v:set(A). v ∈ T ∧ s ⊆ v ∧ v ∩ z = ∅",
								BySets(separatedAll))
							v1, v1Separates := b.ObtainAs[Set[A]](
								"hence, by the induction hypothesis, some open v₁ ⊇ s misses ⋃e",
								"∃v₁:set(A). v₁ ∈ T ∧ s ⊆ v₁ ∧ v₁ ∩ ⋃e = ∅",
								By(carried, rest))

							b.Take(b.TermAs[Set[A]]("v₁ ∩ v₂"))
							b.Show(
								"v₁ ∩ v₂ is open, holds s, and misses every member "+
									"of insert(w, e): w through v₂, the rest through v₁",
								BySets(v1Separates, v2Separates, topological_space.InterOpen.Read(topology).AsFact().At(v1, v2)))
						}))))
		}),
})}

// CompactSeparation — in a Hausdorff space, two disjoint compact sets lie
// in disjoint open sets.
//
// The open sets that some open set holding t misses cover s: a point x
// of s lies in the space outside t, so PointCompactSeparation puts x and
// t in disjoint open sets, and the one holding x is such a set.
// Compactness of s picks finitely many of them covering s; their union u
// is open and holds s, and SetSeparatedFromFiniteUnion meets the open
// sets holding t that miss each of them in one open set v holding t and
// missing u. As for a point, the family is named, never chosen from.
var CompactSeparation = compactSeparationThm{family.Add(registry.ProofEntry{
	Name: "CompactSeparation",
	Key:  "prop_dad69a0f221f12f6",
	Reading: "When s is empty compactness returns the empty subfamily, whose union is ∅ and " +
		"whose intersection is the whole type: u = ∅ and v = ⋃T serve, t lying in the space by " +
		"compact_in. is_topology enters for the union of the u_x and for the finite meet of the v_x.",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"hausdorff(T)",
			"compact_in(s)",
			"compact_in(t)",
			"s ∩ t = ∅",
		},
		Conclusion: "∃u v:set(A). u ∈ T ∧ v ∈ T ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅",
		Abbrev: Abbrev{
			{Name: "separatedFromT", Text: "{u:set(A) | u ∈ T ∧ ∃v:set(A). v ∈ T ∧ t ⊆ v ∧ u ∩ v = ∅}"},
		},
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			s, t *Expr[Set[A]],
			hausdorffT, compactS, compactT, disjoint Fact,
		) {
			sParts := a.Conjuncts(
				a.Unfolded(compactS, CompactInDef),
				"s lies in the space",
				"and every open cover of s has a finite subcover")
			tInSpace := a.Have(
				"t lies in the space, the first clause of its compactness",
				"t ⊆ ⋃T",
				By(compactT, CompactInDef))

			// The open sets that some open set holding t misses.
			familyOpen := a.Have(
				"the family is made of open sets",
				"«separatedFromT» ⊆ T",
				BySets())
			pointwise := a.Have(
				"a point x of s lies in the space outside t, so "+
					"PointCompactSeparation puts x in a member of the family",
				"∀x:A. x ∈ s ⇒ x ∈ ⋃«separatedFromT»",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					xIn := b.Assume()
					position := b.Have(
						"x lies in the space, as s does, and outside t, which s misses",
						"x ∈ ⋃T ∧ x ∉ t",
						BySets(xIn, sParts[0], disjoint))
					_, _, apart := b.Obtain2(
						"so open sets w ∋ x and v ⊇ t are disjoint",
						"∃w v:set(A). w ∈ T ∧ v ∈ T ∧ x ∈ w ∧ t ⊆ v ∧ w ∩ v = ∅",
						By(PointCompactSeparation, topology, hausdorffT, compactT, position))
					b.Show(
						"so w is a member of the family holding x",
						BySets(apart))
				}))
			familyCoversS := a.Have(
				"so the family covers s",
				"s ⊆ ⋃«separatedFromT»",
				BySets(pointwise))
			d, finiteSubcover := a.ObtainAs[Set[Set[A]]](
				"compactness of s at that cover: finitely many of its members already cover s",
				"∃d:set(set(A)). d ⊆ «separatedFromT» ∧ finite(d) ∧ s ⊆ ⋃d",
				By(familyOpen, familyCoversS, sParts[1].At(a.TermAs[Set[Set[A]]]("«separatedFromT»"))))
			separatedD := a.Have(
				"each member of d is one of the family, so an open set holding t misses it",
				"∀w:set(A). w ∈ d ⇒ ∃v:set(A). v ∈ T ∧ t ⊆ v ∧ v ∩ w = ∅",
				BySets(finiteSubcover))
			v, vSeparates := a.ObtainAs[Set[A]](
				"so one open set v holding t misses the union of d",
				"∃v:set(A). v ∈ T ∧ t ⊆ v ∧ v ∩ ⋃d = ∅",
				By(At(Read(SetSeparatedFromFiniteUnion, topology), t, d), tInSpace, finiteSubcover, separatedD))

			a.Take(a.TermAs[Set[A]]("⋃d"))
			a.Take(v)
			a.Show(
				"the union of d is open and holds s, v is open and holds t, and the two are disjoint",
				BySets(vSeparates, finiteSubcover, topological_space.UnionsOpen.Read(topology).At(d)))
		}),
})}

// CompactClosed — in a Hausdorff space, a compact set is closed.
//
// A closed set lies in the space with an open complement there. That k
// lies in the space is the first clause of compactness. Its complement
// is open by the pointwise criterion: it lies in the space, and each of
// its points x — a point of the space outside k — has by SeparatedFromCompact an
// open neighbourhood u missing k, which therefore lies inside the
// complement.
var CompactClosed = compactClosedThm{family.Add(registry.ProofEntry{
	Name: "CompactClosed",
	Key:  "prop_e25003c3a8d0ba56",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀k:set(A).",
		Hypotheses: []string{
			"hausdorff(T)",
			"compact_in(k)",
		},
		Conclusion: "closed_in(k)",
	},
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], k *Expr[Set[A]], _ Fact) {
			// A closed set lies in the space with an open complement there;
			// the assumption reads as its two clauses.
			a.Do(Unfold(topological_space.ClosedInDef))
			hausdorffT := a.Hyp("hausdorff(T)")
			compactK := a.Hyp("compact_in(k)")

			a.Do(SplitConj(
				Case(
					"k lies in the space, the first clause of compactness",
					By(compactK, CompactInDef)),
				Case(
					"the complement of k in the space is open, by the pointwise criterion",
					Simp(Fwd(topological_space.OpenPointwise)),
					Derive(func(b *Argument) {
						b.Fix("x")
						xIn := b.Assume() // x ∈ ⋃T ∖ k
						position := b.Have(
							"x is a point of the space outside k",
							"x ∈ ⋃T ∧ x ∉ k",
							BySets(xIn))
						u, uSeparates := b.Obtain(
							"so some open neighbourhood u of x misses k",
							"∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ k = ∅",
							By(SeparatedFromCompact, topology, hausdorffT, compactK, position))
						b.Take(u)
						b.Show(
							"u is open, lies inside the complement — in the space, being open, and missing k — and holds x",
							BySets(uSeparates))
					})),
			))
		}),
})}

// CompactInSubtopology — a subset k of s is compact in the subspace s
// exactly when it is compact in the whole space. The open sets of the
// subspace are the traces w ∩ s of the open sets w of T, and its points
// are the points of the space in s; k lies in s throughout. An open
// cover c of k in T is traced to an open cover of k in the subspace, since
// cutting to s loses no point of k; finitely many traces cover k, they
// are cut from finitely many members of c, and those cover k, each
// containing its trace. Conversely, an open cover c of k in the subspace
// is traced by the open sets whose trace is a member of c: they cover k,
// since each member of c is such a trace, so finitely many of them cover
// k, and their traces are finitely many members of c covering k. Naming
// that family avoids choosing, for each member of c, an open set it is
// the trace of.
var CompactInSubtopology = compactInSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "CompactInSubtopology",
	Key:  "prop_2369049dd0d01c5e",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s k:set(A).",
		Hypotheses: []string{
			"k ⊆ s",
		},
		Conclusion: "compact_in(subtopology(T, s), k) ⇔ compact_in(T, k)",
		Abbrev: Abbrev{
			// The traces on s of a cover c and of a subfamily d of it, and the
			// open sets whose trace is a member of c.
			{Name: "tracesOfC", Text: "image(λw:set(A). w ∩ s, c)"},
			{Name: "tracesOfD", Text: "image(λw:set(A). w ∩ s, d)"},
			{Name: "tracedIntoC", Text: "{w:set(A) | w ∈ T ∧ w ∩ s ∈ c}"},
		},
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s, k *Expr[Set[A]], inside Fact) {
			// Cutting an open set down to s, the map whose image is the
			// subspace topology.
			cut := a.TermAs[Fun[Set[A], Set[A]]]("λw:set(A). w ∩ s")
			a.Iff()
			a.Forward(
				"compact in the subspace: the traces of an open cover of k in T cover "+
					"it, and finitely many of them are cut from finitely many members",
				func(b *Argument, compactInSubspace Fact) {
					parts := b.Conjuncts(
						b.Unfolded(compactInSubspace, CompactInDef),
						"k lies in the subspace",
						"and every open cover of k in the subspace has a finite subcover")
					inSubspace, subcoverInSubspace := parts[0], parts[1]
					b.Do(Unfold(CompactInDef), SplitConj(
						Case(
							"k lies in the space, whose part in s is the space of the subspace",
							BySets(inSubspace, topological_space.SubtopologySpace.At(T, s))),
						Case(
							"every open cover of k in T has a finite subcover",
							Derive(func(inner *Argument) {
								cover := inner.FixAs[Set[Set[A]]]("c")
								covering := inner.Assume() // c is a family of open sets of T covering k
								traces := inner.TermAs[Set[Set[A]]]("«tracesOfC»")
								tracesOpen := inner.Have(
									"the traces of the members of c are open in the subspace",
									"«tracesOfC» ⊆ subtopology(T, s)",
									By(
										Normalized,
										covering,
										topological_space.SubtopologyDef.At(T, s),
										set_image.ImageSubset.At(cut, cover, T)))
								tracesCoverK := inner.Have(
									"and they cover k, which lies in s",
									"k ⊆ ⋃«tracesOfC»",
									BySets(inside, covering))
								e, fewTraces := inner.ObtainAs[Set[Set[A]]](
									"so finitely many traces e cover k, by compactness in the subspace",
									"∃e:set(set(A)). e ⊆ «tracesOfC» ∧ finite(e) ∧ k ⊆ ⋃e",
									By(tracesOpen, tracesCoverK, subcoverInSubspace.At(traces)))
								d, cutFrom := inner.ObtainAs[Set[Set[A]]](
									"and they are cut from finitely many members d of c",
									"∃d:set(set(A)). finite(d) ∧ e = image(λw:set(A). w ∩ s, d) ∧ d ⊆ c",
									By(finite_set.FiniteSubsetImage.At(cut, cover, e), fewTraces))
								fromD := inner.Conjuncts(
									cutFrom,
									"d is finite",
									"e is the family of traces of the members of d",
									"d lies in c")
								within := inner.Have(
									"a trace lies in the member of d it is cut from",
									"⋃e ⊆ ⋃d",
									fromD[1].Rw(),
									BySets())
								covered := inner.Have(
									"so d covers k",
									"k ⊆ ⋃d",
									BySets(fewTraces, within))
								inner.Take(d)
								inner.Show(
									"d is a finite subfamily of c covering k",
									By(fromD[0], fromD[2], covered))
							})),
					))
				})
			a.Backward(
				"compact in T: the open sets tracing into an open cover of k in the "+
					"subspace cover k, and finitely many of them trace a finite subcover",
				func(b *Argument, compact Fact) {
					parts := b.Conjuncts(
						b.Unfolded(compact, CompactInDef),
						"k lies in the space",
						"and every open cover of k in T has a finite subcover")
					inSpace, subcover := parts[0], parts[1]
					b.Do(Unfold(CompactInDef), SplitConj(
						Case(
							"k lies in the space and in s, the space of the subspace",
							BySets(inside, inSpace, topological_space.SubtopologySpace.At(T, s))),
						Case(
							"every open cover of k in the subspace has a finite subcover",
							Derive(func(inner *Argument) {
								inner.FixAs[Set[Set[A]]]("c")
								covering := inner.Assume() // c is a family of open sets of the subspace covering k

								liftsOpen := inner.Have(
									"they form a family of open sets",
									"«tracedIntoC» ⊆ T",
									BySets())
								eachInside := inner.Have(
									"a member of c is the trace of an open set, which is one of them and contains it",
									"∀t:set(A). t ∈ subtopology(T, s) ⇒ t ∈ c ⇒ t ⊆ ⋃«tracedIntoC»",
									Simp(Fwd(topological_space.SubtopologyDef), Fwd(set_image.ForallInImage)),
									BySets())
								liftsCoverK := inner.Have(
									"so they cover k, as c does",
									"k ⊆ ⋃«tracedIntoC»",
									BySets(covering, eachInside))
								d, finiteSubcover := inner.ObtainAs[Set[Set[A]]](
									"by compactness in T, finitely many of them, d, cover k",
									"∃d:set(set(A)). d ⊆ «tracedIntoC» ∧ finite(d) ∧ k ⊆ ⋃d",
									By(liftsOpen, liftsCoverK, subcover.At(inner.TermAs[Set[Set[A]]]("«tracedIntoC»"))))
								inC := inner.Have(
									"each member of d is one of the family, so its trace is a member of c",
									"∀w:set(A). w ∈ d ⇒ w ∩ s ∈ c",
									BySets(finiteSubcover))
								tracesInC := inner.Have(
									"so the traces of the members of d are members of c",
									"«tracesOfD» ⊆ c",
									Unfold(set_basic.SubsetDef),
									Simp(Fwd(set_image.ForallInImage)),
									By(inC))
								tracesCover := inner.Have(
									"and they cover k, which lies in s",
									"k ⊆ ⋃«tracesOfD»",
									BySets(inside, finiteSubcover))
								inner.Take(inner.TermAs[Set[Set[A]]]("«tracesOfD»"))
								inner.Show(
									"the traces of d are finitely many members of c covering k",
									By(tracesInC, finite_set.FiniteImage.At(cut, d), finiteSubcover, tracesCover))
							})),
					))
				})
		}),
})}

// CompactInOwnSubtopology — a compact set is compact as a subspace of
// itself: it lies inside itself, so CompactInSubtopology above reads its
// compactness in the subspace as its compactness in the whole space.
var CompactInOwnSubtopology = compactInOwnSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "CompactInOwnSubtopology",
	Key:  "prop_fe31b7470314766f",
	Build: family.Theorem(Statement{
		Binders:    "∀T:set(set(A)). ∀k:set(A).",
		Hypotheses: []string{"compact_in(T, k)"},
		Conclusion: "compact_in(subtopology(T, k), k)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], k *Expr[Set[A]], compactK Fact) {
			a.Show(
				"k lies inside itself, and a subset of the subspace is compact there as it is in the space",
				By(compactK, CompactInSubtopology.At(T, k, k), set_order.SubsetRefl.At(k)))
		}),
})}

// ---------------------------------------------------------------------------
// Small compact sets, and what compactness survives further
// ---------------------------------------------------------------------------

// EmptyCompact — the empty set is compact: it lies in every space, and the
// empty subfamily of any cover is finite and covers it.
var EmptyCompact = emptyCompactThm{family.Add(registry.ProofEntry{
	Name: "EmptyCompact",
	Key:  "prop_75bde691306f2d27",
	Build: family.Theorem("∀T:set(set(A)). compact_in(T, ∅)",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Do(Unfold(CompactInDef), SplitConj(
				Case(
					"the empty set lies in the space",
					BySets()),
				Case(
					"every cover of the empty set has a finite subcover, the empty one",
					Derive(func(b *Argument) {
						b.Fix("c")
						b.Assume() // c is a family of open sets covering ∅
						b.Take(b.TermAs[Set[Set[A]]]("∅"))
						b.Show(
							"the empty family lies in c, is finite, and covers the empty set",
							BySets(finite_set.FiniteRules))
					})),
			))
		}),
})}

// FiniteCompact — a finite set of points of the space is compact: given a
// cover, pick for each point of k a member holding it; the members picked
// are the image of k, so finitely many, and they cover k.
var FiniteCompact = finiteCompactThm{family.Add(registry.ProofEntry{
	Name: "FiniteCompact",
	Key:  "prop_c63542e90a986486",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀k:set(A).",
		Hypotheses: []string{
			"finite(k)",
			"k ⊆ ⋃T",
		},
		Conclusion: "compact_in(T, k)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], k *Expr[Set[A]], finiteK, inSpace Fact) {
			a.Do(Unfold(CompactInDef), SplitConj(
				Case(
					"k lies in the space",
					By(inSpace)),
				Case(
					"every open cover of k has a finite subcover",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[A]]]("c")
						covering := b.Assume() // c is a family of open sets covering k
						f, picks := b.ObtainAs[Fun[A, Set[A]]](
							"choosing for each point x of k a member f(x) of c holding it",
							"∃f:A → set(A). ∀x:A. x ∈ k ⇒ f(x) ∈ c ∧ x ∈ f(x)",
							BySets(covering))
						b.Take(b.TermAs[Set[Set[A]]]("image(f, k)"))
						b.Show(
							"the members picked, the image of the finite k under f, lie in c and cover k",
							Simp(Fwd(set_image.UnionsImage)),
							BySets(finiteK, picks, finite_set.FiniteImage.At(f, k)))
					})),
			))
		}),
})}

// CompactUnions — finitely many compact sets unite to a compact set. By
// induction on the family: no sets unite to the empty set, which is
// compact, and one more compact set x unites with the union of the rest,
// compact by the induction hypothesis, to a union of two compact sets.
var CompactUnions = compactUnionsThm{family.Add(registry.ProofEntry{
	Name: "CompactUnions",
	Key:  "prop_3022330d7a088cbb",
	Build: family.Theorem(Statement{
		Binders: "∀T f:set(set(A)).",
		Hypotheses: []string{
			"finite(f)",
			"∀k:set(A). k ∈ f ⇒ compact_in(T, k)",
		},
		Conclusion: "compact_in(T, ⋃f)",
	},
		func(a *Argument, T, f *Expr[Set[Set[A]]], finite, compactMembers Fact) {
			a.Show(
				"the induction carries the property to f, which is finite with compact members",
				ByInduction(finite_set.FiniteInduct, finite, Generalizing(compactMembers),
					Case(
						"no sets unite to the empty set, which is compact",
						By(EmptyCompact, set_algebra.UnionsEmpty)),
					Case(
						"one more compact set x unites with the union of the rest, compact by the induction hypothesis",
						Derive(func(b *Argument) {
							x := b.FixAs[Set[A]]()
							b.FixAs[Set[Set[A]]]("s")
							carried := b.Assume() // the induction hypothesis, itself conditional
							given := b.Assume()   // every member of insert(x, s) is compact
							members := b.Have(
								"x is compact, and so is every member of s",
								"compact_in(T, x) ∧ (∀k:set(A). k ∈ s ⇒ compact_in(T, k))",
								By(given, set_basic.ForallInInsert))
							b.Show(
								"⋃insert(x, s) is x ∪ ⋃s, a union of two compact sets",
								Simp(Fwd(set_algebra.UnionsInsert)),
								By(carried, members, CompactUnion.At(T, x, b.TermAs[Set[A]]("⋃s"))))
						}))))
		}),
})}

// CompactInterClosed — a compact set meets a closed set in a compact set:
// an open cover of k ∩ c, with the open complement ⋃T ∖ c of c added,
// covers k; finitely many of its members cover k, and those of them taken
// from the cover still cover k ∩ c, which the complement misses.
var CompactInterClosed = compactInterClosedThm{family.Add(registry.ProofEntry{
	Name: "CompactInterClosed",
	Key:  "prop_64e68d350eae50d2",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀k c:set(A).",
		Hypotheses: []string{
			"compact_in(T, k)",
			"closed_in(T, c)",
		},
		Conclusion: "compact_in(T, k ∩ c)",
		Abbrev: Abbrev{
			{Name: "withComplement", Text: "insert(⋃T ∖ c, v)"},
		},
	},
		func(a *Argument, T *Expr[Set[Set[A]]], k, c *Expr[Set[A]], compactK, closedC Fact) {
			kParts := a.Conjuncts(
				a.Unfolded(compactK, CompactInDef),
				"k lies in the space",
				"and every open cover of k has a finite subcover")
			cParts := a.Conjuncts(
				a.Unfolded(closedC, topological_space.ClosedInDef),
				"c lies in the space",
				"and its complement there is open")
			a.Do(Unfold(CompactInDef), SplitConj(
				Case(
					"k ∩ c lies in the space, as k does",
					BySets(kParts[0])),
				Case(
					"every open cover of k ∩ c has a finite subcover",
					Derive(func(b *Argument) {
						v := b.FixAs[Set[Set[A]]]("v")
						covering := b.Assume() // v is a family of open sets covering k ∩ c
						enlargedOpen := b.Have(
							"with the complement of c added, the family is still made of open sets",
							"«withComplement» ⊆ T",
							By(covering, cParts[1], set_order.InsertSubset))
						enlargedCovers := b.Have(
							"and it covers k: a point of k outside c lies in the complement",
							"k ⊆ ⋃«withComplement»",
							Simp(Fwd(set_algebra.UnionsInsert)),
							BySets(covering, kParts[0]))
						e, finiteSubcover := b.ObtainAs[Set[Set[A]]](
							"by compactness of k, finitely many of its members e cover k",
							"∃e:set(set(A)). e ⊆ «withComplement» ∧ finite(e) ∧ k ⊆ ⋃e",
							By(enlargedOpen, enlargedCovers, kParts[1].At(b.TermAs[Set[Set[A]]]("«withComplement»"))))
						b.Take(b.TermAs[Set[Set[A]]]("e ∩ v"))
						b.Show(
							"the members of e taken from v are finitely many and cover k ∩ c, which the complement misses",
							BySets(finiteSubcover, finite_set.FiniteInter.At(e, v)))
					})),
			))
		}),
})}

// CompactInter — in a Hausdorff space two compact sets meet in a
// compact set: the second is closed (CompactClosed), and a compact set
// meets a closed set in a compact set (CompactInterClosed).
var CompactInter = compactInterThm{family.Add(registry.ProofEntry{
	Name: "CompactInter",
	Key:  "prop_cc4ee1e0adc44219",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"hausdorff(T)",
			"compact_in(s)",
			"compact_in(t)",
		},
		Conclusion: "compact_in(s ∩ t)",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			s, t *Expr[Set[A]],
			hausdorffT, compactS, compactT Fact,
		) {
			a.Show(
				"t is closed, being compact in a Hausdorff space, and s meets it in a compact set",
				By(CompactInterClosed, compactS, CompactClosed, topology, hausdorffT, compactT))
		}),
})}

// CompactNest — in a compact space a decreasing sequence of non-empty
// closed sets has a common point.
//
// The sequence decreases all the way: c(n) lies in c(m) whenever m ≤ n
// (order.DecreasingFromSteps). Finitely many of the c(n) are those at a
// finite set of indices, all at most some N, so they all hold c(N), which
// is non-empty and lies in the space. The space thus meets the intersection
// of any finitely many of the closed sets c(n), and by the finite
// intersection property (CompactFip) it meets the intersection of all.
var CompactNest = compactNestThm{family.Add(registry.ProofEntry{
	Name: "CompactNest",
	Key:  "prop_e19118f0c4c8df23",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀c:(num → set(A)).",
		Hypotheses: []string{
			"compact_in(T, ⋃T)",
			"∀n:num. closed_in(T, c(n)) ∧ ¬(c(n) = ∅) ∧ c(n + 1) ⊆ c(n)",
		},
		Conclusion: "¬(⋂image(c, 𝕌) = ∅)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], c *Arrow[Nat, Set[A]], compactSpace, nested Fact) {
			closedTerms := a.Have(
				"the sets of the sequence are closed",
				"∀b:set(A). b ∈ image(c, 𝕌) ⇒ closed_in(T, b)",
				Simp(Fwd(set_image.ForallInImage)),
				By(nested))
			finitelyMany := a.Have(
				"the space meets the intersection of finitely many of them, which holds the one of largest index",
				"∀g:set(set(A)). finite(g) ∧ g ⊆ image(c, 𝕌) ⇒ ¬(⋃T ∩ ⋂g = ∅)",
				Derive(func(b *Argument) {
					g := b.FixAs[Set[Set[A]]]("g")
					fewTerms := b.Assume() // g is finite and made of sets of the sequence
					s, atIndices := b.ObtainAs[Set[Nat]](
						"g is made of the c(n) for n in a finite set s of indices",
						"∃s:set(num). finite(s) ∧ g = image(c, s) ∧ s ⊆ 𝕌",
						By(finite_set.FiniteSubsetImage.At(c, b.TermAs[Set[Nat]]("𝕌"), g), fewTerms))
					indices := b.Conjuncts(
						atIndices,
						"s is finite",
						"g is made of the c(n) for n in s",
						"s is a set of numbers")
					N, bounded := b.ObtainAs[Nat](
						"the finitely many indices are all at most some N",
						"∃N:num. s ⊆ 0 .. N",
						By(num_segment.FiniteIffBounded.At(s), indices[0]))
					inside := b.Have(
						"so c(N) lies in each set of g",
						"c(N) ⊆ ⋂g",
						indices[1].Rw(),
						Simp(Fwd(set_image.IntersImage)),
						BySets(nested, bounded, At(order.DecreasingFromSteps, c)))
					b.Show(
						"and c(N) is non-empty and lies in the space, being closed",
						BySets(inside, nested.At(N), topological_space.ClosedInDef.At(T, c.Apply(N))))
				}))
			meets := a.Have(
				"so by the finite intersection property the space meets the intersection of the whole sequence",
				"¬(⋃T ∩ ⋂image(c, 𝕌) = ∅)",
				By(compactSpace, closedTerms, finitelyMany, CompactFip))
			a.Show(
				"which is therefore not empty",
				BySets(meets))
		}),
})}

// CompactLimitPoint — an infinite subset of a compact set has a limit
// point in it.
//
// Suppose no point of k is a limit point of s. Then each point x of k has
// an open neighbourhood holding no point of s but x, so the open sets
// meeting s in finitely many points cover k. Finitely many of them, d,
// cover k, so s lies in the union of its traces on the members of d —
// finitely many finite sets — and s is finite. No choice function enters:
// the open sets are named by the family, never chosen point by point.
var CompactLimitPoint = compactLimitPointThm{family.Add(registry.ProofEntry{
	Name: "CompactLimitPoint",
	Key:  "prop_3bc457036a486bde",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀k s:set(A).",
		Hypotheses: []string{
			"compact_in(T, k)",
			"s ⊆ k",
			"infinite(s)",
		},
		Conclusion: "∃x:A. x ∈ k ∧ x ∈ derived_set(T, s)",
		Abbrev: Abbrev{
			{Name: "meetsSFinitely", Text: "{u:set(A) | u ∈ T ∧ finite(u ∩ s)}"},
			{Name: "tracesOfD", Text: "image(λu:set(A). u ∩ s, d)"},
		},
	},
		func(a *Argument, T *Expr[Set[Set[A]]], k, s *Expr[Set[A]], compactK, inside, infiniteS Fact) {
			parts := a.Conjuncts(
				a.Unfolded(compactK, CompactInDef),
				"k lies in the space",
				"and every open cover of k has a finite subcover")
			// Cutting an open set down to its points of s.
			trace := a.TermAs[Fun[Set[A], Set[A]]]("λu:set(A). u ∩ s")

			noLimitPoint := a.SupposeNot() // no point of k is a limit point of s
			pointwise := a.Have(
				"a point x of k is no limit point of s, so an open set around "+
					"x holds no point of s but x, and it is a member of the family",
				"∀x:A. x ∈ k ⇒ x ∈ ⋃«meetsSFinitely»",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					notLimit := b.Have(
						"x is no limit point of s",
						"x ∉ derived_set(T, s)",
						By(noLimitPoint, xIn))
					inSpace := b.Have(
						"x lies in the space, as k does",
						"x ∈ ⋃T",
						BySets(xIn, parts[0]))
					_, isolated := b.ObtainAs[Set[A]](
						"so some open u around x holds no point of s but x",
						"∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ s ⊆ {x}",
						BySets(b.Unfolded(notLimit, topological_space.DerivedSetDef), inSpace))
					b.Show(
						"u meets s inside the finite {x}, so in finitely many points, and it holds x",
						BySets(
							isolated,
							finite_set.FiniteSubset.At(b.TermAs[Set[A]]("u ∩ s"), b.TermAs[Set[A]]("{x}")),
							finite_set.FiniteSing.At(x)))
				}))
			familyOpen := a.Have(
				"the family is made of open sets",
				"«meetsSFinitely» ⊆ T",
				BySets())
			familyCoversK := a.Have(
				"so the family covers k",
				"k ⊆ ⋃«meetsSFinitely»",
				BySets(pointwise))
			d, finiteSubcover := a.ObtainAs[Set[Set[A]]](
				"compactness of k at that cover: finitely many of its members already cover k",
				"∃d:set(set(A)). d ⊆ «meetsSFinitely» ∧ finite(d) ∧ k ⊆ ⋃d",
				By(familyOpen, familyCoversK, parts[1].At(a.TermAs[Set[Set[A]]]("«meetsSFinitely»"))))
			traces := a.TermAs[Set[Set[A]]]("«tracesOfD»")
			tracesFinite := a.Have(
				"each member of d is one of the family, so its trace on s is finite",
				"∀t:set(A). t ∈ «tracesOfD» ⇒ finite(t)",
				Simp(Fwd(set_image.ForallInImage)),
				BySets(finiteSubcover))
			tracesCoverS := a.Have(
				"and s, inside k, lies in the union of its traces on the members of d",
				"s ⊆ ⋃«tracesOfD»",
				Simp(Fwd(set_image.UnionsImage)),
				BySets(inside, finiteSubcover))
			unionFinite := a.Have(
				"finitely many finite traces unite to a finite set",
				"finite(⋃«tracesOfD»)",
				By(
					tracesFinite,
					finiteSubcover,
					finite_set.FiniteImage.At(trace, d),
					finite_set.FiniteUnions.At(traces)))
			a.Show(
				"so s, inside it, is finite, which it is not",
				By(
					infiniteS,
					finite_set.InfiniteDef.At(s),
					unionFinite,
					tracesCoverS,
					finite_set.FiniteSubset.At(s, a.TermAs[Set[A]]("⋃«tracesOfD»"))))
		}),
})}

// DiscreteCompactIffFinite — the compact sets of a discrete space are its
// finite subsets. A finite set of points of the space is compact
// (FiniteCompact), and the space of the discrete topology on X is X.
// Conversely the singletons of the points of a compact k are open and
// cover k; finitely many of them do, the singletons of finitely many points
// j of k, and k lies in j, so it is finite.
var DiscreteCompactIffFinite = discreteCompactIffFiniteThm{family.Add(registry.ProofEntry{
	Name: "DiscreteCompactIffFinite",
	Key:  "prop_c3db80ff1abd9460",
	Build: family.Theorem("∀X k:set(A). compact_in({t:set(A) | t ⊆ X}, k) ⇔ finite(k) ∧ k ⊆ X",
		func(a *Argument, X, k *Expr[Set[A]]) {
			// A point's singleton, the open set the discrete topology has
			// around it.
			singleton := a.TermAs[Fun[A, Set[A]]]("λx:A. {x}")
			a.Iff()
			a.Forward(
				"compact: finitely many of the open singletons of its points "+
					"cover k, and they are the singletons of finitely many points",
				func(b *Argument, compact Fact) {
					parts := b.Conjuncts(
						b.Unfolded(compact, CompactInDef),
						"k lies in the space",
						"and every open cover of k has a finite subcover")
					inX := b.Have(
						"k lies in X, the space of the discrete topology on X",
						"k ⊆ X",
						By(parts[0], topological_space.DiscreteSpace.At(X)))
					singletonsOpen := b.Have(
						"the singletons of the points of k are open, being subsets of X",
						"image(λx:A. {x}, k) ⊆ {t:set(A) | t ⊆ X}",
						BySets(inX))
					singletonsCover := b.Have(
						"and they cover k",
						"k ⊆ ⋃image(λx:A. {x}, k)",
						Simp(Fwd(set_image.UnionsImage)),
						BySets())
					d, fewSingletons := b.ObtainAs[Set[Set[A]]](
						"by compactness of k, finitely many of them, d, cover k",
						"∃d:set(set(A)). d ⊆ image(λx:A. {x}, k) ∧ finite(d) ∧ k ⊆ ⋃d",
						By(singletonsOpen, singletonsCover, parts[1].At(b.TermAs[Set[Set[A]]]("image(λx:A. {x}, k)"))))
					j, fromJ := b.ObtainAs[Set[A]](
						"they are the singletons of finitely many points j of k",
						"∃j:set(A). finite(j) ∧ d = image(λx:A. {x}, j) ∧ j ⊆ k",
						By(fewSingletons, finite_set.FiniteSubsetImage.At(singleton, k, d)))
					inJ := b.Have(
						"so k lies in j, the union of the singletons of its points",
						"k ⊆ j",
						BySets(fromJ, fewSingletons, set_image.UnionsImage.At(singleton, j)))
					b.Show(
						"so k, inside the finite j, is finite, and it lies in X",
						By(inX, inJ, fromJ, finite_set.FiniteSubset.At(k, j)))
				})
			a.Backward(
				"finite: a finite set of points of the space, which is X, is compact",
				func(b *Argument, finiteInX Fact) {
					b.Show(
						"FiniteCompact, the space of the discrete topology on X being X",
						By(
							finiteInX,
							FiniteCompact.At(b.TermAs[Set[Set[A]]]("{t:set(A) | t ⊆ X}"), k),
							topological_space.DiscreteSpace.At(X)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Locally compact spaces
// ---------------------------------------------------------------------------

// CompactImpLocallyCompact — a compact space is locally compact: the space
// itself is an open neighbourhood of each of its points, and it lies in a
// compact set, itself.
var CompactImpLocallyCompact = compactImpLocallyCompactThm{family.Add(registry.ProofEntry{
	Name: "CompactImpLocallyCompact",
	Key:  "prop_a94153e5b917da9",
	Build: topological_space.IsTopology.Law(Statement{
		Hypotheses: []string{
			"compact_in(⋃T)",
		},
		Conclusion: "locally_compact_space(T)",
	},
		func(a *Argument, topology topological_space.IsTopologyFact[on.T], compactSpace Fact) {
			a.Do(Unfold(LocallyCompactSpaceDef))
			a.FixAs[A]("x")
			xIn := a.Assume() // x is a point of the space
			space := a.TermAs[Set[A]]("⋃T")
			a.Take(space)
			a.Take(space)
			a.Show(
				"the space is open, compact, holds x, and lies in itself",
				BySets(topological_space.SpaceOpen.Read(topology), compactSpace, xIn))
		}),
})}

// LocallyCompactClosedSubtopology — a closed subspace of a locally
// compact space is locally compact. A point x of the subspace is a point
// of the space in c, so it has an open neighbourhood u inside a compact k.
// The trace u ∩ c is open in the subspace and holds x; it lies in k ∩ c,
// the meet of a compact set with a closed one, which is compact, and
// compact in the subspace too, lying in c (CompactInSubtopology).
var LocallyCompactClosedSubtopology = locallyCompactClosedSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "LocallyCompactClosedSubtopology",
	Key:  "prop_7f66d927e9e9caca",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀c:set(A).",
		Hypotheses: []string{
			"locally_compact_space(T)",
			"closed_in(T, c)",
		},
		Conclusion: "locally_compact_space(subtopology(T, c))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], c *Expr[Set[A]], locallyCompact, closedC Fact) {
			neighbourhoods := a.Unfolded(locallyCompact, LocallyCompactSpaceDef)
			a.Do(Unfold(LocallyCompactSpaceDef))
			x := a.FixAs[A]("x")
			xIn := a.Assume() // x is a point of the subspace
			position := a.Have(
				"x is a point of the space in c, which is what the points of the subspace are",
				"x ∈ ⋃T ∧ x ∈ c",
				BySets(xIn, topological_space.SubtopologySpace.At(T, c)))
			u, k, around := a.Obtain2As[Set[A], Set[A]](
				"as a point of the space, x has an open neighbourhood u inside a compact k",
				"∃u k:set(A). u ∈ T ∧ compact_in(T, k) ∧ x ∈ u ∧ u ⊆ k",
				By(neighbourhoods.At(x), position))
			compactTrace := a.Have(
				"k ∩ c is compact, the meet of a compact set with a "+
					"closed one, and so compact in the subspace, lying in c",
				"compact_in(subtopology(T, c), k ∩ c)",
				By(
					around,
					closedC,
					set_order.InterSubset.At(c, k),
					CompactInterClosed.At(T, k, c),
					CompactInSubtopology.At(T, c, a.TermAs[Set[A]]("k ∩ c"))))
			a.Take(a.TermAs[Set[A]]("u ∩ c"))
			a.Take(a.TermAs[Set[A]]("k ∩ c"))
			a.Show(
				"the trace u ∩ c is open in the subspace, holds x, and lies in the compact k ∩ c",
				BySets(compactTrace, position, around, topological_space.TraceOpen.At(T, c, u)))
		}),
})}

// LocallyCompactHausdorffNeighbourhood — in a locally compact Hausdorff
// space every open neighbourhood w of a point x holds an open
// neighbourhood of x whose closure is compact and lies in w.
//
// x has an open neighbourhood u inside a compact k. The part of k outside
// u ∩ w, where k meets the closed complement of the open u ∩ w, is
// compact and misses x, so PointCompactSeparation puts x and that part in
// disjoint open sets p and q. Let v = p ∩ (u ∩ w): it is open and holds x.
// Its closure lies in k, which is closed in a Hausdorff space, and in the
// closed complement of q, which holds p (ClosureMinimal, twice); a point of
// k outside q lies in u ∩ w, so the closure lies in w. And as a closed set
// inside the compact k, the closure is compact.
var LocallyCompactHausdorffNeighbourhood = locallyCompactHausdorffNeighbourhoodThm{family.Add(registry.ProofEntry{
	Name: "LocallyCompactHausdorffNeighbourhood",
	Key:  "prop_b5ff6630eef42a81",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀w:set(A). ∀x:A.",
		Hypotheses: []string{
			"hausdorff(T)",
			"locally_compact_space(T)",
			"w ∈ T",
			"x ∈ w",
		},
		Conclusion: "∃v:set(A). v ∈ T ∧ x ∈ v ∧ compact_in(closure(v)) ∧ closure(v) ⊆ w",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			w *Expr[Set[A]],
			x *Expr[A],
			hausdorffT, locallyCompact, wOpen, xInW Fact,
		) {
			T := a.TermAs[Set[Set[A]]]("T")
			inSpace := a.Have(
				"x lies in the space, in the open w",
				"x ∈ ⋃T",
				BySets(wOpen, xInW))
			u, k, around := a.Obtain2As[Set[A], Set[A]](
				"x has an open neighbourhood u inside a compact k",
				"∃u k:set(A). u ∈ T ∧ compact_in(k) ∧ x ∈ u ∧ u ⊆ k",
				By(locallyCompact, LocallyCompactSpaceDef, inSpace))
			meet := a.TermAs[Set[A]]("u ∩ w")
			meetOpen := a.Have(
				"u ∩ w is open",
				"u ∩ w ∈ T",
				By(around, wOpen, topological_space.InterOpen.Read(topology).AsFact().At(u, w)))

			// The part of k outside u ∩ w, and two open sets keeping x apart
			// from it.
			rest := a.TermAs[Set[A]]("k ∩ (⋃T ∖ (u ∩ w))")
			restCompact := a.Have(
				"the part of k outside u ∩ w is compact: there k meets "+
					"the complement of the open u ∩ w, which is closed",
				"compact_in(k ∩ (⋃T ∖ (u ∩ w)))",
				By(
					meetOpen,
					around,
					topological_space.OpenClosedComplement.At(T, meet),
					CompactInterClosed.At(T, k, a.TermAs[Set[A]]("⋃T ∖ (u ∩ w)"))))
			outside := a.Have(
				"x lies in u ∩ w, so outside that part",
				"x ∉ k ∩ (⋃T ∖ (u ∩ w))",
				BySets(xInW, around))
			p, q, apart := a.Obtain2As[Set[A], Set[A]](
				"so x and that part lie in disjoint open sets p and q",
				"∃p q:set(A). p ∈ T ∧ q ∈ T ∧ x ∈ p ∧ k ∩ (⋃T ∖ (u ∩ w)) ⊆ q ∧ p ∩ q = ∅",
				By(PointCompactSeparation.Read(topology).At(rest, x), hausdorffT, restCompact, inSpace, outside))

			v, vDef := a.LetAs[Set[A]]("v", "p ∩ (u ∩ w)")
			vOpen := a.Have(
				"v is open, a meet of open sets",
				"v ∈ T",
				By(
					Normalized,
					vDef,
					apart,
					meetOpen,
					topological_space.InterOpen.Read(topology).AsFact().At(p, meet)))
			inK := a.Have(
				"v lies in u, so in k, which is closed, being compact in a Hausdorff space; so does its closure",
				"closure(v) ⊆ k",
				BySets(
					vDef,
					hausdorffT,
					around,
					CompactClosed.Read(topology).At(k),
					topological_space.ClosureMinimal.At(T, v, k)))
			offQ := a.Have(
				"v lies in p, which misses q",
				"v ⊆ ⋃T ∖ q",
				BySets(vDef, apart))
			closureOffQ := a.Have(
				"so its closure misses q too, the complement of the open q being closed",
				"closure(v) ⊆ ⋃T ∖ q",
				By(
					apart,
					topological_space.OpenClosedComplement.At(T, q),
					offQ,
					topological_space.ClosureMinimal.At(T, v, a.TermAs[Set[A]]("⋃T ∖ q"))))
			inW := a.Have(
				"a point of k outside q lies in u ∩ w, so the closure of v lies in w",
				"closure(v) ⊆ w",
				BySets(inK, closureOffQ, apart))
			compactClosure := a.Have(
				"the closure of v is closed and lies in the compact k, so it is compact",
				"compact_in(closure(v))",
				BySets(
					around,
					inK,
					vOpen,
					topological_space.ClosureClosed.Read(topology).At(v),
					ClosedSubsetCompact.At(T, k, a.TermAs[Set[A]]("closure(v)"))))
			a.Take(v)
			a.Show(
				"v is open and holds x, and its closure is compact and lies in w",
				BySets(vDef, compactClosure, vOpen, inW, around, apart))
		}),
})}

// LocallyCompactOpenSubtopology — an open subspace of a locally compact
// Hausdorff space is locally compact. A point x of the subspace is a point
// of the space in u, so it has an open neighbourhood v whose closure is
// compact and lies in u (LocallyCompactHausdorffNeighbourhood). v lies in
// its closure, so in u, which makes it open in the subspace; and the
// closure, lying in u, is compact in the subspace too
// (CompactInSubtopology).
var LocallyCompactOpenSubtopology = locallyCompactOpenSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "LocallyCompactOpenSubtopology",
	Key:  "prop_5f6ac31e8511c129",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀u:set(A).",
		Hypotheses: []string{
			"hausdorff(T)",
			"locally_compact_space(T)",
			"u ∈ T",
		},
		Conclusion: "locally_compact_space(subtopology(T, u))",
	},
		func(
			a *Argument,
			topology topological_space.IsTopologyFact[on.T],
			u *Expr[Set[A]],
			hausdorffT, locallyCompact, uOpen Fact,
		) {
			T := a.TermAs[Set[Set[A]]]("T")
			uMember := a.MemberOf[on.T](u, uOpen)
			// The subspace's local compactness, read by its definition; the
			// space's own is cited below as it stands.
			a.Do(Simp(Fwd(LocallyCompactSpaceDef)))
			x := a.FixAs[A]("x")
			xIn := a.Assume() // x is a point of the subspace
			position := a.Have(
				"x is a point of the space in u, which is what the points of the subspace are",
				"x ∈ ⋃T ∧ x ∈ u",
				BySets(xIn, topological_space.SubtopologySpace.At(T, u)))
			v, nbhd := a.ObtainAs[Set[A]](
				"x has an open neighbourhood v whose closure is compact and lies in u",
				"∃v:set(A). v ∈ T ∧ x ∈ v ∧ compact_in(closure(v)) ∧ closure(v) ⊆ u",
				By(
					LocallyCompactHausdorffNeighbourhood.Read(topology).At(uMember, x),
					hausdorffT,
					locallyCompact,
					position))
			inU := a.Have(
				"v lies in its closure, so in u",
				"v ⊆ u",
				BySets(nbhd, topological_space.SubsetClosure.At(T, v)))
			closureV := a.TermAs[Set[A]]("closure(v)")
			a.Take(v)
			a.Take(closureV)
			a.Show(
				"v, an open set inside the open u, is open in the subspace and holds "+
					"x; its closure holds v and, lying in u, is compact in the subspace",
				By(
					inU,
					nbhd,
					topological_space.OpenInOpenSubtopology.Read(topology).At(uMember, v),
					CompactInSubtopology.At(T, u, closureV),
					topological_space.SubsetClosure.At(T, v)))
		}),
})}
