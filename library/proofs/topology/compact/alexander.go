// alexander.go — the Alexander subbase lemma: a set every cover of which
// by members of a family b has a finite subcover is compact in the
// topology b generates on it. And the finite bookkeeping it rests on:
// sets each covering k together with finitely many members of a family
// meet, finitely many at a time, in a set that does the same.

package compact

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// IntersCoverUpToFinite — if each of finitely many sets covers k together
// with finitely many members of c, so does their intersection.
//
// By induction on the finite family. The intersection of no sets is the
// whole type, which covers k with no member of c added. A set x and the
// intersection of the rest, covering k with finitely many members d₁ and
// d₂ of c respectively, meet in a set covering k with the members of
// d₁ ∪ d₂: a point of k in neither union lies in x and in every other set.
var IntersCoverUpToFinite = intersCoverUpToFiniteThm{family.Add(registry.ProofEntry{
	Name: "IntersCoverUpToFinite",
	Key:  "prop_bb6695577371faa4",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(A). ∀c f:set(set(A)).",
		Hypotheses: []string{
			"finite(f)",
			"∀s:set(A). s ∈ f ⇒ ∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ k ⊆ s ∪ ⋃d",
		},
		Conclusion: "∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ k ⊆ ⋂f ∪ ⋃d",
	},
		func(a *Argument, k *Expr[Set[A]], c, f *Expr[Set[Set[A]]], finite, membersCover Fact) {
			// A set covering k together with finitely many members of c.
			coversWithFinitelyMany := a.TermAs[Set[Set[A]]](
				"λs:set(A). ∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ k ⊆ s ∪ ⋃d")

			a.Show(
				"the induction carries the property to f, which is finite with every member covering k so",
				ByInduction(finite_set.FiniteInduct, finite, Generalizing(membersCover),
					Case(
						"the intersection of no sets is everything, which covers k with no member of c added",
						Derive(func(b *Argument) {
							b.Assume() // the empty family has no members to ask anything of
							b.Take(b.TermAs[Set[Set[A]]]("∅"))
							b.Show(
								"∅ is a finite subfamily of c, and ⋂∅ covers k",
								BySets(finite_set.FiniteRules))
						})),
					Case(
						"a set x and the intersection of the rest each cover k "+
							"with finitely many members of c, and so does their meet",
						Derive(func(b *Argument) {
							x := b.FixAs[Set[A]]()
							s := b.FixAs[Set[Set[A]]]("s")
							carried := b.Assume() // the induction hypothesis, itself conditional
							given := b.Assume()   // every member of insert(x, s) covers k so
							members := b.Have(
								"x covers k with finitely many members of c, and so does every member of s",
								"(∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ k ⊆ x ∪ ⋃d) ∧ "+
									"(∀t:set(A). t ∈ s ⇒ ∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ k ⊆ t ∪ ⋃d)",
								By(given, set_basic.ForallInInsert.At(coversWithFinitelyMany, x, s)))
							parts := b.Conjuncts(
								members,
								"x covers k with finitely many members of c",
								"and so does every member of s")
							d1, first := b.UnpackAs[Set[Set[A]]](parts[0], "d₁")
							d2, rest := b.ObtainAs[Set[Set[A]]](
								"by the induction hypothesis ⋂s covers k with finitely many members d₂ of c",
								"∃d₂:set(set(A)). d₂ ⊆ c ∧ finite(d₂) ∧ k ⊆ ⋂s ∪ ⋃d₂",
								By(carried, parts[1]))
							b.Take(b.TermAs[Set[Set[A]]]("d₁ ∪ d₂"))
							b.Show(
								"the members of d₁ ∪ d₂ complete the meet of x and ⋂s to a cover of k",
								SplitConj(
									Case(
										"d₁ ∪ d₂ is a finite subfamily of c",
										By(first, rest, finite_set.FiniteUnionImp.At(d1, d2), set_order.UnionSubset)),
									Case(
										"a point of k in neither ⋃d₁ nor ⋃d₂ lies in x and in every member of s",
										BySets(first, rest)),
								))
						})),
				))
		}),
})}

// AlexanderSubbase — the Alexander subbase lemma: if every cover of X by
// members of b has a finite subcover, X is compact in the topology b
// generates on X.
//
// Suppose some open cover of X has no finite subcover. The open covers of
// X with no finite subcover hold the union of each non-empty chain of
// them, a finite subfamily of the union lying inside one member of the
// chain; so by Zorn's lemma one of them, m, is maximal. An open set u
// outside m covers X together with finitely many members of m: adding u
// to m leaves the family, so finitely many members of insert(u, m) cover
// X. And X itself is no member of m, which would then have the finite
// subcover {X}. Now the members of m that lie in b cover X. A point x of
// X lies in a member w of m, and w, being open, holds the meet of
// finitely many generators around x. Were none of those generators in
// m ∩ b, each would be open and outside m, so each would cover X with
// finitely many members of m, and so would their meet; with w in place of
// the meet, that is a finite subcover of m. So x lies in a member of
// m ∩ b. By the hypothesis finitely many members of m ∩ b cover X — a
// finite subcover of m after all.
var AlexanderSubbase = alexanderSubbaseThm{family.Add(registry.ProofEntry{
	Name: "AlexanderSubbase",
	Key:  "prop_5d782eb1845526d3",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(A). ∀b:set(set(A)).",
		Hypotheses: []string{
			"∀c:set(set(A)). c ⊆ b ∧ X ⊆ ⋃c ⇒ ∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ X ⊆ ⋃d",
		},
		Conclusion: "compact_in(topology_generated_on(X, b), X)",
	},
		func(a *Argument, X *Expr[Set[A]], b *Expr[Set[Set[A]]], subcovers Fact) {
			_, TDef := a.LetAs[Set[Set[A]]]("T", "topology_generated_on(X, b)")
			generatorsOpen := a.Have(
				"the members of b and X itself are open, being the generators of T",
				"b ∪ {X} ⊆ T",
				TDef.Rw(),
				Unfold(topological_space.TopologyGeneratedOnDef),
				Cite(topological_space.GeneratedContains))
			inSpace := a.Have(
				"so X lies in the space",
				"X ⊆ ⋃T",
				BySets(generatorsOpen))

			notCompact := a.SupposeNot()
			c, uncovered := a.ObtainAs[Set[Set[A]]](
				"X lying in the space, some open cover c of X has no finite subcover",
				"∃c:set(set(A)). c ⊆ T ∧ X ⊆ ⋃c ∧ ¬(∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ X ⊆ ⋃d)",
				By(a.Unfolded(notCompact, CompactInDef), inSpace))

			// The open covers of X with no finite subcover.
			F, FDef := a.LetAs[Set[Set[Set[A]]]](
				"F",
				"{e:set(set(A)) | e ⊆ T ∧ X ⊆ ⋃e ∧ ¬(∃d:set(set(A)). d ⊆ e ∧ finite(d) ∧ X ⊆ ⋃d)}")
			inF := a.Have(
				"a member of F is an open cover of X with no finite subcover",
				"∀e:set(set(A)). e ∈ F ⇔ e ⊆ T ∧ X ⊆ ⋃e ∧ ¬(∃d:set(set(A)). d ⊆ e ∧ finite(d) ∧ X ⊆ ⋃d)",
				BySets(FDef))
			nonEmpty := a.Have(
				"F is not empty: c is a member",
				"F ≠ ∅",
				By(inF.At(c), uncovered, set_basic.MemberNotEmpty.At(F)))
			chainUnions := a.Have(
				"F holds the union of each of its non-empty chains",
				"∀C:set(set(set(A))). C ⊆ F ∧ C ≠ ∅ ∧ (∀s t:set(set(A)). s ∈ C ∧ t ∈ C ⇒ s ⊆ t ∨ t ⊆ s) ⇒ ⋃C ∈ F",
				Derive(func(inner *Argument) {
					C := inner.FixAs[Set[Set[Set[A]]]]("C")
					chain := inner.Conjuncts(
						inner.Assume(),
						"C lies in F",
						"C is not empty",
						"any two members of C are comparable")
					members := inner.Have(
						"each member of C is an open cover of X with no finite subcover",
						"∀e:set(set(A)). e ∈ C ⇒ e ⊆ T ∧ X ⊆ ⋃e ∧ ¬∃d:set(set(A)). d ⊆ e ∧ finite(d) ∧ X ⊆ ⋃d",
						BySets(FDef, chain[0]))
					open := inner.Have(
						"so ⋃C is a family of open sets",
						"⋃C ⊆ T",
						By(members, set_order.UnionsSubset))
					e, eIn := inner.ObtainAs[Set[Set[A]]](
						"C has a member e",
						"∃e:set(set(A)). e ∈ C",
						By(chain[1], set_basic.MemberNotEmpty.At(C)))
					eParts := inner.Conjuncts(
						GroupPremises(eIn, members.At(e)),
						"e is a family of open sets",
						"covering X",
						"with no finite subcover")
					covers := inner.Have(
						"⋃C covers X, as its member e does",
						"X ⊆ ⋃⋃C",
						BySets(eIn, eParts[1]))
					insideMember := inner.Have(
						"a finite subfamily of ⋃C lies inside one member of the chain",
						"∀d:set(set(A)). finite(d) ∧ d ⊆ ⋃C ⇒ ∃t:set(set(A)). t ∈ C ∧ d ⊆ t",
						By(chain[1], chain[2], finite_set.FiniteSubsetUnionsChain))
					noneFinite := inner.Have(
						"so no finite subfamily of ⋃C covers X, no member of C having one",
						"¬(∃d:set(set(A)). d ⊆ ⋃C ∧ finite(d) ∧ X ⊆ ⋃d)",
						By(members, insideMember))
					inner.Show(
						"so ⋃C is a member of F",
						By(inF.At(inner.TermAs[Set[Set[A]]]("⋃C")), open, covers, noneFinite))
				}))
			m, maximal := a.ObtainAs[Set[Set[A]]](
				"by Zorn's lemma F has a maximal member m",
				"∃m:set(set(A)). m ∈ F ∧ (∀e:set(set(A)). e ∈ F ∧ m ⊆ e ⇒ e = m)",
				By(nonEmpty, chainUnions, order.ZornFamily.At(F)))
			mParts := a.Conjuncts(
				maximal,
				"m is a member of F",
				"and the only member of F containing m")
			mIn, onlyMember := mParts[0], mParts[1]
			mFacts := a.Conjuncts(
				a.Simplified(mIn, Fwd(inF)),
				"the members of m are open",
				"m covers X",
				"and no finite subfamily of m covers X")
			mOpen, mCovers, noFinite := mFacts[0], mFacts[1], mFacts[2]

			// The maximality of m, read off at an open set it does not hold.
			completes := a.Have(
				"an open set u outside m covers X together with finitely many members of m",
				"∀u:set(A). u ∈ T ∧ u ∉ m ⇒ ∃d:set(set(A)). d ⊆ m ∧ finite(d) ∧ X ⊆ u ∪ ⋃d",
				Derive(func(inner *Argument) {
					inner.FixAs[Set[A]]("u")
					uParts := inner.Conjuncts(
						inner.Assume(),
						"u is open",
						"and no member of m")
					enlarged := inner.TermAs[Set[Set[A]]]("insert(u, m)")
					notInF := inner.Have(
						"insert(u, m) contains m and is another family, so maximality keeps it out of F",
						"insert(u, m) ∉ F",
						BySets(onlyMember.At(enlarged), uParts[1]))
					openCover := inner.Have(
						"insert(u, m) is a family of open sets covering X",
						"insert(u, m) ⊆ T ∧ X ⊆ ⋃insert(u, m)",
						SplitConj(
							Case(
								"u and the members of m are open",
								By(uParts[0], mOpen, set_order.InsertSubset)),
							Case(
								"the members of m already cover X",
								Simp(Fwd(set_algebra.UnionsInsert)),
								BySets(mCovers)),
						))
					d, few := inner.ObtainAs[Set[Set[A]]](
						"so finitely many of its members, d, cover X",
						"∃d:set(set(A)). d ⊆ insert(u, m) ∧ finite(d) ∧ X ⊆ ⋃d",
						By(inF.At(enlarged), notInF, openCover))
					inner.Take(inner.TermAs[Set[Set[A]]]("d ∖ {u}"))
					inner.Show(
						"the members of d other than u complete u to a cover of X",
						SplitConj(
							Case(
								"they are finitely many members of m",
								BySets(few, finite_set.FiniteDiff.At(d, inner.TermAs[Set[Set[A]]]("{u}")))),
							Case(
								"and a point of X outside u lies in one of them",
								BySets(few)),
						))
				}))
			spaceNotInM := a.Have(
				"X is no member of m, which would then have the finite subcover {X}",
				"X ∉ m",
				By(
					noFinite,
					finite_set.FiniteSing.At(X),
					set_order.SingSubset.At(m, X),
					set_algebra.UnionsSing.At(X),
					set_order.SubsetRefl.At(X)))

			// The members of m that lie in b cover X.
			pointwise := a.Have(
				"each point x of X lies in a member of m ∩ b",
				"∀x:A. x ∈ X ⇒ x ∈ ⋃(m ∩ b)",
				Derive(func(inner *Argument) {
					inner.FixAs[A]("x")
					xIn := inner.Assume()
					w, wHolds := inner.ObtainAs[Set[A]](
						"m covers X, so a member w of m holds x",
						"∃w:set(A). w ∈ m ∧ x ∈ w",
						BySets(xIn, mCovers))
					generators := inner.TermAs[Set[Set[A]]]("b ∪ {X}")
					wGenerated := inner.Have(
						"w is open, so it lies in the topology b ∪ {X} generates",
						"w ∈ topology_generated(b ∪ {X})",
						BySets(wHolds, TDef, mOpen, topological_space.TopologyGeneratedOnDef.At(X, b)))
					_, meets := inner.ObtainAs[Set[Set[A]]](
						"so w is a union of meets of finitely many generators",
						"∃g:set(set(A)). "+
							"    w = ⋃g ∧ (∀v:set(A). v ∈ g ⇒ ∃f:set(set(A)). finite(f) ∧ ¬(f = ∅) ∧ f ⊆ b ∪ {X} ∧ v = ⋂f)",
						By(wGenerated, topological_space.GeneratedOpenIff.At(generators, w)))
					meetParts := inner.Conjuncts(
						meets,
						"w is the union of g",
						"and each member of g is the meet of finitely many generators")
					v, vHolds := inner.ObtainAs[Set[A]](
						"x lies in one of them, v, which lies inside w",
						"∃v:set(A). v ∈ g ∧ x ∈ v ∧ v ⊆ w",
						BySets(meetParts[0], wHolds))
					f, fMeet := inner.UnpackAs[Set[Set[A]]](GroupPremises(vHolds, meetParts[1].At(v)), "f")
					some := inner.Have(
						"some generator s in f lies in m ∩ b",
						"∃s:set(A). s ∈ f ∧ s ∈ m ∩ b",
						Derive(func(none *Argument) {
							noneIn := none.SupposeNot()
							outside := none.Have(
								"then each generator in f is open and outside m: a member of b outside m ∩ b, or X",
								"∀s:set(A). s ∈ f ⇒ s ∈ T ∧ s ∉ m",
								BySets(fMeet, noneIn, generatorsOpen, spaceNotInM))
							each := none.Have(
								"so each covers X together with finitely many members of m",
								"∀s:set(A). s ∈ f ⇒ ∃d:set(set(A)). d ⊆ m ∧ finite(d) ∧ X ⊆ s ∪ ⋃d",
								By(completes, outside))
							d, meetCompleted := none.ObtainAs[Set[Set[A]]](
								"and so does their meet, with finitely many members d of m",
								"∃d:set(set(A)). d ⊆ m ∧ finite(d) ∧ X ⊆ ⋂f ∪ ⋃d",
								By(fMeet, each, IntersCoverUpToFinite.At(X, m, f)))
							subcover := none.Have(
								"w contains the meet, so w with the members of d is a finite subcover of m",
								"insert(w, d) ⊆ m ∧ finite(insert(w, d)) ∧ X ⊆ ⋃insert(w, d)",
								Simp(Fwd(set_algebra.UnionsInsert)),
								SplitConj(
									Case(
										"w and the members of d are finitely many members of m",
										By(meetCompleted, wHolds, set_order.InsertSubset, finite_set.FiniteInsert.At(w, d))),
									Case(
										"a point of X outside ⋃d lies in ⋂f, which is v, inside w",
										BySets(meetCompleted, fMeet, vHolds)),
								))
							none.Show(
								"which m does not have",
								By(noFinite, subcover))
						}))
					_, sIn := inner.UnpackAs[Set[A]](some, "s")
					inner.Show(
						"x lies in v, the meet of f, and so in its member s",
						BySets(sIn, fMeet, vHolds))
				}))
			subbasicCover := a.Have(
				"so the members of m ∩ b cover X",
				"X ⊆ ⋃(m ∩ b)",
				BySets(pointwise))
			_, few := a.ObtainAs[Set[Set[A]]](
				"by the hypothesis finitely many of them, d, cover X",
				"∃d:set(set(A)). d ⊆ m ∩ b ∧ finite(d) ∧ X ⊆ ⋃d",
				By(subbasicCover, subcovers.At(a.TermAs[Set[Set[A]]]("m ∩ b")), set_order.InterSubset.At(b, m)))
			a.Show(
				"so d is a finite subcover of m, which has none",
				BySets(noFinite, few))
		}),
})}
