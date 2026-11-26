// zorn.go — the three maximal principles, each read off the one before:
// Zorn's lemma for a family of sets, from the fixed-point theorem;
// Hausdorff's maximal principle, at the family of the chains that
// contain a given one; and Zorn's lemma for a preorder, at the relation
// cut down to the set. The README carries the chapter story.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ZornFamily — Zorn's lemma for a family F of sets, by the fixed-point
// theorem at a function that climbs inside F. Call t a step from s when
// t contains s, is a member of F unless it is s, and is s only where
// every member of F that contains s is s. Every set has a step: a
// member of F that contains it and is another set, where there is one,
// and itself otherwise; a function f picks a step from each set. f only
// enlarges, and it preserves the property of being empty or a member of
// F, f(s) being a member of F or s. That property passes to the union
// of a chain G of sets that have it: the members of G that lie in F
// have the same union, the other members being empty, and they are a
// chain inside F, so F contains their union unless there are none, when
// the union is empty. The empty set has to be allowed, the empty family
// being a chain. So f fixes a set m that is empty or a member of F.
// Being its own step, m is the only member of F that contains m; and it
// is a member of F, for an empty m lies in a member of F, which is then
// m.
var ZornFamily = zornFamilyThm{family.Add(registry.ProofEntry{
	Name: "ZornFamily",
	Key:  "prop_af795708e04375f7",
	Build: family.Theorem(
		Statement{
			Binders: "∀F:set(set(A)).",
			Hypotheses: []string{
				"F ≠ ∅",
				"∀c:set(set(A)). c ⊆ F ∧ c ≠ ∅ ∧ (∀s t:set(A). s ∈ c ∧ t ∈ c ⇒ s ⊆ t ∨ t ⊆ s) ⇒ ⋃c ∈ F",
			},
			Conclusion: "∃m:set(A). m ∈ F ∧ (∀s:set(A). s ∈ F ∧ m ⊆ s ⇒ s = m)",
		},
		func(a *Argument, F *Expr[Set[Set[A]]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"F is not empty",
				"F contains the union of each of its non-empty chains")
			nonEmpty, chainUnions := parts[0], parts[1]

			stepDef := a.Let(
				"step",
				a.Term(
					"λs:set(A). λt:set(A). s ⊆ t ∧ (t ∈ F ∨ t = s) ∧ (t = s ⇒ ∀d:set(A). d ∈ F ∧ s ⊆ d ⇒ d = s)"))
			stepReads := a.Have(
				"t is a step from s exactly when the three clauses hold of the two sets",
				"∀s t:set(A). step(s, t) ⇔ s ⊆ t ∧ (t ∈ F ∨ t = s) ∧ (t = s ⇒ ∀d:set(A). d ∈ F ∧ s ⊆ d ⇒ d = s)",
				By(Normalized, stepDef))

			everySetSteps := a.Have(
				"every set has a step",
				"∀s:set(A). ∃t:set(A). step(s, t)",
				Derive(func(b *Argument) {
					s := b.FixAs[Set[A]]("s")
					b.Cases(b.Term("∃d:set(A). d ∈ F ∧ s ⊆ d ∧ d ≠ s"))
					b.When(
						"some member of F contains s and is another set",
						func(c *Argument, some Fact) {
							d, above := c.UnpackAs[Set[A]](some)
							c.Take(d)
							c.Show(
								"it is a step from s: not being s, it is asked nothing by the third clause",
								By(Normalized, above, stepReads.At(s, d)))
						})
					b.Otherwise(
						"every member of F that contains s is s",
						func(c *Argument, none Fact) {
							c.Take(s)
							c.Show(
								"s is then a step from itself",
								By(none, stepReads.At(s, s), set_order.SubsetRefl.At(s)))
						})
				}))
			f, steps := a.ObtainAs[Fun[Set[A], Set[A]]](
				"choosing a step from each set is a function f",
				"∃f:(set(A) → set(A)). ∀s:set(A). step(s, f(s))",
				By(everySetSteps))

			// The property the fixed point is to have.
			emptyOrInF := a.TermAs[Set[Set[A]]]("λs:set(A). s = ∅ ∨ s ∈ F")

			inflationary := a.Have(
				"f only enlarges its argument",
				"∀s:set(A). s ⊆ f(s)",
				Derive(func(b *Argument) {
					s := b.FixAs[Set[A]]("s")
					b.Show(
						"a step from s contains s: the first clause",
						By(steps.At(s), stepReads.At(s, b.TermAs[Set[A]]("f(s)"))))
				}))
			preserved := a.Have(
				"f preserves being empty or a member of F",
				"∀s:set(A). (s = ∅ ∨ s ∈ F) ⇒ f(s) = ∅ ∨ f(s) ∈ F",
				Derive(func(b *Argument) {
					s := b.FixAs[Set[A]]("s")
					b.Show(
						"a step from s is a member of F, or is s: the second clause",
						By(Normalized, steps.At(s), stepReads.At(s, b.TermAs[Set[A]]("f(s)"))))
				}))
			passesToChainUnions := a.Have(
				"being empty or a member of F passes to the union of a chain of sets that are one or the other",
				Statement{
					Binders: "∀G:set(set(A)).",
					Hypotheses: []string{
						"∀s:set(A). s ∈ G ⇒ s = ∅ ∨ s ∈ F",
						"∀s t:set(A). s ∈ G ∧ t ∈ G ⇒ s ⊆ t ∨ t ⊆ s",
					},
					Conclusion: "⋃G = ∅ ∨ ⋃G ∈ F",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("G")
					about := b.Conjuncts(
						b.Assume(),
						"every member of G is empty or a member of F",
						"any two members of G are comparable")
					members, chain := about[0], about[1]

					// The members of G that lie in F.
					inF := b.TermAs[Set[Set[A]]]("G ∩ F")

					sameUnion := b.Have(
						"the other members of G are empty, so the members in F have the same union",
						"⋃(G ∩ F) = ⋃G",
						BySets(members))
					some := b.Unless(
						b.Term("G ∩ F = ∅"),
						"no member of G lies in F",
						Given(func(c *Argument, none Fact) {
							empty := c.Have(
								"the union of G is then the union of an empty family, which is empty",
								"⋃G = ∅",
								sameUnion.RwRev(),
								none.Rw(),
								Cite(set_algebra.UnionsEmpty.Inst[A]()))
							c.Show(
								"the first alternative: the union of G is empty",
								By(Normalized, empty))
						}))
					inside := b.Have(
						"the members of G in F are a subfamily of F",
						"G ∩ F ⊆ F",
						BySets())
					subfamilyIsChain := b.Have(
						"and a chain, G being one",
						"∀s t:set(A). s ∈ G ∩ F ∧ t ∈ G ∩ F ⇒ s ⊆ t ∨ t ⊆ s",
						BySets(chain))
					b.Show(
						"the second alternative: F contains their union, which is the union of G",
						By(sameUnion, inside, some, subfamilyIsChain, chainUnions.At(inF)))
				}))

			m, atM := a.ObtainAs[Set[A]](
				"so f fixes a set m that is empty or a member of F: the fixed-point theorem",
				"∃m:set(A). (m = ∅ ∨ m ∈ F) ∧ f(m) = m",
				By(inflationary, preserved, passesToChainUnions, BourbakiWitt.At(f, emptyOrInF)))
			aboutM := a.Conjuncts(
				atM,
				"m is empty or a member of F",
				"f fixes m")
			emptyOrMember, fixed := aboutM[0], aboutM[1]

			maximal := a.Have(
				"m is its own step, so every member of F that contains m is m: the third clause",
				"∀d:set(A). d ∈ F ∧ m ⊆ d ⇒ d = m",
				By(fixed, steps.At(m), stepReads.At(m, a.TermAs[Set[A]]("f(m)"))))
			e, eInF := a.ObtainAs[Set[A]](
				"F has a member e",
				"∃e:set(A). e ∈ F",
				By(nonEmpty, set_basic.MemberNotEmpty.At(F)))
			mInF := a.Have(
				"m is a member of F",
				"m ∈ F",
				emptyOrMember.SplitDisj(
					LeftHolds(
						"m is empty: it lies in e, which is then m",
						Given(func(b *Argument, empty Fact) {
							below := b.Have(
								"the empty set lies in every set",
								"m ⊆ e",
								empty.Rw(),
								By(set_order.EmptySubset.At(e)))
							same := b.Have(
								"and the only member of F that contains m is m",
								"e = m",
								By(eInF, below, maximal.At(e)))
							b.Show(
								"so m is a member of F, as e is",
								same.RwRev(),
								By(eInF))
						})),
					RightHolds(
						"m is a member of F as it stands",
						Given(func(b *Argument, member Fact) { b.Do(By(member)) })),
				))

			a.Take(m)
			a.Show(
				"m is a member of F, and the only one that contains m",
				By(mInF, maximal))
		}),
})}

// HausdorffMaximality — Hausdorff's maximal principle, by Zorn's lemma
// at the family of the chains of R that contain c. The family is not
// empty, c being a member. It contains the union of each non-empty
// chain G of its members: the members of G are chains of R and G is a
// chain under inclusion, so the union is a chain of R (`ChainUnions`);
// and the union contains a member of G, which contains c. A member m
// that no other member contains is then a maximal chain: a chain of R
// that contains m contains c, so it is a member of the family, and
// then it is m. Nothing is asked of R, for the one thing the argument
// uses of chains is that the union of a chain of them is a chain.
var HausdorffMaximality = hausdorffMaximalityThm{family.Add(registry.ProofEntry{
	Name: "HausdorffMaximality",
	Key:  "prop_45db74a1bdef5c33",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:(A → A → bool). ∀c:set(A).",
			Hypotheses: []string{
				"chain(R, c)",
			},
			Conclusion: "∃m:set(A). c ⊆ m ∧ chain(R, m) ∧ (∀d:set(A). chain(R, d) ∧ m ⊆ d ⇒ d = m)",
		},
		func(a *Argument, R *Arrow2[A, A, Bool], c *Expr[Set[A]], cIsChain Fact) {
			// The chains of R that contain c, as a family of sets.
			above, aboveDef := a.LetAs[Set[Set[A]]]("above", "{d:set(A) | chain(R, d) ∧ c ⊆ d}")
			inAbove := a.Have(
				"the members of that family are the chains of R that contain c",
				"∀d:set(A). d ∈ above ⇔ chain(R, d) ∧ c ⊆ d",
				BySets(aboveDef))

			cInAbove := a.Have(
				"c is a member: a chain of R, and it contains itself",
				"c ∈ above",
				By(cIsChain, set_order.SubsetRefl.At(c), inAbove.At(c)))
			nonEmpty := a.Have(
				"so the family is not empty",
				"above ≠ ∅",
				By(Normalized, cInAbove, set_basic.MemberNotEmpty.At(above)))

			closedUnderChainUnions := a.Have(
				"the family contains the union of each of its non-empty chains",
				"∀G:set(set(A)). G ⊆ above ∧ G ≠ ∅ ∧ (∀s t:set(A). s ∈ G ∧ t ∈ G ⇒ s ⊆ t ∨ t ⊆ s) ⇒ ⋃G ∈ above",
				Derive(func(b *Argument) {
					G := b.FixAs[Set[Set[A]]]("G")
					union := b.TermAs[Set[A]]("⋃G")
					about := b.Conjuncts(
						b.Assume(),
						"G is a part of the family",
						"G is not empty",
						"any two members of G are comparable")
					partOfFamily, gNonEmpty, gIsChain := about[0], about[1], about[2]

					// The inclusion of G in the family, read member by member.
					inFamily := b.Unfolded(partOfFamily, set_basic.SubsetDef)
					members := b.Have(
						"each member of G is a member of the family: a chain of R that contains c",
						"∀s:set(A). s ∈ G ⇒ chain(R, s) ∧ c ⊆ s",
						b.ForEach(func(s *Expr[Set[A]]) Action {
							return By(inFamily.At(s), inAbove.At(s))
						}))
					unionIsChain := b.Have(
						"the union of G is a chain of R: its members are, and G is a chain under inclusion",
						"chain(R, ⋃G)",
						By(members, gIsChain, ChainUnions.At(R, G)))
					g, gInG := b.ObtainAs[Set[A]](
						"G has a member g",
						"∃g:set(A). g ∈ G",
						By(gNonEmpty, set_basic.MemberNotEmpty.At(G)))
					cBelowUnion := b.Have(
						"c lies in g, and g in the union",
						"c ⊆ ⋃G",
						By(
							gInG,
							members.At(g),
							set_order.MemberSubsetUnions.At(G, g),
							set_order.SubsetTrans.At(c, g, union)))
					b.Show(
						"the union is a chain of R that contains c: a member of the family",
						By(unionIsChain, cBelowUnion, inAbove.At(union)))
				}))

			m, atM := a.ObtainAs[Set[A]](
				"so the family has a member m that no other member contains: Zorn's lemma",
				"∃m:set(A). m ∈ above ∧ (∀s:set(A). s ∈ above ∧ m ⊆ s ⇒ s = m)",
				By(nonEmpty, closedUnderChainUnions, ZornFamily.At(above)))
			aboutM := a.Conjuncts(
				atM,
				"m is a member of the family",
				"every member of the family that contains m is m")
			mInAbove, onlyMember := aboutM[0], aboutM[1]
			mIsChainAboveC := a.Have(
				"m is a chain of R that contains c",
				"chain(R, m) ∧ c ⊆ m",
				By(mInAbove, inAbove.At(m)))

			maximal := a.Have(
				"every chain of R that contains m is m",
				"∀d:set(A). chain(R, d) ∧ m ⊆ d ⇒ d = m",
				Derive(func(b *Argument) {
					d := b.FixAs[Set[A]]("d")
					aboutD := b.Conjuncts(
						b.Assume(),
						"d is a chain of R",
						"d contains m")
					dIsChain, mBelowD := aboutD[0], aboutD[1]

					dInAbove := b.Have(
						"d contains c, through m, so it is a member of the family",
						"d ∈ above",
						By(dIsChain, mBelowD, mIsChainAboveC, set_order.SubsetTrans.At(c, m, d), inAbove.At(d)))
					b.Show(
						"and the only member that contains m is m",
						By(dInAbove, mBelowD, onlyMember.At(d)))
				}))

			a.Take(m)
			a.Show(
				"m contains c, is a chain of R, and lies in no other chain of R",
				By(mIsChainAboveC, maximal))
		}),
})}

// Zorn — Zorn's lemma, by Hausdorff's maximal principle at R cut down
// to s: the relation that holds of two points of s the first of which
// is below the second. The principle grows the empty chain into a
// maximal chain m of that relation. A point of m is comparable with
// itself there, which makes it a point of s, so m lies in s; and two
// points of m, comparable there, are comparable under R. So m is a
// chain of R inside s, and the hypothesis gives it an upper bound b in
// s. That b is maximal. Let x be a point of s that b is below. R being
// reflexive, x is below itself; and every point of m is below b, so
// below x, R being transitive. Then m with x added is still a chain of
// the cut-down relation, and it contains m, which is maximal: it is m.
// So x is a point of m, and x is below b. Antisymmetry is not used.
var Zorn = zornThm{family.Add(registry.ProofEntry{
	Name: "Zorn",
	Key:  "prop_b819e084e37ce4f",
	Build: Preorder.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"∀c:set(A). c ⊆ s ∧ chain(R, c) ⇒ ∃b:A. b ∈ s ∧ upper_bound(R, c, b)",
		},
		Conclusion: "∃m:A. maximal(R, s, m)",
	},
		func(a *Argument, R *Arrow2[A, A, Bool], pre Fact, s *Expr[Set[A]], bounded Fact) {
			// R cut down to s: both points lie in s, and the first is
			// below the second.
			inS, inSDef := a.LetAs[Fun2[A, A, Bool]]("inS", "λx:A. λy:A. x ∈ s ∧ y ∈ s ∧ R(x, y)")
			inSReads := a.Have(
				"x is below y in the cut-down relation exactly when both are points of s and x is below y under R",
				"∀x y:A. inS(x, y) ⇔ x ∈ s ∧ y ∈ s ∧ R(x, y)",
				By(Normalized, inSDef))

			// A maximal chain of the cut-down relation.
			empty := a.TermAs[Set[A]]("∅⟨A:A⟩")
			emptyIsChain := a.Have(
				"the empty set is a chain of the cut-down relation: it has no two points to compare",
				"chain(inS, ∅)",
				Unfold(ChainDef),
				BySets())
			m, atM := a.ObtainAs[Set[A]](
				"Hausdorff's maximal principle grows it into a maximal chain m of that relation",
				"∃m:set(A). ∅ ⊆ m ∧ chain(inS, m) ∧ (∀d:set(A). chain(inS, d) ∧ m ⊆ d ⇒ d = m)",
				By(emptyIsChain, HausdorffMaximality.At(inS, empty)))
			aboutM := a.Conjuncts(
				atM,
				"m contains the empty chain it was grown from",
				"m is a chain of the cut-down relation",
				"every chain of the cut-down relation that contains m is m")
			mIsChain, noLargerChain := aboutM[1], aboutM[2]

			// m lies in s, and is a chain of R.
			pairwise := a.Unfolded(mIsChain, ChainDef)
			pointsInS := a.Have(
				"a point of m is comparable with itself in the cut-down relation, which makes it a point of s",
				"∀x:A. x ∈ m ⇒ x ∈ s",
				a.ForEach(func(x *Expr[A]) Action {
					return By(pairwise.At(x, x), inSReads.At(x, x))
				}))
			mInS := a.Have(
				"so m lies in s",
				"m ⊆ s",
				BySets(pointsInS))
			comparableUnderR := a.Have(
				"two points of m are comparable in the cut-down relation, and so under R",
				"∀x y:A. x ∈ m ∧ y ∈ m ⇒ R(x, y) ∨ R(y, x)",
				a.ForEach(func(x *Expr[A]) Action {
					return a.ForEach(func(y *Expr[A]) Action {
						return By(pairwise.At(x, y), inSReads.At(x, y), inSReads.At(y, x))
					})
				}))
			// chain and maximal are read here through their definitions
			// cited as facts: an unfold at the goal reaches the hypotheses
			// too, and the reading of the cut-down relation must stay.
			mIsChainOfR := a.Have(
				"which makes m a chain of R",
				"chain(R, m)",
				By(comparableUnderR, ChainDef.At(R, m)))

			// An upper bound of m in s.
			b, atB := a.ObtainAs[A](
				"the hypothesis on s, at m: a point b of s that is an upper bound of m",
				"∃b:A. b ∈ s ∧ upper_bound(R, m, b)",
				By(mInS, mIsChainOfR, bounded.At(m)))
			aboutB := a.Conjuncts(
				atB,
				"b is a point of s",
				"b is an upper bound of m")
			bInS, bBounds := aboutB[0], aboutB[1]
			belowB := a.Unfolded(bBounds, UpperBoundDef)

			// b is maximal: a point of s that b is below can be added to
			// m, so it is a point of m already.
			nothingAbove := a.Have(
				"a point of s that b is below is below b in turn",
				"∀x:A. x ∈ s ∧ R(b, x) ⇒ R(x, b)",
				Derive(func(c *Argument) {
					x := c.FixAs[A]("x")
					aboutX := c.Conjuncts(
						c.Assume(),
						"x is a point of s",
						"b is below x")
					xInS, bBelowX := aboutX[0], aboutX[1]
					larger := c.TermAs[Set[A]]("insert(x, m)")

					xBelowItself := c.Have(
						"x is below itself in the cut-down relation: it is a point of s, and R is reflexive",
						"inS(x, x)",
						By(xInS, Reflexive.Read(pre).At(x), inSReads.At(x, x)))
					comparableWithM := c.Have(
						"a point of m is comparable with x in the cut-down relation, "+
							"being below it: it lies in s, below b, and b is below x",
						"∀y:A. y ∈ m ⇒ inS(x, y) ∨ inS(y, x)",
						c.ForEach(func(y *Expr[A]) Action {
							return By(
								xInS,
								bBelowX,
								pointsInS.At(y),
								belowB.At(y),
								Transitive.Read(pre).At(y, b, x),
								inSReads.At(y, x))
						}))
					largerIsChain := c.Have(
						"so m with x added is still a chain of the cut-down relation",
						"chain(inS, insert(x, m))",
						By(mIsChain, xBelowItself, comparableWithM, ChainInsert.At(inS, m, x)))
					mBelowLarger := c.Have(
						"and it contains m",
						"m ⊆ insert(x, m)",
						BySets())
					same := c.Have(
						"so it is m, m being a maximal chain",
						"insert(x, m) = m",
						By(largerIsChain, mBelowLarger, noLargerChain.At(larger)))
					xInM := c.Have(
						"x, a point of the larger set, is then a point of m",
						"x ∈ m",
						BySets(same))
					c.Show(
						"so x is below b, as every point of m is",
						By(xInM, belowB.At(x)))
				}))

			a.Take(b)
			a.Show(
				"b is a point of s, and whatever point of s it is below is below it in turn: b is maximal in s",
				By(bInS, nothingAbove, MaximalDef.At(R, s, b)))
		}),
})}
