// countable.go — countability: what it is to be no larger than ℕ, which
// sets are, and that the pairs of naturals are as many as the naturals.

package cardinal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// CountableCover — a set is countable exactly when some sequence runs
// through all of it: the surjective reading of ≤ at t = ℕ.
var CountableCover = countableCoverThm{family.Add(registry.ProofEntry{
	Name: "CountableCover",
	Key:  "prop_d426d73c6983432d",
	Build: family.Theorem("∀s:set(A). countable(s) ⇔ ∃f:(num → A). s ⊆ image(f, 𝕌⟨A:num⟩)",
		Opening(Unfold(CountableDef), func(a *Argument, s *Expr[Set[A]]) {
			a.Show(
				"s is no larger than ℕ exactly when a map from ℕ covers it",
				By(CardLeCover.At(s, a.TermAs[Set[Nat]]("𝕌⟨A:num⟩"))))
		})),
})}

// NumCountable — ℕ is countable: the identity tags each natural by
// itself.
var NumCountable = numCountableThm{family.Add(registry.ProofEntry{
	Name: "NumCountable",
	Key:  "prop_e537a17d3145f1fa",
	Build: family.Theorem("countable(𝕌⟨A:num⟩)",
		Opening(Unfold(CountableDef), func(a *Argument) {
			a.Show(
				"ℕ is no larger than itself",
				By(CardLeRefl.At(a.TermAs[Set[Nat]]("𝕌⟨A:num⟩"))))
		})),
})}

// CardLeCountable — a set no larger than a countable one is countable:
// tag it through the injection.
var CardLeCountable = cardLeCountableThm{family.Add(registry.ProofEntry{
	Name: "CardLeCountable",
	Key:  "prop_d4dbbd614644d70a",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B).",
		Hypotheses: []string{
			"card_le(s, t)",
			"countable(t)",
		},
		Conclusion: "countable(s)",
	},
		Opening(Unfold(CountableDef), func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], h Fact) {
			a.Show(
				"s ≤ t ≤ ℕ",
				By(h, CardLeTrans.At(s, t, a.TermAs[Set[Nat]]("𝕌⟨A:num⟩"))))
		})),
})}

// CountableSubset — a subset of a countable set is countable.
var CountableSubset = countableSubsetThm{family.Add(registry.ProofEntry{
	Name: "CountableSubset",
	Key:  "prop_39036d2ed25c3b24",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"countable(t)",
			"s ⊆ t",
		},
		Conclusion: "countable(s)",
	},
		func(a *Argument, s, t *Expr[Set[A]], h Fact) {
			a.Show(
				"s is no larger than t, which is countable",
				By(h, CardLeSubset.At(s, t), CardLeCountable.At(s, t)))
		}),
})}

// CountableEmpty — the empty set is countable: any map tags its no
// points.
var CountableEmpty = countableEmptyThm{family.Add(registry.ProofEntry{
	Name: "CountableEmpty",
	Key:  "prop_9ee6585c016f490",
	Build: family.Theorem("countable(∅⟨A:A⟩)",
		Opening(Chain(
			Unfold(CountableDef), Unfold(CardLeDef), Unfold(functions.InjectiveOnDef)), func(a *Argument) {
			a.Take(a.Term("λx:A. 0"))
			a.Show(
				"there are no points to send or to tell apart",
				BySets())
		})),
})}

// NumPairCountable — ℕ × ℕ is countable: tag each pair by the natural
// the pairing function num_pair makes of its two components. A tag is
// a natural, so every pair lands in ℕ; and two pairs with one tag have
// the same components, num_pair being injective, so they are one pair,
// since a pair is the pair of its components.
var NumPairCountable = numPairCountableThm{family.Add(registry.ProofEntry{
	Name: "NumPairCountable",
	Key:  "prop_7dab84d5b4beb774",
	Build: family.Theorem("countable(𝕌⟨A:prod(num, num)⟩)",
		Opening(Chain(
			Unfold(CountableDef), Unfold(CardLeDef), Unfold(functions.InjectiveOnDef)), func(a *Argument) {
			a.Take(a.TermAs[Fun[Prod[Nat, Nat], Nat]]("λp:prod(num, num). num_pair(fst(p), snd(p))"))
			oneToOne := a.Have(
				"two pairs with one tag are one pair",
				"∀p q:prod(num, num). num_pair(fst(p), snd(p)) = num_pair(fst(q), snd(q)) ⇒ p = q",
				Derive(func(b *Argument) {
					p, q := b.FixAs[Prod[Nat, Nat]](), b.FixAs[Prod[Nat, Nat]]()
					b.Show(
						"equal tags have equal components, and each pair is the pair of its components",
						By(
							datatype_universe.NumPairInjective.At(
								b.TermAs[Nat]("fst(p)"), b.TermAs[Nat]("snd(p)"), b.TermAs[Nat]("fst(q)"), b.TermAs[Nat]("snd(q)")),
							pairs.PairEta.At(p),
							pairs.PairEta.At(q)))
				}))
			a.Show(
				"every tag is a natural, and no two pairs share one",
				BySets(oneToOne))
		})),
})}

// PairNumBijection — the pairs of naturals and the naturals are the same
// size. Each injects into the other: the pairs into the naturals because
// they are countable (NumPairCountable), the naturals into the pairs by
// n ↦ (n, 0), since equal pairs have equal first components. Schröder–
// Bernstein joins the two injections into a bijection.
var PairNumBijection = pairNumBijectionThm{family.Add(registry.ProofEntry{
	Name: "PairNumBijection",
	Key:  "prop_4e069f3d40027a54",
	Build: family.Theorem("card_eq(𝕌⟨A:prod(num, num)⟩, 𝕌⟨A:num⟩)",
		func(a *Argument) {
			naturalPairs := a.TermAs[Set[Prod[Nat, Nat]]]("𝕌⟨A:prod(num, num)⟩")
			naturals := a.TermAs[Set[Nat]]("𝕌⟨A:num⟩")
			intoPairs := a.Have(
				"n ↦ (n, 0) sends the naturals into the pairs, identifying none of them",
				"card_le(𝕌⟨A:num⟩, 𝕌⟨A:prod(num, num)⟩)",
				Unfold(CardLeDef),
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Nat, Prod[Nat, Nat]]]("λn:num. (n, 0)"))
					b.Show(
						"every (n, 0) is a pair, and (m, 0) = (n, 0) has equal first components, m = n",
						Unfold(functions.InjectiveOnDef),
						BySets(pairs.PairEq))
				}))
			intoNaturals := a.Have(
				"the pairs of naturals are countable: they inject into the naturals",
				"card_le(𝕌⟨A:prod(num, num)⟩, 𝕌⟨A:num⟩)",
				By(NumPairCountable, CountableDef.At(naturalPairs)))
			a.Show(
				"each injects into the other, and Schröder–Bernstein joins them into a bijection",
				By(intoPairs, intoNaturals, SchroederBernstein.At(naturalPairs, naturals)))
		}),
})}

// CountableEnumeration — a nonempty countable set is the range of a
// sequence, not merely covered by one. Take a point a of s and a
// sequence e covering s, and keep e(n) where it lies in s, putting a in
// its place elsewhere: every value is then a point of s, and each point
// of s, being some e(n), is still reached at n.
var CountableEnumeration = countableEnumerationThm{family.Add(registry.ProofEntry{
	Name: "CountableEnumeration",
	Key:  "prop_12877c9177f771ea",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"countable(s)",
			"¬(s = ∅)",
		},
		Conclusion: "∃f:(num → A). s = image(f, 𝕌⟨A:num⟩)",
	},
		func(a *Argument, s *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"s is countable",
				"s is not empty")
			countable, nonempty := parts[0], parts[1]
			_, aIn := a.Obtain(
				"s has a point a",
				"∃a:A. a ∈ s",
				By(nonempty, set_basic.MemberNotEmpty.At(s)))
			_, covers := a.Obtain(
				"some sequence e covers s",
				"∃e:(num → A). s ⊆ image(e, 𝕌⟨A:num⟩)",
				By(countable, CountableCover.At(s)))
			a.Take(a.TermAs[Fun[Nat, A]]("λn:num. COND(e(n) ∈ s, e(n), a)"))
			a.Show(
				"each value is e(n) ∈ s or a ∈ s, and each point of s is some e(n), kept at n",
				BySets(aIn, covers))
		}),
})}

// FiniteCountable — some f lists a finite set on the positions
// 1 .. card(s); the positions are naturals, so f run over all of ℕ
// already covers the set.
var FiniteCountable = finiteCountableThm{family.Add(registry.ProofEntry{
	Name: "FiniteCountable",
	Key:  "prop_40a2c7e4f59aa36e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "countable(s)",
	},
		func(a *Argument, s *Expr[Set[A]], finite Fact) {
			_, listed := a.Obtain(
				"some f lists s on the positions 1 .. card(s)",
				"∃f:(num → A). s = image(f, 1 .. card(s))",
				By(finite, num_segment.FiniteIndex.At(s)))
			covered := a.Have(
				"each position is a natural, so f over all of ℕ reaches every point of s",
				"s ⊆ image(f, 𝕌⟨A:num⟩)",
				BySets(listed))
			a.Show(
				"f is a sequence covering s, which is what countability asks",
				By(Normalized, covered, CountableCover.At(s)))
		}),
})}

// CountableImage — the image of a countable set is countable: it is no
// larger than the set it is the image of (CardLeImage), which is no
// larger than ℕ.
var CountableImage = countableImageThm{family.Add(registry.ProofEntry{
	Name: "CountableImage",
	Key:  "prop_d42cadfb52ca28a2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀s:set(A).",
		Hypotheses: []string{
			"countable(s)",
		},
		Conclusion: "countable(image(f, s))",
	},
		func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]], countableS Fact) {
			a.Show(
				"image(f, s) ≤ s ≤ ℕ",
				By(countableS, CardLeImage.At(f, s), CardLeCountable.At(a.TermAs[Set[B]]("image(f, s)"), s)))
		}),
})}

// CountableUnions — a countable union of countable sets is countable.
// With no sets the union is empty. Otherwise F is the range of a
// sequence e, and each e(i), a member of F, is covered by a sequence.
// Choosing one such cover C(i) for every i at once — the argument's use
// of choice — indexes the whole union by pairs of naturals: a point of
// e(i) is C(i, j) for some j, the value at (i, j) of the map
// p ↦ C(fst(p), snd(p)). So ⋃F lies inside the image of ℕ × ℕ under
// that map, which is countable.
var CountableUnions = countableUnionsThm{family.Add(registry.ProofEntry{
	Name: "CountableUnions",
	Key:  "prop_2c6a90dfefafdd4b",
	Build: family.Theorem(Statement{
		Binders: "∀F:set(set(A)).",
		Hypotheses: []string{
			"countable(F)",
			"∀s:set(A). s ∈ F ⇒ countable(s)",
		},
		Conclusion: "countable(⋃F)",
	},
		func(a *Argument, F *Expr[Set[Set[A]]], h Fact) {
			parts := a.Conjuncts(
				h,
				"F is countable",
				"every member of F is countable")
			countableF, membersCountable := parts[0], parts[1]
			nonempty := a.Unless(
				a.Term("F = ∅"),
				"with no sets to join, the union is empty",
				Given(func(b *Argument, empty Fact) {
					b.Show(
						"⋃∅ = ∅, and ∅ is countable",
						empty.Rw(),
						Simp(Fwd(set_algebra.UnionsEmpty)),
						Cite(CountableEmpty))
				}))
			e, enumerates := a.ObtainAs[Fun[Nat, Set[A]]](
				"F is the range of a sequence e",
				"∃e:(num → set(A)). F = image(e, 𝕌⟨A:num⟩)",
				By(countableF, nonempty, CountableEnumeration.At(F)))
			naturals := a.TermAs[Set[Nat]]("𝕌⟨A:num⟩")
			covered := a.Have(
				"each e(i) is a member of F, so countable, so covered by a sequence",
				"∀i:num. ∃c:(num → A). e(i) ⊆ image(c, 𝕌⟨A:num⟩)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					member := b.Have(
						"e(i) is a value of e, and F is the range of e",
						"e(i) ∈ F",
						enumerates.Rw(),
						By(set_basic.InUniv.At(i), set_image.FunInImage.At(e, naturals, i)))
					b.Show(
						"a countable set is covered by a sequence",
						By(member, membersCountable, CountableCover.At(b.TermAs[Set[A]]("e(i)"))))
				}))
			_, chosen := a.Obtain(
				"choose one cover C(i) for every i at once",
				"∃C:(num → num → A). ∀i:num. e(i) ⊆ image(C(i), 𝕌⟨A:num⟩)",
				By(covered))
			naturalPairs := a.TermAs[Set[Prod[Nat, Nat]]]("𝕌⟨A:prod(num, num)⟩")
			index := a.TermAs[Fun[Prod[Nat, Nat], A]]("λp:prod(num, num). C(fst(p), snd(p))")
			indexRange := a.TermAs[Set[A]]("image(λp:prod(num, num). C(fst(p), snd(p)), 𝕌⟨A:prod(num, num)⟩)")
			indexed := a.Have(
				"a point of ⋃F lies in some e(i), so is C(i, j) for some j, the value at the pair (i, j)",
				"⋃F ⊆ image(λp:prod(num, num). C(fst(p), snd(p)), 𝕌⟨A:prod(num, num)⟩)",
				BySets(chosen, enumerates, pairs.Fst, pairs.Snd))
			a.Show(
				"the pairs of naturals are countable, so is their image, and ⋃F lies inside it",
				By(
					indexed,
					NumPairCountable,
					CountableImage.At(index, naturalPairs),
					CountableSubset.At(a.TermAs[Set[A]]("⋃F"), indexRange)))
		}),
})}

// CountableProduct — sequences e₁ covering s and e₂ covering t cover the
// product together: a point p of it has its components in s and t, say
// fst(p) = e₁(i) and snd(p) = e₂(j), so p = (e₁(i), e₂(j)) is the value at
// (i, j) of the map (i, j) ↦ (e₁(i), e₂(j)) on ℕ × ℕ. So the product lies
// inside that map's image, which is countable because ℕ × ℕ is.
var CountableProduct = countableProductThm{family.Add(registry.ProofEntry{
	Name: "CountableProduct",
	Key:  "prop_4b5905c1047327bc",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B).",
		Hypotheses: []string{
			"countable(s)",
			"countable(t)",
		},
		Conclusion: "countable(set_cross(s, t))",
		Abbrev: Abbrev{
			{Name: "pairedSequences", Text: "λp:prod(num, num). (e₁(fst(p)), e₂(snd(p)))"},
			{Name: "pairedValues", Text: "image(«pairedSequences», 𝕌⟨A:prod(num, num)⟩)"},
		},
	},
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], h Fact) {
			parts := a.Conjuncts(
				h,
				"s is countable",
				"t is countable")
			countableS, countableT := parts[0], parts[1]
			_, coversS := a.Obtain(
				"some sequence e₁ covers s",
				"∃e₁:(num → A). s ⊆ image(e₁, 𝕌⟨A:num⟩)",
				By(countableS, CountableCover.At(s)))
			_, coversT := a.Obtain(
				"some sequence e₂ covers t",
				"∃e₂:(num → B). t ⊆ image(e₂, 𝕌⟨A:num⟩)",
				By(countableT, CountableCover.At(t)))
			pairMap := a.TermAs[Fun[Prod[Nat, Nat], Prod[A, B]]]("«pairedSequences»")
			values := a.Have(
				"each (e₁(i), e₂(j)) is a value of the map",
				"∀i j:num. (e₁(i), e₂(j)) ∈ «pairedValues»",
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat](), b.FixAs[Nat]()
					b.Show(
						"the map sends (i, j), whose components are i and j, to (e₁(i), e₂(j))",
						By(
							set_image.FunInRange.At(pairMap, b.TermAs[Prod[Nat, Nat]]("(i, j)")),
							pairs.Fst.At(i, j),
							pairs.Snd.At(i, j)))
				}))
			components := a.Have(
				"a point p of the product has fst(p) ∈ s and snd(p) ∈ t, values "+
					"e₁(i) and e₂(j), so p = (fst(p), snd(p)) is (e₁(i), e₂(j))",
				"∀p:prod(A, B). p ∈ set_cross(s, t) ⇒ ∃i j:num. p = (e₁(i), e₂(j))",
				BySets(coversS, coversT, At(set_product.InCrossProjections, s, t), pairs.PairEta))
			covered := a.Have(
				"every point of the product, being some (e₁(i), e₂(j)), is the value at (i, j)",
				"set_cross(s, t) ⊆ «pairedValues»",
				BySets(components, values))
			product := a.TermAs[Set[Prod[A, B]]]("set_cross(s, t)")
			pairImage := a.TermAs[Set[Prod[A, B]]]("«pairedValues»")
			natPairs := a.TermAs[Set[Prod[Nat, Nat]]]("𝕌⟨A:prod(num, num)⟩")
			a.Show(
				"the product lies inside the image of ℕ × ℕ, which is countable",
				By(
					covered,
					CountableSubset.At(product, pairImage),
					CountableImage.At(pairMap, natPairs),
					NumPairCountable))
		}),
})}

// CountableUnion — two countable sets have countable union: the finite
// family {s, t} is countable, and both its members are countable, so the
// countable-union theorem applies to it.
var CountableUnion = countableUnionThm{family.Add(registry.ProofEntry{
	Name: "CountableUnion",
	Key:  "prop_f8e6759e50f5e0ee",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"countable(s)",
			"countable(t)",
		},
		Conclusion: "countable(s ∪ t)",
	},
		func(a *Argument, s, t *Expr[Set[A]], h Fact) {
			a.Do(Simp(Rev(set_algebra.UnionsPair)))
			membersCountable := a.Have(
				"each member of the pair is one of the two countable sets",
				"∀u:set(A). u ∈ {s, t} ⇒ countable(u)",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("u")
					inPair := b.Assume()
					other := b.Unless(
						b.TermAs[Bool]("u = s"),
						"a member equal to s is countable",
						Given(func(c *Argument, equal Fact) {
							c.Show(
								"s is countable",
								By(Normalized, equal, h))
						}))
					isT := b.Have(
						"the other member of the pair is t",
						"u = t",
						BySets(other, inPair))
					b.Show(
						"t is countable",
						By(Normalized, isT, h))
				}))
			pair := a.TermAs[Set[Set[A]]]("{s, t}")
			rules := a.Conjuncts(
				finite_set.FiniteRules.Inst[Set[A]](),
				"the empty family is finite",
				"inserting a set preserves finiteness")
			a.Show(
				"the union of the countable family {s, t} is countable",
				By(
					membersCountable,
					rules[0],
					rules[1].At(t, a.TermAs[Set[Set[A]]]("∅")),
					rules[1].At(s, a.TermAs[Set[Set[A]]]("{t}")),
					FiniteCountable.At(pair),
					CountableUnions.At(pair)))
		}),
})}

// CountableFiniteSubsets — finite subsets of a countable set are countable:
// a sequence covering the set puts every finite subset inside the image of
// one finite initial segment, and each such image has finitely many subsets.
var CountableFiniteSubsets = countableFiniteSubsetsThm{family.Add(registry.ProofEntry{
	Name: "CountableFiniteSubsets",
	Key:  "prop_15c67e3b8fa070d1",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A).",
		Hypotheses: []string{"countable(s)"},
		Conclusion: "countable({t:set(A) | finite(t) ∧ t ⊆ s})",
	}, func(a *Argument, s *Expr[Set[A]], countableS Fact) {
		f, covers := a.ObtainAs[Fun[Nat, A]](
			"a sequence f covers s",
			"∃f:(num → A). s ⊆ image(f, 𝕌⟨A:num⟩)",
			By(countableS, CountableCover.At(s)))
		P, pDef := a.LetAs[Fun[Nat, Set[Set[A]]]]("P",
			"λn:num. {t:set(A) | t ⊆ image(f, 0 .. n)}")
		naturals := a.TermAs[Set[Nat]]("𝕌⟨A:num⟩")
		finiteStages := a.Have(
			"each finite initial segment has finitely many subsets",
			"∀n:num. finite(P(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				segment := b.TermAs[Set[Nat]]("0 .. n")
				b.Show(
					"the segment image is finite, so its family of subsets is finite",
					By(
						pDef,
						num_segment.Finite.At(b.TermAs[Nat]("0"), n),
						finite_set.FiniteImage.At(f, segment),
						finite_set.FinitePowerset.At(b.TermAs[Set[A]]("image(f, 0 .. n)"))))
			}))
		finiteFamily := a.Have(
			"every stage in the image of P is finite",
			"∀u:set(set(A)). u ∈ image(P, 𝕌) ⇒ finite(u)",
			BySets(finiteStages))
		stages := a.TermAs[Set[Set[Set[A]]]]("image(P, 𝕌)")
		countableUnion := a.Have(
			"countably many finite families have a countable union",
			"countable(⋃image(P, 𝕌))",
			By(
				finiteFamily,
				NumCountable,
				CountableImage.At(P, naturals),
				FiniteCountable.Inst[Set[A]](),
				CountableUnions.Inst[Set[A]]().At(stages)))
		bounded := a.Have(
			"every finite subset of s lies in one stage",
			"∀t:set(A). finite(t) ∧ t ⊆ s ⇒ ∃n:num. t ⊆ image(f, 0 .. n)",
			Derive(func(b *Argument) {
				t := b.FixAs[Set[A]]()
				finiteSubset := b.Assume()
				imageLaw := b.Simplified(finite_set.FiniteSubsetImage.At(f, naturals, t))
				u, represented := b.ObtainAs[Set[Nat]](
					"a finite set u of sequence indices represents t",
					"∃u:set(num). finite(u) ∧ t = image(f, u)",
					By(imageLaw, covers, finiteSubset, set_order.SubsetTrans.At(t, s, b.TermAs[Set[A]]("image(f, 𝕌)"))))
				n, bound := b.ObtainAs[Nat](
					"the finite index set u is bounded",
					"∃n:num. u ⊆ 0 .. n",
					By(represented, num_segment.FiniteIffBounded.At(u)))
				b.Take(n)
				b.Show(
					"the image of u lies in the image of its bounding segment",
					BySets(bound, represented))
			}))
		included := a.Have(
			"the union of the stages contains every finite subset of s",
			"{t:set(A) | finite(t) ∧ t ⊆ s} ⊆ ⋃image(P, 𝕌)",
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				t := b.FixAs[Set[A]]("t")
				member := b.Assume()
				_, bound := b.ObtainAs[Nat](
					"choose a stage containing t",
					"∃n:num. t ⊆ image(f, 0 .. n)",
					BySets(bounded.At(t), member))
				b.Show(
					"t belongs to that stage, hence to their union",
					BySets(pDef, bound))
			}))
		a.Show(
			"a subset of the countable union is countable",
			By(
				countableUnion,
				included,
				CountableSubset.Inst[Set[A]]().At(
					a.TermAs[Set[Set[A]]]("{t:set(A) | finite(t) ∧ t ⊆ s}"),
					a.TermAs[Set[Set[A]]]("⋃image(P, 𝕌)"))))
	}),
})}

// CountableFiniteModifications — the functions that differ from a fixed
// function a at finitely many points, each such point in a countable set J
// and the value there drawn from a countable set C(i), are countably many.
// Each is fixed by its changed-coordinate graph, the pairs (i, f(i)) at the
// points where it differs from a: a finite subset of J × ⋃image(C, J),
// which is countable, so it has countably many finite subsets.
var CountableFiniteModifications = countableFiniteModificationsThm{family.Add(registry.ProofEntry{
	Name: "CountableFiniteModifications",
	Key:  "prop_2fa7bc3c9b043d91",
	Build: family.Sections(Statement{
		Binders: "∀J:set(I). ∀a:(I → A). ∀C:(I → set(A)).",
		Hypotheses: []string{
			"countable(J)",
			"∀i:I. i ∈ J ⇒ countable(C(i))",
		},
		Conclusion: "countable( " +
			"    {f:(I → A) | finite({i:I | f(i) ≠ a(i)}) ∧ (∀i:I. f(i) ≠ a(i) ⇒ i ∈ J ∧ f(i) ∈ C(i))})",
		Abbrev: Abbrev{
			{Name: "modifications", Text: "{f:(I → A) | " +
				"    finite({i:I | f(i) ≠ a(i)}) ∧ (∀i:I. f(i) ≠ a(i) ⇒ i ∈ J ∧ f(i) ∈ C(i))}"},
			{Name: "changedGraph", Text: "λa:(I → A). λf:(I → A). image(λi:I. (i, f(i)), {i:I | f(i) ≠ a(i)})"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		graphDetermines := ctx.Lemma(Statement{
			Binders: "∀a f g:(I → A).",
			Hypotheses: []string{
				"«changedGraph»(a, f) = «changedGraph»(a, g)",
			},
			Conclusion: "f = g",
		}, func(b *Argument, a, f, g *Expr[Fun[I, A]], equalGraphs Fact) {
			b.Show(
				"equal graphs of the changed coordinates determine the function",
				BySets(equalGraphs, pairs.PairEq))
		})
		return ctx.Theorem(headline, func(
			b *Argument,
			J *Expr[Set[I]],
			a *Expr[Fun[I, A]],
			C *Expr[Fun[I, Set[A]]],
			assumptions Fact,
		) {
			countableFactors := b.Have(
				"every chosen coordinate set is countable",
				"∀u:set(A). u ∈ image(C, J) ⇒ countable(u)",
				BySets(assumptions))
			values := b.TermAs[Set[A]]("⋃image(C, J)")
			countableValues := b.Have(
				"all chosen coordinate values together form a countable set",
				"countable(⋃image(C, J))",
				By(
					countableFactors,
					assumptions,
					CountableImage.At(C, J),
					CountableUnions.At(b.TermAs[Set[Set[A]]]("image(C, J)"))))
			graphs := b.TermAs[Set[Set[Prod[I, A]]]](
				"{t:set(prod(I, A)) | finite(t) ∧ t ⊆ set_cross(J, ⋃image(C, J))}")
			countableGraphs := b.Have(
				"finite graphs in the countable coordinate and value set are countable",
				"countable({t:set(prod(I, A)) | finite(t) ∧ t ⊆ set_cross(J, ⋃image(C, J))})",
				By(
					countableValues,
					assumptions,
					CountableProduct.At(J, values),
					CountableFiniteSubsets.At(b.TermAs[Set[Prod[I, A]]]("set_cross(J, ⋃image(C, J))"))))
			graphIn := b.Have(
				"each finite modification has such a finite graph",
				Statement{
					Binders: "∀f:(I → A).",
					Hypotheses: []string{
						"f ∈ «modifications»",
					},
					Conclusion: "finite(«changedGraph»(a, f)) ∧ «changedGraph»(a, f) ⊆ set_cross(J, ⋃image(C, J))",
				},
				Derive(func(c *Argument) {
					c.FixAs[Fun[I, A]]("f")
					member := c.Assume()
					c.Show(
						"the modification has a finite graph in the coordinate and value product",
						SplitConj(
							Case(
								"the changed-coordinate graph is finite",
								By(
									member,
									finite_set.FiniteImage.At(
										c.TermAs[Fun[I, Prod[I, A]]]("λi:I. (i, f(i))"), c.TermAs[Set[I]]("{i:I | f(i) ≠ a(i)}")))),
							Case(
								"every graph pair uses an active coordinate and a chosen value",
								Simp(Fwd(set_image.ImageSubsetIff)),
								Derive(func(d *Argument) {
									i := d.FixAs[I]("i")
									changed := d.Assume()
									d.Show(
										"the pair belongs to the coordinate and value product",
										BySets(changed, member, set_product.InCross.At(J, values, i, d.TermAs[A]("f(i)"))))
								}))))
				}))
			graphMap := b.TermAs[Fun[Fun[I, A], Set[Prod[I, A]]]]("«changedGraph»(a)")
			injective := b.Have(
				"the graph encoding is injective on finite modifications",
				"injective_on(«modifications», «changedGraph»(a))",
				By(functions.InjectiveOnDef, At(graphDetermines, a)))
			embeds := b.Have(
				"finite modifications inject into the countable family of finite graphs",
				"card_le(«modifications», {t:set(prod(I, A)) | finite(t) ∧ t ⊆ set_cross(J, ⋃image(C, J))})",
				Unfold(CardLeDef),
				Witness(graphMap),
				By(graphIn, injective))
			b.Show(
				"the graph encoding makes the modifications countable",
				By(
					countableGraphs,
					embeds,
					CardLeCountable.At(b.TermAs[Set[Fun[I, A]]]("«modifications»"), graphs)))
		})
	}),
})}
