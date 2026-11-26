// powerset_encoding.go — over a general inner type A, the powerset of
// prod(num, A) holds a sequence of its members, so a pair of them, a
// natural beside each, its finitely supported multiplicities, and the
// finitely supported coefficient functions on those with their
// coefficients in a set that injects. Then an index type closed under
// pairs, sequences, and functions that are constant outside a finite
// set. These explicit encodings use choice and countable enumeration,
// not infinite cardinal multiplication or a well-ordering of the index
// type.

package cardinal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// The subsets of prod(num, A) that the members over one inner type A
// size, their pairs and their sequences.
type (
	_Subset            = Set[Prod[Nat, A]]
	_PairOfSubsets     = Prod[_Subset, _Subset]
	_SequenceOfSubsets = Fun[Nat, _Subset]
)

// SequencesIntoPowerSet — a sequence of subsets of prod(num, A) is one
// subset: the n-th is written on the natural coordinates paired with n.
// A point (num_pair(n, j), a) lies in the code of s just when (j, a) lies
// in s(n), num_pair being one-to-one. So two sequences with one code have
// the same points in their n-th terms at every n, and a sequence is the
// sequence of its terms.
var SequencesIntoPowerSet = sequencesIntoPowerSetThm{family.Add(registry.ProofEntry{
	Name: "SequencesIntoPowerSet",
	Key:  "prop_92219492df6a9656",
	Build: family.Theorem(Statement{
		Conclusion: "card_le(𝕌⟨A:num → set(prod(num, A))⟩, 𝕌⟨A:set(prod(num, A))⟩)",
		Abbrev: Abbrev{
			{Name: "code", Text: "λs:num → set(prod(num, A)). " +
				"    {(num_pair(n, j), a) | n:num, j:num, a:A | (j, a) ∈ s(n)}"},
		},
	},
		Opening(Chain(Unfold(CardLeDef), Unfold(functions.InjectiveOnDef)), func(a *Argument) {
			a.Take(a.TermAs[Fun[_SequenceOfSubsets, _Subset]]("«code»"))

			// What a code holds at each index.
			atIndex := a.Have(
				"(num_pair(n, j), a) lies in the code of s just "+
					"when (j, a) lies in s(n), num_pair being one-to-one",
				"∀s:num → set(prod(num, A)). ∀n j:num. ∀a:A. (num_pair(n, j), a) ∈ «code»(s) ⇔ (j, a) ∈ s(n)",
				BySets(
					datatype_universe.NumPairInjective,
					pairs.PairEq.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[A]())))

			decode := a.Have(
				"a code determines its sequence",
				"∀s t:(num → set(prod(num, A))). «code»(s) = «code»(t) ⇒ s = t",
				Derive(func(b *Argument) {
					s, t := b.FixAs[_SequenceOfSubsets]("s"), b.FixAs[_SequenceOfSubsets]("t")
					sameCode := b.Assume()
					terms := b.Have(
						"the n-th terms hold the same points (j, a), those with (num_pair(n, j), a) in the one code",
						"∀n:num. s(n) = t(n)",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							c.Show(
								"a point (j, a) lies in s(n) just when (num_pair(n, "+
									"j), a) lies in the code of s, which is the code of t",
								By(
									atIndex.At(s, n),
									atIndex.At(t, n),
									sameCode,
									pairs.PairSurjective.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[A]()),
									set_basic.Extension.At(c.TermAs[_Subset]("s(n)"), c.TermAs[_Subset]("t(n)"))))
						}))
					b.Show(
						"a sequence is the sequence of its terms",
						By(Normalized, terms))
				}))

			a.Show(
				"each code is a subset of prod(num, A), and a code determines its sequence",
				BySets(decode))
		})),
	Reading: "No hypothesis, at every inner type A: the " +
		"natural coordinate carries the index of the sequence.",
})}

// PairsIntoPowerSet — a pair of subsets of prod(num, A) is one subset:
// the pair (S, T) is the sequence S, T, T, …, which returns S at 0 and T
// at 1, 1 being other than 0, so two pairs with one sequence have the
// same coordinates, and a pair is the pair of its coordinates; the
// sequences of subsets are one subset (SequencesIntoPowerSet).
var PairsIntoPowerSet = pairsIntoPowerSetThm{family.Add(registry.ProofEntry{
	Name: "PairsIntoPowerSet",
	Key:  "prop_36345cb506989b3",
	Build: family.Theorem("card_le(𝕌⟨A:prod(set(prod(num, A)), set(prod(num, A)))⟩, "+
		"    𝕌⟨A:set(prod(num, A))⟩)",
		func(a *Argument) {
			pairsOfSubsets := a.TermAs[Set[_PairOfSubsets]]("𝕌⟨A:prod(set(prod(num, A)), set(prod(num, A)))⟩")
			sequences := a.TermAs[Set[_SequenceOfSubsets]]("𝕌⟨A:num → set(prod(num, A))⟩")
			subsets := a.TermAs[Set[_Subset]]("𝕌⟨A:set(prod(num, A))⟩")
			intoSequences := a.Have(
				"a pair (S, T) is the sequence S, T, T, …, and that sequence determines its pair",
				"card_le(𝕌⟨A:prod(set(prod(num, A)), set(prod(num, A)))⟩, 𝕌⟨A:num → set(prod(num, A))⟩)",
				Unfold(CardLeDef),
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[_PairOfSubsets, _SequenceOfSubsets]](
						"λp:prod(set(prod(num, A)), set(prod(num, A))). λn:num. COND(n = 0, fst(p), snd(p))"))
					b.Show(
						"the sequence of p returns fst(p) at 0 and snd(p) at 1, and a pair is the pair of its coordinates",
						Unfold(functions.InjectiveOnDef),
						BySets(nat_arith.OneNotZero, pairs.PairEta))
				}))
			a.Show(
				"and the sequences inject into the subsets",
				By(intoSequences, SequencesIntoPowerSet, CardLeTrans.At(pairsOfSubsets, sequences, subsets)))
		}),
	Reading: "No hypothesis: the natural coordinate carries the index of a sequence " +
		"whatever the inner type A is, so the statement holds at every A, prod(A, B) among " +
		"them. It is the room for a pair of members of the powerset, read where a set of " +
		"pairs — a localization's numerators and denominators — is sized against the powerset.",
})}

// PowerSetTimesNum — a natural beside a subset of prod(num, A) is
// encoded as one subset: (n, S) goes to the pair ({(n, a) | a : A}, S),
// whose first coordinate, nonempty, names n alone, and the pairs of
// subsets are one subset (PairsIntoPowerSet).
var PowerSetTimesNum = powerSetTimesNumThm{family.Add(registry.ProofEntry{
	Name: "PowerSetTimesNum",
	Key:  "prop_cbf40cedcbb3479c",
	Build: family.Theorem("card_le(𝕌⟨A:prod(num, set(prod(num, A)))⟩, 𝕌⟨A:set(prod(num, A))⟩)",
		func(a *Argument) {
			numberAndSubset := a.TermAs[Set[Prod[Nat, _Subset]]]("𝕌⟨A:prod(num, set(prod(num, A)))⟩")
			pairsOfSubsets := a.TermAs[Set[_PairOfSubsets]]("𝕌⟨A:prod(set(prod(num, A)), set(prod(num, A)))⟩")
			subsets := a.TermAs[Set[_Subset]]("𝕌⟨A:set(prod(num, A))⟩")
			intoPairs := a.Have(
				"the natural is recorded by its tagged pairs, beside the unchanged subset",
				"card_le(𝕌⟨A:prod(num, set(prod(num, A)))⟩, 𝕌⟨A:prod(set(prod(num, A)), set(prod(num, A)))⟩)",
				Unfold(CardLeDef),
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Prod[Nat, _Subset], _PairOfSubsets]](
						"λp:prod(num, set(prod(num, A))). ({(fst(p), a) | a:A | ⊤}, snd(p))"))
					b.Show(
						"the two subsets form a code that determines the source pair",
						Unfold(functions.InjectiveOnDef),
						SplitConj(
							Case(
								"each code is a pair of subsets",
								BySets()),
							Case(
								"the tagged pairs determine the natural and the second coordinate retains the subset",
								Derive(func(c *Argument) {
									c.FixAs[Prod[Nat, _Subset]]("x")
									c.FixAs[Prod[Nat, _Subset]]("y")
									sameCode := c.Assume()
									c.Do(
										sameCode.Simp(Fwd(pairs.PairEq.Inst(TypeBinder.BindA[_Subset](), TypeBinder.BindB[_Subset]()))))
									c.Show(
										"equal tagged sets recover the natural coordinate, and both coordinates recover the source pair",
										CalcEq(
											Leg(
												c.TermAs[Prod[Nat, _Subset]]("(fst(x), snd(x))"),
												"x is the pair of its coordinates",
												Cite(pairs.PairEta.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[_Subset]()))),
											Leg(
												c.TermAs[Prod[Nat, _Subset]]("(fst(y), snd(y))"),
												"a tagged point in the common first subset determines the natural coordinate",
												BySets(
													sameCode,
													pairs.PairEq.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[A]()),
													pairs.PairEq.At(
														c.TermAs[Nat]("fst(x)"),
														c.TermAs[_Subset]("snd(x)"),
														c.TermAs[Nat]("fst(y)"),
														c.TermAs[_Subset]("snd(y)")))),
											FinalLeg(
												"the coordinates of y form y",
												Cite(pairs.PairEta.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[_Subset]())))))
								}))))
				}))
			a.Show(
				"pairs of subsets inject into the subsets",
				By(intoPairs, PairsIntoPowerSet, CardLeTrans.At(numberAndSubset, pairsOfSubsets, subsets)))
		}),
	Reading: "No hypothesis: the encoding works for every inner type A, a one-point type " +
		"included (then the statement says ℕ × 𝒫(ℕ) injects into 𝒫(ℕ)). Read at n = 0 and at " +
		"n = 1 it gives two injections of the powerset into itself with disjoint images.",
})}

// FiniteMultisetsIntoPowerSet — the finitely supported maps from the
// subsets of prod(num, A) to the naturals inject into those subsets: a
// sequence runs through a map's finite support, and the sequence of its
// points paired with their values is one subset; the map is zero off it.
var FiniteMultisetsIntoPowerSet = finiteMultisetsIntoPowerSetThm{family.Add(registry.ProofEntry{
	Name: "FiniteMultisetsIntoPowerSet",
	Key:  "prop_b49e94d326fbac2b",
	Build: family.Theorem("card_le({m:(set(prod(num, A)) → num) | finite(fun_support(0, m))}, "+
		"    𝕌⟨A:set(prod(num, A))⟩)",
		func(a *Argument) {
			numberAndSubset := a.TermAs[Set[Prod[Nat, _Subset]]]("𝕌⟨A:prod(num, set(prod(num, A)))⟩")
			sequences := a.TermAs[Set[_SequenceOfSubsets]]("𝕌⟨A:num → set(prod(num, A))⟩")
			subsets := a.TermAs[Set[_Subset]]("𝕌⟨A:set(prod(num, A))⟩")
			_, pairCode := a.ObtainAs[Fun[Prod[Nat, _Subset], _Subset]](
				"choose an injection coding a multiplicity beside a subset",
				"∃j:(prod(num, set(prod(num, A))) → set(prod(num, A))). "+
					"    injective_on(𝕌⟨A:prod(num, set(prod(num, A)))⟩, j)",
				By(Normalized, PowerSetTimesNum, CardLeDef.At(numberAndSubset, subsets)))
			_, sequenceCode := a.ObtainAs[Fun[_SequenceOfSubsets, _Subset]](
				"choose an injection coding a sequence of subsets",
				"∃σ:((num → set(prod(num, A))) → set(prod(num, A))). injective_on(𝕌⟨A:num → set(prod(num, A))⟩, σ)",
				By(Normalized, SequencesIntoPowerSet, CardLeDef.At(sequences, subsets)))

			covers := a.Have(
				"the finite support of each map is covered by a sequence",
				Statement{
					Binders:    "∀m:(set(prod(num, A)) → num).",
					Hypotheses: []string{"finite(fun_support(0, m))"},
					Conclusion: "∃e:(num → set(prod(num, A))). ∀x:set(prod(num, A)). " +
						"    ¬(m(x) = 0) ⇒ x ∈ image(e, 𝕌⟨A:num⟩)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[_Subset, Nat]]("m")
					finite := b.Assume()
					support := b.TermAs[Set[_Subset]]("fun_support(0, m)")
					e, covered := b.ObtainAs[_SequenceOfSubsets](
						"a finite set is countable, so some sequence covers the support",
						"∃e:(num → set(prod(num, A))). fun_support(0, m) ⊆ image(e, 𝕌⟨A:num⟩)",
						By(finite, FiniteCountable.At(support), CountableCover.At(support)))
					b.Take(e)
					b.Show(
						"every nonzero point belongs to the support and hence to the cover",
						BySets(covered))
				}))
			_, listed := a.ObtainAs[Fun[Fun[_Subset, Nat], _SequenceOfSubsets]](
				"choose such a covering sequence E(m) for every finite-support map",
				"∃E:((set(prod(num, A)) → num) → num → set(prod(num, A))). ∀m:(set(prod(num, A)) → num). "+
					"    finite(fun_support(0, m)) ⇒ ∀x:set(prod(num, A)). ¬(m(x) = 0) ⇒ x ∈ image(E(m), 𝕌⟨A:num⟩)",
				By(covers))
			_, listDef := a.LetAs[Fun[Fun[_Subset, Nat], _SequenceOfSubsets]](
				"L", "λm:(set(prod(num, A)) → num). λk:num. j((m(E(m)(k)), E(m)(k)))")
			code, codeDef := a.LetAs[Fun[Fun[_Subset, Nat], _Subset]](
				"code", "λm:(set(prod(num, A)) → num). σ(L(m))")

			decode := a.Have(
				"two finite-support maps with one code are equal",
				Statement{
					Binders: "∀f g:(set(prod(num, A)) → num).",
					Hypotheses: []string{
						"finite(fun_support(0, f))",
						"finite(fun_support(0, g))",
						"code(f) = code(g)",
					},
					Conclusion: "f = g",
				},
				Derive(func(b *Argument) {
					f, g := b.FixAs[Fun[_Subset, Nat]]("f"), b.FixAs[Fun[_Subset, Nat]]("g")
					parts := b.Conjuncts(
						b.Assume(),
						"f has finite support",
						"g has finite support",
						"f and g have one code")
					finiteF, finiteG, sameCode := parts[0], parts[1], parts[2]
					b.Do(sameCode.Simp(Fwd(codeDef)))
					listF, listG := b.TermAs[_SequenceOfSubsets]("L(f)"), b.TermAs[_SequenceOfSubsets]("L(g)")
					entries := b.Have(
						"the injective sequence code determines every list entry",
						"∀k:num. L(f)(k) = L(g)(k)",
						Derive(func(c *Argument) {
							injective := c.Unfolded(sequenceCode, functions.InjectiveOnDef)
							c.Show(
								"the two coded sequences agree pointwise",
								By(
									Normalized,
									injective.At(listF, listG),
									sameCode,
									set_basic.InUniv.At(listF),
									set_basic.InUniv.At(listG)))
						}))
					b.Do(entries.Simp(Fwd(listDef)))
					listedAlike := b.Have(
						"f and g agree at every point of either list",
						"∀k:num. f(E(f)(k)) = g(E(f)(k)) ∧ f(E(g)(k)) = g(E(g)(k))",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							injective := c.Unfolded(pairCode, functions.InjectiveOnDef)
							entryF := c.TermAs[Prod[Nat, _Subset]]("(f(E(f)(k)), E(f)(k))")
							entryG := c.TermAs[Prod[Nat, _Subset]]("(g(E(g)(k)), E(g)(k))")
							c.Show(
								"the injective pair code recovers both the listed point and its multiplicity",
								By(
									entries.At(k),
									injective.At(entryF, entryG),
									pairs.PairEq.At(c.TermAs[Nat]("f(E(f)(k))"), c.TermAs[_Subset]("E(f)(k)"),
										c.TermAs[Nat]("g(E(g)(k))"), c.TermAs[_Subset]("E(g)(k)")),
									set_basic.InUniv.At(entryF),
									set_basic.InUniv.At(entryG)))
						}))
					agreement := b.TermAs[Set[_Subset]]("λy:set(prod(num, A)). f(y) = g(y)")
					onListF := b.Have(
						"f and g agree on the range of E(f)",
						"∀y:set(prod(num, A)). y ∈ image(E(f), 𝕌⟨A:num⟩) ⇒ f(y) = g(y)",
						By(listedAlike, Where(set_image.ForallInImage, "P", agreement)))
					onListG := b.Have(
						"f and g agree on the range of E(g)",
						"∀y:set(prod(num, A)). y ∈ image(E(g), 𝕌⟨A:num⟩) ⇒ f(y) = g(y)",
						By(listedAlike, Where(set_image.ForallInImage, "P", agreement)))
					b.Show(
						"each nonzero point lies on its cover; outside both covers the two values are zero",
						Funext(),
						Derive(func(c *Argument) {
							x := c.FixAs[_Subset]("x")
							c.Show(
								"the two values agree",
								By(Normalized, finiteF, finiteG, listed.At(f, x), listed.At(g, x), onListF.At(x), onListG.At(x)))
						}))
				}))
			a.Show(
				"the code sends the finite-support maps injectively into the subsets",
				Unfold(CardLeDef),
				Derive(func(b *Argument) {
					b.Take(code)
					b.Show(
						"every code is a subset, and its finite-support map is determined",
						Unfold(functions.InjectiveOnDef),
						BySets(decode))
				}))
		}),
	Reading: "Finiteness of the support is load-bearing: every subset s gives the indicator " +
		"map with value 1 on s, so all maps from the subsets to ℕ outnumber the subsets " +
		"(CantorUniv). The powerset is infinite through its natural coordinate whatever A is; for " +
		"a one-point A the statement is that the finitely supported maps 𝒫(ℕ) → ℕ inject into 𝒫(ℕ).",
})}

// PolynomialsIntoPowerSet — over a set C of coefficients that injects
// into the subsets of prod(num, A), the coefficient functions on maps
// from those subsets to the naturals inject too, when only finitely many
// maps carry a coefficient other than zero, each of those has finite
// support, and each such coefficient lies in C. The function zero
// everywhere goes to the pair code of (∅, ∅), any other to that of 𝕌
// beside the sequence code of its finite graph off zero, each map coded
// beside its coefficient.
var PolynomialsIntoPowerSet = polynomialsIntoPowerSetThm{family.Add(registry.ProofEntry{
	Name: "PolynomialsIntoPowerSet",
	Key:  "prop_4286f6308e02e0d1",
	Build: family.Theorem(Statement{
		Binders: "∀C:set(B). ∀zero:B.",
		Hypotheses: []string{
			"card_le(C, 𝕌⟨A:set(prod(num, A))⟩)",
		},
		Conclusion: "card_le({f:(set(prod(num, A)) → num) → B | " +
			"        finite(fun_support(zero, f)) ∧ " +
			"        (∀m:(set(prod(num, A)) → num). ¬(f(m) = zero) ⇒ finite(fun_support(0, m)) ∧ f(m) ∈ C)}, " +
			"    𝕌⟨A:set(prod(num, A))⟩)",
	},
		func(a *Argument, C *Expr[Set[B]], zero *Expr[B], coefficientBound Fact) {
			type (
				monomial    = Fun[_Subset, Nat]
				polynomial  = Fun[monomial, B]
				supportList = Fun[Nat, monomial]
			)
			_, monomialDef := a.LetAs[Set[monomial]](
				"M", "{m:(set(prod(num, A)) → num) | finite(fun_support(0, m))}")
			_, polynomialDef := a.LetAs[Set[polynomial]](
				"P",
				"{f:((set(prod(num, A)) → num) → B) | "+
					"    finite(fun_support(zero, f)) ∧ "+
					"    (∀m:(set(prod(num, A)) → num). ¬(f(m) = zero) ⇒ finite(fun_support(0, m)) ∧ f(m) ∈ C)}")
			subsets := a.TermAs[Set[_Subset]]("𝕌⟨A:set(prod(num, A))⟩")
			pairsOfSubsets := a.TermAs[Set[_PairOfSubsets]]("𝕌⟨A:prod(set(prod(num, A)), set(prod(num, A)))⟩")
			sequences := a.TermAs[Set[_SequenceOfSubsets]]("𝕌⟨A:num → set(prod(num, A))⟩")
			_, monomialCode := a.ObtainAs[Fun[monomial, _Subset]](
				"choose an injection of the finite-support monomials into the subsets",
				"∃j₁:((set(prod(num, A)) → num) → set(prod(num, A))). injective_on(M, j₁)",
				Simp(Fwd(monomialDef)),
				By(
					FiniteMultisetsIntoPowerSet,
					CardLeDef.Inst(TypeBinder.BindA[monomial](), TypeBinder.BindB[_Subset]())))
			_, coefficientCode := a.ObtainAs[Fun[B, _Subset]](
				"choose an injection of C into the subsets",
				"∃j₂:(B → set(prod(num, A))). injective_on(C, j₂)",
				By(Normalized, coefficientBound, CardLeDef.At(C, subsets)))
			_, pairCode := a.ObtainAs[Fun[_PairOfSubsets, _Subset]](
				"choose an injection coding pairs of subsets",
				"∃c:(prod(set(prod(num, A)), set(prod(num, A))) → set(prod(num, A))). "+
					"    injective_on(𝕌⟨A:prod(set(prod(num, A)), set(prod(num, A)))⟩, c)",
				By(Normalized, PairsIntoPowerSet, CardLeDef.At(pairsOfSubsets, subsets)))
			_, sequenceCode := a.ObtainAs[Fun[_SequenceOfSubsets, _Subset]](
				"choose an injection coding sequences of subsets",
				"∃σ:((num → set(prod(num, A))) → set(prod(num, A))). injective_on(𝕌⟨A:num → set(prod(num, A))⟩, σ)",
				By(Normalized, SequencesIntoPowerSet, CardLeDef.At(sequences, subsets)))

			enumerable := a.Have(
				"the nonempty support of an eligible polynomial is the range of a sequence",
				Statement{
					Binders:    "∀f:((set(prod(num, A)) → num) → B).",
					Hypotheses: []string{"f ∈ P", "¬(fun_support(zero, f) = ∅)"},
					Conclusion: "∃e:(num → (set(prod(num, A)) → num)). fun_support(zero, f) = image(e, 𝕌⟨A:num⟩)",
				},
				Derive(func(b *Argument) {
					b.FixAs[polynomial]("f")
					eligible := b.Assume()
					b.Do(eligible.Simp(Fwd(polynomialDef)))
					support := b.TermAs[Set[monomial]]("fun_support(zero, f)")
					b.Show(
						"a nonempty finite set is countable and has an exact enumeration",
						By(eligible, FiniteCountable.At(support), CountableEnumeration.At(support)))
				}))
			_, listed := a.ObtainAs[Fun[polynomial, supportList]](
				"choose an exact support enumeration E(f) for each nonzero eligible polynomial",
				"∃E:(((set(prod(num, A)) → num) → B) → num → (set(prod(num, A)) → num)). "+
					"∀f:((set(prod(num, A)) → num) → B). "+
					"    f ∈ P ∧ ¬(fun_support(zero, f) = ∅) ⇒ fun_support(zero, f) = image(E(f), 𝕌⟨A:num⟩)",
				By(enumerable))
			a.Do(listed.Simp(Fwd(polynomialDef)))
			entryValid := a.Have(
				"every listed entry supplies the domains of both guarded injections",
				Statement{
					Binders:    "∀f:((set(prod(num, A)) → num) → B). ∀k:num.",
					Hypotheses: []string{"f ∈ P", "¬(fun_support(zero, f) = ∅)"},
					Conclusion: "E(f)(k) ∈ M ∧ f(E(f)(k)) ∈ C",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[polynomial]("f")
					b.FixAs[Nat]("k")
					eligible := b.Assume()
					b.Do(eligible.Simp(Fwd(polynomialDef)))
					b.Show(
						"an exact support entry has nonzero coefficient, "+
							"hence a finite-support monomial and a coefficient in C",
						Simp(Fwd(monomialDef)),
						BySets(eligible, listed.At(f)))
				}))
			a.Do(entryValid.Simp(Fwd(polynomialDef)))
			_, listDef := a.LetAs[Fun[polynomial, _SequenceOfSubsets]](
				"L", "λf:((set(prod(num, A)) → num) → B). λk:num. c((j₁(E(f)(k)), j₂(f(E(f)(k)))))")
			_, taggedDef := a.LetAs[Fun[polynomial, _PairOfSubsets]](
				"tagged",
				"λf:((set(prod(num, A)) → num) → B). "+
					"    (COND(fun_support(zero, f) = ∅, ∅⟨A:prod(num, A)⟩, 𝕌⟨A:prod(num, A)⟩), "+
					"        COND(fun_support(zero, f) = ∅, ∅⟨A:prod(num, A)⟩, σ(L(f))))")
			code, codeDef := a.LetAs[Fun[polynomial, _Subset]](
				"code", "λf:((set(prod(num, A)) → num) → B). c(tagged(f))")

			decode := a.Have(
				"the tagged code determines an eligible polynomial",
				"∀f g:((set(prod(num, A)) → num) → B). f ∈ P ∧ g ∈ P ∧ code(f) = code(g) ⇒ f = g",
				Derive(func(b *Argument) {
					f, g := b.FixAs[polynomial]("f"), b.FixAs[polynomial]("g")
					parts := b.Conjuncts(
						b.Assume(),
						"f is eligible",
						"g is eligible",
						"f and g have one code")
					eligibleF, eligibleG, sameCode := parts[0], parts[1], parts[2]
					b.Do(
						eligibleF.Simp(Fwd(polynomialDef)), eligibleG.Simp(Fwd(polynomialDef)), sameCode.Simp(Fwd(codeDef)))
					taggedF, taggedG := b.TermAs[_PairOfSubsets]("tagged(f)"), b.TermAs[_PairOfSubsets]("tagged(g)")
					sameTagged := b.Have(
						"the injective pair code recovers the tagged pair",
						"tagged(f) = tagged(g)",
						Derive(func(c *Argument) {
							injective := c.Unfolded(pairCode, functions.InjectiveOnDef)
							c.Show(
								"equal outer codes have equal tagged pairs",
								By(
									injective.At(taggedF, taggedG),
									sameCode,
									set_basic.InUniv.At(taggedF),
									set_basic.InUniv.At(taggedG)))
						}))
					b.Do(sameTagged.Simp(
						Fwd(taggedDef),
						Fwd(pairs.PairEq.Inst(TypeBinder.BindA[_Subset](), TypeBinder.BindB[_Subset]()))))
					halves := b.Conjuncts(
						sameTagged,
						"the empty or nonempty tags agree",
						"the list payloads agree")
					tags, payloads := halves[0], halves[1]
					nonemptyF := b.Unless(
						b.TermAs[Bool]("fun_support(zero, f) = ∅"),
						"with empty support, the common tag makes both polynomials zero",
						Given(func(c *Argument, emptyF Fact) {
							c.Show(
								"the empty tags identify the two zero functions",
								BySets(emptyF, tags))
						}))
					nonemptyG := b.Have(
						"the nonempty tag also makes g's support nonempty",
						"¬(fun_support(zero, g) = ∅)",
						BySets(nonemptyF, tags))
					listF, listG := b.TermAs[_SequenceOfSubsets]("L(f)"), b.TermAs[_SequenceOfSubsets]("L(g)")
					entries := b.Have(
						"the nonzero sequence payload determines every coded list entry",
						"∀k:num. L(f)(k) = L(g)(k)",
						Derive(func(d *Argument) {
							injective := d.Unfolded(sequenceCode, functions.InjectiveOnDef)
							d.Show(
								"both payloads are the same sequence code",
								By(
									Normalized,
									injective.At(listF, listG),
									nonemptyF,
									nonemptyG,
									payloads,
									set_basic.InUniv.At(listF),
									set_basic.InUniv.At(listG)))
						}))
					b.Do(entries.Simp(Fwd(listDef)))
					listedAlike := b.Have(
						"the two functions agree at every point listed by either support enumeration",
						"∀k:num. f(E(f)(k)) = g(E(f)(k)) ∧ f(E(g)(k)) = g(E(g)(k))",
						Derive(func(d *Argument) {
							k := d.FixAs[Nat]("k")
							validF := d.Have(
								"f's listed monomial and coefficient lie in the injection domains",
								"E(f)(k) ∈ M ∧ f(E(f)(k)) ∈ C",
								By(eligibleF, nonemptyF, entryValid.At(f, k)))
							validG := d.Have(
								"g's listed monomial and coefficient lie in the injection domains",
								"E(g)(k) ∈ M ∧ g(E(g)(k)) ∈ C",
								By(eligibleG, nonemptyG, entryValid.At(g, k)))
							entryF := d.TermAs[_PairOfSubsets]("(j₁(E(f)(k)), j₂(f(E(f)(k))))")
							entryG := d.TermAs[_PairOfSubsets]("(j₁(E(g)(k)), j₂(g(E(g)(k))))")
							oneEntry := d.Have(
								"a pair code recovers the monomial code and the coefficient code",
								"j₁(E(f)(k)) = j₁(E(g)(k)) ∧ j₂(f(E(f)(k))) = j₂(g(E(g)(k)))",
								Derive(func(e *Argument) {
									injective := e.Unfolded(pairCode, functions.InjectiveOnDef)
									e.Show(
										"the coded pair has equal halves",
										By(
											injective.At(entryF, entryG),
											entries.At(k),
											pairs.PairEq.At(e.TermAs[_Subset]("j₁(E(f)(k))"), e.TermAs[_Subset]("j₂(f(E(f)(k)))"),
												e.TermAs[_Subset]("j₁(E(g)(k))"), e.TermAs[_Subset]("j₂(g(E(g)(k)))")),
											set_basic.InUniv.At(entryF),
											set_basic.InUniv.At(entryG)))
								}))
							monomialInjective := d.Unfolded(monomialCode, functions.InjectiveOnDef)
							coefficientInjective := d.Unfolded(coefficientCode, functions.InjectiveOnDef)
							d.Show(
								"valid monomials and coefficients are recovered by their respective injections",
								By(
									validF,
									validG,
									oneEntry,
									monomialInjective.At(d.TermAs[monomial]("E(f)(k)"), d.TermAs[monomial]("E(g)(k)")),
									coefficientInjective.At(d.TermAs[B]("f(E(f)(k))"), d.TermAs[B]("g(E(g)(k))"))))
						}))
					agreement := b.TermAs[Set[monomial]]("λm:(set(prod(num, A)) → num). f(m) = g(m)")
					onListF := b.Have(
						"the polynomials agree on the range of E(f)",
						"∀m:(set(prod(num, A)) → num). m ∈ image(E(f), 𝕌⟨A:num⟩) ⇒ f(m) = g(m)",
						By(listedAlike, Where(set_image.ForallInImage, "P", agreement)))
					onListG := b.Have(
						"the polynomials agree on the range of E(g)",
						"∀m:(set(prod(num, A)) → num). m ∈ image(E(g), 𝕌⟨A:num⟩) ⇒ f(m) = g(m)",
						By(listedAlike, Where(set_image.ForallInImage, "P", agreement)))
					supportRanges := b.Have(
						"the two supports are exactly the two enumeration ranges",
						"fun_support(zero, f) = image(E(f), 𝕌⟨A:num⟩) ∧ fun_support(zero, g) = image(E(g), 𝕌⟨A:num⟩)",
						By(eligibleF, eligibleG, nonemptyF, nonemptyG, listed.At(f), listed.At(g)))
					b.Show(
						"the functions agree on both supports and are zero everywhere else",
						Funext(),
						Derive(func(d *Argument) {
							m := d.FixAs[monomial]("m")
							d.Show(
								"the coefficients agree at this monomial",
								BySets(supportRanges, onListF.At(m), onListG.At(m)))
						}))
				}))
			a.Show(
				"the tagged code injects the eligible polynomials into the subsets",
				Unfold(CardLeDef),
				Derive(func(b *Argument) {
					b.Take(code)
					b.Show(
						"every code is a subset, and the decoder recovers its eligible polynomial",
						Unfold(functions.InjectiveOnDef),
						BySets(decode))
				}))
		}),
	Reading: "The three conditions on f are load-bearing; let b be a member of C other than " +
		"zero. Without the finiteness of the maps carrying a coefficient, every function from the " +
		"finitely supported maps to {zero, b} would be in the set, more of them than subsets " +
		"(Cantor). Without the finite support of each such map, the set would hold, for every map m " +
		"from the subsets to ℕ, the function with value b at m and zero elsewhere, again more than " +
		"subsets; the encoding reads that condition too, since FiniteMultisetsIntoPowerSet injects " +
		"only the finitely supported maps, and every map carrying a coefficient other than zero is " +
		"one by it. Without the membership in C the coefficients would range over all of B, which " +
		"need not inject. zero is any value of B and need not lie in C: the coefficients off the " +
		"support are not encoded. At C = 𝕌⟨A:B⟩ the hypothesis is that B injects and the last " +
		"condition is void; at C a ring's carrier and zero its zero the set holds the ring's " +
		"polynomials in the variables of the powerset (free_algebra's PolynomialCarrierIntoPowerSet).",
})}

// EventuallyConstantDef — some value is taken outside a finite set.
// The value belongs to the function, not to an ambient module structure.
var EventuallyConstantDef = eventuallyConstantDefThm{family.Define(registry.DefEntry{
	Name: "EventuallyConstantDef", Const: "eventually_constant",
	Key:       "prop_10747fcb144a8d96",
	Type:      "(I → A) → bool",
	Equations: []string{"∀f:(I → A). eventually_constant(f) ⇔ ∃a:A. finite(fun_support(a, f))"},
})}

// The index of the three encodings that follow, as phantom spellings:
// _IndexPoint is a point of X = prod(num, prod(A, B)), and _IndexSubset a
// point of set(X), where each of them lands.
type (
	_IndexPoint  = Prod[Nat, Prod[A, B]]
	_IndexSubset = Set[_IndexPoint]
)

// LeftFactorIntoPowerSet — the points of A, the left factor of
// prod(A, B), inject into the subsets of prod(num, prod(A, B)): send x to
// the set {(0, (x, b)) | b : B} of its tagged pairs. A type is never
// empty, so x's set holds a pair (0, (x, b)); when y has the same set
// that pair is some (0, (y, c)), and equal pairs have equal components,
// so x = y.
var LeftFactorIntoPowerSet = leftFactorIntoPowerSetThm{family.Add(registry.ProofEntry{
	Name: "LeftFactorIntoPowerSet",
	Key:  "prop_cb81e96c0f41691d",
	Build: family.Theorem("card_le(𝕌⟨A:A⟩, 𝕌⟨A:set(prod(num, prod(A, B)))⟩)",
		Opening(Chain(Unfold(CardLeDef), Unfold(functions.InjectiveOnDef)), func(a *Argument) {
			a.Take(a.TermAs[Fun[A, _IndexSubset]]("λa:A. {(0, (a, b)) | b:B | ⊤}"))
			a.Show(
				"each set of tagged pairs is a subset, and one set for "+
					"x and y has (0, (x, b)) = (0, (y, c)) at any b, so x = y",
				BySets(
					pairs.PairEq.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Prod[A, B]]()),
					pairs.PairEq.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())))
		})),
})}

// RightFactorIntoPowerSet — the points of B, the right factor of
// prod(A, B), inject into the subsets of prod(num, prod(A, B)): send b to
// the set {(0, (a, b)) | a : A} of its tagged pairs, as
// LeftFactorIntoPowerSet does for A.
var RightFactorIntoPowerSet = rightFactorIntoPowerSetThm{family.Add(registry.ProofEntry{
	Name: "RightFactorIntoPowerSet",
	Key:  "prop_35d37d18cccc52ad",
	Build: family.Theorem("card_le(𝕌⟨A:B⟩, 𝕌⟨A:set(prod(num, prod(A, B)))⟩)",
		Opening(Chain(Unfold(CardLeDef), Unfold(functions.InjectiveOnDef)), func(a *Argument) {
			a.Take(a.TermAs[Fun[B, _IndexSubset]]("λb:B. {(0, (a, b)) | a:A | ⊤}"))
			a.Show(
				"each set of tagged pairs is a subset, and a tagged pair in a common set has one right coordinate",
				BySets(
					pairs.PairEq.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Prod[A, B]]()),
					pairs.PairEq.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())))
		})),
})}

// FiniteSupportIntoPowerSet — an eventually constant f from set(X) to A
// is coded by a pair of subsets: j₁ of a value α(f) that f takes off a
// finite set, and j₃ of a sequence listing the points where f leaves
// α(f), each written j₂ of itself with j₁ of the value f takes there
// (j₁, j₂, j₃ the injections of LeftFactorIntoPowerSet,
// PairsIntoPowerSet and SequencesIntoPowerSet; the list is a countable
// cover of a finite set, so an empty one needs no case of its own). Two
// functions with one code share the value and the listed points with
// their values, and both take the value at every point neither list
// reaches. The pairs of subsets inject into the subsets
// (PairsIntoPowerSet again).
var FiniteSupportIntoPowerSet = finiteSupportIntoPowerSetThm{family.Add(registry.ProofEntry{
	Name: "FiniteSupportIntoPowerSet",
	Key:  "prop_2ac7a05f8630c48d",
	Build: family.Theorem("card_le({f:(set(prod(num, prod(A, B))) → A) | eventually_constant(f)}, "+
		"    𝕌⟨A:set(prod(num, prod(A, B)))⟩)",
		func(a *Argument) {
			values := a.TermAs[Set[A]]("𝕌⟨A:A⟩")
			subsets := a.TermAs[Set[_IndexSubset]]("𝕌⟨A:set(prod(num, prod(A, B)))⟩")
			pairsOfSubsets := a.TermAs[Set[Prod[_IndexSubset, _IndexSubset]]](
				"𝕌⟨A:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, B))))⟩")
			sequences := a.TermAs[Set[Fun[Nat, _IndexSubset]]]("𝕌⟨A:num → set(prod(num, prod(A, B)))⟩")

			// The three encodings, each an injection into the subsets.
			_, valueCode := a.Unpack(a.Have(
				"the values inject into the subsets",
				"∃j₁:(A → set(prod(num, prod(A, B)))). injective_on(𝕌⟨A:A⟩, j₁)",
				By(Normalized, LeftFactorIntoPowerSet, CardLeDef.At(values, subsets))), "j₁")
			_, pairCode := a.Unpack(a.Have(
				"the pairs of subsets inject into the subsets",
				"∃j₂:(prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, B)))) → "+
					"        set(prod(num, prod(A, B)))). "+
					"    injective_on(𝕌⟨A:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, B))))⟩, j₂)",
				By(Normalized, PairsIntoPowerSet.Inst[Prod[A, B]](), CardLeDef.At(pairsOfSubsets, subsets))), "j₂")
			_, sequenceCode := a.Unpack(a.Have(
				"the sequences of subsets inject into the subsets",
				"∃j₃:((num → set(prod(num, prod(A, B)))) → set(prod(num, prod(A, B)))). "+
					"    injective_on(𝕌⟨A:num → set(prod(num, prod(A, B)))⟩, j₃)",
				By(Normalized, SequencesIntoPowerSet.Inst[Prod[A, B]](), CardLeDef.At(sequences, subsets))), "j₃")
			valueInjective := a.Unfolded(valueCode, functions.InjectiveOnDef)
			pairInjective := a.Unfolded(pairCode, functions.InjectiveOnDef)
			sequenceInjective := a.Unfolded(sequenceCode, functions.InjectiveOnDef)

			// The eventual value and the list of exceptions, chosen for
			// every eventually constant function at once.
			_, eventual := a.ObtainAs[Fun[Fun[_IndexSubset, A], A]](
				"choose for each eventually constant f a value α(f) it takes off a finite set",
				"∃α:((set(prod(num, prod(A, B))) → A) → A). ∀f:(set(prod(num, prod(A, B))) → A). "+
					"    eventually_constant(f) ⇒ finite(fun_support(α(f), f))",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Fun[_IndexSubset, A], A]](
						"λf:(set(prod(num, prod(A, B))) → A). εa:A. finite(fun_support(a, f))"))
					b.FixAs[Fun[_IndexSubset, A]]("f")
					taken := b.Unfolded(b.Assume(), EventuallyConstantDef)
					b.Show(
						"an eventually constant f has such a value, and ε picks one",
						By(Normalized, taken))
				}))
			_, listed := a.ObtainAs[Fun[Fun[_IndexSubset, A], Fun[Nat, _IndexSubset]]](
				"choose for each eventually constant f a sequence E(f) through every point where f leaves α(f)",
				"∃E:((set(prod(num, prod(A, B))) → A) → num → set(prod(num, prod(A, B)))). "+
					"∀f:(set(prod(num, prod(A, B))) → A). "+
					"    eventually_constant(f) ⇒ "+
					"    ∀x:set(prod(num, prod(A, B))). ¬(f(x) = α(f)) ⇒ x ∈ image(E(f), 𝕌⟨A:num⟩)",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Fun[_IndexSubset, A], Fun[Nat, _IndexSubset]]](
						"λf:(set(prod(num, prod(A, B))) → A). " +
							"εe:(num → set(prod(num, prod(A, B)))). " +
							"∀x:set(prod(num, prod(A, B))). " +
							"    ¬(f(x) = α(f)) ⇒ x ∈ image(e, 𝕌⟨A:num⟩)"))
					f := b.FixAs[Fun[_IndexSubset, A]]("f")
					constant := b.Assume()
					exceptions := b.TermAs[Set[_IndexSubset]]("fun_support(α(f), f)")
					listable := b.Have(
						"those points are finitely many, so countably many, so a sequence runs through them",
						"∃e:(num → set(prod(num, prod(A, B)))). ∀x:set(prod(num, prod(A, B))). "+
							"    ¬(f(x) = α(f)) ⇒ x ∈ image(e, 𝕌⟨A:num⟩)",
						Derive(func(c *Argument) {
							e, covered := c.ObtainAs[Fun[Nat, _IndexSubset]](
								"the finite set where f leaves α(f) is countable, so a sequence covers it",
								"∃e:(num → set(prod(num, prod(A, B)))). fun_support(α(f), f) ⊆ image(e, 𝕌⟨A:num⟩)",
								By(constant, eventual.At(f), FiniteCountable.At(exceptions), CountableCover.At(exceptions)))
							c.Take(e)
							c.Show(
								"each such point lies in the cover",
								BySets(covered))
						}))
					b.Show(
						"ε picks such a sequence",
						By(listable))
				}))

			decode := a.Have(
				"two eventually constant functions with one code are one function",
				Statement{
					Binders: "∀f g:(set(prod(num, prod(A, B))) → A).",
					Hypotheses: []string{
						"eventually_constant(f)",
						"eventually_constant(g)",
						"(j₁(α(f)), j₃(λk:num. j₂((E(f)(k), j₁(f(E(f)(k))))))) = " +
							"(j₁(α(g)), j₃(λk:num. j₂((E(g)(k), j₁(g(E(g)(k)))))))",
					},
					Conclusion: "f = g",
				},
				Derive(func(b *Argument) {
					f, g := b.FixAs[Fun[_IndexSubset, A]]("f"), b.FixAs[Fun[_IndexSubset, A]]("g")
					parts := b.Conjuncts(
						b.Assume(),
						"f is eventually constant",
						"g is eventually constant",
						"f and g have one code")
					constantF, constantG, oneCode := parts[0], parts[1], parts[2]
					valueF, valueG := b.TermAs[_IndexSubset]("j₁(α(f))"), b.TermAs[_IndexSubset]("j₁(α(g))")
					listF := b.TermAs[Fun[Nat, _IndexSubset]]("λk:num. j₂((E(f)(k), j₁(f(E(f)(k)))))")
					listG := b.TermAs[Fun[Nat, _IndexSubset]]("λk:num. j₂((E(g)(k), j₁(g(E(g)(k)))))")
					halves := b.Conjuncts(
						b.Have(
							"equal pairs have equal halves",
							"j₁(α(f)) = j₁(α(g)) ∧ "+
								"j₃(λk:num. j₂((E(f)(k), j₁(f(E(f)(k)))))) = j₃(λk:num. j₂((E(g)(k), j₁(g(E(g)(k))))))",
							By(
								oneCode,
								pairs.PairEq.At(valueF, b.TermAs[_IndexSubset]("j₃(λk:num. j₂((E(f)(k), j₁(f(E(f)(k))))))"),
									valueG, b.TermAs[_IndexSubset]("j₃(λk:num. j₂((E(g)(k), j₁(g(E(g)(k))))))")))),
						"the value halves agree",
						"the list halves agree")
					oneValue := b.Have(
						"j₁ tells values apart, so f and g share the eventual value",
						"α(f) = α(g)",
						By(valueInjective.At(b.TermAs[A]("α(f)"), b.TermAs[A]("α(g)")), halves[0], set_basic.InUniv))
					oneList := b.Have(
						"j₃ tells sequences apart, so the two lists agree",
						"(λk:num. j₂((E(f)(k), j₁(f(E(f)(k)))))) = (λk:num. j₂((E(g)(k), j₁(g(E(g)(k))))))",
						By(
							sequenceInjective.At(listF, listG),
							halves[1],
							set_basic.InUniv.At(listF),
							set_basic.InUniv.At(listG)))
					entries := b.Have(
						"so do their entries",
						"∀k:num. j₂((E(f)(k), j₁(f(E(f)(k))))) = j₂((E(g)(k), j₁(g(E(g)(k)))))",
						By(Normalized, oneList))
					listedAlike := b.Have(
						"f and g agree at every listed point",
						"∀k:num. f(E(f)(k)) = g(E(f)(k)) ∧ f(E(g)(k)) = g(E(g)(k))",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							entryF := c.TermAs[Prod[_IndexSubset, _IndexSubset]]("(E(f)(k), j₁(f(E(f)(k))))")
							entryG := c.TermAs[Prod[_IndexSubset, _IndexSubset]]("(E(g)(k), j₁(g(E(g)(k))))")
							oneEntry := c.Have(
								"j₂ tells pairs apart, so the k-th entries agree",
								"(E(f)(k), j₁(f(E(f)(k)))) = (E(g)(k), j₁(g(E(g)(k))))",
								By(
									pairInjective.At(entryF, entryG),
									entries.At(k),
									set_basic.InUniv.At(entryF),
									set_basic.InUniv.At(entryG)))
							pointF, pointG := c.TermAs[_IndexSubset]("E(f)(k)"), c.TermAs[_IndexSubset]("E(g)(k)")
							onePoint := c.Have(
								"so the k-th points agree, and so do the codes of the values there",
								"E(f)(k) = E(g)(k) ∧ j₁(f(E(f)(k))) = j₁(g(E(g)(k)))",
								By(
									oneEntry,
									pairs.PairEq.At(
										pointF,
										c.TermAs[_IndexSubset]("j₁(f(E(f)(k)))"),
										pointG,
										c.TermAs[_IndexSubset]("j₁(g(E(g)(k)))"))))
							oneLabel := c.Have(
								"j₁ tells values apart",
								"f(E(f)(k)) = g(E(g)(k))",
								By(
									valueInjective.At(c.TermAs[A]("f(E(f)(k))"), c.TermAs[A]("g(E(g)(k))")),
									onePoint,
									set_basic.InUniv))
							c.Show(
								"so f and g agree at the k-th point of either list",
								By(Normalized, onePoint, oneLabel))
						}))
					agreement := b.TermAs[Set[_IndexSubset]]("λy:set(prod(num, prod(A, B))). f(y) = g(y)")
					onListF := b.Have(
						"so f and g agree on the range of E(f)",
						"∀y:set(prod(num, prod(A, B))). y ∈ image(E(f), 𝕌⟨A:num⟩) ⇒ f(y) = g(y)",
						By(listedAlike, Where(set_image.ForallInImage, "P", agreement)))
					onListG := b.Have(
						"and on the range of E(g)",
						"∀y:set(prod(num, prod(A, B))). y ∈ image(E(g), 𝕌⟨A:num⟩) ⇒ f(y) = g(y)",
						By(listedAlike, Where(set_image.ForallInImage, "P", agreement)))
					pointwise := b.Have(
						"a point where f or g leaves the shared value is on its list; elsewhere both take it",
						"∀x:set(prod(num, prod(A, B))). f(x) = g(x)",
						b.ForEach(func(x *Expr[_IndexSubset]) Action {
							return By(
								constantF,
								constantG,
								listed.At(f, x),
								listed.At(g, x),
								onListF.At(x),
								onListG.At(x),
								oneValue)
						}))
					b.Show(
						"functions that agree everywhere are equal",
						By(Normalized, pointwise))
				}))

			encoded := a.Have(
				"coding each eventually constant function sends them injectively into the pairs of subsets",
				"card_le({f:(set(prod(num, prod(A, B))) → A) | eventually_constant(f)}, "+
					"    𝕌⟨A:prod(set(prod(num, prod(A, B))), set(prod(num, prod(A, B))))⟩)",
				Unfold(CardLeDef),
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Fun[_IndexSubset, A], Prod[_IndexSubset, _IndexSubset]]](
						"λf:(set(prod(num, prod(A, B))) → A). (j₁(α(f)), j₃(λk:num. j₂((E(f)(k), j₁(f(E(f)(k)))))))"))
					b.Show(
						"every code is a pair of subsets, and a code determines its function",
						Unfold(functions.InjectiveOnDef),
						BySets(decode))
				}))
			a.Show(
				"and the pairs of subsets inject into the subsets",
				By(
					encoded,
					PairsIntoPowerSet.Inst[Prod[A, B]](),
					CardLeTrans.At(
						a.TermAs[Set[Fun[_IndexSubset, A]]](
							"{f:(set(prod(num, prod(A, B))) → A) | eventually_constant(f)}"),
						pairsOfSubsets,
						subsets)))
		}),
})}
