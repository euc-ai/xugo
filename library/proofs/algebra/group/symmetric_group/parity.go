package symmetric_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// PermutationInversionsDef collects the pairs below n that p reverses.
var PermutationInversionsDef = permutationInversionsDefThm{family.Define(registry.DefEntry{
	Name:  "PermutationInversionsDef",
	Key:   "prop_9f4a00da6fa14ef2",
	Deps:  []registry.EntryLike{PermutationDef.Retraction},
	Const: "permutation_inversions",
	Type:  "num → permutation(num) → set(prod(num, num))",
	Equations: []string{
		"∀n:num. ∀p:permutation(num). " +
			"    permutation_inversions(n, p) = " +
			"    {z:prod(num, num) | " +
			"        fst(z) < snd(z) ∧ snd(z) < n ∧ permutation_map(p, snd(z)) < permutation_map(p, fst(z))}",
	},
})}

// PermutationEvenDef reads the parity of the inversion count.
var PermutationEvenDef = permutationEvenDefThm{family.Define(registry.DefEntry{
	Name:  "PermutationEvenDef",
	Key:   "prop_c9ee4aab079ffd6b",
	Deps:  []registry.EntryLike{PermutationInversionsDef},
	Const: "permutation_even",
	Type:  "num → permutation(num) → bool",
	Equations: []string{
		"∀n:num. ∀p:permutation(num). " +
			"    permutation_even(n, p) ⇔ nat_even(card(permutation_inversions(n, p)))",
	},
})}

// PermutationIdentityEven — the identity permutation is even, for every
// bound n: it reverses no pair, so it has no inversions, and 0 is even.
var PermutationIdentityEven = permutationIdentityEvenThm{family.Add(registry.ProofEntry{
	Name: "PermutationIdentityEven",
	Key:  "prop_c057404ac843ab4a",
	Build: family.Theorem("∀n:num. permutation_even(n, permutation_identity)", func(
		a *Argument,
		n *Expr[Nat],
	) {
		noInversions := a.Have(
			"the identity reverses no pair",
			"permutation_inversions(n, permutation_identity) = ∅",
			Unfold(PermutationInversionsDef),
			Simp(Fwd(MapIdentity), Fwd(set_basic.Extension), Fwd(set_basic.NotInEmpty)),
			a.ForEach(func(z *Expr[Prod[Nat, Nat]]) Action { return ByArith() }))
		a.Show(
			"so the identity has no inversions, an even number of them",
			Unfold(PermutationEvenDef),
			noInversions.Rw(),
			Simp(Fwd(cardinality.CardClauses), Fwd(nat_parity.NatEven)),
			Basic())
	}),
})}

// PermutationParityProduct — for q permuting the points below n and p any
// permutation, the product p·q is even exactly when p and q have the same
// parity. The law is proved with every permutation r of the points below n
// in place of the right-hand factor q, by strong induction on the number of
// inversions of r. Composing with the identity changes nothing, and the
// identity is even (PermutationIdentityEven). Any other r descends at some k,
// and r·s, s the swap of k and k + 1, has one inversion fewer; the swap flips
// the parity of r and of p·r alike, so the induction hypothesis at r·s gives
// the claim at r.
var PermutationParityProduct = permutationParityProductThm{family.Add(registry.ProofEntry{
	Name: "PermutationParityProduct",
	Key:  "prop_3e25e51ae6304bad",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀p q:permutation(num).",
		Hypotheses: []string{
			"q ∈ symmetric_group({i:num | i < n})",
		},
		Conclusion: "permutation_even(n, p * q) ⇔ (permutation_even(n, p) ⇔ permutation_even(n, q))",
	}, func(a *Argument, n *Expr[Nat], p, q *Expr[Permutation[Nat]], qIn Fact) {
		segment := a.TermAs[Set[Nat]]("{i:num | i < n}")
		permutationGroup := a.TermAs[group.GroupOps[Permutation[Nat]]]("permutation_group")
		symmetric := a.TermAs[Set[Permutation[Nat]]]("symmetric_group({i:num | i < n})")

		multiplicative := a.Have(
			"by strong induction on the number m of inversions of "+
				"r: p·r is even exactly when p and r have the same parity",
			Statement{
				Binders: "∀m:num. ∀r:permutation(num).",
				Hypotheses: []string{
					"r ∈ symmetric_group({i:num | i < n})",
					"card(permutation_inversions(n, r)) = m",
				},
				Conclusion: "permutation_even(n, p * r) ⇔ (permutation_even(n, p) ⇔ permutation_even(n, r))",
			},
			ByInduction(nat_order.StrongInduction,
				Case(
					"granted for every permutation with fewer than m inversions, it holds for one with m",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("m")
						fewer := b.Assume()
						r := b.FixAs[Permutation[Nat]]("r")
						given := b.Conjuncts(
							b.Assume(),
							"r permutes the points below n",
							"r has m inversions")
						rIn, count := given[0], given[1]

						notIdentity := b.Unless(
							b.Term("r = permutation_identity"),
							"where r is the identity, p·r is p, and the identity is even",
							Given(func(c *Argument, isIdentity Fact) {
								unit := c.Have(
									"p composed with the identity is p",
									"p * permutation_identity = p",
									By(group.RightIdentity.Read(SymmetricGroup).At(p)))
								c.Show(
									"p is even exactly when p is",
									isIdentity.Rw(),
									unit.Rw(),
									By(PermutationIdentityEven.At(n)))
							}))
						k, descent := b.ObtainAs[Nat](
							"a permutation other than the identity descends somewhere",
							"∃k:num. suc(k) < n ∧ permutation_map(r, suc(k)) < permutation_map(r, k)",
							By(PermutationAdjacentDescent.At(n, r), rIn, notIdentity))
						steps := b.Conjuncts(
							descent,
							"k + 1 lies below n",
							"r reverses k and k + 1")
						adjacent, reversed := steps[0], steps[1]
						s := b.TermAs[Permutation[Nat]]("transposition(k, suc(k))")
						rs := b.TermAs[Permutation[Nat]]("r * transposition(k, suc(k))")
						pr := b.TermAs[Permutation[Nat]]("p * r")

						sIn := b.Have(
							"the swap of k and k + 1 permutes the points below n",
							"transposition(k, suc(k)) ∈ symmetric_group({i:num | i < n})",
							ByArith(adjacent, TranspositionInSymmetricGroup.At(segment, k, b.TermAs[Nat]("suc(k)"))))
						rsIn := b.Have(
							"and so does r·s, the permutations of the points below n being closed under products",
							"r * transposition(k, suc(k)) ∈ symmetric_group({i:num | i < n})",
							By(
								rIn,
								sIn,
								group.SubgroupMul.At(permutationGroup, symmetric, r, s),
								SymmetricGroupSubgroup.At(segment)))
						oneFewer := b.Have(
							"r·s has one inversion fewer than r",
							"suc(card(permutation_inversions(n, r * transposition(k, suc(k))))) = "+
								"card(permutation_inversions(n, r))",
							By(InversionsAdjacentSwap.At(n, k, r), adjacent, reversed))
						atSwapped := b.Have(
							"so the induction hypothesis holds at r·s",
							"permutation_even(n, p * (r * transposition(k, suc(k)))) ⇔ "+
								"(permutation_even(n, p) ⇔ permutation_even(n, r * transposition(k, suc(k))))",
							ByArith(
								fewer.At(b.TermAs[Nat]("card(permutation_inversions(n, r * transposition(k, suc(k))))"), rs),
								oneFewer,
								count,
								rsIn))
						regroup := b.Have(
							"p·(r·s) is (p·r)·s",
							"p * (r * transposition(k, suc(k))) = p * r * transposition(k, suc(k))",
							By(group.Assoc.Read(SymmetricGroup).At(p, r, s)))
						flipPR := b.Have(
							"the swap flips the parity of p·r",
							"permutation_even(n, p * (r * transposition(k, suc(k)))) ⇔ ¬permutation_even(n, p * r)",
							regroup.Rw(),
							By(PermutationParityAdjacentSwap.At(n, k, pr), adjacent))
						flipR := b.Have(
							"and the parity of r",
							"permutation_even(n, r * transposition(k, suc(k))) ⇔ ¬permutation_even(n, r)",
							By(PermutationParityAdjacentSwap.At(n, k, r), adjacent))
						b.Show(
							"so p·r is even exactly when p·(r·s) is odd, that is when p and r·s "+
								"have opposite parities, that is when p and r have the same parity",
							By(flipPR, atSwapped, flipR))
					}))))

		a.Show(
			"read at q and its own number of inversions",
			By(multiplicative.At(a.TermAs[Nat]("card(permutation_inversions(n, q))"), q), qIn))
	}),
})}

// InversionsAdjacentSwap — composing a permutation p on the right with the
// swap s of two adjacent points k and k + 1 below n changes its number of
// inversions by exactly one: up when p keeps k before k + 1, down when it
// reverses them. The pair (k, k + 1) is an inversion of exactly one of p and
// p·s. Every other inversion (i, j) of p goes to the inversion (s(i), s(j))
// of p·s: s moves only k and k + 1, and each by one, so it keeps every other
// ordered pair in order and below n, and p·s reverses s(i) and s(j) exactly
// when p reverses i and j. That holds of every permutation in place of p,
// and read at p·s it carries the other inversions of p·s to those of
// (p·s)·s, which is p, s undoing itself; so the remaining inversions of the
// two are matched one to one.
var InversionsAdjacentSwap = inversionsAdjacentSwapThm{family.Add(registry.ProofEntry{
	Name: "InversionsAdjacentSwap",
	Key:  "prop_141de606ddaaca95",
	Build: family.Theorem(Statement{
		Binders: "∀n k:num. ∀p:permutation(num).",
		Hypotheses: []string{
			"suc(k) < n",
		},
		Conclusion: "(permutation_map(p, k) < permutation_map(p, suc(k)) ⇒ " +
			"    card(«inversions of p·s») = suc(card(permutation_inversions(n, p)))) ∧ " +
			"(permutation_map(p, suc(k)) < permutation_map(p, k) ⇒ " +
			"    suc(card(«inversions of p·s»)) = card(permutation_inversions(n, p)))",
		Abbrev: Abbrev{
			{Name: "inversions of p·s", Text: "permutation_inversions(n, p * transposition(k, suc(k)))"},
		},
	}, func(a *Argument, n, k *Expr[Nat], p *Expr[Permutation[Nat]], adjacent Fact) {
		sk := a.TermAs[Nat]("suc(k)")
		s := a.TermAs[Permutation[Nat]]("transposition(k, suc(k))")
		ps := a.TermAs[Permutation[Nat]]("p * transposition(k, suc(k))")
		e := a.TermAs[Prod[Nat, Nat]]("(k, suc(k))")
		inversions := a.TermAs[Set[Prod[Nat, Nat]]]("permutation_inversions(n, p)")
		swapped := a.TermAs[Set[Prod[Nat, Nat]]]("«inversions of p·s»")
		others := a.TermAs[Set[Prod[Nat, Nat]]]("delete(permutation_inversions(n, p), (k, suc(k)))")
		swappedOthers := a.TermAs[Set[Prod[Nat, Nat]]]("delete(«inversions of p·s», (k, suc(k)))")

		involution := a.Have(
			"s undoes itself",
			"∀x:num. "+
				"    permutation_map(transposition(k, suc(k)), permutation_map(transposition(k, suc(k)), x)) = x",
			a.ForEach(func(x *Expr[Nat]) Action {
				return By(MapCompose.At(s, s, x), TranspositionSelfInverse.At(k, sk), MapIdentity.At(x))
			}))
		inOrder := a.Have(
			"s keeps every ordered pair in order except (k, k + 1)",
			Statement{
				Binders: "∀i j:num.",
				Hypotheses: []string{
					"i < j",
					"¬(i = k ∧ j = suc(k))",
				},
				Conclusion: "permutation_map(transposition(k, suc(k)), i) < " +
					"permutation_map(transposition(k, suc(k)), j)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				b.FixAs[Nat]("j")
				b.Show(
					"s moves only k and k + 1, each by one",
					Simp(Fwd(MapTransposition)),
					CondRewrite(),
					ByArith())
			}))
		below := a.Have(
			"s keeps the points below n below n",
			"∀j:num. j < n ⇒ permutation_map(transposition(k, suc(k)), j) < n",
			a.ForEach(func(j *Expr[Nat]) Action {
				return Chain(Simp(Fwd(MapTransposition)), CondRewrite(), ByArith(adjacent))
			}))
		offTarget := a.Have(
			"s sends no ordered pair to (k, k + 1)",
			Statement{
				Binders: "∀i j:num.",
				Hypotheses: []string{
					"i < j",
				},
				Conclusion: "¬(permutation_map(transposition(k, suc(k)), i) = k ∧ " +
					"    permutation_map(transposition(k, suc(k)), j) = suc(k))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				b.FixAs[Nat]("j")
				b.Show(
					"only k + 1 goes to k, and only k to k + 1",
					Simp(Fwd(MapTransposition)),
					CondRewrite(),
					ByArith())
			}))

		membership := a.Have(
			"an inversion of r is a pair z with fst(z) < snd(z) < n that r reverses",
			"∀r:permutation(num). ∀z:prod(num, num). "+
				"    z ∈ permutation_inversions(n, r) ⇔ "+
				"    fst(z) < snd(z) ∧ snd(z) < n ∧ permutation_map(r, snd(z)) < permutation_map(r, fst(z))",
			Simp(Fwd(PermutationInversionsDef)),
			BySets())
		reading := a.Have(
			"a pair (i, j) is an inversion of r exactly when i < j < n and r reverses i and j",
			"∀r:permutation(num). ∀i j:num. "+
				"    (i, j) ∈ permutation_inversions(n, r) ⇔ "+
				"    i < j ∧ j < n ∧ permutation_map(r, j) < permutation_map(r, i)",
			Simp(Fwd(membership), Fwd(pairs.Fst), Fwd(pairs.Snd)),
			Basic())
		finite := a.Have(
			"an inversion set lies in the square of the points below n, so it is finite",
			"∀r:permutation(num). finite(permutation_inversions(n, r))",
			Derive(func(b *Argument) {
				r := b.FixAs[Permutation[Nat]]("r")
				inverted := b.TermAs[Set[Prod[Nat, Nat]]]("permutation_inversions(n, r)")
				segment := b.TermAs[Set[Nat]]("{i:num | i < n}")
				square := b.TermAs[Set[Prod[Nat, Nat]]]("set_cross({i:num | i < n}, {i:num | i < n})")
				within := b.Have(
					"both coordinates of an inversion lie below n",
					"permutation_inversions(n, r) ⊆ set_cross({i:num | i < n}, {i:num | i < n})",
					Derive(func(c *Argument) {
						c.Do(Unfold(set_basic.SubsetDef))
						z := c.FixAs[Prod[Nat, Nat]]("z")
						inverts := c.Assume()
						c.Show(
							"fst(z) < snd(z) < n",
							ByArith(inverts, membership.At(r, z), set_product.InCrossProjections.At(segment, segment, z)))
					}))
				b.Show(
					"a part of the finite square is finite",
					By(
						within,
						finite_set.FiniteSubset.At(inverted, square),
						finite_set.FiniteProduct.At(segment, segment),
						num_segment.FiniteBelowStrict.At(n)))
			}))

		carried := a.Have(
			"for every r, s carries each inversion of r other than (k, k + 1) to one of r·s",
			Statement{
				Binders: "∀r:permutation(num). ∀i j:num.",
				Hypotheses: []string{
					"(i, j) ∈ delete(permutation_inversions(n, r), (k, suc(k)))",
				},
				Conclusion: "(permutation_map(transposition(k, suc(k)), i), " +
					"    permutation_map(transposition(k, suc(k)), j)) ∈ " +
					"delete(permutation_inversions(n, r * transposition(k, suc(k))), (k, suc(k)))",
			},
			Derive(func(b *Argument) {
				r := b.FixAs[Permutation[Nat]]("r")
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				other := b.Assume()
				rs := b.TermAs[Permutation[Nat]]("r * transposition(k, suc(k))")
				si := b.TermAs[Nat]("permutation_map(transposition(k, suc(k)), i)")
				sj := b.TermAs[Nat]("permutation_map(transposition(k, suc(k)), j)")
				ofR := b.TermAs[Set[Prod[Nat, Nat]]]("permutation_inversions(n, r)")
				ofRS := b.TermAs[Set[Prod[Nat, Nat]]]("permutation_inversions(n, r * transposition(k, suc(k)))")
				read := b.Have(
					"i < j < n, r reverses i and j, and (i, j) is not (k, k + 1)",
					"i < j ∧ j < n ∧ permutation_map(r, j) < permutation_map(r, i) ∧ ¬(i = k ∧ j = suc(k))",
					By(
						other,
						reading.At(r, i, j),
						set_basic.InDelete.At(ofR, b.TermAs[Prod[Nat, Nat]]("(i, j)"), e),
						pairs.PairEq.At(i, j, k, sk)))
				b.Show(
					"s(i) < s(j) < n, r·s reverses them as r reversed i and j, and (s(i), s(j)) is not (k, k + 1)",
					By(
						read,
						reading.At(rs, si, sj),
						inOrder.At(i, j),
						below.At(j),
						offTarget.At(i, j),
						involution.At(i),
						involution.At(j),
						set_basic.InDelete.At(
							ofRS,
							b.TermAs[Prod[Nat, Nat]](
								"(permutation_map(transposition(k, suc(k)), i), permutation_map(transposition(k, suc(k)), j))"),
							e),
						pairs.PairEq.At(si, sj, k, sk),
						MapCompose.At(r, s, si),
						MapCompose.At(r, s, sj)))
			}))

		swap, swapDef := a.LetAs[Fun[Prod[Nat, Nat], Prod[Nat, Nat]]](
			"σ",
			"λz:prod(num, num). "+
				"    (permutation_map(transposition(k, suc(k)), fst(z)), "+
				"        permutation_map(transposition(k, suc(k)), snd(z)))")
		carriedPairs := a.Have(
			"so σ, s on both coordinates, carries the other "+
				"inversions of r into those of r·s, and undoes itself",
			Statement{
				Binders: "∀r:permutation(num). ∀w:prod(num, num).",
				Hypotheses: []string{
					"w ∈ delete(permutation_inversions(n, r), (k, suc(k)))",
				},
				Conclusion: "σ(w) ∈ " +
					"delete(permutation_inversions(n, r * transposition(k, suc(k))), (k, suc(k))) ∧ " +
					"σ(σ(w)) = w",
			},
			Derive(func(b *Argument) {
				r := b.FixAs[Permutation[Nat]]("r")
				w := b.FixAs[Prod[Nat, Nat]]("w")
				i, j, isPair := b.Obtain2As[Nat, Nat](
					"write w as a pair (i, j)",
					"∃i j:num. w = (i, j)",
					By(pairs.PairSurjective.At(w)))
				b.Show(
					"σ(i, j) is (s(i), s(j))",
					isPair.Rw(),
					swapDef.Rw(),
					Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
					By(carried.At(r, i, j), involution.At(i), involution.At(j)))
			}))
		undo := a.Have(
			"s undoes itself after p too: (p·s)·s is p",
			"p * transposition(k, suc(k)) * transposition(k, suc(k)) = p",
			By(
				group.Assoc.Read(SymmetricGroup).At(p, s, s),
				TranspositionSelfInverse.At(k, sk),
				group.RightIdentity.Read(SymmetricGroup).At(p)))
		// read at p·s, where (p·s)·s is p: σ carries the other inversions of p·s back into those of p
		backPairs := a.Simplified(carriedPairs.At(ps), Fwd(undo))
		sameRest := a.Have(
			"so p and p·s have as many inversions besides (k, k + 1)",
			"card(delete(«inversions of p·s», (k, suc(k)))) = "+
				"card(delete(permutation_inversions(n, p), (k, suc(k))))",
			By(
				carriedPairs.At(p),
				backPairs,
				finite.At(p),
				finite_set.FiniteDeleteImp.At(inversions, e),
				cardinality.MutualInversesCard.At(others, swappedOthers, swap, swap)))

		values := a.Have(
			"p·s reads p at k and at k + 1 the other way round",
			"permutation_map(p * transposition(k, suc(k)), k) = permutation_map(p, suc(k)) ∧ "+
				"permutation_map(p * transposition(k, suc(k)), suc(k)) = permutation_map(p, k)",
			Simp(Fwd(MapCompose), Fwd(MapTransposition)),
			ByArith())

		up := a.Have(
			"when p keeps k before k + 1, (k, k + 1) is an inversion of p·s and not of p",
			Statement{
				Hypotheses: []string{
					"permutation_map(p, k) < permutation_map(p, suc(k))",
				},
				Conclusion: "card(«inversions of p·s») = suc(card(permutation_inversions(n, p)))",
			},
			Derive(func(b *Argument) {
				ascending := b.Assume()
				gained := b.Have(
					"(k, k + 1) is an inversion of p·s",
					"(k, suc(k)) ∈ «inversions of p·s»",
					ByArith(reading.At(ps, k, sk), values, adjacent, ascending))
				missing := b.Have(
					"but not of p",
					"(k, suc(k)) ∉ permutation_inversions(n, p)",
					ByArith(reading.At(p, k, sk), ascending))
				b.Show(
					"so p·s has the shared inversions and (k, k + 1)",
					ByArith(
						sameRest,
						cardinality.CountsOneMore.At(swapped, e),
						gained,
						finite.At(ps),
						cardinality.CardDelete.At(inversions, e),
						finite.At(p),
						missing))
			}))
		down := a.Have(
			"when p reverses k and k + 1, (k, k + 1) is an inversion of p and not of p·s",
			Statement{
				Hypotheses: []string{
					"permutation_map(p, suc(k)) < permutation_map(p, k)",
				},
				Conclusion: "suc(card(«inversions of p·s»)) = card(permutation_inversions(n, p))",
			},
			Derive(func(b *Argument) {
				descending := b.Assume()
				lost := b.Have(
					"(k, k + 1) is an inversion of p",
					"(k, suc(k)) ∈ permutation_inversions(n, p)",
					ByArith(reading.At(p, k, sk), adjacent, descending))
				missing := b.Have(
					"but not of p·s",
					"(k, suc(k)) ∉ «inversions of p·s»",
					ByArith(reading.At(ps, k, sk), values, descending))
				b.Show(
					"so p has the shared inversions and (k, k + 1)",
					ByArith(
						sameRest,
						cardinality.CountsOneMore.At(inversions, e),
						lost,
						finite.At(p),
						cardinality.CardDelete.At(swapped, e),
						finite.At(ps),
						missing))
			}))
		a.Show(
			"so the count goes up by one when p keeps k before k + 1, and down by one when p reverses them",
			By(up, down))
	}),
})}

// PermutationParityAdjacentSwap — swapping two adjacent points k and k + 1
// below n on the right of a permutation flips its parity. The swap changes
// the number of inversions by one (InversionsAdjacentSwap), so it changes
// that number's parity. p, being one-to-one, keeps k and k + 1 apart, so the
// swap either adds the inversion (k, k + 1) or removes it.
var PermutationParityAdjacentSwap = permutationParityAdjacentSwapThm{family.Add(registry.ProofEntry{
	Name: "PermutationParityAdjacentSwap",
	Key:  "prop_c7a8b2767a661a4d",
	Build: family.Theorem(Statement{
		Binders: "∀n k:num. ∀p:permutation(num).",
		Hypotheses: []string{
			"suc(k) < n",
		},
		Conclusion: "permutation_even(n, p * transposition(k, suc(k))) ⇔ ¬permutation_even(n, p)",
	}, func(a *Argument, n, k *Expr[Nat], p *Expr[Permutation[Nat]], adjacent Fact) {
		sk := a.TermAs[Nat]("suc(k)")
		injective := a.Have(
			"p is one-to-one",
			"injective_on(𝕌, permutation_map(p))",
			By(MapBijective.At(p)))
		separates := a.Unfolded(injective, functions.InjectiveOnDef)
		apart := a.Have(
			"so p keeps k and k + 1 apart",
			"permutation_map(p, k) ≠ permutation_map(p, suc(k))",
			ByArith(separates.At(k, sk), set_basic.InUniv.At(k), set_basic.InUniv.At(sk)))
		a.Do(Unfold(PermutationEvenDef))
		a.Cases(a.Term("permutation_map(p, k) < permutation_map(p, suc(k))"))
		a.When(
			"p keeps k before k + 1: one inversion more",
			func(b *Argument, ascending Fact) {
				more := b.Have(
					"p·s has one inversion more than p",
					"card(permutation_inversions(n, p * transposition(k, suc(k)))) = "+
						"suc(card(permutation_inversions(n, p)))",
					By(InversionsAdjacentSwap.At(n, k, p), adjacent, ascending))
				b.Show(
					"a successor has the other parity",
					more.Rw(),
					Cite(nat_parity.NatEven))
			})
		a.Otherwise(
			"p reverses k and k + 1: one inversion fewer",
			func(b *Argument, notAscending Fact) {
				descending := b.Have(
					"p reverses k and k + 1",
					"permutation_map(p, suc(k)) < permutation_map(p, k)",
					ByArith(notAscending, apart))
				fewer := b.Have(
					"p·s has one inversion fewer than p",
					"suc(card(permutation_inversions(n, p * transposition(k, suc(k))))) = "+
						"card(permutation_inversions(n, p))",
					By(InversionsAdjacentSwap.At(n, k, p), adjacent, descending))
				b.Show(
					"a successor has the other parity",
					fewer.RwRev(),
					Cite(nat_parity.NatEven))
			})
	}),
})}

// PermutationParityInverse — a permutation of the points below n has the
// parity of its inverse: p⁻¹p is the identity, which is even
// (PermutationIdentityEven), so p⁻¹ and p have the same parity
// (PermutationParityProduct).
var PermutationParityInverse = permutationParityInverseThm{family.Add(registry.ProofEntry{
	Name: "PermutationParityInverse",
	Key:  "prop_c2254246e2c9b737",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀p:permutation(num).",
		Hypotheses: []string{
			"p ∈ symmetric_group({i:num | i < n})",
		},
		Conclusion: "permutation_even(n, permutation_inverse(p)) ⇔ permutation_even(n, p)",
	}, func(a *Argument, n *Expr[Nat], p *Expr[Permutation[Nat]], pIn Fact) {
		inverse := a.TermAs[Permutation[Nat]]("permutation_inverse(p)")
		a.Show(
			"p⁻¹p is the identity, which is even, so p⁻¹ has the parity of p",
			By(
				pIn,
				group.LeftInverse.Read(SymmetricGroup).At(p),
				PermutationParityProduct.At(n, inverse, p),
				PermutationIdentityEven.At(n)))
	}),
})}

// TranspositionOdd — a transposition of two distinct points below n is odd.
// An adjacent transposition (k k+1) is the identity followed by the swap of
// k and k+1, which flips the identity's parity
// (PermutationParityAdjacentSwap); conjugating (k l) by the adjacent
// (l l+1) gives (k l+1), a product of three odd permutations, so induction
// on l makes every (k l) with k < l odd, and (i j) = (j i) gives the other
// order.
var TranspositionOdd = transpositionOddThm{family.Add(registry.ProofEntry{
	Name: "TranspositionOdd",
	Key:  "prop_d539723d26aee836",
	Build: family.Theorem(Statement{
		Binders: "∀n i j:num.",
		Hypotheses: []string{
			"i < n",
			"j < n",
			"i ≠ j",
		},
		Conclusion: "¬permutation_even(n, transposition(i, j))",
	}, func(a *Argument, n, i, j *Expr[Nat], given Fact) {
		points := a.TermAs[Set[Nat]]("{m:num | m < n}")

		adjacent := a.Have(
			"an adjacent transposition (k k+1) is odd",
			"∀k:num. suc(k) < n ⇒ ¬permutation_even(n, transposition(k, suc(k)))",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				below := b.Assume()
				swap := b.TermAs[Permutation[Nat]]("transposition(k, suc(k))")
				identity := b.TermAs[Permutation[Nat]]("permutation_identity")
				unit := b.Have(
					"(k k+1) is the identity followed by (k k+1)",
					"permutation_identity * transposition(k, suc(k)) = transposition(k, suc(k))",
					By(group.LeftIdentity.Read(SymmetricGroup).At(swap)))
				b.Show(
					"so its parity is the identity's, flipped, and the identity is even",
					By(
						Normalized,
						below,
						unit,
						PermutationParityAdjacentSwap.At(n, k, identity),
						PermutationIdentityEven.At(n)))
			}))

		ordered := a.Have(
			"every (k l) with k < l < n is odd",
			"∀k l:num. k < l ∧ l < n ⇒ ¬permutation_even(n, transposition(k, l))",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				b.Induct("l")
				b.Base(
					"no k lies below 0",
					ByArith())
				b.Step(
					"(k l+1) is (k l) conjugated by the adjacent (l l+1)",
					func(c *Argument, ih Fact) {
						l := c.TermAs[Nat]("l")
						next := c.TermAs[Nat]("suc(l)")
						bounds := c.Assume()
						other := c.Unless(
							c.Term("k = l"),
							"where k = l, (k l+1) is the adjacent (l l+1)",
							Given(func(d *Argument, same Fact) {
								d.Show(
									"an adjacent transposition is odd",
									same.Rw(),
									By(bounds, adjacent.At(l)))
							}))
						order := c.Have(
							"otherwise k lies below l and below n, and differs from l + 1",
							"k < l ∧ l < n ∧ k < n ∧ k ≠ suc(l)",
							ByArith(other, bounds))
						swap := c.TermAs[Permutation[Nat]]("transposition(l, suc(l))")
						earlier := c.TermAs[Permutation[Nat]]("transposition(k, l)")
						swapEarlier := c.TermAs[Permutation[Nat]]("transposition(l, suc(l)) * transposition(k, l)")
						swapIn := c.Have(
							"(l l+1) permutes the points below n",
							"transposition(l, suc(l)) ∈ symmetric_group({m:num | m < n})",
							By(order, bounds, TranspositionInSymmetricGroup.At(points, l, next)))
						earlierIn := c.Have(
							"so does (k l)",
							"transposition(k, l) ∈ symmetric_group({m:num | m < n})",
							By(order, TranspositionInSymmetricGroup.At(points, k, l)))
						pairEven := c.Have(
							"(l l+1)(k l) is a product of two odd permutations, so it is even",
							"permutation_even(n, transposition(l, suc(l)) * transposition(k, l))",
							By(order, bounds, ih, earlierIn, adjacent.At(l), PermutationParityProduct.At(n, swap, earlier)))
						c.Show(
							"(k l+1) is (l l+1)(k l)(l l+1), that even product followed by the odd (l l+1), so it is odd",
							By(
								other,
								order,
								bounds,
								swapIn,
								pairEven,
								TranspositionConjugate.At(k, l, next),
								PermutationParityProduct.At(n, swapEarlier, swap),
								adjacent.At(l)))
					})
			}))

		notBelow := a.Unless(
			a.Term("i < j"),
			"where i < j, (i j) is one of those",
			Given(func(c *Argument, below Fact) {
				c.Show(
					"(i j) is odd",
					By(below, given, ordered.At(i, j)))
			}))
		above := a.Have(
			"otherwise j lies below i",
			"j < i",
			ByArith(notBelow, given))
		swapped := a.Have(
			"and (i j) is (j i)",
			"transposition(i, j) = transposition(j, i)",
			By(TranspositionSymmetric))
		a.Show(
			"(j i) is odd",
			swapped.Rw(),
			By(above, given, ordered.At(j, i)))
	}),
})}

// ParityAfterTransposition — composing a permutation of the points below n
// with the transposition of two of them flips its parity: the product is
// even exactly when its factors have the same parity
// (PermutationParityProduct), and a transposition is odd
// (TranspositionOdd).
var ParityAfterTransposition = parityAfterTranspositionThm{family.Add(registry.ProofEntry{
	Name: "ParityAfterTransposition",
	Key:  "prop_bf88d7e60997048b",
	Build: family.Theorem(Statement{
		Binders: "∀n i j:num. ∀q:permutation(num).",
		Hypotheses: []string{
			"i < n",
			"j < n",
			"i ≠ j",
			"q ∈ symmetric_group({k:num | k < n})",
		},
		Conclusion: "permutation_even(n, transposition(i, j) * q) ⇔ ¬permutation_even(n, q)",
	},
		func(a *Argument, n, i, j *Expr[Nat], q *Expr[Permutation[Nat]], given Fact) {
			tau := a.TermAs[Permutation[Nat]]("transposition(i, j)")
			a.Show(
				"τ·q is even exactly when τ and q have the same parity, and τ is odd",
				By(given, PermutationParityProduct.At(n, tau, q), TranspositionOdd.At(n, i, j)))
		}),
})}
