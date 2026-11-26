// counting.go — counting with sums over ℕ: summing 1 counts a finite set,
// a term is at most its sum, a set is counted through its fibres, a
// disjoint family through its sets, a constant summed over a finite set,
// the points where a predicate holds,
// a relation counted by its rows or by its columns, and the parity of
// finite sums and of incidences counted both ways.

package nat_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// SumOfOnes — summing 1 over a finite set counts it: both sides grow by one at
// each new element.
var SumOfOnes = sumOfOnesThm{family.Add(registry.ProofEntry{
	Name: "SumOfOnes",
	Key:  "prop_f3085b245c6c8449",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "Σ_{x∈s} 1 = card(s)",
	},
		func(a *Argument, s *Expr[Set[A]], finiteS Fact) {
			a.Show(
				"finite induction carries the equation to every finite set",
				ByInduction(finite_set.FiniteInductFresh, finiteS,
					Case(
						"the empty set sums to 0 and has no element",
						By(Clauses, cardinality.CardClauses)),
					Case(
						"a new element adds one to each side",
						Derive(func(b *Argument) {
							b.Fix()
							b.Fix("t")
							carried := b.Assume()
							b.Show(
								"the sum and the count each take the new element",
								ByArith(carried, Clauses, cardinality.CardClauses))
						}))))
		}),
})}

// TermLeSum — a term of a finite sum of naturals is at most the sum.
// Split off that term; adding the remaining sum cannot decrease it.
var TermLeSum = termLeSumThm{family.Add(registry.ProofEntry{
	Name: "TermLeSum",
	Key:  "prop_2352ea4bde021a88",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → num). ∀s:set(A). ∀x:A.",
		Hypotheses: []string{
			"finite(s)",
			"x ∈ s",
		},
		Conclusion: "f(x) ≤ Σ_{y∈s} f(y)",
	},
		func(a *Argument, f *Arrow[A, Nat], s *Expr[Set[A]], x *Expr[A], finiteS, inS Fact) {
			a.Show(
				"the sum is f(x) plus the sum over the remaining points",
				Unfold(NatSumDef),
				By(
					finiteS,
					inS,
					monoidal.Delete.Read(MonoidalNatAdd).At(s, f, x),
					nat_order.LessEqAdd.At(f.Apply(x), a.TermAs[Nat]("iterated_op(+, delete(s, x), f)"))))
		}),
})}

// SumLeEqTermwise — two sums over a finite set, the first at most the
// second term by term, that are equal agree at every term: the second sum
// is the first plus the sum of the gaps g(y) − f(y), so the gaps sum to 0
// and each of them is 0.
var SumLeEqTermwise = sumLeEqTermwiseThm{family.Add(registry.ProofEntry{
	Name: "SumLeEqTermwise",
	Key:  "prop_aaf73d29dce932d",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f g:(A → num). ∀x:A.",
		Hypotheses: []string{
			"finite(s)",
			"∀y:A. y ∈ s ⇒ f(y) ≤ g(y)",
			"Σ_{y∈s} f(y) = Σ_{y∈s} g(y)",
			"x ∈ s",
		},
		Conclusion: "f(x) = g(x)",
	},
		func(
			a *Argument,
			s *Expr[Set[A]],
			f, g *Arrow[A, Nat],
			x *Expr[A],
			finite, below, equal, member Fact,
		) {
			gaps := a.TermAs[Fun[A, Nat]]("λy:A. g(y) - f(y)")
			pointwise := a.Have(
				"each term of g is the term of f plus its gap",
				"∀y:A. y ∈ s ⇒ g(y) = f(y) + (g(y) - f(y))",
				a.ForEach(func(y *Expr[A]) Action {
					return ByArith(below.At(y))
				}))
			split := a.Have(
				"so the sum of g is the sum of f plus the sum of the gaps",
				"Σ_{y∈s} g(y) = Σ_{y∈s} f(y) + Σ_{y∈s} (g(y) - f(y))",
				By(
					pointwise,
					finite,
					Congruence.At(s, g, a.TermAs[Fun[A, Nat]]("λy:A. f(y) + (g(y) - f(y))")),
					Add.At(f, gaps, s)))
			a.Show(
				"the two sums being equal, the gaps sum to 0, the gap at "+
					"x among them, and f(x) ≤ g(x) makes the two terms equal",
				ByArith(finite, below.At(x), equal, split, member, EqZero.At(s, gaps)))
		}),
})}

// CardByFibres — a finite set is counted through a relation to T: each
// source point has a unique related point in T, whose fibre has size w(y).
// The relation chooses a map into T. Regroup its sum of ones over T, then
// replace each fibre sum by its prescribed size.
var CardByFibres = cardByFibresThm{family.Add(registry.ProofEntry{
	Name: "CardByFibres",
	Key:  "prop_73f577b7874e585a",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀T:set(B). ∀R:(A → B → bool). ∀w:(B → num).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ ∃!y:B. y ∈ T ∧ R(x, y)",
			"∀y:B. y ∈ T ⇒ has_size({x:A | x ∈ s ∧ R(x, y)}, w(y))",
		},
		Conclusion: "card(s) = Σ_{y∈T} w(y)",
	},
		func(
			a *Argument,
			s *Expr[Set[A]],
			T *Expr[Set[B]],
			R *Arrow2[A, B, Bool],
			w *Arrow[B, Nat],
			finiteS, unique, sizes Fact,
		) {
			f, onT := a.ObtainAs[Fun[A, B]](
				"each point of s is sent to the point of T it is related to",
				"∃f:(A → B). ∀x:A. x ∈ s ⇒ f(x) ∈ T ∧ R(x, f(x))",
				By(unique))
			fibres := a.Have(
				"over a point of T the fibre of f is the set of points related to it",
				"∀y:B. y ∈ T ⇒ {x:A | x ∈ s ∧ f(x) = y} = {x:A | x ∈ s ∧ R(x, y)}",
				BySets(unique, onT))
			fibreSums := a.Have(
				"so the sum of ones over a fibre is w",
				"∀y:B. y ∈ T ⇒ Σ_{x∈{x:A | x ∈ s ∧ f(x) = y}} 1 = w(y)",
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					inT := b.Assume()
					fibre := b.TermAs[Set[A]]("{x:A | x ∈ s ∧ f(x) = y}")
					b.Show(
						"a sized set is finite, and its sum of ones is its size",
						By(fibres.At(y), sizes.At(y), inT, SumOfOnes.At(fibre), cardinality.HasSizeDef))
				}))
			covered := a.Have(
				"the image of f lies in T",
				"image(f, s) ⊆ T",
				BySets(onT))
			ones := a.TermAs[Fun[A, Nat]]("λx:A. 1")
			a.Show(
				"the count of s is its sum of ones, read over the fibres",
				CalcEq(
					Leg(
						a.TermAs[Nat]("Σ_{x∈s} 1"),
						"a finite set's size is its sum of ones",
						By(finiteS, SumOfOnes.At(s))),
					Leg(
						a.TermAs[Nat]("Σ_{y∈T} Σ_{x∈{x:A | x ∈ s ∧ f(x) = y}} 1"),
						"the sum regroups over T, which covers the image of f",
						Unfold(NatSumDef),
						By(finiteS, covered, monoidal.Regroup.Read(MonoidalNatAdd).At(f, ones, s, T))),
					FinalLeg(
						"each fibre sum is its prescribed size",
						By(fibreSums, Congruence.Inst[B]()))))
		}),
})}

// CardOfDisjointFamily — the union of a finite family of pairwise disjoint
// finite sets has as many points as the sets have between them: each point of
// the union lies in exactly one set of the family, so the union is counted by
// the sets it falls into, the points falling into S(i) being S(i).
var CardOfDisjointFamily = cardOfDisjointFamilyThm{family.Add(registry.ProofEntry{
	Name: "CardOfDisjointFamily",
	Key:  "prop_ced4e07852a826dd",
	Build: family.Theorem(Statement{
		Binders: "∀S:(A → set(B)). ∀I:set(A).",
		Hypotheses: []string{
			"finite(I)",
			"∀i:A. i ∈ I ⇒ finite(S(i))",
			"∀i j:A. i ∈ I ∧ j ∈ I ∧ i ≠ j ⇒ disjoint(S(i), S(j))",
		},
		Conclusion: "card(⋃image(S, I)) = Σ_{i∈I} card(S(i))",
	}, func(a *Argument, S *Arrow[A, Set[B]], I *Expr[Set[A]], finiteIndex, finiteSets, apart Fact) {
		union := a.TermAs[Set[B]]("⋃image(S, I)")
		finiteUnion := a.Have(
			"the union is finite, being a finite union of finite sets",
			"finite(⋃image(S, I))",
			By(
				finiteSets,
				finiteIndex,
				finite_set.FiniteImage.At(S, I),
				finite_set.FiniteFiniteUnions.At(a.TermAs[Set[Set[B]]]("image(S, I)")),
				set_image.ForallInImage.At(S, I, a.TermAs[Fun[Set[B], Bool]]("λt:set(B). finite(t)"))))
		oneSet := a.Have(
			"a point of the union lies in a set of the family, and in no other, the sets being disjoint",
			"∀x:B. x ∈ ⋃image(S, I) ⇒ ∃!i:A. i ∈ I ∧ x ∈ S(i)",
			BySets(apart))
		sized := a.Have(
			"the points of the union in S(i) are S(i), which has card(S(i)) points",
			"∀i:A. i ∈ I ⇒ has_size({x:B | x ∈ ⋃image(S, I) ∧ x ∈ S(i)}, card(S(i)))",
			Derive(func(b *Argument) {
				i := b.FixAs[A]("i")
				iIn := b.Assume()
				fibre := b.Have(
					"S(i) lies in the union",
					"{x:B | x ∈ ⋃image(S, I) ∧ x ∈ S(i)} = S(i)",
					BySets(iIn))
				b.Show(
					"and is finite",
					fibre.Rw(),
					By(iIn, finiteSets.At(i), cardinality.HasSizeDef))
			}))
		a.Show(
			"so the union is counted by the sets its points fall into",
			By(
				finiteUnion,
				oneSet,
				sized,
				CardByFibres.At(
					union,
					I,
					a.TermAs[Fun2[B, A, Bool]]("λx:B. λi:A. x ∈ S(i)"),
					a.TermAs[Fun[A, Nat]]("λi:A. card(S(i))"))))
	}),
})}

// SumConst — a constant summed over a finite set is the size of the set
// times the constant: c times the sum of ones over s.
var SumConst = sumConstThm{family.Add(registry.ProofEntry{
	Name: "SumConst",
	Key:  "prop_5a66d0f22de9996b",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀c:num.",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "Σ_{x∈s} c = card(s) * c",
	},
		func(a *Argument, s *Expr[Set[A]], c *Expr[Nat], finite Fact) {
			ones := a.TermAs[Fun[A, Nat]]("λx:A. 1")
			size := a.TermAs[Nat]("card(s)")
			a.Show(
				"the sum of ones over s counts s, and c comes out of the sum of the c * 1",
				By(
					finite,
					SumOfOnes.At(s),
					ScalarLeft.At(c, ones, s),
					nat_arith.MulSym.At(c, size),
					nat_arith.MulOne))
		}),
})}

// CountByIndicator — the points of a finite set satisfying P are counted
// by summing over the set the indicator of P: the sum of ones over the
// part of s where P holds is the sum over s of 1 where P holds and 0
// elsewhere.
var CountByIndicator = countByIndicatorThm{family.Add(registry.ProofEntry{
	Name: "CountByIndicator",
	Key:  "prop_890182bf94b6e2e9",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀P:(A → bool).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "card({x:A | x ∈ s ∧ P(x)}) = Σ_{x∈s} COND(P(x), 1, 0)",
	},
		func(a *Argument, s *Expr[Set[A]], P *Expr[Set[A]], finite Fact) {
			ones := a.TermAs[Fun[A, Nat]]("λx:A. 1")
			part := a.TermAs[Set[A]]("{x:A | x ∈ s ∧ P(x)}")
			a.Show(
				"the part of s where P holds is finite and counted by "+
					"its sum of ones, which is the sum of the indicator over s",
				By(finite, Restrict.At(s, P, ones), SumOfOnes.At(part), finite_set.FiniteRestrict.At(s, P)))
		}),
})}

// DoubleCounting — a relation between two finite sets is counted by its
// rows or by its columns: summing over s the number of points of t
// related to each, or over t the number of points of s related to each,
// gives the same number. Both are the double sum of the relation's
// indicator, taken in the two orders.
var DoubleCounting = doubleCountingThm{family.Add(registry.ProofEntry{
	Name: "DoubleCounting",
	Key:  "prop_2552003ba55e9324",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B). ∀R:(A → B → bool).",
		Hypotheses: []string{
			"finite(s)",
			"finite(t)",
		},
		Conclusion: "Σ_{i∈s} card({j:B | j ∈ t ∧ R(i, j)}) = Σ_{j∈t} card({i:A | i ∈ s ∧ R(i, j)})",
	},
		func(a *Argument, s *Expr[Set[A]], t *Expr[Set[B]], R *Arrow2[A, B, Bool], finiteS, finiteT Fact) {
			a.Show(
				"both are the double sum of the indicator of R",
				CalcEq(
					Leg(
						a.Term("Σ_{i∈s} Σ_{j∈t} COND(R(i, j), 1, 0)"),
						"each row is counted by its indicator",
						By(Congruence, CountByIndicator, finiteT)),
					Leg(
						a.Term("Σ_{j∈t} Σ_{i∈s} COND(R(i, j), 1, 0)"),
						"the two finite sums exchange",
						By(Swap, finiteS, finiteT)),
					FinalLeg(
						"and each column is counted by its indicator",
						By(Congruence, CountByIndicator, finiteS)),
				))
		}),
})}

// OddSumIffOddCount — a finite sum is odd exactly when it has an odd
// number of odd terms. Adding the indicator of oddness to each term makes
// every term even, so the sum and the indicator count have an even sum.
var OddSumIffOddCount = oddSumIffOddCountThm{family.Add(registry.ProofEntry{
	Name: "OddSumIffOddCount",
	Key:  "prop_9f607335d27d37b1",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀g:(A → num). ∀P:(A → bool).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ (nat_odd(g(x)) ⇔ P(x))",
		},
		Conclusion: "nat_odd(Σ_{x∈s} g(x)) ⇔ nat_odd(card({x:A | x ∈ s ∧ P(x)}))",
	},
		func(a *Argument, s *Expr[Set[A]], g *Arrow[A, Nat], P *Expr[Set[A]], finite, parity Fact) {
			evenIsDivisible := a.Have(
				"a number is even exactly when 2 divides it, both saying its remainder by 2 is 0",
				"∀n:num. nat_even(n) ⇔ 2 ∣ n",
				By(nat_parity.EvenIffModTwoZero, nat_divides.DividesMod))
			termwise := a.Have(
				"2 divides every term with its indicator added",
				"∀x:A. x ∈ s ⇒ 2 ∣ g(x) + COND(P(x), 1, 0)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inS := b.Assume()
					b.Cases(b.Term("P(x)"))
					b.When(
						"where P holds the term is odd, and adding 1 makes it even",
						func(c *Argument, holds Fact) {
							c.Show(
								"g(x) + 1 is even",
								ByArith(
									holds,
									parity.At(x),
									inS,
									evenIsDivisible.At(c.TermAs[Nat]("g(x) + 1")),
									nat_parity.EvenAdd.At(c.TermAs[Nat]("g(x)"), c.TermAs[Nat]("1"))))
						})
					b.Otherwise(
						"elsewhere the term is even, and 0 is added",
						func(c *Argument, fails Fact) {
							c.Show(
								"g(x) is even",
								ByArith(fails, parity.At(x), inS, evenIsDivisible.At(c.TermAs[Nat]("g(x)"))))
						})
				}))
			total := a.Have(
				"so 2 divides the sum with the count added, the count being the sum of the indicator",
				"nat_even(Σ_{x∈s} g(x) + card({x:A | x ∈ s ∧ P(x)}))",
				By(
					finite,
					termwise,
					evenIsDivisible.At(a.TermAs[Nat]("Σ_{x∈s} g(x) + card({x:A | x ∈ s ∧ P(x)})")),
					DividesSum.At(
						a.TermAs[Nat]("2"),
						a.TermAs[Fun[A, Nat]]("λx:A. g(x) + COND(P(x), 1, 0)"),
						s),
					Add.At(g, a.TermAs[Fun[A, Nat]]("λx:A. COND(P(x), 1, 0)"), s),
					CountByIndicator.At(s, P)))
			a.Show(
				"and two numbers with an even sum are odd together or even together",
				ByArith(
					total,
					nat_parity.EvenAdd.At(
						a.TermAs[Nat]("Σ_{x∈s} g(x)"),
						a.TermAs[Nat]("card({x:A | x ∈ s ∧ P(x)})"))))
		}),
})}

// DoorsAndRoomsParity — doors and rooms: for faces and simplices under an
// incidence, when every boundary face lies in one simplex and every other
// face in two, and a full simplex holds one door and any other none or
// two, an odd number of doors on the boundary means an odd number of full
// simplices. The pairs of a door and a simplex holding it are counted
// once by doors and once by simplices (DoubleCounting); the two sums are
// one number, and their odd terms are the boundary doors on the one side
// and the full simplices on the other.
var DoorsAndRoomsParity = doorsAndRoomsParityThm{family.Add(registry.ProofEntry{
	Name: "DoorsAndRoomsParity",
	Key:  "prop_312b47f57b3bd7a4",
	Reading: "Pure combinatorics at two arbitrary types and an arbitrary " +
		"incidence. The two finiteness hypotheses make every counted set finite; " +
		"with no faces the boundary count is 0, not odd, and the statement is vacuous.",
	Build: family.Theorem(Statement{
		Binders: "∀incident:(A → B → bool). " +
			"∀faces:set(A). " +
			"∀simplices:set(B). " +
			"∀boundary:(A → bool). " +
			"∀full:(B → bool). " +
			"∀door:(A → bool).",
		Hypotheses: []string{
			"finite(faces)",
			"finite(simplices)",
			"∀f:A. f ∈ faces ∧ boundary(f) ⇒ card({s:B | s ∈ simplices ∧ incident(f, s)}) = 1",
			"∀f:A. f ∈ faces ∧ ¬boundary(f) ⇒ card({s:B | s ∈ simplices ∧ incident(f, s)}) = 2",
			"∀s:B. s ∈ simplices ∧ full(s) ⇒ card({f:A | f ∈ faces ∧ incident(f, s) ∧ door(f)}) = 1",
			"∀s:B. " +
				"    s ∈ simplices ∧ ¬full(s) ⇒ " +
				"    card({f:A | f ∈ faces ∧ incident(f, s) ∧ door(f)}) = 0 ∨ " +
				"    card({f:A | f ∈ faces ∧ incident(f, s) ∧ door(f)}) = 2",
			"nat_odd(card({f:A | f ∈ faces ∧ door(f) ∧ boundary(f)}))",
		},
		Conclusion: "nat_odd(card({s:B | s ∈ simplices ∧ full(s)}))",
		Abbrev: Abbrev{
			{Name: "doors", Text: "{f:A | f ∈ faces ∧ door(f)}"},
		},
	},
		func(
			a *Argument,
			incident *Arrow2[A, B, Bool],
			faces *Expr[Set[A]],
			simplices *Expr[Set[B]],
			boundary *Expr[Set[A]],
			full *Expr[Set[B]],
			door *Expr[Set[A]],
			finiteFaces, finiteSimplices, boundaryOne, innerTwo, fullOne, otherNoneOrTwo, oddBoundary Fact,
		) {
			finiteDoors := a.Have(
				"the doors are finitely many, the faces being so",
				"finite(«doors»)",
				By(finiteFaces, finite_set.FiniteRestrict))
			doorsOf := a.Have(
				"the doors at a simplex are its faces that are doors",
				"∀s:B. {f:A | f ∈ «doors» ∧ incident(f, s)} = {f:A | f ∈ faces ∧ incident(f, s) ∧ door(f)}",
				BySets())
			boundaryDoors := a.Have(
				"and the doors on the boundary are the boundary faces that are doors",
				"{f:A | f ∈ «doors» ∧ boundary(f)} = {f:A | f ∈ faces ∧ door(f) ∧ boundary(f)}",
				BySets())
			pairs := a.Have(
				"the pairs of a door and a simplex holding it, counted by doors and by simplices",
				"Σ_{f∈«doors»} card({s:B | s ∈ simplices ∧ incident(f, s)}) = "+
					"Σ_{s∈simplices} card({f:A | f ∈ faces ∧ incident(f, s) ∧ door(f)})",
				Simp(Rev(doorsOf)),
				By(finiteDoors, finiteSimplices, DoubleCounting))
			doorParity := a.Have(
				"a door lies in an odd number of simplices exactly when it is on the boundary",
				"∀f:A. f ∈ «doors» ⇒ (nat_odd(card({s:B | s ∈ simplices ∧ incident(f, s)})) ⇔ boundary(f))",
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					isDoor := b.Assume()
					b.Cases(b.Term("boundary(f)"))
					b.When(
						"on the boundary it lies in one simplex",
						func(c *Argument, onBoundary Fact) {
							c.Show(
								"and 1 is odd",
								ByArith(onBoundary, boundaryOne.At(f), isDoor))
						})
					b.Otherwise(
						"inside it lies in two",
						func(c *Argument, inside Fact) {
							c.Show(
								"and 2 is even",
								ByArith(inside, innerTwo.At(f), isDoor))
						})
				}))
			simplexParity := a.Have(
				"a simplex has an odd number of doors exactly when it is full",
				"∀s:B. s ∈ simplices ⇒ (nat_odd(card({f:A | f ∈ faces ∧ incident(f, s) ∧ door(f)})) ⇔ full(s))",
				Derive(func(b *Argument) {
					s := b.FixAs[B]("s")
					inSimplices := b.Assume()
					b.Cases(b.Term("full(s)"))
					b.When(
						"a full simplex has one door",
						func(c *Argument, isFull Fact) {
							c.Show(
								"and 1 is odd",
								ByArith(isFull, fullOne.At(s), inSimplices))
						})
					b.Otherwise(
						"any other has none or two",
						func(c *Argument, notFull Fact) {
							c.Do(GroupPremises(inSimplices, notFull, otherNoneOrTwo.At(s)).SplitDisj(
								LeftHolds(
									"none, and 0 is even",
									Given(func(d *Argument, none Fact) {
										d.Show(
											"its count of doors is even",
											ByArith(notFull, none))
									})),
								RightHolds(
									"two, and 2 is even",
									Given(func(d *Argument, two Fact) {
										d.Show(
											"its count of doors is even",
											ByArith(notFull, two))
									}))))
						})
				}))
			byDoors := a.Have(
				"so the count by doors is odd exactly when the boundary doors are odd in number",
				"nat_odd(Σ_{f∈«doors»} card({s:B | s ∈ simplices ∧ incident(f, s)})) ⇔ "+
					"nat_odd(card({f:A | f ∈ faces ∧ door(f) ∧ boundary(f)}))",
				Simp(Rev(boundaryDoors)),
				By(finiteDoors, doorParity, OddSumIffOddCount))
			bySimplices := a.Have(
				"and the count by simplices exactly when the full simplices are",
				"nat_odd(Σ_{s∈simplices} card({f:A | f ∈ faces ∧ incident(f, s) ∧ door(f)})) ⇔ "+
					"nat_odd(card({s:B | s ∈ simplices ∧ full(s)}))",
				By(finiteSimplices, simplexParity, OddSumIffOddCount))
			a.Show(
				"the two counts are one number, so the full simplices are odd in number as the boundary doors are",
				By(oddBoundary, byDoors, bySimplices, pairs))
		}),
})}
