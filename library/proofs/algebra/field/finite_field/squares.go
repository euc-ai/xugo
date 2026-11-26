// squares.go — the squares of a finite field: where 2 ≠ 0 the nonzero
// squares are half of the nonzero elements, told apart by Euler's criterion.

package finite_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteFieldSquares — in a finite field where 2 ≠ 0 the nonzero squares
// are half of the nonzero elements, and some nonzero element is not a
// square: squaring sends the nonzero elements onto the nonzero squares two
// to one (field.FieldSquareRoots), and since one is a nonzero element the
// half is a proper part.
var FiniteFieldSquares = finiteFieldSquaresThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldSquares",
	Key:  "prop_ea42608271b8777b",
	Reading: "2≠0 alone makes squaring two to one on the nonzero elements; finiteness turns that " +
		"into the count, and the count into a nonsquare — the complex numbers, where 2≠0, have none. " +
		"In characteristic two squaring is one to one, and every element of a finite field is a square.",

	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A).",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
		},
		Conclusion: "card(«squares»(k)) * 2 = card(k.carrier) - 1 ∧ " +
			"(∃e:A. e ∈ k.carrier ∧ e ≠ k.zero ∧ e ∉ «squares»(k))",
		Abbrev: Abbrev{
			{Name: "nonzero", Text: "{z:A | z ∈ k.carrier ∧ z ≠ k.zero}"},
		},
	}, func(a *Argument, k Fact, finite, two Fact) {
		ring := field.RingOn.Read(k)
		carrier := a.TermAs[Set[A]]("k.carrier")
		zero := a.TermAs[A]("k.zero")
		nonzero := a.TermAs[Set[A]]("«nonzero»")
		squares := a.TermAs[Set[A]]("«squares»(k)")
		nonzeroFinite := a.Have(
			"the nonzero elements form a finite set",
			"finite(«nonzero»)",
			By(finite, finite_set.FiniteRestrict.At(carrier, a.TermAs[Set[A]]("λz:A. z ≠ k.zero"))))
		inside := a.Have(
			"a square of a nonzero element is nonzero",
			"«squares»(k) ⊆ «nonzero»",
			BySets(field.MulEqZeroOn.Read(k), comm_ring.MulIn.Read(ring)))
		squaresFinite := a.Have(
			"so the nonzero squares form a finite set",
			"finite(«squares»(k))",
			By(nonzeroFinite, inside, finite_set.FiniteSubset.At(squares, nonzero)))
		oneSquare := a.Have(
			"each nonzero element x has the one square x·x",
			"∀x:A. x ∈ «nonzero» ⇒ ∃!y:A. y ∈ «squares»(k) ∧ x * x = y",
			BySets())
		twoRoots := a.Have(
			"each nonzero square has exactly two square roots, both nonzero",
			"∀y:A. y ∈ «squares»(k) ⇒ has_size({x:A | x ∈ «nonzero» ∧ x * x = y}, 2)",
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				square := b.Assume()
				z, root := b.UnpackAs[A](square, "z")
				parts := b.Conjuncts(
					root,
					"z lies in k",
					"z is not zero",
					"y is z·z")
				zm := b.MemberOf[on.Any](z, parts[0])
				yNonzero := b.Have(
					"y is not zero, as z is not",
					"y ≠ k.zero",
					By(Normalized, parts[1], parts[2], field.MulEqZeroOn.Read(k).At(zm, zm)))
				nonzeroRoots := b.Have(
					"every square root of the nonzero y is nonzero",
					"{x:A | x ∈ «nonzero» ∧ x * x = y} = {x:A | x ∈ k.carrier ∧ x * x = y}",
					BySets(yNonzero, comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(zero)))
				rooted := b.Have(
					"z is a square root of y",
					"{x:A | x ∈ k.carrier ∧ x * x = y} ≠ ∅",
					BySets(parts[0], parts[2]))
				b.Show(
					"y has no square root or two, and it has z",
					By(
						yNonzero,
						two,
						rooted,
						nonzeroRoots,
						field.FieldSquareRoots.Read(k).At(y),
						cardinality.HasSizeZero.At(b.TermAs[Set[A]]("{x:A | x ∈ k.carrier ∧ x * x = y}"))))
			}))
		byFibres := a.Have(
			"counting the nonzero elements by their squares, two to each",
			"card(«nonzero») = sum(«squares»(k), λy:A. 2)",
			By(
				nonzeroFinite,
				oneSquare,
				twoRoots,
				nat_sum.CardByFibres.At(
					nonzero,
					squares,
					a.TermAs[Fun2[A, A, Bool]]("λx:A. λy:A. x * x = y"),
					a.TermAs[Fun[A, Nat]]("λy:A. 2"))))
		halving := a.Have(
			"the nonzero elements are twice the nonzero squares",
			"card(«nonzero») = card(«squares»(k)) * 2",
			ByArith(
				byFibres,
				squaresFinite,
				nat_sum.ScalarLeft.At(a.TermAs[Nat]("2"), a.TermAs[Fun[A, Nat]]("λy:A. 1"), squares),
				nat_sum.SumOfOnes.At(squares)))
		deleted := a.Have(
			"the nonzero elements are k with zero removed",
			"«nonzero» = delete(k.carrier, k.zero)",
			BySets())
		nonzeroCount := a.Have(
			"removing zero from k leaves card(k) − 1 elements",
			"card(«nonzero») = card(k.carrier) - 1",
			By(finite, deleted, cardinality.CardDelete.At(carrier, zero), comm_ring.ZeroIn.Read(ring)))
		nonempty := a.Have(
			"one is a nonzero element",
			"«nonzero» ≠ ∅",
			BySets(comm_ring.OneIn.Read(ring), field.OneNotZeroOn.Read(k)))
		fewer := a.Have(
			"so the nonzero squares are fewer than the nonzero elements",
			"card(«squares»(k)) < card(«nonzero»)",
			ByArith(halving, nonzeroFinite, nonempty, cardinality.CardEqZero.At(nonzero)))
		notAll := a.Have(
			"hence not every nonzero element is a square",
			"¬(«nonzero» ⊆ «squares»(k))",
			ByArith(fewer, squaresFinite, cardinality.CardSubset.At(nonzero, squares)))
		a.Show(
			"the count, and a nonzero nonsquare",
			SplitConj(
				Case(
					"twice the nonzero squares is card(k) − 1",
					ByArith(halving, nonzeroCount)),
				Case(
					"a nonzero element outside the squares exists",
					BySets(notAll))))
	}),
})}

// SquaresAreHalf — in a finite field where 2 ≠ 0 the nonzero squares number
// half of the nonzero elements, (q − 1)/2 for q the size of the field, and
// q − 1 is twice that half: twice their number is q − 1
// (FiniteFieldSquares), which leaves no remainder.
var SquaresAreHalf = squaresAreHalfThm{family.Add(registry.ProofEntry{
	Name: "SquaresAreHalf",
	Key:  "prop_dacc57b03426c02a",
	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A).",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
		},
		Conclusion: "card(«squares»(k)) = «half»(k) ∧ card(k.carrier) - 1 = «half»(k) + «half»(k)",
	}, func(a *Argument, k Fact, finite, two Fact) {
		a.Show(
			"q − 1 is the number of nonzero squares times two, with no remainder",
			ByArith(
				finite,
				two,
				FiniteFieldSquares.Read(k),
				nat_div_mod.DivUniq.At(
					a.TermAs[Nat]("card(k.carrier) - 1"),
					a.TermAs[Nat]("2"),
					a.TermAs[Nat]("card(«squares»(k))"),
					a.TermAs[Nat]("0"))))
	}),
})}

// RootsOfUnityBound — for n > 0 a field has at most n elements x with
// x ^ n = 1: zero and those elements are all fixed by the (n + 1)-th power,
// which fixes at most n + 1 points (FiniteConstantsBound), and zero is not
// among them.
var RootsOfUnityBound = rootsOfUnityBoundThm{family.Add(registry.ProofEntry{
	Name: "RootsOfUnityBound",
	Key:  "prop_a27ef2e38ca2cff8",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_on(A). ∀n:num.",
		Hypotheses: []string{"0 < n"},
		Conclusion: "finite(«roots») ∧ card(«roots») ≤ n",
		Abbrev: Abbrev{
			{Name: "roots", Text: "{x:A | x ∈ F.carrier ∧ monoid_pow(F.mul, F.one, x, n) = F.one}"},
			{Name: "fixed", Text: "finite_constants(field_ring(F), n + 1, 1)"},
		},
	}, func(a *Argument, F field.FieldFact[on.F], n *Expr[Nat], positive Fact) {
		ring := field.RingOn.Read(F)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		one := a.TermAs[Nat]("1")
		zero := a.TermAs[A]("F.zero")
		roots := a.TermAs[Set[A]]("«roots»")
		fixed := a.TermAs[Set[A]]("«fixed»")
		withZero := a.TermAs[Set[A]]("insert(F.zero, «roots»)")
		fixedDef := FiniteConstantsDef.At(
			a.TermAs[RingOps[A]]("field_ring(F)"), a.TermAs[Nat]("n + 1"), one)
		zeroM := a.MemberOf[on.F](zero, comm_ring.ZeroIn.Read(ring))
		fewFixed := a.Have(
			"the (n + 1)-th power fixes at most n + 1 points",
			"finite(«fixed») ∧ card(«fixed») ≤ n + 1",
			ByArith(positive, FiniteConstantsBound.Read(F).At(a.TermAs[Nat]("n + 1"), one)))
		// The fixed points finite_constants(R, q, m) are those of the q^m-th
		// power; read at q = n + 1 and m = 1, the exponent is (n + 1) ^ 1.
		step := a.Have(
			"the (n + 1)-th power of x is its n-th power times x",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ F.carrier"},
				Conclusion: "monoid_pow(F.mul, F.one, x, (n + 1) ^ 1) = monoid_pow(F.mul, F.one, x, n) * x",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xm := b.MemberOf[on.F](x, b.Assume())
				b.Show(
					"a power of a sum of exponents is a product",
					ByArith(
						F,
						xm,
						comm_monoid.PowAddOn.Read(multiplicative).At(xm, n, one),
						comm_monoid.PowOneOn.Read(multiplicative).At(xm)))
			}))
		zeroFixed := a.Have(
			"zero is fixed, as zero absorbs the product",
			"F.zero ∈ «fixed»",
			BySets(
				zeroM,
				step.At(zero),
				fixedDef,
				comm_ring.MulRightZeroOn.Read(ring).At(comm_monoid.PowIn.Read(multiplicative).At(zeroM, n))))
		rootsFixed := a.Have(
			"a root of one is fixed, its n-th power being one",
			"«roots» ⊆ «fixed»",
			BySets(step, fixedDef, comm_monoid.LeftIdentityOn.Read(multiplicative)))
		predecessor := a.Have(
			"n is one more than n − 1",
			"n = n - 1 + 1",
			ByArith(positive))
		zeroNotRoot := a.Have(
			"zero is no root of one, its positive power being zero",
			"monoid_pow(F.mul, F.one, F.zero, n) ≠ F.one",
			ByArith(
				F,
				predecessor,
				comm_monoid.PowAddOn.Read(multiplicative).At(zeroM, a.TermAs[Nat]("n - 1"), one),
				comm_monoid.PowOneOn.Read(multiplicative).At(zeroM),
				field.OneNotZeroOn.Read(F)))
		allFixed := a.Have(
			"so zero and the roots of one are fixed",
			"insert(F.zero, «roots») ⊆ «fixed»",
			BySets(zeroFixed, rootsFixed))
		a.Show(
			"the roots of one with zero added are at most n + 1",
			ByArith(
				zeroNotRoot,
				allFixed,
				fewFixed,
				finite_set.FiniteSubset.At(withZero, fixed),
				finite_set.FiniteInsert.At(zero, roots),
				cardinality.CardSubset.At(withZero, fixed),
				cardinality.InsertCountsOneMore.At(roots, zero)))
	}),
})}

// HalfPowerRootsAreSquares — in a finite field of q elements where 2 ≠ 0,
// the roots of x^((q − 1)/2) = 1 are exactly the nonzero squares: a nonzero
// square z·z raised to the power (q − 1)/2 is z^(q − 1) = 1 (FiniteFieldLagrange),
// so the (q − 1)/2 nonzero squares (SquaresAreHalf) are among those roots,
// which are at most (q − 1)/2 (RootsOfUnityBound).
var HalfPowerRootsAreSquares = halfPowerRootsAreSquaresThm{family.Add(registry.ProofEntry{
	Name: "HalfPowerRootsAreSquares",
	Key:  "prop_3d9da7d1c7c7f6ce",
	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A).",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
		},
		Conclusion: "«roots» = «squares»(k)",
		Abbrev: Abbrev{
			{Name: "roots", Text: "{x:A | x ∈ k.carrier ∧ monoid_pow(k.mul, k.one, x, «half»(k)) = k.one}"},
		},
	}, func(a *Argument, k Fact, finite, two Fact) {
		ring := field.RingOn.Read(k)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		half := a.TermAs[Nat]("«half»(k)")
		squares := a.TermAs[Set[A]]("«squares»(k)")
		roots := a.TermAs[Set[A]]("«roots»")
		halves := a.Conjuncts(
			GroupPremises(finite, two, SquaresAreHalf.Read(k)),
			"there are h = (q − 1)/2 nonzero squares",
			"and q − 1 is twice h")
		count, twice := halves[0], halves[1]
		positive := a.Have(
			"h is positive, a field having at least two elements",
			"0 < «half»(k)",
			ByArith(
				finite,
				twice,
				field.CarrierSubfield.Read(k),
				FiniteSubfieldAtLeastTwo.Read(k).At(a.TermAs[Set[A]]("k.carrier"))))
		squaresAreRoots := a.Have(
			"a nonzero square z·z has h-th power z^(q − 1) = 1",
			"∀z:A. z ∈ k.carrier ∧ z ≠ k.zero ⇒ monoid_pow(k.mul, k.one, z * z, «half»(k)) = k.one",
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				parts := b.Conjuncts(
					b.Assume(),
					"z lies in k",
					"z is not zero")
				zm := b.MemberOf[on.Any](z, parts[0])
				b.Show(
					"(z·z)^h = z^h · z^h = z^(h + h) = z^(q − 1)",
					By(
						finite,
						parts[1],
						twice,
						comm_monoid.MulPowOn.Read(multiplicative).At(zm, zm, half),
						comm_monoid.PowAddOn.Read(multiplicative).At(zm, half, half),
						FiniteFieldLagrange.Read(k).At(zm)))
			}))
		inside := a.Have(
			"the nonzero squares are roots",
			"«squares»(k) ⊆ «roots»",
			BySets(squaresAreRoots, comm_ring.MulIn.Read(ring)))
		bound := a.Have(
			"there are at most h roots",
			"finite(«roots») ∧ card(«roots») ≤ «half»(k)",
			By(positive, RootsOfUnityBound.Read(k).At(half)))
		a.Show(
			"h squares inside at most h roots fill them",
			ByArith(count, inside, bound, cardinality.CardSubsetLe.At(squares, roots)))
	}),
})}

// FiniteFieldEulerCriterion — Euler's criterion in a finite field of q
// elements where 2 ≠ 0: a nonzero element raised to the power (q − 1)/2 is
// one when it is a square and minus one when it is not. The roots of
// x^((q − 1)/2) = 1 are the nonzero squares (HalfPowerRootsAreSquares); off
// them the power still squares to x^(q − 1) = 1, so it is the other square
// root of one (field.SquareRootsOfSquare).
var FiniteFieldEulerCriterion = finiteFieldEulerCriterionThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldEulerCriterion",
	Key:  "prop_2d746ed4be508acd",
	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A). ∀d:A.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
			"d ∈ k.carrier",
			"d ≠ k.zero",
		},
		Conclusion: "(d ∈ «squares»(k) ⇒ monoid_pow(k.mul, k.one, d, «half»(k)) = k.one) ∧ " +
			"(d ∉ «squares»(k) ⇒ monoid_pow(k.mul, k.one, d, «half»(k)) = -k.one)",
	}, func(a *Argument, k Fact, d *Expr[A], finite, two, dIn, dNonzero Fact) {
		ring := field.RingOn.Read(k)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		half := a.TermAs[Nat]("«half»(k)")
		dm := a.MemberOf[on.Any](d, dIn)
		roots := a.Have(
			"the roots of x^h = 1, h = (q − 1)/2, are the nonzero squares",
			"{x:A | x ∈ k.carrier ∧ monoid_pow(k.mul, k.one, x, «half»(k)) = k.one} = «squares»(k)",
			By(finite, two, HalfPowerRootsAreSquares.Read(k)))
		a.Show(
			"a square has h-th power one and a nonsquare minus one",
			SplitConj(
				Case(
					"a nonzero square is a root of x^h = 1",
					Derive(func(b *Argument) {
						square := b.Assume()
						b.Show(
							"d lies among the roots",
							BySets(square, roots))
					})),
				Case(
					"a nonsquare has h-th power minus one",
					Derive(func(b *Argument) {
						nonsquare := b.Assume()
						halves := b.Conjuncts(
							GroupPremises(finite, two, SquaresAreHalf.Read(k)),
							"there are h nonzero squares",
							"and q − 1 is twice h")
						squared := b.Have(
							"d^h squares to d^(q − 1) = 1",
							"monoid_pow(k.mul, k.one, d, «half»(k)) * monoid_pow(k.mul, k.one, d, «half»(k)) = k.one * k.one",
							ByArith(
								k,
								finite,
								dNonzero,
								halves[1],
								comm_monoid.PowAddOn.Read(multiplicative).At(dm, half, half),
								FiniteFieldLagrange.Read(k).At(dm)))
						notOne := b.Have(
							"d^h is not one, d not being a square",
							"monoid_pow(k.mul, k.one, d, «half»(k)) ≠ k.one",
							BySets(nonsquare, dIn, roots))
						oneM := b.MemberOf[on.Any](b.TermAs[A]("k.one"), comm_ring.OneIn.Read(ring))
						b.Show(
							"so d^h is minus one, the other square root of one",
							By(
								squared,
								notOne,
								field.SquareRootsOfSquare.Read(k).At(oneM, comm_monoid.PowIn.Read(multiplicative).At(dm, half))))
					}))))
	}),
})}

// SquareOrTwistedSquare — in a finite field where 2 ≠ 0, for a nonsquare e
// exactly one of a nonzero d and e·d is a square: by Euler's criterion
// (FiniteFieldEulerCriterion) e^h = −1 for h = (q − 1)/2, so (e·d)^h = −d^h,
// and the h-th power of a nonzero element is one exactly on the squares and
// minus one off them, one and minus one being distinct.
var SquareOrTwistedSquare = squareOrTwistedSquareThm{family.Add(registry.ProofEntry{
	Name: "SquareOrTwistedSquare",
	Key:  "prop_7ef77d56b443c269",
	Reading: "d≠0 is load-bearing: at d = 0 neither d nor e·d = 0 is a nonzero square, and " +
		"the equivalence fails. So is e≠0: at e = 0, e·d = 0 is never one, and the equivalence " +
		"fails at every nonsquare d. 2≠0 separates one from minus one; in a finite field of " +
		"characteristic two every element is a square, and no nonsquare e exists.",

	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A). ∀e d:A.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
			"e ∈ k.carrier",
			"e ≠ k.zero",
			"e ∉ «squares»(k)",
			"d ∈ k.carrier",
			"d ≠ k.zero",
		},
		Conclusion: "d ∈ «squares»(k) ⇔ e * d ∉ «squares»(k)",
	}, func(
		a *Argument,
		k Fact,
		e, d *Expr[A],
		finite, two, eIn, eNonzero, eNonsquare, dIn, dNonzero Fact,
	) {
		ring := field.RingOn.Read(k)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		half := a.TermAs[Nat]("«half»(k)")
		em := a.MemberOf[on.Any](e, eIn)
		dm := a.MemberOf[on.Any](d, dIn)
		edm := comm_ring.MulIn.Read(ring).At(em, dm)
		eNegative := a.Have(
			"e is no square, so e^h is minus one",
			"monoid_pow(k.mul, k.one, e, «half»(k)) = -k.one",
			By(finite, two, eNonzero, eNonsquare, FiniteFieldEulerCriterion.Read(k).At(em)))
		product := a.Have(
			"so (e·d)^h = e^h · d^h = −d^h",
			"monoid_pow(k.mul, k.one, e * d, «half»(k)) = -monoid_pow(k.mul, k.one, d, «half»(k))",
			ByArith(
				k,
				eNegative,
				comm_monoid.MulPowOn.Read(multiplicative).At(em, dm, half),
				comm_monoid.PowIn.Read(multiplicative).At(dm, half)))
		edNonzero := a.Have(
			"e·d is not zero",
			"e * d ≠ k.zero",
			By(eNonzero, dNonzero, field.MulEqZeroOn.Read(k).At(em, dm)))
		signs := a.Have(
			"one is not minus one, as 2 ≠ 0",
			"k.one ≠ -k.one",
			ByArith(k, two))
		a.Iff()
		a.Forward(
			"a square d makes e·d a nonsquare",
			func(b *Argument, dSquare Fact) {
				dOne := b.Have(
					"d is a square, so d^h is one",
					"monoid_pow(k.mul, k.one, d, «half»(k)) = k.one",
					By(finite, two, dNonzero, dSquare, FiniteFieldEulerCriterion.Read(k).At(dm)))
				edNegative := b.Have(
					"then (e·d)^h = −d^h is minus one",
					"monoid_pow(k.mul, k.one, e * d, «half»(k)) = -k.one",
					ByArith(k, dOne, product, comm_monoid.PowIn.Read(multiplicative).At(dm, half)))
				b.Show(
					"(e·d)^h is minus one, not one, so e·d is not a square",
					By(finite, two, edNonzero, signs, edNegative, FiniteFieldEulerCriterion.Read(k).At(edm)))
			})
		a.Backward(
			"a nonsquare e·d makes d a square",
			func(b *Argument, edNonsquare Fact) {
				edNegative := b.Have(
					"e·d is no square, so (e·d)^h is minus one",
					"monoid_pow(k.mul, k.one, e * d, «half»(k)) = -k.one",
					By(finite, two, edNonzero, edNonsquare, FiniteFieldEulerCriterion.Read(k).At(edm)))
				dOne := b.Have(
					"then −d^h = −1, so d^h is one",
					"monoid_pow(k.mul, k.one, d, «half»(k)) = k.one",
					ByArith(k, edNegative, product, comm_monoid.PowIn.Read(multiplicative).At(dm, half)))
				b.Show(
					"d^h is one, not minus one, so d is a square",
					By(finite, two, dNonzero, signs, dOne, FiniteFieldEulerCriterion.Read(k).At(dm)))
			})
	}),
})}

// SquareRootsWithTwistTotalTwo — in a finite field where 2 ≠ 0, for a
// nonsquare e an element d and its twist e·d have two square roots between
// them: where d = 0 each has the one square root zero (field.FieldSquareRoots),
// and otherwise exactly one of d and e·d is a square (SquareOrTwistedSquare),
// which has two square roots while the other has none.
var SquareRootsWithTwistTotalTwo = squareRootsWithTwistTotalTwoThm{family.Add(registry.ProofEntry{
	Name: "SquareRootsWithTwistTotalTwo",
	Key:  "prop_412fa4c7b3feff03",
	Build: family.Sections(Statement{
		Binders: "∀k:field_on(A). ∀e d:A.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
			"e ∈ k.carrier",
			"e ≠ k.zero",
			"e ∉ «squares»(k)",
			"d ∈ k.carrier",
		},
		Conclusion: "card(«roots»(d)) + card(«roots»(e * d)) = 2",
		Abbrev: Abbrev{
			{Name: "roots", Text: "λc:A. {z:A | z ∈ k.carrier ∧ z * z = c}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		rootCount := ctx.Lemma(Statement{
			Binders: "∀k:field_on(A). ∀d:A.",
			Hypotheses: []string{
				"k.one + k.one ≠ k.zero",
				"d ≠ k.zero",
			},
			Conclusion: "(d ∈ «squares»(k) ⇒ card(«roots»(d)) = 2) ∧ (d ∉ «squares»(k) ⇒ card(«roots»(d)) = 0)",
		}, func(a *Argument, k Fact, d *Expr[A], two, dNonzero Fact) {
			a.Show(
				"a nonzero square has two square roots, a nonzero nonsquare none",
				SplitConj(
					Case(
						"a square d = r·r has r among its roots, so it has two of them",
						Derive(func(b *Argument) {
							square := b.Assume()
							_, root := b.UnpackAs[A](square, "r")
							found := b.Have(
								"r is a square root of d",
								"«roots»(d) ≠ ∅",
								BySets(root))
							sized := b.Have(
								"d has none or two square roots, and r is one",
								"has_size(«roots»(d), 2)",
								By(two, dNonzero, found, field.FieldSquareRoots.Read(k).At(d), cardinality.HasSizeZero))
							b.Show(
								"so it has two",
								By(sized, cardinality.HasSizeDef))
						})),
					Case(
						"a root r of a nonsquare d is nonzero, as d is, so d = r·r would be a nonzero square",
						Derive(func(b *Argument) {
							nonsquare := b.Assume()
							none := b.Have(
								"no element of k squares to d",
								"«roots»(d) = ∅",
								BySets(dNonzero, nonsquare, field.MulEqZeroOn.Read(k)))
							b.Show(
								"so d has no square root to count",
								By(none, cardinality.CardClauses))
						})),
				))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			k Fact,
			e, d *Expr[A],
			finite, two, eIn, eNonzero, eNonsquare, dIn Fact,
		) {
			ed := a.TermAs[A]("e * d")
			em := a.MemberOf[on.Any](e, eIn)
			dm := a.MemberOf[on.Any](d, dIn)
			a.Cases(a.TermAs[Bool]("d = k.zero"))
			a.When(
				"where d vanishes, zero is the one square root of d and of e·d",
				func(b *Argument, dZero Fact) {
					edZero := b.Have(
						"e·d vanishes with d",
						"e * d = k.zero",
						ByArith(k, dZero, em))
					oneRoot := b.Have(
						"zero is the one square root of d",
						"card(«roots»(d)) = 1",
						By(two, dZero, field.FieldSquareRoots.Read(k).At(d), cardinality.HasSizeDef))
					oneTwistedRoot := b.Have(
						"and of e·d",
						"card(«roots»(e * d)) = 1",
						By(two, edZero, field.FieldSquareRoots.Read(k).At(ed), cardinality.HasSizeDef))
					b.Show(
						"one root and one make two",
						ByArith(oneRoot, oneTwistedRoot))
				})
			a.Otherwise(
				"elsewhere exactly one of d and e·d is a square, and it has both square roots",
				func(b *Argument, dNonzero Fact) {
					edNonzero := b.Have(
						"e·d is a product of nonzero elements of a field",
						"e * d ≠ k.zero",
						ByArith(k, dNonzero, eNonzero, dm, em))
					exactlyOne := b.Have(
						"e is no square, so d is a square exactly when e·d is not",
						"d ∈ «squares»(k) ⇔ e * d ∉ «squares»(k)",
						By(finite, two, eNonzero, eNonsquare, dNonzero, SquareOrTwistedSquare.Read(k).At(em, dm)))
					b.Cases(b.TermAs[Bool]("d ∈ «squares»(k)"))
					b.When(
						"d is a square and e·d is not",
						func(c *Argument, dSquare Fact) {
							twoRoots := c.Have(
								"d has two square roots",
								"card(«roots»(d)) = 2",
								By(two, dNonzero, dSquare, Read(rootCount, k).At(d)))
							noTwistedRoot := c.Have(
								"e·d has none",
								"card(«roots»(e * d)) = 0",
								By(two, edNonzero, exactlyOne, dSquare, Read(rootCount, k).At(ed)))
							c.Show(
								"two square roots and none make two",
								ByArith(twoRoots, noTwistedRoot))
						})
					b.Otherwise(
						"e·d is a square and d is not",
						func(c *Argument, dNonsquare Fact) {
							noRoot := c.Have(
								"d has no square root",
								"card(«roots»(d)) = 0",
								By(two, dNonzero, dNonsquare, Read(rootCount, k).At(d)))
							twoTwistedRoots := c.Have(
								"e·d has two",
								"card(«roots»(e * d)) = 2",
								By(two, edNonzero, exactlyOne, dNonsquare, Read(rootCount, k).At(ed)))
							c.Show(
								"no square root and two make two",
								ByArith(noRoot, twoTwistedRoots))
						})
				})
		})
	}),
})}
