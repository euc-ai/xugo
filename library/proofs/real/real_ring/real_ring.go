// real_ring.go — the chapter: ℝ as a commutative ring.
//
// Five parts, marked by banners:
//
// - The axioms state the additive group on the left
// - What distributivity buys once the additive group cancels
// - Negation as a computation (an involution
// - `x - y` is `x + -y`
// - The chapter's one argument that reaches back for a multiplicative

package real_ring

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The axioms state the additive group on the left
// ---------------------------------------------------------------------------
//
// commutativity mirrors them on the right, and associativity turns the
// mirrored pair into cancellation.
//
// README §1 "The additive group, completed on the right".

// AddRightId — the axioms state the additive identity on the left;
// commutativity carries it to the right.
var AddRightId = addRightIdThm{family.Add(registry.ProofEntry{
	Name: "AddRightId",
	Key:  "prop_56a81e9302b5c415",
	Build: family.Theorem("∀x:real. x + &0 = x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			a.Do(
				// x + &0 = &0 + x — commutativity at (x, &0).
				Cite(real_construction.AddSym, x, v.Lit(0)),
				// ↦ &0 + x = x, the left identity.
				Cite(real_construction.AddLeftId),
			)
		}),
})}

// AddRightInv — the axioms state the additive inverse on the left;
// commutativity carries it to the right.
var AddRightInv = addRightInvThm{family.Add(registry.ProofEntry{
	Name: "AddRightInv",
	Key:  "prop_3ad59652fb2d6b7f",
	Build: family.Theorem("∀x:real. x + -x = &0",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			a.Do(
				// x + -x = -x + x — commutativity at (x, -x).
				Cite(real_construction.AddSym, x, v.Negate(x)),
				// ↦ -x + x = &0, the left inverse.
				Cite(real_construction.AddLeftInv),
			)
		}),
})}

// AddLeftCancel — adding x on the left is injective.
//
// The ⇐ direction is congruence. The ⇒ direction is the additive
// group's standard argument: -x undoes x, so a summand can be read back
// out of the sum it sits in, and sums that agree were built from
// summands that agree.
var AddLeftCancel = addLeftCancelThm{family.Add(registry.ProofEntry{
	Name: "AddLeftCancel",
	Key:  "prop_2031a7e5561ba03e",
	Build: family.Theorem("∀x y z:real. x + y = x + z ⇔ y = z",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			negX := v.Negate(x)
			invPair := v.Add(negX, x) // -x + x, the pair AddLeftInv collapses to &0
			a.Iff()
			a.Forward(
				"add -x on the left and read each summand back out of its sum",
				func(b *Argument, sum Fact) {
					b.Do(CalcEq(
						Leg(
							v.Add(zero, y),
							"a zero in front of y changes nothing",
							Cite(real_construction.AddLeftId)),
						Leg(
							v.Add(invPair, y),
							"and that zero is -x + x",
							Cite(real_construction.AddLeftInv)),
						Leg(
							v.Add(negX, v.Add(x, y)),
							"regroup, so -x faces the sum x + y",
							Cite(real_construction.AddAssoc)),
						Leg(
							v.Add(negX, v.Add(x, z)),
							"the hypothesis, under -x + ·",
							By(Normalized, sum)),
						Leg(
							v.Add(invPair, z),
							"regroup back, freeing -x + x from z",
							Cite(real_construction.AddAssoc)),
						Leg(
							v.Add(zero, z),
							"-x + x collapses to zero once more",
							Cite(real_construction.AddLeftInv)),
						FinalLeg(
							"and the leading zero drops off z",
							Cite(real_construction.AddLeftId)),
					))
				})
			a.Backward(
				"y and z are the same real, so x + y and x + z are the same sum",
				func(b *Argument, eq Fact) {
					b.Show(
						"congruence under x + ·",
						By(Normalized, eq))
				})
		}),
})}

// AddRightCancel — adding z on the right is injective.
//
// Nothing new is proved here: commutativity turns each of the two sums
// around so that z leads, and what is left is AddLeftCancel read
// verbatim. Both directions of the ⇔ travel that same conjugation, so
// the argument does not split.
var AddRightCancel = addRightCancelThm{family.Add(registry.ProofEntry{
	Name: "AddRightCancel",
	Key:  "prop_15e5e7fd6270f865",
	Build: family.Theorem("∀x y z:real. x + z = y + z ⇔ x = y",
		func(a *Argument, x, y, z Term) {
			a.Show(
				"commute both sums so that z leads, then cancel z on the left",
				By(
					At(real_construction.AddSym, x, z), // x + z = z + x
					At(real_construction.AddSym, y, z), // y + z = z + y
					At(AddLeftCancel, z, x, y),         // z + x = z + y ⇔ x = y
				))
		}),
})}

// AddLeftCancelZero — adding y to x leaves x alone exactly when y is
// zero.
//
// This is AddLeftCancel at z := &0, once the lone x on the right of the
// equation is read as the sum x + &0: cancelling the common x is then
// the entire content. The cancellation law is itself an equivalence, so
// both directions come out of it together and the ⇔ never has to be
// split.
var AddLeftCancelZero = addLeftCancelZeroThm{family.Add(registry.ProofEntry{
	Name: "AddLeftCancelZero",
	Key:  "prop_15777c71a3889f42",
	Build: family.Theorem("∀x y:real. x + y = x ⇔ y = &0",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				// x + y = x + &0 ⇔ y = &0 — cancellation at (x, y, &0).
				Cite(AddLeftCancel, x, y, v.Lit(0)),
				// and x + &0 is x, so that equivalence is the goal.
				Cite(AddRightId),
			)
		}),
})}

// NegLeftUnique — an additive inverse is unique: a left summand that
// cancels y is already -y.
//
// The ⇐ direction is the left-inverse axiom read at y. The ⇒ direction
// is the group's usual uniqueness argument: adding -y on the right of a
// sum that vanishes strips y off the left summand and leaves it exposed
// as -y.
var NegLeftUnique = negLeftUniqueThm{family.Add(registry.ProofEntry{
	Name: "NegLeftUnique",
	Key:  "prop_5f26aa1ee74850cb",
	Build: family.Theorem("∀x y:real. x + y = &0 ⇔ x = -y",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			negY := v.Negate(y)
			invPair := v.Add(y, negY) // y + -y, the pair AddRightInv collapses to &0
			a.Iff()
			a.Forward(
				"add -y on the right of the vanishing sum and read x back out",
				func(b *Argument, sum Fact) {
					b.Do(CalcEq(
						Leg(
							v.Add(x, zero),
							"a zero behind x changes nothing",
							Cite(AddRightId)),
						Leg(
							v.Add(x, invPair),
							"and that zero is y + -y",
							Cite(AddRightInv)),
						Leg(
							v.Add(v.Add(x, y), negY),
							"regroup, so -y faces the sum x + y",
							Cite(real_construction.AddAssoc)),
						Leg(
							v.Add(zero, negY),
							"the hypothesis, under · + -y",
							By(Normalized, sum)),
						FinalLeg(
							"and the leading zero drops off -y",
							Cite(real_construction.AddLeftId)),
					))
				})
			a.Backward(
				"x is -y, so the sum is the inverse pair -y + y",
				func(b *Argument, eq Fact) {
					b.Show(
						"substituting x = -y, the left inverse sends the sum to &0",
						By(Normalized, eq, At(real_construction.AddLeftInv, y)))
				})
		}),
})}

// AddAC — the three laws that let a rewriter normalize any +-sum: swap
// two summands, rebracket a triple, and lift the inner summand of a
// right-nested triple to the front. The first two ARE the axioms; the
// third is the two composed, which is what the AC deriver does.
var AddAC = addACThm{family.Add(registry.ProofEntry{
	Name: "AddAC",
	Key:  "prop_dc96d5186ad0efe2",
	Build: family.Theorem("∀n m p:real. "+
		"    m + n = n + m ∧ m + n + p = m + (n + p) ∧ m + (n + p) = n + (m + p)",
		func(a *Argument, n, m, p Term) {
			ctx := a.Ctx()
			a.Do(SplitConjAll(
				Case(
					"commutativity — the axiom itself",
					Cite(real_construction.AddSym)),
				// The axiom signs this equation the other way round.
				Case(
					"associativity — the axiom itself",
					Cite(real_construction.AddAssoc)),
				Case(
					"left-commutativity — the two leading summands trade "+
						"places: assoc unbrackets, sym swaps, assoc rebrackets",
					ACRegroupWith(real_construction.AddAC(ctx))),
			))
		}),
})}

// OfNumSuc — the numeral embedding sends ℕ's successor to adding one.
//
// This closes the additive group: with ℝ's sum in hand, it is where
// ℕ's own step first meets it. The successor is the sum n + 1 in ℕ,
// and the embedding is additive, so it carries that sum to &n + &1.
var OfNumSuc = ofNumSucThm{family.Add(registry.ProofEntry{
	Name: "OfNumSuc",
	Key:  "prop_51501ac4296bd1c5",
	Build: family.Theorem("∀n:num. &suc(n) = &n + &1",
		func(a *Argument, n Term) {
			one := a.Ctx().Numeral(1)
			a.Show(
				"read suc(n) as the sum n + 1 in ℕ, then carry that sum across the additive embedding",
				By(
					Normalized,
					At(nat_arith.Add1, n),                  // suc(n₀) = n₀ + 1
					At(real_construction.OfNumAdd, n, one), // &(n₀ + 1) = &n₀ + &1
				))
		}),
})}

// ---------------------------------------------------------------------------
// What distributivity buys once the additive group cancels
// ---------------------------------------------------------------------------
//
// what distributivity buys once the additive group cancels: the zero law,
// the identity on the right, the other distributive law, and the ×-AC pack
// that rewrites any product into normal form.
//
// README §2 "Zero, one, and the other distributive law".

// MulRightZero — the chapter's first fact that genuinely needs
// distributivity.
//
// Nothing in the multiplicative monoid decides what x·&0 is; the law
// linking the two structures does. Spreading x over the sum &0 + &0
// shows that x·&0 added to itself is x·&0 again, and a summand that can
// be added to a quantity without moving it is the additive identity —
// which is exactly what left-cancellation reads back out.
var MulRightZero = mulRightZeroThm{family.Add(registry.ProofEntry{
	Name: "MulRightZero",
	Key:  "prop_27802823ffbbf067",
	Build: family.Theorem("∀x:real. x * &0 = &0",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			prod := v.Mul(x, zero) // x · &0 — the quantity the whole argument is about
			doubled := a.Have(
				"adding x·&0 to itself does the same as adding &0 to it",
				MakeProp(v.Add(prod, prod).Eq(v.Add(prod, zero))),
				CalcEq(
					Leg(
						v.Mul(x, v.Add(zero, zero)),
						"distributivity backwards: the two copies are x spread over &0 + &0",
						Cite(real_construction.LeftDistrib)),
					Leg(
						prod,
						"the inner sum collapses — &0 + &0 is &0",
						Cite(real_construction.AddLeftId)),
					FinalLeg(
						"and re-attaching a zero on the right changes nothing",
						Cite(AddRightId)),
				))
			a.Show(
				"cancel the common x·&0 on the left: the two right-hand summands must agree",
				By(doubled, AddLeftCancel))
		}),
})}

// MulRightId — the axioms state the multiplicative identity on the
// left; commutativity carries it to the right.
var MulRightId = mulRightIdThm{family.Add(registry.ProofEntry{
	Name: "MulRightId",
	Key:  "prop_63390346f1a138d7",
	Build: family.Theorem("∀x:real. x * &1 = x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			a.Do(
				// x * &1 = &1 * x — commutativity at (x, &1).
				Cite(real_construction.MulSym, x, v.Lit(1)),
				// ↦ &1 * x = x, the left identity.
				Cite(real_construction.MulLeftId),
			)
		}),
})}

// MulLeftZero — zero annihilates on the left, by the commutative-ring law.
var MulLeftZero = mulLeftZeroThm{family.Add(registry.ProofEntry{
	Name:  "MulLeftZero",
	Key:   "prop_4b5a654764217ec9",
	Build: family.Theorem("∀x:real. &0 * x = &0", By(comm_ring.MulLeftZero.Read(CommRing))),
})}

// RightDistrib — the axioms distribute a factor over a sum on the left;
// commutativity carries the law to the right. The whole product swings
// around, the left-handed law fires once, and each summand swings back.
var RightDistrib = rightDistribThm{family.Add(registry.ProofEntry{
	Name: "RightDistrib",
	Key:  "prop_fae57c906b75a8f0",
	Build: family.Theorem("∀x y z:real. (x + y) * z = x * z + y * z",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			zSum := v.Mul(z, v.Add(x, y)) // z·(x + y)
			zx, zy := v.Mul(z, x), v.Mul(z, y)
			a.Do(CalcEq(
				Leg(
					zSum,
					"commute, putting the sum where the left-handed axiom wants it",
					Cite(real_construction.MulSym)),
				Leg(
					v.Add(zx, zy),
					"the left-handed axiom splits z across the sum",
					Cite(real_construction.LeftDistrib)),
				FinalLeg(
					"commute both summands back",
					By(At(real_construction.MulSym, z, x), At(real_construction.MulSym, z, y))),
			))
		}),
})}

// MulAC — the three laws that let a rewriter normalize any ×-product:
// swap two factors, rebracket a triple, and lift the inner factor of a
// right-nested triple to the front. The first two ARE the axioms; the
// third is the two composed, which is what the AC deriver does.
var MulAC = mulACThm{family.Add(registry.ProofEntry{
	Name: "MulAC",
	Key:  "prop_8f0225cc0a582714",
	Build: family.Theorem("∀n m p:real. "+
		"    m * n = n * m ∧ m * n * p = m * (n * p) ∧ m * (n * p) = n * (m * p)",
		func(a *Argument, n, m, p Term) {
			ctx := a.Ctx()
			a.Do(SplitConjAll(
				Case(
					"commutativity — the axiom itself",
					Cite(real_construction.MulSym)),
				// likewise, up to orientation: the axiom signs this equation
				// the other way round.
				Case(
					"associativity — the axiom itself",
					Cite(real_construction.MulAssoc)),
				Case(
					"left-commutativity — the two leading factors trade "+
						"places: assoc unbrackets, sym swaps, assoc rebrackets",
					ACRegroupWith(real_construction.MulAC(ctx))),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Negation as a computation (an involution
// ---------------------------------------------------------------------------
//
// negation as a computation (an involution, a distribution over sums,
// multiplication by -&1) and as a move across an equation.
//
// README §3 "Negation".

// NegNeg — -x annihilates two partners: --x standing on its right, and
// x standing on its left. Both sums are &0, so the two partners agree,
// and cancelling -x off the front leaves --x = x.
var NegNeg = negNegThm{family.Add(registry.ProofEntry{
	Name: "NegNeg",
	Key:  "prop_e614a4f850243a39",
	Build: family.Theorem("∀x:real. --x = x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			negX := v.Negate(x)
			negNegX := v.Negate(negX)
			a.Do(
				// -x + --x = -x + x ⇔ --x = x — cancellation of -x on the left
				// is what reduces the goal to a claim about the two sums.
				Cite(AddLeftCancel, negX, negNegX, x),
				// -x + --x = &0 — the right inverse, at -x.
				Cite(AddRightInv, negX),
				// ↦ -x + x = &0, the left-inverse axiom, which is the other sum.
				Cite(real_construction.AddLeftInv),
			)
		}),
})}

// NegAdd — the sum of the negations is an additive inverse of the sum,
// and an additive inverse is unique, so it is THE negation of the sum.
//
// That it is an inverse is a regrouping: laid against x + y, the sum
// -x + -y offers each summand its own negative, and two vanishing pairs
// leave &0. NegLeftUnique then reads the conclusion off directly, which
// is what keeps the argument to one computation.
var NegAdd = negAddThm{family.Add(registry.ProofEntry{
	Name: "NegAdd",
	Key:  "prop_b092b00f4f49b9eb",
	Build: family.Theorem("∀x y:real. -(x + y) = -x + -y",
		func(a *Argument, x, y Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero := v.Lit(0)
			sum := v.Add(x, y)                        // x + y — the quantity being negated
			negSum := v.Add(v.Negate(x), v.Negate(y)) // -x + -y — the candidate inverse
			xPair := v.Add(v.Negate(x), x)            // -x + x
			yPair := v.Add(v.Negate(y), y)            // -y + y

			vanish := a.Have(
				"-x + -y tested against x + y: the sum vanishes",
				MakeProp(v.Add(negSum, sum).Eq(zero)),
				CalcEq(
					Leg(
						v.Add(xPair, yPair),
						"regroup, so each negative meets its own summand",
						ACRegroupWith(real_construction.AddAC(ctx))),
					Leg(
						v.Add(zero, zero),
						"each pair is a left inverse, so each collapses to &0",
						Cite(real_construction.AddLeftInv)),
					FinalLeg(
						"and zero added to zero is zero",
						Cite(real_construction.AddLeftId)),
				))
			a.Show(
				"uniqueness of the additive inverse: the summand that cancels x + y IS -(x + y)",
				By(vanish, NegLeftUnique))
		}),
})}

// NegZero — the sum -&0 + &0 is read twice. Adding &0 on the right
// changes nothing, so it is -&0; the left-inverse axiom says it is &0.
// Hence -&0 = -&0 + &0 = &0.
var NegZero = negZeroThm{family.Add(registry.ProofEntry{
	Name: "NegZero",
	Key:  "prop_7471902afe125897",
	Build: family.Theorem("-&0 = &0",
		func(a *Argument) {
			v := ops(a.Ctx())
			negZero := v.Negate(v.Lit(0))
			a.Do(
				// -&0 + &0 = -&0 — right identity at -&0.
				Cite(AddRightId, negZero),
				// ↦ -&0 = -&0 + &0, which is the sum above read the other way.
				Cite(real_construction.AddLeftInv),
			)
		}),
})}

// MulRightNeg — the chapter's bridge between the additive and the
// multiplicative structure.
//
// The multiplicative monoid says nothing about what x·(-y) is; what
// pins it down is what it adds to. Distributivity folds the sum
// x·(-y) + x·y back into x spread over -y + y, which is x·&0 and so
// &0 — and the only thing that annihilates x·y is its negation.
var MulRightNeg = mulRightNegThm{family.Add(registry.ProofEntry{
	Name: "MulRightNeg",
	Key:  "prop_b272166742cb1a01",
	Build: family.Theorem("∀x y:real. x * -y = -(x * y)",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			negY := v.Negate(y)
			vanishingSum := v.Add(v.Mul(x, negY), v.Mul(x, y)) // x·(-y) + x·y
			a.Do(
				Suffices(MakeProp(vanishingSum.Eq(zero)),
					"an additive inverse is unique, so it is enough that x·(-y) annihilates x·y",
					Cite(NegLeftUnique)),
				CalcEq(
					Leg(
						v.Mul(x, v.Add(negY, y)),
						"distributivity backwards: the two products are x spread over -y + y",
						Cite(real_construction.LeftDistrib)),
					Leg(
						v.Mul(x, zero),
						"and that inner sum is the left-inverse pair, which collapses to &0",
						Cite(real_construction.AddLeftInv)),
					FinalLeg(
						"leaving x times zero, which is zero",
						Cite(MulRightZero)),
				),
			)
		}),
})}

// MulLeftNeg — negating the left factor negates the product, by the ring law.
var MulLeftNeg = mulLeftNegThm{family.Add(registry.ProofEntry{
	Name:  "MulLeftNeg",
	Key:   "prop_5b22515583ff635e",
	Build: family.Theorem("∀x y:real. -x * y = -(x * y)", By(comm_ring.MulLeftNeg.Read(CommRing))),
})}

// MulNegNeg — two signs in one product cancel. Each sign leaves its
// factor through the bridge on its own side: the left one first, then
// the right one from inside the negation the first left behind. What
// then stands outside the product is a double negation, which is no
// sign at all.
var MulNegNeg = mulNegNegThm{family.Add(registry.ProofEntry{
	Name: "MulNegNeg",
	Key:  "prop_18793ed8c9c2f9ce",
	Build: family.Theorem("∀x y:real. -x * -y = x * y",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			product := v.Mul(x, y)                     // x·y
			leftOut := v.Negate(v.Mul(x, v.Negate(y))) // -(x·(-y))
			bothOut := v.Negate(v.Negate(product))     // --(x·y)
			a.Do(CalcEq(
				Leg(
					leftOut,
					"the sign on the left factor comes out of the product",
					Cite(MulLeftNeg)),
				Leg(
					bothOut,
					"then the sign on the right factor, from inside the negation",
					Cite(MulRightNeg)),
				FinalLeg(
					"and the doubled sign is no sign at all",
					Cite(NegNeg)),
			))
		}),
})}

// NegMinusOne — the unary minus is not a separate operation: it is the
// scalar -&1 acting by multiplication. The sign on the left factor is
// the only thing that distinguishes this product from &1 · x, so
// carrying it out of the product leaves the multiplicative identity to
// finish the computation.
var NegMinusOne = negMinusOneThm{family.Add(registry.ProofEntry{
	Name: "NegMinusOne",
	Key:  "prop_7a50000dfe098d48",
	Build: family.Theorem("∀x:real. -&1 * x = -x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			a.Do(CalcEq(
				Leg(
					v.Negate(v.Mul(v.Lit(1), x)),
					"the sign sits on a factor, so it comes out of the product",
					Cite(MulLeftNeg)),
				FinalLeg(
					"and what is left inside is one times x",
					Cite(real_construction.MulLeftId)),
			))
		}),
})}

// NegEq — the two ways of writing one equation between a real and a
// negation.
//
// Each direction is the involution read at one of the two variables:
// given -x = y, negating both sides makes -y the double negation of x,
// which is x; given x = -y, the same move at y turns -x into y. Neither
// direction needs the other, and both instances stand together, so the
// ⇔ never has to be split.
var NegEq = negEqThm{family.Add(registry.ProofEntry{
	Name: "NegEq",
	Key:  "prop_37011e4a3e940e82",
	Build: family.Theorem("∀x y:real. -x = y ⇔ x = -y",
		func(a *Argument, x, y Term) {
			// The two instances are the whole argument, but they meet the goal
			// as an ⇔ between two equations rather than as a rewrite, so the
			// close needs the clause-forming shaping first — after it, Basic
			// finishes and no refutation runs.
			a.Show(
				"negate each side; the double negation the move creates collapses",
				By(
					Normalized,
					At(NegNeg, x), // -(-x) = x, which carries the ⇒ direction
					At(NegNeg, y), // -(-y) = y, which carries the ⇐
				))
		}),
})}

// NegEqZero — the sum x + -x is read twice, and the two readings meet
// at the goal. AddRightInv says the sum is &0; AddLeftCancelZero says
// it returns x exactly when the summand -x is &0. So "-x is &0" and
// "x is &0" are one statement about that single sum.
//
// The argument never mentions the involution, and there is no case
// split: this is the additive group cancelling, not a fact about
// negation, so both directions of the ⇔ are the same reading.
var NegEqZero = negEqZeroThm{family.Add(registry.ProofEntry{
	Name: "NegEqZero",
	Key:  "prop_5b764de065f70a63",
	Build: family.Theorem("∀x:real. -x = &0 ⇔ x = &0",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			a.Do(
				// x + -x = x ⇔ -x = &0 — cancellation at y := -x: a summand
				// leaves the sum sitting at x exactly when it is &0.
				Cite(AddLeftCancelZero, x, v.Negate(x)),
				// ↦ &0 = x ⇔ x = &0 — the sum evaluates, and what is left is
				// one equation read in either order.
				Cite(AddRightInv),
			)
		}),
})}

// ---------------------------------------------------------------------------
// `x - y` is `x + -y`
// ---------------------------------------------------------------------------
//
// `x - y` is `x + -y`, so this movement is bookkeeping over the previous
// two: unfold the definition, apply a group law, fold back. The identities
// come first, then the add/subtract adjunctions, the negation
// interactions, the regrouping laws, distribution over a difference, and
// last the law later chapters reach for most.
//
// README §4 "Subtraction".

// SubRightZero — unfolding `real_sub` turns the difference into a sum
// whose right summand is the negation of zero. NegZero collapses that
// summand back to zero, and what is left is the right identity.
var SubRightZero = subRightZeroThm{family.Add(registry.ProofEntry{
	Name: "SubRightZero",
	Key:  "prop_70926f49d621735d",
	Build: family.Theorem("∀x:real. x - &0 = x",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x. x + -&0 = x — real_sub's defining equation, applied
				// under the binder: the statement stays ∀-closed.
				Unfold(RealSubDef),
				// ↦ ∀x. x + &0 = x — zero is its own negative.
				Cite(NegZero),
				// and that IS the right-identity law.
				Cite(AddRightId),
			)
		}),
})}

// SubLeftZero — subtraction is not a primitive of ℝ: it is defined as
// adding the negation. Unfolding that definition leaves zero added to
// -x, which the left-identity axiom erases, and no subtraction remains
// to reason about.
var SubLeftZero = subLeftZeroThm{family.Add(registry.ProofEntry{
	Name: "SubLeftZero",
	Key:  "prop_21f3e34a873b663b",
	Build: family.Theorem("∀x:real. &0 - x = -x",
		func(a *Argument, x Term) {
			a.Do(
				// &0 - x ↦ &0 + -x — real_sub's defining equation.
				Unfold(RealSubDef),
				// ↦ &0 + -x = -x, the left identity read at -x.
				Cite(real_construction.AddLeftId),
			)
		}),
})}

// SubRefl — subtraction is not a primitive of this chapter. Unfolding
// `real_sub` turns a difference into a sum with a negation, and the
// difference of a real with ITSELF is then the right-inverse law
// verbatim: AddRightInv wearing a minus sign.
var SubRefl = subReflThm{family.Add(registry.ProofEntry{
	Name: "SubRefl",
	Key:  "prop_ff55b32bcbd8b62c",
	Build: family.Theorem("∀x:real. x - x = &0",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x. x + -x = &0 — real_sub's defining equation, applied
				// under the binder: the statement stays ∀-closed.
				Unfold(RealSubDef),
				// and that IS the right-inverse law.
				Cite(AddRightInv),
			)
		}),
})}

// SubAddRight — subtraction is only a name for adding the negation, so
// this is the additive group's cancellation written out. Nothing about
// subtraction beyond its definition enters the argument, which is why
// the chain reaches no further than the group axioms.
var SubAddRight = subAddRightThm{family.Add(registry.ProofEntry{
	Name: "SubAddRight",
	Key:  "prop_7226b41eeefbb778",
	Build: family.Theorem("∀x y:real. x - y + y = x",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			negY := v.Negate(y)
			zero := v.Lit(0)
			unfolded := v.Add(v.Add(x, negY), y)  // (x + -y) + y
			regrouped := v.Add(x, v.Add(negY, y)) // x + (-y + y)
			a.Do(CalcEq(
				Leg(
					unfolded,
					"x - y is by definition x + -y",
					Unfold(RealSubDef)),
				Leg(
					regrouped,
					"reassociate, bracketing y with its own negation",
					Cite(real_construction.AddAssoc)),
				Leg(
					v.Add(x, zero),
					"the inverse pair -y + y collapses to zero",
					Cite(real_construction.AddLeftInv)),
				FinalLeg(
					"and zero is an identity on the right",
					Cite(AddRightId)),
			))
		}),
})}

// SubAddLeft — the left-handed half of the add/subtract adjunction, and
// the one law here that never opens a difference at all. The sum is the
// one SubAddRight already settles, written the other way round, so
// commutativity is the whole content: `x - y` rides through as a single
// opaque term and every fact used about it is SubAddRight's.
var SubAddLeft = subAddLeftThm{family.Add(registry.ProofEntry{
	Name: "SubAddLeft",
	Key:  "prop_34de33d0b8741c5b",
	Build: family.Theorem("∀x y:real. y + (x - y) = x",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			diff := v.Minus.Apply(x, y) // x - y, carried whole
			a.Do(CalcEq(
				Leg(
					v.Add(diff, y),
					"commute, so the difference meets its subtrahend on the right",
					Cite(real_construction.AddSym)),
				FinalLeg(
					"where taking away and adding back is already settled",
					Cite(SubAddRight)),
			))
		}),
})}

// EqSubRightAdd — half of the add/subtract adjunction, and one of the
// two laws that let an equation be rearranged.
//
// The two sides of the ⇔ are one comparison written at two places.
// Putting y back on the right of x - y returns x, so comparing x with
// z + y is comparing (x - y) + y with z + y — and a common summand on
// the right cancels. Both directions travel that single comparison, so
// the ⇔ does not split; and the difference is never opened, since every
// fact used about it is SubAddRight's.
var EqSubRightAdd = eqSubRightAddThm{family.Add(registry.ProofEntry{
	Name: "EqSubRightAdd",
	Key:  "prop_7596892541a71f2d",
	Build: family.Theorem("∀x y z:real. x - y = z ⇔ x = z + y",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			diff := v.Minus.Apply(x, y) // x - y, carried whole
			// The premises meet the goal as an ⇔ between equations rather
			// than as a rewrite, so the close is shaped first; Basic finishes
			// there and no refutation runs.
			a.Show(
				"put y back on the right of x - y, then cancel it from both sums",
				By(
					Normalized,
					At(SubAddRight, x, y),          // (x - y) + y = x
					At(AddRightCancel, diff, z, y), // (x - y) + y = z + y ⇔ x - y = z
				))
		}),
})}

// SubRightNeg — the two minus signs meet. Subtraction is defined as
// adding the negation, so what gets added here is the negation of -y;
// negation is an involution, so that is y itself, and no law about
// subtraction beyond its definition is involved.
var SubRightNeg = subRightNegThm{family.Add(registry.ProofEntry{
	Name: "SubRightNeg",
	Key:  "prop_44edc2555ed14e3c",
	Build: family.Theorem("∀x y:real. x - -y = x + y",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. x + --y = x + y — real_sub's defining equation,
				// applied under the binders: the statement stays ∀-closed.
				Unfold(RealSubDef),
				// and the doubled sign on y is no sign at all.
				Cite(NegNeg),
			)
		}),
})}

// NegSub — with both differences written as sums there is no
// subtraction left to reason about, only a negated sum. One unfold
// reaches both sides at once, which is why the chain that follows is
// pure additive algebra and never has to fold anything back.
var NegSub = negSubThm{family.Add(registry.ProofEntry{
	Name: "NegSub",
	Key:  "prop_fd14ee27e0c64d2",
	Build: family.Theorem("∀x y:real. -(x - y) = y - x",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			negX := v.Negate(x)
			distributed := v.Add(negX, v.Negate(v.Negate(y))) // -x + --y
			collapsed := v.Add(negX, y)                       // -x + y
			a.Do(
				// ↦ -(x + -y) = y + -x
				Unfold(RealSubDef),
				CalcEq(
					Leg(
						distributed,
						"negation distributes over the sum",
						Cite(NegAdd)),
					Leg(
						collapsed,
						"and the doubled sign on y is no sign at all",
						Cite(NegNeg)),
					FinalLeg(
						"leaving two summands to commute",
						Cite(real_construction.AddSym)),
				),
			)
		}),
})}

// SubNegNeg — what is left of this law once both differences are
// written as sums is commutativity of addition wearing subtraction's
// notation.
//
// NegSub would reach it too, through NegAdd; unfolding directly is the
// same number of steps and one dep fewer.
var SubNegNeg = subNegNegThm{family.Add(registry.ProofEntry{
	Name: "SubNegNeg",
	Key:  "prop_f54627093198e486",
	Build: family.Theorem("∀x y:real. -x - -y = y - x",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. -x + --y = y + -x — real_sub's defining equation,
				// which reaches both differences at once.
				Unfold(RealSubDef),
				// ↦ ∀x y. -x + y = y + -x — negation is an involution.
				Cite(NegNeg),
				// which closes: the two sides are now one sum written in
				// both orders, and addition is commutative.
				Cite(real_construction.AddSym),
			)
		}),
})}

// SubLeftNeg — subtracting y from -x is negating the sum. Written
// as a sum, the left side is -x + -y, which is exactly how NegAdd
// spells the negation of x + y; so one unfold and one reading of that
// law, right to left, is the whole proof.
var SubLeftNeg = subLeftNegThm{family.Add(registry.ProofEntry{
	Name: "SubLeftNeg",
	Key:  "prop_fc44007aa3f70c1d",
	Build: family.Theorem("∀x y:real. -x - y = -(x + y)",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. -x + -y = -(x + y)
				Unfold(RealSubDef),
				// which is NegAdd's own equation read right to left, and closes.
				Cite(NegAdd),
			)
		}),
})}

// SubTriangle — the intermediate point cancels itself. Written as
// sums, the two differences offer b and -b to the same total, and once
// they are brought together the law is the additive group's inverse
// axiom with an identity to tidy up after it.
//
// Nothing about subtraction survives the unfold, which is why the
// argument reaches no further than the four additive axioms.
var SubTriangle = subTriangleThm{family.Add(registry.ProofEntry{
	Name: "SubTriangle",
	Key:  "prop_8000125824138c46",
	Build: family.Theorem("∀a b c:real. a - b + (b - c) = a - c",
		// The receiver is `arg`, not the chapter's usual `a` — the statement
		// binds a, b and c, and the binder names win.
		func(arg *Argument, a, b, c Term) {
			ctx := arg.Ctx()
			v := ops(ctx)
			negB, negC := v.Negate(b), v.Negate(c)
			zero := v.Lit(0)
			regrouped := v.Add(a, v.Add(v.Add(negB, b), negC)) // a + ((-b + b) + -c)
			collapsed := v.Add(a, v.Add(zero, negC))           // a + (&0 + -c)
			arg.Do(
				// ↦ (a + -b) + (b + -c) = a + -c
				Unfold(RealSubDef),
				CalcEq(
					Leg(
						regrouped,
						"regroup, so that -b meets the b the second difference contributes",
						ACRegroupWith(real_construction.AddAC(ctx))),
					Leg(
						collapsed,
						"the inverse pair -b + b collapses to zero",
						Cite(real_construction.AddLeftInv)),
					FinalLeg(
						"and zero is an identity on the left",
						Cite(real_construction.AddLeftId)),
				),
			)
		}),
})}

// SubAddPairwise — pairing each minuend with its own subtrahend costs
// nothing, because written out as sums both sides are the same four
// summands a, b, -c, -d in a different order. One thing stands in the
// way of saying so: on the left the two subtrahends are negated
// together, so the negation has to be distributed before either of
// them is a summand that can move at all.
var SubAddPairwise = subAddPairwiseThm{family.Add(registry.ProofEntry{
	Name: "SubAddPairwise",
	Key:  "prop_a62dee0f9303b0e8",
	Build: family.Theorem("∀a b c d:real. a + b - (c + d) = a - c + (b - d)",
		// The receiver is `arg`, not the chapter's usual `a` — the statement
		// binds a, b, c and d, and the binder names win.
		func(arg *Argument, a, b, c, d Term) {
			ctx := arg.Ctx()
			v := ops(ctx)
			separated := v.Add(v.Add(a, b), v.Add(v.Negate(c), v.Negate(d))) // (a + b) + (-c + -d)
			arg.Do(
				// ↦ (a + b) + -(c + d) = (a + -c) + (b + -d)
				Unfold(RealSubDef),
				CalcEq(
					Leg(
						separated,
						"negating a sum negates each summand, which is what frees -c and -d to move apart",
						Cite(NegAdd)),
					FinalLeg(
						"and the rest is a rearrangement of the same four summands: each subtrahend joins its own minuend",
						ACRegroupWith(real_construction.AddAC(ctx))),
				),
			)
		}),
})}

// SubSelfAdd — the x that is subtracted meets the x inside the sum and
// they annihilate, so only -y survives. Getting them to meet is the
// whole argument: the difference has to be opened, the negation pushed
// across the sum so that -x appears at all, and the brackets moved so
// that -x stands next to x.
var SubSelfAdd = subSelfAddThm{family.Add(registry.ProofEntry{
	Name: "SubSelfAdd",
	Key:  "prop_ab734384fc88206d",
	Build: family.Theorem("∀x y:real. x - (x + y) = -y",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			negX, negY := v.Negate(x), v.Negate(y)
			zero := v.Lit(0)
			opened := v.Add(x, v.Negate(v.Add(x, y))) // x + -(x + y)
			spread := v.Add(x, v.Add(negX, negY))     // x + (-x + -y)
			regrouped := v.Add(v.Add(x, negX), negY)  // (x + -x) + -y
			a.Do(CalcEq(
				Leg(
					opened,
					"x - (x + y) is by definition x + -(x + y)",
					Unfold(RealSubDef)),
				Leg(
					spread,
					"negating the sum negates each summand, which is what puts -x in reach of x",
					Cite(NegAdd)),
				Leg(
					regrouped,
					"reassociate, bracketing x with its own negation",
					Cite(real_construction.AddAssoc)),
				Leg(
					v.Add(zero, negY),
					"the inverse pair x + -x collapses to zero",
					Cite(AddRightInv)),
				FinalLeg(
					"and zero is an identity on the left",
					Cite(real_construction.AddLeftId)),
			))
		}),
})}

// SubLeftDistrib — the chapter has no law about subtraction to apply
// here, and needs none: a difference is a sum with a negation, so
// distributing over one is the left-handed axiom applied to the other.
// The single extra ingredient is MulRightNeg, which carries the
// negation back out of the product it landed inside.
var SubLeftDistrib = subLeftDistribThm{family.Add(registry.ProofEntry{
	Name: "SubLeftDistrib",
	Key:  "prop_158fd6b584660eaf",
	Build: family.Theorem("∀x y z:real. x * (y - z) = x * y - x * z",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			xy := v.Mul(x, y) // the summand the chain never touches
			a.Do(
				// ↦ x·(y + -z) = x·y + -(x·z)
				Unfold(RealSubDef),
				CalcEq(
					Leg(
						v.Add(xy, v.Mul(x, v.Negate(z))),
						"the left-handed axiom splits x across the sum",
						Cite(real_construction.LeftDistrib)),
					FinalLeg(
						"and x·(-z) is -(x·z): the sign comes out of the product",
						Cite(MulRightNeg)),
				),
			)
		}),
})}

// SubRightDistrib — the mirror of SubLeftDistrib, and the same
// observation: there is no law about subtraction to apply, because a
// difference is a sum with a negation. Written that way the goal is
// the right-handed distributive law, and the only thing left to do is
// carry the negation back out of the product it landed inside.
var SubRightDistrib = subRightDistribThm{family.Add(registry.ProofEntry{
	Name: "SubRightDistrib",
	Key:  "prop_f9d94b87e72e739a",
	Build: family.Theorem("∀x y z:real. (x - y) * z = x * z - y * z",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			xz := v.Mul(x, z) // the summand the chain never touches
			a.Do(
				// ↦ (x + -y)·z = x·z + -(y·z)
				Unfold(RealSubDef),
				CalcEq(
					Leg(
						v.Add(xz, v.Mul(v.Negate(y), z)),
						"the right-handed law splits the sum across z",
						Cite(RightDistrib)),
					FinalLeg(
						"and (-y)·z is -(y·z): the sign comes out of the product",
						Cite(MulLeftNeg)),
				),
			)
		}),
})}

// SubEqZero — two rewrites, and no case split: both directions of the
// ⇔ travel the same road.
//
// Unfolding `real_sub` restates the left side as "x cancels -y from the
// left", which is exactly what NegLeftUnique recognises, and it names
// the only real that does so: -(-y). NegNeg collapses that double
// negation, leaving the same equation on both sides of the ⇔.
var SubEqZero = subEqZeroThm{family.Add(registry.ProofEntry{
	Name: "SubEqZero",
	Key:  "prop_3ef627c006335397",
	Build: family.Theorem("∀x y:real. x - y = &0 ⇔ x = y",
		func(a *Argument, x, y Term) {
			a.Do(
				// x - y ↦ x + -y — real_sub's defining equation.
				Unfold(RealSubDef),
				// ↦ x = --y ⇔ x = y — the left summand that annihilates -y,
				// identified.
				Cite(NegLeftUnique),
				// and --y is y, so the ⇔ now reads x = y ⇔ x = y.
				Cite(NegNeg),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The chapter's one argument that reaches back for a multiplicative
// ---------------------------------------------------------------------------
//
// the chapter's one argument that reaches back for a multiplicative
// inverse, and the cancellation it buys.
//
// README §5 "The integral domain".

// MulEqZero — the integral-domain law, and the chapter's only argument
// that reaches back for a multiplicative inverse.
//
// One direction is the two zero laws: a factor that is &0 annihilates
// whatever stands beside it, left or right. The other is where ℝ being a
// field is finally used — a left factor that is NOT &0 has an inverse,
// and running the vanishing product through it strips that factor off,
// leaving the surviving factor alone against &0.
var MulEqZero = mulEqZeroThm{family.Add(registry.ProofEntry{
	Name: "MulEqZero",
	Key:  "prop_5805f3562867b765",
	Build: family.Theorem("∀x y:real. x * y = &0 ⇔ x = &0 ∨ y = &0",
		// x arrives as a wrapper rather than a bare Term because the ⇒
		// branch needs to BUILD the proposition x = &0 to case-split on, and
		// Eq lives on the wrapper.
		func(a *Argument, x *TermWrapper, y Term) {
			v := ops(a.Ctx())
			zero, one := v.Lit(0), v.Lit(1)
			invX := v.Inv.Apply(x)
			a.Iff()
			a.Forward(
				"divide the vanishing product by the factor that is not &0",
				func(b *Argument, prod Fact) {
					nonzero := b.Unless(
						x.Eq(zero),
						"x = &0 is the left disjunct outright",
						TrivialNormalized())
					// With x ≠ &0 the left disjunct is refuted, so what is
					// left to prove is y = &0.
					b.Do(TrivialSimplify())
					scale := b.Have(
						"a real that is not &0 has a left inverse",
						MakeProp(v.Mul(invX, x).Eq(one)),
						By(nonzero, At(real_construction.MulLeftInverse, x)))
					b.Do(CalcEq(
						Leg(
							v.Mul(one, y),
							"a leading &1 changes nothing",
							Cite(real_construction.MulLeftId)),
						Leg(
							v.Mul(v.Mul(invX, x), y),
							"and that &1 is inv(x) · x",
							By(Normalized, scale)),
						Leg(
							v.Mul(invX, v.Mul(x, y)),
							"regroup, so the inverse faces the product itself",
							Cite(real_construction.MulAssoc)),
						Leg(
							v.Mul(invX, zero),
							"the hypothesis, under inv(x) ·",
							By(Normalized, prod)),
						FinalLeg(
							"and a factor of &0 collapses what is left",
							Cite(MulRightZero)),
					))
				})
			a.Backward(
				"a factor that is &0 annihilates the product",
				func(b *Argument, vanishes Fact) {
					b.Show(
						"one of the two zero laws applies, whichever factor the hypothesis names",
						By(
							Normalized,
							vanishes,
							At(MulLeftZero, y),  // &0 · y = &0
							At(MulRightZero, x), // x · &0 = &0
						))
				})
		}),
})}

// MulLeftCancel — multiplicative cancellation, and the last thing the
// integral domain buys.
//
// The argument moves everything to one side, where the zero-divisor law
// can see it. An equality is the vanishing of a difference; a difference
// of two products with a common left factor is that factor times a
// single difference; a product vanishes exactly when one of its factors
// does; and the surviving difference vanishes exactly when its two sides
// agree — which is the right-hand disjunct. The four steps are
// equivalences throughout, so nothing distinguishes the two directions
// of the ⇔ and the proof does not split.
var MulLeftCancel = mulLeftCancelThm{family.Add(registry.ProofEntry{
	Name: "MulLeftCancel",
	Key:  "prop_f39430542921e56f",
	Build: family.Theorem("∀x y z:real. x * y = x * z ⇔ x = &0 ∨ y = z",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			gap := v.Minus.Apply(y, z) // the difference the two products differ by
			a.Show(
				"carry the equation to one side, factor x out of the difference, and split the vanishing product",
				By(
					Normalized,
					At(SubEqZero, v.Mul(x, y), v.Mul(x, z)), // x·y - x·z = &0 ⇔ x·y = x·z
					At(SubLeftDistrib, x, y, z),             // x·(y - z) = x·y - x·z
					At(MulEqZero, x, gap),                   // x·(y - z) = &0 ⇔ x = &0 ∨ y - z = &0
					At(SubEqZero, y, z),                     // y - z = &0 ⇔ y = z
				))
		}),
})}

// MulRightCancel — the commutative mirror of MulLeftCancel.
//
// Cancellation does not care which side the shared factor stands on, so
// there is no second integral-domain argument to make here. Commuting
// each of the two products carries the common z from the back of both
// to the front of both, and what is then left is a statement
// MulLeftCancel already decides. Both directions of the ⇔ ride the same
// two commutations, so the proof does not split.
var MulRightCancel = mulRightCancelThm{family.Add(registry.ProofEntry{
	Name: "MulRightCancel",
	Key:  "prop_d543523a1691f637",
	Build: family.Theorem("∀x y z:real. x * z = y * z ⇔ x = y ∨ z = &0",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			// The two commutations are named facts rather than the chapter's
			// usual flat rewrite cites: against this ⇔ goal a MulSym cite
			// parks as a hypothesis and leaves the conclusion untouched
			// (bare and ground alike), so each swing is established first
			// and then rewritten with.
			swingX := a.Have(
				"commute the left product so the shared factor leads",
				MakeProp(v.Mul(x, z).Eq(v.Mul(z, x))),
				Cite(real_construction.MulSym))
			swingY := a.Have(
				"commute the right product the same way",
				MakeProp(v.Mul(y, z).Eq(v.Mul(z, y))),
				Cite(real_construction.MulSym))
			a.Do(
				swingX.Rw(), // ↦ z·x = y·z ⇔ x = y ∨ z = &0
				swingY.Rw(), // ↦ z·x = z·y ⇔ x = y ∨ z = &0
			)
			a.Show(
				"the shared factor now leads both products, which is cancellation on the left",
				By(Normalized, At(MulLeftCancel, z, x, y))) // z·x = z·y ⇔ z = &0 ∨ x = y
		}),
})}
