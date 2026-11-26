// int_congruence.go — the chapter: congruence mod n on ℤ.
//
// Seven parts, marked by banners:
//
// - Congruence is an equivalence
// - The two readings of one definition
// - ℕ's congruence, read in ℤ
// - What may be replaced inside a congruence
// - What a congruence buys for computing a remainder: it may be taken
// EARLY
// - What congruences may be combined by
// - Naming one integer out of a congruence class

package int_congruence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Congruence is an equivalence
// ---------------------------------------------------------------------------
//
// Before it is anything else the chapter's relation is an equivalence,
// which is what lets its classes be spoken of at all. The definition
// alone proves it: neither reading below is needed.

// CongruenceEquivalence — read through its definition, x ≡ y (mod m)
// says that x - y is a multiple of m, and each of the three properties
// asks for one more multiple, which is exhibited outright: 0, the given
// one negated, the two given ones added. The residue classes mod m are
// the classes of this equivalence, so relations/equivalence's calculus
// of classes reads at it.
var CongruenceEquivalence = congruenceEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "CongruenceEquivalence",
	Key:  "prop_f71451afc6cfbe7e",
	Build: family.Theorem("∀m:int. equivalence(λx:int. λy:int. x ≡ y (mod m))",
		func(a *Argument, m *Expr[Int]) {
			v := ops(a.Ctx())

			a.Do(
				// ask for the three properties, and read the relation as
				// "x - y is a multiple of m": the congruence is
				// divisibility of the difference, and divisibility is
				// having a multiple
				Unfold(equivalence.Equivalence), Unfold(IntCongDef), Unfold(int_divides.IntDividesDef),
				SplitConjAll(
					Case(
						"reflexive: x - x is m times 0",
						Derive(func(b *Argument) {
							b.Do(Unfold(equivalence.ReflexiveDef))
							b.FixAs[Int]("x")
							b.Take(v.Zero)
							b.Show(
								"x - x and m · 0 are both 0",
								ByArith())
						})),
					Case(
						"symmetric: y - x is m times the negated multiple",
						Derive(func(b *Argument) {
							b.Do(Unfold(equivalence.SymmetricDef))
							b.FixAs[Int]("x")
							b.FixAs[Int]("y")
							related := b.Assume()
							// x - y = m · z, z the multiple the hypothesis hands over
							_, gap := b.Unpack(related)
							b.Take(b.TermAs[Int]("-z"))
							b.Show(
								"y - x = -(x - y) = m · (-z)",
								ByArith(gap))
						})),
					Case(
						"transitive: x - z is m times the sum of the two multiples",
						Derive(func(b *Argument) {
							b.Do(Unfold(equivalence.TransitiveDef))
							b.FixAs[Int]("x")
							b.FixAs[Int]("y")
							b.FixAs[Int]("z")
							both := b.Conjuncts(
								b.Assume(),
								"the first congruence: x - y is a multiple k of m",
								"and the second: y - z is a multiple l")
							// The definition calls both multiples z; they are named k and l.
							_, gapXY := b.Unpack(both[0], "k")
							_, gapYZ := b.Unpack(both[1], "l")
							b.Take(b.TermAs[Int]("k + l"))
							b.Show(
								"x - z = (x - y) + (y - z) = m · k + m · l",
								ByArith(gapXY, gapYZ))
						})),
				))
		}),
})}

// ---------------------------------------------------------------------------
// The two readings of one definition
// ---------------------------------------------------------------------------
//
// They share a file because a proof about congruence opens by choosing
// between them, and it is the same choice every time: witness the
// multiple, or compare the remainders.

// CongruentIffMultiple makes the multiple explicit, and that is the
// whole content: to prove a congruence you exhibit `d`, and to use one
// you are handed it. It is the step at which a congruence becomes an
// equation.
var CongruentIffMultiple = congruentIffMultipleThm{family.Add(registry.ProofEntry{
	Name: "CongruentIffMultiple",
	Key:  "prop_5af862a4741ff2d4",
	Build: family.Theorem("∀x y n:int. x ≡ y (mod n) ⇔ ∃d:int. x - y = n * d",
		func(a *Argument) {

			// Two unfoldings and the two sides meet in the middle. The
			// binders are left standing: each definition rewrites beneath
			// them, so no quantity here needs a name.
			a.Do(
				// The congruence is defined as divisibility of the
				// difference ↦ n ∣ (x - y).
				Unfold(IntCongDef),
				// and divisibility is the existence of the multiple, which
				// is the right-hand side up to the orientation of the
				// equation — so this one closes.
				Unfold(int_divides.IntDividesDef),
			)
		}),
})}

// CongruentIffSameRem removes the existential. `CongruentIffMultiple`
// makes the multiple explicit, so proving a congruence there means
// producing one; here nothing need be produced, because the division
// algorithm has already computed a normal form for each side and being
// congruent is nothing more than having the same normal form. That is
// what makes the relation decidable, and it is the shape the rest of
// the chapter reasons in.
//
// The two directions are two different uses of the division algorithm,
// sharing only the characterization above and the commutativity of `·`.
//
// ⇐ subtracts the two division identities from each other. The
// remainders are assumed equal, so they cancel, and what survives is n
// times the difference of the quotients: a multiple, exhibited outright
// rather than searched for.
//
// ⇒ never touches a division identity. The multiple the congruence
// hands over carries y up to x, and a whole multiple of n added to a
// dividend is invisible to the remainder — `int_div_rem.RemMulAdd`,
// which holds at every divisor, the zero one included. So the modulus
// &0 is not a special case here, and neither arm splits on it.
var CongruentIffSameRem = congruentIffSameRemThm{family.Add(registry.ProofEntry{
	Name: "CongruentIffSameRem",
	Key:  "prop_80006998fb369bd4",
	Build: family.Theorem("∀x y n:int. x ≡ y (mod n) ⇔ rem(x, n) = rem(y, n)",
		func(a *Argument, x, y, n Term) {
			v := ops(a.Ctx())

			a.Iff()
			a.Forward(
				"the multiple carries y up to x, and the remainder does not see a whole multiple of n go by",
				func(b *Argument, congruent Fact) {
					d, gap := b.Obtain(
						"the congruence hands its multiple over",
						"∃d:int. x - y = n * d",
						By(congruent, CongruentIffMultiple))

					b.Show(
						"so x is y plus that multiple, and dividing it by n leaves y's own remainder",
						By(
							gap,
							At(int_real_lift.EqSubRightAdd, x, y, v.Mul.Apply(n, d)), // x - y = n * d ⇔ x = n * d + y
							At(int_real_lift.MulSym, n, d),                           // n * d = d * n
							At(int_div_rem.RemMulAdd, d, n, y)))                      // int_rem(d * n + y, n) = int_rem(y, n)
				})
			a.Backward(
				"equal remainders leave only the quotients to differ, and n times that difference is the multiple",
				func(b *Argument, sameRem Fact) {
					quotX, quotY := v.IntDiv.Apply(x, n), v.IntDiv.Apply(y, n)
					remX, remY := v.IntRem.Apply(x, n), v.IntRem.Apply(y, n)
					// the multiple of n each dividend contains, and the two gaps
					multX, multY := v.Mul.Apply(quotX, n), v.Mul.Apply(quotY, n)
					multGap := v.Sub.Apply(multX, multY)
					quotGap := v.Sub.Apply(quotX, quotY)

					gap := b.Have(
						"subtract the two division identities: the remainders cancel and n factors out of what is left",
						"x - y = n * (div(x, n) - div(y, n))",
						By(
							sameRem,
							At(int_div_rem.DivisionIdentity, x, n), // int_div(x, n) * n + int_rem(x, n) = x
							At(int_div_rem.DivisionIdentity, y, n), // int_div(y, n) * n + int_rem(y, n) = y
							// regroup the difference so that the two remainders meet:
							// (multX + int_rem(x, n)) - (multY + int_rem(y, n)) = multGap + (int_rem(x, n) - int_rem(y, n))
							At(int_real_lift.SubAddPairwise, multX, remX, multY, remY),
							At(int_real_lift.SubRefl, remY),                    // int_rem(y, n) - int_rem(y, n) = &0
							At(int_real_lift.AddRightIdentity, multGap),        // multGap + &0 = multGap
							At(int_real_lift.SubRightDistrib, quotX, quotY, n), // quotGap * n = multGap
							// and quotGap * n = n * quotGap, the claim's right side
							At(int_real_lift.MulSym, quotGap, n)))

					b.Show(
						"a difference that is n times something is a congruence mod n",
						By(Normalized, gap, At(CongruentIffMultiple, x, y, n)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// ℕ's congruence, read in ℤ
// ---------------------------------------------------------------------------
//
// ℕ has its own congruence, defined inside ℕ as equality of remainders
// (nat_num/nat_congruence), and the embedding carries it to this chapter's
// relation. The clause belongs to the sentence "& is an embedding of
// ordered semirings" that int_embed states operation by operation; it
// sits here rather than at the boundary for the reason the remainder's
// transport sits in int_div_rem — the ℤ side of the clause is this
// chapter's own characterization, and the boundary chapter is below.

// OfNumCongruent — two naturals are congruent exactly when their images
// are, at the image of the modulus. Nothing about ℕ is proved: the ℕ
// relation is an equality of remainders by definition and the ℤ one by
// CongruentIffSameRem, the remainder's transport puts the two equations
// on one side of `&`, and injectivity reads the ℤ equation back as the
// ℕ one — which is why the last step matters as much as the first.
var OfNumCongruent = ofNumCongruentThm{family.Add(registry.ProofEntry{
	Name: "OfNumCongruent",
	Key:  "prop_2a06d07803c77996",
	Build: family.Theorem("∀x y n:num. x ≡ y (mod n) ⇔ &x ≡ &y (mod &n)",
		func(a *Argument, x, y, n Term) {
			v := ops(a.Ctx())

			a.Do(
				// ↦ nat_mod(x₀, n₀) = nat_mod(y₀, n₀) ⇔ &x₀ ≡ &y₀ (mod &n₀)
				Unfold(nat_congruence.CongDef),
				// &x₀ ≡ &y₀ (mod &n₀) ⇔ int_rem(&x₀, &n₀) = int_rem(&y₀, &n₀)
				Cite(CongruentIffSameRem, v.IntOfNum.Apply(x), v.IntOfNum.Apply(y), v.IntOfNum.Apply(n)),
				// each ℕ remainder's image, at both ends: &(nat_mod(x₀, n₀)) =
				// int_rem(&x₀, &n₀), and the same at y₀
				Cite(int_div_rem.OfNumRem, x, n),
				Cite(int_div_rem.OfNumRem, y, n),
				// leaving &(nat_mod(x₀, n₀)) = &(nat_mod(y₀, n₀)) against a goal that
				// says nat_mod(x₀, n₀) = nat_mod(y₀, n₀) — injectivity is exactly that
				// gap. Bare because the statement is over free variables and
				// has no binder slots to ground.
				Cite(int_embed.OfNumEq),
			)
		}),
})}

// ---------------------------------------------------------------------------
// What may be replaced inside a congruence
// ---------------------------------------------------------------------------
//
// A congruence does not see the difference between an argument and its
// remainder, so either side may be reduced before anything else happens.
//
// The three members are that one permission: stated bare, then as a
// replacement in the left argument and in the right. All three make the
// same two moves — read every congruence in sight as an equality of
// remainders, then let the reduction that appears twice collapse into
// the one that appears once — so the godocs below say only what is
// particular to each. Both facts they cite hold at every modulus, `&0`
// included, so nothing here is guarded and nothing splits.

// RemCongruent is the permission in its bare form: what the division
// leaves over may stand in for the dividend it came from. It is the one
// member with a single congruence to read, so the claim reduces to
// nothing more than "reducing twice is reducing once" — no multiple of
// the modulus is ever produced, and the quotient never appears.
var RemCongruent = remCongruentThm{family.Add(registry.ProofEntry{
	Name: "RemCongruent",
	Key:  "prop_957452a4dbefa5fa",
	Build: family.Theorem("∀m n:int. rem(m, n) ≡ m (mod n)",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())

			a.Show(
				"a remainder is congruent to what it came from",
				By(
					// int_rem(m, n) ≡ m (mod n) ⇔ int_rem(int_rem(m, n), n) = int_rem(m, n)
					At(CongruentIffSameRem, v.IntRem.Apply(m, n), m, n),
					// which is that right side
					int_div_rem.RemRem))
		}),
})}

// RemLeft replaces the left argument by its remainder. The two readings
// differ in one place only — on the left `x` has been reduced twice —
// so collapsing that second reduction identifies them outright, and
// nothing need be assumed about `x`, `y` or the modulus.
var RemLeft = remLeftThm{family.Add(registry.ProofEntry{
	Name: "RemLeft",
	Key:  "prop_85bdca1bf77debe6",
	Build: family.Theorem("∀x y n:int. rem(x, n) ≡ y (mod n) ⇔ x ≡ y (mod n)",
		func(a *Argument, x, y, n Term) {
			v := ops(a.Ctx())

			a.Show(
				"the doubled reduction of x is the only difference between the two readings",
				By(
					// int_rem(x, n) ≡ y (mod n) ⇔ int_rem(int_rem(x, n), n) = int_rem(y, n)
					At(CongruentIffSameRem, v.IntRem.Apply(x, n), y, n),
					// x ≡ y (mod n) ⇔ int_rem(x, n) = int_rem(y, n)
					At(CongruentIffSameRem, x, y, n),
					// the two right sides are one equation
					int_div_rem.RemRem))
		}),
})}

// RemRight is the same permission at the other argument, and it is named
// for the slot that varies: the argument being replaced is the right one.
// Its proof is not RemLeft's with the letters exchanged — the unreduced
// reading is cited unchanged, and only the reduction and the collapse
// move to the other side.
var RemRight = remRightThm{family.Add(registry.ProofEntry{
	Name: "RemRight",
	Key:  "prop_752137d16294dd5d",
	Build: family.Theorem("∀x y n:int. x ≡ rem(y, n) (mod n) ⇔ x ≡ y (mod n)",
		func(a *Argument, x, y, n Term) {
			v := ops(a.Ctx())

			a.Show(
				"y this time carries the reduction that has to collapse",
				By(
					// x ≡ int_rem(y, n) (mod n) ⇔ int_rem(x, n) = int_rem(int_rem(y, n), n)
					At(CongruentIffSameRem, x, v.IntRem.Apply(y, n), n),
					// x ≡ y (mod n) ⇔ int_rem(x, n) = int_rem(y, n)
					At(CongruentIffSameRem, x, y, n),
					// the two right sides are one equation
					int_div_rem.RemRem))
		}),
})}

// ---------------------------------------------------------------------------
// What a congruence buys for computing a remainder: it may be taken EARLY
// ---------------------------------------------------------------------------
//
// Each operand may be replaced by the remainder it leaves BEFORE the
// operation is performed rather than after, so no intermediate result ever
// has to grow past the modulus — which is what makes modular arithmetic
// computable.
//
// The permission does not come from anything about division. It is read
// off congruence alone: an argument and the remainder it leaves are
// congruent, congruent quantities may be combined, and congruent
// quantities leave the same remainder. Three of the four members below
// are exactly that reading and nothing else, one per ring operation;
// they differ only in which compatibility law the first step spends.
//
// The fourth is the exception. Its second operand is a count rather
// than an integer the relation relates, so there is no compatibility
// law of that shape for it to spend; it spends the multiplicative one a
// variable number of times instead, and says so at its own entry.

// RemOfSum. Each operand is congruent to the remainder it leaves, and
// congruences add, so the two sums are congruent — and congruent
// quantities leave the same remainder, which is the equation asked for.
//
// `RemCongruent` states its congruence with the remainder on the LEFT,
// and the instance wanted here needs it on the right. `CongruentIffSameRem`
// supplies the reversal: read in either direction a congruence is the
// one equality of remainders, and equality is symmetric. That is its
// first job here; turning the finished congruence back into an equation
// is its second.
var RemOfSum = remOfSumThm{family.Add(registry.ProofEntry{
	Name: "RemOfSum",
	Key:  "prop_740f7df1a924ee68",
	Build: family.Theorem("∀x y n:int. rem(x + y, n) = rem(rem(x, n) + rem(y, n), n)",
		func(a *Argument, x, y, n Term) {
			v := ops(a.Ctx())
			remX, remY := v.IntRem.Apply(x, n), v.IntRem.Apply(y, n)

			congruent := a.Have(
				"each operand is congruent to the remainder it leaves, and congruences add",
				"x + y ≡ rem(x, n) + rem(y, n) (mod n)",
				By(
					// x ≡ int_rem(x, n) ⇒ y ≡ int_rem(y, n) ⇒ x + y ≡ int_rem(x, n) + int_rem(y, n)
					At(AddCongruent, x, remX, y, remY, n),
					// both antecedents, one per operand — cited bare because
					// the same fact is wanted at two arguments
					RemCongruent,
					// and read the other way round, which is where the
					// remainder has to stand in these two antecedents
					CongruentIffSameRem))

			// The law is read at the two sums: under the canonical binder order
			// the bare cite does not find this instance by search.
			a.Show(
				"congruent quantities leave the same remainder, which is the claim",
				By(congruent, At(CongruentIffSameRem, a.Term("x + y"), a.Term("rem(x, n) + rem(y, n)"), n)))
		}),
})}

// RemOfProduct is RemOfSum with the multiplicative compatibility entry
// in place of the additive one, and is otherwise the same three
// premises in the same two steps. That it costs no more than the sum is
// worth saying, because the two compatibility entries are not alike —
// one of them has to build its multiple of the modulus where the other
// only regroups. All of that extra work is spent inside the entry, and
// none of it surfaces here.
var RemOfProduct = remOfProductThm{family.Add(registry.ProofEntry{
	Name: "RemOfProduct",
	Key:  "prop_3119ce6056bbc12d",
	Build: family.Theorem("∀x y n:int. rem(x * y, n) = rem(rem(x, n) * rem(y, n), n)",
		func(a *Argument, x, y, n Term) {
			v := ops(a.Ctx())
			remX, remY := v.IntRem.Apply(x, n), v.IntRem.Apply(y, n)

			congruent := a.Have(
				"each factor is congruent to the remainder it leaves, and congruences multiply",
				"x * y ≡ rem(x, n) * rem(y, n) (mod n)",
				By(
					// x ≡ int_rem(x, n) ⇒ y ≡ int_rem(y, n) ⇒ x * y ≡ int_rem(x, n) * int_rem(y, n)
					At(MulCongruent, x, remX, y, remY, n),
					RemCongruent,
					CongruentIffSameRem))

			// The law is read at the two terms: under the canonical binder order
			// the bare cite does not find this instance by search.
			a.Show(
				"congruent quantities leave the same remainder, which is the claim",
				By(congruent, At(CongruentIffSameRem, a.Term("x * y"), a.Term("rem(x, n) * rem(y, n)"), n)))
		}),
})}

// RemOfDifference is the third member to read the same sentence, and it
// differs from the two above it only in the compatibility entry its
// first step cites. No property of subtraction is used anywhere below:
// which operation is being reduced early is settled entirely by that one
// citation.
var RemOfDifference = remOfDifferenceThm{family.Add(registry.ProofEntry{
	Name: "RemOfDifference",
	Key:  "prop_43bac56c613943d2",
	Build: family.Theorem("∀x y n:int. rem(x - y, n) = rem(rem(x, n) - rem(y, n), n)",
		func(a *Argument, x, y, n Term) {
			v := ops(a.Ctx())
			remX, remY := v.IntRem.Apply(x, n), v.IntRem.Apply(y, n)

			congruent := a.Have(
				"each operand is congruent to the remainder it leaves, and congruences subtract",
				"x - y ≡ rem(x, n) - rem(y, n) (mod n)",
				By(
					// x ≡ int_rem(x, n) ⇒ y ≡ int_rem(y, n) ⇒ x - y ≡ int_rem(x, n) - int_rem(y, n)
					At(SubCongruent, x, remX, y, remY, n),
					RemCongruent,
					CongruentIffSameRem))

			// The law is read at the two terms: under the canonical binder order
			// the bare cite does not find this instance by search.
			a.Show(
				"congruent quantities leave the same remainder, which is the claim",
				By(congruent, At(CongruentIffSameRem, a.Term("x - y"), a.Term("rem(x, n) - rem(y, n)"), n)))
		}),
})}

// RemOfPower is RemOfProduct iterated. An exponent counts factors, so
// the permission to reduce a factor before multiplying is granted once
// per factor, and an induction on the exponent is the whole argument:
// the power's own recursion peels one factor off, the product law
// reduces that factor and the tail separately, and the induction
// hypothesis identifies the two tails.
//
// The step meets an asymmetry the binary members never do. On the right
// the base is a remainder already, so reducing it a second time changes
// nothing — and saying that is the one premise below which is neither
// the recursion, nor the product law, nor the hypothesis.
//
// No congruence is stated anywhere in this proof. Each of the three
// members above passes through one; here the product law has already
// done so, and what gets iterated is the equation it left behind.
var RemOfPower = remOfPowerThm{family.Add(registry.ProofEntry{
	Name: "RemOfPower",
	Key:  "prop_f3e6c73678931c0e",
	Build: family.Theorem("∀k:num. ∀x n:int. rem(int_pow(x, k), n) = rem(int_pow(rem(x, n), k), n)",
		func(a *Argument) {
			v := ops(a.Ctx())
			// The exponent is left bound — it is what the induction runs
			// on — and the two integers are fixed inside each branch.
			k := a.Binder("k")

			a.Induct(k)
			a.Base(
				"no factors at all, and the empty product is &1 however it was taken",
				func(b *Argument) {
					x := b.Fix()
					n := b.Fix()
					zero := b.Ctx().Numeral(0)

					// `int_pow.PowClauses` is a merged pack — a zero clause
					// and a successor clause — and only the zero clause is wanted
					// here, so the exponent slot is idle and any term fills it.
					// `Normalized` is needed on this branch and not on the step
					// because once the clause has fired the two sides are the same
					// term, and folding them together is what it does.
					b.Show(
						"both sides are the remainder of &1, so nothing separates them",
						By(Normalized, At(int_pow.PowClauses, x, zero), At(int_pow.PowClauses, v.IntRem.Apply(x, n), zero)))
				})
			a.Step(
				"one more factor of the base multiplies each side",
				func(b *Argument, tails Fact) {
					x := b.Fix()
					n := b.Fix()
					// the right side's base, which is a remainder already
					remX := v.IntRem.Apply(x, n)
					// and the two tails the hypothesis relates
					powX, powRem := v.Pow.Apply(x, k), v.Pow.Apply(remX, k)

					b.Show(
						"reduce the new factor and the tail separately on both sides: the tails "+
							"are the hypothesis, and the two new factors leave the same remainder",
						By(
							// int_rem(int_pow(x, k), n) = int_rem(int_pow(int_rem(x, n), k), n)
							tails.At(x, n),
							// x * int_pow(x, k) = int_pow(x, suc(k)), and the
							// same recursion over the reduced base
							At(int_pow.PowClauses, x, k),
							At(int_pow.PowClauses, remX, k),
							// each product's remainder, taken factor by factor
							At(RemOfProduct, x, powX, n),
							At(RemOfProduct, remX, powRem, n),
							// which on the right asks for the base a second time
							int_div_rem.RemRem))
				})
		}),
})}

// ---------------------------------------------------------------------------
// What congruences may be combined by
// ---------------------------------------------------------------------------
//
// A congruence is not merely an equivalence relation: it is a RING
// congruence, so congruent quantities may be added, subtracted and
// multiplied and stay congruent. That is what lets `x ≡ y (mod n)` be
// handled like an equation, and it is what every later statement about the
// remainder of a sum, a difference or a product rests on.
//
// None of the three can be read off the ℤ theory this chapter builds
// over, which states none of them, so all three are proved here. All
// three open the same way — read every congruence in sight as the
// multiple of the modulus it exhibits — and past that opening they part
// company, on differences that are mathematical rather than stylistic.
//
// What separates them is how the multiple the goal wants is reached
// from the two it is given. The sum regroups its way to it and never has
// to name either. The difference reaches the same regrouping, but only
// after moving each of its differences across an equation, and that
// detour spells them out. The product cannot regroup at all: its
// multiple involves the surviving factors as well, so it is built rather
// than found. Each member's own comment says which.
//
// The product law then iterates: factors congruent one by one give
// congruent finite products, the fold at ℤ's multiplication inheriting the
// relation its operation respects.

// AddCongruent — congruences add. Exported: with its two siblings it is
// the chapter's statement that congruence is a ring congruence, and that
// is chapter API. Nothing is constructed here. The two
// premises put x and u each a multiple of n away from y and v, and
// regrouping the difference of the two sums stands those two multiples
// side by side, where the modulus comes out of both at once. The
// multiple the goal asks for is that sum: it is forced, not chosen, so
// the proof is one premise list and the distributive law it ends on is
// the only cite that does not need to say where it applies.
var AddCongruent = addCongruentThm{family.Add(registry.ProofEntry{
	Name: "AddCongruent",
	Key:  "prop_7ab94315f16fa95",
	Build: family.Theorem(Statement{
		Binders: "∀x y u v n:int.",
		Hypotheses: []string{
			"x ≡ y (mod n)",
			"u ≡ v (mod n)",
		},
		Conclusion: "x + u ≡ y + v (mod n)",
	},
		func(a *Argument, x, y, u, v, n Term, congXY, congUV Fact) {
			op := ops(a.Ctx())

			a.Show(
				"the two gaps regroup into the gap between the sums, and the modulus comes out of them together",
				By(
					congXY,
					congUV,
					// the three congruences as the multiples they exhibit —
					// two given, one wanted
					At(CongruentIffMultiple, x, y, n),
					At(CongruentIffMultiple, u, v, n),
					At(CongruentIffMultiple, op.Add.Apply(x, u), op.Add.Apply(y, v), n),
					// (x + u) - (y + v) = (x - y) + (u - v), which is where
					// the two given multiples meet
					At(int_real_lift.SubAddPairwise, x, u, y, v),
					// and n comes out of their sum. Cited bare: its instance
					// is at the two multiples, which this proof never names.
					int_real_lift.LeftDistrib))
		}),
})}

// SubCongruent — congruences subtract. Exported for AddCongruent's
// reason. The multiple the goal asks for is the difference of the two it
// is given, exactly as the sum's is their sum, but it is not reached the
// same way. The regrouping the sum uses takes a DIFFERENCE OF SUMS
// apart, which is what the additive goal already is, while the
// subtractive goal is a difference of differences. So each of the three
// differences is first moved across an equation and becomes a sum, and
// only then does that same regrouping stand the two multiples side by
// side.
//
// The detour is what forces both given multiples to be named: every
// instance below is spelled at one of them, where the sum's proof names
// neither.
var SubCongruent = subCongruentThm{family.Add(registry.ProofEntry{
	Name: "SubCongruent",
	Key:  "prop_416b077184ca2277",
	Build: family.Theorem(Statement{
		Binders: "∀x y u v n:int.",
		Hypotheses: []string{
			"x ≡ y (mod n)",
			"u ≡ v (mod n)",
		},
		Conclusion: "x - u ≡ y - v (mod n)",
	},
		func(a *Argument, x, y, u, v, n Term, congXY, congUV Fact) {
			op := ops(a.Ctx())

			e, gapXY := a.Obtain(
				"the first congruence hands over the multiple separating x from y",
				"∃e:int. x - y = n * e",
				By(congXY, CongruentIffMultiple))

			f, gapUV := a.Obtain(
				"and the second the one separating u from v",
				"∃f:int. u - v = n * f",
				By(congUV, CongruentIffMultiple))

			// the multiples the two given congruences exhibit, and the one the
			// goal asks for
			multXY, multUV := op.Mul.Apply(n, e), op.Mul.Apply(n, f)
			multWanted := op.Mul.Apply(n, op.Sub.Apply(e, f))
			// and the two differences it is asked to stand between
			diffXU, diffYV := op.Sub.Apply(x, u), op.Sub.Apply(y, v)

			a.Show(
				"read all three differences as sums: subtracting the first two stands "+
					"n·e₀ and n·f₀ apart from y - v, and n comes out of them together",
				// Each of the three differences has been turned into a sum by
				// its own equation, and after those rewrites the two sides are
				// the same term.
				By(
					gapXY,
					gapUV,
					// x - y = n·e₀ ⇔ x = n·e₀ + y, and the same for u
					At(int_real_lift.EqSubRightAdd, x, y, multXY),
					At(int_real_lift.EqSubRightAdd, u, v, multUV),
					// and on what is to be shown: (x - u) - (y - v) = n·(e₀ - f₀)
					// ⇔ x - u = n·(e₀ - f₀) + (y - v)
					At(int_real_lift.EqSubRightAdd, diffXU, diffYV, multWanted),
					// (n·e₀ + y) - (n·f₀ + v) = (n·e₀ - n·f₀) + (y - v): the two
					// multiples meet, and what is left beside them is exactly the
					// pair standing on the other side
					At(int_real_lift.SubAddPairwise, multXY, y, multUV, v),
					// n·(e₀ - f₀) = n·e₀ - n·f₀, which is that difference of
					// multiples with n outside it
					At(int_real_lift.SubLeftDistrib, n, e, f),
					// and a difference that is n times something is a congruence
					At(CongruentIffMultiple, diffXU, diffYV, n)))
		}),
})}

// MulCongruent — congruences multiply. Exported for AddCongruent's
// reason. The two factors are replaced one
// at a time, and that is the whole idea: moving x down to y with u
// standing changes the product by (x - y)·u, then moving u down to v
// with y standing changes it by y·(u - v). Each change is visibly a
// multiple of n, the two are consecutive, and consecutive differences
// telescope — so the gap between the original product and the final one
// is their sum, and the modulus comes out of that.
//
// Both given multiples must be named for this, since the one the goal
// asks for is a combination of them and of the two surviving factors —
// there is nothing to regroup one's way to. Naming them is also what
// makes each single-factor move visible as a multiple, which is the
// step the telescoping then adds up.
var MulCongruent = mulCongruentThm{family.Add(registry.ProofEntry{
	Name: "MulCongruent",
	Key:  "prop_f381c8e9396b6d9f",
	Build: family.Theorem(Statement{
		Binders: "∀x y u v n:int.",
		Hypotheses: []string{
			"x ≡ y (mod n)",
			"u ≡ v (mod n)",
		},
		Conclusion: "x * u ≡ y * v (mod n)",
	},
		func(a *Argument, x, y, u, v, n Term, congXY, congUV Fact) {
			op := ops(a.Ctx())
			// the three products the telescope runs through
			xu, yu, yv := op.Mul.Apply(x, u), op.Mul.Apply(y, u), op.Mul.Apply(y, v)

			e, gapXY := a.Obtain(
				"the first congruence hands over the multiple separating x from y",
				"∃e:int. x - y = n * e",
				By(congXY, CongruentIffMultiple))

			f, gapUV := a.Obtain(
				"and the second the one separating u from v",
				"∃f:int. u - v = n * f",
				By(congUV, CongruentIffMultiple))

			moveX := a.Have(
				"hold u and move x down to y: the product changes by (x - y)·u, so by n·(e·u)",
				"x * u - y * u = n * (e * u)",
				By(
					gapXY,
					// ↦ the claim's left side becomes (x - y)·u, where the
					// given multiple can be substituted. Bare: the cite
					// rewrites the goal rather than joining the premises.
					int_real_lift.SubRightDistrib,
					// n·(e₀·u) = (n·e₀)·u — the substituted multiple, with n
					// moved to the outside
					At(int_real_lift.MulAssoc, n, e, u)))

			moveU := a.Have(
				"now hold y and move u down to v: it changes by y·(u - v), so by n·(f·y)",
				"y * u - y * v = n * (f * y)",
				By(
					gapUV,
					// ↦ the claim's left side becomes y·(u - v)
					int_real_lift.SubLeftDistrib,
					// this time the multiple lands on the inside — y·(n·f₀) =
					// (n·f₀)·y — and only then does n reach the outside
					At(int_real_lift.MulSym, y, op.Mul.Apply(n, f)),
					At(int_real_lift.MulAssoc, n, f, y)))

			a.Show(
				"the two moves are consecutive, so together they carry x·u to y·v by a single multiple of n",
				By(
					moveX,
					moveU,
					// (x·u - y·u) + (y·u - y·v) = x·u - y·v: the telescope
					At(int_real_lift.SubTriangle, xu, yu, yv),
					// n·(e₀·u + f₀·y) = n·(e₀·u) + n·(f₀·y): the multiple wanted
					At(int_real_lift.LeftDistrib, n, op.Mul.Apply(e, u), op.Mul.Apply(f, y)),
					// and a difference that is n times something is a congruence
					At(CongruentIffMultiple, xu, yv, n)))
		}),
})}

// ProductCongruent — factors congruent mod n give congruent products: a
// congruence mod n respects multiplication and relates 1 to itself, and a
// relation the operation respects is inherited by the fold.
var ProductCongruent = productCongruentThm{family.Add(registry.ProofEntry{
	Name: "ProductCongruent",
	Key:  "prop_9d24a2ff3a6dba66",
	Build: family.Theorem(Statement{
		Binders: "∀n:int. ∀f g:(A → int). ∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ f(x) ≡ g(x) (mod n)",
		},
		Conclusion: "Π_{x∈s} f(x) ≡ Π_{x∈s} g(x) (mod n)",
	}, func(a *Argument, n *Expr[Int], f, g *Arrow[A, Int], s *Expr[Set[A]], finite, agree Fact) {
		a.Do(Unfold(int_product.IntProductDef))
		a.Show(
			"congruence mod n survives multiplication, so it passes through the fold",
			By(
				finite,
				agree,
				int_real_lift.MonoidalMul,
				MulCongruent,
				CongruentIffSameRem,
				Where(monoidal.Related, "R", a.Term("λu:int. λv:int. u ≡ v (mod n)"))))
	}),
})}

// ---------------------------------------------------------------------------
// Naming one integer out of a congruence class
// ---------------------------------------------------------------------------
//
// A class is infinite, so computing with congruences means naming a
// member of one. What makes a name possible is that a class is spread
// thin: any two of its members differ by a whole multiple of the
// modulus. So a stretch of integers narrower than the modulus holds at
// most one member of a class, and dividing by the modulus hands out a
// stretch that holds at least one.
//
// Existence is settled by dividing, and the representative it exhibits
// is the remainder — nothing is searched for, because the division has
// already produced an integer with the properties asked for.
// Uniqueness is the at-most-one half: congruent integers closer
// together than the modulus are the same integer; so two sign values,
// −1, 0 or 1, congruent modulo an odd prime are equal. At a positive
// modulus the two compose, and "the residue" becomes something that
// may be spoken of rather than merely sought.
//
// The last two members are about that name. One takes it in ℕ: where
// the class has a nonnegative member at all — which is what that
// member's guard asks for — the representative may be taken to be an
// embedded natural. The other says which integer the name picks out.
// Lying in the stretch and being congruent to the dividend is not
// merely something the remainder does; it is what makes an integer the
// remainder, so the remainder IS the residue rather than one choice of
// it.

// ResidueInRange is the at-least-one half, and it is settled by the
// division algorithm alone. Both bounds asked for are the algorithm's
// own bounds on its remainder, and the congruence asked for is what
// this chapter's reduction law says about any remainder whatever — so
// the witness is the remainder and there is nothing else to check.
//
// The modulus has to be nonzero, and the reason is visible in the
// statement rather than in the proof: at &0 the stretch a
// representative is asked to fall in is empty, so no integer could
// answer.
var ResidueInRange = residueInRangeThm{family.Add(registry.ProofEntry{
	Name: "ResidueInRange",
	Key:  "prop_bbf4d53612a7e4e8",
	Build: family.Theorem(Statement{
		Binders: "∀a n:int.",
		Hypotheses: []string{
			"n ≠ &0",
		},
		Conclusion: "∃x:int. &0 ≤ x ∧ x < |n| ∧ x ≡ a (mod n)",
	},
		func(arg *Argument, a, n Term, nonZero Fact) {
			v := ops(arg.Ctx())

			// The representative is what dividing a by n leaves over.
			arg.Take(v.IntRem.Apply(a, n))

			arg.Show(
				"dividing a by n has already produced all three conditions",
				By(
					nonZero,
					// n ≠ &0 ⇒ … ∧ &0 ≤ int_rem(a, n) ∧ int_rem(a, n) < int_abs(n),
					// which is the pair of bounds
					At(int_div_rem.DivisionAlgorithm, a, n),
					// which is the congruence
					RemCongruent))
		}),
})}

// NaturalRepresentative takes the representative in ℕ. Its guard is
// what asks the class to meet the nonnegatives at all: away from &0
// every class does, and at &0 the class is the single integer x, so
// there the guard is the whole question. Under it the remainder is
// nonnegative, and a nonnegative integer is the image of a natural —
// so the remainder, which is a class member at every modulus, is
// named by the natural the embedding carries it back from.
//
// The guard is never split on, and the reason is that
// `int_div_rem.RemNonnegIff` has already absorbed the split: it states
// the nonnegativity of a remainder as equivalent to exactly this
// guard. So the hypothesis converts straight into the form the
// embedding has to be inverted under, and the zero modulus — the only
// place the guard bites — needs no case of its own.
var NaturalRepresentative = naturalRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "NaturalRepresentative",
	Key:  "prop_b450274d340b38e8",
	Build: family.Theorem(Statement{
		Binders: "∀x n:int.",
		Hypotheses: []string{
			"n = &0 ⇒ &0 ≤ x",
		},
		Conclusion: "∃k:num. &k ≡ x (mod n)",
	},
		func(a *Argument, x, n Term, meetsNonnegatives Fact) {
			v := ops(a.Ctx())
			residue := v.IntRem.Apply(x, n)

			// The natural exhibited is the one dividing x by n leaves over,
			// read back across the embedding.
			a.Take(v.NumOfInt.Apply(residue))

			a.Show(
				"the remainder is nonnegative under exactly this guard, so the "+
					"embedding recovers it, and it was congruent to x to begin with",
				By(
					meetsNonnegatives,
					// &0 ≤ int_rem(x, n) ⇔ n = &0 ⇒ &0 ≤ x, whose right side is
					// the guard on the nose
					At(int_div_rem.RemNonnegIff, x, n),
					// &0 ≤ int_rem(x, n) ⇒ &(num_of_int(int_rem(x, n))) = int_rem(x, n),
					// which turns the exhibited natural back into the remainder
					At(int_embed.NumOfIntSection, residue),
					// the congruence asked for
					RemCongruent))
		}),
})}

// EqOfSmallDifference is the at-most-one half: integers congruent
// modulo n and less than n apart do not differ at all. It rests on a
// size bound for divisors — what divides a quantity is no larger than
// that quantity, unless the quantity is &0. The modulus divides the
// gap here, and the gap is too small for that bound to hold, so the
// escape clause is the only way out and the gap is &0.
//
// That bound is stated about `∣`, which neither `CongruentIffMultiple`
// nor `CongruentIffSameRem` produces. So the first step goes back past
// both of them to the definition, which is a divisibility statement
// and nothing else.
var EqOfSmallDifference = eqOfSmallDifferenceThm{family.Add(registry.ProofEntry{
	Name: "EqOfSmallDifference",
	Key:  "prop_a94a1ace74a6b010",
	Build: family.Theorem(Statement{
		Binders: "∀x y n:int.",
		Hypotheses: []string{
			"|x - y| < n",
			"x ≡ y (mod n)",
		},
		Conclusion: "x = y",
	},
		func(a *Argument, x, y, n Term, congruentAndClose Fact) {
			v := ops(a.Ctx())
			gap := v.Sub.Apply(x, y)
			absGap, absN := v.Abs.Apply(gap), v.Abs.Apply(n)

			divides := a.Have(
				"unfold the congruence to the divisibility it is defined to be",
				"n ∣ (x - y)",
				// The congruence is divisibility of the difference, so
				// the unfolding leaves the assumption saying the claim.
				Unfold(IntCongDef))

			// The gap is a multiple of n and smaller than n, so it has
			// nowhere to be but &0. Splitting on that is what makes the
			// second branch's impossibility a checked step rather than a
			// remark.
			a.Cases(gap.Eq(v.Zero))
			a.When(
				"the gap vanishes, which is what it means for the two to be equal",
				func(b *Argument, vanishes Fact) {
					b.Show(
						"nothing separates them",
						By(vanishes, int_real_lift.SubEqZero))
				})
			a.Otherwise(
				"a nonzero gap would have to be at least as big as n, and it is smaller",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"so this branch is empty",
						By(
							congruentAndClose,
							divides,
							nonzero,
							// a divisor is no larger than what it divides,
							// once what it divides is not &0
							At(int_divides.DivisorBoundedByDividend, n, gap),
							// int_abs(n) ≤ int_abs(x - y) < n
							At(int_real_lift.LessEqLessThanTrans, absN, absGap, n),
							// which no integer admits, its size never being
							// smaller than itself
							At(int_real_lift.AbsDominates, n),
							At(int_real_lift.NotLessThan, absN, n)))
				})
		}),
})}

// EqOfCongruentSigns — two sign values, integers between −1 and 1, that
// are congruent modulo an odd prime p are equal: they differ by at most 2,
// which is less than p, and congruent integers closer together than the
// modulus are equal.
var EqOfCongruentSigns = eqOfCongruentSignsThm{family.Add(registry.ProofEntry{
	Name: "EqOfCongruentSigns",
	Key:  "prop_f3b38a7659951ff1",
	Build: family.Theorem(Statement{
		Binders: "∀p:num. ∀u v:int.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"-&1 ≤ u",
			"u ≤ &1",
			"-&1 ≤ v",
			"v ≤ &1",
			"u ≡ v (mod &p)",
		},
		Conclusion: "u = v",
	}, func(
		arg *Argument,
		p *Expr[Nat],
		u, v *Expr[Int],
		prime, odd, uLow, uHigh, vLow, vHigh, congruent Fact,
	) {
		modulus := arg.TermAs[Int]("&p")
		three := arg.Have(
			"an odd prime is at least 3",
			"3 ≤ p",
			ByArith(prime, odd, nat_prime.PrimeAtLeastTwo.At(p)))
		arg.Show(
			"u and v differ by at most 2 < p, and congruent integers that close are equal",
			ByArith(
				three,
				uLow,
				uHigh,
				vLow,
				vHigh,
				congruent,
				int_real_lift.AbsBetween.At(v, u, modulus),
				EqOfSmallDifference.At(u, v, modulus)))
	}),
})}

// RemCharacterization names the residue by property rather than by
// construction: an integer congruent to the dividend and lying in the
// stretch has nowhere else to be, so it is what the division leaves
// over. Existence above already exhibits the remainder; what is added
// here is that nothing else answers.
//
// At the zero modulus the stretch is empty and nothing could lie in
// it, which is why the condition has a second branch at all. What
// opens there is the convention the division constants were fixed
// under, that the whole dividend is left over.
//
// Both directions run on the same four facts, so there are no arms to
// separate. A congruence is an equality of remainders; an integer is
// its own remainder exactly under that same condition; and a remainder
// is its own remainder, which is what puts it there.
var RemCharacterization = remCharacterizationThm{family.Add(registry.ProofEntry{
	Name: "RemCharacterization",
	Key:  "prop_440a4eb87dc7bdc2",
	Build: family.Theorem(
		"∀m n p:int. rem(m, n) = p ⇔ ((n = &0 ∧ m = p) ∨ (&0 ≤ p ∧ p < |n|)) ∧ m ≡ p (mod n)",
		func(a *Argument, m, n, p Term) {
			// Every fact here is an equation between remainders, so the
			// claim is those equations composed.
			a.Show(
				"read as remainders: the congruence equates the two, and the condition "+
					"says p is already its own — so each side of the claim is the other",
				By(
					// m ≡ p (mod n) ⇔ int_rem(m, n) = int_rem(p, n)
					At(CongruentIffSameRem, m, p, n),
					// int_rem(p, n) = p ⇔ n = &0 ∨ (&0 ≤ p ∧ p < int_abs(n)),
					// which is the condition, the degenerate branch included
					At(int_div_rem.RemEqSelf, p, n),
					// int_rem(m, &0) = m: at the zero modulus that branch also
					// carries m = p, and this is what makes the two agree
					At(int_div_rem.RemByZero, m),
					// int_rem(int_rem(m, n), n) = int_rem(m, n): the remainder satisfies
					// the condition, which is what the ⇒ direction needs
					At(int_div_rem.RemRem, m, n)))
		}),
})}
