// closure.go — the class of polynomial functions and what it is closed
// under. A real function is polynomial when some finite coefficient
// list sums to it, `p x = Σ_{i∈0..m} cᵢ·xⁱ`. The generators exhibit
// such a list outright, the linear laws build one out of the lists
// for their parts, and the rest are inductions — on the degree,
// through the peel that reads a coefficient sum as its constant term
// plus x times a shorter sum; on the exponent; on the index set.
//
// Three conventions the file lives by. A close that decides a guard
// or a COND, or reads a resident equation at the goal's own point, is
// a leaf the normalizer decides, so no refutation is wanted; it carries
// `Normalized` where the bare spelling would still reach the refuter,
// with no per-site prose either way. `Simp(Fwd(law))` fires the law as its statement writes it and
// `Simp(Rev(law))` the other way; the `↦` gloss beside each such
// site is the goal it leaves. And an opened polynomial's degree
// and list keep their statement names, `m` and `c`, unless the proof
// already declares those names elsewhere — a lemma's binders, an
// earlier opened polynomial — in which case they are the next mints,
// `m₀` and `c₀`, and the claims spell whichever the page has.

package real_polynomial

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The generators
// ---------------------------------------------------------------------------
//
// A constant and the identity are polynomial, and the proof of each is
// the same move: open the definition, name the degree and the
// coefficient list, and compute the sum. Unfolding
// `polynomial_function(f)` leaves
//
//	∃m c. ∀x. f(x) = real_sum(0 .. m, λi. c(i) * real_pow(x, i))
//
// with f's body in place of f(x); the two `Take`s supply m and c, and
// the point x is then fixed. The lists are as short as they can be —
// one coefficient for a constant, two for the identity — so the sum
// computes by reading the interval calculus at its shortest intervals:
// a point, and a point with its successor.

// Const — a constant function is polynomial.
var Const = constThm{family.Add(registry.ProofEntry{
	Name: "Const",
	Key:  "prop_a72888f423912836",
	Build: family.Theorem("∀c:real. polynomial_function(λx:real. c)",
		func(a *Argument, c *Expr[Real]) {
			a.Do(Unfold(PolynomialFunctionDef))
			// Degree 0, and the one coefficient is c.
			a.Take(a.Term("0"))
			a.Take(a.Term("λi:num. c"))
			x := a.FixAs[Real]("x")

			// A sum over the one-point interval is its summand there:
			// ↦ c = c * real_pow(x, 0).
			a.Do(Cite(real_sum.IntervalPoint))
			a.Show(
				"the empty product is &1, and a factor of &1 changes nothing",
				By(real_pow.PowExpZeroClause.At(x), real_ring.MulRightId.At(c)))
		}),
})}

// Id — the identity is polynomial: its list reads &0 at the constant
// term and &1 at the linear one, and the sum over 0 .. 1 is computed
// by peeling its top point off, leaving a one-point sum below it.
var Id = idThm{family.Add(registry.ProofEntry{
	Name: "Id",
	Key:  "prop_7b1bcc2d83c1321f",
	Build: family.Theorem("polynomial_function(λx:real. x)",
		func(a *Argument) {
			a.Do(Unfold(PolynomialFunctionDef))
			// Degree 1, and the coefficient at i is &i.
			a.Take(a.Term("1"))
			a.Take(a.Term("λi:num. &i"))
			x := a.FixAs[Real]("x")

			one := a.Ctx().Nat(1)
			zero := a.Ctx().Nat(0)
			summand := a.TermAs[Fun[Nat, Real]]("λi:num. &i * real_pow(x, i)")

			bounds := a.Have(
				"the interval 0 .. 1 has a top point, and it lies above the bottom",
				"0 < 1 ∧ 0 ≤ 1",
				By(nat_order.PosIffNonzero.At(one), nat_arith.OneNotZero, nat_order.ZeroLessEq.At(one)))
			peeled := a.Have(
				"so the top point comes off the sum",
				"sum(0 .. 1, λi:num. &i * real_pow(x, i)) = "+
					"sum(0 .. 1 - 1, λi:num. &i * real_pow(x, i)) + &1 * real_pow(x, 1)",
				By(bounds, real_sum.PeelRight.At(one, zero, summand)))
			a.Show(
				"what remains is the one-point sum &0·x⁰, which vanishes, and the top term &1·x¹, which is x",
				By(
					peeled,
					nat_monus.SubRefl.At(one),
					real_sum.IntervalPoint.At(zero, summand),
					real_ring.MulLeftZero,
					real_construction.MulLeftId,
					real_pow.PowOne.At(x),
					real_construction.AddLeftId.At(x)))
		}),
})}

// Identity — the identity function is polynomial, being the
// coefficient list of Id under another name.
var Identity = identityThm{family.Add(registry.ProofEntry{
	Name: "Identity",
	Key:  "prop_a79158d9d3dfbc87",
	Build: family.Theorem("polynomial_function(identity_map)",
		func(a *Argument) {
			// identity is λx. x by definition, and that is Id's statement.
			a.Do(Unfold(functions.IdentityApply), Cite(Id))
		}),
})}

// ---------------------------------------------------------------------------
// The linear closure
// ---------------------------------------------------------------------------
//
// The class is closed under the linear operations. Every member that
// builds a list opens the way the generators do — unfold, name the
// degree and the list, fix the point — and then computes in the
// interval calculus of `iterate/real/real_sum` with three tools: a scalar
// comes out of a sum, two sums over one interval add pointwise, and a
// sum may be read over a longer interval when the summand vanishes on
// the extension. The members that build no list reduce to a sibling.
//
// A hypothesis `polynomial_function(p)` opens the same way, by
// `Unpack2`, into a degree and a list, and the claim texts spell those
// by their MINTS — `m₀`, `c₀`, `c₁`, … — rather than by the
// definition's binders `m` and `c`: the binder `c` collides with the
// statement's own scalar `c` (ScalarLeft), and two hypotheses open
// with the same binders at once (Add). The Go names bind to the same
// vocabulary.
//
// One engine seam, said once: `Unfold` on the goal also rewrites the
// resident hypotheses — a ∧-hypothesis is split into its two halves,
// and the constant is opened in them as it is in the goal. Add and
// Sub, whose hypothesis is a conjunction, therefore take it as
// `_ Fact` and re-name each half by `a.Hyp(text)` after the unfold,
// before unpacking.

// ScalarLeft — a scalar multiple of a polynomial is polynomial:
// scaling the function scales its list.
var ScalarLeft = scalarLeftThm{family.Add(registry.ProofEntry{
	Name: "ScalarLeft",
	Key:  "prop_f974a78fa946be5d",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:(real → real). ∀c:real.",
			Hypotheses: []string{
				"polynomial_function(p)",
			},
			Conclusion: "polynomial_function(λx:real. c * p(x))",
		},
		func(a *Argument, p *Arrow[Real, Real], c *Expr[Real], polynomial Fact) {
			a.Do(Unfold(PolynomialFunctionDef))
			// The list, discarded here, is spelled c₁ below.
			m, _, sumAt := a.Unpack2(polynomial)
			// The same degree, and each coefficient scaled by c.
			a.Take(m)
			a.Take(a.Term("λi:num. c * c₁(i)"))
			x := a.FixAs[Real]("x")

			zero := a.Ctx().Nat(0)
			degree := ext.As[Nat](m)
			interval := a.TermAs[Set[Nat]]("0 .. m")
			terms := a.TermAs[Fun[Nat, Real]]("λi:num. c₁(i) * real_pow(x, i)")
			scaledTerms := a.TermAs[Fun[Nat, Real]]("λi:num. c * (c₁(i) * real_pow(x, i))")
			rescaledTerms := a.TermAs[Fun[Nat, Real]]("λi:num. (c * c₁(i)) * real_pow(x, i)")

			a.Do(CalcEq(
				Leg(
					a.TermAs[Real]("c * sum(0 .. m, λi:num. c₁(i) * real_pow(x, i))"),
					"p(x) is its sum",
					By(sumAt.At(x))),
				Leg(
					a.TermAs[Real]("sum(0 .. m, λi:num. c * (c₁(i) * real_pow(x, i)))"),
					"and the scalar moves inside the sum",
					By(real_sum.ScalarLeft.At(c, terms, interval))),
				FinalLeg(
					"where it regroups onto each coefficient, by associativity",
					By(
						real_construction.MulAssoc,
						real_sum.IntervalCongruence.At(zero, degree, scaledTerms, rescaledTerms))),
			))
		}),
})}

// ScalarRight — and on the other side, by commuting the scalar to the
// left under the λ.
var ScalarRight = scalarRightThm{family.Add(registry.ProofEntry{
	Name: "ScalarRight",
	Key:  "prop_2c6eacd42284bd89",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:(real → real). ∀c:real.",
			Hypotheses: []string{
				"polynomial_function(p)",
			},
			Conclusion: "polynomial_function(λx:real. p(x) * c)",
		},
		func(a *Argument, p *Arrow[Real, Real], c *Expr[Real], polynomial Fact) {
			// λx. p(x) * c ↦ λx. c * p(x)
			a.Do(Simp(Fwd(real_construction.MulSym)))
			a.Show(
				"the scalar now sits on the left, which is ScalarLeft's conclusion",
				By(polynomial, ScalarLeft))
		}),
})}

// Add — the sum of two polynomials is polynomial: adding the functions
// adds their lists, once both are padded with zeros to a common
// length. A list read past its own degree, with COND(i ≤ m, cᵢ, &0)
// for the missing coefficients, sums to the same value; that padding
// is the lemma the two hypotheses are read through before the sums
// are merged, and the one place a list is rewritten before it can be
// combined.
var Add = addThm{family.Add(registry.ProofEntry{
	Name: "Add",
	Key:  "prop_c21372a0cc2cfd11",
	Build: family.Sections(
		Statement{
			Binders: "∀p q:(real → real).",
			Hypotheses: []string{
				"polynomial_function(p)",
				"polynomial_function(q)",
			},
			Conclusion: "polynomial_function(λx:real. p(x) + q(x))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// Padding: a list of degree m, read up to any n ≥ m with &0 past
			// m, sums to the same value. `real_sum.ZeroPad` says so of the
			// terms cᵢ·xⁱ silenced past m, and a term silenced is its
			// coefficient silenced, since &0·xⁱ is &0.
			padded := ctx.Lemma(
				Statement{
					Binders: "∀x:real. ∀m n:num. ∀c:(num → real).",
					Hypotheses: []string{
						"m ≤ n",
					},
					Conclusion: "sum(0 .. m, λi:num. c(i) * real_pow(x, i)) = " +
						"sum(0 .. n, λi:num. COND(i ≤ m, c(i), &0) * real_pow(x, i))",
				},
				func(a *Argument, x *Expr[Real], m, n *Expr[Nat], c *Arrow[Nat, Real], reaches Fact) {
					interval := a.TermAs[Set[Nat]]("0 .. n")
					terms := a.TermAs[Fun[Nat, Real]]("λi:num. c(i) * real_pow(x, i)")
					silencedTerms := a.TermAs[Fun[Nat, Real]]("λi:num. COND(i ≤ m, c(i) * real_pow(x, i), &0)")
					paddedList := a.TermAs[Fun[Nat, Real]]("λi:num. COND(i ≤ m, c(i), &0) * real_pow(x, i)")

					silencing := a.Have(
						"a term silenced is its coefficient silenced",
						"∀i:num. COND(i ≤ m, c(i) * real_pow(x, i), &0) = COND(i ≤ m, c(i), &0) * real_pow(x, i)",
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							power := b.TermAs[Real]("real_pow(x, i)")
							b.Cases(b.Term("i ≤ m"))
							b.When(
								"i ≤ m: both conditionals read the term",
								func(b *Argument, holds Fact) {
									b.Show(
										"which is cᵢ·xⁱ on either side",
										By(holds))
								})
							b.Otherwise(
								"m < i: both read &0, and &0·xⁱ is &0",
								func(b *Argument, fails Fact) {
									b.Show(
										"so both sides are &0",
										By(fails, real_ring.MulLeftZero.At(power)))
								})
						}))
					a.Do(CalcEq(
						Leg(
							a.TermAs[Real]("sum(0 .. n, λi:num. COND(i ≤ m, c(i) * real_pow(x, i), &0))"),
							"the sum reaches over the long interval once its terms are silenced past m",
							By(reaches, real_sum.ZeroPad.At(m, n, terms))),
						FinalLeg(
							"and the silenced terms are the padded list, point by point",
							By(silencing, real_sum.CongruenceEverywhere.At(interval, silencedTerms, paddedList))),
					))
				})

			return ctx.Theorem(headline, func(a *Argument, p, q *Arrow[Real, Real], _ Fact) {
				// The two hypotheses open in turn, p's as (m₀, c₀) and q's
				// as (m₁, c₁).
				a.Do(Unfold(PolynomialFunctionDef))
				m0, c0, pSum := a.Unpack2(a.Hyp(
					"∃m:num. ∃c:(num → real). ∀x:real. p(x) = sum(0 .. m, λi:num. c(i) * real_pow(x, i))"))
				m1, c1, qSum := a.Unpack2(a.Hyp(
					"∃m:num. ∃c:(num → real). ∀x:real. q(x) = sum(0 .. m, λi:num. c(i) * real_pow(x, i))"))
				// Degree m₀ + m₁, and the two lists padded to it and added.
				a.Take(a.Term("m₀ + m₁"))
				a.Take(a.Term("λi:num. COND(i ≤ m₀, c₀(i), &0) + COND(i ≤ m₁, c₁(i), &0)"))
				x := a.FixAs[Real]("x")

				zero := a.Ctx().Nat(0)
				degree0, degree1 := ext.As[Nat](m0), ext.As[Nat](m1)
				degree := a.TermAs[Nat]("m₀ + m₁")
				paddedP := a.TermAs[Fun[Nat, Real]]("λi:num. COND(i ≤ m₀, c₀(i), &0) * real_pow(x, i)")
				paddedQ := a.TermAs[Fun[Nat, Real]]("λi:num. COND(i ≤ m₁, c₁(i), &0) * real_pow(x, i)")
				termwise := a.TermAs[Fun[Nat, Real]](
					"λi:num. COND(i ≤ m₀, c₀(i), &0) * real_pow(x, i) + COND(i ≤ m₁, c₁(i), &0) * real_pow(x, i)")
				added := a.TermAs[Fun[Nat, Real]](
					"λi:num. (COND(i ≤ m₀, c₀(i), &0) + COND(i ≤ m₁, c₁(i), &0)) * real_pow(x, i)")

				a.Do(CalcEq(
					Leg(
						a.TermAs[Real]("sum(0 .. m₀, λi:num. c₀(i) * real_pow(x, i)) + "+
							"sum(0 .. m₁, λi:num. c₁(i) * real_pow(x, i))"),
						"p(x) and q(x) are their sums",
						By(pSum.At(x), qSum.At(x))),
					Leg(
						a.TermAs[Real]("sum(0 .. m₀ + m₁, λi:num. COND(i ≤ m₀, c₀(i), &0) * real_pow(x, i)) + "+
							"sum(0 .. m₀ + m₁, λi:num. COND(i ≤ m₁, c₁(i), &0) * real_pow(x, i))"),
						"each padded to the common degree, which neither exceeds",
						By(
							At(padded, x, m0, degree, c0),
							At(padded, x, m1, degree, c1),
							nat_order.LessEqAdd.At(degree0, degree1),
							nat_order.LessEqAddLeft.At(degree0, degree1))),
					Leg(
						a.TermAs[Real]("sum(0 .. m₀ + m₁, "+
							"    λi:num. COND(i ≤ m₀, c₀(i), &0) * real_pow(x, i) + COND(i ≤ m₁, c₁(i), &0) * real_pow(x, i))"),
						"two sums over one interval add pointwise",
						By(real_sum.IntervalAdd.At(zero, degree, paddedP, paddedQ))),
					FinalLeg(
						"and at each point the two padded coefficients add before the power multiplies",
						By(real_ring.RightDistrib, real_sum.IntervalCongruence.At(zero, degree, termwise, added))),
				))
			})
		}),
})}

// Neg — a function is polynomial exactly when its negation is. Both
// directions are ScalarLeft at the scalar -&1: the negation is -&1
// times the function, and the function is -&1 times its negation.
var Neg = negThm{family.Add(registry.ProofEntry{
	Name: "Neg",
	Key:  "prop_2df0973f0b67876b",
	Build: family.Theorem(
		"∀p:(real → real). polynomial_function(λx:real. -p(x)) ⇔ polynomial_function(p)",
		func(a *Argument, p *Arrow[Real, Real]) {
			a.Iff()
			a.Forward(
				"p is -&1 times its negation, a scalar multiple of a polynomial",
				func(b *Argument, negPolynomial Fact) {
					scaled := b.Have(
						"-&1 times the negation is polynomial, by ScalarLeft",
						"polynomial_function(λx:real. -&1 * -p(x))",
						By(negPolynomial, ScalarLeft))
					same := b.Have(
						"and it is p, pointwise",
						"(λx:real. -&1 * -p(x)) = p",
						Derive(func(c *Argument) {
							c.Do(Funext())
							x := c.FixAs[Real]("x")
							negated := c.TermAs[Real]("-p(x)")
							c.Show(
								"at x, -&1 · -p(x) is --p(x), which is p(x)",
								By(real_ring.NegMinusOne.At(negated), real_ring.NegNeg.At(p.Apply(x))))
						}))
					b.Show(
						"so p is polynomial",
						By(Normalized, scaled, same))
				})
			a.Backward(
				"the negation is -&1 times p, a scalar multiple of a polynomial",
				func(b *Argument, polynomial Fact) {
					// λx. -p(x) ↦ λx. -&1 * p(x)
					b.Do(Simp(Rev(real_ring.NegMinusOne)))
					b.Show(
						"which is polynomial by ScalarLeft",
						By(polynomial, ScalarLeft))
				})
		}),
})}

// Sub — the difference of two polynomials is polynomial: it is the sum
// of the first with the negation of the second, and both of those
// constructions are above.
var Sub = subThm{family.Add(registry.ProofEntry{
	Name: "Sub",
	Key:  "prop_8699d7b5c8d86798",
	Build: family.Theorem(
		Statement{
			Binders: "∀p q:(real → real).",
			Hypotheses: []string{
				"polynomial_function(p)",
				"polynomial_function(q)",
			},
			Conclusion: "polynomial_function(λx:real. p(x) - q(x))",
		},
		func(a *Argument, p, q *Arrow[Real, Real], _ Fact) {
			// λx. p(x) - q(x) ↦ λx. p(x) + -q(x)
			a.Do(Unfold(real_ring.RealSubDef))
			pPolynomial := a.Hyp("polynomial_function(p)")
			qPolynomial := a.Hyp("polynomial_function(q)")
			negated := a.Have(
				"-q is polynomial, as q is",
				"polynomial_function(λx:real. -q(x))",
				By(qPolynomial, Neg))
			a.Show(
				"and the sum of p and -q is polynomial",
				By(pPolynomial, negated, Add))
		}),
})}

// ---------------------------------------------------------------------------
// Products and sums
// ---------------------------------------------------------------------------
//
// The class is closed under multiplication, and with it under powers
// and under finite sums. A product of two coefficient lists is their
// convolution, and nothing here writes it down: what carries the part
// is how a coefficient sum one degree higher reads. Peeled at its
// lowest point it is the constant term plus x times the sum with the
// list shifted down by one — the Horner form — and read upwards that
// peel is an induction on the degree. Three primitives spell it: the
// peel; that multiplying a polynomial by x keeps it polynomial, the
// peel read backwards on the list shifted up by one; and the induction
// itself, stated for an arbitrary property so that the two members
// needing it read it off rather than run it again. The product law is
// that induction at "times q, still polynomial"; the structural
// induction principle below is the same induction at the caller's own
// property.

// Horner — the peel: a coefficient sum one degree higher is its
// constant term plus x times the sum over the list shifted down, in
// four legs.
var Horner = hornerThm{family.Add(registry.ProofEntry{
	Name: "Horner",
	Key:  "prop_57ffbd5359b11e4c",
	Build: family.Theorem(
		"∀m:num. ∀c:(num → real). ∀x:real. "+
			"    sum(0 .. m + 1, λi:num. c(i) * real_pow(x, i)) = "+
			"    c(0) + x * sum(0 .. m, λi:num. c(i + 1) * real_pow(x, i))",
		func(a *Argument, m *Expr[Nat], c *Arrow[Nat, Real], x *Expr[Real]) {
			zero := a.Ctx().Nat(0)
			one := a.Ctx().Nat(1)
			above := a.TermAs[Nat]("m + 1")
			interval := a.TermAs[Set[Nat]]("0 .. m")
			terms := a.TermAs[Fun[Nat, Real]]("λi:num. c(i) * real_pow(x, i)")
			shiftedTerms := a.TermAs[Fun[Nat, Real]]("λi:num. c(i + 1) * real_pow(x, i + 1)")
			xTimesTerms := a.TermAs[Fun[Nat, Real]]("λi:num. x * (c(i + 1) * real_pow(x, i))")
			shiftedList := a.TermAs[Fun[Nat, Real]]("λi:num. c(i + 1) * real_pow(x, i)")

			carries := a.Have(
				"each term of the shifted summand carries one factor of x, since x^(i+1) is x·xⁱ",
				"∀i:num. c(i + 1) * real_pow(x, i + 1) = x * (c(i + 1) * real_pow(x, i))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					coefficient := b.TermAs[Real]("c(i + 1)")
					power := b.TermAs[Real]("real_pow(x, i)")
					b.Show(
						"and the factor x moves to the front of the product",
						By(
							Normalized,
							real_pow.PowAddOne.At(x, i),
							real_construction.MulAssoc.At(coefficient, x, power),
							real_construction.MulSym.At(coefficient, x),
							real_construction.MulAssoc.At(x, coefficient, power)))
				}))
			a.Do(CalcEq(
				// The interval stays `0 + 1 .. m + 1`, unreduced: the next leg
				// reads it as Shift's stated shape, `m + p .. n + p`.
				Leg(
					a.TermAs[Real]("c(0) * real_pow(x, 0) + sum(0 + 1 .. m + 1, λi:num. c(i) * real_pow(x, i))"),
					"the lowest point comes off the front of the sum",
					By(nat_order.ZeroLessEq.At(above), real_sum.PeelLeft.At(zero, above, terms))),
				Leg(
					a.TermAs[Real]("c(0) + sum(0 .. m, λi:num. c(i + 1) * real_pow(x, i + 1))"),
					"x⁰ is &1, and what is left is the same summand read one point lower",
					By(
						Normalized,
						real_pow.PowExpZeroClause.At(x),
						real_ring.MulRightId.At(c.Apply(zero)),
						real_sum.Shift.At(zero, m, one, terms))),
				Leg(
					a.TermAs[Real]("c(0) + sum(0 .. m, λi:num. x * (c(i + 1) * real_pow(x, i)))"),
					"each of whose terms carries one factor of x",
					By(carries, real_sum.CongruenceEverywhere.At(interval, shiftedTerms, xTimesTerms))),
				FinalLeg(
					"and the common factor comes out of the sum",
					By(real_sum.ScalarLeft.At(x, shiftedList, interval))),
			))
		}),
})}

// TimesX — multiplying a polynomial by x keeps it polynomial: the list
// shifts up by one, with &0 as the new constant term, and the peel at
// the shifted-up list is x times the original sum.
var TimesX = timesXThm{family.Add(registry.ProofEntry{
	Name: "TimesX",
	Key:  "prop_9f32ee9b6982c9cc",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:(real → real).",
			Hypotheses: []string{
				"polynomial_function(p)",
			},
			Conclusion: "polynomial_function(λx:real. x * p(x))",
		},
		func(a *Argument, p *Arrow[Real, Real], polynomial Fact) {
			a.Do(Unfold(PolynomialFunctionDef))
			m, _, sumAt := a.Unpack2(polynomial)
			a.Take(a.Term("m + 1"))
			a.Take(a.Term("λi:num. COND(i = 0, &0, c(i - 1))"))
			x := a.FixAs[Real]("x")

			one := a.Ctx().Nat(1)
			degree := ext.As[Nat](m)
			interval := a.TermAs[Set[Nat]]("0 .. m")
			terms := a.TermAs[Fun[Nat, Real]]("λi:num. c(i) * real_pow(x, i)")
			shiftedUp := a.TermAs[Fun[Nat, Real]]("λi:num. COND(i = 0, &0, c(i - 1))")
			shiftedUpTerms := a.TermAs[Fun[Nat, Real]](
				"λi:num. COND(i + 1 = 0, &0, c(i + 1 - 1)) * real_pow(x, i)")
			xTimesSum := a.TermAs[Real](
				"x * sum(0 .. m, λi:num. COND(i + 1 = 0, &0, c(i + 1 - 1)) * real_pow(x, i))")

			unshifted := a.Have(
				"the shifted-up list read one point higher is the "+
					"list itself: i + 1 is never 0, and i + 1 - 1 is i",
				"∀i:num. c(i) * real_pow(x, i) = COND(i + 1 = 0, &0, c(i + 1 - 1)) * real_pow(x, i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					b.Show(
						"so the conditional reads its second arm, at i",
						By(Normalized, peano.SucNotZero.At(i), nat_arith.Add1.At(i), nat_monus.AddSubCancel.At(i, one)))
				}))
			a.Do(CalcEq(
				Leg(
					a.TermAs[Real]("x * sum(0 .. m, λi:num. c(i) * real_pow(x, i))"),
					"p(x) is its sum",
					By(sumAt.At(x))),
				Leg(
					xTimesSum,
					"whose list is the shifted-up list read one point higher",
					By(unshifted, real_sum.CongruenceEverywhere.At(interval, terms, shiftedUpTerms))),
				FinalLeg(
					"and that is the peel of the shifted-up list, whose constant term is &0",
					By(Horner.At(degree, shiftedUp, x), real_construction.AddLeftId.At(xTimesSum))),
			))
		}),
})}

// HornerInduction — the degree induction, for an arbitrary property: a
// property that holds of every constant, survives multiplication by the
// identity and survives addition holds of every coefficient sum. The
// peel carries the step, reading the sum one degree higher as a
// constant plus x times a shorter sum the hypothesis already covers.
var HornerInduction = hornerInductionThm{family.Add(registry.ProofEntry{
	Name: "HornerInduction",
	Key:  "prop_47cfd660c87e6feb",
	Build: family.Theorem(
		Statement{
			Binders: "∀P:((real → real) → bool). ∀m:num. ∀c:(num → real).",
			Hypotheses: []string{
				"∀c:real. P(λx:real. c)",
				"(∀f:(real → real). P(f) ⇒ P(λx:real. x * f(x))) ∧ " +
					"(∀f g:(real → real). P(f) ∧ P(g) ⇒ P(λx:real. f(x) + g(x)))",
			},
			Conclusion: "P(λx:real. sum(0 .. m, λi:num. c(i) * real_pow(x, i)))",
		},
		func(a *Argument, P *Arrow[Fun[Real, Real], Bool], constants, rules Fact) {
			steps := a.Conjuncts(
				rules,
				"P survives multiplication by the identity",
				"and survives addition")
			// Binding P α-renames the binder it strips under, so the goal
			// spells the degree m₀; Binder takes the statement's name.
			m := a.Binder("m")

			a.Induct(m)
			a.Base(
				"m₀ = 0: the sum is the constant c(0)",
				func(b *Argument) {
					b.FixAs[Fun[Nat, Real]]("c")
					constant := b.TermAs[Real]("c(0)")

					same := b.Have(
						"a sum over the one-point interval is its term there, and x⁰ is &1",
						"(λx:real. sum(0 .. 0, λi:num. c(i) * real_pow(x, i))) = λx:real. c(0)",
						Derive(func(d *Argument) {
							d.Do(Funext())
							x := d.FixAs[Real]("x")
							zero := d.Ctx().Nat(0)
							terms := d.TermAs[Fun[Nat, Real]]("λi:num. c(i) * real_pow(x, i)")
							d.Show(
								"so at x the sum is c(0)",
								By(
									Normalized,
									real_sum.IntervalPoint.At(zero, terms),
									real_pow.PowExpZeroClause.At(x),
									real_ring.MulRightId.At(constant)))
						}))
					b.Show(
						"and P holds of the constant c(0)",
						By(Normalized, same, constants.At(constant)))
				})
			a.Step(
				"m₀ → suc m₀: the peel reads the sum as c(0) + x·Σ', a "+
					"constant plus the identity times a sum the hypothesis covers",
				func(b *Argument, ih Fact) {
					c := b.FixAs[Fun[Nat, Real]]()
					degree := ext.As[Nat](m)
					constant := b.TermAs[Real]("c(0)")
					shiftedList := b.TermAs[Fun[Nat, Real]]("λi:num. c(i + 1)")
					constantFn := b.TermAs[Fun[Real, Real]]("λx:real. c(0)")
					shiftedSum := b.TermAs[Fun[Real, Real]](
						"λx:real. sum(0 .. m₀, λi:num. c(i + 1) * real_pow(x, i))")
					xTimesShifted := b.TermAs[Fun[Real, Real]](
						"λx:real. x * sum(0 .. m₀, λi:num. c(i + 1) * real_pow(x, i))")

					split := b.Have(
						"peeled, the sum is c(0) + x·Σ'",
						"(λx:real. sum(0 .. suc(m₀), λi:num. c(i) * real_pow(x, i))) = "+
							"(λx:real. c(0) + x * sum(0 .. m₀, λi:num. c(i + 1) * real_pow(x, i)))",
						Derive(func(d *Argument) {
							d.Do(Funext())
							x := d.FixAs[Real]("x")
							d.Show(
								"at x: suc m₀ is m₀ + 1, and the peel applies",
								By(Horner.At(degree, c, x), nat_arith.Add1.At(degree)))
						}))
					inner := b.Have(
						"P holds of Σ', by the hypothesis at the shifted list",
						"P(λx:real. sum(0 .. m₀, λi:num. c(i + 1) * real_pow(x, i)))",
						By(ih.At(shiftedList)))
					scaled := b.Have(
						"so of x·Σ', the identity times it",
						"P(λx:real. x * sum(0 .. m₀, λi:num. c(i + 1) * real_pow(x, i)))",
						By(inner, steps[0].At(shiftedSum)))
					b.Show(
						"and P holds of the constant c(0), hence of their sum",
						By(split, scaled, constants.At(constant), steps[1].At(constantFn, xTimesShifted)))
				})
		}),
})}

// Mul — the product of two polynomials is polynomial: p is opened as
// a coefficient sum, and the lemma below carries a coefficient sum
// times a polynomial by the degree induction.
var Mul = mulThm{family.Add(registry.ProofEntry{
	Name: "Mul",
	Key:  "prop_52e92e849837acc3",
	Build: family.Sections(
		Statement{
			Binders: "∀p q:(real → real).",
			Hypotheses: []string{
				"polynomial_function(p)",
				"polynomial_function(q)",
			},
			Conclusion: "polynomial_function(λx:real. p(x) * q(x))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// A coefficient sum times a polynomial is polynomial: the
			// degree induction at "times q, still polynomial", whose three
			// rules are the scalar law, the shift and the sum law.
			byDegree := ctx.Lemma(
				Statement{
					Binders: "∀m:num. ∀c:(num → real). ∀q:(real → real).",
					Hypotheses: []string{
						"polynomial_function(q)",
					},
					Conclusion: "polynomial_function(λx:real. sum(0 .. m, λi:num. c(i) * real_pow(x, i)) * q(x))",
				},
				func(a *Argument, m *Expr[Nat], c *Arrow[Nat, Real], q *Arrow[Real, Real], qPolynomial Fact) {
					timesQ := a.TermAs[Fun[Fun[Real, Real], Bool]](
						"λf:(real → real). polynomial_function(λx:real. f(x) * q(x))")

					a.Show(
						"so every coefficient sum times q is polynomial",
						ByInduction(HornerInduction.At(timesQ, m, c),

							Case(
								"constants: a constant times q is a scalar multiple of q, whatever the constant",
								By(qPolynomial, ScalarLeft)),

							Case(
								"times the identity: (x·f)·q regroups as x·(f·q), and x times a covered product stays covered",
								Derive(func(b *Argument) {
									b.FixAs[Fun[Real, Real]]("f")
									covered := b.Assume()
									product := b.TermAs[Fun[Real, Real]]("λx:real. f(x) * q(x)")

									same := b.Have(
										"the two readings agree at every point, by associativity",
										"(λx:real. x * f(x) * q(x)) = λx:real. x * (f(x) * q(x))",
										Funext(),
										By(real_construction.MulAssoc))
									b.Show(
										"so it is x times a polynomial, which TimesX keeps polynomial",
										By(covered, same, TimesX.At(product)))
								})),

							Case(
								"sums: (f + g)·q is f·q + g·q, a sum of two covered products",
								Derive(func(b *Argument) {
									b.FixAs[Fun[Real, Real]]("f")
									b.FixAs[Fun[Real, Real]]("g")
									parts := b.Assume()
									fq := b.TermAs[Fun[Real, Real]]("λx:real. f(x) * q(x)")
									gq := b.TermAs[Fun[Real, Real]]("λx:real. g(x) * q(x)")

									same := b.Have(
										"the sum splits over q at every point, by distributivity",
										"(λx:real. (f(x) + g(x)) * q(x)) = λx:real. f(x) * q(x) + g(x) * q(x)",
										Funext(),
										By(real_ring.RightDistrib))
									b.Show(
										"so it is the sum of two polynomials",
										By(parts, same, Add.At(fq, gq)))
								})),
						))
				})

			return ctx.Theorem(headline, func(a *Argument, p, q *Arrow[Real, Real], both Fact) {
				// The goal stays folded, so that the lemma's conclusion meets
				// it; only p's half of the hypothesis is opened, inside its
				// own claim.
				pOpens := a.Have(
					"p is some coefficient sum",
					"∃m:num. ∃c:(num → real). ∀x:real. p(x) = sum(0 .. m, λi:num. c(i) * real_pow(x, i))",
					// Unfolding opens the hypothesis, whose first half IS the
					// claim — so the unfold closes it outright.
					Unfold(PolynomialFunctionDef))
				qPolynomial := a.Have(
					"and q is polynomial",
					"polynomial_function(q)",
					By(both))
				m, c, pSum := a.Unpack2(pOpens)

				product := a.Have(
					"the sum times q is polynomial, by induction on the degree",
					"polynomial_function(λx:real. sum(0 .. m₀, λi:num. c₀(i) * real_pow(x, i)) * q(x))",
					By(qPolynomial, At(byDegree, m, c, q)))
				same := a.Have(
					"and p·q is that function, p being its sum at every point",
					"(λx:real. p(x) * q(x)) = λx:real. sum(0 .. m₀, λi:num. c₀(i) * real_pow(x, i)) * q(x)",
					Derive(func(b *Argument) {
						b.Do(Funext())
						x := b.FixAs[Real]("x")
						b.Show(
							"at x, p(x) is its sum",
							By(pSum.At(x)))
					}))
				a.Show(
					"so p·q is polynomial",
					By(product, same))
			})
		}),
})}

// Pow — a power of a polynomial is polynomial: induction on the
// exponent, p⁰ being the constant &1 and p^(n+1) the product of p
// with pⁿ.
var Pow = powThm{family.Add(registry.ProofEntry{
	Name: "Pow",
	Key:  "prop_2a17466abd7f816d",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:(real → real). ∀n:num.",
			Hypotheses: []string{
				"polynomial_function(p)",
			},
			Conclusion: "polynomial_function(λx:real. real_pow(p(x), n))",
		},
		func(a *Argument, p *Arrow[Real, Real], polynomial Fact) {
			one := a.TermAs[Real]("&1")
			// Binding p α-renames the binder it strips under, so the goal
			// spells the exponent n₀; Binder takes the statement's name.
			n := a.Binder("n")
			a.Induct(n)
			a.Base(
				"n₀ = 0: p(x)⁰ is &1 at every point, a constant", // λx. real_pow(p(x), 0) ↦ λx. &1
				Simp(Fwd(real_pow.PowExpZeroClause)),
				By(Const.At(one)))
			a.Step(
				"n₀ → suc n₀: p(x)^(suc n₀) is p(x)·p(x)^n₀, the product of p with a polynomial",
				func(b *Argument, ih Fact) {
					power := b.TermAs[Fun[Real, Real]]("λx:real. real_pow(p(x), n₀)")
					// λx. real_pow(p(x), suc(n)) ↦ λx. p(x) * real_pow(p(x), n)
					b.Do(Simp(Fwd(real_pow.PowExpSucClause)))
					b.Show(
						"which is polynomial by Mul",
						By(polynomial, ih, Mul.At(p, power)))
				})
		}),
})}

// Sum — a finite sum of polynomials, indexed over any finite set, is
// polynomial: induction on the index set, the empty sum being the
// constant &0 and one more index adding one more polynomial. The
// property carried across the induction is the statement itself, read
// at an index set t: the hypothesis restricted to t makes the sum over
// t polynomial.
var Sum = sumThm{family.Add(registry.ProofEntry{
	Name: "Sum",
	Key:  "prop_7b32f26f454dc639",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀p:(real → A → real).",
			Hypotheses: []string{
				"finite(s)",
				"∀i:A. i ∈ s ⇒ polynomial_function(λx:real. p(x, i))",
			},
			Conclusion: "polynomial_function(λx:real. sum(s, p(x)))",
		},
		func(a *Argument, s *Expr[Set[A]], p *Arrow2[Real, A, Real], finite, polynomialTerms Fact) {
			zero := a.TermAs[Real]("&0")

			a.Show(
				"so the property holds of every finite index set, and s is one",
				ByInduction(finite_set.FiniteInductFresh, finite, Generalizing(polynomialTerms),

					Case(
						"∅: the empty sum is &0 at every point, a constant",
						Derive(func(b *Argument) {
							b.Assume() // the hypothesis on ∅, which asks nothing
							same := b.Have(
								"the sum over ∅ is &0 at every point",
								"(λx:real. sum(∅⟨A:A⟩, p(x))) = λx:real. &0",
								// Pointwise, by the recursion's empty clause.
								Funext(),
								By(Normalized, real_sum.Clauses))
							b.Show(
								"and the constant &0 is polynomial",
								By(Normalized, same, Const.At(zero)))
						})),

					Case(
						"insert: one more index adds one more polynomial to a sum the property already covers",
						Derive(func(b *Argument) {
							e := b.FixAs[A]("e")
							t := b.FixAs[Set[A]]("t")
							carried := b.Assume()  // the property at t, e not in t, and t finite
							onInsert := b.Assume() // the hypothesis on insert(e, t)
							atE := b.TermAs[Fun[Real, Real]]("λx:real. p(x, e)")
							overT := b.TermAs[Fun[Real, Real]]("λx:real. sum(t, p(x))")

							restricted := b.Have(
								"the hypothesis on insert(e, t) holds on t in particular",
								"∀i:A. i ∈ t ⇒ polynomial_function(λx:real. p(x, i))",
								Derive(func(d *Argument) {
									i := d.FixAs[A]()
									inT := d.Assume()
									d.Show(
										"an index in t is in insert(e, t)",
										By(inT, onInsert.At(i), set_basic.InInsert.At(t, e, i)))
								}))
							rest := b.Have(
								"so the sum over t is polynomial, by the property carried",
								"polynomial_function(λx:real. sum(t, p(x)))",
								By(carried, restricted))
							first := b.Have(
								"and the summand at e is polynomial, e being in insert(e, t)",
								"polynomial_function(λx:real. p(x, e))",
								By(onInsert.At(e), set_basic.InInsert.At(t, e, e)))
							same := b.Have(
								"the sum over insert(e, t) is the summand at e plus the sum over t",
								"(λx:real. sum(insert(e, t), p(x))) = λx:real. p(x, e) + sum(t, p(x))",
								// Pointwise: the recursion adds the value at the new index,
								// e being new to t.
								Funext(),
								By(Normalized, carried, real_sum.Clauses))
							b.Show(
								"so it is the sum of two polynomials",
								By(same, first, rest, Add.At(atE, overT)))
						})),
				))
		}),
})}

// ---------------------------------------------------------------------------
// The induction principle
// ---------------------------------------------------------------------------
//
// The generators exhaust the class: a property of real functions that
// holds of the identity and of every constant, and survives addition
// and multiplication, holds of every polynomial. The proof reads a
// polynomial as its coefficient sum and hands that sum to the degree
// induction above, whose three rules the four here supply: the
// constants and the sums rules are two of them verbatim, and a
// function multiplied by the identity is the product rule at λx. x.
// Composition is the principle's first consumer: for polynomial q,
// the property "composed with q, polynomial" holds of the four
// generators, so it holds of every polynomial p.

// Induction — the structural induction principle for polynomials.
var Induction = inductionThm{family.Add(registry.ProofEntry{
	Name: "Induction",
	Key:  "prop_8fddbc170a6ade1f",
	Build: family.Sections(
		Statement{
			Binders: "∀P:((real → real) → bool). ∀p:(real → real).",
			Hypotheses: []string{
				"P(λx:real. x)",
				"(∀c:real. P(λx:real. c)) ∧ " +
					"((∀f g:(real → real). P(f) ∧ P(g) ⇒ P(λx:real. f(x) + g(x))) ∧ " +
					"    (∀f g:(real → real). P(f) ∧ P(g) ⇒ P(λx:real. f(x) * g(x))))",
				"polynomial_function(p)",
			},
			Conclusion: "P(p)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// A property satisfying the four rules holds of every
			// coefficient sum: the degree induction above at P, whose
			// three rules the generators supply.
			byDegree := ctx.Lemma(
				Statement{
					Binders: "∀P:((real → real) → bool).",
					Hypotheses: []string{
						"P(λx:real. x)",
						"(∀c:real. P(λx:real. c)) ∧ " +
							"((∀f g:(real → real). P(f) ∧ P(g) ⇒ P(λx:real. f(x) + g(x))) ∧ " +
							"    (∀f g:(real → real). P(f) ∧ P(g) ⇒ P(λx:real. f(x) * g(x))))",
					},
					Conclusion: "∀m:num. ∀c:(num → real). P(λx:real. sum(0 .. m, λi:num. c(i) * real_pow(x, i)))",
				},
				func(a *Argument, P *Arrow[Fun[Real, Real], Bool], generators Fact) {
					products := a.Have(
						"P survives multiplication",
						"∀f g:(real → real). P(f) ∧ P(g) ⇒ P(λx:real. f(x) * g(x))",
						By(generators))
					id := a.TermAs[Fun[Real, Real]]("λx:real. x")
					// The principle is cited at a point, so its degree and
					// list are fixed here rather than left standing.
					m := a.FixAs[Nat]("m")
					c := a.FixAs[Fun[Nat, Real]]("c")

					a.Show(
						"so P holds of the sum of the list c up to m",
						ByInduction(HornerInduction.At(P, m, c),
							Case(
								"constants: P holds of every constant, which is one of the generators",
								By(generators)),
							Case(
								"times the identity: the product rule at λx. x, whose left factor is the identity generator",
								Derive(func(b *Argument) {
									f := b.FixAs[Fun[Real, Real]]()
									holds := b.Assume()
									b.Show(
										"so P holds of x·f",
										By(generators, holds, products.At(id, f)))
								})),
							Case(
								"sums: P survives addition, which is another of the generators",
								By(generators)),
						))
				})

			return ctx.Theorem(headline, func(a *Argument, P *Arrow[Fun[Real, Real], Bool], generators Fact,
				p *Arrow[Real, Real], isPolynomial Fact) {
				// The definition opens in that hypothesis alone — p is some
				// coefficient sum — and the rules hypothesis stays whole.
				pOpens := a.Unfolded(isPolynomial, PolynomialFunctionDef)
				m, c, pSum := a.Unpack2(pOpens)
				same := a.Have(
					"and p is that sum, as a function",
					"p = λx:real. sum(0 .. m₀, λi:num. c₀(i) * real_pow(x, i))",
					Derive(func(b *Argument) {
						b.Do(Funext())
						x := b.FixAs[Real]("x")
						b.Show(
							"at x, p(x) is its sum",
							By(pSum.At(x)))
					}))
				a.Show(
					"so P holds of p, a coefficient sum",
					By(Normalized, same, generators, At(byDegree, P, m, c)))
			})
		}),
})}

// Compose — the composition of two polynomials is polynomial. The
// property "polynomial when composed with q" is proved for every
// polynomial p by the induction principle: composing distributes over
// the generators — the identity and the constants compose to q and to
// themselves, and composition passes through a sum or a product point
// by point — so the four rules hold and the principle carries the
// property to every polynomial.
var Compose = composeThm{family.Add(registry.ProofEntry{
	Name: "Compose",
	Key:  "prop_cac9b07787784da4",
	Build: family.Theorem(
		Statement{
			Binders: "∀q p:(real → real).",
			Hypotheses: []string{
				"polynomial_function(q)",
				"polynomial_function(p)",
			},
			Conclusion: "polynomial_function(p ∘ q)",
		},
		func(a *Argument, q, p *Arrow[Real, Real], qPolynomial, polynomial Fact) {
			a.Show(
				"so the property holds of every polynomial, and p is one",
				ByInduction(Induction, polynomial,

					Case(
						"identity: (λx. x) ∘ q is q, which is polynomial",
						Derive(func(b *Argument) {
							same := b.Have(
								"composing the identity with q is q",
								"(λx:real. x) ∘ q = q",
								Unfold(functions.ComposeApply))
							b.Show(
								"which is polynomial",
								By(Normalized, qPolynomial, same))
						})),

					Case(
						"constants: (λx. c) ∘ q is the constant c",
						Derive(func(b *Argument) {
							c := b.FixAs[Real]("c")
							same := b.Have(
								"composing a constant with q leaves it constant",
								"(λx:real. c) ∘ q = (λx:real. c)",
								Unfold(functions.ComposeApply))
							b.Show(
								"which is polynomial",
								By(Normalized, same, Const.At(c)))
						})),

					Case(
						"sums: (f + g) ∘ q is f∘q + g∘q, a sum of two polynomials",
						Derive(func(b *Argument) {
							b.FixAs[Fun[Real, Real]]("f")
							b.FixAs[Fun[Real, Real]]("g")
							parts := b.Assume() // f∘q and g∘q polynomial
							fq := b.TermAs[Fun[Real, Real]]("f ∘ q")
							gq := b.TermAs[Fun[Real, Real]]("g ∘ q")
							same := b.Have(
								"composition passes through the sum, point by point",
								"(λx:real. f(x) + g(x)) ∘ q = (λx:real. (f ∘ q)(x) + (g ∘ q)(x))",
								Unfold(functions.ComposeApply))
							b.Show(
								"so it is the sum of two polynomials",
								By(parts, same, Add.At(fq, gq)))
						})),

					Case(
						"products: (f · g) ∘ q is (f∘q)·(g∘q), a product of two polynomials",
						Derive(func(b *Argument) {
							b.FixAs[Fun[Real, Real]]("f")
							b.FixAs[Fun[Real, Real]]("g")
							parts := b.Assume() // f∘q and g∘q polynomial
							fq := b.TermAs[Fun[Real, Real]]("f ∘ q")
							gq := b.TermAs[Fun[Real, Real]]("g ∘ q")
							same := b.Have(
								"composition passes through the product, point by point",
								"(λx:real. f(x) * g(x)) ∘ q = (λx:real. (f ∘ q)(x) * (g ∘ q)(x))",
								Unfold(functions.ComposeApply))
							b.Show(
								"so it is the product of two polynomials",
								By(parts, same, Mul.At(fq, gq)))
						})),
				))
		}),
})}
