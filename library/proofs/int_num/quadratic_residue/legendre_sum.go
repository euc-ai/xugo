// legendre_sum.go — a quadratic nonresidue exists modulo every odd prime p,
// so the symbols (a/p) over the residues a < p add up to 0.

package quadratic_residue

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// NonresidueExists — for an odd prime p some natural number e is a
// quadratic nonresidue: (e/p) = −1. It is found in a field F of p elements,
// where 2 ≠ 0, so some nonzero element z is not a square. z is the image of
// an integer a, whose symbol then maps to −1 and so, lying between −1 and 1,
// is −1; a natural number congruent to a has a's symbol. The integers modulo
// p are such a field.
var NonresidueExists = nonresidueExistsThm{family.Add(registry.ProofEntry{
	Name: "NonresidueExists",
	Key:  "prop_d6c3ef6cd1068e71",
	Build: family.Sections(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "∃e:num. legendre_symbol(e, p) = -1",
	}, func(ctx *Script, headline string) *GoalStackNode {
		inField := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀p:num.",
			Hypotheses: []string{
				"nat_prime(p)",
				"p ≠ 2",
				"has_size(F.carrier, p)",
			},
			Conclusion: "∃e:num. legendre_symbol(e, p) = -1",
		}, func(arg *Argument, F field.FieldFact[on.F], p *Expr[Nat], prime, odd, size Fact) {
			ring := field.RingOn.Read(F)
			integers := characteristic_zero.IntegerMapHomomorphism.Read(ring)
			one := arg.TermAs[Int]("1")
			minusOne := arg.TermAs[Int]("-1")
			characteristic := arg.Have(
				"F has characteristic p",
				"field_characteristic(F, p)",
				By(prime, size, finite_field.PrimeSizeCharacteristic.Read(F).At(p)))
			z, nonsquare := arg.ObtainAs[A](
				"a finite field in which 2 ≠ 0 has a nonzero element that is not a square",
				"∃z:A. z ∈ F.carrier ∧ z ≠ F.zero ∧ z ∉ {x * x | x:A | x ∈ F.carrier ∧ x ≠ F.zero}",
				By(
					prime,
					odd,
					characteristic,
					finite_field.OddCharacteristicTwoNonzero.Read(F).At(p),
					size,
					cardinality.HasSizeDef,
					finite_field.FiniteFieldSquares.Read(F)))
			parts := arg.Conjuncts(
				nonsquare,
				"z lies in F",
				"z is not zero",
				"z is not a square")
			a, preimage := arg.ObtainAs[Int](
				"z is the image of an integer a",
				"∃a:int. integer_map(field_ring(F), a) = z",
				By(prime, size, finite_field.IntegerMapOnto.Read(F).At(p, arg.MemberOf[on.F](z, parts[0]))))
			symbol := arg.TermAs[Int]("legendre_symbol(a, p)")
			symbolImage := arg.Have(
				"the image of a is a nonzero nonsquare, so (a/p) maps to −1",
				"integer_map(field_ring(F), legendre_symbol(a, p)) = -F.one",
				By(prime, size, preimage, parts[1], parts[2], LegendreInField.Read(F).At(p, a)))
			congruent := arg.Have(
				"−1 maps to −1 too, and integers with one image are congruent mod p",
				"legendre_symbol(a, p) ≡ -1 (mod p)",
				By(
					characteristic,
					symbolImage,
					finite_field.IntegerMapEqIff.Read(F).At(p, symbol, minusOne),
					ring_homomorphism.MapNeg.Read(integers).AsFact().At(one),
					ring_homomorphism.MapOne.Read(integers),
					set_basic.InUniv.At(one)))
			nonresidue := arg.Have(
				"two values between −1 and 1 congruent modulo p are equal",
				"legendre_symbol(a, p) = -1",
				ByArith(
					prime,
					odd,
					congruent,
					LegendreValues.At(a, p),
					int_congruence.EqOfCongruentSigns.At(p, symbol, minusOne)))
			k, natural := arg.ObtainAs[Nat](
				"a is congruent mod p to a natural number k",
				"∃k:num. k ≡ a (mod int_of_num(p))",
				ByArith(
					prime,
					nat_prime.PrimeAtLeastTwo.At(p),
					int_congruence.NaturalRepresentative.At(a, arg.TermAs[Int]("p"))))
			arg.Take(k)
			arg.Show(
				"k has a's symbol",
				By(Normalized, nonresidue, natural, LegendreCongruent.At(arg.TermAs[Int]("k"), a, p)))
		})

		return ctx.Theorem(headline, func(arg *Argument, p *Expr[Nat], prime, odd Fact) {
			arg.Show(
				"the integers modulo p are a field with p elements",
				By(
					prime,
					odd,
					finite_field.PrimeFieldOn.At(p),
					finite_field.FiniteFieldDef,
					At(
						inField,
						arg.TermAs[FieldOps[Set[Int]]](
							"ideal_quotient_field(int_ring, ideal_span(int_ring, {int_of_num(p)}))"),
						p)))
		})
	}),
})}

// LegendreSumZero — for an odd prime p the Legendre symbols of the residues
// below p add up to 0. Take a nonresidue e. Multiplying by e and reducing
// mod p permutes the residues below p, e being prime to p, so the sum is
// unchanged when each a is replaced by the residue of e·a; that residue's
// symbol is (e/p)(a/p) = −(a/p). The sum is therefore its own negative.
var LegendreSumZero = legendreSumZeroThm{family.Add(registry.ProofEntry{
	Name: "LegendreSumZero",
	Key:  "prop_bde065981155cec",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "Σ_{a<p} legendre_symbol(a, p) = 0",
		Abbrev: Abbrev{
			{Name: "S", Text: "Σ_{a<p} legendre_symbol(a, p)"},
		},
	}, func(arg *Argument, p *Expr[Nat], prime, odd Fact) {
		e, nonresidue := arg.UnpackAs[Nat](GroupPremises(prime, odd, NonresidueExists.At(p)), "e")
		notDivides := arg.Have(
			"p does not divide e, whose symbol is not 0",
			"¬(p ∣ e)",
			ByArith(
				nonresidue,
				LegendreSymbolDef.At(arg.TermAs[Int]("e"), p),
				int_divides.OfNumDivides.At(p, e)))
		coprime := arg.Have(
			"so e is prime to p",
			"nat_coprime(e, p)",
			By(
				Normalized,
				prime,
				notDivides,
				nat_prime.PrimeCoprimeIffNotDivides.At(p),
				nat_gcd.CoprimeSym.At(e, p)))
		into := arg.Have(
			"the residue of e·a lies below p",
			"∀a:num. a < p ⇒ rem(e * a, p) < p",
			ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p), nat_div_mod.Division))
		injective := arg.Have(
			"and the residues of e·x and e·y agree only when x = y",
			"injective_on({a:num | a < p}, λa:num. rem(e * a, p))",
			Derive(func(b *Argument) {
				b.Do(Unfold(functions.InjectiveOnDef))
				x, y := b.FixAs[Nat]("x"), b.FixAs[Nat]("y")
				given := b.Assume()
				b.Show(
					"e·x ≡ e·y cancels to x ≡ y, e being prime to p, "+
						"and two numbers below p with one residue are equal",
					By(
						coprime,
						given,
						nat_congruence.CongDef.At(b.TermAs[Nat]("e * x"), b.TermAs[Nat]("e * y"), p),
						nat_congruence.CongDef.At(x, y, p),
						nat_congruence.MulCancel.At(e, x, y, p),
						nat_div_mod.ModInjectiveBelow.At(x, y, p)))
			}))
		flips := arg.Have(
			"the residue of e·a has symbol (e/p)(a/p) = −(a/p)",
			"∀a:num. legendre_symbol(rem(e * a, p), p) = -legendre_symbol(a, p)",
			Derive(func(b *Argument) {
				a := b.FixAs[Nat]("a")
				ea := b.TermAs[Nat]("e * a")
				residue := b.Have(
					"the residue of e·a is congruent to e·a",
					"rem(e * a, p) ≡ e * int_of_num(a) (mod int_of_num(p))",
					By(
						nat_congruence.ResidueCongruent.At(ea, p),
						int_congruence.OfNumCongruent.At(b.TermAs[Nat]("rem(e * a, p)"), ea, p),
						int_embed.OfNumMul.At(e, a)))
				b.Show(
					"congruent integers share a symbol, and the symbol is multiplicative",
					ByArith(
						prime,
						odd,
						Scaled(b.TermAs[Int]("legendre_symbol(a, p)"), nonresidue),
						residue,
						LegendreCongruent.At(
							b.TermAs[Int]("rem(e * a, p)"),
							b.TermAs[Int]("&e * &a"),
							p),
						LegendreMul.At(b.TermAs[Int]("e"), b.TermAs[Int]("a"), p)))
			}))
		total := arg.BigOpAs[Nat, Int]("«S»")
		multiplyByE := arg.TermAs[Fun[Nat, Nat]]("λa:num. rem(e * a, p)")
		finite := num_segment.FiniteBelowStrict.At(p)
		ownNegative := arg.Have(
			"multiplying by e reorders the sum and reverses every symbol",
			"«S» = -«S»",
			CalcEq(
				Leg(
					arg.TermAs[Int]("Σ_{a<p} legendre_symbol(rem(e * a, p), p)"),
					"a ↦ rem(e·a, p) is an injective self-map of the residues below p, which does not move a sum",
					Unfold(int_sum.IntSumDef),
					By(
						into,
						injective,
						finite,
						monoidal.Injection.Read(int_real_lift.MonoidalAdd).At(total.Summand(), multiplyByE, total.Range()),
						functions.ComposeApply.At(total.Summand(), multiplyByE))),
				Leg(
					arg.TermAs[Int]("Σ_{a<p} -legendre_symbol(a, p)"),
					"each symbol changes sign",
					By(flips)),
				FinalLeg(
					"and negation, which keeps 0 and carries a sum to the sum of the negatives, comes out of the sum",
					Unfold(int_sum.IntSumDef),
					By(
						finite,
						int_real_lift.MonoidalAdd,
						int_real_lift.NeutralAdd,
						int_real_lift.NegZero,
						int_real_lift.NegAdd,
						monoidal.Homomorphic.Read(int_real_lift.MonoidalAdd).At(
							arg.TermAs[Op[Int]]("int_add"),
							arg.TermAs[Fun[Int, Int]]("λu:int. -u"),
							total.Range(),
							total.Summand())))))
		arg.Show(
			"an integer equal to its own negative is 0",
			ByArith(ownNegative))
	}),
})}
