// gauss_sum.go — the Gauss sum's identities. A sum over the residues below p
// may be taken in any order, so the twisted sum Σ_a (a/p) ζ^(ak) is (k/p)
// times the Gauss sum. In characteristic q the q-th power map fixes the
// integers' images and passes through a sum, so the q-th power of the Gauss
// sum is (q/p) times the Gauss sum; and the square of the Gauss sum, a double
// sum of powers of ζ, is (−1/p)·p.

package gauss_sum

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/roots_of_unity"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/quadratic_residue"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// TwistedGaussSum — for a p-th root of unity ζ, p an odd prime, the twisted
// sum Σ_{a<p} (a/p) ζ^(ak) is (k/p) times the Gauss sum. When p divides k
// every ζ^(ak) is one, so the sum is the image of Σ_{a<p} (a/p) = 0, and
// (k/p) = 0. Otherwise (a/p) = (k/p)·(ak mod p / p), since
// (ak/p) = (a/p)(k/p) and (k/p)² = 1, and ζ^(ak) = ζ^(ak mod p); and
// a ↦ ak mod p permutes the residues below p, so the sum is (k/p) times the
// Gauss sum.
var TwistedGaussSum = twistedGaussSumThm{family.Add(registry.ProofEntry{
	Name: "TwistedGaussSum",
	Key:  "prop_d777bb7cf43538e1",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀ζ:A. ∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"ζ ∈ F.carrier",
			"monoid_pow(F.mul, F.one, ζ, p) = F.one",
		},
		Conclusion: "module_sum(F.add, " +
			"    F.zero, " +
			"    {a:num | a < p}, " +
			"    λa:num. «χ»(a) * monoid_pow(F.mul, F.one, ζ, a * k)) = " +
			"«χ»(k) * gauss_sum(F, ζ, p)",
	}, func(
		arg *Argument,
		F field.FieldFact[on.F],
		ζ *Expr[A],
		p, k *Expr[Nat],
		primeP, oddP, ζIn, root Fact,
	) {
		ring := field.RingOn.Read(F)
		powers := comm_ring.MulMonoidOn.Read(ring)
		ζm := arg.MemberOf[on.F](ζ, ζIn)
		below := arg.TermAs[Set[Nat]]("{a:num | a < p}")
		symbolK := arg.TermAs[Int]("legendre_symbol(k, p)")
		imageK := arg.MemberOf[on.F](
			arg.TermAs[A]("«χ»(k)"),
			characteristic_zero.IntegerMapInCarrier.Read(ring).At(symbolK))
		termIn := arg.Have(
			"each term (a/p)·ζᵃ of the Gauss sum lies in F",
			"∀a:num. «χ»(a) * monoid_pow(F.mul, F.one, ζ, a) ∈ F.carrier",
			By(
				comm_ring.MulIn.Read(ring),
				characteristic_zero.IntegerMapInCarrier.Read(ring),
				comm_monoid.PowIn.Read(powers),
				ζm))
		terms := arg.TermAs[Fun[Nat, A]]("λa:num. «χ»(a) * monoid_pow(F.mul, F.one, ζ, a)")
		arg.Cases(arg.Term("p ∣ k"))
		arg.When(
			"p divides k: every ζ^(ak) is one, the symbols sum to zero, and (k/p) = 0",
			func(b *Argument, divides Fact) {
				m, multiple := b.ObtainAs[Nat](
					"k is a multiple of p",
					"∃m:num. k = p * m",
					By(divides, nat_divides.DividesFactor.At(p, k)))
				unity := b.Have(
					"so ζᵏ = (ζᵖ)ᵐ = 1",
					"monoid_pow(F.mul, F.one, ζ, k) = F.one",
					By(
						Normalized,
						multiple,
						root,
						comm_monoid.PowPowOn.Read(powers).At(ζm, p, m),
						comm_monoid.IdentityPowOn.Read(powers).At(m)))
				termOne := b.Have(
					"each term is (a/p), ζ^(ak) being (ζᵏ)ᵃ = 1",
					"∀a:num. «χ»(a) * monoid_pow(F.mul, F.one, ζ, a * k) = «χ»(a)",
					Derive(func(c *Argument) {
						a := c.FixAs[Nat]("a")
						image := c.MemberOf[on.F](
							c.TermAs[A]("«χ»(a)"),
							characteristic_zero.IntegerMapInCarrier.Read(ring).At(c.TermAs[Int]("legendre_symbol(a, p)")))
						c.Show(
							"(ζᵏ)ᵃ = 1ᵃ = 1",
							By(
								unity,
								comm_monoid.PowPowOn.Read(powers).At(ζm, k, a),
								nat_arith.MulSym.At(a, k),
								comm_monoid.IdentityPowOn.Read(powers).At(a),
								comm_monoid.RightIdentityOn.Read(powers).At(image)))
					}))
				symbolZero := b.Have(
					"p divides k, so (k/p) = 0",
					"legendre_symbol(k, p) = 0",
					By(
						divides,
						int_divides.OfNumDivides.At(p, k),
						quadratic_residue.LegendreSymbolDef.At(b.TermAs[Int]("k"), p)))
				gauss := b.MemberOf[on.F](b.TermAs[A]("gauss_sum(F, ζ, p)"), b.Have(
					"the Gauss sum lies in F",
					"gauss_sum(F, ζ, p) ∈ F.carrier",
					Unfold(GaussSumDef),
					By(
						termIn,
						module.ModuleSumIn.Read(module.RegularModuleOn.Read(ring)).At(below, terms),
						num_segment.FiniteBelowStrict.At(p))))
				homomorphism := characteristic_zero.IntegerMapHomomorphism.Read(ring)
				b.Show(
					"the sum is the image of Σ (a/p) = 0, and (k/p)·g = 0·g",
					CalcEq(
						Leg(
							b.TermAs[A]("module_sum(F.add, F.zero, {a:num | a < p}, «χ»)"),
							"term by term, the sum is Σ (a/p) read in F",
							By(termOne, module.ModuleSumCongruence)),
						Leg(
							b.TermAs[A]("integer_map(field_ring(F), Σ_{a<p} legendre_symbol(a, p))"),
							"the integers' map carries the integer sum to the sum of the images",
							By(
								characteristic_zero.IntegerMapSum.Read(ring).At(
									below,
									b.TermAs[Fun[Nat, Int]]("λa:num. legendre_symbol(a, p)")),
								num_segment.FiniteBelowStrict.At(p))),
						Leg(
							b.TermAs[A]("F.zero"),
							"the symbols sum to zero, and the map keeps zero",
							By(
								primeP,
								oddP,
								quadratic_residue.LegendreSumZero.At(p),
								ring_homomorphism.MapZero.Read(homomorphism))),
						FinalLeg(
							"(k/p) is zero, and so is its product with the Gauss sum",
							By(
								Normalized,
								symbolZero,
								ring_homomorphism.MapZero.Read(homomorphism),
								comm_ring.MulLeftZeroOn.Read(ring).At(gauss)))))
			})
		arg.Otherwise(
			"p does not divide k: (a/p) = (k/p)·(ak mod p / p), and a ↦ ak mod p permutes the residues",
			func(b *Argument, notDivides Fact) {
				pNonzero := b.Have(
					"p is not zero",
					"p ≠ 0",
					ByArith(primeP, nat_prime.PrimeAtLeastTwo.At(p)))
				unit := b.Have(
					"p does not divide k, so (k/p) is 1 or −1",
					"legendre_symbol(&k, p) = 1 ∨ legendre_symbol(k, p) = -1",
					By(
						notDivides,
						int_divides.OfNumDivides.At(p, k),
						quadratic_residue.LegendreSymbolDef.At(b.TermAs[Int]("k"), p)))
				squareOne := b.Have(
					"so (k/p)² = 1",
					"legendre_symbol(&k, p) * legendre_symbol(k, p) = 1",
					unit.SplitDisj(
						LeftHolds(
							"(k/p) = 1",
							Given(func(c *Argument, one Fact) {
								c.Show(
									"1 · 1 = 1",
									ByArith(one))
							})),
						RightHolds(
							"(k/p) = −1",
							Given(func(c *Argument, minusOne Fact) {
								c.Show(
									"(−1) · (−1) = 1",
									ByArith(minusOne))
							}))))
				twist := b.Have(
					"(a/p) = (k/p)·(ak mod p / p)",
					"∀a:num. legendre_symbol(a, p) = legendre_symbol(&k, p) * legendre_symbol(rem(a * k, p), p)",
					Derive(func(c *Argument) {
						a := c.FixAs[Nat]("a")
						product := c.TermAs[Nat]("a * k")
						residue := c.TermAs[Nat]("rem(a * k, p)")
						congruent := c.Have(
							"ak mod p is congruent to a·k",
							"rem(a * k, p) ≡ &a * k (mod &p)",
							By(
								nat_congruence.ResidueCongruent.At(product, p),
								int_congruence.OfNumCongruent.At(residue, product, p),
								int_embed.OfNumMul.At(a, k)))
						c.Show(
							"so (ak mod p / p) = (a/p)(k/p); multiplied by (k/p), whose square is one, it gives (a/p)",
							ByArith(
								primeP,
								oddP,
								congruent,
								Scaled(c.TermAs[Int]("legendre_symbol(a, p)"), squareOne),
								Scaled(symbolK, quadratic_residue.LegendreCongruent.At(
									c.TermAs[Int]("rem(a * k, p)"),
									c.TermAs[Int]("&a * k"),
									p)),
								Scaled(symbolK, quadratic_residue.LegendreMul.At(
									c.TermAs[Int]("a"),
									c.TermAs[Int]("k"),
									p))))
					}))
				period := b.Have(
					"a power of ζ depends only on its exponent mod p, ζᵖ being one",
					"∀n:num. monoid_pow(F.mul, F.one, ζ, n) = monoid_pow(F.mul, F.one, ζ, rem(n, p))",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						quotient := c.TermAs[Nat]("div(n, p)")
						remainder := c.TermAs[Nat]("rem(n, p)")
						c.Show(
							"divide n by p",
							CalcEq(
								Leg(
									c.TermAs[A]("monoid_pow(F.mul, F.one, ζ, div(n, p) * p + rem(n, p))"),
									"n = div(n, p)·p + rem(n, p)",
									By(Normalized, pNonzero, nat_div_mod.Division.At(n, p))),
								Leg(
									c.TermAs[A](
										"monoid_pow(F.mul, F.one, monoid_pow(F.mul, F.one, ζ, p), div(n, p)) * "+
											"monoid_pow(F.mul, F.one, ζ, rem(n, p))"),
									"split the exponent, ζ^(div(n, p)·p) being (ζᵖ)^div(n, p)",
									By(
										comm_monoid.PowAddOn.Read(powers).At(ζm, c.TermAs[Nat]("div(n, p) * p"), remainder),
										comm_monoid.PowPowOn.Read(powers).At(ζm, p, quotient),
										nat_arith.MulSym.At(quotient, p))),
								FinalLeg(
									"ζᵖ is one, and so is every power of it",
									By(
										root,
										comm_monoid.IdentityPowOn.Read(powers).At(quotient),
										comm_monoid.LeftIdentityOn.Read(powers).At(comm_monoid.PowIn.Read(powers).At(ζm, remainder))))))
					}))
				termTwist := b.Have(
					"(a/p)·ζ^(ak) = (k/p)·((ak mod p / p)·ζ^(ak mod p)), the twist read in F",
					"∀a:num. "+
						"    «χ»(a) * monoid_pow(F.mul, F.one, ζ, a * k) = "+
						"    «χ»(k) * («χ»(rem(a * k, p)) * monoid_pow(F.mul, F.one, ζ, rem(a * k, p)))",
					Derive(func(c *Argument) {
						a := c.FixAs[Nat]("a")
						residue := c.TermAs[Nat]("rem(a * k, p)")
						residueSymbol := c.TermAs[Int]("legendre_symbol(rem(a * k, p), p)")
						residueImage := c.MemberOf[on.F](
							c.TermAs[A]("«χ»(rem(a * k, p))"),
							characteristic_zero.IntegerMapInCarrier.Read(ring).At(residueSymbol))
						c.Show(
							"ζ^(ak) = ζ^(ak mod p); the integers' map is multiplicative, "+
								"every integer lying in the integer ring; then regroup",
							By(
								twist.At(a),
								period.At(c.TermAs[Nat]("a * k")),
								ring_homomorphism.MapMul.Read(characteristic_zero.IntegerMapHomomorphism.Read(ring)).AsFact().At(
									symbolK,
									residueSymbol),
								set_basic.InUniv.Inst[Int](),
								comm_monoid.AssocOn.Read(powers).At(
									imageK, residueImage, comm_monoid.PowIn.Read(powers).At(ζm, residue))))
					}))
				twistedIn := b.Have(
					"(k/p) times a term of the Gauss sum lies in F",
					"∀j:num. «χ»(k) * («χ»(j) * monoid_pow(F.mul, F.one, ζ, j)) ∈ F.carrier",
					Derive(func(c *Argument) {
						j := c.FixAs[Nat]("j")
						term := c.MemberOf[on.F](
							c.TermAs[A]("«χ»(j) * monoid_pow(F.mul, F.one, ζ, j)"),
							termIn.At(j))
						c.Show(
							"a product of two members",
							By(comm_ring.MulIn.Read(ring).At(imageK, term)))
					}))
				coprime := b.Have(
					"k is prime to p, which does not divide it",
					"nat_coprime(k, p)",
					By(
						Normalized,
						primeP,
						notDivides,
						nat_prime.PrimeCoprimeIffNotDivides.At(p),
						nat_gcd.CoprimeSym.At(k, p)))
				injective := b.Have(
					"a ↦ ak mod p is injective below p",
					"injective_on({a:num | a < p}, λa:num. rem(a * k, p))",
					Unfold(functions.InjectiveOnDef),
					Derive(func(c *Argument) {
						x := c.FixAs[Nat]("x")
						y := c.FixAs[Nat]("y")
						parts := c.Conjuncts(
							c.Assume(),
							"x lies below p",
							"y lies below p",
							"xk and yk leave one residue mod p")
						congruent := c.Have(
							"so kx ≡ ky (mod p)",
							"k * x ≡ k * y (mod p)",
							By(
								parts[2],
								nat_congruence.CongDef.At(c.TermAs[Nat]("k * x"), c.TermAs[Nat]("k * y"), p),
								nat_arith.MulSym.At(x, k),
								nat_arith.MulSym.At(y, k)))
						cancelled := c.Have(
							"k is prime to p, so it cancels: x ≡ y (mod p)",
							"x ≡ y (mod p)",
							By(coprime, congruent, nat_congruence.MulCancel.At(k, x, y, p)))
						c.Show(
							"two numbers below p congruent mod p are equal",
							By(
								parts[0],
								parts[1],
								cancelled,
								nat_congruence.CongDef.At(x, y, p),
								nat_div_mod.ModInjectiveBelow.At(x, y, p)))
					}))
				b.Show(
					"term by term (a/p)·ζ^(ak) is (k/p) times the term at ak mod p, and reindexing brings out (k/p)",
					CalcEq(
						Leg(
							b.TermAs[A](
								"module_sum(F.add, "+
									"    F.zero, "+
									"    {a:num | a < p}, "+
									"    λa:num. «χ»(k) * («χ»(rem(a * k, p)) * monoid_pow(F.mul, F.one, ζ, rem(a * k, p))))"),
							"term by term, (a/p)·ζ^(ak) = (k/p)·((ak mod p / p)·ζ^(ak mod p))",
							By(termTwist, module.ModuleSumCongruence)),
						Leg(
							b.TermAs[A](
								"module_sum(F.add, "+
									"    F.zero, "+
									"    {a:num | a < p}, "+
									"    λb:num. «χ»(k) * («χ»(b) * monoid_pow(F.mul, F.one, ζ, b)))"),
							"a ↦ ak mod p permutes the residues below p",
							By(
								twistedIn,
								injective,
								pNonzero,
								nat_div_mod.Division,
								module.ModuleSumReindex.Read(comm_ring.AddMonoidOn.Read(ring)).At(
									p,
									b.TermAs[Fun[Nat, Nat]]("λa:num. rem(a * k, p)"),
									b.TermAs[Fun[Nat, A]]("λb:num. «χ»(k) * («χ»(b) * monoid_pow(F.mul, F.one, ζ, b))")))),
						FinalLeg(
							"(k/p) comes out of the sum, which is the Gauss sum",
							Unfold(GaussSumDef),
							By(
								termIn,
								module.ModuleSumSmul.Read(module.RegularModuleOn.Read(ring)).At(below, imageK, terms),
								num_segment.FiniteBelowStrict.At(p)))))
			})
	}),
})}

// GaussSumFrobenius — in characteristic q the q-th power of the Gauss sum is
// (q/p) times the Gauss sum. The q-th power is additive in characteristic q,
// so it passes through the sum; it fixes each (a/p), an integer's image, and
// takes ζᵃ to ζ^(aq). What is left is the twisted Gauss sum at q,
// Σ_a (a/p) ζ^(aq), which is (q/p) times the Gauss sum.
var GaussSumFrobenius = gaussSumFrobeniusThm{family.Add(registry.ProofEntry{
	Name: "GaussSumFrobenius",
	Key:  "prop_381f58bfc1963103",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀ζ:A. ∀p q:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"ring_prime_characteristic(field_ring(F), q)",
			"ζ ∈ F.carrier",
			"monoid_pow(F.mul, F.one, ζ, p) = F.one",
		},
		Conclusion: "monoid_pow(F.mul, F.one, gauss_sum(F, ζ, p), q) = «χ»(q) * gauss_sum(F, ζ, p)",
	}, func(arg *Argument, F field.FieldFact[on.F], ζ *Expr[A], p, q *Expr[Nat],
		primeP, oddP, characteristic, ζIn, root Fact) {
		ring := field.RingOn.Read(F)
		powers := comm_ring.MulMonoidOn.Read(ring)
		ζm := arg.MemberOf[on.F](ζ, ζIn)
		below := arg.TermAs[Set[Nat]]("{a:num | a < p}")
		frobeniusTerm := arg.Have(
			"the q-th power of (a/p)·ζᵃ is (a/p)·ζ^(aq)",
			"∀a:num. "+
				"    monoid_pow(F.mul, F.one, «χ»(a) * monoid_pow(F.mul, F.one, ζ, a), q) = "+
				"    «χ»(a) * monoid_pow(F.mul, F.one, ζ, a * q)",
			Derive(func(b *Argument) {
				a := b.FixAs[Nat]("a")
				symbol := b.TermAs[Int]("legendre_symbol(a, p)")
				image := b.MemberOf[on.F](
					b.TermAs[A]("«χ»(a)"),
					characteristic_zero.IntegerMapInCarrier.Read(ring).At(symbol))
				b.Show(
					"(xy)^q = x^q·y^q; the q-th power fixes (a/p), and (ζᵃ)^q = ζ^(aq)",
					By(
						characteristic,
						finite_field.FrobeniusFixesIntegers.Read(ring).At(q, symbol),
						comm_monoid.MulPowOn.Read(powers).At(image, comm_monoid.PowIn.Read(powers).At(ζm, a), q),
						comm_monoid.PowPowOn.Read(powers).At(ζm, a, q)))
			}))
		termIn := arg.Have(
			"each term (a/p)·ζᵃ lies in F",
			"∀a:num. «χ»(a) * monoid_pow(F.mul, F.one, ζ, a) ∈ F.carrier",
			By(
				comm_ring.MulIn.Read(ring),
				characteristic_zero.IntegerMapInCarrier.Read(ring),
				comm_monoid.PowIn.Read(powers),
				ζm))
		zeroPow := arg.Have(
			"the q-th power fixes zero, the image of the integer 0",
			"monoid_pow(F.mul, F.one, F.zero, q) = F.zero",
			By(
				Normalized,
				characteristic,
				finite_field.FrobeniusFixesIntegers.Read(ring).At(q, arg.TermAs[Int]("0")),
				ring_homomorphism.MapZero.Read(characteristic_zero.IntegerMapHomomorphism.Read(ring))))

		add, zero := arg.TermAs[Op[A]]("F.add"), arg.TermAs[A]("F.zero")
		terms := arg.TermAs[Fun[Nat, A]]("λa:num. «χ»(a) * monoid_pow(F.mul, F.one, ζ, a)")
		arg.Show(
			"the q-th power passes through the sum, which is then the twisted Gauss sum at q",
			CalcEq(
				Leg(
					arg.TermAs[A](
						"module_sum(F.add, "+
							"    F.zero, "+
							"    {a:num | a < p}, "+
							"    λa:num. monoid_pow(F.mul, F.one, «χ»(a) * monoid_pow(F.mul, F.one, ζ, a), q))"),
					"in characteristic q the q-th power is additive and fixes zero, so it passes through the sum",
					Unfold(GaussSumDef),
					By(
						characteristic,
						finite_field.FrobeniusAdditive.Read(ring),
						zeroPow,
						termIn,
						module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(ring)).At(
							add,
							zero,
							arg.TermAs[Fun[A, A]]("λz:A. monoid_pow(F.mul, F.one, z, q)"),
							below,
							terms),
						num_segment.FiniteBelowStrict.At(p))),
				Leg(
					arg.TermAs[A](
						"module_sum(F.add, F.zero, {a:num | a < p}, λa:num. «χ»(a) * monoid_pow(F.mul, F.one, ζ, a * q))"),
					"term by term, the q-th power fixes (a/p) and takes ζᵃ to ζ^(aq)",
					By(frobeniusTerm, module.ModuleSumCongruence)),
				FinalLeg(
					"the twisted Gauss sum at q is (q/p) times the Gauss sum",
					By(primeP, oddP, root, TwistedGaussSum.Read(F).At(ζm, p, q)))))
	}),
})}

// GaussSumSquareDoubleSum — the square of the Gauss sum as a double sum:
// g·g = Σ_{b<p} (b/p) · Σ_{a<p} ζ^(a(b+1)). Multiplying the second factor
// out term by term gives g·(a/p)ζᵃ = ζᵃ·((a/p)·g), and (a/p)·g is the
// twisted sum Σ_b (b/p) ζ^(ba); so g·g = Σ_a Σ_b (b/p) ζ^(a + ba), and
// with the two sums interchanged (b/p) comes out of the inner one.
var GaussSumSquareDoubleSum = gaussSumSquareDoubleSumThm{family.Add(registry.ProofEntry{
	Name: "GaussSumSquareDoubleSum",
	Key:  "prop_e62977f87d447fc9",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀ζ:A. ∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"ζ ∈ F.carrier",
			"monoid_pow(F.mul, F.one, ζ, p) = F.one",
		},
		Conclusion: "gauss_sum(F, ζ, p) * gauss_sum(F, ζ, p) = " +
			"module_sum(F.add, " +
			"    F.zero, " +
			"    {b:num | b < p}, " +
			"    λb:num. " +
			"        «χ»(b) * " +
			"        module_sum(F.add, " +
			"            F.zero, " +
			"            {a:num | a < p}, " +
			"            λa:num. monoid_pow(F.mul, F.one, ζ, a * (b + 1))))",
		Abbrev: Abbrev{
			{Name: "row", Text: "λa:num. " +
				"    module_sum(F.add, " +
				"        F.zero, " +
				"        {b:num | b < p}, " +
				"        λb:num. «χ»(b) * monoid_pow(F.mul, F.one, ζ, a * (b + 1)))"},
			{Name: "column", Text: "λb:num. " +
				"    module_sum(F.add, " +
				"        F.zero, " +
				"        {a:num | a < p}, " +
				"        λa:num. «χ»(b) * monoid_pow(F.mul, F.one, ζ, a * (b + 1)))"},
		},
	}, func(
		arg *Argument,
		F field.FieldFact[on.F],
		ζ *Expr[A],
		p *Expr[Nat],
		primeP, oddP, ζIn, root Fact,
	) {
		ring := field.RingOn.Read(F)
		powers := comm_ring.MulMonoidOn.Read(ring)
		regular := module.RegularModuleOn.Read(ring)
		ζm := arg.MemberOf[on.F](ζ, ζIn)
		below := arg.TermAs[Set[Nat]]("{a:num | a < p}")
		finite := num_segment.FiniteBelowStrict.At(p)
		termIn := arg.Have(
			"each (b/p)·ζⁿ lies in F",
			"∀b n:num. «χ»(b) * monoid_pow(F.mul, F.one, ζ, n) ∈ F.carrier",
			By(
				comm_ring.MulIn.Read(ring),
				characteristic_zero.IntegerMapInCarrier.Read(ring),
				comm_monoid.PowIn.Read(powers),
				ζm))
		terms := arg.TermAs[Fun[Nat, A]]("λa:num. «χ»(a) * monoid_pow(F.mul, F.one, ζ, a)")
		gauss := arg.MemberOf[on.F](arg.TermAs[A]("gauss_sum(F, ζ, p)"), arg.Have(
			"so does the Gauss sum",
			"gauss_sum(F, ζ, p) ∈ F.carrier",
			Unfold(GaussSumDef),
			By(termIn, module.ModuleSumIn.Read(regular).At(below, terms), finite)))
		combine := arg.Have(
			"ζᵃ·((b/p)·ζ^(ba)) = (b/p)·ζ^(a(b+1))",
			"∀a b:num. "+
				"    monoid_pow(F.mul, F.one, ζ, a) * («χ»(b) * monoid_pow(F.mul, F.one, ζ, b * a)) = "+
				"    «χ»(b) * monoid_pow(F.mul, F.one, ζ, a * (b + 1))",
			Derive(func(c *Argument) {
				a := c.FixAs[Nat]("a")
				c.FixAs[Nat]("b")
				product := c.TermAs[Nat]("b * a")
				image := c.MemberOf[on.F](
					c.TermAs[A]("«χ»(b)"),
					characteristic_zero.IntegerMapInCarrier.Read(ring).At(c.TermAs[Int]("legendre_symbol(b, p)")))
				exponent := c.Have(
					"a(b + 1) = a + ba",
					"a * (b + 1) = a + b * a",
					ByArith())
				c.Show(
					"regroup, and the powers of ζ multiply by adding their exponents",
					CalcEq(
						Leg(
							c.TermAs[A]("«χ»(b) * (monoid_pow(F.mul, F.one, ζ, a) * monoid_pow(F.mul, F.one, ζ, b * a))"),
							"regroup the three factors",
							ByArith(
								F,
								image,
								comm_monoid.PowIn.Read(powers).At(ζm, a),
								comm_monoid.PowIn.Read(powers).At(ζm, product))),
						FinalLeg(
							"ζᵃ·ζ^(ba) = ζ^(a + ba), and a + ba = a(b + 1)",
							By(exponent, comm_monoid.PowAddOn.Read(powers).At(ζm, a, product)))))
			}))
		row := arg.Have(
			"the a-th term g·(a/p)ζᵃ is ζᵃ times the twisted sum (a/p)·g, a sum over b",
			"∀a:num. gauss_sum(F, ζ, p) * («χ»(a) * monoid_pow(F.mul, F.one, ζ, a)) = «row»(a)",
			Derive(func(c *Argument) {
				a := c.FixAs[Nat]("a")
				power := comm_monoid.PowIn.Read(powers).At(ζm, a)
				image := c.MemberOf[on.F](
					c.TermAs[A]("«χ»(a)"),
					characteristic_zero.IntegerMapInCarrier.Read(ring).At(c.TermAs[Int]("legendre_symbol(a, p)")))
				c.Show(
					"regroup, read (a/p)·g as the twisted sum, and let ζᵃ enter it",
					CalcEq(
						Leg(
							c.TermAs[A](
								"monoid_pow(F.mul, F.one, ζ, a) * "+
									"module_sum(F.add, F.zero, {b:num | b < p}, λb:num. «χ»(b) * monoid_pow(F.mul, F.one, ζ, b * a))"),
							"g·(a/p)ζᵃ = ζᵃ·((a/p)·g), and (a/p)·g is the twisted sum Σ_b (b/p) ζ^(ba)",
							ByArith(F, gauss, image, power, primeP, oddP, root, TwistedGaussSum.Read(F).At(ζm, p, a))),
						Leg(
							c.TermAs[A](
								"module_sum(F.add, "+
									"    F.zero, "+
									"    {b:num | b < p}, "+
									"    λb:num. monoid_pow(F.mul, F.one, ζ, a) * («χ»(b) * monoid_pow(F.mul, F.one, ζ, b * a)))"),
							"ζᵃ passes into the sum",
							By(
								termIn,
								module.ModuleSumSmul.Read(regular).At(
									below,
									power,
									c.TermAs[Fun[Nat, A]]("λb:num. «χ»(b) * monoid_pow(F.mul, F.one, ζ, b * a)")),
								finite)),
						FinalLeg(
							"term by term, ζᵃ·(b/p)ζ^(ba) = (b/p)ζ^(a(b+1))",
							By(combine, module.ModuleSumCongruence))))
			}))
		factor := arg.Have(
			"(b/p) comes out of the sum over a",
			"∀b:num. "+
				"    «column»(b) = "+
				"    «χ»(b) * "+
				"    module_sum(F.add, F.zero, {a:num | a < p}, λa:num. monoid_pow(F.mul, F.one, ζ, a * (b + 1)))",
			Derive(func(c *Argument) {
				c.FixAs[Nat]("b")
				image := c.MemberOf[on.F](
					c.TermAs[A]("«χ»(b)"),
					characteristic_zero.IntegerMapInCarrier.Read(ring).At(c.TermAs[Int]("legendre_symbol(b, p)")))
				c.Show(
					"a factor passes out of a sum",
					By(
						ζm,
						comm_monoid.PowIn.Read(powers),
						module.ModuleSumSmul.Read(regular).At(
							below,
							image,
							c.TermAs[Fun[Nat, A]]("λa:num. monoid_pow(F.mul, F.one, ζ, a * (b + 1))")),
						finite))
			}))
		arg.Show(
			"multiply out, read each (a/p)·g as a twisted sum, and sum over a first",
			CalcEq(
				Leg(
					arg.TermAs[A](
						"module_sum(F.add, "+
							"    F.zero, "+
							"    {a:num | a < p}, "+
							"    λa:num. gauss_sum(F, ζ, p) * («χ»(a) * monoid_pow(F.mul, F.one, ζ, a)))"),
					"unfold the second factor alone, g = Σ_a (a/p)ζᵃ, and multiply g into it term by term",
					By(
						termIn,
						GaussSumDef.At(arg.TermAs[FieldOps[A]]("F"), ζ, p),
						module.ModuleSumSmul.Read(regular).At(below, gauss, terms),
						finite)),
				Leg(
					arg.TermAs[A]("module_sum(F.add, F.zero, {a:num | a < p}, «row»)"),
					"term by term, g·(a/p)ζᵃ is Σ_b (b/p) ζ^(a(b+1))",
					By(row, module.ModuleSumCongruence)),
				Leg(
					arg.TermAs[A]("module_sum(F.add, F.zero, {b:num | b < p}, «column»)"),
					"the two sums interchange",
					By(
						termIn,
						module.ModuleSumSwap.Read(regular).At(
							below,
							below,
							arg.TermAs[Fun2[Nat, Nat, A]]("λa:num. λb:num. «χ»(b) * monoid_pow(F.mul, F.one, ζ, a * (b + 1))")),
						finite)),
				FinalLeg(
					"(b/p) comes out of each inner sum",
					By(factor, module.ModuleSumCongruence))))
	}),
})}

// GaussSumSquare — the square of the quadratic Gauss sum is (−1/p)·p. In the
// double sum g·g = Σ_b (b/p) · Σ_a ζ^(a(b+1)) the power sum is p when p
// divides b + 1 and zero otherwise, ζ being a p-th root of unity other than
// one; below p only b = p − 1 has p dividing b + 1, so g·g = (p − 1 / p)·p,
// and p − 1 ≡ −1 (mod p).
var GaussSumSquare = gaussSumSquareThm{family.Add(registry.ProofEntry{
	Name: "GaussSumSquare",
	Key:  "prop_b88d9f1b2f06c477",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀ζ:A. ∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"ζ ∈ F.carrier",
			"ζ ≠ F.one",
			"monoid_pow(F.mul, F.one, ζ, p) = F.one",
		},
		Conclusion: "gauss_sum(F, ζ, p) * gauss_sum(F, ζ, p) = " +
			"integer_map(field_ring(F), legendre_symbol(-1, p) * p)",
	}, func(
		arg *Argument,
		F field.FieldFact[on.F],
		ζ *Expr[A],
		p *Expr[Nat],
		primeP, oddP, ζIn, nontrivial, root Fact,
	) {
		ring := field.RingOn.Read(F)
		regular := module.RegularModuleOn.Read(ring)
		ζm := arg.MemberOf[on.F](ζ, ζIn)
		below := arg.TermAs[Set[Nat]]("{b:num | b < p}")
		powerSums := arg.Have(
			"the power sum Σ_a ζ^(a(b+1)) is p when p divides b + 1 and zero otherwise",
			"∀b:num. "+
				"    module_sum(F.add, "+
				"        F.zero, "+
				"        {a:num | a < p}, "+
				"        λa:num. monoid_pow(F.mul, F.one, ζ, a * (b + 1))) = "+
				"    COND(p ∣ b + 1, monoid_pow(F.add, F.zero, F.one, p), F.zero)",
			Derive(func(c *Argument) {
				c.FixAs[Nat]("b")
				c.Show(
					"ζ is a p-th root of unity other than one",
					By(
						primeP,
						nontrivial,
						root,
						roots_of_unity.RootOfUnityPowerSum.Read(F).At(ζm, p, c.TermAs[Nat]("b + 1"))))
			}))
		termIn := arg.Have(
			"each term (b/p)·(p or 0) lies in F",
			"∀b:num. «χ»(b) * COND(p ∣ b + 1, monoid_pow(F.add, F.zero, F.one, p), F.zero) ∈ F.carrier",
			By(
				comm_ring.MulIn.Read(ring),
				characteristic_zero.IntegerMapInCarrier.Read(ring),
				comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)),
				comm_ring.OneIn.Read(ring),
				comm_ring.ZeroIn.Read(ring)))
		vanish := arg.Have(
			"below p, the terms off b = p − 1 vanish",
			Statement{
				Binders: "∀b:num.",
				Hypotheses: []string{
					"b < p",
					"b ≠ p - 1",
				},
				Conclusion: "«χ»(b) * COND(p ∣ b + 1, monoid_pow(F.add, F.zero, F.one, p), F.zero) = F.zero",
			},
			Derive(func(c *Argument) {
				c.FixAs[Nat]("b")
				between := c.Assume()
				notDivides := c.Have(
					"0 < b + 1 < p, so p does not divide b + 1",
					"¬(p ∣ b + 1)",
					ByArith(between, nat_divides.DividesLessEq.At(p, c.TermAs[Nat]("b + 1"))))
				image := c.MemberOf[on.F](
					c.TermAs[A]("«χ»(b)"),
					characteristic_zero.IntegerMapInCarrier.Read(ring).At(c.TermAs[Int]("legendre_symbol(b, p)")))
				c.Show(
					"the condition fails, and (b/p)·0 = 0",
					By(notDivides, comm_ring.MulRightZeroOn.Read(ring).At(image)))
			}))
		bounds := arg.Have(
			"p − 1 lies below p, and its successor is p",
			"p - 1 < p ∧ p - 1 + 1 = p",
			ByArith(primeP, nat_prime.PrimeAtLeastTwo.At(p)))
		minusOne := arg.Have(
			"p − 1 ≡ −1 (mod p)",
			"p - 1 ≡ -1 (mod &p)",
			ByArith(
				bounds,
				int_congruence.CongruentIffMultiple.At(
					arg.TermAs[Int]("p - 1"),
					arg.TermAs[Int]("-1"),
					arg.TermAs[Int]("p"))))
		symbol := arg.TermAs[Int]("legendre_symbol(-1, p)")
		arg.Show(
			"in the double sum only b = p − 1 survives, with the power sum p",
			CalcEq(
				Leg(
					arg.TermAs[A](
						"module_sum(F.add, "+
							"    F.zero, "+
							"    {b:num | b < p}, "+
							"    λb:num. "+
							"        «χ»(b) * "+
							"        module_sum(F.add, "+
							"            F.zero, "+
							"            {a:num | a < p}, "+
							"            λa:num. monoid_pow(F.mul, F.one, ζ, a * (b + 1))))"),
					"the square as a double sum",
					By(primeP, oddP, root, GaussSumSquareDoubleSum.Read(F).At(ζm, p))),
				Leg(
					arg.TermAs[A](
						"module_sum(F.add, "+
							"    F.zero, "+
							"    {b:num | b < p}, "+
							"    λb:num. «χ»(b) * COND(p ∣ b + 1, monoid_pow(F.add, F.zero, F.one, p), F.zero))"),
					"term by term, the power sum is p or zero",
					By(powerSums, module.ModuleSumCongruence)),
				Leg(
					arg.TermAs[A]("«χ»(p - 1) * COND(p ∣ p - 1 + 1, monoid_pow(F.add, F.zero, F.one, p), F.zero)"),
					"only the term at b = p − 1 survives",
					By(
						termIn,
						vanish,
						bounds,
						module.ModuleSumSingle.Read(regular).At(
							below,
							arg.TermAs[Nat]("p - 1"),
							arg.TermAs[Fun[Nat, A]](
								"λb:num. «χ»(b) * COND(p ∣ b + 1, monoid_pow(F.add, F.zero, F.one, p), F.zero)")),
						num_segment.FiniteBelowStrict.At(p))),
				Leg(
					arg.TermAs[A]("«χ»(p - 1) * monoid_pow(F.add, F.zero, F.one, p)"),
					"p divides (p − 1) + 1 = p",
					By(bounds, nat_divides.DividesRefl.At(p))),
				FinalLeg(
					"(p − 1 / p) = (−1/p); the integers' map is multiplicative, "+
						"every integer lying in the integer ring, and takes p to p·1",
					By(
						minusOne,
						set_basic.InUniv.Inst[Int](),
						quadratic_residue.LegendreCongruent.At(
							arg.TermAs[Int]("p - 1"),
							arg.TermAs[Int]("-1"),
							p),
						ring_homomorphism.MapMul.Read(characteristic_zero.IntegerMapHomomorphism.Read(ring)).AsFact().At(
							symbol,
							arg.TermAs[Int]("p")),
						characteristic_zero.IntegerMapOfNum.Read(ring).At(p)))))
	}),
})}
