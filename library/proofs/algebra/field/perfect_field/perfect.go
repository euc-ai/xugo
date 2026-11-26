// perfect.go — perfect fields in characteristic p, read through the p-th power map.

package perfect_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ZeroDerivativeCoefficients — over a field of characteristic p, a
// polynomial with zero derivative has its coefficients on the multiples of
// p. The coefficient of the derivative below i is the numeral i times
// f(i). Off the multiples of p the Chinese remainder theorem gives a
// multiple of i that is one more than a multiple of p, so the numeral i is
// invertible in the field and f(i) is zero.
var ZeroDerivativeCoefficients = zeroDerivativeCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "ZeroDerivativeCoefficients",
	Key:  "prop_fc7f3f8d674bc739",
	Reading: "That f lies over the carrier is load-bearing: a term off " +
		"the carrier is multiplied by the numeral with no law to cancel it.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:num. ∀f:(num → A). ∀i:num.",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(F), p)",
			"polynomial_over(F.carrier, f)",
			"polynomial_derivative(f) = vec_zero",
			"¬(p ∣ i)",
		},
		Conclusion: "f(i) = F.zero",
		Abbrev: Abbrev{
			{Name: "numeral", Text: "λn:num. monoid_pow(F.add, F.zero, F.one, n)"},
		},
	},
		func(
			a *Argument,
			F field.FieldFact[on.F],
			p *Expr[Nat],
			characteristic Fact,
			f *Arrow[Nat, A],
			over, derivative Fact,
			i *Expr[Nat],
			notMultiple Fact,
		) {
			ring := field.RingOn.Read(F)
			additive := comm_ring.AddMonoidOn.Read(ring)
			zero, one := a.TermAs[A]("F.zero"), a.TermAs[A]("F.one")
			oneMember := a.MemberOf[on.F](one, comm_ring.OneIn.Read(ring))
			prime := a.Unfolded(characteristic, finite_field.PrimeCharacteristicDef)
			coefficients := a.Have(
				"every coefficient of f lies in the field",
				"∀k:num. f(k) ∈ F.carrier",
				By(over, polynomial.PolynomialOverDef))
			numerals := a.Have(
				"every numeral lies in the field",
				"∀n:num. «numeral»(n) ∈ F.carrier",
				a.ForEach(
					func(n *Expr[Nat]) Action { return By(comm_monoid.PowIn.Read(additive).At(oneMember, n)) }))
			u, v, bezout := a.Obtain2As[Nat, Nat](
				"a multiple of i is one more than a multiple of p",
				"∃u v:num. i * u = v * p + 1",
				Derive(func(b *Argument) {
					oneIndex, zeroIndex := b.TermAs[Nat]("1"), b.TermAs[Nat]("0")
					x, residues := b.ObtainAs[Nat](
						"p is coprime to i, so the Chinese remainder theorem gives x ≡ 1 mod p and x ≡ 0 mod i",
						"∃x:num. x ≡ 1 (mod p) ∧ x ≡ 0 (mod i)",
						By(
							prime,
							notMultiple,
							nat_prime.PrimeCoprimeIffNotDivides,
							nat_congruence.ChineseRemainder.At(p, i, oneIndex, zeroIndex)))
					q, multiple := b.ObtainAs[Nat](
						"x is a multiple of i",
						"∃q:num. x = q * i",
						By(
							Normalized,
							residues,
							nat_congruence.CongDef.At(x, zeroIndex, i),
							nat_div_mod.ZeroMod.At(i),
							nat_div_mod.ModEqZero.At(x, i)))
					b.Take(q)
					b.Take(b.TermAs[Nat]("div(x, p)"))
					b.Show(
						"and one more than the multiple div(x, p) * p, the residue of x modulo p being one",
						ByArith(
							residues,
							prime,
							multiple,
							nat_congruence.CongDef.At(x, oneIndex, p),
							nat_prime.PrimeAtLeastTwo.At(p),
							nat_div_mod.ModUniq.At(oneIndex, p, zeroIndex, oneIndex),
							nat_div_mod.Division.At(x, p)))
				}))
			invertible := a.Have(
				"read in the field, where the numeral p is zero, the numeral u inverts the numeral i",
				"«numeral»(i) * «numeral»(u) = F.one",
				Simp(Rev(comm_ring.AddPowMulOn.Read(ring))),
				bezout.Rw(),
				Simp(
					Fwd(comm_monoid.PowAddOn.Read(additive)),
					Fwd(comm_ring.OneIn.Read(ring)),
					Fwd(comm_monoid.PowOneOn.Read(additive)),
					Fwd(comm_ring.AddPowMulOn.Read(ring))),
				ByArith(comm_ring.OneIn.Read(ring), prime, numerals.At(v)))
			nonzero := a.Have(
				"so the numeral i is not zero",
				"«numeral»(i) ≠ F.zero",
				By(
					field.OneNotZeroOn.Read(F),
					invertible,
					numerals.At(u),
					comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(a.TermAs[A]("«numeral»(u)"))))
			j, predecessor := a.ObtainAs[Nat](
				"i is a successor, since p divides zero",
				"∃j:num. i = suc(j)",
				By(notMultiple, nat_divides.DividesZero.At(p), peano.Cases.At(i)))
			product := a.Have(
				"the coefficient of the derivative at j is the numeral i times f(i)",
				"«numeral»(i) * f(i) = F.zero",
				predecessor.Rw(),
				By(
					derivative,
					polynomial.PolynomialDerivativeDef.At(
						a.TermAs[Op[A]]("F.add"), zero, a.TermAs[Op[A]]("F.mul"), one, f, j),
					vec_space.VecZeroDef.At(zero, j)))
			a.Show(
				"a nonzero numeral cancels from the product",
				By(
					product,
					nonzero,
					numerals.At(i),
					coefficients.At(i),
					field.MulEqZeroOn.Read(F).AsFact().At(a.TermAs[A]("«numeral»(i)"), f.Apply(i))))
		}),
})}

// PolynomialFrobenius — in characteristic p the p-th power of a polynomial
// is the polynomial in x ^ p of the p-th powers of its coefficients: the
// p-th power adds in the ring of polynomials, which has characteristic p,
// so it passes through the sum of the monomials, and the p-th power of a
// monomial is taken factor by factor.
var PolynomialFrobenius = polynomialFrobeniusThm{family.Add(registry.ProofEntry{
	Name: "PolynomialFrobenius",
	Key:  "prop_f12c6f8bc5f5715e",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p n:num. ∀h:(num → A).",
		Hypotheses: []string{
			"ring_prime_characteristic(R, p)",
			"polynomial_over(R.carrier, h)",
			"vec⟨n⟩(h)",
		},
		Conclusion: "polynomial_pow(h, p) = " +
			"module_sum(vec_add, " +
			"    vec_zero, " +
			"    «below»(n), " +
			"    λj:num. monoid_pow(R.mul, R.one, h(j), p) • basis_vector(p * j))",
		Abbrev: Abbrev{
			{Name: "below", Text: "λm:num. {j:num | j < m}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Scalars pull out of a product of polynomials.
		scalars := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀c d:A. ∀u v:(num → A).",
			Hypotheses: []string{
				"c ∈ R.carrier",
				"d ∈ R.carrier",
				"polynomial_over(R.carrier, u)",
				"polynomial_over(R.carrier, v)",
			},
			Conclusion: "polynomial_mul(c • u, d • v) = (c * d) • polynomial_mul(u, v)",
		}, func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			c, d *Member[A, on.R],
			u, v *Arrow[Nat, A],
			uOver, vOver Fact,
		) {
			polynomialModule := polynomial.PolynomialModuleOn.Read(ring)
			scaled := a.TermAs[Fun[Nat, A]]("c • u")
			coefficients := a.Have(
				"the coefficients of u, of v and of c • u lie in R",
				"∀i:num. u(i) ∈ R.carrier ∧ v(i) ∈ R.carrier ∧ (c • u)(i) ∈ R.carrier",
				By(
					c,
					uOver,
					vOver,
					polynomial.PolynomialOverDef,
					vec_space.VecScalarMulDef,
					comm_ring.MulIn.Read(ring)))
			leftScalar := a.Have(
				"c comes out of the first factor, the product commuting",
				"polynomial_mul(c • u, v) = c • polynomial_mul(u, v)",
				By(
					c,
					coefficients,
					polynomial.PolynomialMulComm.Read(ring).AsFact().At(scaled, v),
					polynomial.PolynomialMulComm.Read(ring).AsFact().At(v, u),
					polynomial.PolynomialMulScalar.Read(ring).AsFact().At(c, v, u)))
			a.Show(
				"d comes out of the second factor, and the two scalars multiply",
				CalcEq(
					Leg(
						a.TermAs[Fun[Nat, A]]("d • polynomial_mul(c • u, v)"),
						"d comes out of the second factor",
						By(d, coefficients, polynomial.PolynomialMulScalar.Read(ring).AsFact().At(d, scaled, v))),
					FinalLeg(
						"then c comes out of the first, and scaling by d after c is scaling by their product",
						leftScalar.Rw(),
						By(
							c,
							d,
							uOver,
							vOver,
							comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(c, d),
							polynomial.PolynomialMulOver.Read(ring).At(u, v),
							module.SmulMul.Read(polynomialModule)))))
		})
		// A power of a monomial is the monomial of the power of its coefficient, at n times the index.
		monomial := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀c:A. ∀i n:num.",
			Hypotheses: []string{
				"c ∈ R.carrier",
			},
			Conclusion: "polynomial_pow(c • basis_vector(i), n) = " +
				"monoid_pow(R.mul, R.one, c, n) • basis_vector(n * i)",
		}, func(a *Argument, ring comm_ring.CommRingFact[on.R], c *Member[A, on.R], i, n *Expr[Nat]) {
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			a.Induct(n)
			a.Base(
				"the zeroth power is the one polynomial, one times the zeroth power of the variable",
				Simp(
					Fwd(polynomial.PolynomialPowZero.Read(ring)),
					Fwd(comm_monoid.MonoidPowDef),
					Fwd(nat_arith.Mul)),
				By(
					module.SmulOne.Read(polynomial.PolynomialModuleOn.Read(ring)),
					polynomial.BasisVectorOver.Read(ring).At(a.TermAs[Nat]("0"))))
			a.Step(
				"one more factor multiplies the scalars and adds the exponents",
				func(b *Argument, ih Fact) {
					scaled := b.TermAs[Fun[Nat, A]]("c • basis_vector(i)")
					power := b.TermAs[A]("monoid_pow(R.mul, R.one, c, n)")
					basisI, basisNI :=
						b.TermAs[Fun[Nat, A]]("basis_vector(i)"), b.TermAs[Fun[Nat, A]]("basis_vector(n * i)")
					exponent := b.Have(
						"the exponent gains i",
						"suc(n) * i = i + n * i",
						ByArith())
					b.Show(
						"multiply the monomial by its n-th power",
						CalcEq(
							Leg(
								b.TermAs[Fun[Nat, A]](
									"polynomial_mul(c • basis_vector(i), monoid_pow(R.mul, R.one, c, n) • basis_vector(n * i))"),
								"the next power multiplies by the monomial once more",
								By(ih, polynomial.PolynomialPowSuc.Read(ring).At(n, scaled))),
							Leg(
								b.TermAs[Fun[Nat, A]](
									"(c * monoid_pow(R.mul, R.one, c, n)) • polynomial_mul(basis_vector(i), basis_vector(n * i))"),
								"the two scalars come out of the product",
								By(
									c,
									polynomial.BasisVectorOver.Read(ring),
									comm_monoid.PowIn.Read(multiplicative).AsFact().At(c, n),
									Read(scalars, ring).At(c, power, basisI, basisNI))),
							FinalLeg(
								"the powers of the variable multiply by adding exponents",
								exponent.Rw(),
								Simp(Fwd(comm_monoid.MonoidPowDef), Rev(polynomial.BasisVectorMul.Read(ring))),
								Basic())))
				})
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p, n *Expr[Nat],
			characteristic Fact,
			h *Arrow[Nat, A],
			over, length Fact,
		) {
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			polynomialModule := polynomial.PolynomialModuleOn.Read(ring)
			add, zero := a.TermAs[Op[Fun[Nat, A]]]("vec_add"), a.TermAs[Fun[Nat, A]]("vec_zero")
			indices := a.TermAs[Set[Nat]]("«below»(n)")
			monomials, powers :=
				a.TermAs[Fun[Nat, Fun[Nat, A]]]("λj:num. h(j) • basis_vector(j)"),
				a.TermAs[Fun[Nat, Fun[Nat, A]]]("λj:num. polynomial_pow(h(j) • basis_vector(j), p)")
			prime := a.Unfolded(characteristic, finite_field.PrimeCharacteristicDef)
			coefficients := a.Have(
				"every coefficient of h lies in R",
				"∀j:num. h(j) ∈ R.carrier",
				By(over, polynomial.PolynomialOverDef))
			adds := a.Have(
				"the polynomials have characteristic p, so the p-th power adds on them",
				Statement{
					Binders: "∀u v:(num → A).",
					Hypotheses: []string{
						"u ∈ polynomial_ring(R).carrier",
						"v ∈ polynomial_ring(R).carrier",
					},
					Conclusion: "polynomial_pow(u + v, p) = polynomial_pow(u, p) + polynomial_pow(v, p)",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[Fun[Nat, A]]("u"), b.FixAs[Fun[Nat, A]]("v")
					members := b.Assume()
					b.Show(
						"this is the additivity of the Frobenius power in the polynomial ring",
						Simp(Fwd(polynomial.PolynomialPowDef)),
						By(
							characteristic,
							finite_field.PolynomialRingCharacteristic.Read(ring).At(p),
							members,
							finite_field.FrobeniusAdditive.Read(polynomials).AsFact().At(p, u, v)))
				}))
			zeroPower := a.Have(
				"and it keeps the zero polynomial, p being a successor",
				"polynomial_pow(vec_zero, p) = vec_zero",
				Derive(func(b *Argument) {
					m, predecessor := b.ObtainAs[Nat](
						"p is a successor, being prime",
						"∃m:num. p = suc(m)",
						ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p), peano.Cases.At(p)))
					polynomialZero := b.TermAs[Fun[Nat, A]]("vec_zero")
					b.Show(
						"a positive power of zero has zero as a factor",
						predecessor.Rw(),
						By(
							polynomial.PolynomialPowSuc.Read(ring).At(m, polynomialZero),
							polynomial.PolynomialPowOver.Read(ring).At(m, polynomialZero),
							polynomial.VecZeroOver.Read(ring),
							comm_ring.MulLeftZeroOn.Read(polynomials).AsFact().At(
								b.TermAs[Fun[Nat, A]]("polynomial_pow(vec_zero, m)"))))
				}))
			monomialsOver := a.Have(
				"each monomial of h is a polynomial",
				"∀j:num. polynomial_over(R.carrier, h(j) • basis_vector(j))",
				By(coefficients, module.SmulIn.Read(polynomialModule), polynomial.BasisVectorOver.Read(ring)))
			powered := a.Have(
				"the p-th power of each monomial is taken factor by factor",
				"∀j:num. "+
					"    polynomial_pow(h(j) • basis_vector(j), p) = "+
					"    monoid_pow(R.mul, R.one, h(j), p) • basis_vector(p * j)",
				a.ForEach(func(j *Expr[Nat]) Action {
					return By(coefficients.At(j), Read(monomial, ring).At(h.Apply(j), j, p))
				}))
			a.Show(
				"expand h, carry the p-th power through the sum, and take it monomial by monomial",
				CalcEq(
					Leg(
						a.TermAs[Fun[Nat, A]](
							"polynomial_pow(module_sum(vec_add, vec_zero, «below»(n), λj:num. h(j) • basis_vector(j)), p)"),
						"h is the sum of its monomials",
						By(over, length, polynomial.PolynomialExpansion.Read(ring).AsFact().At(n, h))),
					Leg(
						a.TermAs[Fun[Nat, A]](
							"module_sum(vec_add, vec_zero, «below»(n), λj:num. polynomial_pow(h(j) • basis_vector(j), p))"),
						"the p-th power adds and keeps zero, so it passes through the finite sum",
						By(
							adds,
							zeroPower,
							monomialsOver,
							num_segment.FiniteBelowStrict.At(n),
							module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(polynomials)).At(
								add,
								zero,
								a.TermAs[Fun[Fun[Nat, A], Fun[Nat, A]]]("λq:(num → A). polynomial_pow(q, p)"),
								indices,
								monomials))),
					FinalLeg(
						"each term is the p-th power of its monomial",
						By(
							powered,
							module.ModuleSumCongruence.At(
								add,
								zero,
								indices,
								powers,
								a.TermAs[Fun[Nat, Fun[Nat, A]]](
									"λj:num. monoid_pow(R.mul, R.one, h(j), p) • basis_vector(p * j)"))))))
		})
	}),
})}

// PolynomialPthRoot — over a field of characteristic p in which every
// element is a p-th power, a polynomial with its coefficients on the
// multiples of p is a p-th power: the p-th roots h(j) of its coefficients
// f(p * j) vanish where those do, so they make a polynomial, and by
// PolynomialFrobenius its p-th power is the sum of the f(p * j) x ^ (p * j),
// which are all the monomials of f that are not zero.
var PolynomialPthRoot = polynomialPthRootThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPthRoot",
	Key:  "prop_eda07d9d16c68fd8",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:num. ∀f:(num → A).",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(F), p)",
			"∀a:A. a ∈ F.carrier ⇒ ∃b:A. b ∈ F.carrier ∧ monoid_pow(F.mul, F.one, b, p) = a",
			"polynomial_over(F.carrier, f)",
			"∀i:num. ¬(p ∣ i) ⇒ f(i) = F.zero",
		},
		Conclusion: "∃h:(num → A). polynomial_over(F.carrier, h) ∧ f = polynomial_pow(h, p)",
		Abbrev: Abbrev{
			{Name: "below", Text: "λm:num. {j:num | j < m}"},
		},
	},
		func(
			a *Argument,
			F field.FieldFact[on.F],
			p *Expr[Nat],
			characteristic, roots Fact,
			f *Arrow[Nat, A],
			over, onMultiples Fact,
		) {
			ring := field.RingOn.Read(F)
			polynomialModule := polynomial.PolynomialModuleOn.Read(ring)
			zero, carrier := a.TermAs[A]("F.zero"), a.TermAs[Set[A]]("F.carrier")
			prime := a.Unfolded(characteristic, finite_field.PrimeCharacteristicDef)
			two := a.Have(
				"a prime is at least two",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo))
			h, chosen := a.ObtainAs[Fun[Nat, A]](
				"choose a p-th root h(j) of each coefficient f(p * j)",
				"∃h:(num → A). ∀j:num. h(j) ∈ F.carrier ∧ monoid_pow(F.mul, F.one, h(j), p) = f(p * j)",
				Derive(func(b *Argument) {
					exists := b.Have(
						"each coefficient of f has a p-th root in the field",
						"∀j:num. ∃b:A. b ∈ F.carrier ∧ monoid_pow(F.mul, F.one, b, p) = f(p * j)",
						By(roots, over, polynomial.PolynomialOverDef))
					b.Show(
						"the roots assemble to a function",
						By(exists))
				}))
			n, length := a.UnpackAs[Nat](
				a.Conjuncts(
					a.Unfolded(over, polynomial.PolynomialOverDef),
					"f vanishes from some index n on",
					"and every coefficient of f lies in the field")[0],
				"n")
			scaledBound := a.Have(
				"multiplying by p does not lower an index",
				"∀j:num. j ≤ p * j",
				a.ForEach(func(j *Expr[Nat]) Action {
					return ByArith(two, nat_order.LessEqSelfMul.At(j, p))
				}))
			tail := a.Unfolded(length, vec_space.VecDef)
			hLength := a.Have(
				"h vanishes from n on: there n ≤ i ≤ p * i, and only zero has p-th power zero",
				"vec⟨n⟩(h)",
				Simp(Fwd(vec_space.VecDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					past := b.Assume()
					scaled := b.TermAs[Nat]("p * i")
					b.Show(
						"f vanishes at p * i",
						By(
							past,
							scaledBound.At(i),
							nat_order.LessEqTrans.At(n, i, scaled),
							tail.At(scaled),
							chosen.At(i),
							field.PowEqZeroOn.Read(F).AsFact().At(b.TermAs[A]("h(i)"), p)))
				}))
			hOver := a.Have(
				"so h is a polynomial over the field",
				"polynomial_over(F.carrier, h)",
				By(Normalized, chosen, hLength, polynomial.PolynomialOverDef.At(zero, carrier, h)))
			terms := a.TermAs[Fun[Nat, Fun[Nat, A]]]("λi:num. f(i) • basis_vector(i)")
			multiple := a.TermAs[Fun[Nat, Nat]]("λj:num. p * j")
			wholeLength := a.TermAs[Nat]("p * n")
			indices, wholeIndices := a.TermAs[Set[Nat]]("«below»(n)"), a.TermAs[Set[Nat]]("«below»(p * n)")
			multiples := a.TermAs[Set[Nat]]("image(λj:num. p * j, «below»(n))")
			add, polynomialZero := a.TermAs[Op[Fun[Nat, A]]]("vec_add"), a.TermAs[Fun[Nat, A]]("vec_zero")
			rootTerms := a.TermAs[Fun[Nat, Fun[Nat, A]]]("λj:num. f(p * j) • basis_vector(p * j)")
			powerTerms := a.TermAs[Fun[Nat, Fun[Nat, A]]](
				"λj:num. monoid_pow(F.mul, F.one, h(j), p) • basis_vector(p * j)")
			power := a.Have(
				"f is the p-th power of h",
				"f = polynomial_pow(h, p)",
				Derive(func(b *Argument) {
					lower := b.Have(
						"multiplying by p keeps the order of indices",
						"∀j:num. j < n ⇔ p * j < p * n",
						b.ForEach(func(j *Expr[Nat]) Action {
							return ByArith(two, nat_order.LessThanMulCancel.At(p, j, n))
						}))
					inside := b.Have(
						"the images of the indices below n lie below p * n",
						"image(λj:num. p * j, «below»(n)) ⊆ «below»(p * n)",
						BySets(lower))
					monomials := b.Have(
						"each monomial of f is a polynomial",
						"∀i:num. polynomial_over(F.carrier, f(i) • basis_vector(i))",
						By(
							over,
							polynomial.PolynomialOverDef,
							module.SmulIn.Read(polynomialModule),
							polynomial.BasisVectorOver.Read(ring)))
					multiplesOnly := b.Have(
						"an index below p * n that is no image is no multiple of p",
						"∀i:num. i < p * n ∧ i ∉ image(λj:num. p * j, «below»(n)) ⇒ ¬(p ∣ i)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							outside := c.Assume()
							divides := c.SupposeNot()
							x, factored := c.ObtainAs[Nat](
								"write i as p * x",
								"∃x:num. i = p * x",
								By(Normalized, divides, nat_divides.DividesFactor.At(p, i)))
							c.Show(
								"then x lies below n, and i is an image after all",
								By(factored, outside, lower.At(x), set_basic.InImage.At(multiple, indices, i)))
						}))
					dropped := b.Have(
						"the monomials of f off the multiples of p vanish",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"i ∈ «below»(p * n)",
								"i ∉ image(λj:num. p * j, «below»(n))",
							},
							Conclusion: "f(i) • basis_vector(i) = vec_zero",
						},
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							outside := c.Assume()
							coefficient := c.Have(
								"the coefficient of f there is zero",
								"f(i) = F.zero",
								By(outside, multiplesOnly.At(i), onMultiples.At(i)))
							c.Show(
								"zero scales to the zero polynomial",
								coefficient.Rw(),
								By(module.ZeroSmul.Read(polynomialModule), polynomial.BasisVectorOver.Read(ring).At(i)))
						}))
					injective := b.Have(
						"multiplying by p is injective",
						"injective_on(«below»(n), λj:num. p * j)",
						ByArith(two, functions.InjectiveOnDef, nat_arith.MulEqLCancel))
					wideLength := b.Have(
						"f vanishes from p * n on as well",
						"vec⟨p * n⟩(f)",
						By(length, scaledBound.At(n), vec_space.VecMono.At(zero, n, wholeLength, f)))
					b.Show(
						"reindex the monomials of f over the multiples of p, and read their coefficients as p-th powers",
						CalcEq(
							Leg(
								b.TermAs[Fun[Nat, A]](
									"module_sum(vec_add, vec_zero, «below»(p * n), λi:num. f(i) • basis_vector(i))"),
								"f is the sum of its monomials",
								By(over, wideLength, polynomial.PolynomialExpansion.Read(ring).AsFact().At(wholeLength, f))),
							Leg(
								b.TermAs[Fun[Nat, A]](
									"module_sum(vec_add, vec_zero, image(λj:num. p * j, «below»(n)), λi:num. f(i) • basis_vector(i))"),
								"only the multiples of p contribute",
								By(
									inside,
									monomials,
									dropped,
									num_segment.FiniteBelowStrict.At(wholeLength),
									module.ModuleSumSupport.Read(polynomialModule).At(wholeIndices, multiples, terms))),
							Leg(
								b.TermAs[Fun[Nat, A]](
									"module_sum(vec_add, vec_zero, «below»(n), λj:num. f(p * j) • basis_vector(p * j))"),
								"reindex along the injective multiplication by p",
								By(
									injective,
									monomials,
									num_segment.FiniteBelowStrict.At(n),
									module.ModuleSumImage.Read(polynomialModule).At(indices, multiple, terms))),
							Leg(
								b.TermAs[Fun[Nat, A]](
									"module_sum(vec_add, "+
										"    vec_zero, "+
										"    «below»(n), "+
										"    λj:num. monoid_pow(F.mul, F.one, h(j), p) • basis_vector(p * j))"),
								"each coefficient f(p * j) is the p-th power of h(j)",
								By(chosen, module.ModuleSumCongruence.At(add, polynomialZero, indices, rootTerms, powerTerms))),
							FinalLeg(
								"and this is the p-th power of h",
								By(characteristic, hOver, hLength, PolynomialFrobenius.Read(ring).AsFact().At(p, n, h)))))
				}))
			a.Take(h)
			a.Show(
				"h is that polynomial",
				By(hOver, power))
		}),
})}

// FrobeniusSurjectivePerfect — a field of prime characteristic p in which
// every element is a p-th power is perfect. An irreducible f that is not
// separable has zero derivative, so its coefficients stand on the multiples
// of p and it is the p-th power of a polynomial h (PolynomialPthRoot). That
// factors f as h times h ^ (p - 1). Over a domain a power has the exponent
// times the degree, so the positive degree of f keeps the degree of h from
// zero, and neither factor is constant, against irreducibility.
var FrobeniusSurjectivePerfect = frobeniusSurjectivePerfectThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusSurjectivePerfect",
	Key:  "prop_7dcce1286869ede9",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:num.",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(F), p)",
			"∀a:A. a ∈ F.carrier ⇒ ∃b:A. b ∈ F.carrier ∧ monoid_pow(F.mul, F.one, b, p) = a",
		},
		Conclusion: "perfect_field(F)",
	},
		func(a *Argument, F field.FieldFact[on.F], p *Expr[Nat], characteristic, roots Fact) {
			ring := field.RingOn.Read(F)
			domain := integral_domain.FieldIntegralDomain.Read(F)
			prime := a.Unfolded(characteristic, finite_field.PrimeCharacteristicDef)
			two := a.Have(
				"a prime is at least two",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo))
			a.Do(Unfold(PerfectFieldDef))
			f := a.FixAs[Fun[Nat, A]]("f")
			irreducible := a.Assume()
			inseparable := a.SupposeNot()
			parts := a.Conjuncts(
				a.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
				"f is over the field",
				"f has positive degree",
				"every factorization of f has a factor of degree zero")
			over, positive, factorizations := parts[0], parts[1], parts[2]
			zeroDerivative := a.Have(
				"irreducible and not separable, f has zero derivative",
				"polynomial_derivative(f) = vec_zero",
				By(inseparable, irreducible, separable_polynomial.SeparableIffDerivative.Read(F).At(f)))
			onMultiples := a.Have(
				"so the coefficients of f stand on the multiples of p",
				"∀i:num. ¬(p ∣ i) ⇒ f(i) = F.zero",
				By(F, characteristic, over, zeroDerivative, ZeroDerivativeCoefficients))
			h, rooted := a.ObtainAs[Fun[Nat, A]](
				"so f is the p-th power of a polynomial h",
				"∃h:(num → A). polynomial_over(F.carrier, h) ∧ f = polynomial_pow(h, p)",
				By(F, characteristic, roots, over, onMultiples, PolynomialPthRoot.Read(F).At(p, f)))
			rootedParts := a.Conjuncts(
				rooted,
				"h is a polynomial over the field",
				"f is its p-th power")
			hOver, power := rootedParts[0], rootedParts[1]
			m, predecessor := a.ObtainAs[Nat](
				"p is a successor",
				"∃m:num. p = suc(m)",
				ByArith(two, peano.Cases.At(p)))
			cofactor := a.TermAs[Fun[Nat, A]]("polynomial_pow(h, m)")
			factored := a.Have(
				"h divides its own p-th power, with the (p - 1)-th power for cofactor",
				"f = polynomial_mul(h, polynomial_pow(h, m))",
				By(power, predecessor, polynomial.PolynomialPowSuc.Read(ring).At(m, h)))
			cofactorOver := a.Have(
				"the cofactor is a polynomial over the field",
				"polynomial_over(F.carrier, polynomial_pow(h, m))",
				By(hOver, polynomial.PolynomialPowOver.Read(ring).At(m, h)))
			fDegree := a.Have(
				"f, the p-th power of h, has p times its degree",
				"polynomial_degree(f) = p * polynomial_degree(h)",
				power.Rw(),
				By(hOver, polynomial.DegreePow.Read(domain).At(p, h)))
			degree := a.TermAs[Nat]("polynomial_degree(h)")
			hNotConstant := a.Have(
				"so h is not constant, f having positive degree",
				"polynomial_degree(h) ≠ 0",
				ByArith(positive, fDegree, nat_arith.MulEqZero.At(p, degree)))
			cofactorNotConstant := a.Have(
				"nor is the cofactor, which has m times that degree, m not being zero",
				"polynomial_degree(polynomial_pow(h, m)) ≠ 0",
				ByArith(
					hNotConstant,
					hOver,
					predecessor,
					two,
					polynomial.DegreePow.Read(domain).At(m, h),
					nat_arith.MulEqZero.At(m, degree)))
			a.Show(
				"so f has no factor of degree zero, against irreducibility",
				By(
					factorizations.At(h, cofactor),
					hOver,
					cofactorOver,
					factored,
					hNotConstant,
					cofactorNotConstant))
		}),
})}

// PrimeRootDegree — in characteristic p, an element t outside a subfield P
// whose p-th power lies in P has degree exactly p over P. Over L the p-th
// power of X - t has its coefficients in P, by the Frobenius, so it is a
// nonzero polynomial over P vanishing at t. The minimal polynomial of t divides
// it, and a monic divisor of a power of X - t is a power of X - t. Its constant
// term is then a power u ^ m of u = -t with 0 < m ≤ p, lying in P with u ^ p.
// If m were below p, a multiple of m would be one more than a multiple of p, and
// dividing the two powers of u would put u in P, and t with it.
var PrimeRootDegree = primeRootDegreeThm{family.Add(registry.ProofEntry{
	Name: "PrimeRootDegree",
	Key:  "prop_1be6ee2a834d4cb",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀P:set(A). ∀p:num. ∀t:A.",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(L), p)",
			"subfield(L, P)",
			"t ∈ L.carrier",
			"t ∉ P",
			"monoid_pow(L.mul, L.one, t, p) ∈ P",
		},
		Conclusion: "finite_extension(L, P, field_adjoin(L, P, {t})) ∧ " +
			"extension_degree(L, P, field_adjoin(L, P, {t})) = p",
	}, func(ctx *Script, headline string) *GoalStackNode {
		// A monic divisor of a power of X - t is itself a power of X - t, of its own degree.
		divisor := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀t:A. ∀n:num. ∀h:(num → A).",
			Hypotheses: []string{
				"t ∈ L.carrier",
				"polynomial_over(L.carrier, h)",
				"polynomial_monic(h)",
				"polynomial_divides(field_ring(L), h, polynomial_pow(«linear»(t), n))",
			},
			Conclusion: "h = polynomial_pow(«linear»(t), polynomial_degree(h))",
		}, func(a *Argument, L field.FieldFact[on.L], t *Member[A, on.L]) {
			ring := field.RingOn.Read(L)
			domain := integral_domain.FieldIntegralDomain.Read(L)
			polynomials := polynomial.PolynomialDomain.Read(domain)
			zero, one, carrier := a.TermAs[A]("L.zero"), a.TermAs[A]("L.one"), a.TermAs[Set[A]]("L.carrier")
			coefficientRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			l, lDef := a.LetAs[Fun[Nat, A]]("l", "«linear»(t)")
			linear := a.Conjuncts(
				a.Simplified(polynomial_roots.LinearFactor.Read(ring).At(t), Rev(lDef)),
				"l is a polynomial over L",
				"l is monic",
				"l has degree at most one",
				"l takes the value y - t at each point y of L",
				"l vanishes at t",
				"l has degree one when one is not zero")
			lOver, lMonic, lVanishes, lNontrivial := linear[0], linear[1], linear[4], linear[5]
			lDegree := a.Have(
				"one is not zero in a field, so l has degree one",
				"polynomial_degree(l) = 1",
				By(field.OneNotZeroOn.Read(L), lNontrivial))
			cancel := a.Have(
				"l is monic, so not zero, and it cancels from a product",
				Statement{
					Binders: "∀u v:(num → A).",
					Hypotheses: []string{
						"polynomial_over(L.carrier, u)",
						"polynomial_over(L.carrier, v)",
						"polynomial_mul(l, u) = polynomial_mul(l, v)",
					},
					Conclusion: "u = v",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[Fun[Nat, A]]("u"), b.FixAs[Fun[Nat, A]]("v")
					b.Show(
						"polynomials over a field are a domain",
						By(
							b.Assume(),
							lOver,
							lMonic,
							polynomial.MonicNonzero.Read(domain).At(l),
							integral_domain.MulCancelLeft.Read(polynomials).AsFact().At(l, u, v)))
				}))
			a.Induct("n")
			a.Base(
				"a monic divisor of one has degree zero, so it is one",
				func(b *Argument) {
					h := b.FixAs[Fun[Nat, A]]("h")
					data := b.Conjuncts(
						b.Assume(),
						"h is a polynomial over L",
						"h is monic",
						"h divides the zeroth power of l")
					hOver, hMonic, hDivides := data[0], data[1], data[2]
					constant := b.Have(
						"the degree of h is at most that of one, which is zero",
						"polynomial_degree(h) = 0",
						ByArith(
							hDivides,
							hOver,
							polynomial.PolynomialPowZero.Read(ring).At(l),
							polynomial_division.DividesDegree.Read(L),
							polynomial.DegreeBasisVector.Read(ring),
							integral_domain.OneNotZero.Read(polynomials),
							field.OneNotZeroOn.Read(L)))
					b.Show(
						"a monic polynomial of degree zero is one, the zeroth power of l",
						By(
							Normalized,
							constant,
							hMonic,
							hOver,
							polynomial.PolynomialPowZero.Read(ring).At(l),
							polynomial.MonicDegreeZero.Read(ring).At(h)))
				})
			a.Step(
				"a root of the product is a root of h or of its cofactor; l splits off there and cancels",
				func(b *Argument, smaller Fact) {
					n := b.TermAs[Nat]("n")
					last := b.TermAs[Fun[Nat, A]]("polynomial_pow(l, n)")
					h := b.FixAs[Fun[Nat, A]]("h")
					data := b.Conjuncts(
						b.Assume(),
						"h is a polynomial over L",
						"h is monic",
						"h divides the next power of l")
					hOver, hMonic, hDivides := data[0], data[1], data[2]
					r, cofactor := b.UnpackAs[Fun[Nat, A]](
						b.Unfolded(hDivides, polynomial_division.PolynomialDividesDef), "r")
					cofactorParts := b.Conjuncts(
						cofactor,
						"the cofactor r is a polynomial over L",
						"the next power of l is h times r")
					rOver, product := cofactorParts[0], cofactorParts[1]
					lastOver := polynomial.PolynomialPowOver.Read(ring).At(n, l)
					next := b.Have(
						"the next power of l is l times the last",
						"polynomial_mul(l, polynomial_pow(l, n)) = polynomial_mul(h, r)",
						By(product, polynomial.PolynomialPowSuc.Read(ring).At(n, l)))
					hValue := b.TermAs[A]("polynomial_eval(h, t)")
					rValue := b.TermAs[A]("polynomial_eval(r, t)")
					root := b.Have(
						"l vanishes at t, so the product does, and a field has no zero divisors",
						"polynomial_eval(h, t) = L.zero ∨ polynomial_eval(r, t) = L.zero",
						By(
							next,
							lVanishes,
							t,
							hOver,
							lOver,
							rOver,
							lastOver,
							polynomial_evaluation.EvalMulRoot.Read(ring).AsFact().At(l, last, t),
							polynomial_evaluation.EvalMul.Read(ring).AsFact().At(h, r, t),
							polynomial_evaluation.EvalIn.Read(ring).AsFact().At(h, t),
							polynomial_evaluation.EvalIn.Read(ring).AsFact().At(r, t),
							field.MulEqZeroOn.Read(L).AsFact().At(hValue, rValue)))
					b.Cases(b.Term("polynomial_eval(h, t) = L.zero"))
					b.When(
						"t is a root of h: h is l times a monic q, which the hypothesis makes a power of l",
						func(c *Argument, hRoot Fact) {
							q, factored := c.ObtainAs[Fun[Nat, A]](
								"h, monic and so nonzero, is l times a nonzero q one degree lower",
								"∃q:(num → A). "+
									"    polynomial_over(L.carrier, q) ∧ "+
									"    q ≠ vec_zero ∧ "+
									"    h = polynomial_mul(l, q) ∧ "+
									"    polynomial_degree(h) = suc(polynomial_degree(q))",
								By(
									lDef,
									hOver,
									hMonic,
									hRoot,
									t,
									polynomial.MonicNonzero.Read(domain).At(h),
									polynomial_roots.RootFactorization.Read(domain).At(h, t)))
							parts := c.Conjuncts(
								factored,
								"q is a polynomial over L",
								"q is not zero",
								"h is l times q",
								"h is one degree above q")
							qOver, hProduct, degreeStep := parts[0], parts[2], parts[3]
							degrees := c.Have(
								"the degrees of l and q add to that of h",
								"polynomial_degree(l) + polynomial_degree(q) = polynomial_degree(h)",
								ByArith(lDegree, degreeStep))
							leading := c.Have(
								"the leading coefficients of l and q multiply at that degree",
								"polynomial_mul(l, q, polynomial_degree(h)) = l(polynomial_degree(l)) * q(polynomial_degree(q))",
								By(degrees, lOver, qOver, polynomial.LeadingCoefficientMul.Read(ring).At(l, q)))
							unit := c.Have(
								"h and l being monic, one times the leading coefficient of q is one",
								"L.one * q(polynomial_degree(q)) = L.one",
								By(
									Normalized,
									leading,
									hProduct,
									hMonic,
									lMonic,
									polynomial.PolynomialMonicDef.At(zero, one, h),
									polynomial.PolynomialMonicDef.At(zero, one, l)))
							qCoefficients := polynomial.PolynomialOverDef.At(zero, carrier, q)
							qMonic := c.Have(
								"so q is monic",
								"polynomial_monic(q)",
								ByArith(L, unit, qOver, polynomial.PolynomialMonicDef.At(zero, one, q), qCoefficients))
							regrouped := c.Have(
								"regroup the product as l times q times r",
								"polynomial_mul(l, polynomial_pow(l, n)) = polynomial_mul(l, polynomial_mul(q, r))",
								By(
									next,
									hProduct,
									rOver,
									lOver,
									qOver,
									polynomial.PolynomialMulAssoc.Read(ring).At(l, q, r),
									polynomial.PolynomialOverDef.At(zero, carrier, r),
									polynomial.PolynomialOverDef.At(zero, carrier, l),
									qCoefficients))
							cancelled := c.Have(
								"cancel l",
								"polynomial_pow(l, n) = polynomial_mul(q, r)",
								By(
									regrouped,
									lOver,
									qOver,
									rOver,
									lastOver,
									polynomial.PolynomialMulOver.Read(ring).At(q, r),
									cancel.At(last, c.TermAs[Fun[Nat, A]]("polynomial_mul(q, r)"))))
							qPower := c.Have(
								"q is monic and divides the last power of l, so it is a power of l",
								"q = polynomial_pow(l, polynomial_degree(q))",
								By(
									smaller.At(q),
									cancelled,
									qOver,
									rOver,
									qMonic,
									polynomial_division.PolynomialDividesDef.At(coefficientRing, q, last)))
							c.Show(
								"so h is l times that power",
								By(
									Normalized,
									hProduct,
									degreeStep,
									qPower,
									polynomial.PolynomialPowSuc.Read(ring).At(c.TermAs[Nat]("polynomial_degree(q)"), l)))
						})
					b.Otherwise(
						"t is a root of r: l splits off r, and h divides the last power of l",
						func(c *Argument, notRoot Fact) {
							rRoot := c.Have(
								"so t is a root of the cofactor",
								"polynomial_eval(r, t) = L.zero",
								By(root, notRoot))
							rFactor := c.Have(
								"so l divides r",
								"polynomial_divides(field_ring(L), l, r)",
								By(Normalized, lDef, rRoot, t, rOver, polynomial_roots.FactorTheorem.Read(ring).At(r, t)))
							w, rFactored := c.UnpackAs[Fun[Nat, A]](
								c.Unfolded(rFactor, polynomial_division.PolynomialDividesDef), "w")
							parts := c.Conjuncts(
								rFactored,
								"the second cofactor w is a polynomial over L",
								"r is l times w")
							wOver, rProduct := parts[0], parts[1]
							regrouped := c.Have(
								"l commutes past h in the product",
								"polynomial_mul(l, polynomial_pow(l, n)) = polynomial_mul(l, polynomial_mul(h, w))",
								By(
									rProduct,
									next,
									hOver,
									lOver,
									wOver,
									polynomial.PolynomialMulLeftComm.Read(ring).At(h, l, w),
									polynomial.PolynomialOverDef.At(zero, carrier, h),
									polynomial.PolynomialOverDef.At(zero, carrier, l),
									polynomial.PolynomialOverDef.At(zero, carrier, w)))
							cancelled := c.Have(
								"cancel l",
								"polynomial_pow(l, n) = polynomial_mul(h, w)",
								By(
									regrouped,
									hOver,
									lOver,
									wOver,
									lastOver,
									polynomial.PolynomialMulOver.Read(ring).At(h, w),
									cancel.At(last, c.TermAs[Fun[Nat, A]]("polynomial_mul(h, w)"))))
							c.Show(
								"h is monic and divides the last power of l, so it is a power of l",
								By(
									smaller.At(h),
									cancelled,
									hOver,
									wOver,
									hMonic,
									polynomial_division.PolynomialDividesDef.At(coefficientRing, h, last)))
						})
				})
		})

		// Off the multiples of a prime p, a multiple of i is one more than a multiple of p.
		bezout := ctx.Lemma(Statement{
			Binders: "∀p i:num.",
			Hypotheses: []string{
				"nat_prime(p)",
				"¬(p ∣ i)",
			},
			Conclusion: "∃u v:num. i * u = p * v + 1",
		}, func(a *Argument, p, i *Expr[Nat], prime, notMultiple Fact) {
			oneIndex, zeroIndex := a.TermAs[Nat]("1"), a.TermAs[Nat]("0")
			x, residues := a.ObtainAs[Nat](
				"p is coprime to i, so the Chinese remainder theorem gives x ≡ 1 mod p and x ≡ 0 mod i",
				"∃x:num. x ≡ 1 (mod p) ∧ x ≡ 0 (mod i)",
				By(
					prime,
					notMultiple,
					nat_prime.PrimeCoprimeIffNotDivides,
					nat_congruence.ChineseRemainder.At(p, i, oneIndex, zeroIndex)))
			q, multiple := a.ObtainAs[Nat](
				"x is a multiple of i",
				"∃q:num. x = q * i",
				By(
					Normalized,
					residues,
					nat_congruence.CongDef.At(x, zeroIndex, i),
					nat_div_mod.ZeroMod.At(i),
					nat_div_mod.ModEqZero.At(x, i)))
			a.Take(q)
			a.Take(a.TermAs[Nat]("div(x, p)"))
			a.Show(
				"and one more than the multiple p * div(x, p), the residue of x modulo p being one",
				ByArith(
					residues,
					prime,
					multiple,
					nat_congruence.CongDef.At(x, oneIndex, p),
					nat_prime.PrimeAtLeastTwo.At(p),
					nat_div_mod.ModUniq.At(oneIndex, p, zeroIndex, oneIndex),
					nat_div_mod.Division.At(x, p)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			P *Expr[Set[A]],
			p *Expr[Nat],
			t *Expr[A],
			characteristic, setPSubfield, tIn, tOutside, powerIn Fact,
		) {
			ring := field.RingOn.Read(L)
			domain := integral_domain.FieldIntegralDomain.Read(L)
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			fieldValue := a.TermAs[FieldOps[A]]("L")
			zero, one, carrier := a.TermAs[A]("L.zero"), a.TermAs[A]("L.one"), a.TermAs[Set[A]]("L.carrier")
			zeroMember := a.MemberOf[on.L](zero, comm_ring.ZeroIn.Read(ring))
			tMember := a.MemberOf[on.L](t, tIn)
			prime := a.Unfolded(characteristic, finite_field.PrimeCharacteristicDef)
			two := a.Have(
				"a prime is at least two",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo))
			pred, predecessor := a.ObtainAs[Nat](
				"p is a successor",
				"∃k:num. p = suc(k)",
				ByArith(two, peano.Cases.At(p)))
			zeroPower := a.Have(
				"the p-th power of zero is zero",
				"monoid_pow(L.mul, L.one, L.zero, p) = L.zero",
				predecessor.Rw(),
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				ByArith(
					L,
					comm_ring.ZeroIn.Read(ring),
					comm_monoid.PowIn.Read(multiplicative).AsFact().At(zero, pred)))
			setPSubset := a.Have(
				"P lies in L",
				"P ⊆ L.carrier",
				By(setPSubfield, field.SubfieldSubset.At(fieldValue, P)))
			setPRing := a.Have(
				"P is a ring under the operations of L",
				"comm_ring_on(restrict_ring(field_ring(L), P))",
				By(setPSubfield, field.SubfieldCommRing.Read(L).At(P)))
			setPPowers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(setPRing))
			setPModule := polynomial.PolynomialModuleOn.Read(setPRing)

			l, lDef := a.LetAs[Fun[Nat, A]]("l", "«linear»(t)")
			linear := a.Conjuncts(
				a.Simplified(polynomial_roots.LinearFactor.Read(ring).At(tMember), Rev(lDef)),
				"l is a polynomial over L",
				"l is monic",
				"l has degree at most one",
				"l takes the value y - t at each point y of L",
				"l vanishes at t",
				"l has degree one when one is not zero")
			lOver, lMonic, lValues, lVanishes, lNontrivial :=
				linear[0], linear[1], linear[3], linear[4], linear[5]
			lDegree := a.Have(
				"one is not zero in a field, so l has degree one",
				"polynomial_degree(l) = 1",
				By(field.OneNotZeroOn.Read(L), lNontrivial))
			u, uDef := a.LetAs[A]("u", "L.zero - t")
			lAtZero := a.Have(
				"at zero l takes the value u",
				"polynomial_eval(l, L.zero) = u",
				By(uDef, zeroMember, lValues.At(zero)))
			uIn := a.Have(
				"u lies in L",
				"u ∈ L.carrier",
				By(Normalized, uDef, tMember, zeroMember, comm_ring.SubIn.Read(ring).At(zeroMember, tMember)))
			uMember := a.MemberOf[on.L](u, uIn)
			uPower := a.Have(
				"the p-th power adds, and t + u is zero, so the p-th power of u is minus that of t",
				"monoid_pow(L.mul, L.one, u, p) = L.zero - monoid_pow(L.mul, L.one, t, p)",
				Derive(func(b *Argument) {
					sum := b.Have(
						"t and u add to zero",
						"t + u = L.zero",
						ByArith(L, uDef, tIn, uIn))
					added := b.Have(
						"so the two p-th powers add to the p-th power of zero",
						"L.zero = monoid_pow(L.mul, L.one, t, p) + monoid_pow(L.mul, L.one, u, p)",
						By(
							characteristic,
							tIn,
							uIn,
							sum,
							zeroPower,
							finite_field.FrobeniusAdditive.Read(ring).AsFact().At(p, t, u)))
					b.Show(
						"which is the claim, read in the field",
						ByArith(
							L,
							added,
							tIn,
							uIn,
							comm_ring.ZeroIn.Read(ring),
							comm_monoid.PowIn.Read(multiplicative).AsFact().At(t, p),
							comm_monoid.PowIn.Read(multiplicative).AsFact().At(u, p)))
				}))
			uPowerIn := a.Have(
				"so the p-th power of u lies in P",
				"monoid_pow(L.mul, L.one, u, p) ∈ P",
				By(
					uPower,
					setPSubfield,
					powerIn,
					field.SubfieldZero.At(fieldValue, P),
					field.SubfieldSub.Read(L).AsFact().At(P, zero, a.TermAs[A]("monoid_pow(L.mul, L.one, t, p)"))))

			constantCoefficient := a.Have(
				"the coefficient of l at 0 is its value at zero",
				"l(0) = u",
				By(Normalized, lOver, lAtZero, polynomial_evaluation.EvalAtZero.Read(ring).At(l)))
			leadingCoefficient := a.Have(
				"the coefficient of l at 1 is one, l being monic of degree one",
				"l(1) = L.one",
				By(Normalized, lMonic, lDegree, polynomial.PolynomialMonicDef.At(zero, one, l)))
			degreeBound := a.TermAs[Nat]("suc(polynomial_degree(l))")
			lLength := a.Have(
				"l vanishes from index 2 on",
				"vec⟨2⟩(l)",
				ByArith(
					lOver,
					lDegree,
					polynomial.DegreeVec.At(zero, carrier, l),
					vec_space.VecMono.At(zero, degreeBound, a.TermAs[Nat]("2"), l)))
			coefficientPowers := a.Have(
				"the p-th powers of the two coefficients of l lie in P",
				"∀j:num. j < 2 ⇒ monoid_pow(L.mul, L.one, l(j), p) ∈ P",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("j")
					below := b.Assume()
					b.Cases(b.Term("j = 0"))
					b.When(
						"at 0 the coefficient is u",
						func(c *Argument, atZero Fact) {
							c.Show(
								"whose p-th power lies in P",
								By(atZero, constantCoefficient, uPowerIn))
						})
					b.Otherwise(
						"at 1 the coefficient is one",
						func(c *Argument, positive Fact) {
							atOne := c.Have(
								"the index is 1",
								"j = 1",
								ByArith(below, positive))
							c.Show(
								"and the powers of one are one, which lies in P",
								By(
									atOne,
									leadingCoefficient,
									setPSubfield,
									field.SubfieldOne.At(fieldValue, P),
									comm_monoid.IdentityPowOn.Read(multiplicative).At(p)))
						})
				}))
			terms := a.Have(
				"each term of the Frobenius expansion of the p-th power of l is a polynomial over P",
				Statement{
					Binders:    "∀j:num.",
					Hypotheses: []string{"j ∈ {j:num | j < 2}"},
					Conclusion: "polynomial_over(P, monoid_pow(L.mul, L.one, l(j), p) • basis_vector(p * j))",
				},
				By(
					setPRing,
					coefficientPowers,
					module.SmulIn.Read(setPModule),
					polynomial.BasisVectorOver.Read(setPRing)))
			f := a.TermAs[Fun[Nat, A]]("polynomial_pow(l, p)")
			fOver := a.Have(
				"so the p-th power of l is a polynomial over P",
				"polynomial_over(P, polynomial_pow(l, p))",
				Derive(func(b *Argument) {
					expansion := b.Have(
						"the Frobenius expands it over the two coefficients of l",
						"polynomial_pow(l, p) = "+
							"module_sum(vec_add, "+
							"    vec_zero, "+
							"    {j:num | j < 2}, "+
							"    λj:num. monoid_pow(L.mul, L.one, l(j), p) • basis_vector(p * j))",
						By(
							characteristic,
							lOver,
							lLength,
							PolynomialFrobenius.Read(ring).AsFact().At(p, b.TermAs[Nat]("2"), l)))
					b.Show(
						"and a finite sum of polynomials over P is one",
						By(
							expansion,
							setPRing,
							terms,
							module.ModuleSumIn.Read(setPModule).AsFact().At(
								b.TermAs[Set[Nat]]("{j:num | j < 2}"),
								b.TermAs[Fun[Nat, Fun[Nat, A]]]("λj:num. monoid_pow(L.mul, L.one, l(j), p) • basis_vector(p * j)")),
							num_segment.FiniteBelowStrict.At(b.TermAs[Nat]("2"))))
				}))
			fDegree := a.Have(
				"it has degree p",
				"polynomial_degree(polynomial_pow(l, p)) = p",
				ByArith(lDegree, lOver, polynomial.DegreePow.Read(domain).At(p, l)))
			pNonzero := a.Have(
				"p is not zero",
				"p ≠ 0",
				ByArith(two))
			fNonzero := a.Have(
				"so it is not the zero polynomial",
				"polynomial_pow(l, p) ≠ vec_zero",
				By(fDegree, pNonzero, polynomial.DegreeVecZero.At(zero)))
			fRoot := a.Have(
				"and it vanishes at t, as l does",
				"polynomial_eval(polynomial_pow(l, p), t) = L.zero",
				By(lOver, tIn, lVanishes, zeroPower, polynomial_evaluation.EvalPow.Read(ring).AsFact().At(p, l, t)))
			algebraic := a.Have(
				"so t is algebraic over P",
				"algebraic_over(L, P, t)",
				By(fOver, fNonzero, fRoot, algebraic_element.AlgebraicOverDef.At(fieldValue, P, t)))

			h, hDef := a.LetAs[Fun[Nat, A]]("h", "minimal_polynomial(L, P, t)")
			minimal := a.Conjuncts(
				a.Have(
					"the minimal polynomial h of t is monic over P",
					"polynomial_over(P, h) ∧ polynomial_monic(h)",
					By(
						Normalized,
						hDef,
						setPSubfield,
						tIn,
						algebraic,
						algebraic_element.MinimalPolynomialSpec.Read(L).AsFact().At(P, t))),
				"h is a polynomial over P",
				"h is monic")
			hOverP, hMonic := minimal[0], minimal[1]
			hPositive := a.Have(
				"it has positive degree",
				"0 < polynomial_degree(h)",
				By(
					Normalized,
					hDef,
					setPSubfield,
					tIn,
					algebraic,
					algebraic_element.MinimalPolynomialPositive.Read(L).AsFact().At(P, t)))
			hDividesOverP := a.Have(
				"it divides every polynomial over P vanishing at t",
				"polynomial_divides(restrict_ring(field_ring(L), P), h, polynomial_pow(l, p))",
				By(
					hDef,
					setPSubfield,
					tIn,
					algebraic,
					fOver,
					fRoot,
					algebraic_element.MinimalPolynomialDivides.Read(L).AsFact().At(P, t, f)))
			hDivides := a.Have(
				"and so divides the p-th power of l over L",
				"polynomial_divides(field_ring(L), h, polynomial_pow(l, p))",
				By(
					setPSubset,
					hDividesOverP,
					polynomial_division.DividesMono.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), P, h, f)))
			hOver := a.Have(
				"h is a polynomial over L",
				"polynomial_over(L.carrier, h)",
				By(setPSubset, hOverP, polynomial.PolynomialOverMono.At(zero, P, carrier, h)))
			hPower := a.Have(
				"a monic divisor of a power of l is a power of l",
				"h = polynomial_pow(l, polynomial_degree(h))",
				By(Normalized, lDef, tIn, hOver, hMonic, hDivides, Read(divisor, L).At(t, p, h)))
			hBound := a.Have(
				"and its degree is at most p",
				"polynomial_degree(h) ≤ p",
				By(hOver, fNonzero, hDivides, fDegree, polynomial_division.DividesDegree.Read(L).AsFact().At(h, f)))
			m, mDef := a.LetAs[Nat]("m", "polynomial_degree(h)")
			hValue := a.Have(
				"h is the m-th power of l, so its value at zero is u ^ m",
				"polynomial_eval(h, L.zero) = monoid_pow(L.mul, L.one, u, m)",
				hPower.Rw(),
				By(lOver, lAtZero, zeroMember, polynomial_evaluation.EvalPow.Read(ring).AsFact().At(m, l, zero)))
			constantTerm := a.Have(
				"the constant term of h is its value at zero",
				"h(0) = monoid_pow(L.mul, L.one, u, m)",
				By(hValue, hOver, zeroMember, polynomial_evaluation.EvalAtZero.Read(ring).At(h)))
			mPowerIn := a.Have(
				"so u ^ m lies in P, h being over P",
				"monoid_pow(L.mul, L.one, u, m) ∈ P",
				By(constantTerm, hOverP, polynomial.PolynomialOverDef.At(zero, P, h)))
			degreeIsP := a.Have(
				"the degree m of h is p",
				"m = p",
				Derive(func(b *Argument) {
					differs := b.SupposeNot()
					notMultiple := b.Have(
						"0 < m < p, so p does not divide m",
						"¬(p ∣ m)",
						ByArith(differs, hBound, hPositive, nat_divides.DividesLessEq.At(p, m)))
					c, d, multiples := b.Obtain2As[Nat, Nat](
						"a multiple of m is one more than a multiple of p",
						"∃c d:num. m * c = p * d + 1",
						By(prime, notMultiple, At(bezout, p, m)))
					tRecovered := b.Have(
						"t is zero minus u",
						"t = L.zero - u",
						ByArith(L, uDef, tIn, uIn))
					uOutside := b.Have(
						"so u lies outside P, as t does",
						"u ∉ P",
						By(
							Normalized,
							tRecovered,
							tOutside,
							setPSubfield,
							field.SubfieldZero.At(fieldValue, P),
							field.SubfieldSub.Read(L).AsFact().At(P, zero, u)))
					uNonzero := b.Have(
						"and u is not zero, which lies in P",
						"u ≠ L.zero",
						By(Normalized, uOutside, setPSubfield, field.SubfieldZero.At(fieldValue, P)))
					large := b.TermAs[Nat]("p * d")
					small := b.TermAs[Nat]("m * c")
					dividend := b.TermAs[A]("monoid_pow(L.mul, L.one, u, m * c)")
					divisorPower := b.TermAs[A]("monoid_pow(L.mul, L.one, u, p * d)")
					divisorIn := b.Have(
						"u ^ (p * d) is a power of u ^ p, so it lies in P",
						"monoid_pow(L.mul, L.one, u, p * d) ∈ P",
						By(
							setPRing,
							uIn,
							uPowerIn,
							comm_monoid.PowPowOn.Read(multiplicative).AsFact().At(u, p, d),
							setPPowers.AsFact().At(b.TermAs[A]("monoid_pow(L.mul, L.one, u, p)"), d)))
					dividendIn := b.Have(
						"u ^ (m * c) is a power of u ^ m, so it lies in P",
						"monoid_pow(L.mul, L.one, u, m * c) ∈ P",
						By(
							setPRing,
							uIn,
							mPowerIn,
							comm_monoid.PowPowOn.Read(multiplicative).AsFact().At(u, m, c),
							setPPowers.AsFact().At(b.TermAs[A]("monoid_pow(L.mul, L.one, u, m)"), c)))
					divisorNonzero := b.Have(
						"a power of the nonzero u is not zero",
						"monoid_pow(L.mul, L.one, u, p * d) ≠ L.zero",
						By(uNonzero, uIn, field.PowEqZeroOn.Read(L).AsFact().At(u, large)))
					oneMore := b.Have(
						"so u ^ (m * c) is u ^ (p * d) times u",
						"monoid_pow(L.mul, L.one, u, m * c) = monoid_pow(L.mul, L.one, u, p * d) * u",
						CalcEq(
							Leg(
								b.TermAs[A]("monoid_pow(L.mul, L.one, u, p * d + 1)"),
								"the exponents differ by one",
								multiples.Rw(),
								Basic()),
							Leg(
								b.TermAs[A]("monoid_pow(L.mul, L.one, u, p * d) * monoid_pow(L.mul, L.one, u, 1)"),
								"a sum of exponents is a product of powers",
								By(uIn, comm_monoid.PowAddOn.Read(multiplicative).AsFact().At(u, large, b.TermAs[Nat]("1")))),
							FinalLeg(
								"and the first power of u is u",
								By(comm_monoid.PowOneOn.Read(multiplicative).At(uMember)))))
					quotient := b.Have(
						"so u is their quotient",
						"u = monoid_pow(L.mul, L.one, u, m * c) / monoid_pow(L.mul, L.one, u, p * d)",
						By(
							oneMore,
							divisorNonzero,
							uIn,
							comm_monoid.PowIn.Read(multiplicative).AsFact().At(u, large),
							comm_monoid.PowIn.Read(multiplicative).AsFact().At(u, small),
							field.DivIn.Read(L).AsFact().At(dividend, divisorPower),
							field.DivLeftMulOn.Read(L).AsFact().At(dividend, divisorPower),
							integral_domain.MulCancelLeft.Read(domain).AsFact().At(
								divisorPower,
								b.TermAs[A]("monoid_pow(L.mul, L.one, u, m * c) / monoid_pow(L.mul, L.one, u, p * d)"),
								u)))
					b.Show(
						"and a quotient of two elements of P lies in P, against u outside P",
						By(
							Normalized,
							quotient,
							uOutside,
							dividendIn,
							divisorIn,
							setPSubfield,
							field.SubfieldDiv.Read(L).AsFact().At(P, dividend, divisorPower)))
				}))
			a.Show(
				"the extension degree of the adjoin is the degree of h",
				By(
					hDef,
					degreeIsP,
					mDef,
					setPSubfield,
					tIn,
					algebraic,
					algebraic_element.AdjoinDegree.Read(L).AsFact().At(P, t)))
		})
	}),
})}

// _ClosureOfField is the host type of the algebraic closure of a field on
// A, set(prod(num, num → A)).
type _ClosureOfField = Set[Prod[Nat, Fun[Nat, A]]]

// PerfectFrobeniusSurjective — in a perfect field of characteristic p every
// element is a p-th power. Embed F in a closed field G and take an irreducible
// factor q of f = X ^ p - a, with a root θ of its image in G, so θ ^ p = ι(a).
// If θ lay outside the image P of F, then θ would have degree p over P
// (PrimeRootDegree), so q would have degree at least p and be a constant
// multiple of f, whose derivative is zero: but q, irreducible over the perfect
// field F, is separable. So θ is the image of an element of F, a p-th root of a.
var PerfectFrobeniusSurjective = perfectFrobeniusSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "PerfectFrobeniusSurjective",
	Key:  "prop_76125134a5c284a0",
	Build: family.Sections(Statement{
		Binders: "∀F:field_on(A). ∀p:num. ∀a:A.",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(F), p)",
			"perfect_field(F)",
			"a ∈ F.carrier",
		},
		Conclusion: "∃b:A. b ∈ F.carrier ∧ monoid_pow(F.mul, F.one, b, p) = a",
		// The embedding AlgebraicClosureFieldOn states, named in that chapter's table only.
		Abbrev: Abbrev{
			{Name: "closureEmbedding", Text: "λx:A. {(0, λn:num. x)}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// A map keeping the identity and the product of a monoid keeps its powers.
		mapPower := ctx.Lemma(Statement{
			Binders: "∀op:(A → A → A). ∀e:A. ∀c:set(A). ∀op₂:(B → B → B). ∀e₂:B. ∀h:(A → B). ∀x:A. ∀n:num.",
			Hypotheses: []string{
				"comm_monoid_on(c, op, e)",
				"x ∈ c",
				"h(e) = e₂",
				"∀u v:A. u ∈ c ∧ v ∈ c ⇒ h(op(u, v)) = op₂(h(u), h(v))",
			},
			Conclusion: "h(monoid_pow(op, e, x, n)) = monoid_pow(op₂, e₂, h(x), n)",
		}, func(
			a *Argument,
			op *Arrow2[A, A, A],
			e *Expr[A],
			c *Expr[Set[A]],
			op2 *Arrow2[B, B, B],
			e2 *Expr[B],
			h *Arrow[A, B],
			x *Expr[A],
			n *Expr[Nat],
			monoid, xIn, identity, multiplicative Fact,
		) {
			a.Induct(n)
			a.Base(
				"the zeroth powers are the identities, which h keeps",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(identity))
			a.Step(
				"one more factor is carried through the product",
				func(b *Argument, ih Fact) {
					b.Show(
						"h keeps the next power",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(
							ih,
							xIn,
							multiplicative.At(x, b.TermAs[A]("monoid_pow(op, e, x, n)")),
							comm_monoid.PowIn.Read(monoid).AsFact().At(x, n)))
				})
		})

		// With F mapped into a closed field G, each a of F has a p-th root in F.
		intoClosed := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀p:num. ∀a:A.",
			Hypotheses: []string{
				"ring_prime_characteristic(field_ring(F), p)",
				"perfect_field(F)",
				"a ∈ F.carrier",
				"algebraically_closed_field(G)",
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			},
			Conclusion: "∃b:A. b ∈ F.carrier ∧ monoid_pow(F.mul, F.one, b, p) = a",
		}, func(
			arg *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			p *Expr[Nat],
			a *Expr[A],
			characteristic, perfect, aIn, closed, hom Fact,
		) {
			ring, targetRing := field.RingOn.Read(F), field.RingOn.Read(G)
			domain := integral_domain.FieldIntegralDomain.Read(F)
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			source, target := arg.TermAs[FieldOps[A]]("F"), arg.TermAs[FieldOps[B]]("G")
			zero, one, carrier :=
				arg.TermAs[A]("F.zero"), arg.TermAs[A]("F.one"), arg.TermAs[Set[A]]("F.carrier")
			targetZero, targetOne := arg.TermAs[B]("G.zero"), arg.TermAs[B]("G.one")
			targetCarrier := arg.TermAs[Set[B]]("G.carrier")
			sourceAdd, sourceMul := arg.TermAs[Op[A]]("F.add"), arg.TermAs[Op[A]]("F.mul")
			targetAdd, targetMul := arg.TermAs[Op[B]]("G.add"), arg.TermAs[Op[B]]("G.mul")
			prime := arg.Unfolded(characteristic, finite_field.PrimeCharacteristicDef)
			two := arg.Have(
				"a prime is at least two",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo))
			pNonzero := arg.Have(
				"so p is not zero",
				"p ≠ 0",
				ByArith(two))
			injective := arg.Have(
				"a homomorphism of fields is one-to-one",
				"injective_on(F.carrier, ι)",
				By(F, G, hom, ring_homomorphism.FieldHomomorphismInjective.At(source, target, ι)))
			P, setPDef := arg.LetAs[Set[B]]("P", "image(ι, F.carrier)")
			setPSubfield := arg.Have(
				"the image of F is a subfield of G",
				"subfield(G, P)",
				By(Normalized, setPDef, F, G, hom, ring_homomorphism.ImageSubfield.At(source, target, ι)))
			keepsZero := arg.Have(
				"ι keeps zero",
				"ι(F.zero) = G.zero",
				By(ring_homomorphism.MapZero.Read(hom)))
			keepsOne := arg.Have(
				"and one",
				"ι(F.one) = G.one",
				By(ring_homomorphism.MapOne.Read(hom)))
			numeral := arg.Have(
				"so ι carries the numeral p of F to that of G",
				"ι(monoid_pow(F.add, F.zero, F.one, p)) = monoid_pow(G.add, G.zero, G.one, p)",
				By(
					ring_homomorphism.MapAdd.Read(hom),
					keepsZero,
					keepsOne,
					comm_ring.AddMonoidOn.Read(ring),
					comm_ring.OneIn.Read(ring),
					At(mapPower, sourceAdd, zero, carrier, targetAdd, targetZero, ι, one, p)))
			targetCharacteristic := arg.Have(
				"so G has characteristic p",
				"ring_prime_characteristic(field_ring(G), p)",
				By(
					prime,
					numeral,
					keepsZero,
					finite_field.PrimeCharacteristicDef.At(arg.TermAs[module_record.RingOps[B]]("field_ring(G)"), p)))

			f, fDef := arg.LetAs[Fun[Nat, A]](
				"f", "vec_sub(basis_vector(F.zero, F.one, p), vec_scalar_mul(a, basis_vector(F.zero, F.one, 0)))")
			coefficients := arg.Have(
				"the coefficients of f read off its two basis vectors",
				"∀i:num. f(i) = F.sub(COND(i = p, F.one, F.zero), F.mul(a, COND(i = 0, F.one, F.zero)))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					b.Show(
						"by the definitions of the difference, the scaling and the basis vectors",
						fDef.Rw(),
						Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
						Basic())
				}))
			top := arg.Have(
				"at p the coefficient of f is one",
				"f(p) = F.one",
				Derive(func(b *Argument) {
					low := b.Have(
						"p is not zero",
						"COND(p = 0, F.one, F.zero) = F.zero",
						By(pNonzero))
					cancelled := b.Have(
						"so the constant term contributes nothing there",
						"F.one - a * F.zero = F.one",
						ByArith(F, aIn, comm_ring.OneIn.Read(ring)))
					b.Show(
						"reading the coefficient at p",
						By(coefficients.At(p), low, cancelled))
				}))
			off := arg.Have(
				"off 0 and p the coefficients of f vanish",
				"∀i:num. i ≠ p ∧ i ≠ 0 ⇒ f(i) = F.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					indices := b.Conjuncts(
						b.Assume(),
						"i is not p",
						"i is not 0")
					cancelled := b.Have(
						"both basis vectors vanish at i",
						"F.zero - a * F.zero = F.zero",
						ByArith(F, aIn, comm_ring.ZeroIn.Read(ring)))
					b.Show(
						"reading the coefficient at i",
						By(Normalized, coefficients.At(i), indices[0], indices[1], cancelled))
				}))
			fOver := arg.Have(
				"f is a polynomial over F",
				"polynomial_over(F.carrier, f)",
				By(
					fDef,
					aIn,
					comm_ring.SubIn.Read(polynomials),
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
					polynomial.BasisVectorOver.Read(ring)))
			fLength := arg.Have(
				"f vanishes past p",
				"vec⟨suc(p)⟩(f)",
				ByArith(off, vec_space.VecDef.Inst[A]().At(zero, arg.TermAs[Nat]("suc(p)"), f)))
			bound := arg.Have(
				"so its degree is at most p",
				"polynomial_degree(f) ≤ p",
				By(fLength, polynomial.DegreeLeast.At(zero, f, p)))
			pastDegree := arg.Unfolded(
				GroupPremises(fOver, polynomial.DegreeVec.At(zero, carrier, f)), vec_space.VecDef)
			notPast := arg.Have(
				"and f does not vanish at p, so p is not past its degree",
				"¬(suc(polynomial_degree(f)) ≤ p)",
				By(Normalized, pastDegree.At(p), top, field.OneNotZeroOn.Read(F)))
			fDegree := arg.Have(
				"so f has degree p",
				"polynomial_degree(f) = p",
				ByArith(bound, notPast))
			fNonzero := arg.Have(
				"and it is not the zero polynomial",
				"f ≠ vec_zero(F.zero)",
				By(Normalized, fDegree, pNonzero, polynomial.DegreeVecZero.At(zero)))
			fDerivative := arg.Have(
				"the derivative of f vanishes, the numeral p being zero in F",
				"polynomial_derivative(f) = vec_zero(F.zero)",
				Derive(func(b *Argument) {
					b.Do(Funext())
					j := b.FixAs[Nat]("j")
					next := b.TermAs[A]("f(suc(j))")
					numeralNext := b.TermAs[A]("monoid_pow(F.add, F.zero, F.one, suc(j))")
					index := b.TermAs[Nat]("suc(j)")
					factors := b.Have(
						"at each index the numeral or the coefficient is zero",
						"monoid_pow(F.add, F.zero, F.one, suc(j)) = F.zero ∨ f(suc(j)) = F.zero",
						Derive(func(c *Argument) {
							c.Cases(c.Term("suc(j) = p"))
							c.When(
								"at p the numeral vanishes",
								func(d *Argument, atP Fact) {
									d.Show(
										"the numeral p is zero",
										By(Normalized, atP, prime))
								})
							c.Otherwise(
								"elsewhere the coefficient vanishes",
								func(d *Argument, elsewhere Fact) {
									positive := d.Have(
										"a successor is not zero",
										"suc(j) ≠ 0",
										By(peano.SucNotZero))
									d.Show(
										"suc(j) is neither 0 nor p",
										By(off.At(index), elsewhere, positive))
								})
						}))
					b.Show(
						"so their product vanishes",
						By(
							polynomial.PolynomialDerivativeDef.At(sourceAdd, zero, sourceMul, one, f, j),
							factors,
							comm_ring.OneIn.Read(ring),
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(one, index),
							fOver,
							polynomial.PolynomialOverDef.At(zero, carrier, f),
							field.MulEqZeroOn.Read(F).AsFact().At(numeralNext, next),
							vec_space.VecZeroDef.At(zero, j)))
				}))

			q, factor := arg.ObtainAs[Fun[Nat, A]](
				"f has positive degree, so an irreducible factor q",
				"∃q:(num → A). polynomial_irreducible(field_ring(F), q) ∧ polynomial_divides(field_ring(F), q, f)",
				ByArith(fOver, fDegree, two, polynomial_division.IrreducibleFactorExists.Read(F).At(f)))
			factorParts := arg.Conjuncts(
				factor,
				"q is irreducible",
				"q divides f")
			irreducible, divides := factorParts[0], factorParts[1]
			qDerivative := arg.Have(
				"F is perfect, so q is separable and its derivative is not zero",
				"polynomial_derivative(q) ≠ vec_zero(F.zero)",
				By(
					irreducible,
					perfect,
					PerfectFieldDef.At(source),
					separable_polynomial.SeparableIffDerivative.Read(F).At(q)))
			qParts := arg.Conjuncts(
				arg.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
				"q is a polynomial over F",
				"q has positive degree",
				"every factorization of q has a factor of degree zero")
			qOver, qPositive := qParts[0], qParts[1]
			r, cofactor := arg.UnpackAs[Fun[Nat, A]](
				arg.Unfolded(divides, polynomial_division.PolynomialDividesDef), "r")
			cofactorParts := arg.Conjuncts(
				cofactor,
				"the cofactor r is a polynomial over F",
				"f is q times r")
			rOver, fProduct := cofactorParts[0], cofactorParts[1]

			carrierSubfield := field.CarrierSubfield.Read(F)
			qMapped := arg.TermAs[Fun[Nat, B]]("λi:num. ι(q(i))")
			rMapped := arg.TermAs[Fun[Nat, B]]("λi:num. ι(r(i))")
			qLaws := algebraic_element.FieldEmbeddingPolynomials.At(source, target, ι, carrier, q)
			qImage := arg.Conjuncts(
				arg.Have(
					"ι carries q to a polynomial over P of the same degree",
					"polynomial_over(P, λi:num. ι(q(i))) ∧ polynomial_degree(λi:num. ι(q(i))) = polynomial_degree(q)",
					By(Normalized, setPDef, F, G, hom, carrierSubfield, qOver, qLaws)),
				"the image of q is over P",
				"the image of q has the degree of q")
			qOverP, qDegree := qImage[0], qImage[1]
			setPInG := arg.Have(
				"P lies in G",
				"P ⊆ G.carrier",
				By(setPSubfield, field.SubfieldSubset.At(target, P)))
			qOverG := arg.Have(
				"so the image of q is a polynomial over G",
				"polynomial_over(G.carrier, λi:num. ι(q(i)))",
				By(setPInG, qOverP, polynomial.PolynomialOverMono.At(targetZero, P, targetCarrier, qMapped)))
			θ, root := arg.ObtainAs[B](
				"it has positive degree, so a root θ in the closed field G",
				"∃θ:B. θ ∈ G.carrier ∧ polynomial_eval(λi:num. ι(q(i)), θ) = G.zero",
				ByArith(closed, qOverG, qDegree, qPositive, algebraic_closure.AlgebraicallyClosedDef.At(target)))
			rootParts := arg.Conjuncts(
				root,
				"θ lies in G",
				"the image of q vanishes at θ")
			θIn, qRoot := rootParts[0], rootParts[1]
			rOverP := arg.Have(
				"ι carries r to a polynomial over P",
				"polynomial_over(P, λi:num. ι(r(i)))",
				By(
					Normalized,
					setPDef,
					F,
					G,
					hom,
					carrierSubfield,
					rOver,
					algebraic_element.FieldEmbeddingPolynomials.At(source, target, ι, carrier, r)))
			rOverG := arg.Have(
				"so over G",
				"polynomial_over(G.carrier, λi:num. ι(r(i)))",
				By(setPInG, rOverP, polynomial.PolynomialOverMono.At(targetZero, P, targetCarrier, rMapped)))
			product := arg.Have(
				"ι carries the factorization of f to G",
				"(λi:num. ι(f(i))) = polynomial_mul(λi:num. ι(q(i)), λi:num. ι(r(i)))",
				By(F, G, hom, carrierSubfield, fProduct, qOver, rOver, qLaws))
			imageVanishes := arg.Have(
				"so the image of f vanishes at θ",
				"polynomial_eval(λi:num. ι(f(i)), θ) = G.zero",
				By(
					product,
					qOverG,
					rOverG,
					θIn,
					qRoot,
					polynomial_evaluation.EvalMulRoot.Read(targetRing).AsFact().At(qMapped, rMapped, θ)))
			conditional := arg.Have(
				"ι keeps a conditional of one and zero",
				"∀s:bool. ι(COND(s, F.one, F.zero)) = COND(s, G.one, G.zero)",
				By(keepsOne, keepsZero))
			conditionalIn := arg.Have(
				"and such a conditional lies in F",
				"∀s:bool. COND(s, F.one, F.zero) ∈ F.carrier",
				By(comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
			fImage := arg.Have(
				"ι carries f to X ^ p - ι(a)",
				"(λi:num. ι(f(i))) = "+
					"vec_sub(basis_vector(G.zero, G.one, p), vec_scalar_mul(ι(a), basis_vector(G.zero, G.one, 0)))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					i := b.FixAs[Nat]("i")
					b.Do(Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)))
					atP, atZero := b.Term("i = p"), b.Term("i = 0")
					high := b.TermAs[A]("COND(i = p, F.one, F.zero)")
					low := b.TermAs[A]("COND(i = 0, F.one, F.zero)")
					scaled := b.TermAs[A]("F.mul(a, COND(i = 0, F.one, F.zero))")
					lowImage := b.Have(
						"ι keeps the product of a and the lower conditional",
						"ι(F.mul(a, COND(i = 0, F.one, F.zero))) = G.mul(ι(a), COND(i = 0, G.one, G.zero))",
						By(
							conditionalIn.At(atZero),
							conditional.At(atZero),
							aIn,
							ring_homomorphism.MapMul.Read(hom).AsFact().At(a, low)))
					scaledIn := b.Have(
						"that product lies in F",
						"F.mul(a, COND(i = 0, F.one, F.zero)) ∈ F.carrier",
						By(conditionalIn.At(atZero), aIn, comm_ring.MulIn.Read(ring).AsFact().At(a, low)))
					b.Show(
						"and ι keeps the difference",
						By(
							coefficients.At(i),
							conditionalIn.At(atP),
							conditional.At(atP),
							scaledIn,
							lowImage,
							ring_homomorphism.MapSub.Read(hom).AsFact().At(high, scaled)))
				}))
			aImage := arg.Have(
				"ι(a) lies in G",
				"ι(a) ∈ G.carrier",
				By(aIn, ring_homomorphism.MapIn.Read(hom).AsFact().At(a)))
			basisP := arg.TermAs[Fun[Nat, B]]("basis_vector(G.zero, G.one, p)")
			scaledBasis := arg.TermAs[Fun[Nat, B]]("vec_scalar_mul(ι(a), basis_vector(G.zero, G.one, 0))")
			aValue := arg.TermAs[B]("ι(a)")
			evaluated := arg.Have(
				"X ^ p - ι(a) takes the value θ ^ p - ι(a) at θ",
				"polynomial_eval(vec_sub(basis_vector(G.zero, G.one, p), "+
					"        vec_scalar_mul(ι(a), basis_vector(G.zero, G.one, 0))), "+
					"    θ) = "+
					"G.sub(monoid_pow(G.mul, G.one, θ, p), ι(a))",
				By(
					aImage,
					θIn,
					polynomial_evaluation.EvalSub.Read(targetRing).AsFact().At(basisP, scaledBasis, θ),
					polynomial_evaluation.EvalBasisVector.Read(targetRing).AsFact().At(p, θ),
					polynomial_evaluation.EvalConstant.Read(targetRing).AsFact().At(aValue, θ),
					polynomial.BasisVectorOver.Read(targetRing),
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(targetRing))))
			difference := arg.Have(
				"so θ ^ p - ι(a) is zero",
				"G.sub(monoid_pow(G.mul, G.one, θ, p), ι(a)) = G.zero",
				By(evaluated, imageVanishes, fImage))
			θPower := arg.Have(
				"that is, θ ^ p is ι(a)",
				"monoid_pow(G.mul, G.one, θ, p) = ι(a)",
				ByArith(
					G,
					difference,
					aImage,
					θIn,
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(targetRing)).AsFact().At(θ, p)))

			arg.Cases(arg.Term("θ ∈ P"))
			arg.When(
				"θ is the image of an element of F, which is a p-th root of a",
				func(c *Argument, inside Fact) {
					x, preimage := c.ObtainAs[A](
						"θ is ι(x) for an x in F",
						"∃x:A. θ = ι(x) ∧ x ∈ F.carrier",
						By(inside, setPDef, set_basic.InImage.At(ι, carrier, θ)))
					preimageParts := c.Conjuncts(
						preimage,
						"θ is the image of x",
						"x lies in F")
					θImage, xIn := preimageParts[0], preimageParts[1]
					power := c.Have(
						"so ι carries the p-th power of x to that of ι(x)",
						"ι(monoid_pow(F.mul, F.one, x, p)) = monoid_pow(G.mul, G.one, ι(x), p)",
						By(
							ring_homomorphism.MapMul.Read(hom),
							keepsOne,
							multiplicative,
							xIn,
							At(mapPower, sourceMul, one, carrier, targetMul, targetOne, ι, x, p)))
					images := c.Have(
						"so x ^ p and a have one image",
						"ι(monoid_pow(F.mul, F.one, x, p)) = ι(a)",
						By(power, θImage, θPower))
					equal := c.Have(
						"and ι is one-to-one on F",
						"monoid_pow(F.mul, F.one, x, p) = a",
						By(
							images,
							xIn,
							aIn,
							comm_monoid.PowIn.Read(multiplicative).AsFact().At(x, p),
							injective,
							functions.InjectiveOnDef.At(carrier, ι)))
					c.Take(x)
					c.Show(
						"x is the p-th root",
						By(xIn, equal))
				})
			arg.Otherwise(
				"θ outside P has degree p over P, so q is a constant multiple of f and has zero derivative",
				func(c *Argument, outside Fact) {
					θPowerIn := c.Have(
						"θ ^ p, being ι(a), lies in P",
						"monoid_pow(G.mul, G.one, θ, p) ∈ P",
						By(Normalized, setPDef, aIn, θPower, set_image.FunInImage.At(ι, carrier, a)))
					degree := c.Have(
						"so θ has degree p over P",
						"extension_degree(G, P, field_adjoin(G, P, {θ})) = p",
						By(
							targetCharacteristic,
							setPSubfield,
							θIn,
							outside,
							θPowerIn,
							PrimeRootDegree.Read(G).AsFact().At(P, p, θ)))
					qDegreeNonzero := c.Have(
						"q has positive degree",
						"polynomial_degree(q) ≠ 0",
						ByArith(qPositive))
					qNonzero := c.Have(
						"so q is not zero",
						"q ≠ vec_zero(F.zero)",
						By(Normalized, qDegreeNonzero, polynomial.DegreeVecZero.At(zero)))
					qImageNonzero := c.Have(
						"nor is its image",
						"(λi:num. ι(q(i))) ≠ vec_zero(G.zero)",
						By(F, G, hom, carrierSubfield, qOver, qNonzero, qLaws))
					algebraic := c.Have(
						"so θ is algebraic over P",
						"algebraic_over(G, P, θ)",
						By(qOverP, qImageNonzero, qRoot, algebraic_element.AlgebraicOverDef.At(target, P, θ)))
					adjoined := c.Have(
						"the degree of θ over P is that of its minimal polynomial",
						"extension_degree(G, P, field_adjoin(G, P, {θ})) = polynomial_degree(minimal_polynomial(G, P, θ))",
						By(setPSubfield, θIn, algebraic, algebraic_element.AdjoinDegree.Read(G).AsFact().At(P, θ)))
					least := c.Have(
						"which is at most that of the image of q",
						"polynomial_degree(minimal_polynomial(G, P, θ)) ≤ polynomial_degree(λi:num. ι(q(i)))",
						By(
							setPSubfield,
							θIn,
							qOverP,
							qImageNonzero,
							qRoot,
							algebraic_element.MinimalPolynomialLeast.Read(G).AsFact().At(P, θ, qMapped)))
					lower := c.Have(
						"so q has degree at least p",
						"p ≤ polynomial_degree(q)",
						ByArith(degree, adjoined, least, qDegree))
					rNonzero := c.Have(
						"r is not zero, since f is not",
						"r ≠ vec_zero(F.zero)",
						By(
							Normalized,
							fNonzero,
							fProduct,
							qOver,
							comm_ring.MulRightZeroOn.Read(polynomials).AsFact().At(q)))
					degrees := c.Have(
						"the degrees of q and r add to that of their product",
						"polynomial_degree(polynomial_mul(q, r)) = polynomial_degree(q) + polynomial_degree(r)",
						By(qOver, rOver, qNonzero, rNonzero, polynomial.DegreeMul.Read(domain).At(q, r)))
					rDegree := c.Have(
						"so r has degree zero",
						"polynomial_degree(r) = 0",
						ByArith(degrees, fProduct, fDegree, lower))
					constant := c.TermAs[A]("r(0)")
					rConstant := c.Have(
						"so r is the constant r(0)",
						"r = vec_scalar_mul(r(0), basis_vector(F.zero, F.one, 0))",
						By(rOver, rDegree, polynomial.DegreeZeroConstant.Read(ring).At(r)))
					constantIn := c.Have(
						"which lies in F",
						"r(0) ∈ F.carrier",
						By(rOver, polynomial.PolynomialOverDef.At(zero, carrier, r)))
					constantNonzero := c.Have(
						"and is not zero, being the leading coefficient of r",
						"r(0) ≠ F.zero",
						By(Normalized, rOver, rNonzero, rDegree, polynomial.DegreeLeading.At(zero, carrier, r)))
					scaled := c.Have(
						"so f is r(0) times q",
						"f = vec_scalar_mul(r(0), q)",
						By(
							Normalized,
							fProduct,
							rConstant,
							constantIn,
							qOver,
							polynomial.PolynomialMulConstant.Read(ring).AsFact().At(constant, q)))
					derivative := c.TermAs[Fun[Nat, A]]("polynomial_derivative(q)")
					scaledDerivative := c.Have(
						"so r(0) times the derivative of q is the derivative of f, which is zero",
						"vec_scalar_mul(r(0), polynomial_derivative(q)) = vec_zero(F.zero)",
						By(
							fDerivative,
							scaled,
							constantIn,
							qOver,
							polynomial.PolynomialOverDef,
							polynomial.DerivativeScalar.Read(ring).AsFact().At(constant, q)))
					derivativeOver := c.Have(
						"the derivative of q is a polynomial over F",
						"polynomial_over(F.carrier, polynomial_derivative(q))",
						By(qOver, polynomial.DerivativeOverCarrier.Read(ring).At(q)))
					zeroDerivative := c.Have(
						"r(0) is not zero and cancels, so q has zero derivative",
						"polynomial_derivative(q) = vec_zero(F.zero)",
						Derive(func(d *Argument) {
							d.Do(Funext())
							i := d.FixAs[Nat]("i")
							value := d.TermAs[A]("polynomial_derivative(q, i)")
							pointwise := d.Have(
								"at i the scaled derivative is r(0) times the coefficient",
								"F.mul(r(0), polynomial_derivative(q, i)) = F.zero",
								By(
									scaledDerivative,
									vec_space.VecScalarMulDef.At(sourceMul, constant, derivative, i),
									vec_space.VecZeroDef.At(zero, i)))
							d.Show(
								"a field has no zero divisors",
								By(
									pointwise,
									constantNonzero,
									constantIn,
									derivativeOver,
									polynomial.PolynomialOverDef.At(zero, carrier, derivative),
									field.MulEqZeroOn.Read(F).AsFact().At(constant, value),
									vec_space.VecZeroDef.At(zero, i)))
						}))
					c.Show(
						"against the separability of q",
						By(qDerivative, zeroDerivative))
				})
		})

		return ctx.Theorem(headline, func(
			arg *Argument,
			F field.FieldFact[on.F],
			p *Expr[Nat],
			a *Expr[A],
			characteristic, perfect, aIn Fact,
		) {
			M, closure := arg.UnpackAs[FieldOps[_ClosureOfField]](
				algebraic_closure.AlgebraicClosureFieldOn.Read(F), "M")
			parts := arg.Conjuncts(
				closure,
				"M is a field",
				"M is algebraically closed",
				"the image of F is a subfield of M",
				"the embedding is an isomorphism onto that image",
				"every element of M is algebraic over the image")
			closureField, closed, imageSubfield, isomorphism := parts[0], parts[1], parts[2], parts[3]
			embedding := arg.TermAs[Fun[A, _ClosureOfField]]("«closureEmbedding»")
			image := arg.TermAs[Set[_ClosureOfField]]("image(«closureEmbedding», F.carrier)")
			onto := arg.Conjuncts(
				arg.Unfolded(isomorphism, ring_homomorphism.RingIsomorphismDef),
				"the embedding is a homomorphism onto the image",
				"it is one-to-one",
				"its image is that carrier")
			imageInM := arg.Have(
				"the image of F lies in M",
				"image(«closureEmbedding», F.carrier) ⊆ M.carrier",
				By(imageSubfield, field.SubfieldSubset.At(M, image)))
			hom := arg.Have(
				"so the embedding is a homomorphism into M",
				"ring_homomorphism(field_ring(F), field_ring(M), «closureEmbedding»)",
				By(
					onto[0],
					imageInM,
					field.RingOn.Read(closureField),
					ring_homomorphism.RingHomExtendTarget.At(
						arg.TermAs[module_record.RingOps[A]]("field_ring(F)"),
						arg.TermAs[module_record.RingOps[_ClosureOfField]]("field_ring(M)"),
						embedding,
						image)))
			arg.Show(
				"the closed field M receives F, so a has a p-th root in F",
				By(
					F,
					closureField,
					characteristic,
					perfect,
					aIn,
					closed,
					hom,
					At(intoClosed, arg.TermAs[FieldOps[A]]("F"), M, embedding, p, a)))
		})
	}),
})}

// FrobeniusImageDegree — the p-th power map of a field of characteristic p
// keeps the degree of a finite extension of subfields. It is a ring
// endomorphism, and a ring map of fields carries subfields to subfields and
// keeps degrees.
var FrobeniusImageDegree = frobeniusImageDegreeThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusImageDegree",
	Key:  "prop_c5fa31e31ba9304d",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀p:num. ∀F L:set(A).",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(M), p)",
			"subfield(M, F)",
			"subfield(M, L)",
			"F ⊆ L",
			"finite_extension(M, F, L)",
		},
		Conclusion: "subfield(M, «powers»(L)) ∧ " +
			"finite_extension(M, «powers»(F), «powers»(L)) ∧ " +
			"extension_degree(M, «powers»(F), «powers»(L)) = extension_degree(M, F, L)",
		Abbrev: Abbrev{
			{Name: "powers", Text: "image(frobenius_power(field_ring(M), p))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		p *Expr[Nat],
		F, L *Expr[Set[A]],
		characteristic, subfieldF, subfieldL, inclusion, finite Fact,
	) {
		m := a.TermAs[FieldOps[A]]("M")
		power := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), p)")
		a.Show(
			"the p-th power map is a ring endomorphism, and such a "+
				"map carries L to a subfield and keeps the degree over F",
			By(
				characteristic,
				finite_field.FrobeniusRingHomomorphism.Read(field.RingOn.Read(M)).At(p, a.TermAs[Nat]("1")),
				nat_arith.PowOne,
				subfieldF,
				subfieldL,
				inclusion,
				finite,
				algebraic_element.FieldEmbeddingSubfieldsAdjoin.Read(M).At(m, power),
				algebraic_element.FieldEmbeddingFiniteDegree.Read(M).At(m, power, F, L)))
	}),
})}

// PerfectSubfieldPowers — a perfect subfield is its own p-th powers: read as a
// field, it has the characteristic of M and a p-th root of each of its points.
var PerfectSubfieldPowers = perfectSubfieldPowersThm{family.Add(registry.ProofEntry{
	Name: "PerfectSubfieldPowers",
	Key:  "prop_8c684a575a30b2bc",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀p:num.",
		Hypotheses: []string{
			"ring_prime_characteristic(field_ring(M), p)",
			"subfield(M, k)",
			"perfect_field(restrict_field(M, k))",
		},
		Conclusion: "image(frobenius_power(field_ring(M), p), k) = k",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		p *Expr[Nat],
		characteristic, subfieldK, perfect Fact,
	) {
		restricted := a.Have(
			"k is a field under the operations of M",
			"field_on(restrict_field(M, k))",
			By(subfieldK, field.SubfieldFieldOn.Read(M).At(k)))
		restrictedCharacteristic := a.Have(
			"with the characteristic of M, its one and addition being those of M",
			"ring_prime_characteristic(field_ring(restrict_field(M, k)), p)",
			By(characteristic, finite_field.PrimeCharacteristicDef))
		roots := a.Have(
			"so each point of the perfect field k has a p-th root in k",
			"∀c:A. c ∈ k ⇒ ∃b:A. b ∈ k ∧ monoid_pow(M.mul, M.one, b, p) = c",
			By(restrictedCharacteristic, perfect, PerfectFrobeniusSurjective.Read(restricted)))
		covered := a.Have(
			"so k lies among its own p-th powers",
			"k ⊆ image(frobenius_power(field_ring(M), p), k)",
			BySets(roots, finite_field.FrobeniusPowerDef))
		a.Show(
			"and holds them",
			By(subfieldK, covered, finite_field.PowersInsideSubfield.Read(M).At(p, k), set_order.SubsetAntisym))
	}),
})}

// FiniteExtensionPerfect — a finite extension l of a perfect field k is
// perfect. In characteristic zero every field is. In characteristic p the p-th
// power map keeps degrees and fixes k, so the p-th powers of l lie between k
// and l with the degree of l over k: they are all of l, and a field in which
// every element is a p-th power is perfect.
var FiniteExtensionPerfect = finiteExtensionPerfectThm{family.Add(registry.ProofEntry{
	Name: "FiniteExtensionPerfect",
	Key:  "prop_f584473670c26b79",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k l:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"perfect_field(restrict_field(M, k))",
		},
		Conclusion: "perfect_field(restrict_field(M, l))",
		Abbrev: Abbrev{
			{Name: "powers", Text: "image(frobenius_power(field_ring(M), p))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, l *Expr[Set[A]],
		subfieldK, subfieldL, inclusion, finite, perfect Fact,
	) {
		m := a.TermAs[FieldOps[A]]("M")
		a.Cases(a.TermAs[Bool]("characteristic_zero(field_ring(M))"))
		a.When(
			"in characteristic zero every irreducible polynomial over l is separable",
			func(b *Argument, zero Fact) {
				b.Do(Unfold(PerfectFieldDef))
				f := b.FixAs[Fun[Nat, A]]("f")
				irreducible := b.Assume()
				b.Show(
					"f is separable, the ring of l being the restriction of M's",
					By(
						zero,
						subfieldL,
						irreducible,
						separable_polynomial.CharZeroIrreducibleSeparable.Read(M).At(l, f),
						field.RestrictFieldRing.At(m, l)))
			})
		a.Otherwise(
			"in characteristic p the p-th powers of l are all of l",
			func(b *Argument, notZero Fact) {
				p, characteristic := b.ObtainAs[Nat](
					"the characteristic is a prime p",
					"∃p:num. ring_prime_characteristic(field_ring(M), p)",
					By(Normalized, notZero, finite_field.FieldCharacteristicCases.Read(M)))
				fixed := b.Have(
					"k, perfect, is its own p-th powers",
					"«powers»(k) = k",
					By(characteristic, subfieldK, perfect, PerfectSubfieldPowers.Read(M).At(k, p)))
				fieldL := b.Have(
					"l is a field under the operations of M",
					"field_on(restrict_field(M, l))",
					By(subfieldL, field.SubfieldFieldOn.Read(M).At(l)))
				characteristicL := b.Have(
					"of characteristic p, its zero, one and addition being those of M",
					"ring_prime_characteristic(field_ring(restrict_field(M, l)), p)",
					By(Normalized, characteristic, finite_field.PrimeCharacteristicDef))
				powersL := b.Have(
					"and it holds its p-th powers",
					"«powers»(l) ⊆ l",
					By(subfieldL, finite_field.PowersInsideSubfield.Read(M).At(p, l)))
				images := b.Conjuncts(
					b.Have(
						"the p-th powers of l have the degree of l over k",
						"subfield(M, «powers»(l)) ∧ extension_degree(M, k, «powers»(l)) = extension_degree(M, k, l)",
						By(
							Normalized,
							fixed,
							characteristic,
							subfieldK,
							subfieldL,
							inclusion,
							finite,
							FrobeniusImageDegree.Read(M).At(p, k, l))),
					"the p-th powers of l form a subfield",
					"of degree [l : k]")
				subfieldPowersL, degreeBelow := images[0], images[1]
				kInPowers := b.Have(
					"k lies in them, being its own p-th powers",
					"k ⊆ «powers»(l)",
					BySets(fixed, inclusion))
				onto := b.Have(
					"they lie between k and l with the degree of l, so l is its own p-th powers",
					"l = «powers»(l)",
					By(
						subfieldK,
						subfieldPowersL,
						subfieldL,
						kInPowers,
						powersL,
						finite,
						degreeBelow,
						field_extension.IntermediateDegree.Read(M).At(k, b.TermAs[Set[A]]("«powers»(l)"), l)))
				rootsL := b.Have(
					"every point of l is a p-th power in l",
					"∀a:A. a ∈ l ⇒ ∃b:A. b ∈ l ∧ monoid_pow(M.mul, M.one, b, p) = a",
					BySets(onto, finite_field.FrobeniusPowerDef.Inst[A]().At(b.TermAs[RingOps[A]]("field_ring(M)"), p)))
				b.Show(
					"a field of its p-th powers is perfect",
					By(fieldL, characteristicL, rootsL, FrobeniusSurjectivePerfect.Read(fieldL).AsFact().At(p)))
			})
	}),
})}

// FiniteFieldIsPerfect — a finite field is perfect: every irreducible
// polynomial over it is separable.
var FiniteFieldIsPerfect = finiteFieldIsPerfectThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldIsPerfect",
	Key:  "prop_c73bfc942bb5014f",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_on(A).",
		Hypotheses: []string{"finite(F.carrier)"},
		Conclusion: "perfect_field(F)",
	}, func(a *Argument, F field.FieldFact[on.F], finiteCarrier Fact) {
		a.Show(
			"irreducible polynomials over a finite field are separable",
			Simp(Fwd(PerfectFieldDef)),
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, A]]("p")
				irreducible := b.Assume()
				b.Show(
					"p is separable",
					By(finiteCarrier, irreducible, finite_field.IrreducibleOverFiniteFieldSeparable.Read(F).At(p)))
			}))
	}),
})}
