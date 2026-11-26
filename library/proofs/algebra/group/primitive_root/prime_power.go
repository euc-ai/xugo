// prime_power.go — the units mod a power of an odd prime form a cyclic group:
// a primitive root mod p lifts to one mod every power of p.

package primitive_root

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/units_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// DivisorPinnedByPrimePower — for a prime p and n > 0, a multiple e of n that
// divides n · p ^ (j + 1) but not n · p ^ j is n · p ^ (j + 1). Write e = n · m
// and p ^ (j + 1) = m · c. If p divided c, then p ^ j = m · (c / p) and m would
// divide p ^ j; so p does not divide c, which, dividing a power of p, is then
// coprime to it and is 1.
var DivisorPinnedByPrimePower = divisorPinnedByPrimePowerThm{family.Add(registry.ProofEntry{
	Name: "DivisorPinnedByPrimePower",
	Key:  "prop_f08afcb8ab724f95",
	Build: family.Theorem(Statement{
		Binders: "∀p n j e:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"0 < n",
			"e ∣ n * p ^ (j + 1)",
			"n ∣ e",
			"¬(e ∣ n * p ^ j)",
		},
		Conclusion: "e = n * p ^ (j + 1)",
	}, func(a *Argument, p, n, j, e *Expr[Nat], prime, positive, divides, multiple, notSmaller Fact) {
		power := a.TermAs[Nat]("p ^ (j + 1)")
		m, cofactor := a.ObtainAs[Nat](
			"e is a multiple n · m of n",
			"∃m:num. e = n * m",
			By(multiple, nat_divides.DividesFactor.At(n, e)))
		mDivides := a.Have(
			"cancelling n, m divides p ^ (j + 1)",
			"m ∣ p ^ (j + 1)",
			ByArith(positive, cofactor, divides, nat_divides.MulDividesLCancel.At(n, m, power)))
		mNotDivides := a.Have(
			"m does not divide p ^ j, or e = n · m would divide n · p ^ j",
			"¬(m ∣ p ^ j)",
			By(
				Normalized,
				notSmaller,
				cofactor,
				nat_divides.MulDividesMulLeft.At(n, m, a.TermAs[Nat]("p ^ j"))))
		c, split := a.ObtainAs[Nat](
			"write p ^ (j + 1) = m · c",
			"∃c:num. p ^ (j + 1) = m * c",
			By(mDivides, nat_divides.DividesFactor.At(m, power)))
		a.Cases(a.Term("p ∣ c"))
		a.When(
			"if p divided c, m would divide p ^ j",
			func(b *Argument, pDivides Fact) {
				_, quotient := b.ObtainAs[Nat](
					"c = p · q",
					"∃q:num. c = p * q",
					By(pDivides, nat_divides.DividesFactor.At(p, c)))
				lower := b.Have(
					"cancelling p from p · p ^ j = p · (m · q)",
					"p ^ j = m * q",
					ByArith(
						split,
						Scaled(m, quotient),
						prime,
						nat_arith.PowAdd.At(p, j, b.TermAs[Nat]("1")),
						nat_arith.PowOne.At(p),
						nat_arith.MulEqLCancel.At(p, b.TermAs[Nat]("p ^ j"), b.TermAs[Nat]("m * q")),
						nat_prime.PrimeAtLeastTwo.At(p)))
				b.Show(
					"which m does not",
					By(Normalized, mNotDivides, lower, nat_divides.DividesFactor.At(m, b.TermAs[Nat]("p ^ j"))))
			})
		a.Otherwise(
			"so p does not divide c",
			func(b *Argument, notDivides Fact) {
				one := b.Have(
					"c divides a power of p and is prime to it, so c = 1",
					"c = 1",
					ByArith(
						notDivides,
						prime,
						split,
						nat_prime.CoprimePrimePowerIff.At(p, b.TermAs[Nat]("j + 1"), c),
						nat_divides.DividesOwnMultiple.At(c, m),
						nat_gcd.Coprime.At(c, power),
						nat_divides.DividesRefl.At(c)))
				b.Show(
					"so m = p ^ (j + 1) and e = n · p ^ (j + 1)",
					ByArith(cofactor, split, Scaled(m, one)))
			})
	}),
})}

// PthPowerOfOnePlusMultiple — for an odd prime p, (1 + p · a) ^ p is
// 1 + p² · a plus a multiple of p³ · a². Expanded to second order,
// (1 + p · a) ^ p is 1 + p · (p · a) + C(p, 2) · (p · a)² plus a multiple of
// (p · a)³, and p divides C(p, 2) since 0 < 2 < p.
var PthPowerOfOnePlusMultiple = pthPowerOfOnePlusMultipleThm{family.Add(registry.ProofEntry{
	Name: "PthPowerOfOnePlusMultiple",
	Key:  "prop_9428336744ecda7d",
	Build: family.Theorem(Statement{
		Binders: "∀p a:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "∃w:num. (1 + p * a) ^ p = 1 + p ^ 2 * a + p ^ 3 * a ^ 2 * w",
	}, func(arg *Argument, p, a *Expr[Nat], prime, odd Fact) {
		_, expansion := arg.UnpackAs[Nat](binomial.PowSecondOrder.At(arg.TermAs[Nat]("p * a"), p), "r")
		_, middle := arg.ObtainAs[Nat](
			"p divides C(p, 2), as 0 < 2 < p",
			"∃c:num. binomial(p, 2) = p * c",
			ByArith(
				prime,
				odd,
				nat_prime.PrimeDividesBinomial.At(p, arg.TermAs[Nat]("2")),
				nat_prime.PrimeAtLeastTwo.At(p),
				nat_divides.DividesFactor.At(p, arg.TermAs[Nat]("binomial(p, 2)"))))
		arg.Take(arg.TermAs[Nat]("c + a * r"))
		arg.Show(
			"C(p, 2) · (p · a)² = p³ · a² · c and (p · a)³ · r = p³ · a² · (a · r)",
			ByArith(expansion, Scaled(arg.TermAs[Nat]("(p * a) ^ 2"), middle)))
	}),
})}

// OnePlusPPowersNotOne — for an odd prime p and t not divisible by p,
// (1 + p · t) ^ (p ^ i) is not 1 mod p ^ (i + 2). By induction on i it is
// 1 + p ^ (i + 1) · u with p not dividing u: raising 1 + p · (p ^ i · u) to the
// p-th power gives 1 + p ^ (i + 2) · u plus a multiple of p ^ (i + 3)
// (PthPowerOfOnePlusMultiple), and u plus a multiple of p is still prime to
// p. If it were 1 mod p ^ (i + 2), then p ^ (i + 2) would divide
// p ^ (i + 1) · u, and p would divide u.
var OnePlusPPowersNotOne = onePlusPPowersNotOneThm{family.Add(registry.ProofEntry{
	Name: "OnePlusPPowersNotOne",
	Key:  "prop_fb0092fd0c0bb7b7",
	Build: family.Sections(Statement{
		Binders: "∀p t i:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"¬(p ∣ t)",
		},
		Conclusion: "¬((1 + p * t) ^ (p ^ i) ≡ 1 (mod p ^ (i + 2)))",
		Abbrev: Abbrev{
			{Name: "extra", Text: "p ^ i * u ^ 2 * w"},
			{Name: "next", Text: "p * «extra» + u"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		exact := ctx.Lemma(Statement{
			Binders: "∀p t i:num.",
			Hypotheses: []string{
				"nat_prime(p)",
				"p ≠ 2",
				"¬(p ∣ t)",
			},
			Conclusion: "∃u:num. (1 + p * t) ^ (p ^ i) = 1 + p ^ (i + 1) * u ∧ ¬(p ∣ u)",
		}, func(a *Argument, p, t *Expr[Nat], prime, odd, coprime Fact) {
			one := a.TermAs[Nat]("1")
			a.Induct("i")
			a.Base(
				"(1 + p · t) ^ 1 = 1 + p · t",
				func(b *Argument) {
					b.Take(t)
					b.Show(
						"with u = t",
						Simp(Fwd(nat_arith.PowAdd), Fwd(nat_arith.NatPow), Fwd(nat_arith.PowOne)),
						ByArith(coprime))
				})
			a.Step(
				"one more p-th power",
				func(b *Argument, ih Fact) {
					u, stepped := b.UnpackAs[Nat](ih, "u")
					parts := b.Conjuncts(
						stepped,
						"(1 + p · t) ^ (p ^ i) = 1 + p ^ (i + 1) · u",
						"p does not divide u")
					shift := b.Have(
						"the next power of p is one more factor p",
						"p ^ suc(i) = p ^ i * p",
						ByArith(nat_arith.NatPow))
					regroup := b.Have(
						"the power so far is 1 + p · (p ^ i · u)",
						"(1 + p * t) ^ (p ^ i) = 1 + p * (p ^ i * u)",
						ByArith(
							parts[0],
							Scaled(u, nat_arith.PowAdd.At(p, b.TermAs[Nat]("i"), one)),
							Scaled(b.TermAs[Nat]("p ^ i * u"), nat_arith.PowOne.At(p))))
					power := b.Have(
						"the next power is its p-th power",
						"(1 + p * t) ^ (p ^ suc(i)) = (1 + p * (p ^ i * u)) ^ p",
						By(shift, regroup, nat_arith.PowPow.At(b.TermAs[Nat]("1 + p * t"), b.TermAs[Nat]("p ^ i"), p)))
					_, lifted := b.UnpackAs[Nat](
						GroupPremises(prime, odd, PthPowerOfOnePlusMultiple.At(p, b.TermAs[Nat]("p ^ i * u"))),
						"w")
					extra := b.TermAs[Nat]("«extra»")
					next := b.TermAs[Nat]("«next»")
					b.Take(next)
					b.Show(
						"(1 + p · (p ^ i · u)) ^ p = 1 + p ^ (i + 2) · (u + p · p ^ i · u² · w)",
						SplitConj(
							Case(
								"the exponent of p goes up by one",
								ByArith(
									power,
									lifted,
									Scaled(b.TermAs[Nat]("p * «next»"), shift),
									Scaled(next, nat_arith.PowAdd.At(p, b.TermAs[Nat]("suc(i)"), one)),
									Scaled(b.TermAs[Nat]("p ^ suc(i) * «next»"), nat_arith.PowOne.At(p)))),
							Case(
								"u plus a multiple of p is still prime to p",
								By(
									parts[1],
									nat_divides.DividesAddCancel.At(p, b.TermAs[Nat]("p * «extra»"), u),
									nat_divides.DividesOwnMultiple.At(p, extra)))))
				})
		})
		return ctx.Theorem(headline, func(a *Argument, p, t, i *Expr[Nat], prime, odd, coprime Fact) {
			u, exactly := a.UnpackAs[Nat](GroupPremises(prime, odd, coprime, At(exact, p, t, i)), "u")
			parts := a.Conjuncts(
				exactly,
				"(1 + p · t) ^ (p ^ i) = 1 + p ^ (i + 1) · u",
				"p does not divide u")
			congruent := a.SupposeNot()
			lifted := a.TermAs[Nat]("p ^ (i + 1) * u")
			modulus := a.TermAs[Nat]("p ^ (i + 2)")
			zero := a.TermAs[Nat]("0")
			divides := a.Have(
				"then p ^ (i + 2) divides p ^ (i + 1) · u",
				"p ^ (i + 2) ∣ p ^ (i + 1) * u",
				ByArith(
					congruent,
					parts[0],
					nat_congruence.AddCancel.At(a.TermAs[Nat]("1"), lifted, zero, modulus),
					nat_congruence.CongDef.At(lifted, zero, modulus),
					nat_div_mod.ZeroMod.At(modulus),
					nat_divides.DividesMod.At(modulus, lifted)))
			regroup := a.Have(
				"p ^ (i + 2) is p ^ (i + 1) with one more factor p",
				"p ^ (i + 2) = p ^ (i + 1) * p",
				ByArith(
					nat_arith.PowAdd.At(p, i, a.TermAs[Nat]("2")),
					Scaled(p, nat_arith.PowAdd.At(p, i, a.TermAs[Nat]("1")))))
			a.Show(
				"cancelling p ^ (i + 1), p would divide u",
				ByArith(
					parts[1],
					divides,
					prime,
					regroup,
					nat_divides.MulDividesLCancel.At(a.TermAs[Nat]("p ^ (i + 1)"), p, u),
					nat_arith.PowEqZero.At(p, a.TermAs[Nat]("i + 1")),
					nat_prime.PrimeAtLeastTwo.At(p)))
		})
	}),
})}

// CongruentWithPExactlyDividing — for a prime p and g prime to p, some
// h ≡ g (mod p) has h ^ (p − 1) = 1 + p · t with p not dividing t, so p
// divides h ^ (p − 1) − 1 exactly once. By Fermat's little theorem
// g ^ (p − 1) = 1 + p · s. If p does not divide s, h = g. Otherwise
// g ^ (p − 1) = 1 + p² · q, and h = g · (1 + p) works: (1 + p) ^ (p − 1) is
// 1 + (p − 1) · p plus a multiple of p², so h ^ (p − 1) = 1 + p · t with t
// congruent to p − 1 mod p.
var CongruentWithPExactlyDividing = congruentWithPExactlyDividingThm{family.Add(registry.ProofEntry{
	Name: "CongruentWithPExactlyDividing",
	Key:  "prop_69b1c55d49504fd",
	Build: family.Theorem(Statement{
		Binders: "∀p g:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"¬(p ∣ g)",
		},
		Conclusion: "∃h t:num. h ≡ g (mod p) ∧ h ^ (p - 1) = 1 + p * t ∧ ¬(p ∣ t)",
		Abbrev: Abbrev{
			{Name: "cofactor", Text: "binomial(p - 1, 2) + p * r + q * (1 + p) ^ (p - 1)"},
		},
	}, func(a *Argument, p, g *Expr[Nat], prime, coprime Fact) {
		one := a.TermAs[Nat]("1")
		fermatPower := a.TermAs[Nat]("g ^ (p - 1)")
		s, sDef := a.LetAs[Nat]("s", "div(g ^ (p - 1), p)")
		fermat := a.Have(
			"by Fermat's little theorem g ^ (p − 1) leaves remainder 1 mod p",
			"g ^ (p - 1) = 1 + p * s",
			ByArith(
				prime,
				coprime,
				sDef,
				nat_prime.FermatLittleCoprime.At(p, g),
				nat_congruence.CongDef.At(fermatPower, one, p),
				nat_div_mod.ModLessThan.At(one, p),
				nat_div_mod.Division.At(fermatPower, p),
				nat_prime.PrimeAtLeastTwo.At(p)))
		a.Cases(a.Term("p ∣ s"))
		a.When(
			"p divides s: g · (1 + p) works",
			func(b *Argument, pDivides Fact) {
				_, quotient := b.ObtainAs[Nat](
					"s = p · q, so g ^ (p − 1) = 1 + p² · q",
					"∃q:num. s = p * q",
					By(pDivides, nat_divides.DividesFactor.At(p, s)))
				_, expansion := b.UnpackAs[Nat](binomial.PowSecondOrder.At(p, b.TermAs[Nat]("p - 1")), "r")
				power := b.TermAs[Nat]("(1 + p) ^ (p - 1)")
				rest := b.TermAs[Nat]("«cofactor»")
				b.Take(b.TermAs[Nat]("g * (1 + p)"))
				b.Take(b.TermAs[Nat]("p * «cofactor» + (p - 1)"))
				b.Show(
					"h = g · (1 + p) and t = p − 1 plus a multiple of p",
					SplitConjAll(
						Case(
							"g · (1 + p) = g + g · p is congruent to g",
							ByArith(
								nat_div_mod.ModEq.At(b.TermAs[Nat]("g * (1 + p)"), g, p, g),
								nat_congruence.CongDef.At(b.TermAs[Nat]("g * (1 + p)"), g, p))),
						Case(
							"(g · (1 + p)) ^ (p − 1) = (1 + p² · q) · (1 + (p − 1) · p + p² · (C(p − 1, 2) + p · r))",
							ByArith(
								Scaled(power, fermat),
								Scaled(b.TermAs[Nat]("p * (1 + p) ^ (p - 1)"), quotient),
								expansion,
								nat_arith.MulPowDistrib.At(g, b.TermAs[Nat]("1 + p"), b.TermAs[Nat]("p - 1")))),
						Case(
							"p does not divide p − 1, so not t",
							ByArith(
								prime,
								nat_divides.DividesAddCancel.At(p, b.TermAs[Nat]("p * «cofactor»"), b.TermAs[Nat]("p - 1")),
								nat_divides.DividesOwnMultiple.At(p, rest),
								nat_divides.DividesLessEq.At(p, b.TermAs[Nat]("p - 1")),
								nat_prime.PrimeAtLeastTwo.At(p)))))
			})
		a.Otherwise(
			"p does not divide s: g itself works",
			func(b *Argument, notDivides Fact) {
				b.Take(g)
				b.Take(s)
				b.Show(
					"with t = s",
					By(fermat, notDivides, nat_congruence.CongDef.At(g, g, p)))
			})
	}),
})}

// UnitsModPrimePowerCyclic — the units mod a power p ^ k of an odd prime form
// a cyclic group. For k = 1 they are the units mod p. For k = j + 2, take a
// primitive root g mod p and its lift h (CongruentWithPExactlyDividing); the residue x of h
// mod p ^ k is a unit, and its order e divides the number
// φ(p ^ k) = (p − 1) · p ^ (j + 1) of units. A power h ^ m is 1 mod p ^ k
// exactly when e divides m; h ^ e, then 1 mod p as well, makes p − 1 divide
// e, as h ≡ g; and e does not divide (p − 1) · p ^ j, since h ^ ((p − 1) · p ^ j)
// = (1 + p · t) ^ (p ^ j) is not 1 mod p ^ (j + 2) (OnePlusPPowersNotOne).
// So e = φ(p ^ k) (DivisorPinnedByPrimePower) and x generates the group.
var UnitsModPrimePowerCyclic = unitsModPrimePowerCyclicThm{family.Add(registry.ProofEntry{
	Name: "UnitsModPrimePowerCyclic",
	Key:  "prop_327f1611e6f6f6f2",
	Build: family.Theorem(Statement{
		Binders: "∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"0 < k",
		},
		Conclusion: "cyclic_group(units_mod(p ^ k))",
		Abbrev: Abbrev{
			{Name: "units", Text: "units_mod(p ^ (j + 2))"},
			{Name: "residue", Text: "rem(h, p ^ (j + 2))"},
			{Name: "order", Text: "group_element_order(«units», «residue»)"},
		},
	}, func(a *Argument, p, k *Expr[Nat], prime, odd, positive Fact) {
		a.Cases(a.Term("k = 1"))
		a.When(
			"k = 1: these are the units mod p",
			func(b *Argument, first Fact) {
				b.Show(
					"which form a cyclic group",
					By(first, prime, UnitsModPrimeCyclic.At(p), nat_arith.PowOne.At(p)))
			})
		a.Otherwise(
			"k ≥ 2: a lift h of a primitive root mod p has order φ(p ^ k)",
			func(b *Argument, notFirst Fact) {
				one := b.TermAs[Nat]("1")
				j, jDef := b.LetAs[Nat]("j", "k - 2")
				split := b.Have(
					"k is neither 0 nor 1, so it is j + 2",
					"k = j + 2",
					ByArith(jDef, positive, notFirst))
				b.Do(split.Rw())
				g, primitive := b.UnpackAs[Nat](GroupPremises(prime, PrimitiveRootModPrime.At(p)), "g")
				root := b.Conjuncts(
					primitive,
					"p does not divide g",
					"the powers of g that are 1 mod p are those to a multiple of p − 1")
				h, t, lift := b.Unpack2As[Nat, Nat](
					GroupPremises(prime, root[0], CongruentWithPExactlyDividing.At(p, g)), "h", "t")
				lifted := b.Conjuncts(
					lift,
					"h ≡ g (mod p)",
					"h ^ (p − 1) = 1 + p · t",
					"p does not divide t")
				modulus := b.TermAs[Nat]("p ^ (j + 2)")
				x := b.TermAs[Nat]("«residue»")
				e := b.TermAs[Nat]("«order»")
				hPower := b.TermAs[Nat]("h ^ «order»")
				notH := b.Have(
					"p does not divide h, which is congruent to g",
					"¬(p ∣ h)",
					By(
						Normalized,
						lifted[0],
						root[0],
						nat_congruence.CongDef.At(h, g, p),
						nat_divides.DividesMod.At(p, h),
						nat_divides.DividesMod.At(p, g)))
				units := b.Have(
					"the units mod p ^ k form an abelian group, a power of a prime being positive",
					"abelian_group_on(«units»)",
					ByArith(
						prime,
						units_mod.AbelianGroupOn.At(modulus),
						nat_order.PowPositive.At(p, b.TermAs[Nat]("j + 2")),
						nat_prime.PrimeAtLeastTwo.At(p)))
				finite := b.Have(
					"there are finitely many of them",
					"finite(«units».carrier)",
					By(units_mod.CarrierHasSize.At(modulus), cardinality.HasSizeDef))
				unit := b.Have(
					"the residue x of h mod p ^ k is a unit, h being prime to p",
					"«residue» ∈ «units».carrier",
					ByArith(
						prime,
						notH,
						nat_prime.CoprimePrimePowerIff.At(p, b.TermAs[Nat]("j + 2"), h),
						nat_order.PowPositive.At(p, b.TermAs[Nat]("j + 2")),
						nat_prime.PrimeAtLeastTwo.At(p),
						units_mod.ResidueIn.At(modulus, h)))
				size := b.Have(
					"there are φ(p ^ (j + 2)) = (p − 1) · p ^ (j + 1) units",
					"card(«units».carrier) = (p - 1) * p ^ (j + 1)",
					ByArith(
						prime,
						units_mod.CarrierHasSize.At(modulus),
						cardinality.HasSizeDef,
						totient.TotientPrimePower.At(p, b.TermAs[Nat]("j + 2")),
						nat_monus.MulPowSubOne.At(p, b.TermAs[Nat]("j + 2")),
						nat_monus.RightSubDistrib.At(p, one, b.TermAs[Nat]("p ^ (j + 2 - 1)"))))
				grp := abelian_group.GroupOn.Read(units)
				xm := b.MemberOf[on.Any](x, unit)
				dividesSize := b.Have(
					"the order e of x divides the number of units",
					"«order» ∣ (p - 1) * p ^ (j + 1)",
					ByArith(finite, unit, size, cyclic_group.OrderDividesCard.Read(grp)))
				powers := b.Have(
					"a power h ^ m is 1 mod p ^ k exactly when e divides m",
					"∀m:num. h ^ m ≡ 1 (mod p ^ (j + 2)) ⇔ «order» ∣ m",
					b.ForEach(func(m *Expr[Nat]) Action {
						return By(
							unit,
							cyclic_group.OrderDividesIff.Read(grp).At(xm, m),
							units_mod.UnitsPowMod.At(modulus, x, m),
							units_mod.UnitsModDef,
							group.GroupOneDef,
							nat_congruence.CongDef,
							nat_congruence.ResidueCongruent.At(h, modulus),
							nat_congruence.PowCongruent.At(x, h, modulus, m))
					}))
				modP := b.Have(
					"so h ^ e is 1 mod p ^ k, and so mod p",
					"h ^ «order» ≡ 1 (mod p)",
					ByArith(
						powers.At(e),
						positive,
						nat_divides.DividesRefl.At(e),
						nat_congruence.CongDef.At(hPower, one, modulus),
						nat_congruence.CongDef.At(hPower, one, p),
						nat_div_mod.ModMod.At(hPower, p, b.TermAs[Nat]("p ^ (j + 1)")),
						nat_div_mod.ModMod.At(one, p, b.TermAs[Nat]("p ^ (j + 1)")),
						nat_monus.MulPowSubOne.At(p, b.TermAs[Nat]("j + 2"))))
				multiple := b.Have(
					"p − 1 divides e: g ^ e ≡ h ^ e ≡ 1 mod p",
					"p - 1 ∣ «order»",
					By(
						root[1].At(e),
						lifted[0],
						modP,
						nat_congruence.PowCongruent.At(h, g, p, e),
						nat_congruence.CongDef))
				notSmaller := b.Have(
					"e does not divide (p − 1) · p ^ j: h ^ ((p − 1) · p "+
						"^ j) = (1 + p · t) ^ (p ^ j) is not 1 mod p ^ (j + 2)",
					"¬(«order» ∣ (p - 1) * p ^ j)",
					Derive(func(c *Argument) {
						divides := c.SupposeNot()
						c.Show(
							"else it would be",
							By(
								divides,
								powers.At(c.TermAs[Nat]("(p - 1) * p ^ j")),
								lifted[1],
								prime,
								odd,
								lifted[2],
								nat_arith.PowPow.At(h, c.TermAs[Nat]("p - 1"), c.TermAs[Nat]("p ^ j")),
								OnePlusPPowersNotOne.At(p, t, j)))
					}))
				full := b.Have(
					"so e = (p − 1) · p ^ (j + 1), the number of units",
					"«order» = (p - 1) * p ^ (j + 1)",
					ByArith(
						prime,
						multiple,
						dividesSize,
						notSmaller,
						DivisorPinnedByPrimePower.At(p, b.TermAs[Nat]("p - 1"), j, e),
						nat_prime.PrimeAtLeastTwo.At(p)))
				b.Show(
					"an element whose order is the group's size generates it",
					ByArith(
						finite,
						unit,
						size,
						full,
						grp,
						cyclic_group.ElementOfFullOrderGenerates.At(b.TermAs[group.GroupOps[Nat]]("«units»"), x)))
			})
	}),
})}
