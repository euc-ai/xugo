// multiplicity.go — the multiplicity of p in n: its characterization by the
// powers of p dividing n, which it counts, its values at a non-divisor of n and
// at p itself, its cofactor, and its sum over a product.

package nat_multiplicity

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/registry"
)

// MultiplicitySpec — for 2 ≤ p and n ≠ 0, p to the multiplicity of p in n
// divides n and the next power of p does not. The exponents e with pᵉ ∣ n
// include 0 and are at most n, since e < pᵉ ≤ n; so there is a largest
// one, the power one past it does not divide n, and the choice that
// defines nat_multiplicity finds an exponent of exactly that kind.
var MultiplicitySpec = multiplicitySpecThm{family.Add(registry.ProofEntry{
	Name: "MultiplicitySpec",
	Key:  "prop_a918b6ff90ae3e1d",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"2 ≤ p",
			"n ≠ 0",
		},
		Conclusion: "p ^ nat_multiplicity(p, n) ∣ n ∧ ¬(p ^ (nat_multiplicity(p, n) + 1) ∣ n)",
	}, func(a *Argument, p, n *Expr[Nat], base, nonzero Fact) {
		bounded := a.Have(
			"the exponents whose powers divide n are bounded, by n itself",
			"∃M:num. ∀e:num. p ^ e ∣ n ⇒ e ≤ M",
			Derive(func(b *Argument) {
				b.Take(n)
				e := b.FixAs[Nat]("e")
				pe := b.TermAs[Nat]("p ^ e")
				divides := b.Assume()
				b.Show(
					"e < pᵉ, and pᵉ ≤ n as a divisor of n ≠ 0",
					By(
						base,
						nonzero,
						divides,
						nat_divides.DividesLessEq.At(pe, n),
						nat_order.LessThanPowSelf.At(p, e),
						nat_order.LessThanLessEqTrans.At(e, pe, n),
						nat_order.LessEqOfLessThan.At(e, n)))
			}))
		some := a.Have(
			"the exponent 0 is one of them",
			"∃e:num. p ^ e ∣ n",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Nat]("0"))
				b.Show(
					"p⁰ = 1 divides n",
					By(Normalized, nat_arith.NatPow, nat_divides.OneDivides.At(n)))
			}))
		largest := a.Have(
			"non-empty and bounded, these exponents have a largest",
			"∃e:num. p ^ e ∣ n ∧ (∀k:num. p ^ k ∣ n ⇒ k ≤ e)",
			By(some, bounded, nat_order.MaximumExists.At(a.TermAs[Set[Nat]]("λe:num. p ^ e ∣ n"))))
		// The Unfold below reads this existence, left resident: nat_multiplicity(p, n)
		// opens to the choice of such an e, and some e qualifying makes the chosen one qualify.
		a.Have(
			"past the largest exponent the power no longer divides n, since e + 1 ≤ e fails",
			"∃e:num. p ^ e ∣ n ∧ ¬(p ^ (e + 1) ∣ n)",
			By(largest, nat_arith.Add1, nat_order.SucLessEqIffLessThan, nat_order.LessThanIrrefl))
		a.Show(
			"nat_multiplicity chooses an exponent of that kind",
			Unfold(NatMultiplicityDef))
	}),
})}

// DividesIff — for 2 ≤ p and n ≠ 0, pᵉ divides n exactly when e is at
// most the multiplicity v of p in n. Below v, pᵉ divides pᵛ, which
// divides n; past v, pᵛ⁺¹ would divide pᵉ and so n, which
// MultiplicitySpec denies.
var DividesIff = dividesIffThm{family.Add(registry.ProofEntry{
	Name: "DividesIff",
	Key:  "prop_27455538f1dd9d8c",
	Build: family.Theorem(Statement{
		Binders: "∀p n e:num.",
		Hypotheses: []string{
			"2 ≤ p",
			"n ≠ 0",
		},
		Conclusion: "p ^ e ∣ n ⇔ e ≤ nat_multiplicity(p, n)",
	}, func(a *Argument, p, n, e *Expr[Nat], base, nonzero Fact) {
		v := a.TermAs[Nat]("nat_multiplicity(p, n)")
		next := a.TermAs[Nat]("nat_multiplicity(p, n) + 1")
		spec := a.Conjuncts(
			GroupPremises(base, nonzero, MultiplicitySpec.At(p, n)),
			"pᵛ divides n",
			"pᵛ⁺¹ does not")
		atV, pastV := spec[0], spec[1]
		a.Iff()
		a.Forward(
			"past the multiplicity, the next power would divide pᵉ and so n",
			func(b *Argument, divides Fact) {
				b.Show(
					"e ≤ v, as v < e would give v + 1 ≤ e",
					By(
						pastV,
						divides,
						nat_divides.PowDividesPow.At(p, next, e),
						nat_divides.DividesTrans,
						nat_order.NotLessEq.At(e, v),
						nat_order.SucLessEqIffLessThan.At(v, e),
						nat_arith.Add1.At(v)))
			})
		a.Backward(
			"pᵉ divides pᵛ, which divides n",
			func(b *Argument, le Fact) {
				b.Show(
					"pᵉ ∣ n by transitivity",
					By(le, atV, nat_divides.PowDividesPow.At(p, e, v), nat_divides.DividesTrans))
			})
	}),
})}

// MultiplicityAsCount — for 2 ≤ p and n ≠ 0, the multiplicity v of p in n
// counts the exponents i in 1 .. n with pⁱ ∣ n. By DividesIff those are the
// i ≤ v, so up to a bound M the indicators count min(M, v), by induction on
// M; and v ≤ n, since v < pᵛ ≤ n.
var MultiplicityAsCount = multiplicityAsCountThm{family.Add(registry.ProofEntry{
	Name: "MultiplicityAsCount",
	Key:  "prop_3d36e26fb984b4fb",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"2 ≤ p",
			"n ≠ 0",
		},
		Conclusion: "nat_multiplicity(p, n) = Σ_{i∈1 .. n} COND(p ^ i ∣ n, 1, 0)",
	}, func(a *Argument, p, n *Expr[Nat], base, nonzero Fact) {
		v := a.TermAs[Nat]("nat_multiplicity(p, n)")
		one, zero := a.TermAs[Nat]("1"), a.TermAs[Nat]("0")
		indicator := a.TermAs[Fun[Nat, Nat]]("λi:num. COND(p ^ i ∣ n, 1, 0)")
		upTo := a.Have(
			"up to a bound M the indicators count min(M, v)",
			"∀M:num. Σ_{i∈1 .. M} COND(p ^ i ∣ n, 1, 0) = min(M, nat_multiplicity(p, n))",
			Derive(func(b *Argument) {
				m := ext.As[Nat](b.Binder("M"))
				b.Induct(m)
				b.Base(
					"the sum over 1 .. 0 is empty, and min(0, v) = 0",
					ByArith(nat_sum.IntervalClauses.At(one, zero, indicator), nat_order.NatMinDef.At(zero, v)))
				b.Step(
					"the indicator at M + 1 is 1 exactly when M + 1 ≤ v",
					func(c *Argument, ih Fact) {
						sm := c.TermAs[Nat]("suc(M)")
						// The split decides the COND of the indicator at M + 1; the two closes
						// read the same facts beside the case each one is given.
						c.Cases(c.Term("p ^ suc(M) ∣ n"))
						c.When(
							"pᴹ⁺¹ divides n, so M + 1 ≤ v and the count grows by one",
							func(e *Argument, divides Fact) {
								e.Show(
									"the count at M + 1 is min(M + 1, v)",
									ByArith(
										base,
										nonzero,
										ih,
										divides,
										nat_sum.IntervalClauses.At(one, m, indicator),
										DividesIff.At(p, n, sm),
										nat_order.NatMinDef.At(sm, v),
										nat_order.NatMinDef.At(m, v)))
							})
						c.Otherwise(
							"pᴹ⁺¹ does not divide n, so v ≤ M and the count stays v",
							func(e *Argument, fails Fact) {
								e.Show(
									"the count at M + 1 is min(M + 1, v)",
									ByArith(
										base,
										nonzero,
										ih,
										fails,
										nat_sum.IntervalClauses.At(one, m, indicator),
										DividesIff.At(p, n, sm),
										nat_order.NatMinDef.At(sm, v),
										nat_order.NatMinDef.At(m, v)))
							})
					})
			}))
		a.Show(
			"at M = n the count is v itself, as v < pᵛ ≤ n",
			ByArith(
				base,
				nonzero,
				upTo.At(n),
				MultiplicitySpec.At(p, n),
				nat_divides.DividesLessEq.At(a.TermAs[Nat]("p ^ nat_multiplicity(p, n)"), n),
				nat_order.LessThanPowSelf.At(p, v),
				nat_order.NatMinDef.At(n, v)))
	}),
})}

// MultiplicityUnique — the multiplicity is the one exponent of its kind:
// for 2 ≤ p and n ≠ 0, an e with pᵉ ∣ n and pᵉ⁺¹ ∤ n is the multiplicity
// v of p in n. DividesIff reads pᵉ ∣ n as e ≤ v and pᵉ⁺¹ ∤ n as v < e + 1.
var MultiplicityUnique = multiplicityUniqueThm{family.Add(registry.ProofEntry{
	Name: "MultiplicityUnique",
	Key:  "prop_2092b73357e0e588",
	Build: family.Theorem(Statement{
		Binders: "∀p n e:num.",
		Hypotheses: []string{
			"2 ≤ p",
			"n ≠ 0",
			"p ^ e ∣ n",
			"¬(p ^ (e + 1) ∣ n)",
		},
		Conclusion: "nat_multiplicity(p, n) = e",
	}, func(a *Argument, p, n, e *Expr[Nat], base, nonzero, divides, notNext Fact) {
		v := a.TermAs[Nat]("nat_multiplicity(p, n)")
		next := a.TermAs[Nat]("e + 1")
		atLeast := a.Have(
			"e ≤ v, as pᵉ divides n",
			"e ≤ nat_multiplicity(p, n)",
			By(base, nonzero, divides, DividesIff.At(p, n, e)))
		atMost := a.Have(
			"v ≤ e, as pᵉ⁺¹ does not divide n",
			"nat_multiplicity(p, n) ≤ e",
			By(
				base,
				nonzero,
				notNext,
				DividesIff.At(p, n, next),
				nat_order.NotLessEq.At(next, v),
				nat_order.LessThanSucIffLessEq.At(v, e),
				nat_arith.Add1.At(e)))
		a.Show(
			"v = e by antisymmetry",
			By(atLeast, atMost, nat_order.LessEqAntisym.At(v, e)))
	}),
})}

// MultiplicityOfNonDivisor — a number that does not divide n occurs in n to
// the power 0. The exponent 0 has the property the multiplicity is chosen
// by — p⁰ = 1 divides n and p⁰⁺¹ = p does not — so the chosen exponent has
// it too; and a positive one would make p, a divisor of that power of p, a
// divisor of n.
var MultiplicityOfNonDivisor = multiplicityOfNonDivisorThm{family.Add(registry.ProofEntry{
	Name: "MultiplicityOfNonDivisor",
	Key:  "prop_5d372f5e11533518",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"¬(p ∣ n)",
		},
		Conclusion: "nat_multiplicity(p, n) = 0",
	}, func(a *Argument, p, n *Expr[Nat], notDivides Fact) {
		zero := a.Have(
			"0 is such an exponent: p⁰ = 1 divides n, and p⁰⁺¹ = p does not",
			"p ^ 0 ∣ n ∧ ¬(p ^ (0 + 1) ∣ n)",
			By(
				Normalized,
				notDivides,
				nat_divides.OneDivides.At(n),
				nat_arith.PowOne.At(p),
				nat_arith.NatPow,
				nat_arith.AddLeftZeroClause.At(a.Ctx().Nat(1))))
		chosen := a.Have(
			"so the exponent the multiplicity chooses is one too",
			"p ^ nat_multiplicity(p, n) ∣ n ∧ ¬(p ^ (nat_multiplicity(p, n) + 1) ∣ n)",
			Simp(Fwd(NatMultiplicityDef)),
			By(zero))
		v := a.TermAs[Nat]("nat_multiplicity(p, n)")
		a.Show(
			"a positive exponent would make p, which divides p to it, divide n",
			By(
				Normalized,
				notDivides,
				chosen,
				nat_divides.PowDividesPow.At(p, a.Ctx().Nat(1), v),
				nat_arith.PowOne.At(p),
				nat_divides.DividesTrans.At(p, a.TermAs[Nat]("p ^ nat_multiplicity(p, n)"), n),
				nat_order.OneLessEqIffNonzero.At(v)))
	}),
})}

// MultiplicitySelf — a number p at least 2 occurs in itself exactly once:
// p¹ = p divides p, and p¹⁺¹ = p·p, exceeding p, does not.
var MultiplicitySelf = multiplicitySelfThm{family.Add(registry.ProofEntry{
	Name: "MultiplicitySelf",
	Key:  "prop_d424b30ceb6a1567",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"2 ≤ p",
		},
		Conclusion: "nat_multiplicity(p, p) = 1",
	}, func(a *Argument, p *Expr[Nat], atLeastTwo Fact) {
		square := a.Have(
			"p¹⁺¹ = p·p is at least 2·p, so it exceeds p, which is not 0",
			"¬(p ^ (1 + 1) ≤ p) ∧ p ≠ 0",
			ByArith(atLeastTwo, nat_order.LessEqMulMono.At(p, a.Ctx().Nat(2), p)))
		a.Show(
			"p¹ divides p and p¹⁺¹ does not, a divisor of a nonzero number being no larger than it",
			By(
				atLeastTwo,
				square,
				MultiplicityUnique.At(p, p, a.Ctx().Nat(1)),
				nat_divides.DividesLessEq.At(a.TermAs[Nat]("p ^ (1 + 1)"), p),
				nat_arith.PowOne.At(p),
				nat_divides.DividesRefl.At(p)))
	}),
})}

// MultiplicityCofactor — for 2 ≤ p and n ≠ 0, n is p to its multiplicity v
// times a cofactor that p does not divide: pᵛ divides n, and a cofactor
// p · d would make pᵛ⁺¹ = pᵛ · p divide n.
var MultiplicityCofactor = multiplicityCofactorThm{family.Add(registry.ProofEntry{
	Name: "MultiplicityCofactor",
	Key:  "prop_ecb9a0e0468cefd3",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"2 ≤ p",
			"n ≠ 0",
		},
		Conclusion: "∃c:num. n = p ^ nat_multiplicity(p, n) * c ∧ ¬(p ∣ c)",
	}, func(a *Argument, p, n *Expr[Nat], base, nonzero Fact) {
		v := a.TermAs[Nat]("nat_multiplicity(p, n)")
		spec := a.Conjuncts(
			GroupPremises(base, nonzero, MultiplicitySpec.At(p, n)),
			"pᵛ divides n",
			"pᵛ⁺¹ does not")
		atV, pastV := spec[0], spec[1]
		c, split := a.ObtainAs[Nat](
			"pᵛ divides n, so n = pᵛ · c",
			"∃c:num. n = p ^ nat_multiplicity(p, n) * c",
			By(atV, nat_divides.DividesFactor.At(a.TermAs[Nat]("p ^ nat_multiplicity(p, n)"), n)))
		a.Take(c)
		a.Show(
			"and p ∤ c, since c = p · d would give n = pᵛ⁺¹ · d",
			By(
				pastV,
				split,
				nat_divides.DividesFactor,
				nat_arith.PowAdd.At(p, v, a.TermAs[Nat]("1")),
				nat_arith.PowOne.At(p),
				nat_arith.MulAssoc))
	}),
})}

// MultiplicityMul — the multiplicity of a prime p adds over a product of
// nonzero numbers. With a and b the multiplicities of p in m and n, write
// m = pᵃ · r and n = pᵇ · s with p ∤ r and p ∤ s (MultiplicityCofactor),
// and let k = a + b. Then m · n = pᵏ · (r · s), and
// p ∤ r · s by Euclid's lemma; so pᵏ divides m · n while pᵏ⁺¹ does not,
// since cancelling pᵏ from pᵏ · p ∣ pᵏ · (r · s) would leave p ∣ r · s.
// MultiplicityUnique names k the multiplicity.
var MultiplicityMul = multiplicityMulThm{family.Add(registry.ProofEntry{
	Name: "MultiplicityMul",
	Key:  "prop_332bf116aab90ad1",
	Build: family.Theorem(Statement{
		Binders: "∀p m n:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"m ≠ 0",
			"n ≠ 0",
		},
		Conclusion: "nat_multiplicity(p, m * n) = nat_multiplicity(p, m) + nat_multiplicity(p, n)",
	}, func(arg *Argument, p, m, n *Expr[Nat], prime, mNonzero, nNonzero Fact) {
		base := arg.Have(
			"a prime is at least 2",
			"2 ≤ p",
			By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
		r, mSplit := arg.UnpackAs[Nat](GroupPremises(base, mNonzero, MultiplicityCofactor.At(p, m)), "r")
		mParts := arg.Conjuncts(
			mSplit,
			"m is p to its multiplicity times r",
			"p does not divide r")
		s, nSplit := arg.UnpackAs[Nat](GroupPremises(base, nNonzero, MultiplicityCofactor.At(p, n)), "s")
		nParts := arg.Conjuncts(
			nSplit,
			"n is p to its multiplicity times s",
			"p does not divide s")
		a, _ := arg.LetAs[Nat]("a", "nat_multiplicity(p, m)")
		b, _ := arg.LetAs[Nat]("b", "nat_multiplicity(p, n)")
		k, kDef := arg.LetAs[Nat]("k", "a + b")
		pk, rs := arg.TermAs[Nat]("p ^ k"), arg.TermAs[Nat]("r * s")
		factor := arg.Have(
			"m · n regroups as pᵏ · (r · s)",
			"m * n = p ^ k * (r * s)",
			CalcEq(
				Leg(
					arg.TermAs[Nat]("p ^ a * r * (p ^ b * s)"),
					"substitute the two factorizations",
					By(Normalized, mParts[0], nParts[0])),
				Leg(
					arg.TermAs[Nat]("p ^ a * p ^ b * (r * s)"),
					"regroup the factors",
					ACRegroupWith(nat_arith.MulAC(arg.Ctx()))),
				FinalLeg(
					"the two powers of p combine into pᵏ",
					By(Normalized, kDef, nat_arith.PowAdd.At(p, a, b)))))
		notDividesCofactor := arg.Have(
			"p does not divide r · s, by Euclid's lemma",
			"¬(p ∣ r * s)",
			By(prime, mParts[1], nParts[1], nat_prime.EuclidLemma.At(p, r, s)))
		divides := arg.Have(
			"pᵏ divides m · n",
			"p ^ k ∣ m * n",
			By(Normalized, factor, nat_divides.DividesOwnMultiple.At(pk, rs)))
		nonzeroPower := arg.Have(
			"pᵏ ≠ 0, as p ≥ 2",
			"p ^ k ≠ 0",
			ByArith(base, nat_arith.PowEqZero.At(p, k)))
		notNext := arg.Have(
			"pᵏ⁺¹ = pᵏ · p does not divide m · n: cancelling pᵏ would leave p ∣ r · s",
			"¬(p ^ (k + 1) ∣ m * n)",
			By(
				Normalized,
				nonzeroPower,
				notDividesCofactor,
				factor,
				nat_arith.PowAdd.At(p, k, arg.TermAs[Nat]("1")),
				nat_arith.PowOne.At(p),
				nat_divides.MulDividesLCancel.At(pk, p, rs)))
		arg.Show(
			"so k is the multiplicity of p in m · n",
			By(
				base,
				mNonzero,
				nNonzero,
				divides,
				notNext,
				nat_arith.MulEqZero.At(m, n),
				MultiplicityUnique.At(p, arg.TermAs[Nat]("m * n"), k)))
	}),
})}
