// prime_order.go — roots of unity of prime order: an element x ≠ e with
// xᵖ = e has order p, the sum of ζ^(a·k) over a below p for a p-th root of
// unity ζ ≠ 1 is p or zero, and an algebraically closed field of
// characteristic q, which exists for every prime q, holds such a ζ for every
// prime p ≠ q.

package roots_of_unity

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/lefschetz"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PowIdentityIffPrimeDivides — in a commutative monoid, an element x ≠ e
// with xᵖ = e for a prime p has order p: xᵏ = e exactly when p divides k.
// A multiple of p gives (xᵖ)ᵐ = e. Conversely, were p not to divide k,
// Fermat's little theorem makes k^(p−1) one more than a multiple q·p of p,
// so x^(k^(p−1)) is (xᵖ)^q·x = x; it is also a power of xᵏ = e, so x = e.
var PowIdentityIffPrimeDivides = powIdentityIffPrimeDividesThm{family.Add(registry.ProofEntry{
	Name: "PowIdentityIffPrimeDivides",
	Key:  "prop_3a7a20c8b54db26a",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀x:A. ∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"x ∈ c",
			"x ≠ e",
			"x ^ p = e",
		},
		Conclusion: "x ^ k = e ⇔ p ∣ k",
	},
		func(
			arg *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			x *Expr[A],
			p, k *Expr[Nat],
			prime, xIn, nontrivial, order Fact,
		) {
			xm := arg.MemberOf[on.C](x, xIn)
			arg.Iff()
			arg.Forward(
				"an exponent k with xᵏ = e is a multiple of p",
				func(b *Argument, power Fact) {
					notDivides := b.SupposeNot()
					bounds := b.Have(
						"p is at least two",
						"p ≠ 0 ∧ 1 < p ∧ 0 < p - 1",
						ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p)))
					fermatExponent := b.TermAs[Nat]("k ^ (p - 1)")
					one := b.TermAs[Nat]("1")
					q, fermat := b.ObtainAs[Nat](
						"by Fermat, k^(p − 1) is one more than a multiple of p",
						"∃q:num. k ^ (p - 1) = q * p + 1",
						By(
							prime,
							notDivides,
							bounds,
							nat_prime.FermatLittleCoprime.At(p, k),
							nat_congruence.CongDef.At(fermatExponent, one, p),
							nat_div_mod.ModLessThan.At(one, p),
							nat_div_mod.Division.At(fermatExponent, p)))
					vanishes := b.Have(
						"k^(p − 1) is a multiple of k, so x^(k^(p − 1)) is a power of xᵏ = e",
						"x ^ (k ^ (p - 1)) = e",
						By(
							power,
							bounds,
							nat_monus.MulPowSubOne.At(k, b.TermAs[Nat]("p - 1")),
							comm_monoid.PowPowOn.Read(monoid).At(xm, k, b.TermAs[Nat]("k ^ (p - 1 - 1)")),
							comm_monoid.IdentityPowOn.Read(monoid)))
					fixed := b.Have(
						"and x^(q·p + 1) is (xᵖ)^q · x = x",
						"x ^ (k ^ (p - 1)) = x",
						By(
							order,
							fermat,
							comm_monoid.PowAddOn.Read(monoid).At(xm, b.TermAs[Nat]("q * p"), one),
							comm_monoid.PowPowOn.Read(monoid).At(xm, p, q),
							nat_arith.MulSym.At(q, p),
							comm_monoid.IdentityPowOn.Read(monoid).At(q),
							comm_monoid.PowOneOn.Read(monoid).At(xm),
							comm_monoid.LeftIdentityOn.Read(monoid).At(xm)))
					b.Show(
						"so x = e, which it is not",
						By(Normalized, nontrivial, vanishes, fixed))
				})
			arg.Backward(
				"a multiple p·m of p gives xᵏ = (xᵖ)ᵐ = e",
				func(b *Argument, divides Fact) {
					m, multiple := b.ObtainAs[Nat](
						"k is a multiple of p",
						"∃m:num. k = p * m",
						By(divides, nat_divides.DividesFactor.At(p, k)))
					b.Show(
						"xᵏ = (xᵖ)ᵐ = eᵐ = e",
						By(
							Normalized,
							multiple,
							order,
							comm_monoid.PowPowOn.Read(monoid).At(xm, p, m),
							comm_monoid.IdentityPowOn.Read(monoid)))
				})
		}),
})}

// RootOfUnityPowerSum — for a p-th root of unity ζ ≠ 1 in a field, p prime,
// the sum of ζ^(a·k) over a below p is p when p divides k and zero
// otherwise. The terms are the powers of w = ζᵏ. When p divides k, w is one
// and the sum counts p ones. Otherwise w is not one, ζ having order p, and
// the geometric sum (w − 1)·Σ wᵃ = wᵖ − 1 vanishes, wᵖ being (ζᵖ)ᵏ = 1; the
// nonzero factor w − 1 cancels.
var RootOfUnityPowerSum = rootOfUnityPowerSumThm{family.Add(registry.ProofEntry{
	Name: "RootOfUnityPowerSum",
	Key:  "prop_b696233726995bdd",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀ζ:A. ∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"ζ ∈ F.carrier",
			"ζ ≠ F.one",
			"monoid_pow(F.mul, F.one, ζ, p) = F.one",
		},
		Conclusion: "module_sum(F.add, " +
			"    F.zero, " +
			"    {a:num | a < p}, " +
			"    λa:num. monoid_pow(F.mul, F.one, ζ, a * k)) = " +
			"COND(p ∣ k, monoid_pow(F.add, F.zero, F.one, p), F.zero)",
		Abbrev: Abbrev{
			{Name: "powerSum", Text: "λz:A. " +
				"    module_sum(F.add, F.zero, {a:num | a < p}, λa:num. monoid_pow(F.mul, F.one, z, a))"},
		},
	}, func(
		arg *Argument,
		F field.FieldFact[on.F],
		ζ *Expr[A],
		p, k *Expr[Nat],
		prime, ζIn, nontrivial, root Fact,
	) {
		ring := field.RingOn.Read(F)
		powers := comm_ring.MulMonoidOn.Read(ring)
		ζm := arg.MemberOf[on.F](ζ, ζIn)
		oneM := arg.MemberOf[on.F](arg.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		w, wDef := arg.LetAs[A]("w", "monoid_pow(F.mul, F.one, ζ, k)")
		order := PowIdentityIffPrimeDivides.Read(powers).At(ζm, p, k)
		terms := arg.Have(
			"the a-th term is wᵃ, ζ^(a·k) being (ζᵏ)ᵃ",
			"module_sum(F.add, F.zero, {a:num | a < p}, λa:num. monoid_pow(F.mul, F.one, ζ, a * k)) = "+
				"«powerSum»(w)",
			By(module.ModuleSumCongruence, wDef, ζm, comm_monoid.PowPowOn.Read(powers), nat_arith.MulSym))
		arg.Do(terms.Rw())
		arg.Cases(arg.Term("p ∣ k"))
		arg.When(
			"p divides k: w is one, and the sum counts p ones",
			func(b *Argument, divides Fact) {
				one := b.Have(
					"w is one, p dividing k",
					"w = F.one",
					By(Normalized, order, prime, nontrivial, root, divides, wDef))
				b.Show(
					"p ones sum to p · 1",
					one.Rw(),
					Simp(Fwd(comm_monoid.IdentityPowOn.Read(powers))),
					By(
						module.ModuleSumConstantMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(
							b.TermAs[Set[Nat]]("{a:num | a < p}"),
							oneM),
						num_segment.FiniteBelowStrict.At(p),
						num_segment.HasSizeBelowStrict.At(p),
						cardinality.HasSizeDef))
			})
		arg.Otherwise(
			"p does not divide k: w is not one, and w − 1 cancels from (w − 1)·Σ wᵃ = 0",
			func(b *Argument, notDivides Fact) {
				nontrivialW := b.Have(
					"w is not one, p not dividing k",
					"w ≠ F.one",
					By(Normalized, order, prime, nontrivial, root, notDivides, wDef))
				wm := b.MemberOf[on.F](w, b.Have(
					"w lies in the field",
					"w ∈ F.carrier",
					By(Normalized, wDef, comm_monoid.PowIn.Read(powers).At(ζm, k))))
				sum := b.MemberOf[on.F](b.TermAs[A]("«powerSum»(w)"), b.Have(
					"so does the sum of its powers",
					"«powerSum»(w) ∈ F.carrier",
					By(
						module.ModuleSumIn.Read(module.RegularModuleOn.Read(ring)).At(
							b.TermAs[Set[Nat]]("{a:num | a < p}"),
							b.TermAs[Fun[Nat, A]]("λa:num. monoid_pow(F.mul, F.one, w, a)")),
						num_segment.FiniteBelowStrict,
						comm_monoid.PowIn.Read(powers),
						wm)))
				telescoped := b.Have(
					"the geometric sum telescopes",
					"(w - F.one) * «powerSum»(w) = monoid_pow(F.mul, F.one, w, p) - F.one",
					By(module.GeometricSum.Read(ring).At(wm, p)))
				periodic := b.Have(
					"wᵖ = (ζᵏ)ᵖ = (ζᵖ)ᵏ = 1",
					"monoid_pow(F.mul, F.one, w, p) = F.one",
					By(
						wDef,
						root,
						comm_monoid.PowPowOn.Read(powers).At(ζm, k, p),
						comm_monoid.PowPowOn.Read(powers).At(ζm, p, k),
						nat_arith.MulSym.At(k, p),
						comm_monoid.IdentityPowOn.Read(powers).At(k)))
				vanishes := b.Have(
					"so (w − 1)·Σ wᵃ is zero",
					"(w - F.one) * «powerSum»(w) = F.zero",
					ByArith(F, telescoped, periodic, wm, sum))
				nonzero := b.Have(
					"and w − 1 is not zero",
					"w - F.one ≠ F.zero",
					ByArith(F, nontrivialW, wm))
				b.Show(
					"a product in a field vanishes only with a factor, so the sum is zero",
					By(
						field.MulEqZeroOn.Read(F).At(
							comm_ring.SubIn.Read(ring).At(wm, oneM),
							sum),
						vanishes,
						nonzero,
						notDivides))
			})
	}),
})}

// RootOfUnityInClosedField — an algebraically closed field of prime
// characteristic q holds, for every prime p ≠ q, a p-th root of unity other
// than one. It is a root ζ of Φ = 1 + X + … + X^(p−1), which is not
// constant since p ≥ 2. Since (1 − X)·Φ = 1 − X^p, ζ^p = 1. And ζ ≠ 1, since
// Φ(1) = p·1, which is not zero: one has additive order q
// (PowIdentityIffPrimeDivides), and q does not divide the prime
// p ≠ q.
var RootOfUnityInClosedField = rootOfUnityInClosedFieldThm{family.Add(registry.ProofEntry{
	Name: "RootOfUnityInClosedField",
	Key:  "prop_6696d3336c7dc90e",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀p q:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"ring_prime_characteristic(field_ring(M), q)",
			"nat_prime(p)",
			"p ≠ q",
		},
		Conclusion: "∃ζ:A. ζ ∈ M.carrier ∧ ζ ≠ M.one ∧ monoid_pow(M.mul, M.one, ζ, p) = M.one",
		Abbrev: Abbrev{
			{Name: "Φ", Text: "λn:num. COND(n < p, M.one, M.zero)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		p, q *Expr[Nat],
		closed, characteristic, prime, distinct Fact,
	) {
		ring := field.RingOn.Read(M)
		cyclotomic := arg.TermAs[Fun[Nat, A]]("«Φ»")
		bounds := arg.Have(
			"p is at least two",
			"0 < p ∧ 1 < p",
			ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p)))
		parts := arg.Conjuncts(
			GroupPremises(bounds, polynomial_evaluation.GeometricFactorization.Read(ring).At(p)),
			"1 − X is a polynomial over the field",
			"so is Φ",
			"(1 − X)·Φ is 1 − X^p",
			"Φ takes at one the value p·1")
		linearOver, cyclotomicOver, product, atOne := parts[0], parts[1], parts[2], parts[3]
		nonconstant := arg.Have(
			"Φ is not constant: its coefficient at X is one",
			"0 < polynomial_degree(«Φ»)",
			By(
				cyclotomicOver,
				bounds,
				field.OneNotZeroOn.Read(M),
				polynomial.DegreeZeroIff.At(arg.TermAs[A]("M.zero"), arg.TermAs[Set[A]]("M.carrier"), cyclotomic),
				vec_space.VecDef.At(arg.TermAs[A]("M.zero"), arg.VecAt[A](arg.TermAs[Nat]("1"), "«Φ»")),
				nat_order.LessEqRefl.At(arg.TermAs[Nat]("1")),
				nat_order.PosIffNonzero.At(arg.TermAs[Nat]("polynomial_degree(«Φ»)"))))
		ζ, root := arg.ObtainAs[A](
			"the closed field holds a root ζ of Φ",
			"∃ζ:A. ζ ∈ M.carrier ∧ polynomial_eval(«Φ», ζ) = M.zero",
			By(closed, nonconstant, cyclotomicOver, algebraic_closure.AlgebraicallyClosedDef))
		rootParts := arg.Conjuncts(
			root,
			"ζ lies in the field",
			"Φ vanishes at ζ")
		ζm, vanishesAtRoot := arg.MemberOf[on.M](ζ, rootParts[0]), rootParts[1]
		linear := arg.TermAs[Fun[Nat, A]]("basis_vector(0) - basis_vector(1)")
		binomialVanishes := arg.Have(
			"so 1 − X^p, the multiple (1 − X)·Φ, vanishes at ζ",
			"polynomial_eval(basis_vector(0) - basis_vector(p), ζ) = M.zero",
			By(
				polynomial_evaluation.EvalMulRoot.Read(ring).At(cyclotomic, linear, ζm),
				linearOver,
				cyclotomicOver,
				vanishesAtRoot,
				product))
		periodic := arg.Have(
			"that is, ζ^p = 1",
			"monoid_pow(M.mul, M.one, ζ, p) = M.one",
			ByArith(
				M,
				binomialVanishes,
				ζm,
				polynomial_evaluation.EvalSub.Read(ring).At(
					arg.TermAs[Fun[Nat, A]]("basis_vector(0)"),
					arg.TermAs[Fun[Nat, A]]("basis_vector(p)"),
					ζm),
				polynomial.BasisVectorOver.Read(ring),
				polynomial_evaluation.EvalBasisVector.Read(ring).At(arg.TermAs[Nat]("0"), ζm),
				polynomial_evaluation.EvalBasisVector.Read(ring).At(p, ζm)))
		oneM := arg.MemberOf[on.M](arg.TermAs[A]("M.one"), comm_ring.OneIn.Read(ring))
		numeral := arg.Have(
			"p·1 is not zero: one has additive order q, and q does not divide the prime p ≠ q",
			"monoid_pow(M.add, M.zero, M.one, p) ≠ M.zero",
			By(
				characteristic,
				prime,
				distinct,
				finite_field.PrimeCharacteristicDef,
				PowIdentityIffPrimeDivides.Read(comm_ring.AddMonoidOn.Read(ring)).At(oneM, q, p),
				field.OneNotZeroOn.Read(M),
				nat_prime.PrimeDividesPrime.At(q, p)))
		nontrivial := arg.Have(
			"so ζ is not one: Φ vanishes at ζ but takes p·1 at one",
			"ζ ≠ M.one",
			By(vanishesAtRoot, atOne, numeral))
		arg.Take(ζ)
		arg.Show(
			"ζ is a p-th root of unity other than one",
			By(ζm, nontrivial, periodic))
	}),
})}

// ClosedFieldOfCharacteristic — for every prime q there is an
// algebraically closed field of characteristic q, the place where
// RootOfUnityInClosedField finds its roots: the locally finite closure of
// characteristic q (lefschetz.PrimeClosureLocallyFinite), an algebraically
// closed field on its carrier. Its characteristic is stated both ways a
// citer reads it: as the field's characteristic, and, q being a prime and so
// not zero, as the prime characteristic of its ring.
var ClosedFieldOfCharacteristic = closedFieldOfCharacteristicThm{family.Add(registry.ProofEntry{
	Name: "ClosedFieldOfCharacteristic",
	Key:  "prop_77917549c95e26eb",
	Build: family.Theorem(Statement{
		Binders: "∀q:num.",
		Hypotheses: []string{
			"nat_prime(q)",
		},
		Conclusion: "∃M:field_ops(set(prod(num, num → set(int)))). " +
			"    field_on(M) ∧ " +
			"    algebraically_closed_field(M) ∧ " +
			"    field_characteristic(M, q) ∧ " +
			"    ring_prime_characteristic(field_ring(M), q)",
	}, func(arg *Argument, q *Expr[Nat], prime Fact) {
		M, closure := arg.UnpackAs[FieldOps[Set[Prod[Nat, Fun[Nat, Set[Int]]]]]](
			GroupPremises(prime, lefschetz.PrimeClosureLocallyFinite.At(q)),
			"M")
		arg.Take(M)
		arg.Show(
			"an algebraically closed field on its carrier is a field and "+
				"algebraically closed, and its characteristic q is a prime, not zero",
			ByArith(
				closure,
				prime,
				algebraic_closure.AlgebraicallyClosedFieldOnIff.At(M),
				finite_field.FieldCharacteristicDef.At(M, q),
				nat_prime.PrimeAtLeastTwo.At(q)))
	}),
})}
