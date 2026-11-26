// group.go — the units mod n as an abelian group: the residues below n
// coprime to n, multiplied and reduced mod n.

package units_mod

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// AbelianGroupOn — for n > 0 the residues below n coprime to n form an
// abelian group under multiplication mod n. The proof unfolds
// abelian_group_on and group_on, the record's fields read off units_mod's
// definition, and closes one case per conjunct in the definitions' order.
// A remainder lies below n and is coprime to n exactly when what it reduces
// is (nat_gcd.CoprimeLMod), so the residue of 1 and the reduced product of
// two units are units. The inverse the definition chooses exists by
// nat_congruence.InverseExists; it lies below n, and x times it leaves the
// remainder of 1, so it is coprime to n. Associativity and commutativity
// are those of multiplication, read through the remainders.
var AbelianGroupOn = abelianGroupOnThm{family.Add(registry.ProofEntry{
	Name: "AbelianGroupOn",
	Key:  "prop_2b7012bd6d2e3954",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"0 < n",
		},
		Conclusion: "abelian_group_on(units_mod(n))",
		Abbrev: Abbrev{
			{Name: "inverse", Text: "λx:num. εb:num. b < n ∧ rem(x * b, n) = rem(1, n)"},
		},
	}, func(a *Argument, n *Expr[Nat], positive Fact) {
		one := a.Ctx().Nat(1)
		below := a.Have(
			"every remainder mod n lies below n",
			"∀m:num. rem(m, n) < n",
			a.ForEach(func(m *Expr[Nat]) Action {
				return By(positive, nat_order.PosIffNonzero.At(n), nat_div_mod.Division.At(m, n))
			}))
		inverses := a.Have(
			"every unit has an inverse mod n below n, its congruence read as remainders",
			"∀x:num. x < n ∧ nat_coprime(x, n) ⇒ ∃b:num. b < n ∧ rem(x * b, n) = rem(1, n)",
			By(positive, nat_congruence.InverseExists, nat_congruence.CongDef))
		chosen := a.Have(
			"the inverse the definition chooses for a unit x is "+
				"one: below n, and x times it leaves the remainder of 1",
			"∀x:num. x < n ∧ nat_coprime(x, n) ⇒ «inverse»(x) < n ∧ rem(x * «inverse»(x), n) = rem(1, n)",
			Derive(func(c *Argument) {
				x := c.FixAs[Nat]("x")
				unit := c.Assume()
				c.Show(
					"x has an inverse mod n below n, so the one the definition chooses is one",
					By(HilbertDenoted, inverses.At(x), unit))
			}))
		a.Do(Unfold(abelian_group.AbelianGroupOn), Unfold(group.GroupOn), SplitConjAll(
			Case(
				"the residue of 1 is a unit",
				By(below.At(one), nat_gcd.CoprimeLMod.At(one, n), nat_gcd.OneCoprime.At(n))),
			Case(
				"the reduced product of two units is a unit",
				By(below, nat_gcd.CoprimeLMod, nat_gcd.CoprimeMul)),
			Case(
				"the inverse the definition chooses is a unit",
				Derive(func(c *Argument) {
					x := c.FixAs[Nat]("x")
					unit := c.Assume()
					inverse := c.Conjuncts(
						GroupPremises(unit, chosen.At(x)),
						"the chosen inverse lies below n",
						"x times it leaves the remainder of 1")
					y, _ := c.LetAs[Nat]("y", "«inverse»(x)")
					c.Show(
						"y lies below n, and x·y leaves the remainder of 1, which is coprime to n — so y is coprime to n",
						By(
							Normalized,
							unit,
							inverse[0],
							inverse[1],
							nat_gcd.CoprimeLMod.At(c.TermAs[Nat]("x * y"), n),
							nat_gcd.CoprimeLMod.At(one, n),
							nat_gcd.OneCoprime.At(n),
							nat_gcd.CoprimeMul.At(x, y, n)))
				})),
			Case(
				"multiplication mod n associates",
				By(nat_div_mod.ModMulAssoc)),
			Case(
				"the residue of 1 is a left identity",
				Derive(func(c *Argument) {
					x := c.FixAs[Nat]("x")
					unit := c.Assume()
					c.Show(
						"reducing 1 first changes no remainder, and x is its own remainder",
						By(
							unit,
							nat_div_mod.ModMulModLeft.At(one, x, n),
							nat_arith.OneMul.At(x),
							nat_div_mod.ModLessThan.At(x, n)))
				})),
			Case(
				"the inverse the definition chooses is a left inverse",
				Derive(func(c *Argument) {
					x := c.FixAs[Nat]("x")
					unit := c.Assume()
					c.Show(
						"x times it leaves the remainder of 1, and multiplication commutes",
						By(unit, chosen.At(x), nat_arith.MulSym))
				})),
			Case(
				"multiplication mod n commutes",
				By(nat_arith.MulSym)),
		))
	}),
})}

// MulEqOne — in the units mod n, a product is the identity exactly when
// the two factors are inverse mod n: the group's product is the residue
// of a·b and its identity the residue of 1, so the equation is the
// congruence.
var MulEqOne = mulEqOneThm{family.Add(registry.ProofEntry{
	Name: "MulEqOne",
	Key:  "prop_ff2764f4c455f1fb",
	Build: family.Theorem("∀n a b:num. units_mod(n).mul(a, b) = units_mod(n).one ⇔ a * b ≡ 1 (mod n)",
		func(arg *Argument, n, a, b *Expr[Nat]) {
			arg.Show(
				"both sides say that a·b and 1 leave one remainder mod n",
				By(UnitsModDef, group.GroupMulDef, group.GroupOneDef, nat_congruence.CongDef))
		}),
})}

// ResidueIn — the residue mod n of a number coprime to n is a unit: it
// lies below n, and it is coprime to n as the number is
// (nat_gcd.CoprimeLMod).
var ResidueIn = residueInThm{family.Add(registry.ProofEntry{
	Name: "ResidueIn",
	Key:  "prop_b4167da0b7348abf",
	Build: family.Theorem(Statement{
		Binders: "∀n a:num.",
		Hypotheses: []string{
			"0 < n",
			"nat_coprime(a, n)",
		},
		Conclusion: "rem(a, n) ∈ units_mod(n).carrier",
	}, func(arg *Argument, n, a *Expr[Nat], positive, coprime Fact) {
		bounded := arg.Have(
			"division bounds the residue by the modulus",
			"rem(a, n) < n",
			By(positive, nat_order.PosIffNonzero.At(n), nat_div_mod.Division.At(a, n)))
		coprimeResidue := arg.Have(
			"the residue remains coprime to the modulus",
			"nat_coprime(rem(a, n), n)",
			By(coprime, nat_gcd.CoprimeLMod.At(a, n)))
		arg.Show(
			"a coprime residue below n is a unit",
			BySets(bounded, coprimeResidue))
	}),
})}

// UnitsModPrime — mod a prime p every nonzero residue is a unit: the
// residues below p coprime to p are 1, …, p − 1. 0 is coprime to p only if
// p = 1, and p divides no number strictly between 0 and p, which for a
// prime means coprime to it (nat_prime.PrimeCoprimeIffNotDivides).
var UnitsModPrime = unitsModPrimeThm{family.Add(registry.ProofEntry{
	Name: "UnitsModPrime",
	Key:  "prop_8386a32a76323bd8",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "units_mod(p).carrier = 1 .. p - 1",
	}, func(a *Argument, p *Expr[Nat], prime Fact) {
		pointwise := a.Have(
			"a residue below p is coprime to p exactly when it is not 0",
			"∀x:num. x < p ∧ nat_coprime(x, p) ⇔ 1 ≤ x ∧ x ≤ p - 1",
			Derive(func(b *Argument) {
				x := b.FixAs[Nat]("x")
				b.Iff()
				b.Forward(
					"0 is coprime to p only if p = 1, which a prime is not",
					func(c *Argument, unit Fact) {
						nonzero := c.Have(
							"x is not 0: p divides both 0 and p",
							"x ≠ 0",
							By(
								prime,
								unit,
								nat_gcd.Coprime.At(x, p),
								nat_divides.DividesZero.At(p),
								nat_divides.DividesRefl.At(p),
								nat_prime.PrimeDef.At(p)))
						c.Show(
							"so x lies in 1 .. p − 1",
							ByArith(nonzero, unit))
					})
				b.Backward(
					"p divides no number strictly between 0 and p, and a prime is coprime to what it does not divide",
					func(c *Argument, inRange Fact) {
						atLeastTwo := nat_prime.PrimeAtLeastTwo.At(p)
						below := c.Have(
							"x lies below p",
							"x < p",
							ByArith(prime, inRange, atLeastTwo))
						notDivides := c.Have(
							"p does not divide x",
							"¬(p ∣ x)",
							ByArith(prime, inRange, nat_divides.DividesLessEq.At(p, x), atLeastTwo))
						c.Show(
							"so x is coprime to p",
							By(
								Normalized,
								below,
								prime,
								notDivides,
								nat_prime.PrimeCoprimeIffNotDivides.At(p),
								nat_gcd.CoprimeSym.At(x, p)))
					})
			}))
		a.Show(
			"the carrier is the residues below p coprime to p, which are those of 1 .. p − 1",
			Simp(Fwd(UnitsModDef), Fwd(group.GroupCarrierDef), Fwd(num_segment.IntervalDef)),
			BySets(pointwise))
	}),
})}
