// euler.go — Euler's theorem: a number coprime to n, raised to φ(n), is
// 1 mod n, read off the units mod n as a group with φ(n) members.

package units_mod

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// UnitsPowMod — in the units mod n, the k-th power of a is the residue of
// a^k. By induction on k: the zeroth power is the identity, the residue of
// 1 = a⁰; and the next power multiplies the residue of a^k by a and
// reduces, which leaves the remainder of a · a^k = a^(k+1)
// (nat_div_mod.ModMulModRight).
var UnitsPowMod = unitsPowModThm{family.Add(registry.ProofEntry{
	Name: "UnitsPowMod",
	Key:  "prop_afe2761fc4663b8d",
	Build: family.Theorem("∀n a k:num. "+
		"    monoid_pow(units_mod(n).mul, units_mod(n).one, a, k) = rem(a ^ k, n)",
		func(arg *Argument, n, a *Expr[Nat]) {
			arg.Induct("k")
			arg.Base(
				"the zeroth power is the identity, the residue of 1, and a⁰ = 1",
				Simp(
					Fwd(comm_monoid.MonoidPowDef),
					Fwd(UnitsModDef),
					Fwd(group.GroupOneDef),
					Fwd(nat_arith.NatPow)),
				Refl())
			arg.Step(
				"the next power multiplies by a and reduces mod n",
				func(b *Argument, ih Fact) {
					b.Show(
						"a times the residue of a^k, reduced, is the residue of a · a^k = a^(k+1)",
						Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(ih)),
						Simp(Fwd(nat_div_mod.ModMulModRight), Fwd(nat_arith.NatPow)),
						Refl())
				})
		}),
})}

// CarrierHasSize — there are φ(n) units mod n: the carrier is the set of
// residues below n coprime to n, which is the set φ(n) counts.
var CarrierHasSize = carrierHasSizeThm{family.Add(registry.ProofEntry{
	Name: "CarrierHasSize",
	Key:  "prop_d8bc3aeef5265a80",
	Build: family.Theorem("∀n:num. has_size(units_mod(n).carrier, totient(n))",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"the carrier is the set of residues below n coprime to n, which φ(n) counts",
				By(UnitsModDef, group.GroupCarrierDef, totient.TotientHasSize))
		}),
})}

// Euler — Euler's theorem: for n > 0 and a coprime to n, a^φ(n) ≡ 1 (mod n).
// The residue of a mod n lies below n and is coprime to n, so it is a unit.
// The units form an abelian group (AbelianGroupOn) with φ(n) members
// (CarrierHasSize), and a member of a finite group raised to the group's
// size is the identity (cyclic_group.PowCardIsOne). The group's power is
// the ordinary power reduced mod n (UnitsPowMod) and its identity the
// residue of 1, so the residue raised to φ(n) is 1 mod n; and a is
// congruent to its residue, so a^φ(n) is congruent to that power
// (nat_congruence.PowCongruent).
var Euler = eulerThm{family.Add(registry.ProofEntry{
	Name: "Euler",
	Key:  "prop_99e6909a8c2f304a",
	Build: family.Theorem(Statement{
		Binders: "∀n a:num.",
		Hypotheses: []string{
			"0 < n",
			"nat_coprime(a, n)",
		},
		Conclusion: "a ^ totient(n) ≡ 1 (mod n)",
	}, func(arg *Argument, n *Expr[Nat], positive Fact, a *Expr[Nat], coprime Fact) {
		residue, phi := arg.TermAs[Nat]("rem(a, n)"), arg.TermAs[Nat]("totient(n)")
		units := arg.Have(
			"the units mod n form an abelian group",
			"abelian_group_on(units_mod(n))",
			By(positive, AbelianGroupOn.At(n)))
		unitGroup := abelian_group.GroupOn.Read(units)
		unit := arg.Have(
			"the residue of a is a unit",
			"rem(a, n) ∈ units_mod(n).carrier",
			By(positive, coprime, ResidueIn.At(n, a)))
		finite := arg.Have(
			"there are finitely many units, φ(n) of them",
			"finite(units_mod(n).carrier)",
			By(CarrierHasSize.At(n), cardinality.HasSizeDef))
		// The group is read off the untyped fact units, so the residue pairs
		// with its membership at on.Any. Grounded at units_mod(n), the law's
		// product and identity are read off units_mod's definition:
		// multiplication mod n, and the residue rem(1, n).
		power := cyclic_group.PowCardIsOne.Read(unitGroup).At(arg.MemberOf[on.Any](residue, unit))
		reduced := arg.Have(
			"raised to the number φ(n) of units, the unit rem(a, n) is the identity, the residue of 1",
			"rem(a, n) ^ totient(n) ≡ 1 (mod n)",
			By(
				finite,
				power,
				CarrierHasSize.At(n),
				cardinality.HasSizeDef,
				UnitsPowMod,
				nat_congruence.CongDef.At(arg.TermAs[Nat]("rem(a, n) ^ totient(n)"), arg.Ctx().Nat(1), n)))
		arg.Show(
			"a is congruent to its residue, so their powers φ(n) are congruent, and the residue's is 1",
			By(
				reduced,
				nat_congruence.ResidueCongruent.At(a, n),
				nat_congruence.PowCongruent.At(residue, a, n, phi),
				nat_congruence.CongDef))
	}),
})}
