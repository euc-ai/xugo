// values.go — the values of φ at a prime power and at a prime, and φ's
// positivity.

package totient

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// TotientPrimePower — φ(p^k) = p^k − p^(k−1) for a prime p and k > 0. A
// residue below p^k is coprime to p^k exactly when p does not divide it
// (nat_prime.CoprimePrimePowerIff), so the residues φ counts are those
// below p^k with the multiples of p taken out, and the multiples of p below
// p^k = p·p^(k−1) are p^(k−1) in number (nat_divides.MultiplesBelowCount).
var TotientPrimePower = totientPrimePowerThm{family.Add(registry.ProofEntry{
	Name: "TotientPrimePower",
	Key:  "prop_25ce34cb799ac21f",
	Build: family.Theorem(Statement{
		Binders: "∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"0 < k",
		},
		Conclusion: "totient(p ^ k) = p ^ k - p ^ (k - 1)",
	}, func(a *Argument, p, k *Expr[Nat], prime, positive Fact) {
		power := a.TermAs[Nat]("p ^ k")
		lower := a.TermAs[Nat]("p ^ (k - 1)")
		residues := a.TermAs[Set[Nat]]("{a:num | a < p ^ k}")
		multiplesOfP := a.TermAs[Set[Nat]]("{a:num | a < p ^ k ∧ p ∣ a}")

		positiveP := a.Have(
			"p is positive, being at least 2",
			"0 < p",
			ByArith(prime, nat_prime.PrimeAtLeastTwo.At(p)))
		multiples := a.Have(
			"the multiples of p below p^k = p·p^(k − 1) are p^(k − 1) in number",
			"has_size({a:num | a < p ^ k ∧ p ∣ a}, p ^ (k - 1))",
			By(
				positive,
				positiveP,
				nat_monus.MulPowSubOne.At(p, k),
				nat_divides.MultiplesBelowCount.At(p, lower)))
		coprimes := a.Have(
			"a residue is coprime to p^k exactly when p does not "+
				"divide it, so the coprime residues are the others",
			"{a:num | a < p ^ k ∧ nat_coprime(a, p ^ k)} = {a:num | a < p ^ k} ∖ {a:num | a < p ^ k ∧ p ∣ a}",
			// nat_prime.CoprimePrimePowerIff at p and k, its a left quantified for
			// BySets to read at each residue: the typed At takes the whole tuple, so
			// this cite is untyped.
			BySets(prime, positive, At(nat_prime.CoprimePrimePowerIff, p, k)))
		a.Show(
			"φ(p^k) counts the p^k residues below p^k less the p^(k − 1) multiples of p among them",
			By(
				coprimes,
				multiples,
				set_basic.SubsetDef.At(multiplesOfP, residues),
				num_segment.HasSizeBelowStrict.At(power),
				cardinality.HasSizeDiff.At(residues, multiplesOfP, power, lower),
				TotientHasSize.At(power),
				cardinality.CardOfSized))
	}),
})}

// TotientPrime — φ(p) = p − 1 for a prime p: the case k = 1 of
// TotientPrimePower, p^1 − p^0.
var TotientPrime = totientPrimeThm{family.Add(registry.ProofEntry{
	Name: "TotientPrime",
	Key:  "prop_9c66f81704c54ade",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "totient(p) = p - 1",
	}, func(a *Argument, p *Expr[Nat], prime Fact) {
		a.Show(
			"φ(p^1) = p^1 − p^0, which is p − 1",
			ByArith(prime, TotientPrimePower.At(p, a.TermAs[Nat]("1"))))
	}),
})}

// TotientPositive — φ(n) is positive for n > 0: the remainder of 1 by n is a
// residue below n, coprime to n as 1 is, so the residues φ(n) counts are not
// none. The witness is that remainder and not 1 itself, which is not below n
// at n = 1.
var TotientPositive = totientPositiveThm{family.Add(registry.ProofEntry{
	Name: "TotientPositive",
	Key:  "prop_bf49b8246cfec8c7",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"0 < n",
		},
		Conclusion: "0 < totient(n)",
	},
		func(a *Argument, n *Expr[Nat], positive Fact) {
			one := a.TermAs[Nat]("1")
			residue := a.Have(
				"the remainder of 1 by n is a residue below n, coprime to n as 1 is",
				"rem(1, n) < n ∧ nat_coprime(rem(1, n), n)",
				By(
					positive,
					nat_gcd.Coprime.At(one, n),
					nat_divides.DividesOne,
					nat_gcd.CoprimeLMod.At(one, n),
					nat_div_mod.Division.At(one, n),
					nat_order.PosIffNonzero))
			nonempty := a.Have(
				"so the residues below n coprime to n are not none",
				"{a:num | a < n ∧ nat_coprime(a, n)} ≠ ∅",
				BySets(residue))
			a.Show(
				"φ(n) is their number, and a set of size 0 is empty",
				By(
					nonempty,
					TotientHasSize.At(n),
					cardinality.HasSizeZero.At(a.TermAs[Set[Nat]]("{a:num | a < n ∧ nat_coprime(a, n)}")),
					nat_order.PosIffNonzero.At(a.TermAs[Nat]("totient(n)"))))
		}),
})}
