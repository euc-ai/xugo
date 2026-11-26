// multiples.go — the sets of multiples and of divisors of a number: the
// multiples of p below p·m are m in number, and a positive number has
// finitely many divisors.

package nat_divides

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// MultiplesBelowCount — the multiples of p below p·m are p·b for the m
// numbers b below m, and multiplying by p ≠ 0 is one-to-one, so there are m
// of them.
var MultiplesBelowCount = multiplesBelowCountThm{family.Add(registry.ProofEntry{
	Name: "MultiplesBelowCount",
	Key:  "prop_a54aa9630c510b00",
	Build: family.Theorem(Statement{
		Binders: "∀p m:num.",
		Hypotheses: []string{
			"0 < p",
		},
		Conclusion: "has_size({a:num | a < p * m ∧ p ∣ a}, m)",
	}, func(a *Argument, p, m *Expr[Nat], positive Fact) {
		multiples := a.Have(
			"a is a multiple of p below p·m exactly when it is p·b for some b below m",
			"∀a:num. a < p * m ∧ p ∣ a ⇔ (∃b:num. a = p * b ∧ b < m)",
			a.ForEach(func(a *Expr[Nat]) Action {
				return By(
					positive,
					DividesFactor.At(p, a),
					nat_order.LessThanMulCancel,
					nat_order.PosIffNonzero.At(p))
			}))
		below := a.TermAs[Set[Nat]]("{b:num | b < m}")
		scale := a.TermAs[Fun[Nat, Nat]]("λb:num. p * b")
		image := a.Have(
			"so they are the image of the numbers below m under b ↦ p·b",
			"{a:num | a < p * m ∧ p ∣ a} = image(λb:num. p * b, {b:num | b < m})",
			BySets(multiples))
		oneToOne := a.Have(
			"multiplying by p ≠ 0 is one-to-one",
			"injective_on({b:num | b < m}, λb:num. p * b)",
			By(positive, functions.InjectiveOnDef, nat_arith.MulEqLCancel, nat_order.PosIffNonzero.At(p)))
		a.Show(
			"an image under a one-to-one map has as many points as its source, m",
			By(
				image,
				oneToOne,
				num_segment.HasSizeBelowStrict.At(m),
				cardinality.HasSizeImageInj.At(scale, below, m)))
	}),
})}

// DivisorsFinite — a positive number has finitely many divisors: they lie
// among the numbers up to it.
var DivisorsFinite = divisorsFiniteThm{family.Add(registry.ProofEntry{
	Name: "DivisorsFinite",
	Key:  "prop_d2e1fd12c4d02fcb",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Hypotheses: []string{"0 < n"},
		Conclusion: "finite({d:num | d ∣ n})",
	}, func(arg *Argument, n *Expr[Nat], positive Fact) {
		bounded := arg.Have(
			"a divisor of n is at most n, since n is not 0",
			"∀d:num. d ∣ n ⇒ d ≤ n",
			arg.ForEach(func(d *Expr[Nat]) Action {
				return ByArith(positive, DividesLessEq.At(d, n))
			}))
		arg.Show(
			"so the divisors of n lie among the finitely many numbers up to n",
			By(
				bounded,
				finite_set.FiniteSubset.At(
					arg.TermAs[Set[Nat]]("{d:num | d ∣ n}"), arg.TermAs[Set[Nat]]("{x:num | x ≤ n}")),
				num_segment.FiniteBelow.At(n),
				set_basic.SubsetDef))
	}),
})}
