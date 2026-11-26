// intervals.go — finite sets of integers, counted through the boundary:
// a finite set of integers is bounded below, and the integers strictly
// between a and b, or from a to b, are the images of the naturals below
// their count.

package int_embed

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteIntegersBoundedBelow — a finite set of integers is bounded below:
// its members lie at or above −N for some natural number N.
var FiniteIntegersBoundedBelow = finiteIntegersBoundedBelowThm{family.Add(registry.ProofEntry{
	Name: "FiniteIntegersBoundedBelow",
	Key:  "prop_8d71d32cc07edf9c",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(int).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "∃N:num. ∀j:int. j ∈ s ⇒ -&N ≤ j",
	},
		func(a *Argument, s *Expr[Set[Int]], finite Fact) {
			negation := a.TermAs[Fun[Int, Nat]]("λj:int. num_of_int(-j)")
			finiteNegations := a.Have(
				"the numbers num_of_int(−j), j in s, are finitely many",
				"finite(image(λj:int. num_of_int(-j), s))",
				By(finite, finite_set.FiniteImage.At(negation, s)))
			N, bounded := a.ObtainAs[Nat](
				"so they are bounded by some N",
				"∃N:num. image(λj:int. num_of_int(-j), s) ⊆ 0 .. N",
				By(finiteNegations, num_segment.FiniteIffBounded))
			inSegment := a.Unfolded(bounded, set_basic.SubsetDef)
			a.Take(N)
			a.Show(
				"−j is at most num_of_int(−j) ≤ N",
				Derive(func(b *Argument) {
					j := b.FixAs[Int]("j")
					member := b.Assume()
					negated := b.TermAs[Nat]("num_of_int(-j)")
					atMost := b.Have(
						"num_of_int(−j) is one of those numbers, so at most N",
						"num_of_int(-j) ≤ N",
						By(member, set_image.FunInImage.At(negation, s, j), inSegment.At(negated)))
					b.Show(
						"either −j is negative, or −j = num_of_int(−j)",
						ByArith(atMost, NumOfIntSection.At(b.TermAs[Int]("-j"))))
				}))
		}),
})}

// IntegersBetween — the integers strictly between a and b are finitely
// many, max(b − a − 1, 0) of them: they are the a + j + 1 for the naturals
// j below that number, and j ↦ a + j + 1 is one-to-one.
var IntegersBetween = integersBetweenThm{family.Add(registry.ProofEntry{
	Name: "IntegersBetween",
	Key:  "prop_6796c117e9bf1620",
	Build: family.Theorem("∀a b:int. "+
		"    finite({i:int | a < i ∧ i < b}) ∧ &card({i:int | a < i ∧ i < b}) = max(b - a - &1, &0)",
		func(arg *Argument, a, b *Expr[Int]) {
			nonnegative := arg.Have(
				"the count max(b − a − 1, 0) is not negative",
				"&0 ≤ max(b - a - &1, &0)",
				ByArith())
			m, count := arg.ObtainAs[Nat](
				"so it is a natural number m",
				"∃m:num. max(b - a - &1, &0) = &m",
				By(nonnegative, OfNumExists.At(arg.TermAs[Int]("max(b - a - &1, &0)"))))
			between := arg.Have(
				"the integers strictly between a and b are the a + j + 1 with j below m",
				"∀i:int. a < i ∧ i < b ⇔ ∃j:num. j < m ∧ i = a + &j + &1",
				Derive(func(c *Argument) {
					c.FixAs[Int]("i")
					c.Iff()
					c.Forward(
						"i − a − 1 is such a j",
						func(d *Argument, inside Fact) {
							j := d.TermAs[Nat]("num_of_int(i - a - &1)")
							cast := d.Have(
								"i − a − 1 is not negative, so it is the integer of its natural number",
								"&num_of_int(i - a - &1) = i - a - &1",
								ByArith(inside, NumOfIntSection.At(d.TermAs[Int]("i - a - &1"))))
							d.Take(j)
							d.Show(
								"it lies below m, as i < b, and a + j + 1 is i",
								ByArith(cast, count, inside, OfNumLt.At(j, m)))
						})
					c.Backward(
						"a + j + 1 lies strictly between a and b",
						func(d *Argument, hasJ Fact) {
							_, parts := d.UnpackAs[Nat](hasJ, "j")
							d.Show(
								"j ≥ 0 puts it above a, and j < m below b",
								ByArith(count, parts))
						})
				}))
			shift, below :=
				arg.TermAs[Fun[Nat, Int]]("λj:num. a + &j + &1"), arg.TermAs[Set[Nat]]("{j:num | j < m}")
			asImage := arg.Have(
				"so they are the image of the naturals below m under j ↦ a + j + 1",
				"{i:int | a < i ∧ i < b} = image(λj:num. a + &j + &1, {j:num | j < m})",
				BySets(between))
			oneToOne := arg.Have(
				"j ↦ a + j + 1 is one-to-one",
				"injective_on({j:num | j < m}, λj:num. a + &j + &1)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(c *Argument) {
					x, y := c.FixAs[Nat]("x"), c.FixAs[Nat]("y")
					same := c.Assume()
					c.Show(
						"a + x + 1 = a + y + 1 makes the integers of x and y equal, so x = y",
						ByArith(same, OfNumEq.At(x, y)))
				}))
			sized := arg.Have(
				"so the image has m members",
				"has_size(image(λj:num. a + &j + &1, {j:num | j < m}), m)",
				By(oneToOne, cardinality.HasSizeImageInj.At(shift, below, m), num_segment.HasSizeBelowStrict.At(m)))
			arg.Show(
				"so the integers between a and b are finitely many, m = max(b − a − 1, 0) of them",
				asImage.Rw(),
				By(
					count,
					sized,
					cardinality.HasSizeDef.At(arg.TermAs[Set[Int]]("image(λj:num. a + &j + &1, {j:num | j < m})"), m)))
		}),
})}

// IntIntervalSize — the integers from a to b are finite, max(b − a + 1, 0)
// of them: they are the integers strictly between a − 1 and b + 1.
var IntIntervalSize = intIntervalSizeThm{family.Add(registry.ProofEntry{
	Name: "IntIntervalSize",
	Key:  "prop_3ae557db3f5b0d10",
	Build: family.Theorem("∀a b:int. "+
		"    finite({i:int | a ≤ i ∧ i ≤ b}) ∧ &card({i:int | a ≤ i ∧ i ≤ b}) = max(b - a + &1, &0)",
		func(arg *Argument, a, b *Expr[Int]) {
			pointwise := arg.Have(
				"an integer lies from a to b exactly when it lies strictly between a − 1 and b + 1",
				"∀i:int. a ≤ i ∧ i ≤ b ⇔ a - &1 < i ∧ i < b + &1",
				ByArith())
			same := arg.Have(
				"so the two sets are one",
				"{i:int | a ≤ i ∧ i ≤ b} = {i:int | a - &1 < i ∧ i < b + &1}",
				BySets(pointwise))
			arg.Show(
				"which has max((b + 1) − (a − 1) − 1, 0) = max(b − a + 1, 0) members",
				same.Rw(),
				ByArith(IntegersBetween.At(arg.TermAs[Int]("a - &1"), arg.TermAs[Int]("b + &1"))))
		}),
})}
