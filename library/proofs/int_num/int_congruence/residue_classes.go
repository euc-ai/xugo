// residue_classes.go — the multiples of n as a subgroup of ℤ, normal
// because ℤ commutes: the residue classes mod n are its cosets, and the
// quotient group of algebra/group reads at it.

package int_congruence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// MultiplesSubgroup — the multiples of n are a subgroup of the additive
// group of ℤ: 0 is n · 0, the sum of n · a and n · b is n · (a + b), and
// the negation of n · a is n · (-a). Each closure condition is a
// divisibility, and a divisibility is proved by exhibiting the multiple.
var MultiplesSubgroup = multiplesSubgroupThm{family.Add(registry.ProofEntry{
	Name: "MultiplesSubgroup",
	Key:  "prop_3a0e4c8d0d0422aa",
	Build: family.Theorem(Statement{
		Binders:    "∀n:int.",
		Conclusion: "subgroup(restrict_group(additive_group(int_ring), 𝕌), «multiplesOf»)",
	},
		func(a *Argument, n *Expr[Int]) {
			member := a.Have(
				"a point lies among the multiples exactly when n divides it",
				"∀z:int. z ∈ «multiplesOf» ⇔ n ∣ z",
				BySets())
			// Each closure condition is a membership, read through `member`
			// as a divisibility; a divisibility is proved by exhibiting the
			// multiple.
			a.Do(Unfold(group.SubgroupDef), SplitConjAll(
				Case(
					"the multiples lie in the whole type",
					BySets()),
				Case(
					"0 is a multiple: n times 0",
					Derive(func(b *Argument) {
						zero := b.TermAs[Int]("0")
						divides := b.Have(
							"n divides 0, which is n · 0",
							"n ∣ 0",
							Derive(func(c *Argument) {
								c.Do(Unfold(int_divides.IntDividesDef))
								c.Take(zero)
								c.Show(
									"0 and n · 0 are both 0",
									ByArith())
							}))
						b.Show(
							"so 0 lies among the multiples",
							By(member.At(zero), divides))
					})),
				Case(
					"the sum of two multiples is a multiple: n · a + n · b is n · (a + b)",
					Derive(func(b *Argument) {
						x := b.FixAs[Int]("x")
						y := b.FixAs[Int]("y")
						parts := b.Conjuncts(
							b.Assume(),
							"x lies among the multiples",
							"and so does y")
						xDiv := b.Have(
							"so n divides x",
							"n ∣ x",
							By(member.At(x), parts[0]))
						yDiv := b.Have(
							"and n divides y",
							"n ∣ y",
							By(member.At(y), parts[1]))
						_, xIs := b.UnpackAs[Int](b.Unfolded(xDiv, int_divides.IntDividesDef), "a")
						_, yIs := b.UnpackAs[Int](b.Unfolded(yDiv, int_divides.IntDividesDef), "b")
						sum := b.Have(
							"n divides x + y, which is n · (a + b)",
							"n ∣ x + y",
							Derive(func(c *Argument) {
								c.Do(Unfold(int_divides.IntDividesDef))
								c.Take(c.TermAs[Int]("a + b"))
								c.Show(
									"x + y = n · a + n · b = n · (a + b)",
									ByArith(xIs, yIs))
							}))
						b.Show(
							"so x + y lies among the multiples",
							By(member.At(b.TermAs[Int]("x + y")), sum))
					})),
				Case(
					"the negation of a multiple is a multiple: -(n · a) is n · (-a)",
					Derive(func(b *Argument) {
						x := b.FixAs[Int]("x")
						xDiv := b.Have(
							"n divides x",
							"n ∣ x",
							By(member.At(x), b.Assume()))
						_, xIs := b.UnpackAs[Int](b.Unfolded(xDiv, int_divides.IntDividesDef), "a")
						neg := b.Have(
							"n divides -x, which is n · (-a)",
							"n ∣ -x",
							Derive(func(c *Argument) {
								c.Do(Unfold(int_divides.IntDividesDef))
								c.Take(c.TermAs[Int]("-a"))
								c.Show(
									"-x = -(n · a) = n · (-a)",
									ByArith(xIs))
							}))
						b.Show(
							"so -x lies among the multiples",
							By(member.At(b.TermAs[Int]("-x")), neg))
					})),
			))
		}),
})}

// MultiplesNormal — the multiples of n are a normal subgroup of ℤ: a
// conjugate (g + x) + -g is x itself, since addition commutes, so the
// conjugation condition asks nothing beyond the subgroup. It is the
// normal subgroup the quotient group ℤ/nℤ is taken by.
var MultiplesNormal = multiplesNormalThm{family.Add(registry.ProofEntry{
	Name: "MultiplesNormal",
	Key:  "prop_29da2d4fc28effc2",
	Build: family.Theorem(Statement{
		Binders:    "∀n:int.",
		Conclusion: "normal_subgroup(restrict_group(additive_group(int_ring), 𝕌), «multiplesOf»)",
	},
		func(a *Argument, n *Expr[Int]) {
			a.Do(Unfold(group.NormalSubgroupDef), SplitConj(
				Case(
					"the multiples of n are a subgroup",
					By(MultiplesSubgroup)),
				Case(
					"a conjugate of a multiple is that multiple: (g + x) + -g is x",
					Derive(func(b *Argument) {
						b.FixAs[Int]("g")
						b.FixAs[Int]("x")
						multiple := b.Conjuncts(
							b.Assume(),
							"g is an integer",
							"x is a multiple")[1]
						collapses := b.Have(
							"(g + x) + -g is x, addition commuting",
							"(g + x) + -g = x",
							ByArith())
						b.Show(
							"so the conjugate is x, a multiple",
							collapses.Rw(),
							By(multiple))
					})),
			))
		}),
})}

// ResidueClassIsCoset — the residue class of x mod n is the coset of x
// of the multiples of n. Two sets are equal when they hold the same
// points: a point z lies in the class of x exactly when x ≡ z (mod n),
// that is when x - z is a multiple of n, and in the coset of x exactly
// when -x + z lies among the multiples. The two multiples are each
// other's negation.
var ResidueClassIsCoset = residueClassIsCosetThm{family.Add(registry.ProofEntry{
	Name: "ResidueClassIsCoset",
	Key:  "prop_3d2dd909c039c75f",
	Build: family.Theorem(Statement{
		Binders: "∀n x:int.",
		Conclusion: "equivalence_class(λy:int. λz:int. y ≡ z (mod n), x) = " +
			"left_coset(int_add, x, «multiplesOf»)",
	},
		func(a *Argument, n, x *Expr[Int]) {
			additive := abelian_group.Group.Read(int_real_lift.AddGroup)
			// Two sets are equal when they hold the same points z. The rules
			// below are pinned at int: a Go Simp rule is not instantiated at a
			// type on its own.
			a.Do(Simp(Fwd(set_basic.Extension.Inst[Int]())))
			a.FixAs[Int]("z")
			// z lies in the class of x when x ≡ z (mod n), that is when x - z
			// is a multiple of n; and in the coset of x when -x + z lies among
			// the multiples.
			a.Do(Simp(
				Fwd(equivalence.InClass.Inst[Int]()),
				Fwd(CongruentIffMultiple),
				Fwd(group.InLeftCoset.Read(additive))))
			member := a.Have(
				"a point lies among the multiples exactly when n divides it",
				"∀w:int. w ∈ «multiplesOf» ⇔ n ∣ w",
				BySets())
			divides := a.Have(
				"so -x + z lies among the multiples exactly when n divides it",
				"-x + z ∈ «multiplesOf» ⇔ n ∣ -x + z",
				By(member.At(a.TermAs[Int]("-x + z"))))
			a.Do(divides.Rw(), Unfold(int_divides.IntDividesDef))
			a.Iff()
			a.Forward(
				"x - z = n · d, so -x + z = n · (-d)",
				func(b *Argument, multiple Fact) {
					_, gap := b.UnpackAs[Int](multiple, "d")
					b.Take(b.TermAs[Int]("-d"))
					b.Show(
						"-x + z = -(x - z) = n · (-d)",
						ByArith(gap))
				})
			a.Backward(
				"-x + z = n · e, so x - z = n · (-e)",
				func(b *Argument, multiple Fact) {
					_, gap := b.UnpackAs[Int](multiple, "e")
					b.Take(b.TermAs[Int]("-e"))
					b.Show(
						"x - z = -(-x + z) = n · (-e)",
						ByArith(gap))
				})
		}),
})}
