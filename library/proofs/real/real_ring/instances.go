// instances.go — ℝ is a commutative ring: the instances the abstract
// chapters read, built up from the axioms in the order the structures
// nest, the four fold facts the two monoids yield — what Σ and Π over ℝ
// read the fold mechanism through — and the additive monoid's power of
// one, which is the real numeral. Nothing is proved twice: the additive
// group is the additive monoid plus one axiom, the ring is the two
// structures plus one.

package real_ring

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// AddMonoid — real addition, with zero, is a commutative monoid.
var AddMonoid = addMonoidThm{family.Add(registry.ProofEntry{
	Name: "AddMonoid",
	Key:  "prop_59d3d62a2cc9a8e4",
	Build: family.Instance(comm_monoid.CommMonoid, "comm_monoid(real_add, &0)",
		Case(
			"addition commutes",
			Cite(real_construction.AddSym)),
		Case(
			"addition associates",
			Cite(real_construction.AddAssoc)),
		Case(
			"zero is a left identity",
			Cite(real_construction.AddLeftId))),
})}

// MulMonoid — real multiplication, with one, is a commutative monoid.
var MulMonoid = mulMonoidThm{family.Add(registry.ProofEntry{
	Name: "MulMonoid",
	Key:  "prop_bf74ab237b828ee4",
	Build: family.Instance(comm_monoid.CommMonoid, "comm_monoid(real_mul, &1)",
		Case(
			"multiplication commutes",
			Cite(real_construction.MulSym)),
		Case(
			"multiplication associates",
			Cite(real_construction.MulAssoc)),
		Case(
			"one is a left identity",
			Cite(real_construction.MulLeftId))),
})}

// AddGroup — real addition, with zero and negation, is an abelian
// group: a group — associative, zero a left identity, negation a left
// inverse — whose addition commutes.
var AddGroup = addGroupThm{family.Add(registry.ProofEntry{
	Name: "AddGroup",
	Key:  "prop_60782e87b79c6130",
	Build: family.Instance(abelian_group.AbelianGroup, "abelian_group(additive_group(real_ring))",
		Case(
			"addition, zero and negation form a group",
			Unfold(group.Group),
			SplitConjAll(
				Case(
					"addition associates",
					Cite(real_construction.AddAssoc)),
				Case(
					"zero is a left identity",
					Cite(real_construction.AddLeftId)),
				Case(
					"negation is a left inverse",
					Cite(real_construction.AddLeftInv)))),
		Case(
			"addition commutes",
			Cite(real_construction.AddSym))),
})}

// CommRing — ℝ is a commutative ring: the two structures above, joined
// by the distributive axiom, and subtraction as the definition spells
// it.
var CommRing = commRingThm{family.Add(registry.ProofEntry{
	Name: "CommRing",
	Key:  "prop_56f70d5221b563c8",
	Build: family.Instance(comm_ring.CommRing, "comm_ring(real_ring)",
		Case(
			"the additive group",
			Cite(AddGroup)),
		Case(
			"the multiplicative monoid",
			Cite(MulMonoid)),
		Case(
			"multiplication distributes over addition",
			Cite(real_construction.LeftDistrib)),
		Case(
			"subtraction is addition of the negation",
			Cite(RealSubDef))),
})}

// CommRingOn — ℝ is a commutative ring on its carrier, the whole type:
// the ring restricted to 𝕌 is the ring itself, so the whole-type ring
// is the ring on its carrier. A chapter that reads the laws of a ring on
// a set reads them at ℝ through this instance.
var CommRingOn = commRingOnThm{family.Add(registry.ProofEntry{
	Name: "CommRingOn",
	Key:  "prop_5276abed3107e953",
	Build: family.Theorem("comm_ring_on(real_ring)", func(a *Argument) {
		whole := a.Have(
			"ℝ's ring restricted to the whole type is ℝ's ring",
			"restrict_ring(real_ring, 𝕌) = real_ring",
			Simp(Fwd(module_record.RestrictRingDef), Fwd(RealRingDef)),
			Refl())
		a.Show(
			"so ℝ's ring laws hold on its carrier",
			By(Normalized, comm_ring.CommRingOnUniverse, CommRing, whole))
	}),
})}

// MonoidalAdd — real addition folds: the monoid chapter's bridge, read
// at the additive monoid. Each of these four closes is the law applied
// at the instance, and records no key.
var MonoidalAdd = monoidalAddThm{family.Add(registry.ProofEntry{
	Name:  "MonoidalAdd",
	Key:   "prop_7ae3b9b212a0a6ed",
	Build: family.Theorem("monoidal_op(real_add)", By(comm_monoid.Monoidal, AddMonoid)),
})}

// NeutralAdd — and it folds from zero.
var NeutralAdd = neutralAddThm{family.Add(registry.ProofEntry{
	Name:  "NeutralAdd",
	Key:   "prop_6a90fbee52253024",
	Build: family.Theorem("neutral_elem(real_add) = &0", By(comm_monoid.Neutral, AddMonoid)),
})}

// MonoidalMul — real multiplication folds likewise, at the
// multiplicative monoid.
var MonoidalMul = monoidalMulThm{family.Add(registry.ProofEntry{
	Name:  "MonoidalMul",
	Key:   "prop_e2068b8063af90ff",
	Build: family.Theorem("monoidal_op(real_mul)", By(comm_monoid.Monoidal, MulMonoid)),
})}

// NeutralMul — and it folds from one.
var NeutralMul = neutralMulThm{family.Add(registry.ProofEntry{
	Name:  "NeutralMul",
	Key:   "prop_2dd9fb3e087a0d93",
	Build: family.Theorem("neutral_elem(real_mul) = &1", By(comm_monoid.Neutral, MulMonoid)),
})}

// AddPowOne — n ones summed is the real numeral n: the additive monoid's
// power of one is the embedding of ℕ, the numeral a ring on ℝ reads as n.
// By induction on n: no ones sum to zero, and one more one adds one, as
// the embedding does at a successor (OfNumSuc).
var AddPowOne = addPowOneThm{family.Add(registry.ProofEntry{
	Name: "AddPowOne",
	Key:  "prop_f38765b078d8fd18",
	Build: family.Theorem("∀n:num. monoid_pow(real_add, &0, &1, n) = &n",
		func(a *Argument, n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"no ones sum to zero",
				Cite(comm_monoid.MonoidPowDef.Inst[Real]()))
			a.Step(
				"one more one adds one, as the embedding does at a successor",
				func(b *Argument, previous Fact) {
					b.Show(
						"the sum of n ones and one more is &n + &1 in either order",
						Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Real]()), Fwd(previous), Fwd(OfNumSuc)),
						Cite(real_construction.AddSym))
				})
		}),
})}
