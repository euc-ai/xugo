// instances.go — ℤ is a commutative ring: the instances the abstract
// chapters read, built up from the lifted laws in the order the
// structures nest, the four fold facts they yield, the ring's carrier
// holding every integer, and the embedding into ℝ as a homomorphism of
// additive groups. Nothing is proved twice: the additive group is a
// group plus commutativity, the ring is the two structures plus
// distributivity and subtraction, the homomorphism is two groups plus
// the bridge.

package int_real_lift

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// AddMonoid — integer addition, with zero, is a commutative monoid.
var AddMonoid = addMonoidThm{family.Add(registry.ProofEntry{
	Name: "AddMonoid",
	Key:  "prop_7038d51aa5e70578",
	Build: family.Instance(comm_monoid.CommMonoid, "comm_monoid(int_add, &0)",
		Case(
			"addition commutes",
			Cite(AddSym)),
		Case(
			"addition associates",
			Cite(AddAssoc)),
		Case(
			"zero is a left identity",
			Cite(AddLeftIdentity))),
})}

// MulMonoid — integer multiplication, with one, is a commutative monoid.
var MulMonoid = mulMonoidThm{family.Add(registry.ProofEntry{
	Name: "MulMonoid",
	Key:  "prop_ff37e9568c598836",
	Build: family.Instance(comm_monoid.CommMonoid, "comm_monoid(int_mul, &1)",
		Case(
			"multiplication commutes",
			Cite(MulSym)),
		Case(
			"multiplication associates",
			Cite(MulAssoc)),
		Case(
			"one is a left identity",
			Cite(MulLeftIdentity))),
})}

// IntRingDef — integer ring operations and its whole-type carrier.
var IntRingDef = intRingDefThm{family.Define(registry.DefEntry{
	Name: "IntRingDef",
	Key:  "prop_bbc7db31f13394aa", Const: "int_ring", Type: "ring_ops(int)",
	Equations: []string{"int_ring = mk_ring(int_add, &0, int_neg, int_mul, &1, int_sub, 𝕌)"},
})}

// AddGroup — integer addition, with zero and negation, is an abelian
// group: a group whose addition commutes.
var AddGroup = addGroupThm{family.Add(registry.ProofEntry{
	Name: "AddGroup",
	Key:  "prop_ec194e5e68b7c616",
	Build: family.Instance(abelian_group.AbelianGroup, "abelian_group(additive_group(int_ring))",
		Case(
			"addition, zero and negation form a group",
			Unfold(group.Group),
			SplitConjAll(
				Case(
					"addition associates",
					Cite(AddAssoc)),
				Case(
					"zero is a left identity",
					Cite(AddLeftIdentity)),
				Case(
					"negation is a left inverse",
					Cite(AddLeftInverse)))),
		Case(
			"addition commutes",
			Cite(AddSym))),
})}

// CommRing — ℤ is a commutative ring.
var CommRing = commRingThm{family.Add(registry.ProofEntry{
	Name: "CommRing",
	Key:  "prop_e162d5d0433fb1e2",
	Build: family.Instance(comm_ring.CommRing, "comm_ring(int_ring)",
		Case(
			"the additive group",
			Cite(AddGroup)),
		Case(
			"the multiplicative monoid",
			Cite(MulMonoid)),
		Case(
			"multiplication distributes over addition",
			Cite(LeftDistrib)),
		Case(
			"subtraction is addition of the negation",
			Cite(SubAddNeg))),
})}

// CommRingOn — ℤ is a commutative ring on its carrier, the whole type:
// the ring restricted to 𝕌 is the ring itself, so the whole-type ring
// is the ring on its carrier. A chapter that reads the laws of a ring on
// a set reads them at ℤ through this instance.
var CommRingOn = commRingOnThm{family.Add(registry.ProofEntry{
	Name: "CommRingOn",
	Key:  "prop_fcbef1aec6142a72",
	Build: family.Theorem("comm_ring_on(int_ring)", func(a *Argument) {
		whole := a.Have(
			"ℤ's ring restricted to the whole type is ℤ's ring",
			"restrict_ring(int_ring, 𝕌) = int_ring",
			Simp(Fwd(module_record.RestrictRingDef), Fwd(IntRingDef)),
			Refl())
		a.Show(
			"so ℤ's ring laws hold on its carrier",
			By(Normalized, comm_ring.CommRingOnUniverse, CommRing, whole))
	}),
})}

// IntegerRingCarrierUniversal — every native integer lies in the carrier of
// the integer ring, which is the whole type.
var IntegerRingCarrierUniversal = integerRingCarrierUniversalThm{family.Add(registry.ProofEntry{
	Name: "IntegerRingCarrierUniversal",
	Key:  "prop_bdeb4ce1365d7869",
	Build: family.Theorem("∀c:int. c ∈ int_ring.carrier", func(a *Argument, c *Expr[Int]) {
		a.Show(
			"the integer ring's carrier is the whole type",
			Simp(Fwd(IntRingDef)),
			By(set_basic.InUniv.Inst[Int]()))
	}),
})}

// MonoidalAdd — integer addition folds. Each of these four closes is
// the law applied at the instance, and records no key.
var MonoidalAdd = monoidalAddThm{family.Add(registry.ProofEntry{
	Name:  "MonoidalAdd",
	Key:   "prop_ea8627338d664973",
	Build: family.Theorem("monoidal_op(int_add)", By(comm_monoid.Monoidal, AddMonoid)),
})}

// NeutralAdd — and it folds from zero.
var NeutralAdd = neutralAddThm{family.Add(registry.ProofEntry{
	Name:  "NeutralAdd",
	Key:   "prop_6a21aa284e741531",
	Build: family.Theorem("neutral_elem(int_add) = &0", By(comm_monoid.Neutral, AddMonoid)),
})}

// MonoidalMul — integer multiplication folds.
var MonoidalMul = monoidalMulThm{family.Add(registry.ProofEntry{
	Name:  "MonoidalMul",
	Key:   "prop_bd45895e051952d2",
	Build: family.Theorem("monoidal_op(int_mul)", By(comm_monoid.Monoidal, MulMonoid)),
})}

// NeutralMul — and it folds from one.
var NeutralMul = neutralMulThm{family.Add(registry.ProofEntry{
	Name:  "NeutralMul",
	Key:   "prop_27f0494a91076a5a",
	Build: family.Theorem("neutral_elem(int_mul) = &1", By(comm_monoid.Neutral, MulMonoid)),
})}

// ---------------------------------------------------------------------------
// The embedding into ℝ is a homomorphism
// ---------------------------------------------------------------------------

// RealOfIntHom — the embedding of ℤ into ℝ is a homomorphism of
// additive groups, so every law of the homomorphism chapter reads at
// ℤ → ℝ through this instance. The two groups are the abelian ones read
// as groups.
var RealOfIntHom = realOfIntHomThm{family.Add(registry.ProofEntry{
	Name: "RealOfIntHom",
	Key:  "prop_3d5e87d4f0840092",
	Build: family.Instance(group_homomorphism.GroupHomomorphism,
		"group_homomorphism(restrict_group(additive_group(int_ring), 𝕌), "+
			"    restrict_group(additive_group(real_ring), 𝕌), "+
			"    real_of_int)",
		Case(
			"the source: ℤ's additive group, on the whole type",
			Derive(func(a *Argument) {
				additive := a.Have(
					"ℤ is a group under addition",
					"group(additive_group(int_ring))",
					By(abelian_group.Group, AddGroup))
				a.Show(
					"which is a group on 𝕌",
					By(additive, group.GroupOnUniverse))
			})),
		Case(
			"the target: ℝ's additive group, on the whole type",
			Derive(func(a *Argument) {
				additive := a.Have(
					"ℝ is a group under addition",
					"group(additive_group(real_ring))",
					By(abelian_group.Group, real_ring.AddGroup))
				a.Show(
					"which is a group on 𝕌",
					By(additive, group.GroupOnUniverse))
			})),
		Case(
			"the map carries the whole type into the whole type",
			BySets()),
		Case(
			"the map respects addition",
			Derive(func(a *Argument) {
				a.FixAs[Int]("x")
				a.FixAs[Int]("y")
				a.Assume()
				a.Show(
					"the embedding carries a sum to the sum of the images",
					By(int_construction.AddBridge))
			}))),
})}
