package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
	"github.com/stretchr/testify/require"
)

// The member's evidence at the cite that consumes it (member_evidence.go):
// a premise grounded at a Member whose membership is one of the
// instance's guards is consumed with that evidence listed, carried, or
// refused — never with the point alone.

// rightUnitEnv serves, beside the in-hand structure laws, one law whose
// body is the guarded equation alone: `handUnit(op, e, c) ⇒ ∀x. x ∈ c ⇒
// op(x, e) = x`.
func rightUnitEnv() *inHandReadingEnv {
	e := makeInHandReadingEnv()
	serveThm(e.ctx, "zz_hand_right_unit", core.TestThm(e.ctx.MakePropText(
		"∀op:A → A → A. ∀e:A. ∀c:(A → bool). handUnit(op, e, c) ⇒ ∀x. x ∈ c ⇒ op(x, e) = x").Conclusion()))
	return e
}

const rightUnitGoal = "∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. handUnit(op, u, c) ⇒ x ∈ c ⇒ op(x, u) = x"

type rightUnitBody func(a *Argument, unit, xIn Fact, x *ext.Expr[ext.Nat]) Action

func rightUnitTheorem(e *inHandReadingEnv, body rightUnitBody) *GoalStackNode {
	return e.ctx.Theorem(rightUnitGoal,
		func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
			unit, xIn Fact) {
			a.Show("u is a unit on the right of x", body(a, unit, xIn, x))
		})
}

// A Member handed to an At whose guard is its membership, and nothing of
// its evidence in the list: the point arrives, the evidence would not,
// and the By names the member instead of failing at the refuter.
func TestBy_RefusesAMemberWhoseEvidenceIsNotListed(t *testing.T) {
	e := rightUnitEnv()
	requirePanicContains(t, "does not hold the member's evidence", func() {
		rightUnitTheorem(e, func(a *Argument, unit, xIn Fact, x *ext.Expr[ext.Nat]) Action {
			m := MemberOf(x, xIn)
			return By(Read(depName("zz_hand_right_unit"), unit).At(m))
		})
	})
}

// The member listed beside the premise it grounds: its evidence is in the
// list, as the By idiom writes it.
func TestBy_AMemberListedBesideItsPremise(t *testing.T) {
	e := rightUnitEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return rightUnitTheorem(e, func(a *Argument, unit, xIn Fact, x *ext.Expr[ext.Nat]) Action {
			m := MemberOf(x, xIn)
			return By(m, Read(depName("zz_hand_right_unit"), unit).At(m))
		})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The member carried with the premise (Member.With, WithMembers): the
// premise group holds the evidence.
func TestBy_AMemberCarriedWithItsPremise(t *testing.T) {
	e := rightUnitEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return rightUnitTheorem(e, func(a *Argument, unit, xIn Fact, x *ext.Expr[ext.Nat]) Action {
			m := MemberOf(x, xIn)
			return By(m.With(Read(depName("zz_hand_right_unit"), unit).At(m)))
		})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The membership listed by content rather than by the member's handle
// (ResidentHyp, emit's spelling of a resident premise): the guard is in
// the list.
func TestBy_AMembershipListedByContent(t *testing.T) {
	e := rightUnitEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return rightUnitTheorem(e, func(a *Argument, unit, xIn Fact, x *ext.Expr[ext.Nat]) Action {
			m := MemberOf(x, xIn)
			return By(ResidentHyp(a.Term("x ∈ c")), Read(depName("zz_hand_right_unit"), unit).At(m))
		})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A Member at a slot no membership guard reads is the point alone: there
// is no evidence for the instance to want, and nothing is refused.
func TestBy_AMemberAtASlotWithoutAGuard(t *testing.T) {
	e := rightUnitEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. "+
			"x ∈ c ⇒ (∀y:num. op(y, u) = y) ⇒ op(x, u) = x",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				xIn, unitOnTheRight Fact) {
				m := MemberOf(x, xIn)
				a.Show("u is a unit on the right of x", By(unitOnTheRight.At(m)))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// squareClosedEnv serves, beside the in-hand structure laws, a closure
// law stated before the proof runs, so a reading of it names the member
// it concludes (ReadMember):
//
//	handUnit(op, e, c) ⇒ ∀x. x ∈ c ⇒ op(x, x) ∈ c
func squareClosedEnv() (*inHandReadingEnv, statedDep) {
	e := makeInHandReadingEnv()
	stated := e.ctx.MakePropText(
		"∀op:A → A → A. ∀e:A. ∀c:(A → bool). handUnit(op, e, c) ⇒ ∀x. x ∈ c ⇒ op(x, x) ∈ c")
	serveThm(e.ctx, "zz_hand_square_in", core.TestThm(stated.Conclusion()))
	return e, statedDep{name: "zz_hand_square_in", stated: stated}
}

// squareOf is the closure law read at the structure fact and grounded at
// p: op(p, p), whose evidence is p's and the reading at p.
func squareOf(law statedDep, unit Fact, p *Member[ext.Nat, on.Any]) *Member[ext.Nat, on.Any] {
	return ReadMember[ext.Nat, on.Any](law.stated, Read(law, unit), unit, p)
}

// A member whose evidence holds another closure member — op(x, x) read
// at op(x, x) — is materialized as a fact in hand: each premise of its
// evidence is installed with the evidence before it listed, so the
// reading at the inner member finds x ∈ c, and the reading at the outer
// one finds both memberships.
func TestFactInHand_AClosureMemberReadAtAClosureMember(t *testing.T) {
	e, law := squareClosedEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. ∀R:num → bool. "+
			"handUnit(op, u, c) ⇒ x ∈ c ⇒ (∀y. y ∈ c ⇒ R(y)) ⇒ R(op(op(x, x), op(x, x)))",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, holds Fact) {
				outer := squareOf(law, unit, squareOf(law, unit, MemberOf(x, xIn)))
				held := a.MemberOf[on.Any](&outer.Expr, outer)
				a.Show("R at the square of the square", By(holds, held))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The evidence lists only what the member holds: a closure law read at
// a bare point carries no membership of it, so the inner reading's guard
// x ∈ c, resident in the context, is still refused when the outer
// member is materialized, and a fact the author lists beside the member
// is not handed to its evidence.
func TestFactInHand_AClosureMemberListsOnlyItsEvidence(t *testing.T) {
	e, law := squareClosedEnv()
	const statement = "∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. ∀R:num → bool. " +
		"handUnit(op, u, c) ⇒ x ∈ c ⇒ (∀y. y ∈ c ⇒ R(y)) ⇒ R(op(op(x, x), op(x, x)))"
	const refusal = "at (x₀) is guarded by x₀ ∈ c₀, which the context supplies and the fact in hand does not list"
	bareSquare := func(unit Fact, x *ext.Expr[ext.Nat]) *Member[ext.Nat, on.Any] {
		return ReadMember[ext.Nat, on.Any](law.stated, Read(law, unit), unit, x)
	}
	requirePanicContains(t, refusal, func() {
		e.ctx.Theorem(statement,
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, holds Fact) {
				outer := squareOf(law, unit, bareSquare(unit, x))
				a.MemberOf[on.Any](&outer.Expr, outer)
			})
	})
	requirePanicContains(t, refusal, func() {
		e.ctx.Theorem(statement,
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, holds Fact) {
				outer := squareOf(law, unit, bareSquare(unit, x))
				a.MemberOf[on.Any](&outer.Expr, GroupPremises(xIn, outer))
			})
	})
}

// A closure member carried with a cite (WithMembers): the group lists
// its evidence, and each premise of it is installed with the evidence
// before it listed, so the reading at x finds x ∈ c and the cite at
// op(x, x) finds the member's membership.
func TestFactInHand_AClosureMemberCarriedWithACite(t *testing.T) {
	e, law := squareClosedEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. ∀R:num → bool. "+
			"handUnit(op, u, c) ⇒ x ∈ c ⇒ (∀y. op(u, y) = y ⇒ op(y, u) = y ⇒ R(y)) ⇒ R(op(x, x))",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, holds Fact) {
				square := squareOf(law, unit, MemberOf(x, xIn))
				sides := a.Conjuncts(WithMembers(Read(depName("zz_hand_two_sided"), unit).At(square), square),
					"the unit on the right", "the unit on the left")
				a.Show("R from both sides", By(holds.At(square), sides[1], sides[0]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}
