package proof

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
	"github.com/euc-ai/xugo/ext/prop"
)

// A fact in hand — a resident Have, the ground instance f.At(w…) of a
// resident ∀-fact, a law read at a resident structure fact — is taken
// by the verbs that take a Fact as a cited law is.

// provesInHand runs a section build and reports its panic as the
// test's failure, so one refusal does not end the package's run.
func provesInHand(t *testing.T, build func() *GoalStackNode) (sec *GoalStackNode) {
	t.Helper()
	defer func() {
		if r := recover(); r != nil {
			t.Errorf("refused: %v", r)
			sec = nil
		}
	}()
	return build()
}

type (
	natSet = ext.Set[ext.Nat]
	natFun = ext.Fun[ext.Nat, ext.Nat]
)

// The ground instance of a resident guarded equation rewrites by its
// equation, the fact that discharges its guard listed beside it: the
// group is the instance with its facts, so the fact verbs take it
// (#1268).
func TestFactInHand_RwAtAGroundInstance(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀s:(num → bool). ∀f g:num → num. ∀P:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ⇒ g(x) = f(x)) ⇒ u ∈ s ⇒ P(f(u)) ⇒ P(g(u))",
			func(a *Argument, s *ext.Expr[natSet], f, g *ext.Expr[natFun], P *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				agree, uIn, holds Fact) {
				a.Do(GroupPremises(uIn, agree.At(u)).Rw())
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// next.At(j).Rw() on an unguarded resident ∀-equation (#637).
func TestFactInHand_RwAtAnUnguardedGroundInstance(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀f g:num → num. ∀P:num → bool. ∀j:num. "+
			"(∀k. f(k) = g(k + 1)) ⇒ P(g(j + 1)) ⇒ P(f(j))",
			func(a *Argument, f, g *ext.Expr[natFun], P *ext.Expr[natSet], j *ext.Expr[ext.Nat], next, holds Fact) {
				a.Do(next.At(j).Rw())
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Unpack2 of the ground instance of a resident guarded ∃-fact (#1295,
// #1425).
func TestFactInHand_UnpackAGroundInstance(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀L c:(num → bool). ∀F:num → num → num. ∀X:num. "+
			"(∀Y. Y ∈ L ⇒ ∃r v. r ∈ c ∧ Y = F(r, v)) ⇒ X ∈ L ⇒ ∃r v. X = F(r, v)",
			func(a *Argument, L, c *ext.Expr[natSet], F *ext.Expr[ext.Op[ext.Nat]], X *ext.Expr[ext.Nat], fraction, xIn Fact) {
				r, v, spec := a.Unpack2As[ext.Nat, ext.Nat](GroupPremises(xIn, fraction.At(X)), "r", "v")
				a.Take(r)
				a.Take(v)
				a.Show("the witnesses", By(spec))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Conjuncts splits the ground instance of a resident guarded
// conjunction (#1425).
func TestFactInHand_ConjunctsOfAGroundInstance(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀s:(num → bool). ∀P Q:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ⇒ P(x) ∧ Q(x)) ⇒ u ∈ s ⇒ Q(u) ∧ P(u)",
			func(a *Argument, s *ext.Expr[natSet], P, Q *ext.Expr[natSet], u *ext.Expr[ext.Nat], both, uIn Fact) {
				parts := a.Conjuncts(GroupPremises(uIn, both.At(u)), "P holds at u", "Q holds at u")
				a.Show("the conjuncts, swapped", By(parts[1], parts[0]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Simplified rewrites the ground instance of a resident Have (#1391).
func TestFactInHand_SimplifiedGroundInstance(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀s:(num → bool). ∀f g:num → num. ∀P:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ⇒ P(f(x))) ⇒ (∀y. f(y) = g(y)) ⇒ u ∈ s ⇒ P(g(u))",
			func(a *Argument, s *ext.Expr[natSet], f, g *ext.Expr[natFun], P *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				holds, same, uIn Fact) {
				at := a.Simplified(GroupPremises(uIn, holds.At(u)), Fwd(same))
				a.Show("the simplified instance", By(at))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// MemberOf reads the instance of f.At(w…), not the ∀-statement (#1243,
// #1433).
func TestFactInHand_MemberOfAGroundInstance(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀c:(num → bool). ∀q:num → num. ∀j:num. (∀i. q(i) ∈ c) ⇒ q(j) ∈ c",
			func(a *Argument, c *ext.Expr[natSet], q *ext.Expr[natFun], j *ext.Expr[ext.Nat], qIn Fact) {
				qj := a.TermAs[ext.Nat]("q(j)")
				requirePanicContains(t, "pairs through the Argument's MemberOf", func() { MemberOf(qj, qIn.At(j)) })
				m := a.MemberOf[on.C](qj, qIn.At(j))
				a.Show("the member's evidence", By(m))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Simp takes a resident guarded ∀-equation as a conditional rule whose
// guard discharges from the context (#1262, #1429).
func TestFactInHand_SimpByAResidentGuardedEquation(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀t:(num → bool). ∀F:num → num. ∀P:num → bool. ∀z a:num. "+
			"(∀y. y ∈ t ⇒ F(y) = z) ⇒ a ∈ t ⇒ P(z) ⇒ P(F(a))",
			func(a *Argument, tt *ext.Expr[natSet], F *ext.Expr[natFun], P *ext.Expr[natSet], z, x *ext.Expr[ext.Nat],
				zero, aIn, holds Fact) {
				a.Do(Simp(Fwd(zero)))
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Simp takes a resident ∀-equation as a rule under a binder, where no
// ground instance reaches (#846).
func TestFactInHand_SimpUnderABinder(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀f g:num → num. ∀Q:(num → num) → bool. "+
			"(∀n. f(n) = g(n + 1)) ⇒ Q(λn. g(n + 1)) ⇒ Q(λn. f(n))",
			func(a *Argument, f, g *ext.Expr[natFun], Q *ext.Expr[ext.Fun[natFun, ext.Bool]], identity, holds Fact) {
				a.Do(Simp(Fwd(identity)))
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// inHandReadingEnv: a structure `handUnit : (A → A → A) → A → (A →
// bool) → bool` whose laws are `e ∈ c` (the unit lies in the carrier)
// and `∀x. x ∈ c ⇒ ∃y. y ∈ c ∧ op(x, y) = e` (every point has an
// inverse in c).
type inHandReadingEnv struct{ ctx *Script }

func makeInHandReadingEnv() *inHandReadingEnv {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	setA := MakeFun(core.TypeA(), TypeBool)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("handUnit",
		MakeFun(opA, MakeFun(core.TypeA(), MakeFun(setA, TypeBool)))))
	serveThm(ctx, "zz_hand_unit_in", core.TestThm(ctx.MakePropText(
		"∀op:A → A → A. ∀e:A. ∀c:(A → bool). handUnit(op, e, c) ⇒ e ∈ c").Conclusion()))
	serveThm(ctx, "zz_hand_inverse", core.TestThm(ctx.MakePropText(
		"∀op:A → A → A. ∀e:A. ∀c:(A → bool). handUnit(op, e, c) ⇒ ∀x. x ∈ c ⇒ ∃y. y ∈ c ∧ op(x, y) = e").Conclusion()))
	serveThm(ctx, "zz_hand_two_sided", core.TestThm(ctx.MakePropText(
		"∀op:A → A → A. ∀e:A. ∀c:(A → bool). handUnit(op, e, c) ⇒ ∀x. x ∈ c ⇒ op(x, e) = x ∧ op(e, x) = x").Conclusion()))
	serveThm(ctx, "zz_hand_side_to_side", core.TestThm(ctx.MakePropText(
		"∀op:A → A → A. ∀e:A. ∀c:(A → bool). handUnit(op, e, c) ⇒ ∀x. x ∈ c ⇒ op(x, e) = x ⇒ op(e, x) = x").Conclusion()))
	return &inHandReadingEnv{ctx: ctx}
}

// Unpack of a law read at a resident structure fact, grounded at a
// member (#1276).
func TestFactInHand_UnpackAReadingInstance(t *testing.T) {
	e := makeInHandReadingEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. "+
			"handUnit(op, u, c) ⇒ x ∈ c ⇒ ∃y. op(x, y) = u",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				unit, xIn Fact) {
				m := MemberOf(x, xIn)
				y, inv := a.UnpackAs[ext.Nat](WithMembers(Read(depName("zz_hand_inverse"), unit).At(x), m), "y")
				a.Take(y)
				a.Show("the inverse", By(inv))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// MemberOf reads a law read at a resident structure fact (#1216).
func TestFactInHand_MemberOfAReading(t *testing.T) {
	e := makeInHandReadingEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀R:num → bool. "+
			"handUnit(op, u, c) ⇒ (∀x. x ∈ c ⇒ R(x)) ⇒ R(u)",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], R *ext.Expr[natSet],
				unit, holds Fact) {
				m := a.MemberOf[on.C](u, Read(depName("zz_hand_unit_in"), unit))
				a.Show("R holds at the unit", By(holds, m))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	_ = prop.MakeProp
}

// Unpack of a law read at a resident structure fact, grounded at a
// point whose membership is listed beside it, without the member pairing.
func TestFactInHand_UnpackAPlainReadingInstance(t *testing.T) {
	e := makeInHandReadingEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. "+
			"handUnit(op, u, c) ⇒ x ∈ c ⇒ ∃y. op(x, y) = u",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				unit, xIn Fact) {
				y, inv := a.UnpackAs[ext.Nat](GroupPremises(xIn, Read(depName("zz_hand_inverse"), unit).At(x)), "y")
				a.Take(y)
				a.Show("the inverse", By(inv))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Conjuncts and Simplified take a typed reading's ground instance, the
// premise group its `.At` returns: the evidence is in context, the
// instance is materialized and split or rewritten (#1425).
func TestFactInHand_ConjunctsAndSimplifiedOfAReadingGroup(t *testing.T) {
	e := makeInHandReadingEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. ∀R:num → bool. "+
			"handUnit(op, u, c) ⇒ x ∈ c ⇒ (∀y. op(u, y) = y ⇒ op(y, u) = y ⇒ R(y)) ⇒ R(x)",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, holds Fact) {
				m := MemberOf(x, xIn)
				sides := a.Conjuncts(WithMembers(Read(depName("zz_hand_two_sided"), unit).At(x), m),
					"the unit on the right", "the unit on the left")
				whole := a.Simplified(WithMembers(Read(depName("zz_hand_two_sided"), unit).At(x), m))
				conj, _ := whole.BoundContent()
				require.Len(t, ext.DecomposesAND(conj), 2, "the instance as it stands: %s", ext.PrintTerm(conj))
				a.Show("R from both sides", By(holds.At(x), sides[1], sides[0]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A fact that discharges a guard is named in the group the instance
// travels in: the verb takes the group as it takes the instance, and a
// guard the group leaves out is refused (UnlistedGuardIsRefused).
func TestFactInHand_FactsTravelWithTheirInstance(t *testing.T) {
	const statement = "∀s:(num → bool). ∀P Q R:num → bool. ∀u:num. ∀A:bool. " +
		"(∀x. x ∈ s ⇒ Q(x) ⇒ P(x) ∧ R(x)) ⇒ (A ⇒ u ∈ s) ⇒ (A ⇒ Q(u)) ⇒ A ⇒ R(u) ∧ P(u)"
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(statement,
			func(a *Argument, s *ext.Expr[natSet], P, Q, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], A *ext.Expr[ext.Bool],
				both, inS, holds, assumed Fact) {
				member := a.Have("u is in s", "u ∈ s", By(inS, assumed))
				atU := a.Have("Q holds at u", "Q(u)", By(holds, assumed))
				parts := a.Conjuncts(GroupPremises(member, atU, both.At(u)), "P at u", "R at u")
				whole := a.Simplified(GroupPremises(member, atU, both.At(u)))
				conj, _ := whole.BoundContent()
				require.Len(t, ext.DecomposesAND(conj), 2, "the instance as it stands: %s", ext.PrintTerm(conj))
				a.Show("both parts", By(parts[1], parts[0]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A group is spliced into a group: the cite a typed reading's At returns
// carries its member's evidence, and a further fact travels with both.
// The fact the law is read at supplies its own guard, so listing it
// again is refused.
func TestFactInHand_GroupSplicesAReadingGroup(t *testing.T) {
	e := makeInHandReadingEnv()
	const statement = "∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. ∀R:num → bool. " +
		"handUnit(op, u, c) ⇒ x ∈ c ⇒ op(x, u) = x ⇒ R(op(u, x)) ⇒ R(x)"
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem(statement,
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, right, holds Fact) {
				m := MemberOf(x, xIn)
				left := a.Simplified(GroupPremises(right, WithMembers(Read(depName("zz_hand_side_to_side"), unit).At(x), m)))
				a.Show("R at x, the unit on the left", By(left, holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	requirePanicContains(t, "listed with facts it does not need — every guard of it the discharge met is stated by "+
		"the other facts listed:\n  handUnit(op₀, u₀, c₀) — hyp \"assumption\"", func() {
		e.ctx.Theorem(statement,
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, right, holds Fact) {
				m := MemberOf(x, xIn)
				a.Simplified(GroupPremises(unit, right, WithMembers(Read(depName("zz_hand_side_to_side"), unit).At(x), m)))
			})
	})
}

// A guard the context does not hold stays on the instance, and the verb
// that needs the instance's own shape names it: nothing is assumed.
func TestFactInHand_UnsuppliedGuardIsNamed(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	requirePanicContains(t, "still guarded by u₀ ∈ s₀", func() {
		ctx.Theorem("∀s:(num → bool). ∀f g:num → num. ∀P:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ⇒ g(x) = f(x)) ⇒ P(f(u)) ⇒ P(g(u))",
			func(a *Argument, s *ext.Expr[natSet], f, g *ext.Expr[natFun], P *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				agree, holds Fact) {
				a.Do(agree.At(u).Rw())
			})
	})
	requirePanicContains(t, "still guarded by u₀ ∈ s₀", func() {
		ctx.Theorem("∀s:(num → bool). ∀P Q:num → bool. ∀u:num. (∀x. x ∈ s ⇒ P(x) ∧ Q(x)) ⇒ Q(u) ∧ P(u)",
			func(a *Argument, s *ext.Expr[natSet], P, Q *ext.Expr[natSet], u *ext.Expr[ext.Nat], both Fact) {
				a.Conjuncts(both.At(u), "P holds at u", "Q holds at u")
			})
	})
	requirePanicContains(t, "no rule fired", func() {
		ctx.Theorem("∀t:(num → bool). ∀F:num → num. ∀P:num → bool. ∀z a:num. "+
			"(∀y. y ∈ t ⇒ F(y) = z) ⇒ P(z) ⇒ P(F(a))",
			func(a *Argument, tt *ext.Expr[natSet], F *ext.Expr[natFun], P *ext.Expr[natSet], z, x *ext.Expr[ext.Nat],
				zero, holds Fact) {
				a.Do(Simp(Fwd(zero)))
			})
	})
}

// A ground instance is materialized without a refutation, and a
// resident rule's obligation closes on the hypothesis itself: neither
// spelling records a CNF key, and no certificate of the rule enters the
// theorem caches.
func TestFactInHand_RecordsNoRefutation(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	rw := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀s:(num → bool). ∀f g:num → num. ∀P:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ⇒ g(x) = f(x)) ⇒ u ∈ s ⇒ P(f(u)) ⇒ P(g(u))",
			func(a *Argument, s *ext.Expr[natSet], f, g *ext.Expr[natFun], P *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				agree, uIn, holds Fact) {
				eq := a.Simplified(GroupPremises(uIn, agree.At(u)))
				a.Do(eq.Rw())
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, rw != nil && rw.Proved())
	require.NotContains(t, describeTree(rw), "CNF", "%s", describeTree(rw))
	require.Contains(t, describeTree(rw), "Specialize (keep)")

	var rule core.ThmCert
	simp := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀t:(num → bool). ∀F:num → num. ∀P:num → bool. ∀z a:num. "+
			"(∀y. y ∈ t ⇒ F(y) = z) ⇒ a ∈ t ⇒ P(z) ⇒ P(F(a))",
			func(a *Argument, tt *ext.Expr[natSet], F *ext.Expr[natFun], P *ext.Expr[natSet], z, x *ext.Expr[ext.Nat],
				zero, aIn, holds Fact) {
				content, _ := zero.BoundContent()
				rule = core.Assume(content)
				a.Do(Simp(Fwd(zero)))
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, simp != nil && simp.Proved())
	require.NotContains(t, describeTree(simp), "CNF", "%s", describeTree(simp))
	require.Contains(t, describeTree(simp), "Assumption", "the rule's obligation closes on the hypothesis")
	require.False(t, ctx.LocalThmCache.HasThm(rule), "an assumed rule is no cached theorem")
	require.False(t, ctx.Env.ThmCache.HasThm(rule), "an assumed rule is no cached theorem")
}

// A resident closure listed as a rule discharges another rule's side
// condition at the ground term it needs (#1295): `op(u, v) ∈ s` from
// u ∈ s, v ∈ s and the closure. Without the closure nothing fires.
func TestFactInHand_ResidentClosureDischargesASideCondition(t *testing.T) {
	statement := "∀s:(num → bool). ∀op:num → num → num. ∀F G:num → num. ∀P:num → bool. ∀u v:num. " +
		"(∀x. x ∈ s ⇒ F(x) = G(x)) ⇒ (∀x y. x ∈ s ∧ y ∈ s ⇒ op(x, y) ∈ s) ⇒ u ∈ s ⇒ v ∈ s ⇒ " +
		"P(G(op(u, v))) ⇒ P(F(op(u, v)))"
	type body = func(a *Argument, s *ext.Expr[natSet], op *ext.Expr[ext.Op[ext.Nat]], F, G *ext.Expr[natFun],
		P *ext.Expr[natSet], u, v *ext.Expr[ext.Nat], eq, closed, uIn, vIn, holds Fact)
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(statement, body(func(a *Argument, s *ext.Expr[natSet], op *ext.Expr[ext.Op[ext.Nat]], F, G *ext.Expr[natFun],
			P *ext.Expr[natSet], u, v *ext.Expr[ext.Nat], eq, closed, uIn, vIn, holds Fact) {
			a.Do(Simp(Fwd(eq), Fwd(closed)))
			a.Show("the rewritten goal is the fact", By(holds))
		}))
	})
	require.True(t, sec != nil && sec.Proved())
	requirePanicContains(t, "no rule fired", func() {
		ctx.Theorem(statement, body(func(a *Argument, s *ext.Expr[natSet], op *ext.Expr[ext.Op[ext.Nat]], F, G *ext.Expr[natFun],
			P *ext.Expr[natSet], u, v *ext.Expr[ext.Nat], eq, closed, uIn, vIn, holds Fact) {
			a.Do(Simp(Fwd(eq)))
		}))
	})
}

// A resident rule rewrites another fact in place; a fact does not
// rewrite itself, SimpAll (which rewrites every hypothesis) takes no
// resident rule, and a ground instance is no rule.
func TestFactInHand_ResidentRuleRefusals(t *testing.T) {
	statement := "∀f g:num → num. ∀P:num → bool. ∀j:num. (∀k. f(k) = g(k)) ⇒ P(f(j)) ⇒ P(g(j))"
	type body = func(a *Argument, f, g *ext.Expr[natFun], P *ext.Expr[natSet], j *ext.Expr[ext.Nat], same, holds Fact)
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(statement, body(func(a *Argument, f, g *ext.Expr[natFun], P *ext.Expr[natSet], j *ext.Expr[ext.Nat], same, holds Fact) {
			a.Do(holds.Simp(Fwd(same)))
			a.Show("the rewritten fact is the goal", By(holds))
		}))
	})
	require.True(t, sec != nil && sec.Proved())
	requirePanicContains(t, "does not rewrite itself", func() {
		ctx.Theorem(statement, body(func(a *Argument, f, g *ext.Expr[natFun], P *ext.Expr[natSet], j *ext.Expr[ext.Nat], same, holds Fact) {
			a.Do(same.Simp(Fwd(same)))
		}))
	})
	requirePanicContains(t, "SimpAll rewrites every hypothesis", func() {
		ctx.Theorem(statement, body(func(a *Argument, f, g *ext.Expr[natFun], P *ext.Expr[natSet], j *ext.Expr[ext.Nat], same, holds Fact) {
			a.Do(SimpAll(Fwd(same)))
		}))
	})
	requirePanicContains(t, "f.At(w…).Rw() for a fact in hand", func() {
		ctx.Theorem(statement, body(func(a *Argument, f, g *ext.Expr[natFun], P *ext.Expr[natSet], j *ext.Expr[ext.Nat], same, holds Fact) {
			a.Do(Simp(Fwd(same.At(j))))
		}))
	})
}

// Grounding a resident fact at a tuple whose instance is already
// resident takes the instance as it stands and records nothing; a fact
// named by content grounds as one named by its handle.
func TestFactInHand_GroundingIsIdempotentAndByContent(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀f g:num → num. ∀P:num → bool. ∀j:num. "+
			"(∀k. f(k) = g(k + 1)) ⇒ P(g(j + 1)) ⇒ P(f(j))",
			func(a *Argument, f, g *ext.Expr[natFun], P *ext.Expr[natSet], j *ext.Expr[ext.Nat], next, holds Fact) {
				a.Do(next.At(j))
				a.Do(next.At(j))
				content, _ := next.BoundContent()
				a.Do(ResidentHyp(content).At(j).Rw())
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	require.Equal(t, 1, strings.Count(describeTree(sec), "Specialize"), "%s", describeTree(sec))
}

// A premise group names the facts an instance's guards consume beside
// the law it grounds — the premise-carrying Unpack target (#1433).
func TestFactInHand_UnpackAGroupThatNamesItsGuards(t *testing.T) {
	e := makeInHandReadingEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. "+
			"handUnit(op, u, c) ⇒ x ∈ c ⇒ ∃y. op(x, y) = u",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				unit, xIn Fact) {
				y, inv := a.UnpackAs[ext.Nat](GroupPremises(xIn, Read(depName("zz_hand_inverse"), unit).At(x)), "y")
				a.Take(y)
				a.Show("the inverse", By(inv))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A guard clause that stands inside a resident conjunction supplies the
// guard of a fact in hand, as it supplies the guard of a By premise: the
// same datum, gathered into one resident fact and listed, discharges
// `agree.At(u)` whether the instance is a premise of a close or the fact
// a verb acts on (#1455, BasisSpansOverlap and DualizingMapsOnLine).
func TestFactInHand_GuardSuppliedByAResidentConjunction(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	// Three hypotheses, the middle one a conjunction written as one.
	const rewrite = "∀s:(num → bool). ∀f g:num → num. ∀P Q:num → bool. ∀u:num. " +
		"(∀x. x ∈ s ⇒ g(x) = f(x)) ∧ (u ∈ s ∧ Q(u)) ∧ P(f(u)) ⇒ P(g(u))"
	// The By premise: the conjunction is named, and its conjunct
	// discharges the guard inside the close.
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(rewrite,
			func(a *Argument, s *ext.Expr[natSet], f, g *ext.Expr[natFun], P, Q *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				agree, both, holds Fact) {
				eq := a.Have("the equation at u", "g(u) = f(u)", By(both, agree.At(u)))
				a.Do(eq.Rw())
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	// The fact in hand: the same conjunction resident, the same guard.
	sec = provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(rewrite,
			func(a *Argument, s *ext.Expr[natSet], f, g *ext.Expr[natFun], P, Q *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				agree, both, holds Fact) {
				eq := a.Simplified(GroupPremises(both, agree.At(u)))
				a.Do(eq.Rw())
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	require.NotContains(t, describeTree(sec), "CNF", "the grounding is keyless:\n%s", describeTree(sec))
	// Conjuncts of the instance, the guard again a conjunct of one
	// resident fact.
	sec = provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀s:(num → bool). ∀P Q R:num → bool. ∀u:num. (∀x. x ∈ s ⇒ P(x) ∧ Q(x)) ∧ (u ∈ s ∧ R(u)) ⇒ Q(u) ∧ P(u)",
			func(a *Argument, s *ext.Expr[natSet], P, Q, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], both, held Fact) {
				parts := a.Conjuncts(GroupPremises(held, both.At(u)), "P holds at u", "Q holds at u")
				a.Show("the conjuncts, swapped", By(parts[1], parts[0]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A guard the context supplies in part is refused naming the clause it
// does not supply, not the whole guard: `u ∈ s` is a conjunct of a
// resident fact and `R(u)` is nowhere.
func TestFactInHand_UnsuppliedGuardClauseIsNamed(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	requirePanicContains(t, "the context does not supply R₀(u₀)", func() {
		ctx.Theorem("∀s:(num → bool). ∀f g:num → num. ∀P Q R:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ∧ R(x) ⇒ g(x) = f(x)) ∧ (u ∈ s ∧ Q(u)) ∧ P(f(u)) ⇒ P(g(u))",
			func(a *Argument, s *ext.Expr[natSet], f, g *ext.Expr[natFun], P, Q, R *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				agree, both, holds Fact) {
				a.Do(agree.At(u).Rw())
			})
	})
}

// A law read bare at a resident structure fact — no witnesses — is
// installed as its stated form, one hypothesis, and the guard after the
// structure hypothesis is discharged from the fact listed beside it: as
// written, or as a conjunct of one resident fact. The preserving chain
// read the context instead — with the guard resident as written it
// split the conjunction on install and Conjuncts could not locate the
// fact; with the guard a conjunct it kept the implication (#1533, #1539).
func serveTwoSidedGuardedLaw(e *inHandReadingEnv) {
	serveThm(e.ctx, "zz_hand_two_laws", core.TestThm(e.ctx.MakePropText(
		"∀op:A → A → A. ∀e:A. ∀c:(A → bool). handUnit(op, e, c) ⇒ e ∈ c ⇒ "+
			"(∀x. x ∈ c ⇒ op(x, e) = x) ∧ (∀x. x ∈ c ⇒ op(e, x) = x)").Conclusion()))
}

func TestFactInHand_ConjunctsOfABareReadingWithItsGuardResident(t *testing.T) {
	e := makeInHandReadingEnv()
	serveTwoSidedGuardedLaw(e)
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. handUnit(op, u, c) ⇒ u ∈ c ⇒ x ∈ c ⇒ op(x, u) = x",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat], unit, uIn, xIn Fact) {
				sides := a.Conjuncts(GroupPremises(uIn, Read(depName("zz_hand_two_laws"), unit)), "right unit", "left unit")
				a.Show("the right unit law at x", By(sides[0].At(x), xIn))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

func TestFactInHand_ConjunctsOfABareReadingWithItsGuardAConjunct(t *testing.T) {
	e := makeInHandReadingEnv()
	serveTwoSidedGuardedLaw(e)
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. handUnit(op, u, c) ⇒ u ∈ c ⇒ x ∈ c ⇒ op(x, u) = x",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat], unit, uIn, xIn Fact) {
				both := a.Have("both memberships", "u ∈ c ∧ x ∈ c", By(uIn, xIn))
				a.Do(Clear(uIn, xIn))
				sides := a.Conjuncts(GroupPremises(both, Read(depName("zz_hand_two_laws"), unit)), "right unit", "left unit")
				a.Show("the right unit law at x", By(sides[0].At(x), both))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The witnessed path, the control: a ground instance's guard is
// discharged from a conjunct of one resident fact as before.
func TestFactInHand_ConjunctsOfAGroundInstanceWithItsGuardAConjunct(t *testing.T) {
	e := makeInHandReadingEnv()
	serveTwoSidedGuardedLaw(e)
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. handUnit(op, u, c) ⇒ u ∈ c ⇒ x ∈ c ⇒ op(x, u) = x",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat], unit, uIn, xIn Fact) {
				both := a.Have("both memberships", "u ∈ c ∧ x ∈ c", By(uIn, xIn))
				a.Do(Clear(uIn, xIn))
				sides := a.Conjuncts(GroupPremises(unit, both, At(depName("zz_hand_two_laws"), op, u, c)), "right unit", "left unit")
				a.Show("the right unit law at x", By(sides[0].At(x), both))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A conjunctive guard on the spine is read conjunct by conjunct, each
// as written or as a conjunct of one resident fact: with `u ∈ c` and
// `P(u) ∧ Q(u)` resident the guard `u ∈ c ∧ P(u) ∧ Q(u)` of a ground
// instance is discharged.
func TestFactInHand_ConjunctiveGuardFromSeveralFacts(t *testing.T) {
	e := makeInHandReadingEnv()
	serveThm(e.ctx, "zz_hand_three_guards", core.TestThm(e.ctx.MakePropText(
		"∀op:A → A → A. ∀e:A. ∀c:(A → bool). ∀P Q R:(A → bool). handUnit(op, e, c) ⇒ e ∈ c ∧ P(e) ∧ Q(e) ⇒ R(e)").Conclusion()))
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀P Q R:(num → bool). "+
			"handUnit(op, u, c) ⇒ u ∈ c ⇒ P(u) ⇒ Q(u) ⇒ R(u)",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], P, Q, R *ext.Expr[natSet],
				unit, uIn, pu, qu Fact) {
				a.Have("P and Q at the unit, as one fact", "P(u) ∧ Q(u)", By(pu, qu))
				a.Do(Clear(pu, qu))
				a.Do(Cite(depName("zz_hand_three_guards"), op, u, c, P, Q, R))
				a.Show("R at the unit, the guard discharged", By(a.Hyp(a.Term("R(u)"))))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// MemberOf at on.Any pairs a point with its membership in whatever set
// the fact says — the pairing a law read at an UNTYPED instance takes
// — from any fact in hand, a ground instance the free MemberOf refuses
// included (#1441, #1461).
func TestFactInHand_MemberOfAtAnyCarrier(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀c:(num → bool). ∀P:num → bool. ∀q:num → num. ∀j:num. (∀i. q(i) ∈ c) ⇒ (∀x. x ∈ c ⇒ P(x)) ⇒ P(q(j))",
			func(a *Argument, c *ext.Expr[natSet], P *ext.Expr[natSet], q *ext.Expr[natFun], j *ext.Expr[ext.Nat], qIn, all Fact) {
				qj := a.TermAs[ext.Nat]("q(j)")
				m := a.MemberOf[on.Any](qj, qIn.At(j))
				a.Show("the member's evidence", By(all, m))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	sec = provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀c:(num → bool). ∀P:num → bool. ∀j:num. j ∈ c ⇒ (∀x. x ∈ c ⇒ P(x)) ⇒ P(j)",
			func(a *Argument, c *ext.Expr[natSet], P *ext.Expr[natSet], j *ext.Expr[ext.Nat], jIn, all Fact) {
				m := a.MemberOf[on.Any](j, jIn)
				a.Show("the resident fact's evidence", By(all, m))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A law read at a resident structure fact follows the fact through a
// Let that respells it, as a premise handle does: the reading is
// derived at the hypothesis as the leaf spells it — bare, or at
// witnesses as `Law.Read(fact).At(v)` — and the premise locating that
// hypothesis beside the reading finds it there.
func TestFactInHand_AReadingFollowsItsFactThroughALet(t *testing.T) {
	e := makeInHandReadingEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀f:num → num. ∀c:(num → bool). ∀z:num. handUnit(op, f(z), c) ⇒ f(z) ∈ c",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], f *ext.Expr[natFun], c *ext.Expr[natSet], z *ext.Expr[ext.Nat], unit Fact) {
				inC := Read(depName("zz_hand_unit_in"), unit)
				a.Let("u", a.Term("f(z)").Core())
				a.Show("the unit lies in c", By(inC))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	sec = provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀op:num → num → num. ∀f:num → num. ∀c:(num → bool). ∀x z:num. "+
			"handUnit(op, f(z), c) ⇒ x ∈ c ⇒ op(x, f(z)) = x",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], f *ext.Expr[natFun], c *ext.Expr[natSet], x, z *ext.Expr[ext.Nat],
				unit, xIn Fact) {
				sides := Read(depName("zz_hand_two_sided"), unit)
				a.Let("u", a.Term("f(z)").Core())
				a.Show("the right unit law at x", By(xIn, sides.At(x)))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The control: a reading under a hypothesis the leaf no longer carries
// — cleared since the fact was taken — is refused naming it.
func TestFactInHand_AReadingUnderAClearedFactIsRefused(t *testing.T) {
	e := makeInHandReadingEnv()
	requirePanicContains(t, "is not a hypothesis of this leaf", func() {
		e.ctx.Theorem("∀op:num → num → num. ∀u:num. ∀c:(num → bool). handUnit(op, u, c) ⇒ u ∈ c",
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], unit Fact) {
				inC := Read(depName("zz_hand_unit_in"), unit)
				a.Do(Clear(unit))
				a.Show("the unit lies in c", By(inC))
			})
	})
}

// A rule whose right side holds an instance of its left is refused as a
// rewrite. The failure names it where its left side matches, and a rule
// that matches nowhere is the plain no-fire, naming nothing.
func TestSimp_NamesASelfEmbeddingRuleWhereItMatches(t *testing.T) {
	type relation = ext.Fun[ext.Nat, natSet]
	statement := func(conclusion string) string {
		return "∀R:num → num → bool. ∀Q:num → bool. ∀a b:num. (∀x. R(x, a) ⇔ ∃y. R(y, a) ∧ Q(x)) ⇒ " + conclusion
	}
	body := func(a *Argument, R *ext.Expr[relation], Q *ext.Expr[natSet], x, y *ext.Expr[ext.Nat], rule Fact) {
		a.Do(Simp(Fwd(rule)))
	}
	ctx := NewScript(makeStepTestEnv())
	requirePanicContains(t, "Refused as a rewrite", func() { ctx.Theorem(statement("R(b, a)"), body) })
	requirePanicContains(t, "Refused as a rewrite", func() {
		ctx.Theorem(statement("R(b, a) ⇒ Q(b)"),
			func(a *Argument, R *ext.Expr[relation], Q *ext.Expr[natSet], x, y *ext.Expr[ext.Nat], rule, holds Fact) {
				a.Do(holds.Simp(Fwd(rule)))
			})
	})
	defer func() {
		r := recover()
		require.NotNil(t, r)
		require.Contains(t, fmt.Sprint(r), "no rule fired")
		require.NotContains(t, fmt.Sprint(r), "Refused")
	}()
	ctx.Theorem(statement("Q(b)"), body)
}

// A guard the context supplies through a fact the verb was not handed is
// refused, naming the clause, the resident fact that states it and the
// spelling that lists it; a group that lists one guard's fact and not the
// other's is refused naming the other alone. A listed conjunction
// supplies a guard it holds as a conjunct.
func TestFactInHand_UnlistedGuardIsRefused(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	const statement = "∀s:(num → bool). ∀P Q R:num → bool. ∀u:num. " +
		"(∀x. x ∈ s ⇒ Q(x) ⇒ P(x) ∧ R(x)) ⇒ u ∈ s ⇒ Q(u) ⇒ R(u) ∧ P(u)"
	requirePanicContains(t, "Fact.Conjuncts: the instance of hyp \"assumption\" at (u₀) is guarded by u₀ ∈ s₀, "+
		"which the context supplies and the fact in hand does not list:\n  u₀ ∈ s₀ — stated by the resident fact u₀ ∈ s₀\n"+
		"  a guard is discharged from the facts listed with the instance, never from the context at large", func() {
		ctx.Theorem(statement,
			func(a *Argument, s *ext.Expr[natSet], P, Q, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], both, inS, atU Fact) {
				a.Conjuncts(both.At(u), "P at u", "R at u")
			})
	})
	requirePanicContains(t, "is guarded by Q₀(u₀), which the context supplies and the fact in hand does not list:\n"+
		"  Q₀(u₀) — stated by the resident fact Q₀(u₀)", func() {
		ctx.Theorem(statement,
			func(a *Argument, s *ext.Expr[natSet], P, Q, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], both, inS, atU Fact) {
				a.Conjuncts(GroupPremises(inS, both.At(u)), "P at u", "R at u")
			})
	})
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀s:(num → bool). ∀P Q R:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ⇒ Q(x) ⇒ P(x) ∧ R(x)) ∧ (u ∈ s ∧ Q(u)) ⇒ R(u) ∧ P(u)",
			func(a *Argument, s *ext.Expr[natSet], P, Q, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], both, pair Fact) {
				parts := a.Conjuncts(GroupPremises(pair, both.At(u)), "P at u", "R at u")
				a.Show("both parts", By(parts[1], parts[0]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A fact listed with an instance discharges a guard of it that no other
// listed fact states: a fact no guard reads is refused, as is the later
// of two that state one guard, and a resident fact taken as it stands
// has no guard for a listed fact to discharge.
func TestFactInHand_SurplusListedFactIsRefused(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	const statement = "∀s:(num → bool). ∀P Q R:num → bool. ∀u:num. " +
		"(∀x. x ∈ s ⇒ P(x) ∧ R(x)) ⇒ u ∈ s ⇒ Q(u) ⇒ R(u) ∧ P(u)"
	requirePanicContains(t, "Fact.Conjuncts: the instance of hyp \"assumption\" at (u₀) is listed with facts it does not need — "+
		"every guard of it the discharge met is stated by the other facts listed:\n  Q₀(u₀) — hyp", func() {
		ctx.Theorem(statement,
			func(a *Argument, s *ext.Expr[natSet], P, Q, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], both, inS, atQ Fact) {
				a.Conjuncts(GroupPremises(inS, atQ, both.At(u)), "P at u", "R at u")
			})
	})
	requirePanicContains(t, "stated by the other facts listed:\n  (u₀ ∈ s₀) ∧ Q₀(u₀) — hyp \"u lies in s, where Q holds\"\n", func() {
		ctx.Theorem(statement,
			func(a *Argument, s *ext.Expr[natSet], P, Q, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], both, inS, atQ Fact) {
				again := a.Have("u lies in s, where Q holds", "u ∈ s ∧ Q(u)", By(inS, atQ))
				a.Conjuncts(GroupPremises(inS, again, both.At(u)), "P at u", "R at u")
			})
	})
	requirePanicContains(t, "is listed with facts it does not need — it carries no guard the listed facts discharge:\n  u₀ ∈ s₀", func() {
		ctx.Theorem("∀s:(num → bool). ∀P R:num → bool. ∀u:num. u ∈ s ⇒ R(u) ⇒ P(u) ⇒ P(u) ∧ R(u)",
			func(a *Argument, s *ext.Expr[natSet], P, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], inS, atR, atP Fact) {
				pair := a.Have("both at u", "R(u) ∧ P(u)", By(atR, atP))
				a.Conjuncts(GroupPremises(inS, pair), "R at u", "P at u")
			})
	})
}

// A member's evidence travels with the member and is never reported,
// the member listed in a group or attached by a typed reading's At; the
// same fact listed by hand beside it supplies nothing the evidence does
// not, and is refused.
func TestFactInHand_MemberEvidenceIsNotSurplus(t *testing.T) {
	e := makeInHandReadingEnv()
	const statement = "∀op:num → num → num. ∀u:num. ∀c:(num → bool). ∀x:num. ∀R:num → bool. " +
		"handUnit(op, u, c) ⇒ x ∈ c ⇒ (∀y. op(u, y) = y ⇒ op(y, u) = y ⇒ R(y)) ⇒ R(x)"
	requirePanicContains(t, "stated by the other facts listed:\n  x₀ ∈ c₀ — hyp", func() {
		e.ctx.Theorem(statement,
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, holds Fact) {
				m := MemberOf(x, xIn)
				a.Conjuncts(GroupPremises(xIn, WithMembers(Read(depName("zz_hand_two_sided"), unit).At(x), m)),
					"the unit on the right", "the unit on the left")
			})
	})
	sec := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem(statement,
			func(a *Argument, op *ext.Expr[ext.Op[ext.Nat]], u *ext.Expr[ext.Nat], c *ext.Expr[natSet], x *ext.Expr[ext.Nat],
				R *ext.Expr[natSet], unit, xIn, holds Fact) {
				m := MemberOf(x, xIn)
				sides := a.Conjuncts(GroupPremises(m, WithMembers(Read(depName("zz_hand_two_sided"), unit).At(x), m)),
					"the unit on the right", "the unit on the left")
				a.Show("R from both sides", By(holds.At(x), sides[1], sides[0]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A group runs as a step: `a.Do(GroupPremises(h, f.At(w…)))` grounds the
// instance on the spine with h listed, as `a.Do(f.At(w…))` grounds one
// whose guards no fact need discharge.
func TestFactInHand_GroupGroundsOnTheSpine(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	const statement = "∀s:(num → bool). ∀P R:num → bool. ∀u:num. (∀x. x ∈ s ⇒ P(x) ⇒ R(x)) ⇒ u ∈ s ⇒ P(u) ⇒ R(u)"
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(statement,
			func(a *Argument, s *ext.Expr[natSet], P, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], law, inS, atU Fact) {
				a.Do(GroupPremises(inS, atU, law.At(u)))
				a.Show("R at u stands", By(a.Hyp("R(u)")))
			})
	})
	require.True(t, sec != nil && sec.Proved())
	requirePanicContains(t, "is guarded by P₀(u₀), which the context supplies and the fact in hand does not list", func() {
		ctx.Theorem(statement,
			func(a *Argument, s *ext.Expr[natSet], P, R *ext.Expr[natSet], u *ext.Expr[ext.Nat], law, inS, atU Fact) {
				a.Do(GroupPremises(inS, law.At(u)))
			})
	})
}
