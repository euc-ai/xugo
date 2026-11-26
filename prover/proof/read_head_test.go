package proof

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// The rigid skeleton is a necessary condition of the conclusion match:
// what it prunes, unify's match could never read; what it keeps, the
// match decides. Every ruling below is the match's own — a constant
// against itself alone, an application against an application of the
// same arity, an abstraction against an abstraction — with a variable
// head (a slot, a bound variable) deciding nothing.
func TestReadHead_ConclusionMayMatch(t *testing.T) {
	ind := TypeInd
	f := ext.Const(core.MakeConstMeta("f", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	g := ext.Const(core.MakeConstMeta("g", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	h := ext.Const(core.MakeConstMeta("h", core.MakeFun(ind, core.MakeFun(ind, ind))), core.MakeFun(ind, core.MakeFun(ind, ind)))
	x, y := ext.Var("x", ind), ext.Var("y", ind)
	p := ext.Var("p", core.MakeFun(ind, ind))
	q := ext.Var("q", core.MakeFun(ind, core.TypeBool()))

	target := f.Apply(x).Eq(g.Apply(y))
	cases := []struct {
		name   string
		stated core.Term
		may    bool
	}{
		{"the same rigid skeleton", f.Apply(y).Eq(g.Apply(x)), true},
		{"a flexible head on one side", p.Apply(y).Eq(g.Apply(x)), true},
		{"a bare variable side", x.Eq(g.Apply(x)), true},
		{"a different constant at the head of a side", g.Apply(y).Eq(g.Apply(x)), false},
		{"a different arity under the same constant", h.Apply(x).Apply(y).Eq(g.Apply(x)), false},
		{"a different top constant", q.Apply(x).And(q.Apply(y)), false},
		{"a variable at the top", x.Eq(y).Imply(q.Apply(x)), true},
		{"the head under guarded ∀ and antecedents", ext.ForAll(x)(g.Apply(x).Eq(x).Imply(ext.ForAll(y)(f.Apply(y).Eq(g.Apply(x))))), true},
		{"a mismatch under guarded ∀ and antecedents", ext.ForAll(x)(g.Apply(x).Eq(x).Imply(ext.ForAll(y)(g.Apply(y).Eq(g.Apply(x))))), false},
	}
	for _, c := range cases {
		assert.Equal(t, c.may, skeletonMayMatch(conclusionMatrix(c.stated), target), c.name)
	}

	// An abstraction sits only against an abstraction, and its body is
	// read on: `∀`'s argument is one.
	all := ext.ForAll(x)(f.Apply(x).Eq(g.Apply(x)))
	assert.True(t, skeletonMayMatch(ext.ForAll(y)(f.Apply(y).Eq(g.Apply(y))), all))
	assert.False(t, skeletonMayMatch(ext.ForAll(y)(g.Apply(y).Eq(g.Apply(y))), all), "the body's skeleton is read")
	assert.False(t, skeletonMayMatch(ext.ForAll(y)(f.Apply(y).Eq(g.Apply(y))), f.Apply(x).Eq(g.Apply(x))), "∀ against no ∀")
}

// The skeleton is read with its types: the match equates the types at
// every node after the stated letters are instantiated, and the goal's
// letters never are, so a stated node whose type no instantiation of
// the stated letters brings to the goal's declines the form before any
// instance is built — one substitution across the whole skeleton.
func TestReadHead_SkeletonReadsTheTypes(t *testing.T) {
	ind, bool_ := TypeInd, core.TypeBool()
	A, B := core.MakeVarType("A"), core.MakeVarType("B")
	x, y := ext.Var("x", ind), ext.Var("y", ind)
	a, b := ext.Var("a", A), ext.Var("b", A)
	p, q := ext.Var("p", core.MakeFun(ind, ind)), ext.Var("q", core.MakeFun(ind, ind))
	target := x.Eq(y)

	assert.True(t, skeletonMayMatch(a.Eq(b), target), "an equation at a letter: A := ind")
	assert.False(t, skeletonMayMatch(p.Eq(q), target), "an equation of functions never sits against one of individuals")
	u := ext.Var("u", B)
	assert.True(t, skeletonMayMatch(a.Eq(b), u.Eq(u)), "a stated letter is instantiated to the goal's")
	assert.False(t, skeletonMayMatch(p.Eq(q), u.Eq(u)), "the goal's letter is rigid")

	// One substitution across the skeleton: `rel` stated at A → A → bool
	// against the goal's instance at ind → (ind → ind) → bool binds A
	// to ind at the first argument and cannot bind it to ind → ind at
	// the second.
	rel := core.MakeConstMeta("rel", core.MakeFun(A, core.MakeFun(B, bool_)))
	stated := ext.Const(rel, core.MakeFun(A, core.MakeFun(A, bool_))).Apply(a).Apply(b)
	assert.True(t, skeletonMayMatch(stated, ext.Const(rel, core.MakeFun(ind, core.MakeFun(ind, bool_))).Apply(x).Apply(y)))
	assert.False(t, skeletonMayMatch(stated, ext.Const(rel, core.MakeFun(ind, core.MakeFun(core.MakeFun(ind, ind), bool_))).Apply(x).Apply(p)))
}

// A binder the conclusion does not spell is pinned by an antecedent
// piece matched against the goal's hypotheses or the facts, at the
// piece's head; where nothing at that head is offered, the form is
// declined before the match and Read declines it too, and where
// something is, Read decides.
func TestReadHead_PinningDecidesBeforeTheMatch(t *testing.T) {
	ind, bool_ := TypeInd, core.TypeBool()
	opType := core.MakeFun(ind, core.MakeFun(ind, ind))
	S := ext.Const(core.MakeConstMeta("S", core.MakeFun(opType, core.MakeFun(ind, core.MakeFun(ind, bool_)))),
		core.MakeFun(opType, core.MakeFun(ind, core.MakeFun(ind, bool_))))
	T := ext.Const(core.MakeConstMeta("T", core.MakeFun(ind, bool_)), core.MakeFun(ind, bool_))
	g := ext.Const(core.MakeConstMeta("g", opType), opType)
	op, e, z, x := ext.Var("op", opType), ext.Var("e", ind), ext.Var("z", ind), ext.Var("x", ind)
	a, b, c := ext.Var("a", ind), ext.Var("b", ind), ext.Var("c", ind)
	// `∀op e z. S(op, e, z) ⇒ ∀x. op(x, e) = x`: the conclusion pins op, e
	// and x; z only S's piece can.
	law := StatedHeadOf(prop.MakeProp(ext.ForAll(op, e, z)(S.Apply(op).Apply(e).Apply(z).Imply(ext.ForAll(x)(op.Apply(x).Apply(e).Eq(x))))))
	concl := g.Apply(a).Apply(b).Eq(a)
	fact := S.Apply(g).Apply(b).Apply(c)

	bare := prop.MakeProp(concl)
	assert.False(t, law.MayRead(HeadGoalOf(bare, nil)), "nothing offers S")
	_, ok := law.Read(HeadGoalOf(bare, nil))
	assert.False(t, ok)

	withHyp := prop.MakeProp(concl, fact)
	require.True(t, law.MayRead(HeadGoalOf(withHyp, nil)), "a hypothesis at S")
	reading, ok := law.Read(HeadGoalOf(withHyp, nil))
	require.True(t, ok)
	require.Len(t, reading.Witnesses, 4)
	assert.Equal(t, "c", ext.PrintTerm(reading.Witnesses[2].Witness), "z from the hypothesis")
	require.Len(t, reading.Premises, 1)
	assert.True(t, reading.Premises[0].Resident)

	facts := &FactSource{ByHead: map[core.TermName][]core.Term{"S": {fact}}, Structures: map[core.TermName]bool{}}
	require.True(t, law.MayRead(HeadGoalOf(bare, facts)), "a fact at S")
	reading, ok = law.Read(HeadGoalOf(bare, facts))
	require.True(t, ok)
	assert.Equal(t, "c", ext.PrintTerm(reading.Witnesses[2].Witness), "z from the fact")
	assert.False(t, reading.Premises[0].Resident)

	other := prop.MakeProp(concl, T.Apply(c))
	assert.False(t, law.MayRead(HeadGoalOf(other, nil)), "a hypothesis at another head offers S nothing")

	// A piece headed by a slot is matched against any hypothesis (the
	// first-order approximation of a flexible head) and against no fact.
	P := ext.Var("P", core.MakeFun(ind, bool_))
	slotLaw := StatedHeadOf(prop.MakeProp(ext.ForAll(P, z)(P.Apply(z).Imply(ext.ForAll(x)(x.Eq(x))))))
	reflexive := prop.MakeProp(a.Eq(a))
	assert.False(t, slotLaw.MayRead(HeadGoalOf(reflexive, facts)), "no hypothesis")
	reflexiveWithHyp := prop.MakeProp(a.Eq(a), T.Apply(c))
	assert.True(t, slotLaw.MayRead(HeadGoalOf(reflexiveWithHyp, nil)), "any hypothesis")
	reading, ok = slotLaw.Read(HeadGoalOf(reflexiveWithHyp, nil))
	require.True(t, ok)
	assert.Equal(t, "T", ext.PrintTerm(reading.Witnesses[0].Witness))
	assert.Equal(t, "c", ext.PrintTerm(reading.Witnesses[1].Witness))
}

// ReadHead declines through the skeleton what matchHead would decline
// through the match, and reads what it reads: the pre-read changes no
// verdict.
func TestReadHead_SkeletonPrunesOnlyWhatCannotMatch(t *testing.T) {
	ind := TypeInd
	f := ext.Const(core.MakeConstMeta("f", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	g := ext.Const(core.MakeConstMeta("g", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	a, x, y := ext.Var("a", ind), ext.Var("x", ind), ext.Var("y", ind)
	goal := prop.MakeProp(f.Apply(a).Eq(g.Apply(a)))

	law := prop.MakeProp(ext.ForAll(x, y)(f.Apply(x).Eq(g.Apply(y)).Imply(f.Apply(x).Eq(g.Apply(y)))))
	reading, ok := StatedHeadOf(law).Read(HeadGoalOf(goal, nil))
	require.True(t, ok, "the law's conclusion matches the goal")
	require.Len(t, reading.Witnesses, 2)
	assert.Equal(t, "a", ext.PrintTerm(reading.Witnesses[0].Witness))

	other := StatedHeadOf(prop.MakeProp(ext.ForAll(x, y)(f.Apply(x).Eq(g.Apply(y)).Imply(g.Apply(x).Eq(g.Apply(y))))))
	_, ok = other.Read(HeadGoalOf(goal, nil))
	assert.False(t, ok, "g(x) = g(y) cannot read f(a) = g(a)")
	assert.False(t, other.MayRead(HeadGoalOf(goal, nil)), "and the skeleton says so first")
}

// The rigid head is the skeleton's first level, read once off a stated
// conclusion's matrix: whatever the skeleton keeps, the head keeps, a
// wild head keeps everything, and the head alone decides nothing
// below the top — so an index keyed by it hands a scan the stated
// forms at the goal's head and the wild ones, the ones the skeleton
// then reads on.
func TestReadHead_RigidHeadIsTheSkeletonsFirstLevel(t *testing.T) {
	ind := TypeInd
	f := ext.Const(core.MakeConstMeta("f", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	g := ext.Const(core.MakeConstMeta("g", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	x, y := ext.Var("x", ind), ext.Var("y", ind)
	q := ext.Var("q", core.MakeFun(ind, core.TypeBool()))
	target := f.Apply(x).Eq(g.Apply(y))
	equation := RigidHead{Const: utils.EqStr, Args: 2}

	assert.Equal(t, equation, RigidHeadOf(target))
	assert.Equal(t, []RigidHead{equation}, StatedHeadOf(prop.MakeProp(ext.ForAll(x)(g.Apply(x).Eq(x).Imply(ext.ForAll(y)(q.Apply(y).Imply(f.Apply(y).Eq(g.Apply(x)))))))).Rigids(),
		"read under the guarded ∀s and the antecedents")
	assert.Equal(t, []RigidHead{{}}, StatedHeadOf(prop.MakeProp(x.Eq(y).Imply(q.Apply(x)))).Rigids(), "a variable at the top is wild")
	assert.True(t, RigidHead{}.Wild())
	assert.False(t, equation.Wild())
	_, args := ext.MatchesApply(ext.ForAll(x)(f.Apply(x).Eq(x)))
	lambda := args[0]
	assert.Equal(t, RigidHead{Abs: true}, RigidHeadOf(lambda), "∀'s argument is an abstraction")

	assert.True(t, RigidHead{}.MayMatch(target))
	assert.True(t, RigidHead{}.MayMatch(lambda))
	assert.True(t, equation.MayMatch(target))
	assert.False(t, equation.MayMatch(q.Apply(x)), "another constant at the top")
	assert.False(t, equation.MayMatch(lambda))
	assert.False(t, RigidHead{Const: "f", Args: 2}.MayMatch(f.Apply(x)), "the same constant at another arity")
	assert.True(t, RigidHead{Abs: true}.MayMatch(lambda))
	assert.False(t, RigidHead{Abs: true}.MayMatch(target))

	// The head is a necessary condition of the skeleton's verdict, not
	// the verdict: `g(y) = g(x)` is declined by its sides, at the head
	// every equation carries.
	stated := g.Apply(y).Eq(g.Apply(x))
	assert.False(t, skeletonMayMatch(stated, target))
	assert.True(t, RigidHeadOf(stated).MayMatch(target))
	for _, kept := range []core.Term{f.Apply(y).Eq(g.Apply(x)), x.Eq(g.Apply(x)), x.Eq(y).Imply(q.Apply(x))} {
		require.True(t, skeletonMayMatch(conclusionMatrix(kept), target))
		assert.True(t, RigidHeadOf(conclusionMatrix(kept)).MayMatch(target), ext.PrintTerm(kept))
	}
}

// The plan matches an equation goal the other way round too
// (matchHeadSpelling's flip), so the pre-read tries the goal's sides
// crosswise where they differ: `f(x) = g(x)` reads at `g(a) = f(a)`,
// and at a goal whose sides are one term there is no other way round.
func TestReadHead_PreReadFlipsAnEquationGoal(t *testing.T) {
	ind := TypeInd
	f := ext.Const(core.MakeConstMeta("f", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	g := ext.Const(core.MakeConstMeta("g", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	a, x := ext.Var("a", ind), ext.Var("x", ind)
	law := StatedHeadOf(prop.MakeProp(ext.ForAll(x)(f.Apply(x).Eq(g.Apply(x)))))

	flipped := HeadGoalOf(prop.MakeProp(g.Apply(a).Eq(f.Apply(a))), nil)
	require.True(t, law.MayRead(flipped))
	reading, ok := law.Read(flipped)
	require.True(t, ok, "read the other way round")
	require.Len(t, reading.Witnesses, 1)
	assert.Equal(t, "a", ext.PrintTerm(reading.Witnesses[0].Witness))

	same := HeadGoalOf(prop.MakeProp(f.Apply(a).Eq(f.Apply(a))), nil)
	assert.False(t, StatedHeadOf(prop.MakeProp(ext.ForAll(x)(g.Apply(x).Eq(f.Apply(x))))).MayRead(same), "one term on both sides: nothing to flip")
	assert.False(t, law.MayRead(HeadGoalOf(prop.MakeProp(g.Apply(a).Eq(g.Apply(a))), nil)))
}

// The plan reads a conclusion whole, and also conjunct by conjunct
// where it is a conjunction, and as either Horn clause where it is an
// ⇔ — the goal matched against one side, the other joining the
// antecedents — and at each conjunct of a side that is a conjunction.
// The pre-read follows every reading, and the head is keyed under each
// reading's rigid head, the matrix's first.
func TestReadHead_PreReadFollowsTheConjunctAndHornReadings(t *testing.T) {
	ind := TypeInd
	f := ext.Const(core.MakeConstMeta("f", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	g := ext.Const(core.MakeConstMeta("g", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	h := ext.Const(core.MakeConstMeta("h", core.MakeFun(ind, core.TypeBool())), core.MakeFun(ind, core.TypeBool()))
	a, x := ext.Var("a", ind), ext.Var("x", ind)
	equation := RigidHead{Const: utils.EqStr, Args: 2}
	atH := HeadGoalOf(prop.MakeProp(h.Apply(a)), nil)
	atF := HeadGoalOf(prop.MakeProp(f.Apply(a).Eq(a)), nil)
	atG := HeadGoalOf(prop.MakeProp(g.Apply(a).Eq(a)), nil)

	// `∀x. f(x) = x ⇔ h(x)`: at h(a) the right side reads with the left
	// a premise; at f(a) = a the left side reads with the right one.
	iff := StatedHeadOf(prop.MakeProp(ext.ForAll(x)(f.Apply(x).Eq(x).Eq(h.Apply(x)))))
	assert.Equal(t, []RigidHead{equation, {Const: "h", Args: 1}}, iff.Rigids(), "the ⇔ is an equation at bool; then the sides, once each")
	require.True(t, iff.MayRead(atH))
	reading, ok := iff.Read(atH)
	require.True(t, ok)
	assert.Equal(t, "a", ext.PrintTerm(reading.Witnesses[0].Witness))
	require.Len(t, reading.Premises, 1)
	assert.Equal(t, "f(a) = a", ext.PrintTerm(reading.Premises[0].Term))
	require.True(t, iff.MayRead(atF))
	reading, ok = iff.Read(atF)
	require.True(t, ok)
	assert.Equal(t, "h(a)", ext.PrintTerm(reading.Premises[0].Term))
	assert.False(t, iff.MayRead(atG), "neither side is g(x) = x")

	// `∀x. h(x) ∧ f(x) = x`: either conjunct reads at its goal.
	both := StatedHeadOf(prop.MakeProp(ext.ForAll(x)(h.Apply(x).And(f.Apply(x).Eq(x)))))
	assert.Equal(t, []RigidHead{{Const: utils.AndStr, Args: 2}, {Const: "h", Args: 1}, equation}, both.Rigids())
	require.True(t, both.MayRead(atH))
	_, ok = both.Read(atH)
	assert.True(t, ok)
	require.True(t, both.MayRead(atF))
	_, ok = both.Read(atF)
	assert.True(t, ok)
	assert.False(t, both.MayRead(atG), "no conjunct is g(x) = x, either way round")
	_, ok = both.Read(atG)
	assert.False(t, ok)

	// `∀x. h(x) ⇔ f(x) = x ∧ g(x) = x`: at f(a) = a the right side's
	// first conjunct reads with the left side a premise.
	sides := StatedHeadOf(prop.MakeProp(ext.ForAll(x)(h.Apply(x).Eq(f.Apply(x).Eq(x).And(g.Apply(x).Eq(x))))))
	assert.Equal(t, []RigidHead{equation, {Const: utils.AndStr, Args: 2}, {Const: "h", Args: 1}}, sides.Rigids(),
		"the ⇔, its sides, then the right side's conjuncts — equations, keyed once")
	require.True(t, sides.MayRead(atF))
	reading, ok = sides.Read(atF)
	require.True(t, ok)
	assert.Equal(t, "h(a)", ext.PrintTerm(reading.Premises[0].Term))
	require.True(t, sides.MayRead(atG))
	_, ok = sides.Read(atG)
	assert.True(t, ok, "the second conjunct alike")
	k := ext.Const(core.MakeConstMeta("k", core.MakeFun(ind, ind)), core.MakeFun(ind, ind))
	assert.False(t, sides.MayRead(HeadGoalOf(prop.MakeProp(k.Apply(a).Eq(a)), nil)), "no conjunct of either side is k(x) = x")
}
