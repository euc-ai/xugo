package proof

// witness_order_test.go — the reorder's rename lane, OBSERVED. The
// name-map fast path and the end-to-end permutation are covered by
// TestScriptAtTypes_WitnessOrderFollowsStatedForm; these tests pin the
// lanes around it: a prefix binder Normalize renamed is resolved by
// type-unique elimination (correct even when the prefix also
// reordered — the Fibres-cites-Restrict incident shape), an ambiguous
// or minted binder panics instead of falling back to positional
// silence, and the deliberate pass-through lanes (clause-pack dup
// names, partial grounding) stay positional.

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

// reorderFixture builds the pieces every case here shares: stated
// binders a:ind, P:(ind→bool), b:ind — reading order (a, P, b).
func reorderFixture() (ref Prop, wa, wp, wb Term) {
	pTy := MakeFun(TypeInd, TypeBool)
	a, P, b := Var("a", TypeInd), Var("P", pTy), Var("b", TypeInd)
	ref = core.TestThm(ext.ForAll(a)(ext.ForAll(P)(ext.ForAll(b)(P.Apply(a)))))
	return ref, Var("wa", TypeInd), Var("wp", pTy), Var("wb", TypeInd)
}

func expectReorderPanic(t *testing.T, wants ...string) {
	t.Helper()
	r := recover()
	if !assert.NotNil(t, r, "expected the reorder to panic") {
		return
	}
	msg, _ := r.(string)
	for _, w := range wants {
		assert.Contains(t, msg, w)
	}
}

// A renamed AND transposed prefix binder is resolved by elimination:
// stated (a, P, b), install (Q, a, b) with Q the rename of P. The
// stated-order tuple must land P's witness on Q — under the old
// fallthrough this exact shape read positionally and produced a
// type-correct wrong instance.
func TestReorderWitnesses_RenamedBinderResolvedByElimination(t *testing.T) {
	ref, wa, wp, wb := reorderFixture()
	pTy := MakeFun(TypeInd, TypeBool)
	Q, a, b := Var("Q", pTy), Var("a", TypeInd), Var("b", TypeInd)
	installed := ext.ForAll(Q)(ext.ForAll(a)(ext.ForAll(b)(Q.Apply(a))))

	out := reorderWitnessesToInstall(ref, installed, []Term{wa, wp, wb})
	if assert.Len(t, out, 3) {
		assert.True(t, any(wp) == any(out[0]), "the renamed slot Q must take P's witness")
		assert.True(t, any(wa) == any(out[1]))
		assert.True(t, any(wb) == any(out[2]))
	}
}

// A minted binder — no unclaimed stated binder has its type — must
// panic rather than take a stated-order witness positionally.
func TestReorderWitnesses_MintedBinderPanics(t *testing.T) {
	ref, wa, wp, wb := reorderFixture()
	a, P := Var("a", TypeInd), Var("P", MakeFun(TypeInd, TypeBool))
	minted := Var("mint", MakeFun(TypeBool, TypeBool))
	installed := ext.ForAll(a)(ext.ForAll(P)(ext.ForAll(minted)(P.Apply(a))))

	defer expectReorderPanic(t, "mint", "no unclaimed stated binder has its type")
	reorderWitnessesToInstall(ref, installed, []Term{wa, wp, wb})
}

// Two unclaimed stated binders of the renamed slot's type admit two
// maps — the reorder must refuse, naming the candidates.
func TestReorderWitnesses_AmbiguousCandidatesPanic(t *testing.T) {
	pTy := MakeFun(TypeInd, TypeBool)
	a, P, R := Var("a", TypeInd), Var("P", pTy), Var("R", pTy)
	ref := core.TestThm(ext.ForAll(a)(ext.ForAll(P)(ext.ForAll(R)(P.Apply(a)))))
	// Neither P nor R survives into the prefix: Q could be either.
	Q, b := Var("Q", pTy), Var("b", TypeInd)
	installed := ext.ForAll(a)(ext.ForAll(Q)(ext.ForAll(b)(Q.Apply(a))))

	defer expectReorderPanic(t, "[P R]", "all have its type")
	reorderWitnessesToInstall(ref, installed,
		[]Term{Var("w1", TypeInd), Var("w2", pTy), Var("w3", pTy)})
}

// Two renamed slots sharing one type cannot be ordered by any
// elimination — refuse.
func TestReorderWitnesses_TwoRenamedSlotsShareTypePanic(t *testing.T) {
	pTy := MakeFun(TypeInd, TypeBool)
	a, P, R := Var("a", TypeInd), Var("P", pTy), Var("R", pTy)
	ref := core.TestThm(ext.ForAll(a)(ext.ForAll(P)(ext.ForAll(R)(P.Apply(a)))))
	Q1, Q2 := Var("Q1", pTy), Var("Q2", pTy)
	installed := ext.ForAll(a)(ext.ForAll(Q1)(ext.ForAll(Q2)(Q1.Apply(a))))

	defer expectReorderPanic(t, "shares its type")
	reorderWitnessesToInstall(ref, installed,
		[]Term{Var("w1", TypeInd), Var("w2", pTy), Var("w3", pTy)})
}

// A reference that binds a prefix name twice is the clause-pack lane:
// positional pass-through, unchanged (TestWitnessOrderCensus tracks
// the sites).
func TestReorderWitnesses_DupNameLaneStaysPositional(t *testing.T) {
	s, t2 := Var("s", TypeInd), Var("t", TypeInd)
	inner := ext.ForAll(s)(ext.WrapTerm(s.Core()).Eq(s))
	ref := core.TestThm(ext.ForAll(s)(ext.ForAll(t2)(ext.WrapTerm(s.Core()).Eq(t2))), inner)
	installed := ext.ForAll(s)(ext.ForAll(t2)(ext.WrapTerm(s.Core()).Eq(t2)))

	w1, w2 := Var("w1", TypeInd), Var("w2", TypeInd)
	out := reorderWitnessesToInstall(ref, installed, []Term{w1, w2})
	if assert.Len(t, out, 2) {
		assert.True(t, any(w1) == any(out[0]))
		assert.True(t, any(w2) == any(out[1]))
	}
}

// A PARTIAL tuple never enters the rename lane: shorter than the
// prefix, it grounds the LEADING binders even when a binder is renamed
// — positionally where that reading is well-typed, and by the one
// type-consistent order where it is not (the prenex-habit tuple on a
// stated principle; see the header). Here the positional reading puts
// the individual wa on the predicate binder Q, so the types settle it.
func TestReorderWitnesses_PartialGroundingUnchanged(t *testing.T) {
	ref, wa, wp, _ := reorderFixture()
	pTy := MakeFun(TypeInd, TypeBool)
	Q, a, b := Var("Q", pTy), Var("a", TypeInd), Var("b", TypeInd)
	installed := ext.ForAll(Q)(ext.ForAll(a)(ext.ForAll(b)(Q.Apply(a))))

	out := reorderWitnessesToInstall(ref, installed, []Term{wa, wp})
	if assert.Len(t, out, 2) {
		assert.True(t, any(wp) == any(out[0]), "the predicate grounds Q")
		assert.True(t, any(wa) == any(out[1]), "the individual grounds a")
	}
	// Well-typed positionally: untouched.
	out = reorderWitnessesToInstall(ref, installed, []Term{wp, wa})
	if assert.Len(t, out, 2) {
		assert.True(t, any(wp) == any(out[0]))
		assert.True(t, any(wa) == any(out[1]))
	}
}

// The panic message must carry both orders — the reader's whole
// diagnostic is that one pair of lines.
func TestReorderWitnesses_PanicNamesBothOrders(t *testing.T) {
	ref, wa, wp, wb := reorderFixture()
	a, P := Var("a", TypeInd), Var("P", MakeFun(TypeInd, TypeBool))
	minted := Var("mint", MakeFun(TypeBool, TypeBool))
	installed := ext.ForAll(a)(ext.ForAll(P)(ext.ForAll(minted)(P.Apply(a))))

	defer func() {
		r := recover()
		if !assert.NotNil(t, r) {
			return
		}
		msg, _ := r.(string)
		assert.True(t, strings.Contains(msg, "install prefix: (a P mint)"), "install order missing:\n%s", msg)
		assert.True(t, strings.Contains(msg, "reference:"), "reference missing:\n%s", msg)
	}()
	reorderWitnessesToInstall(ref, installed, []Term{wa, wp, wb})
}

// A spine binder whose NAME an antecedent's own binder reuses — the
// monotonicity criterion's shape, `∀f a. (∀x. P(f(x), a)) ⇒ ∀x y.
// Q(f(x), y)`. The statement binds x twice, so x has no slot by name;
// Normalize keeps the inner x existential and renames the spine one.
// The renamed prefix binder is the spine's x: the stated-order tuple
// (f, a, x, y) must land on the install prefix (a, u, y, f).
func TestReorderWitnesses_RenamedSpineBinderSharingAnInnerName(t *testing.T) {
	fTy := MakeFun(TypeInd, TypeInd)
	f, a, x, y := Var("f", fTy), Var("a", TypeInd), Var("x", TypeInd), Var("y", TypeInd)
	P := Var("P", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
	Q := Var("Q", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
	guard := ForAll(x)(P.Apply(f.Apply(x), a))
	ref := core.TestThm(ForAll(f)(ForAll(a)(guard.Imply(ForAll(x)(ForAll(y)(Q.Apply(f.Apply(x), y)))))))

	u := Var("u", TypeInd)
	installed := ForAll(a)(ForAll(u)(ForAll(y)(ForAll(f)(Q.Apply(f.Apply(u), y)))))

	wf, wa, wx, wy := Var("wf", fTy), Var("wa", TypeInd), Var("wx", TypeInd), Var("wy", TypeInd)
	out := reorderWitnessesToInstall(ref, installed, []Term{wf, wa, wx, wy})
	if assert.Len(t, out, 4) {
		assert.True(t, any(wa) == any(out[0]))
		assert.True(t, any(wx) == any(out[1]), "the renamed slot u is the spine's x")
		assert.True(t, any(wy) == any(out[2]))
		assert.True(t, any(wf) == any(out[3]))
	}
}

// The renamed spine binder takes the reading position of ITS OWN binding
// site, not of the name's first binding: in `∀a. (∀x. P(x, a)) ∧ (∃w.
// R(w)) ⇒ ∀x. Q(x, w')` the antecedent's ∃w is hoisted into the prefix
// and is read BEFORE the spine's x, though x's first binding precedes
// w. Read at the first binding's position the tuple (a, w, x) would
// ground u with w's witness — the same type, so silently.
func TestReorderWitnesses_RenamedSpineBinderKeepsItsOwnPosition(t *testing.T) {
	a, x, w := Var("a", TypeInd), Var("x", TypeInd), Var("w", TypeInd)
	P := Var("P", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
	R := Var("R", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
	guards := ForAll(x)(P.Apply(x, a)).And(Exists(w)(R.Apply(w)))
	ref := core.TestThm(ForAll(a)(guards.Imply(ForAll(x)(Q.Apply(x, a)))))

	u := Var("u", TypeInd)
	installed := ForAll(u)(ForAll(a)(ForAll(w)(Q.Apply(u, a))))

	wa, ww, wx := Var("wa", TypeInd), Var("ww", TypeInd), Var("wx", TypeInd)
	out := reorderWitnessesToInstall(ref, installed, []Term{wa, ww, wx})
	if assert.Len(t, out, 3) {
		assert.True(t, any(wx) == any(out[0]), "u is the spine's x, read last")
		assert.True(t, any(wa) == any(out[1]))
		assert.True(t, any(ww) == any(out[2]))
	}
}

// A name bound more than once only INSIDE the statement — never on its
// spine — still has no slot: the renamed prefix binder is minted, and
// the cite refuses.
func TestReorderWitnesses_InnerOnlyDupNameStaysOutOfThePool(t *testing.T) {
	a, x := Var("a", TypeInd), Var("x", TypeInd)
	P := Var("P", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	guards := ForAll(x)(P.Apply(x, a)).And(ForAll(x)(P.Apply(a, x)))
	b := Var("b", MakeFun(TypeInd, TypeBool))
	ref := core.TestThm(ForAll(a)(ForAll(b)(guards.Imply(Q.Apply(a)))))

	u := Var("u", TypeInd)
	installed := ForAll(a)(ForAll(b)(ForAll(u)(Q.Apply(a))))

	defer expectReorderPanic(t, "u", "no unclaimed stated binder has its type")
	reorderWitnessesToInstall(ref, installed,
		[]Term{Var("wa", TypeInd), Var("wb", MakeFun(TypeInd, TypeBool)), Var("wu", TypeInd)})
}

// TestWitnessOrderNote: a grounding that fails says which lane read its
// tuple where that lane is not the name map — a reference binding a
// prefix name twice (read positionally), a single witness (the first
// prefix binder) — and says nothing where the tuple was mapped by name.
func TestWitnessOrderNote(t *testing.T) {
	s, t2 := Var("s", TypeInd), Var("t", TypeInd)
	inner := ext.ForAll(s)(ext.WrapTerm(s.Core()).Eq(s))
	twice := core.TestThm(ext.ForAll(s)(ext.ForAll(t2)(ext.WrapTerm(s.Core()).Eq(t2))), inner)
	installed := ext.ForAll(s)(ext.ForAll(t2)(ext.WrapTerm(s.Core()).Eq(t2)))
	w1, w2 := Var("w1", TypeInd), Var("w2", TypeInd)

	note := witnessOrderNote(twice, installed, []Term{w1, w2})
	assert.Contains(t, note, "binds s twice")
	assert.Contains(t, note, "positionally against the install prefix (s, t)")
	assert.Contains(t, note, "do not settle a permutation", "two binders of one type")

	assert.Contains(t, witnessOrderNote(twice, installed, []Term{w1}), "first binder, s, as written")

	ref, wa, wp, _ := reorderFixture()
	pTy := MakeFun(TypeInd, TypeBool)
	Q, a := Var("Q", pTy), Var("a", TypeInd)
	byName := ext.ForAll(Q)(ext.ForAll(a)(Q.Apply(a)))
	assert.Empty(t, witnessOrderNote(ref, byName, []Term{wa, wp}), "a name-mapped tuple needs no note")
}
