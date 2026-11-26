package dsl

// Two operands of one connective are unified across a constant's
// occurrence-local stand-ins (reconcileFreshLetters), and a pinned
// nullary is re-read at the domain an application read through its
// meta has fixed for it (rereadPinnedAtom) — the two readings the free
// group chapter found missing: `free_one * x` was refused as two
// arithmetic domains, `free_one = ⁅nil⁆` needed a ⟨⟩ tie, and
// `cons(x, nil)` at a letter type was refused against the vocabulary's
// pin.

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestBareNullaryBesideDeclaredOperator: `e * x` where `*` is a
// chapter's declared operator on a polymorphic carrier and `e` a bare
// polymorphic nullary — the nullary's stand-in reads at the partner's
// instance before the operator is dispatched.
func TestBareNullaryBesideDeclaredOperator(t *testing.T) {
	A := core.MakeVarType("A")
	T := ext.MakeType("grp", A)
	mulMeta := core.MakeConstMeta("fmul", core.MakeFun(T, core.MakeFun(T, T)))
	eMeta := core.MakeConstMeta("e", T)
	scope := &ParseScope{
		ConstMetas:         map[string]core.ConstTermMeta{"fmul": mulMeta, "e": eMeta},
		Vars:               map[string]core.HolType{"x": T},
		Syntax:             testSyntax{"fmul": {Operator: &Operator{Symbol: "*", Args: []int{0, 1}}}},
		FreshenMetaLetters: true,
		StrictResolution:   true,
	}
	res := ParsePropTextInScope("e * x = x", scope)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	mul := findConstOfName(res.Prop.Conclusion(), "fmul")
	require.False(t, mul.IsZero(), "the operator lowers to the declared constant: %s", ext.FormatTerm(res.Prop.Conclusion(), false))
	e := findConstOfName(res.Prop.Conclusion(), "e")
	require.False(t, e.IsZero())
	assert.True(t, e.Type().Equals(T), "the nullary reads at the partner's instance, got %s", ext.FormatType(e.Type()))
}

// TestRigidSideUnifiesPartnersFreshLetter: a definiendum typed at the
// author's letter beside an application whose letter is a stand-in —
// `one = cls(nil)` with `one : grp(A)` declared and `cls : list(A) → grp(A)`
// freshened — reads the right side at A; before, the define door
// refused "equality type mismatch" until the text tied the letter.
func TestRigidSideUnifiesPartnersFreshLetter(t *testing.T) {
	A := core.MakeVarType("A")
	T := ext.MakeType("grp", A)
	listA := ext.MakeType("list", A)
	clsMeta := core.MakeConstMeta("cls", core.MakeFun(listA, T))
	nilMeta := core.MakeConstMeta("nil", listA)
	scope := &ParseScope{
		ConstMetas:         map[string]core.ConstTermMeta{"cls": clsMeta, "nil": nilMeta},
		Vars:               map[string]core.HolType{"one": T},
		FreshenMetaLetters: true,
		StrictResolution:   true,
	}
	res := ParsePropTextInScope("one = cls(nil)", scope)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	cls := findConstOfName(res.Prop.Conclusion(), "cls")
	require.False(t, cls.IsZero())
	assert.True(t, cls.Type().Equals(core.MakeFun(listA, T)), "the application reads at the rigid side's letter, got %s", ext.FormatType(cls.Type()))
	assert.False(t, ext.PropHasTypeVars(res.Prop) && hasFreshLetter(res.Prop), "no stand-in survives: %s", ext.FormatTerm(res.Prop.Conclusion(), false))

	// The free group's own shape: the class map is over lists of
	// LETTERS, `wcls : list(prod(A, bool)) → grp(A)`, and the chapter's
	// vocabulary pins nil at list(A). No instance of the pin is a list
	// of letters, so nil is re-read through its meta at the domain, and
	// the equality then reads the stand-in at the rigid side's A.
	letters := ext.MakeType("list", ext.MakeType("prod", A, core.TypeBool()))
	wclsMeta := core.MakeConstMeta("wcls", core.MakeFun(letters, T))
	pinned := &ParseScope{
		Consts:             map[string]core.ConstTerm{"nil": core.MakeConstTerm(nilMeta, nilMeta.AbsType())},
		ConstMetas:         map[string]core.ConstTermMeta{"wcls": wclsMeta, "nil": nilMeta},
		Vars:               map[string]core.HolType{"one": T},
		FreshenMetaLetters: true,
		StrictResolution:   true,
	}
	res = ParsePropTextInScope("one = wcls(nil)", pinned)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	nilC := findConstOfName(res.Prop.Conclusion(), "nil")
	require.False(t, nilC.IsZero())
	assert.True(t, nilC.Type().Equals(letters), "the pinned nil is the empty word here, got %s", ext.FormatType(nilC.Type()))
	assert.False(t, hasFreshLetter(res.Prop), "no stand-in survives: %s", ext.FormatTerm(res.Prop.Conclusion(), false))
}

// TestPinnedNullaryUnderConsAtLetterType: a chapter pins `nil` at
// list(A) (its vocabulary's Term row) and writes `cons(x, nil)` with
// `x : prod(A, bool)`. Read through cons's meta, x fixes the domain of
// the second argument at list(prod(A, bool)), and the pinned nil is
// re-read there; this was refused "argument type list(A) does not match
// domain list(prod(A, bool))" while the session, which pins nothing,
// accepted the same text. Both with cons a meta alone and with cons
// PINNED at its generic instance too (the chapter's own shape: the
// pinned reading fails on x and the meta reading takes over).
func TestPinnedNullaryUnderConsAtLetterType(t *testing.T) {
	A := core.MakeVarType("A")
	listA := ext.MakeType("list", A)
	letter := ext.MakeType("prod", A, core.TypeBool())
	nilMeta := core.MakeConstMeta("nil", listA)
	consMeta := core.MakeConstMeta("cons", core.MakeFun(A, core.MakeFun(listA, listA)))
	for name, consPinned := range map[string]bool{"cons a meta": false, "cons pinned": true} {
		scope := &ParseScope{
			Consts:             map[string]core.ConstTerm{"nil": core.MakeConstTerm(nilMeta, nilMeta.AbsType())},
			ConstMetas:         map[string]core.ConstTermMeta{"nil": nilMeta, "cons": consMeta},
			Vars:               map[string]core.HolType{"x": letter},
			FreshenMetaLetters: true,
			StrictResolution:   true,
		}
		if consPinned {
			scope.Consts["cons"] = core.MakeConstTerm(consMeta, consMeta.AbsType())
		}
		res := ParsePropTextInScope("cons(x, nil) = cons(x, nil)", scope)
		require.Empty(t, res.Errors, "%s: unexpected errors: %v", name, res.Errors)
		nilC := findConstOfName(res.Prop.Conclusion(), "nil")
		require.False(t, nilC.IsZero(), name)
		assert.True(t, nilC.Type().Equals(ext.MakeType("list", letter)),
			"%s: nil reads at the letter type the first argument fixed, got %s", name, ext.FormatType(nilC.Type()))
	}
}

// TestPinnedHeadsGenericDomainLeavesThePin is the boundary the re-read
// must not cross, measured twice on sets/num_segment: `card` is pinned
// at its generic instance `(A → bool) → num` and `∅` at `num → bool`
// (the chapter's element type). `card(∅) = 0` reads at num — the pinned
// reading of card disagrees with the pin of ∅ and gives way to the meta
// reading, whose stand-in the pin instantiates. Re-reading ∅ at card's
// generic `A → bool` instead left the claim at the abstract letter while
// the counting premise installed at num, and two members stopped
// replaying.
func TestPinnedHeadsGenericDomainLeavesThePin(t *testing.T) {
	A := core.MakeVarType("A")
	setOfA := core.MakeFun(A, core.TypeBool())
	setOfNum := core.MakeFun(NumType, core.TypeBool())
	emptyMeta := core.MakeConstMeta("empty_set", setOfA)
	cardMeta := core.MakeConstMeta("card", core.MakeFun(setOfA, NumType))
	scope := &ParseScope{
		Consts: map[string]core.ConstTerm{
			"empty_set": core.MakeConstTerm(emptyMeta, setOfNum),          // the chapter's pin
			"card":      core.MakeConstTerm(cardMeta, cardMeta.AbsType()), // pinned generic
		},
		ConstMetas:         map[string]core.ConstTermMeta{"empty_set": emptyMeta, "card": cardMeta},
		FreshenMetaLetters: true,
		StrictResolution:   true,
	}
	res := ParsePropTextInScope("card(empty_set) = 0", scope)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	empty := findConstOfName(res.Prop.Conclusion(), "empty_set")
	require.False(t, empty.IsZero())
	assert.True(t, empty.Type().Equals(setOfNum), "the pin stands under a pinned head's generic domain, got %s", ext.FormatType(empty.Type()))
	card := findConstOfName(res.Prop.Conclusion(), "card")
	require.False(t, card.IsZero())
	assert.True(t, card.Type().Equals(core.MakeFun(setOfNum, NumType)), "and card reads at the pin's instance, got %s", ext.FormatType(card.Type()))
}

// hasFreshLetter reports whether any constant in p still carries an
// occurrence-local stand-in.
func hasFreshLetter(p core.Prop) bool { return len(UnpinnedLetters(p)) > 0 }
