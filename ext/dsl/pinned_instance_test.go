package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestParsePinnedNullaryConstAtExpectedInstance: a nullary polymorphic
// constant PINNED in the scope at its abstract instance (a chapter's
// `Term("nil")` row — here `empty_set : A → bool`) is read at the instance a
// monomorphic head's domain expects (`f : (num → bool) → num`), the way
// the session's own elaborator reads it: `f(empty_set) = 0` elaborates with
// empty_set at `num → bool`, instead of refusing "argument type A → bool
// does not match domain num → bool" (the registration-time panic
// `list_sum(nil) = 0` would raise).
func TestParsePinnedNullaryConstAtExpectedInstance(t *testing.T) {
	typeA := core.MakeVarType("A")
	setOfA := core.MakeFun(typeA, core.TypeBool())
	setOfNum := core.MakeFun(NumType, core.TypeBool())
	emptyMeta := core.MakeConstMeta("empty_set", setOfA)
	fMeta := core.MakeConstMeta("f", core.MakeFun(setOfNum, NumType))
	scope := &ParseScope{
		Consts: map[string]core.ConstTerm{
			"empty_set": core.MakeConstTerm(emptyMeta, emptyMeta.AbsType()), // pinned at A
			"f":         core.MakeConstTerm(fMeta, fMeta.AbsType()),
		},
		ConstMetas: map[string]core.ConstTermMeta{
			"empty_set": emptyMeta,
			"f":         fMeta,
		},
	}
	res := ParsePropTextInScope("f(empty_set) = 0", scope)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	empty := findConstOfName(res.Prop.Conclusion(), "empty_set")
	require.False(t, empty.IsZero(), "expected empty_set const, got %s", ext.FormatTerm(res.Prop.Conclusion(), false))
	assert.True(t, empty.Type().Equals(setOfNum), "empty_set read at the domain's instance, got %s", ext.FormatType(empty.Type()))

	// The BOUNDARY, and it is load-bearing: an expectation written in a
	// type VARIABLE does NOT re-read the pin. A pin is a chapter saying
	// the constant means one instance here, and a premise installed at
	// the pin must still meet a goal built from the same text; re-reading
	// at a letter splits them (measured: it broke
	// `num_segment.HasSizeBelowStrict` and `num_segment.Card`, whose
	// `card(∅)` premise installs at num). A statement that wants the
	// constant at another letter annotates it.
	typeB := core.MakeVarType("B")
	setOfB := core.MakeFun(typeB, core.TypeBool())
	gMeta := core.MakeConstMeta("g", core.MakeFun(setOfB, core.TypeBool()))
	scope.Consts["g"] = core.MakeConstTerm(gMeta, gMeta.AbsType())
	scope.ConstMetas["g"] = gMeta
	res = ParsePropTextInScope("g(empty_set)", scope)
	if len(res.Errors) == 0 {
		empty = findConstOfName(res.Prop.Conclusion(), "empty_set")
		require.False(t, empty.IsZero())
		assert.True(t, empty.Type().Equals(setOfA),
			"a type-variable expectation must leave the pin alone, got %s", ext.FormatType(empty.Type()))
	}

	// The pin still answers where nothing expects another instance.
	res = ParsePropTextInScope("empty_set = empty_set", scope)
	require.Empty(t, res.Errors, "unexpected errors: %v", res.Errors)
	empty = findConstOfName(res.Prop.Conclusion(), "empty_set")
	require.False(t, empty.IsZero())
	assert.True(t, empty.Type().Equals(setOfA), "the pinned instance where nothing pins another, got %s", ext.FormatType(empty.Type()))
}
