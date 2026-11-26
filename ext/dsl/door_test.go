package dsl

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
)

// The door's reading of a closed text sets the focus aside: a statement
// that binds its own structure reads the same beside a declared record
// of that structure, where the reading at the focus refuses its symbol
// as bound by two structures — the shape of a session section emitted
// beside the record its theorem's strips declare (engine,
// TestReadAt_AProvedSectionIsTheLaw). A text that names the focus is read
// at the focus.
func TestParsePropTextAtDoor_ClosedTextIsReadClosed(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ, err := ParseTypeText("zz_ops(A)")
	require.NoError(t, err)
	focus := *scope
	focus.Vars = map[string]core.HolType{"T": typ}

	const closed = "∀S:zz_ops(A). ∀x:A. x + x = S.e"
	at := ParsePropTextInScope(closed, &focus)
	require.NotEmpty(t, at.Errors, "read at the focus, the text's + meets T's")
	require.Contains(t, at.Errors[0].Message, "bound by two structures")

	door := ParsePropTextAtDoor(closed, &focus)
	require.Empty(t, door.Errors, "%v", door.Errors)
	alone := ParsePropTextInScope(closed, scope)
	require.Empty(t, alone.Errors)
	require.True(t, door.Prop.AlphaEquals(alone.Prop), "the closed text states what it states with no focus: %v", door.Prop)

	// A text that names the focus's variable is read at the focus.
	named := ParsePropTextAtDoor("∀x:A. x + x = T.e", &focus)
	require.Empty(t, named.Errors, "%v", named.Errors)
	require.Len(t, named.Prop.Conclusion().Frees(nil), 1, "T is the focus's")
	// A text the focus's record alone binds a symbol for is read at the
	// focus: with nothing declared it binds none.
	symbol := ParsePropTextAtDoor("∀x:A. x + x = x + x", &focus)
	require.Empty(t, symbol.Errors, "%v", symbol.Errors)
	require.Len(t, symbol.Prop.Conclusion().Frees(nil), 1, "+ is T's")
}

// The completions the observer hears are the returned reading's, once:
// the closed reading's where it is taken, the focus's where the text
// names something of the focus.
func TestParsePropTextAtDoor_ObserverHearsTheReadingReturned(t *testing.T) {
	scope := implicitTestScope(t)
	var heard []string
	scope.ImplicitCompleted = func(constName, name string, variable bool) {
		heard = append(heard, constName+":"+name)
	}
	typ, err := ParseTypeText("A → A → A")
	require.NoError(t, err)
	scope.Vars = map[string]core.HolType{"mul": typ}

	res := ParsePropTextAtDoor("∀add:(A → A → A). ∀u v:(num → A). vec_add(u, v) = vec_add(v, u)", scope)
	require.Empty(t, res.Errors, "%v", res.Errors)
	require.Len(t, res.Prop.Conclusion().Frees(nil), 0, "read closed")
	require.Equal(t, []string{"vec_add:add", "vec_add:add"}, heard)
}
