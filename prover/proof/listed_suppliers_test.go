package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// A membership in a set-builder supplies each clause of its condition,
// so the refusal of an unlisted guard names it as the fact that states
// the clause: the hypothesis is no conjunction as written, only in the
// rung's reading.
func TestSupplierOf_MembershipSuppliesItsClauses(t *testing.T) {
	member := parseGuardSupply(t, "s ∈ {e:set(num) | Q(e) ∧ W(e)}")
	require.Len(t, conjuncts(member), 1)
	goal := prop.MakeProp(parseGuardSupply(t, "W(t)"), parseGuardSupply(t, "Q(t)"), member)
	got := supplierOf(readerOf(nil), goal, parseGuardSupply(t, "W(s)"))
	require.NotNil(t, got)
	require.True(t, got.AlphaEquals(member), "supplier: %s", ext.PrintTerm(got))
	require.Nil(t, supplierOf(readerOf(nil), goal, parseGuardSupply(t, "W(t)")))
}
