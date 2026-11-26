package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// A claim is read by the rule its statement is read by: under the
// script's coercion domain, and under the script's guard on an `&`
// nothing anchors — whether or not the block has minted a name. Before
// the alias scope carried them, a claim in a block with one `Fix` read
// `&m = &m` at ℝ in a chapter that had declared ℤ, and a chapter that
// declared nothing read it at ℝ without a word at either door.
func TestClaimDoor_ReadsTheScriptsCoercionDomain(t *testing.T) {
	script := func(domain core.HolType) *Script {
		s := &Script{}
		s.ParseScope.Vars = map[string]core.HolType{"m": ext.NumType}
		s.ParseScope.StrictResolution = true
		if domain != nil {
			s.CoerceDomain(domain)
		}
		return s
	}
	alias := map[string]core.VarTerm{"n": core.Var("n₀", ext.NumType)}
	read := func(scope *dsl.ParseScope) (string, string) {
		res := dsl.ParsePropTextInScope("&m = &m", scope)
		if len(res.Errors) > 0 {
			return "", res.Errors[0].Message
		}
		return ext.PrintTerm(res.Prop.Conclusion()), ""
	}

	declared := script(IntDomain)
	plain, _ := declared.parseScopeWithAliases(nil)
	aliased, _ := declared.parseScopeWithAliases(alias)
	for name, scope := range map[string]*dsl.ParseScope{"no alias": plain, "one alias": aliased} {
		text, refusal := read(scope)
		require.Empty(t, refusal, name)
		require.Equal(t, "int_of_num(m) = int_of_num(m)", text, name)
		require.False(t, scope.StrictResolution, "%s: the claim door reports an undeclared name itself", name)
	}

	undeclared := script(nil)
	plain, _ = undeclared.parseScopeWithAliases(nil)
	aliased, _ = undeclared.parseScopeWithAliases(alias)
	for name, scope := range map[string]*dsl.ParseScope{"no alias": plain, "one alias": aliased} {
		_, refusal := read(scope)
		require.Contains(t, refusal, "unanchored", name)
	}

	// A script that is no strict door keeps the loose reading.
	loose := &Script{}
	loose.ParseScope.Vars = map[string]core.HolType{"m": ext.NumType}
	scope, _ := loose.parseScopeWithAliases(alias)
	_, refusal := read(scope)
	require.Empty(t, refusal)

	// The override scope of a statement text carries both as well.
	over := declared.parseScopeWithOverrides([]Term{ext.WrapTerm(dsl.RealOfNumMeta.Term())})
	require.True(t, over.CoerceDomain.Equals(IntDomain))
	require.True(t, over.StrictCoercion)
}
