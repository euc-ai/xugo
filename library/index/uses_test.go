package index

import (
	"slices"
	"testing"

	"github.com/stretchr/testify/require"
)

// A proof that opens a constant stands on its definition: the member is
// among the definition's dependents, the definition among its deps, and
// the index says which of its deps it opens.
func TestAnUnfoldIsADependency(t *testing.T) {
	c := load(t)
	user, ok := c.Resolve("int_construction.GreaterEqIffLessEq")
	require.True(t, ok)
	for _, name := range []string{"int_construction.IntGeDef", "int_construction.IntLeDef", "real_order_ring.RealGeDef"} {
		definition, ok := c.Resolve(name)
		require.True(t, ok, name)
		require.Contains(t, user.Deps, definition.ID, "%s opens %s", user.ID, name)
		require.Contains(t, user.Unfolds, definition.ID)
		require.Contains(t, definition.Dependents, user.ID)
	}
	require.Subset(t, user.Deps, user.Unfolds, "what a member opens is among what it stands on")

	view, err := c.DefinitionView("int_ge")
	require.NoError(t, err)
	require.Contains(t, view.UnfoldedBy, user.ID)
	require.Subset(t, view.CitedBy, view.UnfoldedBy, "a member that opens the constant stands on its definition")
}

// A definition is still stood on where a statement spells its constant
// and the proof never touches it: such a member is no dependent, and
// the answer names the constant its statement spells.
func TestUsedByReadsStatements(t *testing.T) {
	c := load(t)
	m, ok := c.Resolve("polynomial_system_descent.PolynomialSystemDef")
	require.True(t, ok)
	x, ok := c.Resolve("polynomial_system_descent.SolutionDescent")
	require.True(t, ok)
	require.NotContains(t, m.Dependents, x.ID, "%s depends on %s, so it is a dependent and no use", x.ID, m.ID)
	uses := c.UsedBy(m)
	at := slices.IndexFunc(uses, func(u Use) bool { return u.Member == x.ID })
	require.GreaterOrEqual(t, at, 0, "%s uses %s", x.ID, m.ID)
	require.Equal(t, []string{"polynomial_system_solution"}, uses[at].Statement)
}

// What UsedBy lists is what it says: a member that depends on the
// definition is not among its uses, a constant under Statement is one
// the definition mints and the member's statement spells, and a member
// that mints nothing is used by none.
func TestUsedByIsDisjointFromDependents(t *testing.T) {
	c := load(t)
	minted := map[string][]string{}
	for _, d := range c.Definitions {
		minted[d.Member] = append(minted[d.Member], d.Const)
	}
	checked := 0
	for _, m := range c.Members {
		uses := c.UsedBy(m)
		if len(minted[m.ID]) == 0 {
			require.Nil(t, uses, m.ID)
			continue
		}
		for _, u := range uses {
			require.NotEqual(t, m.ID, u.Member)
			require.NotContains(t, m.Dependents, u.Member, "%s: a dependent is listed as a use", m.ID)
			require.NotEmpty(t, u.Statement, "%s: %s uses nothing", m.ID, u.Member)
			for _, name := range u.Statement {
				require.Contains(t, minted[m.ID], name)
				require.Contains(t, c.byID[u.Member].Constants, name)
			}
			checked++
		}
	}
	require.Positive(t, checked)
}

// A Dependents answer carries the uses beside the dependency levels,
// and a Deps answer none.
func TestNeighborsListsUsesWithDependents(t *testing.T) {
	c := load(t)
	m, ok := c.Resolve("polynomial_system_descent.PolynomialSystemDef")
	require.True(t, ok)
	dependents, err := c.Neighbors(m.ID, Dependents, 1)
	require.NoError(t, err)
	uses := c.UsedBy(m)
	require.NotEmpty(t, uses)
	require.Equal(t, uses, dependents.UsedBy)
	deps, err := c.Neighbors(m.ID, Deps, 1)
	require.NoError(t, err)
	require.Empty(t, deps.UsedBy)
}
