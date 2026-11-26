package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// TestDefinitionSimpRules_ByShape pins the one dispatch every define
// door shares: which shapes install their characterizing theorem
// whole, which derive readings, and which install nothing.
func TestDefinitionSimpRules_ByShape(t *testing.T) {
	equation, _ := wfGcdEquation("zz_gcd_rules")
	characterizing := core.NewAxiom(equation.Conclusion())

	t.Run("whole theorem shapes", func(t *testing.T) {
		for _, shape := range []DefinitionShape{
			DefinitionDirect, DefinitionRecursive, DefinitionDataInj, DefinitionDataDistinct,
		} {
			rules, err := DefinitionSimpRules(shape, characterizing)
			require.NoError(t, err, shape)
			require.Len(t, rules, 1, shape)
			require.True(t, rules[0].Rule.AlphaEquals(characterizing), shape)
			require.True(t, any(characterizing) == any(rules[0].Cert), "%s: the rule certifies from the theorem itself", shape)
		}
	})

	t.Run("wf derives the guarded readings", func(t *testing.T) {
		rules, err := DefinitionSimpRules(DefinitionWF, characterizing)
		require.NoError(t, err)
		readings, err := DeriveWFReadings(characterizing)
		require.NoError(t, err)
		require.Len(t, rules, len(readings))
		for i, r := range readings {
			require.True(t, rules[i].Rule.AlphaEquals(r), "reading %d", i)
			require.NotNil(t, rules[i].Cert, "reading %d is promise-backed", i)
		}
	})

	t.Run("principles and specifications install nothing", func(t *testing.T) {
		for _, shape := range []DefinitionShape{
			DefinitionSpec, DefinitionDataInduct, DefinitionDataRecursion,
		} {
			rules, err := DefinitionSimpRules(shape, characterizing)
			require.NoError(t, err, shape)
			require.Empty(t, rules, shape)
		}
	})

	t.Run("not a definition is a fault", func(t *testing.T) {
		_, err := DefinitionSimpRules(NotADefinition, characterizing)
		require.Error(t, err)
		_, err = DefinitionSimpRules(DefinitionDirect, nil)
		require.Error(t, err)
	})
}

func TestDataDefinitionShape_CoversEveryKind(t *testing.T) {
	require.Equal(t, DefinitionDataInduct, DataDefinitionShape(DataInduct))
	require.Equal(t, DefinitionDataRecursion, DataDefinitionShape(DataRecursion))
	require.Equal(t, DefinitionDataInj, DataDefinitionShape(DataInj))
	require.Equal(t, DefinitionDataDistinct, DataDefinitionShape(DataDistinct))
}
