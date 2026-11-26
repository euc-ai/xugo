package main

import (
	"os"
	"testing"

	"github.com/euc-ai/xugo/library/index"
	"github.com/stretchr/testify/require"
)

// `query definition` takes one constant as `const` and several as
// `consts`: one is answered by its definition view, several by one
// answer holding each, the names no chapter defines listed apart. Both
// fields at once, and `consts` on another question, are refused by name.
func TestQueryDefinition_OneOrSeveral(t *testing.T) {
	out, err := rpcQuery([]byte(`{"cmd":"query","what":"definition","const":"nat_gcd"}`))
	require.NoError(t, err)
	require.Equal(t, "nat_gcd", out.(*index.DefinitionView).Definition.Const)

	out, err = rpcQuery([]byte(`{"cmd":"query","what":"definition","consts":["int_gcd","ring_ops","nat_gcd"]}`))
	require.NoError(t, err)
	batch := out.(*index.ConstantsView)
	require.Len(t, batch.Definitions, 2)
	require.Equal(t, "int_gcd", batch.Definitions[0].Definition.Const)
	require.Equal(t, "nat_gcd", batch.Definitions[1].Definition.Const)
	require.Len(t, batch.Undefined, 1)
	require.Equal(t, "ring_ops", batch.Undefined[0].Name)

	_, err = rpcQuery([]byte(`{"cmd":"query","what":"definition","const":"nat_gcd","consts":["int_gcd"]}`))
	require.ErrorContains(t, err, "takes `const` or `consts`, not both")
	_, err = rpcQuery([]byte(`{"cmd":"query","what":"member","member":"nat_gcd.GcdDef","consts":["int_gcd"]}`))
	require.ErrorContains(t, err, "query member takes no `consts`")
}

// On the command line one name asks with `const` and two or more with
// `consts`.
func TestQueryDefinition_CommandLine(t *testing.T) {
	stdout := os.Stdout
	os.Stdout, _ = os.Open(os.DevNull)
	defer func() { os.Stdout = stdout }()

	resetTrace()
	cmdQuery([]string{"definition", "nat_gcd"})
	require.Equal(t, "nat_gcd", traceEntry.Output.(*index.DefinitionView).Definition.Const)

	resetTrace()
	cmdQuery([]string{"definition", "nat_gcd", "int_gcd"})
	batch := traceEntry.Output.(*index.ConstantsView)
	require.Len(t, batch.Definitions, 2)
	require.Empty(t, batch.Undefined)
}
