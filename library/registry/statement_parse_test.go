package registry

import (
	"fmt"
	"slices"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/prover/proof"
)

// A statement that does not parse panics naming the member and its
// family, so a gate that reads every member's statement is not read
// as failing on the member it happened to be iterating.
func TestStatement_ParseRefusalNamesTheMember(t *testing.T) {
	fam := NewFamily("zz_statement_parse", nil)
	bad := fam.Add(ProofEntry{
		Name:  "Bad",
		Build: BuildSpec{Headline: "∀P:(bool → bool). P(0)", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	// The entry's statement is unreadable by design: take it out of the
	// registry again, so a test that reads every member does not meet it.
	t.Cleanup(func() {
		delete(byName, bad.Name)
		if byKey[bad.Key] == bad {
			delete(byKey, bad.Key)
		}
		all = slices.DeleteFunc(all, func(e *ProofEntry) bool { return e == bad })
		fam.entries = slices.DeleteFunc(fam.entries, func(e *ProofEntry) bool { return e == bad })
	})
	defer func() {
		r := recover()
		require.NotNil(t, r, "an ill-typed statement panics")
		msg := fmt.Sprint(r)
		require.Contains(t, msg, "proof registry: zz_statement_parse.Bad states a text that does not parse")
		require.Contains(t, msg, "Script.MakePropText")
	}()
	bad.Statement()
}
