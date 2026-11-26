package registry

import (
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// A chapter's numeric domain is declared once — a row of its
// vocabulary, or on the handle of a family that has none — and read in
// one place, whatever door asks: a member's statement, a definition's
// equation, a session bound to the family.
func TestFamily_CoerceDomain(t *testing.T) {
	const unanchored = "∀m n:num. &m < &n ⇒ m < n"
	reads := func(f *Family) (refusal string) {
		defer func() {
			if r := recover(); r != nil {
				refusal = r.(string)
			}
		}()
		f.ParseScript(parseEnv()).MakePropText(unanchored)
		return ""
	}

	none := NewFamily("zz_coerce_none", nil)
	require.Nil(t, none.CoerceDomain())
	require.Contains(t, reads(none), "unanchored", "no declaration: the statement door refuses")

	handle := NewFamily("zz_coerce_handle", nil).WithCoerceDomain(proof.RealDomain)
	require.True(t, handle.CoerceDomain().Equals(proof.RealDomain))
	require.Empty(t, reads(handle), "declared on the handle")

	row := NewFamily("zz_coerce_row", nil).WithVocabSpec(NewVocabSpec(nil).CoerceDomain(proof.IntDomain))
	require.True(t, row.CoerceDomain().Equals(proof.IntDomain))
	require.Empty(t, reads(row), "declared as a vocabulary row")

	require.PanicsWithValue(t,
		"registry.WithCoerceDomain(zz_coerce_row): the family has a vocabulary — declare the domain there, as its CoerceDomain row",
		func() { row.WithCoerceDomain(proof.RealDomain) })
	require.Panics(t, func() {
		NewFamily("zz_coerce_twice", nil).WithCoerceDomain(proof.RealDomain).
			WithVocabSpec(NewVocabSpec(nil).CoerceDomain(proof.RealDomain))
	}, "a domain declared twice")
}
