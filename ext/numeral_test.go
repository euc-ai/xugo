package ext

import (
	"math/big"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
)

// MakeNumeral ∘ NumeralValue round-trips, including values past 2^64 — the
// whole point of the big.Int rewrite (the old uint64 copies truncated).
func TestNumeralRoundTrip(t *testing.T) {
	cases := []string{
		"0", "1", "2", "3", "42", "255", "256",
		"18446744073709551615",                    // 2^64 - 1
		"18446744073709551616",                    // 2^64    (overflowed uint64 before)
		"340282366920938463463374607431768211457", // 2^128 + 1
	}
	for _, s := range cases {
		n, _ := new(big.Int).SetString(s, 10)
		term := MakeNumeral(n)
		assert.True(t, IsCanonicalNumeral(term), "MakeNumeral output must be canonical: %s", s)
		got, ok := NumeralValue(term)
		assert.True(t, ok, "NumeralValue ok: %s", s)
		assert.Equal(t, 0, got.Cmp(n), "round-trip value: %s -> %s", s, got.String())
		// Printer collapses the tower back to the same decimal.
		assert.Equal(t, s, FormatTerm(term, false), "decimal collapse: %s", s)
	}
}

// _0 alone is the canonical zero and renders "0".
func TestNumeralZero(t *testing.T) {
	z := ZeroMeta.Term()
	assert.True(t, IsCanonicalNumeral(z))
	v, ok := NumeralValue(z)
	assert.True(t, ok)
	assert.Equal(t, int64(0), v.Int64())
	assert.Equal(t, "0", FormatTerm(z, false))
}

// IsCanonicalNumeral rejects non-canonical and non-ground towers, while
// NumeralValue still reads the non-canonical (but ground) ones.
func TestNumeralCanonicality(t *testing.T) {
	// bit0(_0): a redundant leading bit — value 0, but not canonical (_0 is).
	bit0Zero := core.Apply(Bit0Meta.Term(), ZeroMeta.Term())
	v, ok := NumeralValue(bit0Zero)
	assert.True(t, ok, "bit0(_0) is a readable tower")
	assert.Equal(t, int64(0), v.Int64())
	assert.False(t, IsCanonicalNumeral(bit0Zero), "bit0(_0) is not canonical")

	// bit0(x) with a variable: not ground, so neither readable nor canonical;
	// the printer must leave it symbolic.
	x := Var("x", NumType)
	bit0Var := core.Apply(Bit0Meta.Term(), x)
	_, ok = NumeralValue(bit0Var)
	assert.False(t, ok, "bit0(x) has a free var")
	assert.False(t, IsCanonicalNumeral(bit0Var))
	assert.Equal(t, "bit0(x)", FormatTerm(bit0Var, false), "non-ground tower stays symbolic")
}
