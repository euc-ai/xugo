package omega

import (
	"math"
	"math/big"
	"slices"
	"strings"
	"testing"
)

// mono is the monomial c·a, form the linear form with constant k and the
// given monomials, integers the list of the given values and vector the
// same as a row's vector.
func mono(c int64, a Term) monomialL { return monomialL{coeff: integerOf(c), atom: a} }

func vector(values ...int64) _Vector { return vectorOf(integers(values...)) }

func form(k int64, monos ...monomialL) linForm { return linForm{konst: integerOf(k), monos: monos} }

func integers(values ...int64) []_Integer {
	out := make([]_Integer, len(values))
	for i, v := range values {
		out[i] = integerOf(v)
	}
	return out
}

// word is the value of a natural that fits a uint64.
func word(n _Integer) uint64 {
	v := n.bigInt()
	if !v.IsUint64() {
		panic("omega test: " + n.String() + " is not a uint64")
	}
	return v.Uint64()
}

// decimal is the integer a decimal text spells.
func decimal(text string) _Integer {
	v, ok := new(big.Int).SetString(text, 10)
	if !ok {
		panic("omega test: not a decimal integer: " + text)
	}
	return integerOwning(v)
}

// integerSamples straddles every boundary the word arithmetic has to notice:
// zero, the int32 and int64 limits, their neighbours, and values past both.
func integerSamples() []_Integer {
	texts := []string{
		"0", "1", "-1", "2", "-2", "3", "7", "-7", "12", "21",
		"2147483647", "2147483648", "-2147483648", "-2147483649",
		"3037000499", "3037000500", "-3037000500", "4294967296",
		"2305843009213693951", "2305843009213693952", "2432902008176640000",
		"9223372036854775806", "9223372036854775807", "9223372036854775808",
		"-9223372036854775807", "-9223372036854775808", "-9223372036854775809",
		"18446744073709551615", "18446744073709551616", "-18446744073709551616",
		"15511210043330985984000000", "-15511210043330985984000000",
		"340282366920938463463374607431768211456",
	}
	out := make([]_Integer, len(texts))
	for i, text := range texts {
		out[i] = decimal(text)
	}
	return out
}

// canonical reports whether n is held the one way its value allows.
func canonical(n _Integer) bool {
	if n.wide == nil {
		return true
	}
	return n.word == 0 && !n.wide.IsInt64()
}

func TestIntegerArithmeticIsExact(t *testing.T) {
	samples := integerSamples()
	check := func(op string, a, b, got _Integer, want *big.Int) {
		t.Helper()
		if !canonical(got) {
			t.Errorf("%v %s %v: result %v is not canonical", a, op, b, got)
		}
		if got.bigInt().Cmp(want) != 0 {
			t.Errorf("%v %s %v = %v, want %v", a, op, b, got, want)
		}
	}
	for _, a := range samples {
		x := a.bigInt()
		check("neg", a, a, a.neg(), new(big.Int).Neg(x))
		if got, want := a.sign(), x.Sign(); got != want {
			t.Errorf("sign(%v) = %d, want %d", a, got, want)
		}
		if got := a.String(); got != x.String() {
			t.Errorf("String(%v) = %s", x, got)
		}
		for _, b := range samples {
			y := b.bigInt()
			check("+", a, b, a.add(b), new(big.Int).Add(x, y))
			check("-", a, b, a.sub(b), new(big.Int).Sub(x, y))
			check("*", a, b, a.mul(b), new(big.Int).Mul(x, y))
			check("gcd", a, b, a.gcd(b), new(big.Int).GCD(nil, nil, new(big.Int).Abs(x), new(big.Int).Abs(y)))
			if got, want := a.cmp(b), x.Cmp(y); got != want {
				t.Errorf("cmp(%v, %v) = %d, want %d", a, b, got, want)
			}
			if got, want := a.equal(b), x.Cmp(y) == 0; got != want {
				t.Errorf("equal(%v, %v) = %v, want %v", a, b, got, want)
			}
			if b.sign() <= 0 {
				continue
			}
			q, r := a.divMod(b)
			wantQ, wantR := new(big.Int).DivMod(x, y, new(big.Int))
			check("div", a, b, q, wantQ)
			check("mod", a, b, r, wantR)
			if r.sign() < 0 || r.cmp(b) >= 0 {
				t.Errorf("%v mod %v = %v, outside [0, %v)", a, b, r, b)
			}
		}
	}
}

func TestIntegerConstructors(t *testing.T) {
	if got := integerOfUint(math.MaxUint64); got.String() != "18446744073709551615" || !canonical(got) {
		t.Errorf("integerOfUint(MaxUint64) = %v", got)
	}
	if got := integerOfUint(math.MaxInt64); got.wide != nil || got.word != math.MaxInt64 {
		t.Errorf("integerOfUint(MaxInt64) = %v, want a word", got)
	}
	source := new(big.Int).Lsh(big.NewInt(1), 70)
	kept := integerOfBig(source)
	source.SetInt64(5)
	if kept.String() != "1180591620717411303424" {
		t.Errorf("integerOfBig aliased its argument: %v", kept)
	}
	lent := kept.bigInt()
	lent.SetInt64(5)
	if kept.String() != "1180591620717411303424" {
		t.Errorf("bigInt lent the value's own storage: %v", kept)
	}
	if !(_Integer{}).isZero() || !integerOne.isOne() || integerOne.isZero() || decimal("18446744073709551616").isOne() {
		t.Error("isZero / isOne disagree with the values")
	}
}

func TestIntegerDivModRefusesNonPositiveDivisor(t *testing.T) {
	for _, d := range []_Integer{{}, integerOf(-3), decimal("-18446744073709551616")} {
		func() {
			defer func() {
				if recover() == nil {
					t.Errorf("divMod by %v did not panic", d)
				}
			}()
			integerOf(7).divMod(d)
		}()
	}
}

// Equal values write equal keys, distinct values distinct ones, and no key is
// a prefix of another — so a row's coefficients concatenate without separators.
func TestIntegerKeyIsCanonicalAndSelfDelimiting(t *testing.T) {
	key := func(n _Integer) string {
		var b strings.Builder
		n.appendKey(&b)
		return b.String()
	}
	samples := integerSamples()
	for i, a := range samples {
		if again := key(a.add(integerOne).sub(integerOne)); again != key(a) {
			t.Errorf("%v: a recomputed equal value wrote another key", a)
		}
		for j, b := range samples {
			if i == j {
				continue
			}
			if strings.HasPrefix(key(b), key(a)) {
				t.Errorf("key(%v) is a prefix of key(%v)", a, b)
			}
		}
	}
}

func TestIntegerSizeAccounting(t *testing.T) {
	if got := integerOf(math.MaxInt64).wideBytes(); got != 0 {
		t.Errorf("a word-sized value holds %d wide bytes", got)
	}
	small, large := decimal("18446744073709551616"), decimal("340282366920938463463374607431768211456")
	if small.wideBytes() <= 0 || large.wideBytes() <= small.wideBytes() {
		t.Errorf("wide bytes do not grow with the value: %d, %d", small.wideBytes(), large.wideBytes())
	}
	if got := (row{coeffs: vector(1, -7, math.MinInt64), konst: integerOf(math.MaxInt64)}).wideBytes(); got != 0 {
		t.Errorf("a row of words holds %d wide bytes", got)
	}
	wideRow := row{coeffs: vectorOf([]_Integer{small, integerOne}), konst: large}
	if got, floor := wideRow.wideBytes(), small.wideBytes()+large.wideBytes(); got <= floor {
		t.Errorf("row.wideBytes = %d, want more than its two wide values' %d", got, floor)
	}
}

// A vector reads back the entries it was built from, whichever of them left
// the int64 range, and stays one pointer-free slice while none has.
func TestVectorHoldsItsEntries(t *testing.T) {
	samples := integerSamples()
	v := vectorOf(samples)
	if v.len() != len(samples) || !slices.EqualFunc(v.entries(), samples, _Integer.equal) {
		t.Fatalf("entries() = %v, want %v", v.entries(), samples)
	}
	for i, want := range samples {
		if !v.at(i).equal(want) || v.sign(i) != want.sign() {
			t.Errorf("at(%d) = %v sign %d, want %v sign %d", i, v.at(i), v.sign(i), want, want.sign())
		}
	}
	if v.isZero() || !vector(0, 0, 0).isZero() || vector(0, 3).isZero() || !(_Vector{}).isZero() {
		t.Error("isZero disagrees with the entries")
	}
	if words := vector(1, -2, math.MaxInt64, math.MinInt64); words.wide != nil {
		t.Error("a vector of int64 values allocated wide storage")
	}
	padded := v.padded(len(samples) + 3)
	want := append(slices.Clone(samples), _Integer{}, _Integer{}, _Integer{})
	if !slices.EqualFunc(padded.entries(), want, _Integer.equal) {
		t.Errorf("padded = %v", padded.entries())
	}
}

// combination is exact entry by entry, on the word path and past it, and a
// result that fits words comes back as words whatever its operands were.
func TestVectorCombinationIsExact(t *testing.T) {
	samples := integerSamples()
	reversed := slices.Clone(samples)
	slices.Reverse(reversed)
	multipliers := []_Integer{integerOf(1), integerOf(3), integerOf(2147483648), decimal("9223372036854775807"), decimal("18446744073709551616")}
	for _, operands := range [][2][]_Integer{
		{integers(1, -2, 3, 0), integers(5, 7, -11, 0)},                                      // words throughout
		{integers(2147483647, -2147483648, 3037000500), integers(2147483647, 5, 3037000500)}, // products at the edge of a word
		{integers(math.MaxInt64, math.MinInt64, 1), integers(1, 1, math.MaxInt64)},           // sums past it
		{samples, reversed}, // wide operands
	} {
		p, n := vectorOf(operands[0]), vectorOf(operands[1])
		for _, mp := range multipliers {
			for _, mn := range multipliers {
				got := combination(mp, p, mn, n)
				for i := range operands[0] {
					want := mp.mul(operands[0][i]).add(mn.mul(operands[1][i]))
					if !got.at(i).equal(want) {
						t.Fatalf("(%v·%v + %v·%v) = %v, want %v", mp, operands[0][i], mn, operands[1][i], got.at(i), want)
					}
					if got.wide != nil && got.wide[i] != nil && got.wide[i].IsInt64() {
						t.Fatalf("entry %v is held wide though it fits a word", got.at(i))
					}
				}
			}
		}
	}
	// 2⁶⁴·1 − 2⁶⁴·1: wide operands, a result of words.
	wide := decimal("18446744073709551616")
	if got := combination(integerOne, vectorOf([]_Integer{wide}), integerOne, vectorOf([]_Integer{wide.neg()})); got.wide != nil || !got.isZero() {
		t.Errorf("a cancelling combination kept wide storage: %v", got.entries())
	}
}

func TestVectorGCD(t *testing.T) {
	for _, c := range []struct {
		v    _Vector
		want string
	}{
		{vector(), "0"},
		{vector(0, 0), "0"},
		{vector(6, -9, 0), "3"},
		{vector(math.MinInt64, 0), "9223372036854775808"},
		{vector(math.MinInt64, 6), "2"},
		{vectorOf([]_Integer{decimal("36893488147419103232"), decimal("-55340232221128654848")}), "18446744073709551616"},
		{vectorOf([]_Integer{decimal("18446744073709551616"), integerOf(6)}), "2"},
	} {
		if got := c.v.gcd(); got.String() != c.want {
			t.Errorf("gcd(%v) = %v, want %s", c.v.entries(), got, c.want)
		}
	}
}
