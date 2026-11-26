package omega

import (
	"encoding/binary"
	"math"
	"math/big"
	"math/bits"
	"strconv"
	"strings"
)

// _Integer is an exact integer: the value of a numeral, a coefficient of a
// linear form, an entry of a Fourier–Motzkin row, a Farkas multiplier. The
// untrusted model computes with it, and the proof side evaluates the same
// numerals on their bit-trees without a bound, so the two agree at every
// size only because neither rounds nor wraps.
//
// The zero value is 0. A value in the int64 range is held in word, with wide
// nil; any other value is held in wide. Each value has one representation,
// and arithmetic on word-sized operands allocates nothing.
//
// The leading zero-size field makes the type incomparable: `==` on two
// values would compare wide's address, so the compiler refuses it and equal
// is the equality.
type _Integer struct {
	_    [0]func()
	word int64
	wide *big.Int
}

var integerOne = integerOf(1)

func integerOf(n int64) _Integer { return _Integer{word: n} }

func integerOfUint(n uint64) _Integer {
	if n <= math.MaxInt64 {
		return _Integer{word: int64(n)}
	}
	return _Integer{wide: new(big.Int).SetUint64(n)}
}

// integerOfBig is v's value. v stays the caller's.
func integerOfBig(v *big.Int) _Integer {
	if v.IsInt64() {
		return _Integer{word: v.Int64()}
	}
	return _Integer{wide: new(big.Int).Set(v)}
}

// integerOwning is v's value, keeping v itself when the value is wide.
func integerOwning(v *big.Int) _Integer {
	if v.IsInt64() {
		return _Integer{word: v.Int64()}
	}
	return _Integer{wide: v}
}

// bigInt is a's value as a big.Int the caller owns.
func (a _Integer) bigInt() *big.Int {
	if a.wide != nil {
		return new(big.Int).Set(a.wide)
	}
	return big.NewInt(a.word)
}

// operand is a's value for reading: wide itself, or scratch set to word.
func (a _Integer) operand(scratch *big.Int) *big.Int {
	if a.wide != nil {
		return a.wide
	}
	return scratch.SetInt64(a.word)
}

func (a _Integer) sign() int {
	if a.wide != nil {
		return a.wide.Sign()
	}
	switch {
	case a.word > 0:
		return 1
	case a.word < 0:
		return -1
	}
	return 0
}

func (a _Integer) isZero() bool { return a.wide == nil && a.word == 0 }

func (a _Integer) isOne() bool { return a.wide == nil && a.word == 1 }

// cmp is -1, 0 or +1 as a is below, equal to or above b.
func (a _Integer) cmp(b _Integer) int {
	if a.wide == nil && b.wide == nil {
		switch {
		case a.word < b.word:
			return -1
		case a.word > b.word:
			return 1
		}
		return 0
	}
	var x, y big.Int
	return a.operand(&x).Cmp(b.operand(&y))
}

func (a _Integer) equal(b _Integer) bool {
	if a.wide == nil || b.wide == nil {
		return a.wide == nil && b.wide == nil && a.word == b.word
	}
	return a.wide.Cmp(b.wide) == 0
}

func (a _Integer) add(b _Integer) _Integer {
	if a.wide == nil && b.wide == nil {
		if s := a.word + b.word; (s > a.word) == (b.word > 0) {
			return _Integer{word: s}
		}
	}
	return a.addWide(b)
}

func (a _Integer) addWide(b _Integer) _Integer {
	var x, y big.Int
	return integerOwning(new(big.Int).Add(a.operand(&x), b.operand(&y)))
}

func (a _Integer) sub(b _Integer) _Integer {
	if a.wide == nil && b.wide == nil {
		if d := a.word - b.word; (d < a.word) == (b.word > 0) {
			return _Integer{word: d}
		}
	}
	return a.subWide(b)
}

func (a _Integer) subWide(b _Integer) _Integer {
	var x, y big.Int
	return integerOwning(new(big.Int).Sub(a.operand(&x), b.operand(&y)))
}

func (a _Integer) mul(b _Integer) _Integer {
	if a.wide == nil && b.wide == nil {
		if p, ok := mulWord(a.word, b.word); ok {
			return _Integer{word: p}
		}
	}
	return a.mulWide(b)
}

func (a _Integer) mulWide(b _Integer) _Integer {
	var x, y big.Int
	return integerOwning(new(big.Int).Mul(a.operand(&x), b.operand(&y)))
}

// mulWord is a·b when the product is an int64.
func mulWord(a, b int64) (int64, bool) {
	if fitsInt32(a) && fitsInt32(b) {
		return a * b, true
	}
	negative := (a < 0) != (b < 0)
	hi, lo := bits.Mul64(magnitude(a), magnitude(b))
	switch {
	case hi != 0:
		return 0, false
	case negative && lo <= 1<<63:
		return -int64(lo), true // −2⁶³ is int64(2⁶³) negated, which wraps to itself
	case !negative && lo < 1<<63:
		return int64(lo), true
	}
	return 0, false
}

// magnitude is |n|, which for the least int64 is 2⁶³.
func magnitude(n int64) uint64 {
	if n < 0 {
		return -uint64(n)
	}
	return uint64(n)
}

func (a _Integer) neg() _Integer {
	if a.wide == nil && a.word != math.MinInt64 {
		return _Integer{word: -a.word}
	}
	var x big.Int
	return integerOwning(new(big.Int).Neg(a.operand(&x)))
}

// divMod is the floor quotient q and the remainder r of a by a positive d:
// a = q·d + r with 0 ≤ r < d.
func (a _Integer) divMod(d _Integer) (q, r _Integer) {
	if d.sign() <= 0 {
		panic("omega: integer division by the non-positive " + d.String())
	}
	if a.wide == nil && d.wide == nil {
		qw, rw := a.word/d.word, a.word%d.word
		if rw < 0 {
			qw--
			rw += d.word
		}
		return _Integer{word: qw}, _Integer{word: rw}
	}
	var x, y big.Int
	quotient, remainder := new(big.Int).DivMod(a.operand(&x), d.operand(&y), new(big.Int))
	return integerOwning(quotient), integerOwning(remainder)
}

// gcd is the greatest common divisor of |a| and |b|, 0 when both are 0.
func (a _Integer) gcd(b _Integer) _Integer {
	if a.wide == nil && b.wide == nil {
		x, y := magnitude(a.word), magnitude(b.word)
		for y != 0 {
			x, y = y, x%y
		}
		return integerOfUint(x)
	}
	var x, y big.Int
	x.Abs(a.operand(&x))
	y.Abs(b.operand(&y))
	return integerOwning(new(big.Int).GCD(nil, nil, &x, &y))
}

func (a _Integer) String() string {
	if a.wide != nil {
		return a.wide.String()
	}
	return strconv.FormatInt(a.word, 10)
}

// appendKey writes a self-delimiting encoding of a: equal values write equal
// bytes, and no value's bytes are a prefix of another's.
func (a _Integer) appendKey(b *strings.Builder) {
	if a.wide == nil {
		appendWordKey(b, a.word)
		return
	}
	digits := a.wide.Bytes()
	var buf [binary.MaxVarintLen64]byte
	if a.wide.Sign() < 0 {
		b.WriteByte(1)
	} else {
		b.WriteByte(2)
	}
	b.Write(buf[:binary.PutUvarint(buf[:], uint64(len(digits)))])
	b.Write(digits)
}

// appendWordKey is appendKey for the value n.
func appendWordKey(b *strings.Builder, n int64) {
	var buf [binary.MaxVarintLen64]byte
	b.WriteByte(0)
	b.Write(buf[:binary.PutVarint(buf[:], n)])
}

// wideBytes is what a value outside the int64 range holds beyond its word:
// the big.Int's header and its words.
func (a _Integer) wideBytes() int {
	if a.wide == nil {
		return 0
	}
	return bigBytes(a.wide)
}

func bigBytes(v *big.Int) int { return (4 + len(v.Bits())) * (bits.UintSize / 8) }

// _Vector is a vector of exact integers: a Fourier–Motzkin row's
// coefficients, or its certificate. An entry in the int64 range is its word.
// wide is nil while every entry is, and the vector is then one pointer-free
// slice at eight bytes an entry — the form elimination works in. Once an
// entry leaves the range, wide runs parallel to words and holds that entry
// at its index, the word there unused.
type _Vector struct {
	words []int64
	wide  []*big.Int
}

func vectorOf(entries []_Integer) _Vector {
	v := _Vector{words: make([]int64, len(entries))}
	for i, e := range entries {
		if e.wide == nil {
			v.words[i] = e.word
			continue
		}
		if v.wide == nil {
			v.wide = make([]*big.Int, len(entries))
		}
		v.wide[i] = e.wide
	}
	return v
}

func (v _Vector) len() int { return len(v.words) }

func (v _Vector) at(i int) _Integer {
	if v.wide != nil && v.wide[i] != nil {
		return _Integer{wide: v.wide[i]}
	}
	return _Integer{word: v.words[i]}
}

func (v _Vector) sign(i int) int {
	if v.wide != nil && v.wide[i] != nil {
		return v.wide[i].Sign()
	}
	switch w := v.words[i]; {
	case w > 0:
		return 1
	case w < 0:
		return -1
	}
	return 0
}

func (v _Vector) isZero() bool {
	if v.wide != nil {
		return false // a wide entry is not zero
	}
	for _, w := range v.words {
		if w != 0 {
			return false
		}
	}
	return true
}

func (v _Vector) entries() []_Integer {
	out := make([]_Integer, len(v.words))
	for i := range out {
		out[i] = v.at(i)
	}
	return out
}

// padded is v at width n ≥ v.len(), the new entries zero.
func (v _Vector) padded(n int) _Vector {
	out := _Vector{words: make([]int64, n)}
	copy(out.words, v.words)
	if v.wide != nil {
		out.wide = make([]*big.Int, n)
		copy(out.wide, v.wide)
	}
	return out
}

// gcd is the greatest common divisor of the entries' magnitudes, 0 when
// every entry is 0.
func (v _Vector) gcd() _Integer {
	if v.wide != nil {
		var g _Integer
		for i := range v.words {
			g = g.gcd(v.at(i))
		}
		return g
	}
	var g uint64
	for _, w := range v.words {
		for x := magnitude(w); x != 0; {
			g, x = x, g%x
		}
	}
	return integerOfUint(g)
}

// wideBytes is what v holds beyond its words.
func (v _Vector) wideBytes() int {
	if v.wide == nil {
		return 0
	}
	n := len(v.wide) * (bits.UintSize / 8)
	for _, w := range v.wide {
		if w != nil {
			n += bigBytes(w)
		}
	}
	return n
}

// combination is the vector mp·p + mn·n, for p and n of one length.
func combination(mp _Integer, p _Vector, mn _Integer, n _Vector) _Vector {
	if mp.wide == nil && mn.wide == nil && p.wide == nil && n.wide == nil {
		words := make([]int64, len(p.words))
		if combineWords(words, mp.word, p.words, mn.word, n.words) {
			return _Vector{words: words}
		}
	}
	entries := make([]_Integer, len(p.words))
	for i := range entries {
		entries[i] = mp.mul(p.at(i)).add(mn.mul(n.at(i)))
	}
	return vectorOf(entries)
}

// combineWords sets out[i] to mp·p[i] + mn·n[i] and reports whether every
// one of them is an int64; on false, out is not to be read.
func combineWords(out []int64, mp int64, p []int64, mn int64, n []int64) bool {
	mpShort, mnShort := fitsInt32(mp), fitsInt32(mn)
	for i := range out {
		a, b := p[i], n[i]
		var x, y int64
		var ok bool
		if mpShort && fitsInt32(a) {
			x = mp * a
		} else if x, ok = mulWord(mp, a); !ok {
			return false
		}
		if mnShort && fitsInt32(b) {
			y = mn * b
		} else if y, ok = mulWord(mn, b); !ok {
			return false
		}
		s := x + y
		if (s > x) != (y > 0) {
			return false
		}
		out[i] = s
	}
	return true
}

func fitsInt32(n int64) bool { return int64(int32(n)) == n }
