// Native numeral bridge: the single, big.Int-backed conversion between
// Go integers and the BIT-tower encoding of `num` literals.
//
// A natural-number literal is a tower over the three consts defined
// here:
//
//	bits(0)     = _0
//	bits(2k)    = bit0(bits k)
//	bits(2k+1)  = bit1(bits k)
//
// and the engine and omega work over that tower directly.
//
// This file is the one home for that arithmetic, and it goes through
// big.Int: a uint64-capped conversion would silently truncate literals
// ≥ 2^64 in both the parse path and witness construction. The parser,
// the pretty-printer (decimal collapse), and omega all call into these
// helpers.
//
// These are guidance-only helpers — they build and inspect ordinary
// kernel Terms made of named consts; nothing here is part of the trusted
// kernel. The consts live in `ext` (not `core`) because the printer that
// folds them to decimal also lives here, and `ext` is the lowest package
// the parser, printer, and omega all share.

package ext

import (
	"math/big"

	"github.com/euc-ai/xugo/core"
)

// NumMetaType is the meta-level "num" type (the natural numbers;
// 0-ary type constant). Structurally equal to what the DSL's type
// resolver produces for the bare name "num".
var NumMetaType = core.MakeMetaType("num", 0)

// NumType is the HOL `num` type.
var NumType core.HolType = core.MakeCompositeType(NumMetaType)

// The BIT-tower alphabet. Each meta's (name, absType) must match the
// registry's const meta for the same name — ConstTerm
// alpha-key equality hashes only (name, instantiated type), not meta
// identity, so independently-constructed metas with the same name agree.
// dsl/arith.go re-exports these (dsl.ZeroMeta = ext.ZeroMeta, …) so every
// `dsl.*` callsite resolves to the single instance here.
var (
	ZeroMeta = core.MakeConstMeta("_0", NumType)
	Bit0Meta = core.MakeConstMeta("bit0", core.MakeFun(NumType, NumType))
	Bit1Meta = core.MakeConstMeta("bit1", core.MakeFun(NumType, NumType))
)

// MakeNumeral builds the canonical BIT-tower for n.
// Non-positive n maps to _0 — `num` has no negatives, and 0 is _0.
//
// Canonical means no redundant leading bit0: MakeNumeral always produces
// the unique minimal tower, so IsCanonicalNumeral(MakeNumeral(n)) holds
// for every n ≥ 0.
func MakeNumeral(n *big.Int) core.Term {
	if n.Sign() <= 0 {
		return ZeroMeta.Term()
	}
	bit := Bit0Meta.Term()
	if n.Bit(0) == 1 {
		bit = Bit1Meta.Term()
	}
	half := new(big.Int).Rsh(n, 1)
	return core.Apply(bit, MakeNumeral(half))
}

// Canonical reference terms for the tower alphabet.
var (
	zeroTerm = ZeroMeta.Term()
	bit0Term = Bit0Meta.Term()
	bit1Term = Bit1Meta.Term()
)

// NumeralValue reads a BIT-tower to its value. ok=false if t is not a
// well-formed, fully-ground tower (e.g. it contains a variable, or its
// head is some other const).
//
// Accepts non-canonical towers too (e.g. bit0(_0) → 0); use
// IsCanonicalNumeral to additionally require canonical shape.
//
// Head matching is via ConstTerm.Equals, which (by core's "a name fixes a
// type" invariant) panics if it meets a same-named const of a different
// type — e.g. a `bit0 : ind→ind`. That panic is intentional: such a const
// is an ill-formed environment, and surfacing it is core's job, not
// something this helper should silently mask.
func NumeralValue(t core.Term) (*big.Int, bool) {
	if t.Equals(zeroTerm) {
		return big.NewInt(0), true
	}
	a, ok := t.AsAppliedTerm()
	if !ok {
		return nil, false
	}
	fun := a.Fun()
	switch {
	case fun.Equals(bit0Term):
		n, ok := NumeralValue(a.Arg())
		if !ok {
			return nil, false
		}
		return n.Lsh(n, 1), true // 2n
	case fun.Equals(bit1Term):
		n, ok := NumeralValue(a.Arg())
		if !ok {
			return nil, false
		}
		n.Lsh(n, 1)
		return n.Add(n, big.NewInt(1)), true // 2n+1
	}
	return nil, false
}

// IsCanonicalNumeral reports whether t is a ground BIT-tower in canonical
// shape — i.e. it equals MakeNumeral of its own value, so it has no
// redundant leading bit0. _0 is canonical; bit0(_0) and bit0(var) are not.
//
// This is the decidable guard the pretty-printer uses to decide whether a
// subterm may be folded to decimal: only canonical, fully-ground towers
// are, so a mid-proof non-normal tower or a bit0(n) with a variable n
// keeps printing symbolically.
func IsCanonicalNumeral(t core.Term) bool {
	v, ok := NumeralValue(t)
	if !ok {
		return false
	}
	return MakeNumeral(v).Equals(t)
}
