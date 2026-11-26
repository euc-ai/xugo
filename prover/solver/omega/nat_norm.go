package omega

import (
	"math/big"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
)

var (
	natZero = dsl.ZeroMeta.Term()
	natBit0 = dsl.Bit0Meta.Term()
	natBit1 = dsl.Bit1Meta.Term()
)

func bit0(t Term) Term { return ext.Apply(natBit0, t) }

func bit1(t Term) Term { return ext.Apply(natBit1, t) }

func sucT(t Term) Term { return ext.Apply(natSuc, t) }

func isZeroBit(t Term) bool { return t.Equals(natZero) }

func asUnary(t, op Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(op) {
		return a.Arg(), true
	}
	return nil, false
}

func asBit0(t Term) (Term, bool) { return asUnary(t, natBit0) }

func asBit1(t Term) (Term, bool) { return asUnary(t, natBit1) }

// asNumeral reports whether t is a numeral literal — a raw BIT-tree — and
// returns it.
func asNumeral(t Term) (Term, bool) {
	if isBitTree(t) {
		return t, true
	}
	return nil, false
}

// BitsToUint reads a raw BIT-tree as a COUNT — an exponent to unfold, a bound
// to enumerate under, an argument whose evaluation is capped. ok=false if t is
// not a well-formed BIT-tree or its value does not fit in a uint64: a count
// that large is past every cap its callers hold, so they decline. A numeral
// the solver computes with — a constant, a coefficient — is read exactly, at
// any size, by literalValue (domain.go).
func BitsToUint(t Term) (uint64, bool) {
	v, ok := ext.NumeralValue(t)
	if !ok || !v.IsUint64() {
		return 0, false
	}
	return v.Uint64(), true
}

// Numeral builds the literal for n as a raw BIT-tree. Delegates to the shared
// big.Int-backed builder so there is a single numeral encoder.
func Numeral(n uint64) Term { return ext.MakeNumeral(new(big.Int).SetUint64(n)) }

// numeralOf builds the literal for a natural n of any size.
func numeralOf(n _Integer) Term {
	if n.sign() < 0 {
		panic("omega: no numeral for the negative " + n.String())
	}
	return ext.MakeNumeral(n.bigInt())
}

// isBitTree reports whether t is a well-formed (canonical or not) BIT-tree.
func isBitTree(t Term) bool { _, ok := ext.NumeralValue(t); return ok }

// ── Recursive proof-producing evaluators on raw BIT-trees ────────────────────

// sucBits proves ⊢ suc x = z for a BIT-tree x.
func sucBits(x Term) *prop.PropWrapper {
	if isZeroBit(x) {
		return sucBitsZero() // ⊢ suc _0 = bit1 _0
	}
	if a, ok := asBit0(x); ok {
		return sucB0(a) // ⊢ suc (bit0 a) = bit1 a
	}
	if a, ok := asBit1(x); ok {
		// ⊢ suc (bit1 a) = bit0 (suc a),  then suc a → w.
		return sucB1(a).EqTrans(sucBits(a).LeftApply(natBit0))
	}
	panic("sucBits: not a BIT-tree")
}

// addBits proves ⊢ x + y = z for BIT-trees x, y.
func addBits(x, y Term) *prop.PropWrapper {
	if isZeroBit(x) {
		return zeroAddBits(y) // ⊢ _0 + y = y
	}
	if isZeroBit(y) {
		return addBitsZero(x) // ⊢ x + _0 = x
	}
	xa, x0 := asBit0(x)
	xb, x1 := asBit1(x)
	ya, y0 := asBit0(y)
	yb, y1 := asBit1(y)
	switch {
	case x0 && y0:
		// bit0 xa + bit0 ya = bit0 (xa+ya);  xa+ya → z.
		return addB0B0(xa, ya).EqTrans(addBits(xa, ya).LeftApply(natBit0))
	case x0 && y1:
		return addB0B1(xa, yb).EqTrans(addBits(xa, yb).LeftApply(natBit1))
	case x1 && y0:
		return addB1B0(xb, ya).EqTrans(addBits(xb, ya).LeftApply(natBit1))
	case x1 && y1:
		// bit1 xb + bit1 yb = bit0 (suc (xb+yb)).
		rec := addBits(xb, yb)                                         // ⊢ xb+yb = z
		inner := rec.LeftApply(natSuc).EqTrans(sucBits(prop.Rhs(rec))) // ⊢ suc(xb+yb) = w
		return addB1B1(xb, yb).EqTrans(inner.LeftApply(natBit0))
	}
	panic("addBits: not a BIT-tree")
}

// mulBits proves ⊢ x * y = z for BIT-trees x, y.
func mulBits(x, y Term) *prop.PropWrapper {
	if isZeroBit(x) {
		return mulZeroBits(y) // ⊢ _0 * y = _0
	}
	if isZeroBit(y) {
		return mulBitsZero(x) // ⊢ x * _0 = _0  (keeps deeper calls' y non-zero)
	}
	if a, ok := asBit0(x); ok {
		// bit0 a * y = bit0 (a*y);  a*y → z.
		return mulB0(a, y).EqTrans(mulBits(a, y).LeftApply(natBit0))
	}
	if a, ok := asBit1(x); ok {
		// bit1 a * y = bit0 (a*y) + y.  a*y → z, then bit0 z + y → w.
		rec := mulBits(a, y) // ⊢ a*y = z
		// bit0 (a*y) + y = bit0 z + y   (congruence on the left summand)
		midEq := rec.LeftApply(natBit0).LeftApply(natPlus).RightApply(y)
		tail := addBits(bit0(prop.Rhs(rec)), y) // ⊢ bit0 z + y = w
		return mulB1(a, y).EqTrans(midEq).EqTrans(tail)
	}
	panic("mulBits: not a BIT-tree")
}

// ── Public entry points over (raw BIT-tree) literals ─────────────────────────

// liftNumeralBinop runs `eval(l, r) ⊢ l ⋆ r = z` directly when l, r are
// literals (raw BIT-trees).
func liftNumeralBinop(l, r Term, eval func(x, y Term) *prop.PropWrapper) (*prop.PropWrapper, bool) {
	if !isBitTree(l) || !isBitTree(r) {
		return nil, false
	}
	return eval(l, r), true // ⊢ l ⋆ r = z
}

// NormNatAdd proves ⊢ l + r = <literal> when l, r are BIT-tree literals.
func NormNatAdd(l, r Term) (*prop.PropWrapper, bool) {
	return liftNumeralBinop(l, r, addBits)
}

// NormNatMul proves ⊢ l * r = <literal> when l, r are BIT-tree literals.
func NormNatMul(l, r Term) (*prop.PropWrapper, bool) {
	return liftNumeralBinop(l, r, mulBits)
}

// NormNatExp proves ⊢ nat_pow(m, n) = <literal> when m, n are BIT-tree literals. The
// pow analogue of NormNatAdd/Mul, completing the literal-evaluator family. The
// proof piggybacks on `expUnfold` (nat_exp.go) which builds the product chain
// `m · (m · (... · (m · 1)))`; `foldBitsProductChain` then collapses the chain
// to a single literal via repeated NormNatMul + congruence. Soundness rides on
// both: expUnfold reads the nat_pow-recursion bundle, NormNatMul is bit-recursion.
// ok=false on a non-literal operand, on n exceeding expUnfoldMax (the same cap
// expUnfold uses), or when the nat_pow bundle is unsupplied (expUnfold returns nil).
func NormNatExp(m, n Term) (*prop.PropWrapper, bool) {
	if !isBitTree(m) || !isBitTree(n) {
		return nil, false
	}
	nc, ok := BitsToUint(n)
	if !ok {
		return nil, false // n exceeds uint64 — far beyond expUnfoldMax anyway
	}
	unfold := expUnfold(m, nc) // ⊢ nat_pow(m, n) = chain
	if unfold == nil {
		return nil, false
	}
	chainEq, ok := foldBitsProductChain(prop.Rhs(unfold))
	if !ok {
		return nil, false
	}
	return unfold.EqTrans(chainEq), true // ⊢ nat_pow(m, n) = <literal>
}

// foldBitsProductChain folds a right-associated literal product chain
// `a · (b · (c · (... · z)))` (each leaf a BIT-tree literal) into a single
// literal, returning `⊢ chain = literal`. Recursive: fold the tail first via
// NormNatMul-driven congruence, then NormNatMul the head with the tail's
// literal. The terminating leaf (a bare literal) returns reflexivity.
// ok=false if any leaf is not a literal.
func foldBitsProductChain(t Term) (*prop.PropWrapper, bool) {
	if isBitTree(t) {
		return prop.Refl(t), true // base: already a literal
	}
	a, tail, ok := MatchesStar(t)
	if !ok || !isBitTree(a) {
		return nil, false
	}
	tailEq, ok := foldBitsProductChain(tail) // ⊢ tail = tailLit
	if !ok {
		return nil, false
	}
	tailLit := prop.Rhs(tailEq)
	// congruence under `a · _`: ⊢ a · tail = a · tailLit.
	cong := tailEq.LeftApply(ext.Apply(natStar, a))
	mulEq, ok := NormNatMul(a, tailLit) // ⊢ a · tailLit = result
	if !ok {
		return nil, false
	}
	return cong.EqTrans(mulEq), true // ⊢ a · tail = result
}

// ── nat_div / nat_mod evaluation (uniqueness-based, NOT bit-recursion) ────────────────
//
// nat_div/nat_mod have no per-constructor recursion equation the way +/*/suc do; the
// proof-producing route computes the
// quotient/remainder numerically, proves the witness `m = q·n + r ∧ r < n`
// (reusing the bit-recursion evaluators NormNatMul / NormNatAdd / NormNatLt),
// and discharges the bundle's DivModUniq — `∀m n q r. (m = q·n + r ∧ r < n) ⇒
// (nat_div(m, n) = q ∧ nat_mod(m, n) = r)` — then projects the wanted conjunct.
//
// Real once DivModUniq is supplied; until then (or on a shape-mismatched
// bundle / non-canonical input) it DECLINES (ok=false, no fabricated cert — the
// integer-frontier nil contract). n must be > 0 (the witness `r < n` excludes
// the n = 0 division-by-zero convention); ok=false on a non-literal or n = 0.
func divmodEval(m, n Term, wantDiv bool) (*prop.PropWrapper, bool) {
	mv, ok1 := ext.NumeralValue(m)
	nv, ok2 := ext.NumeralValue(n)
	if !ok1 || !ok2 || nv.Sign() == 0 {
		return nil, false
	}
	quotient, remainder := new(big.Int).QuoRem(mv, nv, new(big.Int))
	q, r := ext.MakeNumeral(quotient), ext.MakeNumeral(remainder)
	divEq := eqT(divT(m, n), q) // ⊢ nat_div(m, n) = q
	modEq := eqT(modT(m, n), r) // ⊢ nat_mod(m, n) = r
	// decline: the nat_div/nat_mod evaluator is supply-gated on DivModUniq (+ the numeral
	// sub-evaluators). When a step is unavailable we return "no proof" rather than
	// fabricating a cert — the caller declines (the integer-frontier nil contract).
	decline := func() (*prop.PropWrapper, bool) { return nil, false }

	uniq := divModUniqThm()
	if uniq == nil {
		return decline()
	}
	// Witness `⊢ m = q·n + r` from `q·n = qn` and `qn + r = m`.
	mulW, okm := NormNatMul(q, n) // ⊢ q·n = qn
	if !okm {
		return decline()
	}
	addW, oka := NormNatAdd(prop.Rhs(mulW), r)  // ⊢ qn + r = m'
	if !oka || !prop.Rhs(addW).AlphaEquals(m) { // non-canonical m: cannot evaluate
		return decline()
	}
	// (q·n)+r = qn+r (congruence on the left summand) = m', flipped to m = q·n+r.
	eqW := mulW.LeftApply(natPlus).RightApply(r).EqTrans(addW).EqSym()
	// ⊢ r < n  (from `(r<n) = T`).
	ltW, okl := NormNatLt(r, n)
	if !okl {
		return decline()
	}
	ltProof := ltW.EqSym().EqMP(prop.DerivesTrue)

	// Antecedent `⊢ (m = q·n+r) ∧ (r < n)`, then discharge DivModUniq.
	eqConcl := eqT(m, plus(star(q, n), r))
	ltConcl := lt(r, n)
	ante := prop.ConclAND(eqConcl, ltConcl).DeriveHypFrom(eqW).DeriveHypFrom(ltProof)
	impl, okShape := macroThm(uniq, []Term{m, n, q, r},
		imply(prop.And(eqConcl, ltConcl), prop.And(divEq, modEq)))
	if !okShape { // absent / wrong-shape DivModUniq: cannot evaluate
		return decline()
	}
	full := mp(impl, ante) // ⊢ (nat_div(m, n) = q) ∧ (nat_mod(m, n) = r)
	if wantDiv {
		return full.DeriveTrans(prop.HypAND0(divEq, modEq)), true
	}
	return full.DeriveTrans(prop.HypAND1(divEq, modEq)), true
}

// NormNatDiv proves ⊢ nat_div(m, n) = <literal> for BIT-tree literals (n > 0).
func NormNatDiv(m, n Term) (*prop.PropWrapper, bool) { return divmodEval(m, n, true) }

// NormNatMod proves ⊢ nat_mod(m, n) = <literal> for BIT-tree literals (n > 0).
func NormNatMod(m, n Term) (*prop.PropWrapper, bool) { return divmodEval(m, n, false) }

// norm_num comparison: proof-producing decision of `<`, `≤`, `=`
// between numeral literals, returning ⊢ (m ⋈ n) ⇔ ⊤ or ⊢ (m ⋈ n) ⇔ ⊥.
//
// Bit recursion (base equivalences): a comparison of two BIT-trees
// either terminates at a ⊤/⊥ leaf or reduces — via base.EqTrans(rec) — to a
// strictly smaller comparison. `<` and `≤` are mutually recursive; `=` is
// self-recursive. Each call strips ≥1 BIT, so |x|+|y| decreases: termination.

// ltBits proves ⊢ (x < y) ⇔ ⊤/⊥ for BIT-trees x, y.
func ltBits(x, y Term) *prop.PropWrapper {
	if isZeroBit(x) {
		if isZeroBit(y) {
			return ltZeroZero()
		}
		if b, ok := asBit0(y); ok {
			return ltZeroB0(b).EqTrans(ltBits(natZero, b))
		}
		if b, ok := asBit1(y); ok {
			return ltZeroB1(b)
		}
	}
	if isZeroBit(y) {
		if a, ok := asBit0(x); ok {
			return ltB0Zero(a)
		}
		if a, ok := asBit1(x); ok {
			return ltB1Zero(a)
		}
	}
	xa, x0 := asBit0(x)
	xb, x1 := asBit1(x)
	ya, y0 := asBit0(y)
	yb, y1 := asBit1(y)
	switch {
	case x0 && y0:
		return ltB0B0(xa, ya).EqTrans(ltBits(xa, ya))
	case x0 && y1:
		return ltB0B1(xa, yb).EqTrans(leBits(xa, yb)) // 2a < 2b+1 ⇔ a ≤ b
	case x1 && y0:
		return ltB1B0(xb, ya).EqTrans(ltBits(xb, ya))
	case x1 && y1:
		return ltB1B1(xb, yb).EqTrans(ltBits(xb, yb))
	}
	panic("ltBits: not a BIT-tree")
}

// leBits proves ⊢ (x ≤ y) ⇔ ⊤/⊥ for BIT-trees x, y.
func leBits(x, y Term) *prop.PropWrapper {
	if isZeroBit(x) {
		return leZeroAny(y) // 0 ≤ y always
	}
	if isZeroBit(y) {
		if a, ok := asBit0(x); ok {
			return leB0Zero(a).EqTrans(leBits(a, natZero)) // 2a ≤ 0 ⇔ a ≤ 0
		}
		if a, ok := asBit1(x); ok {
			return leB1Zero(a)
		}
	}
	xa, x0 := asBit0(x)
	xb, x1 := asBit1(x)
	ya, y0 := asBit0(y)
	yb, y1 := asBit1(y)
	switch {
	case x0 && y0:
		return leB0B0(xa, ya).EqTrans(leBits(xa, ya))
	case x0 && y1:
		return leB0B1(xa, yb).EqTrans(leBits(xa, yb))
	case x1 && y0:
		return leB1B0(xb, ya).EqTrans(ltBits(xb, ya)) // 2a+1 ≤ 2b ⇔ a < b
	case x1 && y1:
		return leB1B1(xb, yb).EqTrans(leBits(xb, yb))
	}
	panic("leBits: not a BIT-tree")
}

// eqBits proves ⊢ (x = y) ⇔ ⊤/⊥ for BIT-trees x, y.
func eqBits(x, y Term) *prop.PropWrapper {
	if isZeroBit(x) {
		if isZeroBit(y) {
			return eqZeroZero()
		}
		if b, ok := asBit0(y); ok {
			return eqZeroB0(b).EqTrans(eqBits(natZero, b))
		}
		if b, ok := asBit1(y); ok {
			return eqZeroB1(b)
		}
	}
	if isZeroBit(y) {
		if a, ok := asBit0(x); ok {
			return eqB0Zero(a).EqTrans(eqBits(a, natZero))
		}
		if a, ok := asBit1(x); ok {
			return eqB1Zero(a)
		}
	}
	xa, x0 := asBit0(x)
	xb, x1 := asBit1(x)
	ya, y0 := asBit0(y)
	yb, y1 := asBit1(y)
	switch {
	case x0 && y0:
		return eqB0B0(xa, ya).EqTrans(eqBits(xa, ya))
	case x0 && y1:
		return eqB0B1(xa, yb)
	case x1 && y0:
		return eqB1B0(xb, ya)
	case x1 && y1:
		return eqB1B1(xb, yb).EqTrans(eqBits(xb, yb))
	}
	panic("eqBits: not a BIT-tree")
}

// liftNumeralCmp runs the raw bit comparison `eval(l, r) ⊢ (l ⋈ r) ⇔ ⊤/⊥`
// directly when l, r are BIT-tree literals.
func liftNumeralCmp(l, r Term, eval func(x, y Term) *prop.PropWrapper) (*prop.PropWrapper, bool) {
	if !isBitTree(l) || !isBitTree(r) {
		return nil, false
	}
	return eval(l, r), true
}

// NormNatLt proves ⊢ (l < r) ⇔ ⊤/⊥ for BIT-tree literals l, r.
func NormNatLt(l, r Term) (*prop.PropWrapper, bool) { return liftNumeralCmp(l, r, ltBits) }

// NormNatLe proves ⊢ (l ≤ r) ⇔ ⊤/⊥ for BIT-tree literals l, r.
func NormNatLe(l, r Term) (*prop.PropWrapper, bool) { return liftNumeralCmp(l, r, leBits) }

// NormNatEq proves ⊢ (l = r) ⇔ ⊤/⊥ for BIT-tree literals l, r.
func NormNatEq(l, r Term) (*prop.PropWrapper, bool) { return liftNumeralCmp(l, r, eqBits) }

// Derived numeral comparisons: `>`, `≥`, `≠` reduce to the primitive `<`, `≤`,
// `=` evaluators (above) — no new recursion.
//
//   m > n  ⇔  n < m         (GT def, gtBridge + operand swap)
//   m ≥ n  ⇔  n ≤ m         (GE def, geBridge + operand swap)
//   m ≠ n  ⇔  ¬(m = n)      (≠ is ¬(=); negate the eq verdict)
//
// The not-clauses closing `≠` (prop.NotTrue ⊢ ¬⊤⇔⊥, prop.NotFalse ⊢ ¬⊥⇔⊤) are
// REAL proven theorems, so `≠` adds no placeholder beyond the eq base lemmas.

// NormNatGt proves ⊢ (l > r) ⇔ ⊤/⊥ for numeral literals l, r.
func NormNatGt(l, r Term) (*prop.PropWrapper, bool) {
	sub, ok := NormNatLt(r, l) // ⊢ (r < l) ⇔ V
	if !ok {
		return nil, false
	}
	return gtBridge(l, r).EqTrans(sub), true // ⊢ (l > r) ⇔ (r < l) ⇔ V
}

// NormNatGe proves ⊢ (l ≥ r) ⇔ ⊤/⊥ for numeral literals l, r.
func NormNatGe(l, r Term) (*prop.PropWrapper, bool) {
	sub, ok := NormNatLe(r, l) // ⊢ (r ≤ l) ⇔ V
	if !ok {
		return nil, false
	}
	return geBridge(l, r).EqTrans(sub), true
}

// NormNatNe proves ⊢ ¬(l = r) ⇔ ⊤/⊥ for numeral literals l, r.
func NormNatNe(l, r Term) (*prop.PropWrapper, bool) {
	sub, ok := NormNatEq(l, r) // ⊢ (l = r) ⇔ V
	if !ok {
		return nil, false
	}
	neg := sub.LeftApply(prop.NOT) // ⊢ ¬(l = r) ⇔ ¬V
	if prop.Rhs(sub).Equals(prop.T) {
		return neg.EqTrans(prop.NotTrue), true // ¬⊤ ⇔ ⊥
	}
	return neg.EqTrans(prop.NotFalse), true // ¬⊥ ⇔ ⊤
}

// Comparison consts and the per-constructor base equivalences for the numeral
// comparison decision.
//
// Same bundle discipline as nat_lemmas.go: each closure is the irreducible
// bit-recursion step, proved once, read from the bundle's comparison
// decision theorem (a nil field degrades to a test-only placeholder stand-in,
// bundle.go). The recursive composition here is real kernel
// work.
//
// A comparison reduces to a SMALLER comparison or terminates at ⊤/⊥:
//   <  on (bit0 a, bit1 b) reduces to (a ≤ b)   — so < depends on ≤
//   ≤  on (bit1 a, bit0 b) reduces to (a < b)   — so ≤ depends on <  (mutual)
//   =  is self-recursive.
// ────────────────────────────────────────────────────────────────────

var (
	natLt = dsl.NatLtMeta.Term()
	natLe = dsl.NatLeMeta.Term()
	natGt = dsl.NatGtMeta.Term()
	natGe = dsl.NatGeMeta.Term()
)

func lt(x, y Term) Term  { return ext.Apply(natLt, x, y) }
func le(x, y Term) Term  { return ext.Apply(natLe, x, y) }
func gt(x, y Term) Term  { return ext.Apply(natGt, x, y) }
func ge(x, y Term) Term  { return ext.Apply(natGe, x, y) }
func eqT(x, y Term) Term { return core.Eq(x, y) }

// gtBridge / geBridge: the definitional reductions of `>` / `≥` to swapped
// `<` / `≤` (real: GT / GE defs). `≠` needs no bridge — it IS ¬(=), so
// NormNatNe negates the eq verdict with the real prop.NotTrue/NotFalse.
//
// The bound GT/GE defs (normalized) carry the strict/large relation on the SECOND
// binder applied to SWAPPED args — GE is `∀a b. (a≤b) ⇔ (b≥a)`, GT is
// `∀a b. (a<b) ⇔ (b>a)` — so to land on the `x≥y` / `x>y` direction the def must
// be instantiated at [y, x], NOT [x, y]. Instantiating at [x,y] produces the
// bridge for `y≥x` / `y>x` (the wrong atom), which macroEq cannot orient to the
// wanted shape → degrades to the placeholder seam, which PANICS in a non-test
// build. The bug was masked because a test fabricator produces the wanted shape
// directly, and no fabricator-free test exercised `≥`/`>` (TestGtGeBridge now does).
func gtBridge(x, y Term) *prop.PropWrapper {
	return eqLeaf(gtDefThm(), []Term{y, x}, gt(x, y), lt(y, x))
}
func geBridge(x, y Term) *prop.PropWrapper {
	return eqLeaf(geDefThm(), []Term{y, x}, ge(x, y), le(y, x))
}

// sucLessEqIffLessThan: ⊢ (M < N) ⇔ (suc M ≤ N)   (real: SucLessEqIffLessThan). The strict→non-strict
// bridge used by the integer rounding cut to rewrite a `<` row's proof into the
// `suc M ≤ N` shape (ring then folds suc M = M+1) before the cut.
func sucLessEqIffLessThan(m, n Term) *prop.PropWrapper {
	return eqLeaf(sucLessEqIffLessThanThm(), []Term{m, n}, lt(m, n), le(sucT(m), n))
}

// iffThm: ⊢ p ⇔ q   (⇔ is `=` on bool), as a placeholder stand-in for cmpLeaf's
// degrade path. `thm` is the bundle field cmpLeaf failed to project from (nil
// when unbundled) — threaded through so the seam panic names the right cause.
func iffThm(thm *prop.PropWrapper, p, q Term) *prop.PropWrapper {
	return placeholderEq(thm, p, q)
}

// cmpLeaf returns the conjunct of the bundle decision theorem `arithThm` that
// reduces `targetLHS` (instantiated at args, projected via this file),
// or the placeholder iff `targetLHS ⇔ reduced` when no bundle is installed.
// clauseLeaf binds a `targetLHS = reduced` identity to a conjunct of a
// clause-pack equality theorem (MulClauses / AddClauses), via projectMatch
// (uniform instantiation + either-orientation), or the placeholder when no
// bundle is installed. `fill` is the single atom the clause's variable is set to
// (= the target's atom). A bundle-nil/mis-shaped degrade panics in production
// (bundle.go).
func clauseLeaf(clausesThm *prop.PropWrapper, _ Term, targetLHS, reduced Term) *prop.PropWrapper {
	if clausesThm != nil {
		if w, ok := projectMatch(clausesThm, targetLHS, reduced); ok {
			return w
		}
	}
	return placeholderEq(clausesThm, targetLHS, reduced)
}

func cmpLeaf(arithThm *prop.PropWrapper, _ []Term, targetLHS, reduced Term) *prop.PropWrapper {
	if arithThm != nil {
		if w, ok := projectMatch(arithThm, targetLHS, reduced); ok {
			return w
		}
	}
	return iffThm(arithThm, targetLHS, reduced)
}

// ── `<` base equivalences (project from NumeralLessThan) ────────────────────────────
func ltZeroZero() *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), nil, lt(natZero, natZero), prop.F)
}
func ltZeroB0(b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), []Term{b}, lt(natZero, bit0(b)), lt(natZero, b))
}
func ltZeroB1(b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), []Term{b}, lt(natZero, bit1(b)), prop.T)
}
func ltB0Zero(a Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), []Term{a}, lt(bit0(a), natZero), prop.F)
}
func ltB1Zero(a Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), []Term{a}, lt(bit1(a), natZero), prop.F)
}
func ltB0B0(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), []Term{a, b}, lt(bit0(a), bit0(b)), lt(a, b))
}
func ltB0B1(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), []Term{a, b}, lt(bit0(a), bit1(b)), le(a, b))
}
func ltB1B0(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), []Term{a, b}, lt(bit1(a), bit0(b)), lt(a, b))
}
func ltB1B1(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessThanThm(), []Term{a, b}, lt(bit1(a), bit1(b)), lt(a, b))
}

// ── `≤` base equivalences (project from NumeralLessEq) ────────────────────────────
func leZeroAny(y Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessEqThm(), []Term{y}, le(natZero, y), prop.T)
}
func leB0Zero(a Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessEqThm(), []Term{a}, le(bit0(a), natZero), le(a, natZero))
}
func leB1Zero(a Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessEqThm(), []Term{a}, le(bit1(a), natZero), prop.F)
}
func leB0B0(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessEqThm(), []Term{a, b}, le(bit0(a), bit0(b)), le(a, b))
}
func leB0B1(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessEqThm(), []Term{a, b}, le(bit0(a), bit1(b)), le(a, b))
}
func leB1B0(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessEqThm(), []Term{a, b}, le(bit1(a), bit0(b)), lt(a, b))
}
func leB1B1(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralLessEqThm(), []Term{a, b}, le(bit1(a), bit1(b)), le(a, b))
}

// ── `=` base equivalences (project from NumeralEq) ────────────────────────────

// eqZeroZero: ⊢ (0 = 0) ⇔ ⊤. Proved by REFLEXIVITY, not projected — the corpus
// NumeralEq has no `0=0` conjunct (that base case closes by refl), so
// projecting would degrade. Refl is a real kernel axiom, so this is sound in both
// placeholder and real-corpus modes and needs no bundle field.
func eqZeroZero() *prop.PropWrapper {
	return eqtIntro(prop.Refl(natZero)) // ⊢ 0=0, lifted to ⇔ ⊤
}
func eqZeroB0(b Term) *prop.PropWrapper {
	return cmpLeaf(numeralEqThm(), []Term{b}, eqT(natZero, bit0(b)), eqT(natZero, b))
}
func eqZeroB1(b Term) *prop.PropWrapper {
	return cmpLeaf(numeralEqThm(), []Term{b}, eqT(natZero, bit1(b)), prop.F)
}
func eqB0Zero(a Term) *prop.PropWrapper {
	return cmpLeaf(numeralEqThm(), []Term{a}, eqT(bit0(a), natZero), eqT(a, natZero))
}
func eqB1Zero(a Term) *prop.PropWrapper {
	return cmpLeaf(numeralEqThm(), []Term{a}, eqT(bit1(a), natZero), prop.F)
}
func eqB0B0(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralEqThm(), []Term{a, b}, eqT(bit0(a), bit0(b)), eqT(a, b))
}
func eqB0B1(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralEqThm(), []Term{a, b}, eqT(bit0(a), bit1(b)), prop.F)
}
func eqB1B0(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralEqThm(), []Term{a, b}, eqT(bit1(a), bit0(b)), prop.F)
}
func eqB1B1(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralEqThm(), []Term{a, b}, eqT(bit1(a), bit1(b)), eqT(a, b))
}

// Projection machinery for the named arithmetic conjunctions (AddClauses /
// MulClauses and the NumeralAdd/NumeralSuc/NumeralMul/NumeralLessThan/NumeralLessEq/NumeralEq bit-recursion theorems):
// given a proved conjunction theorem, pull out the conjunct whose stated
// equality/iff matches a target shape and instantiate it. The
// Numeral* decision theorems are stated wholesale (a clean consolidated conjunction of the
// per-bit reduction rules), so the work here is shape-matching the right
// conjunct rather than hand-deriving it. The production entry point is
// projectMatch (consumed by cmpLeaf/clauseLeaf in this file and the
// Sub / nat_pow / factorial clause leaves); splitConjuncts is also used by domain.go
// to flatten a conjunctive hypothesis into its proved leaves.

// splitConjuncts decomposes a proved ⊢ C0 ∧ C1 ∧ … into its proved conjuncts,
// projecting each via the AND-elimination lemmas (HypAND0/1 + DeriveTrans).
func splitConjuncts(p *prop.PropWrapper) []*prop.PropWrapper {
	a, b, ok := prop.MatchesAND(p.Conclusion())
	if !ok {
		return []*prop.PropWrapper{p}
	}
	head := p.DeriveTrans(prop.HypAND0(a, b)) // ⊢ a
	tail := p.DeriveTrans(prop.HypAND1(a, b)) // ⊢ b
	// Recurse into BOTH sides: a conjunction may be left-nested
	// (((c1∧c2)∧c3)…) — as the normalized MulClauses/AddClauses are — not just
	// right-nested, so peeling only the tail would leave a conjunction blob in
	// the head. Recursing both ways flattens any association.
	return append(splitConjuncts(head), splitConjuncts(tail)...)
}

// projectMatch is the robust projector for the named arithmetic conjunctions
// (MulClauses / AddClauses and the NumeralAdd/NumeralMul/NumeralLessThan/NumeralLessEq/NumeralEq bit-recursion
// theorems). It finds the conjunct whose targetLHS first-order-matches EITHER
// side (treating the theorem's leading ∀-bound vars as metavariables) and
// returns it instantiated and oriented to ⊢ targetLHS = _ (⇔ for the comparison
// theorems). Unlike the old positional/LHS-only projection it is independent of
// binder order/count, the reversed orientation many clauses are stated in
// (`n = 1·n`), and conjunction association (with the both-sides splitConjuncts).
//
// Each leading ∀ is instantiated with its OWN bound var, which thereby becomes
// free and serves as the metavar; matchFOEqCommute then solves the binder→atom
// map and TermInst specializes the conjunct to the concrete target.
func projectMatch(thm *prop.PropWrapper, targetLHS, reduced Term) (*prop.PropWrapper, bool) {
	// Strip leading ∀ (the corpus Numeral* / *Clauses form), then per conjunct strip
	// any conjunct-local ∀ (the independently-quantified form). Each
	// instantiated bound var becomes free and serves as a metavar.
	w, base := stripForalls(thm, nil)
	for _, c := range splitConjuncts(w) {
		cc, metas := stripForalls(c, base)
		l, r, ok := prop.MatchesEQ(cc.Conclusion())
		if !ok {
			// Terminal conjunct stated as a BARE fact (P or ¬P), not an
			// equality/iff: NumeralLessThan/NumeralLessEq/NumeralEq state their base cases this way
			// (¬(0<0), 0<bit1 l, 0≠bit1 n). Wrap to the (targetLHS ⇔ reduced)
			// the comparison leaves expect.
			if pw, ok := projectBareFact(cc, metas, targetLHS, reduced); ok {
				return pw, true
			}
			continue
		}
		// Match BOTH sides under ONE substitution: this disambiguates the
		// trivial (bare-metavar) side — which would otherwise greedily bind to
		// the whole target — and picks the correct orientation (many
		// clauses are stated reversed, e.g. `n = 1·n`). EqSym when targetLHS lands on the
		// right.
		if sub, ok := matchBoth(l, targetLHS, r, reduced, metas); ok {
			return reorientIff(cc.TermInst(sub...), targetLHS, reduced), true
		}
		if sub, ok := matchBoth(l, reduced, r, targetLHS, metas); ok {
			return reorientIff(cc.TermInst(sub...).EqSym(), targetLHS, reduced), true
		}
	}
	return nil, false
}

// projectBareFact handles NumeralLessThan/NumeralLessEq/NumeralEq's terminal conjuncts, which the bound
// statements carry as BARE facts (P or ¬P) rather than the P⇔⊤ / P⇔⊥ form the comparison
// leaves expect (cmpLeaf wants ⊢ targetLHS ⇔ reduced). It FO-matches the bare
// conjunct `cc` (its binders already turned into metavars) against the target and
// wraps the instantiated fact via eqtIntro / eqfIntro:
//
//	reduced = ⊤ : conjunct is a bare C with C ≟ targetLHS        → ⊢ targetLHS ⇔ ⊤
//	reduced = ⊥ : conjunct is ¬C with C ≟ targetLHS              → ⊢ targetLHS ⇔ ⊥
//
// For the symmetric `=` the bound statement carries only one of `0 ≠ bit1 n` / `bit0 m ≠
// bit1 n`, while eqB1Zero / eqB1B0 ask the flipped `bit1 a = 0` / `bit1 a = bit0 b`:
// matchFOEqCommute matches the conjunct regardless of inner `=` orientation, and
// reorientIff flips the resulting iff's LHS back to the leaf's orientation.
func projectBareFact(cc *prop.PropWrapper, metas map[core.TermName]core.VarTerm, targetLHS, reduced Term) (*prop.PropWrapper, bool) {
	concl := cc.Conclusion()
	switch {
	case reduced.AlphaEquals(prop.T):
		if sub, ok := matchBoth(concl, targetLHS, nil, nil, metas); ok {
			return reorientIff(eqtIntro(cc.TermInst(sub...)), targetLHS, reduced), true
		}
	case reduced.AlphaEquals(prop.F):
		inner := prop.MatchesNOT(concl)
		if inner == nil {
			return nil, false
		}
		if sub, ok := matchBoth(inner, targetLHS, nil, nil, metas); ok {
			return reorientIff(eqfIntro(cc.TermInst(sub...)), targetLHS, reduced), true
		}
	}
	return nil, false
}

// reorientIff repairs the inner-equality orientation of a projected iff so its two
// sides exactly match (wantL, wantR). matchFOEqCommute FINDS a conjunct whose
// inner equality is stated in the corpus's orientation (`0 = bit0 k`); this
// flips each side back to the leaf's orientation (`bit0 a = 0`) via CommuteEQ.
// No-op for sides that are not equalities or already aligned.
func reorientIff(w *prop.PropWrapper, wantL, wantR Term) *prop.PropWrapper {
	gotL, gotR, ok := prop.MatchesEQ(w.Conclusion())
	if !ok {
		return w
	}
	if pl, pr, ok := prop.MatchesEQ(gotL); ok && !gotL.AlphaEquals(wantL) && eqT(pr, pl).AlphaEquals(wantL) {
		w = prop.CommuteEQ(pr, pl).EqTrans(w) // (q=p)⇔(p=q) ∘ (p=q)⇔Y = (q=p)⇔Y
	}
	if pl, pr, ok := prop.MatchesEQ(gotR); ok && !gotR.AlphaEquals(wantR) && eqT(pr, pl).AlphaEquals(wantR) {
		w = w.EqTrans(prop.CommuteEQ(pl, pr)) // X⇔(p=q) ∘ (p=q)⇔(q=p) = X⇔(q=p)
	}
	return w
}

// eqtIntro: ⊢ C  →  ⊢ C ⇔ ⊤   (via BooleanThms `(p⇔⊤)⇔p`).
func eqtIntro(pf *prop.PropWrapper) *prop.PropWrapper {
	return prop.BooleanThms["p ⇔ ⊤"](pf.Conclusion()).EqSym().EqMP(pf)
}

// iffTrueElim: ⊢ C ⇔ ⊤  →  ⊢ C   (inverse of eqtIntro; strips a proven `⇔ ⊤`).
func iffTrueElim(pf *prop.PropWrapper) *prop.PropWrapper {
	return prop.BooleanThms["p ⇔ ⊤"](prop.Lhs(pf)).EqMP(pf)
}

// eqfIntro: ⊢ ¬C  →  ⊢ C ⇔ ⊥   (via BooleanThms `(p⇔⊥)⇔¬p`).
func eqfIntro(pf *prop.PropWrapper) *prop.PropWrapper {
	c := prop.MatchesNOT(pf.Conclusion())
	return prop.BooleanThms["p ⇔ ⊥"](c).EqSym().EqMP(pf)
}

// stripForalls is the metavar-map view of prop's StripConclForAll:
// it strips every leading ∀ of p — each binder freed and turned into a metavar —
// and returns the body plus the metavar set (a copy of `base` extended with the
// stripped binders, keyed by name so matchFOEqCommute can rebuild the
// substitution targets).
func stripForalls(p *prop.PropWrapper, base map[core.TermName]core.VarTerm) (*prop.PropWrapper, map[core.TermName]core.VarTerm) {
	metas := make(map[core.TermName]core.VarTerm, len(base))
	for k, v := range base {
		metas[k] = v
	}
	body, vars := p.StripConclForAll()
	for _, v := range vars {
		metas[v.Name()] = v
	}
	return body, metas
}

// matchBoth first-order-matches (pl ≟ tl) AND (pr ≟ tr) under a SHARED binding
// of the metavars, returning the substitution. A nil target pattern is an
// unconstrained wildcard (used by projectBareFact's single-side match).
func matchBoth(pl, tl, pr, tr Term, metas map[core.TermName]core.VarTerm) ([]core.TermSubst, bool) {
	inst := unify.TermNameSet{}
	for n := range metas {
		inst.Add(n)
	}
	bind := unify.MatchBindings{}
	if tl != nil && !matchFOEqCommute(pl, tl, inst, bind) {
		return nil, false
	}
	if tr != nil && !matchFOEqCommute(pr, tr, inst, bind) {
		return nil, false
	}
	subs := make([]core.TermSubst, 0, len(bind))
	for name, t := range bind {
		subs = append(subs, core.MakeTermSubst(metas[name], t))
	}
	return subs, true
}

// matchFOEqCommute matches `pat` against `tgt` treating `instantiable` vars as
// flexible (FO) and `=` as commutative at EVERY nesting level — the corpus
// states many equations in the opposite orientation from omega's leaves
// (`0 = bit0 k` vs the leaf's `bit0 a = 0`), and the inversion can be buried
// (an iff between two equalities, an equality conjoined with another). The
// recursive structural descent is unify.TermMatchWith; the swap-with-backtrack
// is injected as a per-node hook so it fires at every `=` the descent crosses.
// reorientIff then repairs the iff's result side.
func matchFOEqCommute(pat, tgt Term, instantiable unify.TermNameSet, bind unify.MatchBindings) bool {
	hook := func(p, t Term, b unify.MatchBindings, recurse unify.MatchRecurse) (handled, ok bool) {
		pl, pr, pok := prop.MatchesEQ(p)
		if !pok {
			return false, false
		}
		tl, tr, tok := prop.MatchesEQ(t)
		if !tok {
			return true, false
		}
		snap := snapshotBindings(b)
		if recurse(pl, tl, b) && recurse(pr, tr, b) {
			return true, true
		}
		restoreBindings(b, snap)
		if recurse(pl, tr, b) && recurse(pr, tl, b) {
			return true, true
		}
		restoreBindings(b, snap)
		return true, false
	}
	return unify.TermMatchWith(pat, tgt, instantiable, bind, hook)
}

func snapshotBindings(b unify.MatchBindings) unify.MatchBindings {
	out := make(unify.MatchBindings, len(b))
	for k, v := range b {
		out[k] = v
	}
	return out
}

func restoreBindings(b, snap unify.MatchBindings) {
	for k := range b {
		delete(b, k)
	}
	for k, v := range snap {
		b[k] = v
	}
}

// instAll is omega's `[]Term`-spelling of prop's ConclForAllInsts:
// instantiate leading ∀'s at successive args, stopping when args are exhausted or
// the conclusion is no longer ∀-headed.
func instAll(p *prop.PropWrapper, args []Term) *prop.PropWrapper {
	return p.ConclForAllInsts(args...)
}
