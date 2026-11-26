package omega

import (
	"github.com/euc-ai/xugo/ext/prop"
)

// commuteADD: ⊢ a + b = b + a   (real: AddSym)
func commuteADD(a, b Term) *prop.PropWrapper {
	return eqLeaf(addSymThm(), []Term{a, b}, plus(a, b), plus(b, a))
}

// associateADD: ⊢ (a + b) + c = a + (b + c)   (real: AddAssoc, reversed)
func associateADD(a, b, c Term) *prop.PropWrapper {
	return eqLeaf(addAssocThm(), []Term{a, b, c}, plus(plus(a, b), c), plus(a, plus(b, c)))
}

// commuteMUL: ⊢ a * b = b * a   (real: MulSym)
func commuteMUL(a, b Term) *prop.PropWrapper {
	return eqLeaf(mulSymThm(), []Term{a, b}, star(a, b), star(b, a))
}

// associateMUL: ⊢ (a * b) * c = a * (b * c)   (real: MulAssoc, reversed)
func associateMUL(a, b, c Term) *prop.PropWrapper {
	return eqLeaf(mulAssocThm(), []Term{a, b, c}, star(star(a, b), c), star(a, star(b, c)))
}

// distributeMUL: ⊢ a * (b + c) = a * b + a * c   (real: LeftAddDistrib)
//
// Shape required by DistributeRewrite: outer op `*`, inner op `+`, producing
// the push-through of a single product over a sum.
func distributeMUL(a, b, c Term) *prop.PropWrapper {
	return eqLeaf(leftAddDistribThm(), []Term{a, b, c}, star(a, plus(b, c)), plus(star(a, b), star(a, c)))
}

// sucAdd1: ⊢ suc x = x + 1   (real: Add1). The successor→coefficient bridge
// that lets linOf/normalizeProof fold `suc` into a linear form (ring.go),
// so `b < suc a` is recognized as the linear `b < a+1`.
func sucAdd1(x Term) *prop.PropWrapper {
	return eqLeaf(add1Thm(), []Term{x}, sucT(x), plus(x, Numeral(1)))
}

// ── Numeral (BIT-tree) base equations for norm_num ───────────────────────────
// Same PLACEHOLDER discipline: these are the irreducible per-constructor
// recursion equations, proved once (arith's Numeral* members). Each
// leaf binds its bundle ∀-theorem and ConclForAllInst's it at the operand
// sub-trees. The recursive *composition* of these (nat_norm.go) is real kernel
// work and is sound the moment the leaves are.
//
// Operate on raw BIT-trees; _0 is the zero bit-leaf natZero.

// zeroAddBits: ⊢ _0 + n = n   (real: AddClauses, _0 case)
func zeroAddBits(n Term) *prop.PropWrapper {
	return clauseLeaf(addClausesThm(), n, plus(natZero, n), n)
}

// addBitsZero: ⊢ n + _0 = n   (real: AddClauses, +_0 case)
func addBitsZero(n Term) *prop.PropWrapper {
	return clauseLeaf(addClausesThm(), n, plus(n, natZero), n)
}

// The bit-recursion add / suc / mult leaves project the matching conjunct out of
// the bundle's named NumeralAdd / NumeralSuc / NumeralMul (via cmpLeaf, like the
// comparison leaves), and fall back to the placeholder statement otherwise.
// They are NOT derived via ring: ring folds numeral coefficients through
// norm_num, which IS these leaves — that path is circular.

// addB0B0: ⊢ bit0 a + bit0 b = bit0 (a + b)
func addB0B0(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralAddThm(), []Term{a, b}, plus(bit0(a), bit0(b)), bit0(plus(a, b)))
}

// addB0B1: ⊢ bit0 a + bit1 b = bit1 (a + b)
func addB0B1(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralAddThm(), []Term{a, b}, plus(bit0(a), bit1(b)), bit1(plus(a, b)))
}

// addB1B0: ⊢ bit1 a + bit0 b = bit1 (a + b)
func addB1B0(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralAddThm(), []Term{a, b}, plus(bit1(a), bit0(b)), bit1(plus(a, b)))
}

// addB1B1: ⊢ bit1 a + bit1 b = bit0 (suc (a + b))
func addB1B1(a, b Term) *prop.PropWrapper {
	return cmpLeaf(numeralAddThm(), []Term{a, b}, plus(bit1(a), bit1(b)), bit0(sucT(plus(a, b))))
}

// sucBitsZero: ⊢ suc _0 = bit1 _0
func sucBitsZero() *prop.PropWrapper {
	return cmpLeaf(numeralSucThm(), nil, sucT(natZero), bit1(natZero))
}

// sucB0: ⊢ suc (bit0 a) = bit1 a
func sucB0(a Term) *prop.PropWrapper {
	return cmpLeaf(numeralSucThm(), []Term{a}, sucT(bit0(a)), bit1(a))
}

// sucB1: ⊢ suc (bit1 a) = bit0 (suc a)
func sucB1(a Term) *prop.PropWrapper {
	return cmpLeaf(numeralSucThm(), []Term{a}, sucT(bit1(a)), bit0(sucT(a)))
}

// mulZeroBits: ⊢ _0 * n = _0   (real: MulClauses, 0* case)
func mulZeroBits(n Term) *prop.PropWrapper {
	return clauseLeaf(mulClausesThm(), n, star(natZero, n), natZero)
}

// mulBitsZero: ⊢ n * _0 = _0   (real: MulClauses, *0 case)
//
// Needed so multiply-by-zero terminates at _0 instead of wrapping zero subtrees
// into non-canonical bit0(…bit0 _0…). With this guard, every deeper mulBits
// call carries a non-zero right operand, which keeps the bit0/bit1 results
// canonical (and lets addBits clean any transient leading bit0 _0).
func mulBitsZero(n Term) *prop.PropWrapper {
	return clauseLeaf(mulClausesThm(), n, star(n, natZero), natZero)
}

// bit0Eq: ⊢ bit0 x = x + x   (real: Bit0, on bare BIT-trees).
func bit0Eq(x Term) *prop.PropWrapper {
	return eqLeaf(bit0Thm(), []Term{x}, bit0(x), plus(x, x))
}

// bit1Eq: ⊢ bit1 x = suc (x + x)   (real: Bit1, on bare BIT-trees).
func bit1Eq(x Term) *prop.PropWrapper {
	return eqLeaf(bit1Thm(), []Term{x}, bit1(x), sucT(plus(x, x)))
}

// sucMulL: ⊢ suc k * l = k * l + l   (real: the MulClauses suc-on-left clause).
func sucMulL(k, l Term) *prop.PropWrapper {
	return clauseLeaf(mulClausesThm(), nil, star(sucT(k), l), plus(star(k, l), l))
}

// mulB0: ⊢ bit0 a * n = bit0 (a * n). DERIVED (NumeralMul recurses on both
// operands, so it cannot supply this left-only step): bit0 a · n = (a+a)·n =
// a·n + a·n = bit0(a·n), via Bit0 + RightAddDistrib. No norm_num recursion,
// so no circularity with the coefficient folding ring drives through these leaves.
func mulB0(a, n Term) *prop.PropWrapper {
	an := star(a, n)
	return bit0Eq(a).LeftApply(natStar).RightApply(n). // bit0 a · n = (a+a)·n
								EqTrans(rightDistrib(a, a, n)). // = a·n + a·n
								EqTrans(bit0Eq(an).EqSym())     // = bit0(a·n)
}

// mulB1: ⊢ bit1 a * n = bit0 (a * n) + n. DERIVED: bit1 a · n = suc(a+a)·n =
// (a+a)·n + n = (a·n + a·n) + n = bit0(a·n) + n, via Bit1 + the MulClauses
// suc clause + RightAddDistrib + Bit0.
func mulB1(a, n Term) *prop.PropWrapper {
	an := star(a, n)
	return bit1Eq(a).LeftApply(natStar).RightApply(n). // bit1 a · n = suc(a+a)·n
								EqTrans(sucMulL(plus(a, a), n)).                                 // = (a+a)·n + n
								EqTrans(rightDistrib(a, a, n).LeftApply(natPlus).RightApply(n)). // = (a·n+a·n) + n
								EqTrans(bit0Eq(an).EqSym().LeftApply(natPlus).RightApply(n))     // = bit0(a·n) + n
}

// ── Semiring identity / distribution lemmas for ring ─────────────────────────
// Same PLACEHOLDER discipline. Reuses associateADD/commuteADD/associateMUL/
// commuteMUL/distributeMUL above.

// oneMulL: ⊢ 1 * a = a   (real: MulClauses)
func oneMulL(a Term) *prop.PropWrapper {
	return clauseLeaf(mulClausesThm(), a, star(Numeral(1), a), a)
}

// addZeroR: ⊢ a + 0 = a   (real: AddClauses)
func addZeroR(a Term) *prop.PropWrapper {
	return clauseLeaf(addClausesThm(), a, plus(a, Numeral(0)), a)
}

// zeroMulNum: ⊢ 0 * a = 0   (real: MulClauses)
func zeroMulNum(a Term) *prop.PropWrapper {
	return clauseLeaf(mulClausesThm(), a, star(Numeral(0), a), Numeral(0))
}

// rightDistrib: ⊢ (a + b) * c = a * c + b * c   (real: RightAddDistrib).
// Used reversed to combine like terms: c₁·a + c₂·a = (c₁+c₂)·a.
func rightDistrib(a, b, c Term) *prop.PropWrapper {
	return eqLeaf(rightAddDistribThm(), []Term{a, b, c}, star(plus(a, b), c), plus(star(a, c), star(b, c)))
}

// mulZeroR: ⊢ x · 0 = 0   (real: MulClauses; drops a multiply-by-0 monomial).
func mulZeroR(x Term) *prop.PropWrapper {
	return clauseLeaf(mulClausesThm(), x, star(x, Numeral(0)), Numeral(0))
}

// NatLemmaBundle is the single injection seam through which omega's leaves obtain
// the named library theorems they derive from. serve.InstallNatBundle constructs
// one from the chapter corpus at startup and installs it via SetNatLemmaBundle;
// every field is an independent ∀-theorem (or named conjunction), so the bundle
// can be populated incrementally — a leaf whose theorem is present derives a real
// kernel proof, a leaf whose field is still nil falls back to a placeholder
// stand-in (bundle.go: the fabricator is test-only, so core.TestThm never
// enters the production build; in a non-test build a bundle-nil leaf panics at
// the placeholder seam instead of fabricating). The no-bundle, placeholder-
// everywhere mode is the algorithm-test / search configuration.
//
// The seam lets a lower layer use library material without taking the library
// as a dependency or threading it through every call. Once the bundle is filled with real Thm, omega is fully sound —
// no code change, only theorem population, remains.
//
// A field carries the name of the library member whose statement it holds:
// LessEqAdd2 is nat_order.LessEqAdd2, DivModUniq is nat_div_mod.DivModUniq. A
// field no member states — an operator's definition (MaxDef), a form the
// install derives from a member (LessEqOfEqSwapped, LessEqMulMono) — is named
// in the same style, beside the member it comes from. IntLemmaBundle and
// RealLemmaBundle follow the same rule, each against its own chapters.
type NatLemmaBundle struct {
	// Ring AC + clauses.
	AddSym, AddAssoc, MulSym, MulAssoc *prop.PropWrapper
	AddClauses, MulClauses             *prop.PropWrapper
	LeftAddDistrib, RightAddDistrib    *prop.PropWrapper
	// suc→+1 bridge for linear-form extraction (Add1: `suc n = n + 1`).
	Add1 *prop.PropWrapper
	// bit0/bit1 unfolding (bit0 n = n+n; bit1 n = suc(n+n)). NOT used for the
	// ring/norm_num addition recursion (that would be circular); used ONLY by the
	// norm_num MULTIPLICATION leaves mulB0/mulB1, which NumeralMul cannot supply
	// (its bit recursion has a different shape) and which are therefore DERIVED
	// from these + RightAddDistrib + the MulClauses suc clause. No circularity:
	// the derivation is explicit lemma composition, not RingProveFull.
	Bit0, Bit1 *prop.PropWrapper
	// Bit-recursion ARITHMETIC decision theorems (add / suc over BIT-trees).
	// Named conjunctions of the per-bit reduction rules; the leaves project the
	// matching conjunct. (NumeralMul is bound and not consumed — the
	// multiplication leaves are derived via Bit0/Bit1.)
	NumeralAdd, NumeralSuc, NumeralMul *prop.PropWrapper
	// Linarith order lemmas.
	NotLessThan, NotLessEq, LessEqAntisym, LessEqOfEq, LessEqOfEqSwapped, ZeroLessEq *prop.PropWrapper
	// SucLessEqIffLessThan (`(m<n) ⇔ (suc m ≤ n)`): the strict→non-strict bridge READ by
	// the integer rounding cut (nat_omega.go) to fold a `<` row into
	// the `suc m ≤ n` form its `g·n ≤ b` rearrangement expects.
	SucLessEqIffLessThan                                             *prop.PropWrapper
	LessEqAdd2, LessThanAdd2, LessEqLessThanAdd2, LessThanLessEqAdd2 *prop.PropWrapper
	LessEqAddCancel, LessThanAddCancel                               *prop.PropWrapper
	LessEqMulMono, LessThanMulMono                                   *prop.PropWrapper
	// Comparison decision theorems (the parity bit-recursion).
	NumeralLessThan, NumeralLessEq, NumeralEq *prop.PropWrapper
	// `>` / `≥` definitional bridges.
	GtDef, GeDef *prop.PropWrapper
	// ── Subtraction (monus) layer — the case-split engine. ────────────────────
	// num subtraction is truncated, so it is NOT a linear primitive; these power
	// the subtraction-cancellation simp leaf (subCancel/subTrunc) and the
	// monus case-split decision path (monusSplittable), which keep `-` out of the
	// sound linear/Farkas core by reducing it to `+`-facts per LessEqTotal branch.
	//   • AddSubLeftCancel — `∀n m. n = (m+n)-n`: the cancellation
	//     congruence — once ring proves `a = b+d`, `(b+d)-b = d` closes a-b → d.
	//   • LessEqTotal — `∀m n. (m≤n) ∨ (n≤m)`: the split source.
	//   • LessThanTrichotomy — `∀m n. ((m<n) ∨ (n<m)) ∨ (m=n)`: the
	//     trichotomy source for the `≠`-hypothesis split (nat_sub.go trichotomyNeq) —
	//     a hyp `¬(a=b)` kills the `m=n` disjunct, leaving `a<b ∨ b<a` to case-split.
	//   • SubEqZero  — `∀m n. (m≤n) ⇔ (0 = m-n)`: the a≤b branch's
	//     truncate-to-0 pin (and subTrunc's rewrite).
	//   • SubAddCancel  — `∀n m. (n≤m) ⇒ (m = (m-n)+n)`  (IMPLICATION form
	//     via PromiseForGeneral; its normal form is the `¬(n≤m) ∨ …` clause): the b≤a
	//     branch's difference pin.
	// LessEqAdd (`∀m n. m ≤ m+n`) is read via the existing lessEqAddThm
	// accessor for subTrunc's `a ≤ b` discharge; no field of its own here.
	AddSubLeftCancel, LessEqTotal, SubEqZero, SubAddCancel *prop.PropWrapper
	// LessThanTrichotomy — `∀m n. ((m<n) ∨ (n<m)) ∨ (m=n)`: READ by the
	// `≠`-hypothesis trichotomy split (nat_sub.go trichotomyNeq).
	LessThanTrichotomy *prop.PropWrapper
	// LessEqAdd — `∀m n. m ≤ (m + n)`: READ by subTrunc to discharge
	// `a ≤ b` from the ring witness `b = a + e` before applying SubEqZero.
	LessEqAdd *prop.PropWrapper
	// MaxDef / MinDef — `nat_max a b = COND(a≤b, b, a)` / `nat_min a b = COND(a≤b, a, b)`
	// (the nat_max/nat_min const defs): READ by the nat_max/nat_min split clients
	// (nat_sub.go). The pin collapses the COND under each branch's LE-guard,
	// reusing the arith deep rewrite. Bound via the const-def mechanism (defNorm),
	// like GtDef/GeDef — definitions carry no proof and are never emitted.
	MaxDef, MinDef *prop.PropWrapper
	// Dist — the num distance |m-n|, the nat→real lift foundation. Bound to
	// nat_monus.Dist, the THEOREM `∀m n. nat_dist(,(m,n)) = (m-n) + (n-m)` (the clean
	// form, NOT the raw fst/snd const def), so the dist→monus bridge (nat_sub.go)
	// is one monomorphic instantiation that routes dist into the truncated-
	// subtraction layer (cancellation/truncation simp + the LessEqTotal monus split).
	Dist *prop.PropWrapper
	// Sub — `∀m n. (m = m-0) ∧ (predecessor(m-n) = m - suc(n))` (the recursion of `-`):
	// READ by the predecessor→(n-1) bridge (nat_sub.go), which specializes the second
	// clause at (m,0) — `predecessor(n-0) = n - suc 0` — and folds `n-0=n` / `suc 0=1` to
	// `predecessor n = n - 1`, routing all predecessor into the monus layer.
	Sub *prop.PropWrapper
	// ── Parity layer — nat_even/nat_odd bridge into the nat_mod-2 layer. ─────────────────
	// nat_even/nat_odd are routed into the existing nat_div/nat_mod machinery rather than given
	// their own decision procedure:
	//   • EvenIffModTwoZero  — `∀n. nat_even n ⇔ (0 = nat_mod(n, 2))`
	//   • OddIffNotEven  — `∀n. nat_odd n  ⇔ ¬nat_even n`
	//   • EvenMul — `∀m n. nat_even(m·n) ⇔ nat_even m ∨ nat_even n`
	//   • EvenAdd  — `∀m n. nat_even(m+n) ⇔ (nat_even m ⇔ nat_even n)`
	// READ by the parity bridge leaf (nat_sub.go): evenBridge rewrites nat_even n
	// to its nat_mod-2 form; oddBridge composes OddIffNotEven with EvenIffModTwoZero to get
	// `nat_odd n ⇔ ¬(0 = nat_mod(n, 2))` (rather than binding `nat_odd n ⇔
	// (1 = nat_mod(n, 2))`: the ¬-form composes better with the literal nat_mod eval
	// and the ≠-hyp split). EvenMul/EvenAdd decompose a parity over a PRODUCT /
	// SUM structurally (evenStructural), the route for NONLINEAR parity goals where
	// the nat_mod-2 bridge would leave an opaque `(a·b) nat_mod 2`; the bool layer then
	// closes the residual (idempotence / excluded middle). (`∀n. nat_even n
	// ∨ nat_odd n` stays unwired: a raw split on `nat_mod(n,2)` only helps LINEAR goals,
	// already covered by the `nat_mod<2` enrichment; the nonlinear win is EvenMul/EvenAdd.)
	EvenIffModTwoZero, OddIffNotEven, EvenMul, EvenAdd *prop.PropWrapper
	// EvenIffDouble — `∀n. nat_even n ⇔ (∃m. n = 2·m)`. READ by
	// the symbolic-even pow-nonneg handler (realSymbolicEvenPowNonneg in
	// real_ops.go): given `nat_even n` in hyps, skolemize via `n = 2·m0` and reduce
	// `&0 ≤ x pow n` to `&0 ≤ (x pow 2) pow m0` (ℝ's PowPow + ℝ's PowTwoNonneg
	// + ℝ's PowNonneg). Lives in the parity layer here because nat_even is a num
	// predicate; consumed cross-domain by the real layer.
	EvenIffDouble *prop.PropWrapper
	// ── Integer (Presburger) layer. ──────────────────────────────────────────
	// Readers are wired incrementally; an unread field is harmless (its leaf
	// keeps its placeholder, same graceful-degradation contract as above).
	// NB: omega's divisibility is nat-native (`dvd(d,n) = ∃q. n = q·d`, NOT
	// a divisibility defined through ℤ — see nat_omega.go), so the whole integer layer stays
	// real-free; there is deliberately NO `divides` field, and
	// `dividesIntro` needs no named lemma of its own (∃-intro + MulSym).
	//   • DivModUniq — `∀m n q r. (m = q·n + r ∧ r < n) ⇒ (nat_div(m, n) = q ∧
	//     nat_mod(m, n) = r)` (nat_div_mod.DivModUniq) — READ by the NormNatDiv /
	//     NormNatMod evaluators (nat_norm.go) AND by the integer rounding cut
	//     (roundedCut, nat_omega.go) to evaluate the symbolic quotient
	//     `(g·N + c) nat_div g = N + nat_div(c, g)`. Also the engine of notDivides (via
	//     NormNatMod). They build the q·n+r witness from the bit-recursion
	//     evaluators and discharge this uniqueness lemma.
	//   • ModEqZero — `∀m n. (∃q. m = q·n) ⇔ (0 = nat_mod(m, n))`
	//     — READ by the notDivides leaf (nat_omega.go): it bridges
	//     the nat-native `∃q. n = q·d` to `0 = nat_mod(n, d)`, which NormNatMod refutes
	//     when d ∤ n. Pure `num`; no `divides`/real route.
	//   • LessEqRightDivEq — `0 < a ⇒ ((n ≤ nat_div(b, a)) ⇔ (a·n ≤ b))`
	//     — READ by the integer rounding cut: after the cut's ring
	//     rearrangement lands the row in `g·n ≤ b` form, this turns it into
	//     `n ≤ nat_div(b, g)`, then DivModUniq evaluates the nat_div. So intCut IS one
	//     instantiation of LessEqRightDivEq + ring (the multi-variable / two-sided
	//     shapes reduce to it via the `oL + D = oR + g·Lr` ring identity, with
	//     the constant remainder s ∈ [0,g) carried through).
	//   • DivMono / DivMult / ModMult — RESERVED for future nat_div/nat_mod cut work.
	DivModUniq                                  *prop.PropWrapper
	ModEqZero                                   *prop.PropWrapper
	LessEqRightDivEq, DivMono, DivMult, ModMult *prop.PropWrapper
	// ── nat_div/nat_mod layer — the bounded-atom enrichment. ─────────────────────────
	// Power the trivial nat_div/nat_mod simp leaves (divModSimp) and the symbolic
	// bounded-atom enrichment (proveLinDivMod) that injects nat_div/nat_mod facts as hyps
	// before linarith. Lookups + side conditions are nil-checked so a partially
	// installed bundle degrades gracefully.
	//   • DivLessEq   — `∀m n. nat_div(m,n) ≤ m`   (unconditional)
	//   • ModLessEq   — `∀m n. nat_mod(m,n) ≤ m`   (unconditional)
	//   • DivZero — `∀n. 0 = nat_div(n, 0)`     (division BY 0)
	//   • ModZero — `∀n. n = nat_mod(n, 0)`     (mod BY 0)
	//   • ModRefl — `∀n. 0 = nat_mod(n, n)`     (unconditional)
	//   • DivRefl — `∀n. (n=0) ∨ (1 = nat_div(n, n))`   (conditional)
	//   • ModLessThan   — `∀m n. (m<n) ⇒ (m = nat_mod(m, n))` (clause form
	//               `¬(m<n) ∨ …`; the leaf wants the implication, via
	//               PromiseForGeneral)
	//   • DivEqZero  — `∀m n. (n=0) ∨ ((m<n) ⇔ (0 = nat_div(m, n)))`
	//   • DivMult2 — `∀m n p. (m=0) ∨ (nat_div(n, p) = nat_div(m*n, m*p))` (
	//               cancellation of a common literal factor, divCommonFactor)
	//   • ModMultAdd — the affine-nat_mod simp `nat_mod(c·n + r, n) →
	//               nat_mod(r,n)`, generalizing the multiple-is-zero fact `nat_mod(k·n,n)=0`.
	//               The bound normal form is a 4-CLAUSE conjunction (multiple as first/second
	//               summand × n as left/right factor), so the leaf PROJECTS the
	//               matching conjunct via clauseLeaf (not eqLeaf) — no MulSym bridge.
	//   • DivDiv  — `∀m n p. m nat_div (n*p) = (nat_div(m, n)) nat_div p` (
	//               unconditional, single equation): the nested-nat_div simp
	//               `nat_div(nat_div(m,n),p) → nat_div(m, n·p)` (eqLeaf auto-orients).
	DivLessEq, ModLessEq, DivZero, ModZero, ModRefl, DivRefl, ModLessThan, DivEqZero, DivMult2, ModMultAdd, DivDiv *prop.PropWrapper
	// nat_div/nat_mod distribution leaves — the residue/quotient normal form.
	//   • DivMulLessEq   — `∀n m. (n * nat_div(m, n)) ≤ m` (
	//               unconditional): the floor LOWER bound, injected by divModFacts
	//               (the nat_div companion to the already-injected ModLessThan upper bound).
	//   • DivMultAdd — the conditional affine-nat_div simp
	//               `nat_div((c·n)+r, n) → c + nat_div(r,n)` — the nat_div companion to
	//               ModMultAdd (term-shrinking: extracts the quotient). The bound normal
	//               form is a 4-CLAUSE conjunction of `(n=0) ∨ eq` disjunctions (multiple
	//               as first/second summand × n as left/right factor); the leaf
	//               discharges `n≠0` (literal divisor) and projects the matching
	//               clause. Conditional, so — unlike ModMultAdd — NOT unconditional.
	//   • ModAddMod  — wired in the COMBINE direction
	//               `nat_mod(nat_mod(a,n)+nat_mod(b,n), n) → nat_mod(a+b, n)`. The bound form states it
	//               in the DISTRIBUTE direction `nat_mod(a+b,n) = nat_mod(nat_mod(a,n)+nat_mod(b,n),n)`
	//               which as an auto-simp would GROW the term and loop; eqLeaf
	//               auto-orients to the reducing (combine) direction.
	//   • DivAddMod  — `∀a n b. (((nat_div(a,n)+nat_div(b,n)) = nat_div(a+b,n))
	//               ⇔ ((nat_mod(a,n)+nat_mod(b,n)) = nat_mod(a+b,n))) ∨ (n=0)`. RESERVED — a
	//               relational iff with NO normalizing direction, so it earns no
	//               auto-fire leaf (would only ever serve a demand-driven congruence
	//               surface). Bound for completeness; not yet consumed by any leaf.
	DivMulLessEq, DivMultAdd, ModAddMod, DivAddMod *prop.PropWrapper
	// PosIffNonzero — `∀n. (n ≠ 0) ⇔ (0 < n)`: READ by the symbolic-
	// n=0 case-split (proveDivModSplitOnZero, nat_divmod.go). The split uses PosIffNonzero
	// to construct the disjunction `(n=0) ∨ (0<n)` from ExcludedMiddle(n=0),
	// so the `n≠0` branch comes out as `0<n` directly (existing nat_div/nat_mod
	// enricher discharges it via proveNeqZero's symbolic route).
	PosIffNonzero *prop.PropWrapper
	// MulEqZero — `∀m n. m * n = 0 ⇔ m = 0 ∨ n = 0`, as stated: ℕ has no
	// zero divisors. READ by the zero-product hypothesis split and the
	// positivity of a product (nat_products.go).
	MulEqZero *prop.PropWrapper
	// The cancellation of a factor, each as stated:
	// `∀m n p. m * n = m * p ⇔ m = 0 ∨ n = p` (MulEqCancel),
	// `∀m n p. m * n ≤ m * p ⇔ m = 0 ∨ n ≤ p` (LessEqMulCancel) and
	// `∀m n p. m * n < m * p ⇔ m ≠ 0 ∧ n < p` (LessThanMulCancel). READ by
	// the cancellation of the factors a hypothesis's two sides share
	// (nat_scaling.go).
	MulEqCancel, LessEqMulCancel, LessThanMulCancel *prop.PropWrapper
	// PowPositive — `∀m n. 0 < nat_pow(m, n) ⇔ m ≠ 0 ∨ n = 0` — and
	// PowEqZero — `∀m n. nat_pow(m, n) = 0 ⇔ m = 0 ∧ n ≠ 0` — as stated.
	// READ by the positivity of a power of a positive base and by a
	// hypothesis that a power is zero (nat_products.go).
	PowPositive, PowEqZero *prop.PropWrapper
	// Division — `∀n m. (n=0) ∨ (nat_mod(m,n) < n ∧ m = nat_div(m,n)·n + nat_mod(m,n))`
	// — the canonical nat_div/nat_mod characterization. READ by the
	// enricher to inject the strict bound `nat_mod(m,n) < n` and the identity
	// `m = nat_div(m,n)·n + nat_mod(m,n)` when `n≠0` discharges (literal-nonzero n via
	// NormNatNe, or symbolic via the existing hyps).
	Division *prop.PropWrapper
	// ── nat_pow layer — literal-exponent unfolding ────────────────────────────────
	// Power the `nat_pow(m, c) → m·m·…·m` unfolding (expUnfold) that unfolds a nat_pow atom
	// with a literal exponent c into a product chain, feeding the result straight
	// into RingProveFull. NO bound-atom enrichment here — nat_pow is unbounded in
	// general, so linarith treats a non-literal-exponent nat_pow as opaque.
	//   • NatPow — `∀m n. (1 = nat_pow(m,0)) ∧ (m·nat_pow(m,n) = nat_pow(m,suc n))`:
	//     the two recursion clauses, projected per c. Base case + step case.
	//   • PowOne — `∀n. n = nat_pow(n, 1)`: direct shortcut for c=1
	//     (faster than going through the recursion step).
	//   • PowTwo — `∀n. n·n = nat_pow(n, 2)`: direct shortcut for c=2.
	//   • OnePow — `∀n. 1 = nat_pow(1, n)`: unconditional simp
	//     `nat_pow(1, n) → 1`. Symbolic n; term strictly shrinks — auto-fires in arith.
	//   • ZeroPow — `∀n. nat_pow(0, n) = COND(n=0, 1, 0)`: the
	//     COND-form `nat_pow(0, n)` rewrite. The Cond's guard then collapses through
	//     trivialCondRewrite + the atom decider (numerically or via hyps), so
	//     `nat_pow(0, n)` becomes `0` when `n≠0` is dischargeable and `1` when `n=0`.
	//     Net term size is essentially preserved, then shrinks under collapse.
	NatPow, PowOne, PowTwo, OnePow, ZeroPow *prop.PropWrapper
	// ── factorial layer — literal-factorial evaluation ─────────────────────────────
	//   • Factorial — `(factorial 0 = 1) ∧ (∀n. factorial(suc n) = suc n · factorial n)`:
	//     the two recursion clauses. The simp leaf factSimp folds a LITERAL
	//     `factorial(c)` all the way to its numeral `c!` (size-safe, like divmodEval —
	//     no symbolic base to grow, unlike nat_pow). Symbolic factorial stays opaque.
	Factorial *prop.PropWrapper
	// ── Enumeration / ordering split layer — bounded enumeration ───────────────
	// Power the bounded-variable enumeration split (proveBoundedEnum): a hyp `x ≤ c` /
	// `x < c` with a literal bound c is peeled into the finite disjunction
	// `x=0 ∨ … ∨ x=c`, each value substituted into the (nonlinear) goal atom and
	// evaluated by the existing literal simps.
	//   • LessEqSplit    — `∀m n. (m≤n) ⇔ ((m<n) ∨ (m=n))`: the peel step.
	//   • LessThanSucIffLessEq — `∀m n. (m < suc n) ⇔ (m ≤ n)`: bridges the
	//     `x<c` disjunct down to `x ≤ c-1` for the recursion (c = suc(c-1) by sucBits).
	LessEqSplit, LessThanSucIffLessEq *prop.PropWrapper
	// ── nat_div/nat_mod enrichment — the nested residue ───────────────────────────────
	//   • ModModRefl — `∀m n. nat_mod(m,n) = nat_mod(nat_mod(m,n), n)` (
	//     idempotence) — READ by the nat_div/nat_mod enricher (nat_divmod.go) to pin a
	//     nested `nat_mod(nat_mod(m,n),n)` atom to its inner `nat_mod(m,n)`. (The companion
	//     "dividend is a multiple of the divisor ⇒ nat_mod = 0" fact needs no field —
	//     it derives from the already-bound ModEqZero; see nat_divmod.go modMultZero.)
	ModModRefl *prop.PropWrapper
}

// natLemmaBundle is the installed bundle, or nil (placeholder mode). All readers go
// through nil-safe accessors below so a nil bundle is never dereferenced.
var natLemmaBundle *NatLemmaBundle

// SetNatLemmaBundle installs the bundle omega's leaves derive from. Pass nil to
// revert to placeholder mode. Set once at engine startup. Drops the
// constraint extraction memos (resetConstraintMemos).
func SetNatLemmaBundle(b *NatLemmaBundle) {
	natLemmaBundle = b
	resetConstraintMemos()
}

// "No silent degrade" is enforced by the placeholder seam (bundle.go), not
// a separate flag: a named-lemma leaf (eqLeaf / implyLeaf / cmpLeaf) whose field
// is nil calls placeholderConcl, which PANICS in production (no fabricator) and
// uses a test stand-in only when a _test.go installed one. So with a real bundle
// installed, every leaf its goals reach MUST bind its real theorem — a nil field
// or shape mismatch panics at the call site, no flag required.
//
// The integer-frontier leaves (the rank-1 cut / general gcd / notDivides /
// divmod evaluator) are NOT named-theorem fields and do not degrade to a
// placeholder: when their real composition can't run (a needed integer theorem
// absent) they DECLINE (ok=false, the nil contract). (mulRearrange4 / monoMerge
// derive from commuteMUL/associateMUL, which ARE checked.)

// Nil-safe accessors for the bit-recursion decision theorems (arithmetic +
// comparison): nil when no bundle is installed or the field is unset, so the
// leaf keeps its placeholder.
func numeralAddThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.NumeralAdd })
}

func numeralSucThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.NumeralSuc })
}

// No accessor for NumeralMul: the field is still populated by the library bundle
// but multiplication leaves are now derived via Bit0/Bit1 instead, so the
// projection has no consumers (see comment on the bundle field above).

func numeralLessThanThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.NumeralLessThan })
}

func numeralLessEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.NumeralLessEq })
}

func numeralEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.NumeralEq })
}

// natBundleField reads a field through the installed bundle, or nil if none.
func natBundleField(f func(*NatLemmaBundle) *prop.PropWrapper) *prop.PropWrapper {
	if natLemmaBundle == nil {
		return nil
	}
	return f(natLemmaBundle)
}

// Nil-safe field accessors for the macro (non-bit-recursion) library theorems.
func addSymThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.AddSym })
}

func addAssocThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.AddAssoc })
}

func mulSymThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.MulSym })
}

func mulAssocThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.MulAssoc })
}

func addClausesThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.AddClauses })
}

func mulClausesThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.MulClauses })
}

func leftAddDistribThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LeftAddDistrib })
}

func rightAddDistribThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.RightAddDistrib })
}

func add1Thm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.Add1 })
}

func bit0Thm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.Bit0 })
}

func bit1Thm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.Bit1 })
}

func notLessThanThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.NotLessThan })
}

func notLessEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.NotLessEq })
}

func lessEqAntisymThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqAntisym })
}

func lessEqOfEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqOfEq })
}

func lessEqOfEqSwappedThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqOfEqSwapped })
}

func zeroLessEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ZeroLessEq })
}

func lessEqAdd2Thm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqAdd2 })
}

func lessThanAdd2Thm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessThanAdd2 })
}

func lessEqLessThanAdd2Thm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqLessThanAdd2 })
}

func lessThanLessEqAdd2Thm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessThanLessEqAdd2 })
}

func lessEqAddCancelThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqAddCancel })
}

func lessThanAddCancelThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessThanAddCancel })
}

func lessEqMulMonoThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqMulMono })
}

func lessThanMulMonoThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessThanMulMono })
}

func gtDefThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.GtDef })
}

func geDefThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.GeDef })
}

// Subtraction-layer accessors.
func addSubLeftCancelThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.AddSubLeftCancel })
}

func lessEqTotalThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqTotal })
}

func lessThanTrichotomyThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessThanTrichotomy })
}

func subEqZeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.SubEqZero })
}

func subAddCancelThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.SubAddCancel })
}

func lessEqAddThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqAdd })
}

func maxDefThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.MaxDef })
}

func minDefThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.MinDef })
}

func distThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.Dist })
}

func subThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.Sub })
}

// Parity accessors — the nat_even/nat_odd → nat_mod-2 bridge.
func evenIffModTwoZeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.EvenIffModTwoZero })
}

func oddIffNotEvenThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.OddIffNotEven })
}

func evenMulThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.EvenMul })
}

func evenAddThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.EvenAdd })
}

// evenIffDoubleThm exposes EvenIffDouble for the symbolic-even pow-nonneg handler
// (real_ops.go). nil-safe; placeholder seam fires when unbundled.
func evenIffDoubleThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.EvenIffDouble })
}

// nat_div/nat_mod accessors — bounded-atom enrichment.
func divLessEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivLessEq })
}

func modLessEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ModLessEq })
}

func divZeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivZero })
}

func modZeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ModZero })
}

func modReflThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ModRefl })
}

func divReflThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivRefl })
}

func modLessThanThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ModLessThan })
}

func divEqZeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivEqZero })
}

func divMult2Thm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivMult2 })
}

func modMultAddThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ModMultAdd })
}

func divDivThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivDiv })
}

func divMulLessEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivMulLessEq })
}

func divMultAddThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivMultAdd })
}

func modAddModThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ModAddMod })
}

// DivAddMod has no accessor: it is a reserved field with no leaf consumer (a
// relational iff, no normalizing direction — see its bundle doc).
func posIffNonzeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.PosIffNonzero })
}

func mulEqZeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.MulEqZero })
}

func mulEqCancelThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.MulEqCancel })
}

func lessEqMulCancelThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqMulCancel })
}

func lessThanMulCancelThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessThanMulCancel })
}

func powPositiveThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.PowPositive })
}

func powEqZeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.PowEqZero })
}

func divisionThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.Division })
}

// nat_pow-layer accessors — literal-exponent unfolding.
func natPowThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.NatPow })
}

func powOneThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.PowOne })
}

func powTwoThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.PowTwo })
}

func onePowThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.OnePow })
}

func zeroPowThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ZeroPow })
}

// factorial accessor — literal-factorial evaluation.
func factorialThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.Factorial })
}

// Integer-layer accessors. Only the read fields get accessors; accessors for
// the reserved nat_div/nat_mod-cut fields are added alongside their leaf wiring (intCut),
// so the bundle never carries a reader without a derivation.
func divModUniqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.DivModUniq })
}

func modEqZeroThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ModEqZero })
}

func lessEqRightDivEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqRightDivEq })
}

func sucLessEqIffLessThanThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.SucLessEqIffLessThan })
}

func lessEqSplitThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessEqSplit })
}

func lessThanSucIffLessEqThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.LessThanSucIffLessEq })
}

func modModReflThm() *prop.PropWrapper {
	return natBundleField(func(b *NatLemmaBundle) *prop.PropWrapper { return b.ModModRefl })
}
