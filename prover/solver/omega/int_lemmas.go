package omega

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// IntLemmaBundle is the ℤ analog of RealLemmaBundle (real_lemmas.go): the
// injection seam through which the integer proof leaves obtain their named
// theorems. Same graceful-degradation contract — a present field derives a real
// kernel proof, a nil field (the default) falls back to a placeholder stand-in
// fabricated by the test-only hook (bundle.go), so core.TestThm never
// enters the production build and the int replay skeleton stays exercisable in
// tests; serve.InstallIntLemmaBundle binds every field to a theorem over ℤ
// (in a non-test build a degrade then panics at the placeholder seam).
//
// The order/ring part of the field set mirrors RealLemmaBundle's law for law,
// because the whole ℤ order/ring suite is the ℝ suite lifted through
// real_of_int: AddSym, LessEqAdd2, LessEqAddLeft,
// LessEqMulLeft, NotLessThan, LessEqOfEq, OfNumAdd/OfNumMul/…
// are the real lemmas one-for-one. In XuGo they are standalone theorems
// (chapter members under library/proofs/int_num), so the int decision layer
// consumes them directly without any real_of_int rewrite. A field is named
// for the member it binds (NatLemmaBundle's rule), so where the ℤ chapters
// name a law differently from the ℝ ones the two fields differ in name and
// not in statement: AddLeftIdentity beside ℝ's AddLeftId, NegNonneg beside
// NegNonnegativeIffNonpositive, GreaterIffLess — a theorem over ℤ — beside
// the definition GtDef.
//
// Two shape differences from num, shared with ℝ: there is no ZeroLessEq
// slot (int variables are free — the refutation injects no 0≤x rows), and the
// scaling lemmas LessEqMulLeft/LessThanMulLeft carry a `&0 ≤ c` / `&0 < c` side
// condition the replay discharges on the concrete numeral coefficient.
//
// The one genuinely int-SPECIFIC field (no real twin — ℝ is not discrete, so it
// cannot lift from a law over ℝ): Discrete (`x + &1 ≤ y ⇔ x < y`),
// consumed by the strict-row strengthening in intBuildAll (int_linarith.go), the
// `int`-type mirror of the `num` `sucLessEqIffLessThan`. It tightens every strict `<` row to a
// non-strict `+ &1 ≤` row, so ℚ-Farkas closes the off-by-one / consecutive-integer
// class (e.g. `x < y ⊢ x + &1 ≤ y`) it otherwise cannot. NOT a gcd cut.
//
// The int "omega" COMPLETENESS frontier proper (genuinely NOT in this layer):
// iterated rank-k gcd cuts (provenance-DAG) → Cooper QE, and variable-divisor
// int_divides. The rank-1 GCD-equality test and gcd rounding cut
// (int_linarith.go) need no bundle field of their own — they route through
// ℤ-discreteness + ℚ-Farkas, not a leaf. Euclidean int_div/int_rem is the int
// twin of num's nat_div/nat_mod layer: `int_div`/`int_rem` have a DSL surface
// (domain.go) and a literal-eval simp + bounded-atom enrichment handler
// (nat_divmod.go, reading the DivisionIdentity / DivModUnique / RemNonneg /
// RemBelowDivisor / Div* / Rem* fields below), with the int_abs-carrying
// bound for a negative / unknown-sign divisor (RemUpperAbs) and the
// DivMulAdd / RemMulAdd distribution beside it. The symbolic
// n=&0 split off RemUpperAbs's disjunction is not built.
type IntLemmaBundle struct {
	// ── Ring AC + identity/distribution — READ by the ring leaves ────────────
	// (int_lemmas.go intCommuteADD…intZeroMul, consumed by intRing /
	// intNormalizeProof). AddLeftIdentity is the one RESERVED slot: the
	// canonical form only ever appends `+ &0` on the right (AddRightIdentity).
	AddSym, AddAssoc, MulSym, MulAssoc                              *prop.PropWrapper
	AddLeftIdentity, AddRightIdentity, MulLeftIdentity, MulLeftZero *prop.PropWrapper
	LeftDistrib, RightDistrib                                       *prop.PropWrapper

	// ── int_of_num homomorphism bridge — READ by the int norm_num evaluators ──
	// (intNormNat*: lift `&m ⋆ &n` / `&m ⋈ &n` to the num evaluator
	// through OfNumAdd/OfNumMul/OfNumLt/OfNumLe/OfNumEq).
	OfNumAdd, OfNumMul, OfNumLt, OfNumLe, OfNumEq *prop.PropWrapper

	// ── Order basics / duality — READ by the leaves now. ──────────────────────
	NotLessThan, NotLessEq, LessEqAntisym, LessEqOfEq, LessEqOfEqSwapped *prop.PropWrapper

	// LessEqTrans: ∀x y z. (x ≤ y) ⇒ (y ≤ z) ⇒ (x ≤ z)   (lifted from
	// ℝ). READ by the two-sided product bound (intProveProductMul2),
	// which chains its two monotone scalings — int does not atomize the product
	// atoms, so plain linarith cannot do the transitivity.
	LessEqTrans *prop.PropWrapper

	// ── Pairwise inequality addition — READ now (LessEqAdd2 family). ─────────
	LessEqAdd2, LessThanAdd2, LessEqLessThanAdd2, LessThanLessEqAdd2 *prop.PropWrapper

	// ── Additive left cancellation — READ now (LessEqAddLeft / LessThanAddLeft). ────
	LessEqAddLeft, LessThanAddLeft *prop.PropWrapper

	// ── Monotone scaling by a positive numeral — READ now (LessEqMulLeft / ──────
	// LessThanMulLeft). Curried shapes, binder order [c, a, b] (the leaf's instAll
	// order):
	//   LessEqMulLeft: ∀c a b. (&0 ≤ c) ⇒ (a ≤ b) ⇒ (c·a ≤ c·b)
	//   LessThanMulLeft: ∀c a b. (&0 < c) ⇒ (a < b) ⇒ (c·a < c·b)
	// The side condition is discharged on the concrete Farkas multiplier via the
	// int norm_num bridge (int_lemmas.go intScale).
	LessEqMulLeft, LessThanMulLeft *prop.PropWrapper

	// ── Cancelling a positive factor OUT of a hypothesis — READ by the hyp-side
	// cancel enrichment (int_cancel.go), the converse of the scaling above.
	// Curried shapes, binder order [c, a, b] with c the cancelled factor:
	//   LessEqCancelMulLeft: ∀c a b. (&0 < c) ⇒ (c·a ≤ c·b) ⇒ (a ≤ b)
	//   LessThanCancelMulLeft: ∀c a b. (&0 < c) ⇒ (c·a < c·b) ⇒ (a < b)
	// The sign premise is STRICT in both — `&0 ≤ c` cancels nothing, since
	// `&0·a ≤ &0·b` holds for every a and b. The RIGHT-factor spellings need no
	// field: the handler commutes both sides through MulSym and reads them
	// with these two. ℤ states neither law natively, so the install lifts the
	// REAL pair through IntOfRealThm (serve/int_bundle.go) — the PowNonneg/PowPos
	// route, since the lift carries a curried implication across unchanged.
	LessEqCancelMulLeft, LessThanCancelMulLeft *prop.PropWrapper

	// ── Product nonnegativity / positivity — READ by the sign-of-product handler
	// LessEqMul: ∀x y. (&0 ≤ x) ⇒ (&0 ≤ y) ⇒ (&0 ≤ x·y). Closes
	// `&0 ≤ x ∧ &0 ≤ y ⊢ &0 ≤ x·y` (int.go); curried, binder [x, y].
	// MulPos: ∀x y. (&0 < x) ⇒ (&0 < y) ⇒ (&0 < x·y)   (the strict
	// twin; lifted from ℝ). With the negation reduction in
	// intProveSignedProduct the two cover all four sign combinations of `x·y ⋈ &0`.
	LessEqMul, MulPos *prop.PropWrapper

	// ── integral domain (no zero divisors) — READ by the MulEqZero hyp-split ─────
	// MulEqZero: ∀x y. (x·y = &0) ⇔ (x = &0 ∨ y = &0)   (lifted from
	// ℝ). A hyp `a·b = &0` becomes the splittable disjunction
	// `a=&0 ∨ b=&0` (int_split.go intHypSplittable), so `x·x=&0 ⊢ x=&0` and
	// `x·y=&0, x≠&0 ⊢ y=&0` close. ℤ is an integral domain.
	MulEqZero *prop.PropWrapper

	// ── neg-order flip — READ by intProveSignedProduct's nonpositive target ───
	// The sign-mixed reduction lands on `&0 ⋈ −(x·y)`; these flip it to the goal
	// `x·y ⋈ &0` at the PROOF level (linarith cannot — it atomizes `−(x·y)` and
	// `x·y` as independent opaque atoms). Iffs, instantiated at the product atom:
	//   NegNonneg: ∀x. (&0 ≤ −x) ⇔ (x ≤ &0)   (lifted from ℝ)
	//   NegPositiveIffNegative: ∀x. (&0 < −x) ⇔ (x < &0)   (lifted from ℝ)
	NegNonneg, NegPositiveIffNegative *prop.PropWrapper

	// ── `>` / `≥` definitional bridges — READ now (GreaterIffLess / GreaterEqIffLessEq-style). ────
	GreaterIffLess, GreaterEqIffLessEq *prop.PropWrapper

	// ── Total subtraction / negation — READ by the signed normalizer ──────────
	// (subneg.go, shared int/real). Field-for-field the RealLemmaBundle
	// subneg block; the ℤ laws are the ℝ laws lifted through real_of_int (the
	// new IntBridges.Sub/Neg make SubDef / NegAdd / NegNeg / NegZero
	// / MulRightNeg auto-lift):
	//   SubDef:  a + (−b) = a − b
	//   NegAdd:  −(a+b) = (−a) + (−b)
	//   NegNeg:  −(−a) = a
	//   NegZero:    −(&0) = &0
	//   MulRightNeg: a·(−b) = −(a·b)
	SubDef, NegAdd, NegNeg, NegZero, MulRightNeg *prop.PropWrapper

	// ── Relation-level move-across — READ by moveAcrossCmp (subneg.go) ─────
	// the subtraction move-across families (the ℝ laws lifted), pushing a top-of-side
	// subtraction across the relation into the positive two-sided form:
	//   LessEqSubAddRight: (x − y ≤ z) ⇔ (x ≤ z + y)
	//   LessEqSubAddLeft: (x ≤ y − z) ⇔ (x + z ≤ y)
	// (Lt/Eq analogues likewise). >/≥ bridge to </≤ upstream, so need none.
	LessEqSubAddRight, LessEqSubAddLeft, LessThanSubAddRight, LessThanSubAddLeft, EqSubRightAdd, EqSubLeftAdd *prop.PropWrapper

	// ── ℤ discreteness — READ by intBuildAll's strict-row pass ─────────────────
	// Discrete: (x + &1 ≤ y) ⇔ (x < y). The lone int-only
	// field; no real analogue to lift (ℝ is dense). NOT a cut.
	Discrete *prop.PropWrapper

	// ── Piecewise operator definitions — READ by the int case split (int_split.go)
	// Each is the operator's own piecewise-by-comparison definition (no real lemma
	// to lift): the case split collapses the COND under each branch's guard.
	//   AbsBySign: int_abs x = COND(&0 ≤ x, x, −x)
	//   MaxDef: int_max a b = COND(a ≤ b, b, a)
	//   MinDef: int_min a b = COND(a ≤ b, a, b)
	//   SgnDef: int_sgn x = COND(&0 < x, &1, COND(x < &0, −&1, &0))
	AbsBySign, MaxDef, MinDef, SgnDef *prop.PropWrapper

	// ── int trichotomy — READ by the `≠`-hyp split (int_split.go intHypSplittable)
	// LessThanTrichotomy: ((a<b) ∨ (b<a)) ∨ (a=b)   (lifted from ℝ).
	LessThanTrichotomy *prop.PropWrapper

	// ── int_pow recursion — READ by the literal-exponent unfold (int.go) ─────
	//   PowZero: int_pow x 0 = &1                 (int_pow's base clause)
	//   PowSuc:  int_pow x (suc n) = x · int_pow x n   (its step clause)
	PowZero, PowSuc *prop.PropWrapper

	// ── int order/disjunction ─────────────────────────────────────────────────
	// LessEqSplit: (a ≤ b) ⇔ ((a < b) ∨ (a = b))   (lifted from ℝ). With
	// Discrete it would peel a two-sided literal range into `x=a ∨ … ∨ x=b`.
	// Currently UNCONSUMED on the int side: the bounded-enum (intProveBoundedEnum
	// in int.go) proves the value disjunction via intProveBoolGoal directly rather
	// than via an explicit LessEqSplit + Discrete peel chain. Field retained for the
	// alternative path; the library still populates it.
	LessEqSplit *prop.PropWrapper

	// ── Image sign split (int.go) — READ by intImageSplit ───────────
	// Image: ∀x. ∃n. (x = −&n) ∨ (x = &n). Every int is ±a-nat; the
	// sign split feeds `x = ±&n` to the int_of_num collapse (int.go) so a
	// sign-dependent nonlinear goal like `&0 ≤ x·x` (SquareNonneg) closes. Int-
	// only (ℝ is not ±-imaged); proved natively, not lifted.
	Image *prop.PropWrapper

	// ── int_divides — READ by the divisibility handlers (intDividesGoal/Skolem) ─
	// DividesDef: ∀d e. (∃z. e = d·z) ⇔ int_divides(d, e). Unfolds
	// a divisibility goal to an ∃-witness intro and a divisibility hyp to a
	// skolemized linear equation (∃-elimination), feeding the gcd-equality test — so
	// `int_divides(&2, &1)` is refuted (2z=1, gcd 2 ∤ 1). Int-only.
	DividesDef *prop.PropWrapper

	// ── int Euclidean int_div/int_rem (nat_divmod.go) — READ by the int_div/int_rem handler ───
	// The int twin of num's nat_div/nat_mod bounded-atom enrichment. Note int's signed
	// dividend means there is NO unconditional `rem ≤ m` / `div ≤ m` (num's
	// ModLessEq/DivLessEq) — the backbone is the unconditional identity plus the
	// nonneg + upper bounds, which (for a literal/positive divisor) pin the
	// values via linarith + ℤ-discreteness with no separate literal evaluator.
	//   DivisionIdentity: m = int_div(m,n)·n + int_rem(m,n)        (unconditional)
	//   RemNonneg:       (n = &0) ∨ (&0 ≤ int_rem(m,n))       (the n≠0 nonneg bound)
	//   RemBelowDivisor:        ¬(&0 < n) ∨ (int_rem(m,n) < n)       (the 0<n upper bound)
	//   RemUpperAbs:  (n = &0) ∨ (int_rem(m,n) < int_abs(n))   (the general
	//     n≠0 upper bound — for a NEGATIVE / unknown-sign divisor, where RemBelowDivisor's
	//     `rem < n` is false; composes with the int_abs case split).
	//   DivModUnique:   (m=q·n+r ∧ &0≤r ∧ r<int_abs(n)) ⇒ (q=int_div(m,n) ∧ r=int_rem(m,n))
	//     — the literal-operand evaluator (folds int_div(&a,&b) /
	//     int_rem(&a,&b) to their numeric values; the int twin of num's divModUniqWitness).
	//   DivByZero/RemByZero/DivByOne/RemByOne: the divisor-0 / divisor-1 simp folds:
	//     int_div(m,&0)=&0, int_rem(m,&0)=m, int_div(m,&1)=m,
	//     int_rem(m,&1)=&0.
	DivisionIdentity, RemNonneg, RemBelowDivisor, RemUpperAbs, DivModUnique *prop.PropWrapper
	DivByZero, RemByZero, DivByOne, RemByOne                                *prop.PropWrapper

	// ── Square / pow-sign / abs ordering (lifted from ℝ) ─────────────────────
	// All consumed by handlers that run
	// after the linear/Image core to PREEMPT the case-split cost when a
	// single lemma instance closes the goal.
	//
	// SquareNonneg: ∀x. &0 ≤ x·x   (lifted from ℝ). READ
	// by intProveSquareNonneg — closes `&0 ≤ x·x` with no sign hyp, an
	// alternative to the Image sign split (single lemma, no ByCases /
	// of_num collapse). intProveMonotone (needing factor-sign hyps) declines.
	SquareNonneg *prop.PropWrapper

	// ── square ↔ abs interchange — atom rewrites ──────────────────────────
	//   SquareOfAbs:  abs(x) pow 2 = x pow 2          (strips abs
	//             from a square; fires only for literal exponent &2)
	//   NegEqZero:   (−x = &0) ⇔ (x = &0)            (zero-
	//             detection through neg — the neg twin of NegNonneg/NegPositiveIffNegative)
	// READ by intPowLawSimp (SquareOfAbs) and intNegEqZeroSimp (NegEqZero) in
	// intArithSimpStep. Goal-side direction; the hyp-side dual waits on a
	// hyp pre-simp pass (same shape limit as ℝ).
	SquareOfAbs, NegEqZero *prop.PropWrapper

	// ── abs ordering + n-ary triangle (sub-RCF lifts) ─────────────────────
	//   AbsLessEqIffPowTwoLessEq: (|x| ≤ |y|) ⇔ (x pow 2 ≤ y pow 2)   (goal-side
	//                simp `x² ≤ y² → |x| ≤ |y|`)
	//   AbsTriangle: |x + y| ≤ |x| + |y|                  (the
	//                binary base, iterated by intProveAbsTriangle for n-ary)
	// READ by intAbsLessEqIffPowTwoLessEqSimp and intProveAbsTriangle.
	AbsLessEqIffPowTwoLessEq, AbsTriangle *prop.PropWrapper

	// ── int_pow sign / no-hyp even-square — READ by intProvePowSign ──────
	//   PowNonneg:    ∀x n. (&0 ≤ x) ⇒ (&0 ≤ x pow n)   (symbolic n)
	//   PowPos:    ∀x n. (&0 < x) ⇒ (&0 < x pow n)
	//   PowTwoNonneg:   ∀x. &0 ≤ x pow 2                  (no hyp,
	//             even-square is nonneg outright)
	// The sign-known nonlinear fragment of pow — NOT full RCF. Lifted from
	// ℝ's PowNonneg / PowPos / PowTwoNonneg.
	PowNonneg, PowPos, PowTwoNonneg *prop.PropWrapper

	// ── int_div/int_rem ↔ divides bridges (stated over ℤ) ─────────────────────────
	// Closes the gap between the rem/div subsystem and the int_divides
	// subsystem: a fact in one domain becomes useful in the other.
	//
	//   DividesIffRemZero: ∀m n. (int_rem(m,n) = &0) ⇔ int_divides(n, m)
	//     READ by intDividesIffRemZeroSimp in intArithSimpStep — a goal
	//     `int_rem(m,n) = &0` rewrites to `int_divides(n, m)`, then
	//     intDividesGoal closes it (via ∃-witness or the gcd test) and
	//     the symmetric hyp side reads as `divides → rem=0`.
	//
	//   DivisorBoundedByDividend: ∀d e. int_divides(d, e) ⇒ ~(e = &0) ⇒ (int_abs d ≤ int_abs e)
	//     READ by intProveDivisorBound — an enrichment
	//     that injects `|d| ≤ |e|` whenever a divisibility hyp is paired
	//     with a derivable `e ≠ &0`, so contradictory pairings like
	//     `int_divides(&5, &3)` (with the implicit `&3 ≠ &0`) close
	//     through the int_abs split + linarith. Complements the gcd-rank-1
	//     test, which doesn't fire on bare `int_divides(literal, literal)`.
	//
	//   QuotientExactOfDivides: ∀m q. int_divides(q, m) ⇒ (int_div(m, q) · q = m)
	//     READ by intProveQuotientExact — an enrichment that,
	//     under a divisibility hyp `q ∣ m`, injects the exact-division
	//     identity so linarith can substitute `int_div(m,q)` away.
	//
	//   OfNumDiv: ∀m n. int_of_num(nat_div(m, n)) = int_div(int_of_num m, int_of_num n)
	//   OfNumRem: ∀m n. int_of_num(nat_mod(m, n)) = int_rem(int_of_num m, int_of_num n)
	//     READ by intNormNatDiv / intNormNatMod — the int_of_num bridges
	//     for int_div/int_rem (the int_div/int_rem siblings of OfNumAdd/Mul). Lets the int
	//     literal evaluator route through num's nat_div/nat_mod evaluator (the
	//     alternative to DivModUnique — cleaner for fully-literal pairs).
	DividesIffRemZero, DivisorBoundedByDividend, QuotientExactOfDivides, OfNumDiv, OfNumRem *prop.PropWrapper

	// ── int_div/int_rem distribution + agent-invoked + quantifier bridges ─────────
	// OfNumPow is the one IntOfRealThm lift (of ℝ's). The rest are
	// int-native.
	//
	//   DivMulAdd:    ∀m n p. ~(n=&0) ⇒ (int_div(m + n·p, n) = int_div(m, n) + p)
	//   RemMulAdd:    ∀m n p. int_rem(m + n·p, n) = int_rem(m, n)
	//     The remainder law carries no guard: at a zero divisor int_rem is
	//     the identity and n·p is &0, so the equation holds as it stands —
	//     the corpus entry (int_div_rem.RemMulAddClauses) states it
	//     unconditionally.
	//     READ by the DivMulAdd / RemMulAdd simp clauses in intDivModFold:
	//     a int_div/int_rem whose first arg contains a `n·p` summand strips that
	//     summand to the outer (the int_div/int_rem of the residual).
	//
	//   DivisionAlgorithm: ∀m n. ~(n=&0) ⇒ (m = int_div(m,n)·n + int_rem(m,n) ∧
	//                                  &0 ≤ int_rem(m,n) ∧ int_rem(m,n) < int_abs(n)).
	//     READ by IntDivisionAlgorithm (exported, AGENT-INVOKED — NOT auto-wired).
	//     As a default handler it would compound with the bool/int_abs splits
	//     into expensive search; the user/agent calls it explicitly when a
	//     int_div/int_rem-heavy goal needs the full identity in one shot.
	//
	//   OfNumPow: ∀m n. int_pow (int_of_num m) n = int_of_num (nat_pow(m, n))
	//                  (lifted from ℝ's). READ by intPowSimp —
	//                  the int_of_num bridge for pow (the pow sibling of
	//                  OfNumAdd/Mul/Div/Rem). Wired into intPowSimp; pairs
	//                  with the num-side nat_pow literal evaluator (NormNatExp)
	//                  once that lands. Today's intPowSimp falls back to
	//                  ExpandEXPRewrite + ring for evaluating literal `&m pow c`.
	//
	//   ForallNonneg:    ∀P. (∀x. &0 ≤ x ⇒ P x) ⇔ (∀n. P (int_of_num n))
	//   ExistsNonneg:    ∀P. (∃x. &0 ≤ x ∧ P x) ⇔ (∃n. P (int_of_num n))
	//     READ by IntForallNonneg(P) / IntExistsNonneg(P) (exported, not auto-
	//     wired). Quantifier-level bridges that route a non-negative int
	//     quantifier to num, so num automation can take over. The caller is
	//     a strategy layer above omega's atom-level decider; omega's job is
	//     the body P(&n) once the quantifier has been transformed.
	DivMulAdd, RemMulAdd, DivisionAlgorithm, OfNumPow, ForallNonneg, ExistsNonneg *prop.PropWrapper

	// ── abs / sgn algebraic laws (the ℤ statements of the ℝ laws)      ────────
	// READ by intAbsSgnSimp (int.go): pushes abs/sgn toward the leaves over an
	// operator-compound argument, so `|x·y| = |x|·|y|`, `|−x| = |x|`,
	// `sgn(x·y) = sgn x · sgn y`, … close as reflexivity after normalization.
	// Mirror of the ℝ-end abs/sgn fold (real_ops.go realAbsSgnSimp).
	// Distinct from the case-split eliminating a piecewise `int_abs x` /
	// `int_sgn x` at a bare leaf — these are pure equational rewrites on
	// compound args. Each is unconditional (holds even at degenerate points).
	//
	//   AbsMul: int_abs(x·y) = int_abs x · int_abs y
	//   AbsEven: int_abs(−x) = int_abs x
	//   AbsIdempotent: int_abs(int_abs x) = int_abs x
	//   OfNumAbs: int_abs(int_of_num n) = int_of_num n
	//   SgnMul: int_sgn(x·y) = int_sgn x · int_sgn y
	//   SgnOdd: int_sgn(−x) = −(int_sgn x)
	AbsMul, AbsEven, AbsIdempotent, OfNumAbs, SgnMul, SgnOdd *prop.PropWrapper
}

// intLemmaBundle is the installed int bundle, or nil (placeholder mode).
var intLemmaBundle *IntLemmaBundle

// SetIntLemmaBundle installs the bundle the int leaves derive from. Pass nil to
// revert to placeholder mode. Set once at engine startup, independently of the
// num/real bundles. Drops the constraint extraction memos (resetConstraintMemos).
func SetIntLemmaBundle(b *IntLemmaBundle) {
	intLemmaBundle = b
	resetConstraintMemos()
}

// intBundleField reads a field through the installed int bundle, or nil if none.
func intBundleField(f func(*IntLemmaBundle) *prop.PropWrapper) *prop.PropWrapper {
	if intLemmaBundle == nil {
		return nil
	}
	return f(intLemmaBundle)
}

// intEqLeaf / intImplyLeaf: the int-bundle analogues of eqLeaf/implyLeaf
// (bundle.go) — identical macro instantiation/orientation, falling back through
// the shared placeholder seam (panics in production, test stand-in otherwise).
func intEqLeaf(thm *prop.PropWrapper, args []Term, wantL, wantR Term) *prop.PropWrapper {
	if w, ok := macroEq(thm, args, wantL, wantR); ok {
		return w
	}
	return placeholderEq(thm, wantL, wantR)
}

func intImplyLeaf(thm *prop.PropWrapper, args []Term, want Term) *prop.PropWrapper {
	if w, ok := macroThm(thm, args, want); ok {
		return w
	}
	return placeholderConcl(thm, want)
}

// Nil-safe accessors for the read-now slots. (AddLeftIdentity stays reserved — see the
// struct doc.)
func intAddSymThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AddSym })
}
func intAddAssocThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AddAssoc })
}
func intMulSymThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MulSym })
}
func intMulAssocThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MulAssoc })
}
func intAddRightIdentityThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AddRightIdentity })
}
func intMulLeftIdentityThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MulLeftIdentity })
}
func intMulLeftZeroThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MulLeftZero })
}
func intLeftDistribThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LeftDistrib })
}
func intRightDistribThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.RightDistrib })
}
func intOfNumAddThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumAdd })
}
func intOfNumMulThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumMul })
}
func intOfNumLtThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumLt })
}
func intOfNumLeThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumLe })
}
func intOfNumEqThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumEq })
}
func intNotLessThanThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.NotLessThan })
}
func intLessEqTransThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqTrans })
}
func intNotLessEqThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.NotLessEq })
}
func intLessEqAntisymThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqAntisym })
}
func intLessEqOfEqThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqOfEq })
}
func intLessEqOfEqSwappedThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqOfEqSwapped })
}
func intLessEqAdd2Thm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqAdd2 })
}
func intLessThanAdd2Thm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessThanAdd2 })
}
func intLessEqLessThanAdd2Thm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqLessThanAdd2 })
}
func intLessThanLessEqAdd2Thm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessThanLessEqAdd2 })
}
func intLessEqAddLeftThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqAddLeft })
}
func intLessThanAddLeftThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessThanAddLeft })
}
func intLessEqCancelMulLeftThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqCancelMulLeft })
}

func intLessThanCancelMulLeftThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessThanCancelMulLeft })
}

func intLessEqMulLeftThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqMulLeft })
}
func intLessThanMulLeftThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessThanMulLeft })
}
func intLessEqMulThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqMul })
}
func intMulEqZeroThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MulEqZero })
}
func intMulPosThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MulPos })
}
func intNegNonnegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.NegNonneg })
}
func intNegPositiveIffNegativeThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.NegPositiveIffNegative })
}
func intGreaterIffLessThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.GreaterIffLess })
}
func intGreaterEqIffLessEqThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.GreaterEqIffLessEq })
}
func intSubDefThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.SubDef })
}
func intNegAddThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.NegAdd })
}
func intNegNegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.NegNeg })
}
func intNegZeroThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.NegZero })
}
func intMulRightNegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MulRightNeg })
}
func intLessEqSubAddRightThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqSubAddRight })
}
func intLessEqSubAddLeftThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessEqSubAddLeft })
}
func intLessThanSubAddRightThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessThanSubAddRight })
}
func intLessThanSubAddLeftThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessThanSubAddLeft })
}
func intEqSubRightAddThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.EqSubRightAdd })
}
func intEqSubLeftAddThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.EqSubLeftAdd })
}
func intDiscreteThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.Discrete })
}
func intAbsBySignThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AbsBySign })
}
func intMaxDefThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MaxDef })
}
func intMinDefThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.MinDef })
}
func intSgnDefThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.SgnDef })
}
func intLessThanTrichotomyThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.LessThanTrichotomy })
}

func intImageThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.Image })
}

func intDividesDefThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DividesDef })
}
func intPowZeroThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.PowZero })
}
func intPowSucThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.PowSuc })
}

// No accessor for LessEqSplit: the field is populated (see comment on the bundle field
// above) but currently has no consumer — intProveBoundedEnum builds the value
// disjunction via the boolean decider directly.

func intDivisionIdentityThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DivisionIdentity })
}
func intRemNonnegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.RemNonneg })
}
func intRemBelowDivisorThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.RemBelowDivisor })
}
func intRemUpperAbsThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.RemUpperAbs })
}
func intDivModUniqueThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DivModUnique })
}
func intDivByZeroThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DivByZero })
}
func intRemByZeroThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.RemByZero })
}
func intDivByOneThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DivByOne })
}
func intRemByOneThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.RemByOne })
}

// ── Accessors: square / pow-sign / abs ordering (lifted from ℝ) ───────────────

func intSquareNonnegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.SquareNonneg })
}
func intSquareOfAbsThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.SquareOfAbs })
}
func intNegEqZeroThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.NegEqZero })
}
func intAbsLessEqIffPowTwoLessEqThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AbsLessEqIffPowTwoLessEq })
}
func intAbsTriangleThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AbsTriangle })
}
func intPowNonnegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.PowNonneg })
}
func intPowPosThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.PowPos })
}
func intPowTwoNonnegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.PowTwoNonneg })
}

// ── Accessors: int_div/int_rem ↔ divides bridges ─────────────────────────────

func intDividesIffRemZeroThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DividesIffRemZero })
}
func intDivisorBoundedByDividendThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DivisorBoundedByDividend })
}
func intQuotientExactOfDividesThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.QuotientExactOfDivides })
}
func intOfNumDivThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumDiv })
}
func intOfNumRemThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumRem })
}

// ── Accessors: int_div/int_rem distribution + agent-invoked + quantifier ─────

func intDivMulAddThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DivMulAdd })
}
func intRemMulAddThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.RemMulAdd })
}
func intDivisionAlgorithmThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.DivisionAlgorithm })
}
func intOfNumPowThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumPow })
}
func intForallNonnegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.ForallNonneg })
}
func intExistsNonnegThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.ExistsNonneg })
}

// ── Accessors: abs / sgn algebraic laws ──────────────────────────────────────

func intAbsMulThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AbsMul })
}
func intAbsEvenThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AbsEven })
}
func intAbsIdempotentThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.AbsIdempotent })
}
func intOfNumAbsThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.OfNumAbs })
}
func intSgnMulThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.SgnMul })
}
func intSgnOddThm() *prop.PropWrapper {
	return intBundleField(func(b *IntLemmaBundle) *prop.PropWrapper { return b.SgnOdd })
}

// Integer (ℤ) proof leaves — the bundle-backed twin of the real leaves
// (real_lemmas.go). Each is one macro instantiation of an IntLemmaBundle field,
// oriented to the engine shape, falling back to a placeholder
// when the field is absent/mis-shaped. The ℤ theorems are the
// ℝ suite lifted through real_of_int, so orientation /
// binder conventions mirror the real leaves exactly:
// AddSym, AddAssoc, MulSym/MulAssoc, LeftDistrib/RightDistrib,
// MulLeftIdentity, AddRightIdentity, MulLeftZero, NotLessThan/NotLessEq, LessEqAntisym,
// LessEqOfEq, LessEqAdd2 family, LessEqAddLeft / LessThanAddLeft,
// LessEqMulLeft / LessThanMulLeft, GreaterIffLess / GreaterEqIffLessEq.
//
// Like ℝ: no intZeroLe — ℤ has no `&0 ≤ x` default, and the int refutation
// injects no nonnegativity rows.

// ── Ring AC / identity / distribution leaves (consumed by intRing) ───────────

// intCommuteADD: ⊢ a + b = b + a   (AddSym)
func intCommuteADD(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intAddSymThm(), []Term{a, b}, intPlusT(a, b), intPlusT(b, a))
}

// intAssociateADD: ⊢ (a + b) + c = a + (b + c)   (AddAssoc, reversed)
func intAssociateADD(a, b, c Term) *prop.PropWrapper {
	return intEqLeaf(intAddAssocThm(), []Term{a, b, c},
		intPlusT(intPlusT(a, b), c), intPlusT(a, intPlusT(b, c)))
}

// intCommuteMUL: ⊢ a · b = b · a   (MulSym)
func intCommuteMUL(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intMulSymThm(), []Term{a, b}, intStarT(a, b), intStarT(b, a))
}

// intAssociateMUL: ⊢ (a · b) · c = a · (b · c)   (MulAssoc, reversed)
func intAssociateMUL(a, b, c Term) *prop.PropWrapper {
	return intEqLeaf(intMulAssocThm(), []Term{a, b, c},
		intStarT(intStarT(a, b), c), intStarT(a, intStarT(b, c)))
}

// intDistributeMUL: ⊢ a · (b + c) = a·b + a·c   (LeftDistrib, reversed)
func intDistributeMUL(a, b, c Term) *prop.PropWrapper {
	return intEqLeaf(intLeftDistribThm(), []Term{a, b, c},
		intStarT(a, intPlusT(b, c)), intPlusT(intStarT(a, b), intStarT(a, c)))
}

// intRightDistrib: ⊢ (a + b) · c = a·c + b·c   (RightDistrib, reversed).
// As with the real leaf, the bound statement's binders are (a, m, b) with m the SHARED
// right factor — `a·m + b·m = (a+b)·m` — so the instAll order is [a, c, b].
func intRightDistrib(a, b, c Term) *prop.PropWrapper {
	return intEqLeaf(intRightDistribThm(), []Term{a, c, b},
		intStarT(intPlusT(a, b), c), intPlusT(intStarT(a, c), intStarT(b, c)))
}

// intOneMul: ⊢ &1 · a = a   (MulLeftIdentity, reversed)
func intOneMul(a Term) *prop.PropWrapper {
	return intEqLeaf(intMulLeftIdentityThm(), []Term{a}, intStarT(intLit(1), a), a)
}

// intAddZeroR: ⊢ a + &0 = a   (AddRightIdentity, reversed)
func intAddZeroR(a Term) *prop.PropWrapper {
	return intEqLeaf(intAddRightIdentityThm(), []Term{a}, intPlusT(a, intLit(0)), a)
}

// intZeroMul: ⊢ &0 · a = &0   (MulLeftZero, reversed)
func intZeroMul(a Term) *prop.PropWrapper {
	return intEqLeaf(intMulLeftZeroThm(), []Term{a}, intStarT(intLit(0), a), intLit(0))
}

// ── goal-negation duality (used by IntLinProve) ──────────────────────────────

// intNotLT: ⊢ ¬(M<N) ⇔ (N≤M)   (NotLessThan)
func intNotLT(m, n Term) *prop.PropWrapper {
	return intEqLeaf(intNotLessThanThm(), []Term{m, n}, not(intLtT(m, n)), intLeT(n, m))
}

// intNotLE: ⊢ ¬(M≤N) ⇔ (N<M)   (NotLessEq)
func intNotLE(m, n Term) *prop.PropWrapper {
	return intEqLeaf(intNotLessEqThm(), []Term{m, n}, not(intLeT(m, n)), intLtT(n, m))
}

// intLessEqAntisym: ⊢ (A≤B) ⇒ (B≤A) ⇒ (A=B)   (LessEqAntisym)
func intLessEqAntisym(a, b Term) *prop.PropWrapper {
	return intImplyLeaf(intLessEqAntisymThm(), []Term{a, b},
		imply(intLeT(a, b), imply(intLeT(b, a), eqT(a, b))))
}

// ── provenance of expanded rows ──────────────────────────────────────────────

// intLessEqOfEq: ⊢ (A = B) ⇒ (A ≤ B)   (LessEqOfEq)
func intLessEqOfEq(a, b Term) *prop.PropWrapper {
	return intImplyLeaf(intLessEqOfEqThm(), []Term{a, b}, imply(eqT(a, b), intLeT(a, b)))
}

// intLessEqOfEqSwapped: ⊢ (A = B) ⇒ (B ≤ A)   (LessEqOfEq on the swapped equality)
func intLessEqOfEqSwapped(a, b Term) *prop.PropWrapper {
	return intImplyLeaf(intLessEqOfEqSwappedThm(), []Term{a, b}, imply(eqT(a, b), intLeT(b, a)))
}

// ── monotone scaling by a positive numeral (LessEqMulLeft / LessThanMulLeft) ────────
// The int scaling lemma carries a nonnegativity premise on the multiplier —
// `&0 ≤ c` for `≤` (LessEqMulLeft), strict `&0 < c` for `<` (LessThanMulLeft) — the
// ℤ analog of the ℝ side condition. Bundle fields hold the curried forms
//
//	LessEqMulLeft: ∀c a b. (&0 ≤ c) ⇒ (a ≤ b) ⇒ (c·a ≤ c·b)
//	LessThanMulLeft: ∀c a b. (&0 < c) ⇒ (a < b) ⇒ (c·a < c·b)
//
// (binder order = the leaf's instAll order [c, a, b]). The leaf instantiates at
// the CONCRETE Farkas multiplier and discharges the side condition numerically
// through the int norm_num bridge (intNormNatLe/Lt — c is always ≥ 2 here:
// λ=1 rows skip scaling).

// intScale is the shared scale-leaf body for the two strictness variants — the
// mirror of realScale. side(⊢ &0 ⋈ &c verdict) comes from the norm_num bridge;
// falls through to the placeholder seam when the field is absent, mis-shaped, or
// the side condition does not evaluate to ⊤.
func intScale(thm *prop.PropWrapper, c _Integer, a, b Term,
	rel func(x, y Term) Term, side func(l, r Term) (*prop.PropWrapper, bool)) *prop.PropWrapper {
	cT := intLitOf(c)
	want := imply(rel(a, b), rel(intMonoTerm(c, a), intMonoTerm(c, b)))
	if thm != nil {
		inst := instAll(thm, []Term{cT, a, b}) // (&0⋈&c) ⇒ (a⋈b) ⇒ (c·a ⋈ c·b)
		if sd, ok := side(intLit(0), cT); ok && prop.Rhs(sd).Equals(prop.T) {
			res := inst.DemoteHyp().DeriveHypFrom(iffTrueElim(sd))
			if res.Conclusion().AlphaEquals(want) {
				return res
			}
		}
	}
	return placeholderConcl(thm, want)
}

// intLeScale: ⊢ (A ≤ B) ⇒ (c·A ≤ c·B)   (c ≥ 1; LessEqMulLeft, `&0 ≤ &c` side)
func intLeScale(c _Integer, a, b Term) *prop.PropWrapper {
	return intScale(intLessEqMulLeftThm(), c, a, b, intLeT, intNormNatLe)
}

// intLtScale: ⊢ (A < B) ⇒ (c·A < c·B)   (c ≥ 1; LessThanMulLeft, `&0 < &c` side)
func intLtScale(c _Integer, a, b Term) *prop.PropWrapper {
	return intScale(intLessThanMulLeftThm(), c, a, b, intLtT, intNormNatLt)
}

// ── pairwise inequality addition (strictness combinations) ───────────────────

// intAddLe2: ⊢ (A≤B) ⇒ (C≤D) ⇒ (A+C ≤ B+D)   (LessEqAdd2)
func intAddLe2(a, b, c, d Term) *prop.PropWrapper {
	return intImplyLeaf(intLessEqAdd2Thm(), []Term{a, b, c, d},
		imply(intLeT(a, b), imply(intLeT(c, d), intLeT(intPlusT(a, c), intPlusT(b, d)))))
}

// intAddLt2: ⊢ (A<B) ⇒ (C<D) ⇒ (A+C < B+D)   (LessThanAdd2)
func intAddLt2(a, b, c, d Term) *prop.PropWrapper {
	return intImplyLeaf(intLessThanAdd2Thm(), []Term{a, b, c, d},
		imply(intLtT(a, b), imply(intLtT(c, d), intLtT(intPlusT(a, c), intPlusT(b, d)))))
}

// intAddLeLt: ⊢ (A≤B) ⇒ (C<D) ⇒ (A+C < B+D)   (LessEqLessThanAdd2)
func intAddLeLt(a, b, c, d Term) *prop.PropWrapper {
	return intImplyLeaf(intLessEqLessThanAdd2Thm(), []Term{a, b, c, d},
		imply(intLeT(a, b), imply(intLtT(c, d), intLtT(intPlusT(a, c), intPlusT(b, d)))))
}

// intAddLtLe: ⊢ (A<B) ⇒ (C≤D) ⇒ (A+C < B+D)   (LessThanLessEqAdd2)
func intAddLtLe(a, b, c, d Term) *prop.PropWrapper {
	return intImplyLeaf(intLessThanLessEqAdd2Thm(), []Term{a, b, c, d},
		imply(intLtT(a, b), imply(intLeT(c, d), intLtT(intPlusT(a, c), intPlusT(b, d)))))
}

// ── left cancellation of a common addend ─────────────────────────────────────

// intAddLcancelLe: ⊢ (P + x ≤ P + y) ⇔ (x ≤ y)   (LessEqAddLeft)
func intAddLcancelLe(p, x, y Term) *prop.PropWrapper {
	return intEqLeaf(intLessEqAddLeftThm(), []Term{p, x, y},
		intLeT(intPlusT(p, x), intPlusT(p, y)), intLeT(x, y))
}

// intAddLcancelLt: ⊢ (P + x < P + y) ⇔ (x < y)   (LessThanAddLeft)
func intAddLcancelLt(p, x, y Term) *prop.PropWrapper {
	return intEqLeaf(intLessThanAddLeftThm(), []Term{p, x, y},
		intLtT(intPlusT(p, x), intPlusT(p, y)), intLtT(x, y))
}

// ── `>` / `≥` definitional bridges ───────────────────────────────────────────

// intGtBridge: ⊢ (x > y) = (y < x)   (GreaterIffLess)
func intGtBridge(x, y Term) *prop.PropWrapper {
	return intEqLeaf(intGreaterIffLessThm(), []Term{x, y}, intGtT(x, y), intLtT(y, x))
}

// intGeBridge: ⊢ (x ≥ y) = (y ≤ x)   (GreaterEqIffLessEq)
func intGeBridge(x, y Term) *prop.PropWrapper {
	return intEqLeaf(intGreaterEqIffLessEqThm(), []Term{x, y}, intGeT(x, y), intLeT(y, x))
}

// ── total subtraction / negation leaves (signed normalizer, subneg.go) ───
// Field-for-field the real subneg leaves; the ℤ laws are the ℝ laws lifted.

// intSubToAddNeg: ⊢ a − b = a + (−b)   (SubDef, sub→add+neg direction)
func intSubToAddNeg(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intSubDefThm(), []Term{a, b}, intSubT(a, b), intPlusT(a, intNegT(b)))
}

// intNegAddL: ⊢ −(a + b) = (−a) + (−b)   (NegAdd)
func intNegAddL(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intNegAddThm(), []Term{a, b},
		intNegT(intPlusT(a, b)), intPlusT(intNegT(a), intNegT(b)))
}

// intNegNegL: ⊢ −(−a) = a   (NegNeg)
func intNegNegL(a Term) *prop.PropWrapper {
	return intEqLeaf(intNegNegThm(), []Term{a}, intNegT(intNegT(a)), a)
}

// intNegZeroL: ⊢ −(&0) = &0   (NegZero)
func intNegZeroL() *prop.PropWrapper {
	return intEqLeaf(intNegZeroThm(), nil, intNegT(intLit(0)), intLit(0))
}

// intMulRightNegL: ⊢ c·(−b) = −(c·b)   (MulRightNeg)
func intMulRightNegL(c, b Term) *prop.PropWrapper {
	return intEqLeaf(intMulRightNegThm(), []Term{c, b}, intStarT(c, intNegT(b)), intNegT(intStarT(c, b)))
}

// ── relation-level move-across leaves (moveAcrossCmp, subneg.go) ─────────

// intLessEqSubAddRight: ⊢ (x − y ≤ z) ⇔ (x ≤ z + y)   (LessEqSubAddRight)
func intLessEqSubAddRight(x, y, z Term) *prop.PropWrapper {
	return intEqLeaf(intLessEqSubAddRightThm(), []Term{x, y, z},
		intLeT(intSubT(x, y), z), intLeT(x, intPlusT(z, y)))
}

// intLessEqSubAddLeft: ⊢ (x ≤ y − z) ⇔ (x + z ≤ y)   (LessEqSubAddLeft)
func intLessEqSubAddLeft(x, y, z Term) *prop.PropWrapper {
	return intEqLeaf(intLessEqSubAddLeftThm(), []Term{x, y, z},
		intLeT(x, intSubT(y, z)), intLeT(intPlusT(x, z), y))
}

// intLessThanSubAddRight: ⊢ (x − y < z) ⇔ (x < z + y)   (LessThanSubAddRight)
func intLessThanSubAddRight(x, y, z Term) *prop.PropWrapper {
	return intEqLeaf(intLessThanSubAddRightThm(), []Term{x, y, z},
		intLtT(intSubT(x, y), z), intLtT(x, intPlusT(z, y)))
}

// intLessThanSubAddLeft: ⊢ (x < y − z) ⇔ (x + z < y)   (LessThanSubAddLeft)
func intLessThanSubAddLeft(x, y, z Term) *prop.PropWrapper {
	return intEqLeaf(intLessThanSubAddLeftThm(), []Term{x, y, z},
		intLtT(x, intSubT(y, z)), intLtT(intPlusT(x, z), y))
}

// intEqSubRightAdd: ⊢ (x − y = z) ⇔ (x = z + y)   (EqSubRightAdd)
func intEqSubRightAdd(x, y, z Term) *prop.PropWrapper {
	return intEqLeaf(intEqSubRightAddThm(), []Term{x, y, z},
		eqT(intSubT(x, y), z), eqT(x, intPlusT(z, y)))
}

// intEqSubLeftAdd: ⊢ (x = y − z) ⇔ (x + z = y)   (EqSubLeftAdd)
func intEqSubLeftAdd(x, y, z Term) *prop.PropWrapper {
	return intEqLeaf(intEqSubLeftAddThm(), []Term{x, y, z},
		eqT(x, intSubT(y, z)), eqT(intPlusT(x, z), y))
}

// ── int_abs piecewise definition (int case split, int_split.go) ──────────────

// intAbsBySign: ⊢ int_abs x = COND(&0 ≤ x, x, −x)   (AbsBySign). The int twin of the
// num maxDef/minDef const-def leaves: the case split collapses the COND under
// each branch's `&0 ≤ x` verdict, pinning int_abs x to x (resp. −x).
func intAbsBySign(x Term) *prop.PropWrapper {
	return intEqLeaf(intAbsBySignThm(), []Term{x},
		intAbsT(x), ext.Cond(intLeT(intLit(0), x), x, intNegT(x)))
}

// intMaxDef: ⊢ int_max a b = COND(a ≤ b, b, a)   (MaxDef).
func intMaxDef(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intMaxDefThm(), []Term{a, b}, intMaxT(a, b), ext.Cond(intLeT(a, b), b, a))
}

// intMinDef: ⊢ int_min a b = COND(a ≤ b, a, b)   (MinDef).
func intMinDef(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intMinDefThm(), []Term{a, b}, intMinT(a, b), ext.Cond(intLeT(a, b), a, b))
}

// intSgnDef: ⊢ int_sgn x = COND(&0 < x, &1, COND(x < &0, −&1, &0))   (SgnDef).
// A nested COND: the outer guard `&0 < x` splits first, and its else-branch
// `COND(x < &0, −&1, &0)` is itself split by the raw-COND kind in the recursion.
func intSgnDef(x Term) *prop.PropWrapper {
	inner := ext.Cond(intLtT(x, intLit(0)), intNegT(intLit(1)), intLit(0))
	return intEqLeaf(intSgnDefThm(), []Term{x}, intSgnT(x), ext.Cond(intLtT(intLit(0), x), intLit(1), inner))
}

// intLessThanTrichotomy: ⊢ ((a<b) ∨ (b<a)) ∨ (a=b)   (LessThanTrichotomy, lifted from ℝ). The
// trichotomy source the `≠`-hyp split consumes (the `a=b` disjunct is killed
// under the `¬(a=b)` hyp). Like the other int order leaves it routes through the
// placeholder seam (intImplyLeaf), so it is exercised in tests and panics in a
// production build with no int bundle — LessThanTrichotomy is an ordinary lifted order
// lemma, not an integer-frontier leaf with a graceful-decline contract.
func intLessThanTrichotomy(a, b Term) *prop.PropWrapper {
	return intImplyLeaf(intLessThanTrichotomyThm(), []Term{a, b},
		or(or(intLtT(a, b), intLtT(b, a)), eqT(a, b)))
}

// intPowZero: ⊢ int_pow x 0 = &1   (int_pow's base clause).
func intPowZero(x Term) *prop.PropWrapper {
	return intEqLeaf(intPowZeroThm(), []Term{x}, intPowT(x, natZero), intLit(1))
}

// intPowSuc: ⊢ int_pow x (suc n) = x · int_pow x n   (int_pow's step clause).
func intPowSuc(x, n Term) *prop.PropWrapper {
	return intEqLeaf(intPowSucThm(), []Term{x, n}, intPowT(x, sucT(n)), intStarT(x, intPowT(x, n)))
}

// No intLeLt leaf: the LessEqSplit lift currently has no consumer on the int side
// (see the LessEqSplit bundle-field comment above).

// ── ℤ discreteness ───────────────────────────────────────────────────────────

// intDiscrete: ⊢ (a + &1 ≤ b) ⇔ (a < b)   (Discrete). The strict-row
// strengthening reads it as `(a<b) ⇒ (a+&1 ≤ b)` via EqSym+EqMP.
func intDiscrete(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intDiscreteThm(), []Term{a, b},
		intLeT(intPlusT(a, intLit(1)), b), intLtT(a, b))
}

// ── Leaves: square / pow-sign / abs ordering (lifted from ℝ) ──────────────────

// intSquareNonneg: ⊢ &0 ≤ x·x   (SquareNonneg, lifted from ℝ). The
// concluded form (no hypothesis). READ by intProveSquareNonneg.
func intSquareNonneg(x Term) *prop.PropWrapper {
	return intImplyLeaf(intSquareNonnegThm(), []Term{x}, intLeT(intLit(0), intStarT(x, x)))
}

// intSquareOfAbs: ⊢ int_pow (int_abs x) 2 = int_pow x 2   (SquareOfAbs). Strips abs
// from a squared expression. READ by intPowLawSimp; fires only for literal &2.
func intSquareOfAbs(x Term) *prop.PropWrapper {
	two := Numeral(2)
	return intEqLeaf(intSquareOfAbsThm(), []Term{x},
		intPowT(intAbsT(x), two), intPowT(x, two))
}

// intNegEqZero: ⊢ (−x = &0) ⇔ (x = &0)   (NegEqZero). Zero-detection through
// neg — the neg twin of NegNonneg/NegPositiveIffNegative. READ by intNegEqZeroSimp (atom rewrite
// in intArithSimpStep).
func intNegEqZero(x Term) *prop.PropWrapper {
	return intEqLeaf(intNegEqZeroThm(), []Term{x},
		eqT(intNegT(x), intLit(0)), eqT(x, intLit(0)))
}

// intAbsLessEqIffPowTwoLessEq: ⊢ (int_pow x 2 ≤ int_pow y 2) ⇔ (int_abs x ≤ int_abs y)
// (AbsLessEqIffPowTwoLessEq). Goal-side simp orientation — wantL (the LHS of the
// produced equality) is the SIMP INPUT (pow shape) so the deep-rewrite drives
// `x² ≤ y² → |x| ≤ |y|`; the bound statement is the reverse `(|x|≤|y|) ⇔ (x²≤y²)`
// orientation, macroEq flipping internally. (Same orientation as
// real_ops.go's realAbsLessEqIffPowTwoLessEqSimp.) READ by intAbsLessEqIffPowTwoLessEqSimp.
func intAbsLessEqIffPowTwoLessEq(x, y Term) *prop.PropWrapper {
	two := Numeral(2)
	return intEqLeaf(intAbsLessEqIffPowTwoLessEqThm(), []Term{x, y},
		intLeT(intPowT(x, two), intPowT(y, two)),
		intLeT(intAbsT(x), intAbsT(y)))
}

// intAbsTriangle: ⊢ int_abs(x + y) ≤ int_abs x + int_abs y   (AbsTriangle,
// binary). READ by intProveAbsTriangle (n-ary closed by iterating with LessEqAdd2
// + LessEqTrans).
func intAbsTriangle(x, y Term) *prop.PropWrapper {
	return intImplyLeaf(intAbsTriangleThm(), []Term{x, y},
		intLeT(intAbsT(intPlusT(x, y)),
			intPlusT(intAbsT(x), intAbsT(y))))
}

// intPowNonnegLeaf: ⊢ (&0 ≤ x) ⇒ (&0 ≤ int_pow x n)   (PowNonneg; symbolic n). READ
// by intProvePowSign.
func intPowNonnegLeaf(x, n Term) *prop.PropWrapper {
	return intImplyLeaf(intPowNonnegThm(), []Term{x, n},
		imply(intLeT(intLit(0), x), intLeT(intLit(0), intPowT(x, n))))
}

// intPowPosLeaf: ⊢ (&0 < x) ⇒ (&0 < int_pow x n)   (PowPos). READ by
// intProvePowSign.
func intPowPosLeaf(x, n Term) *prop.PropWrapper {
	return intImplyLeaf(intPowPosThm(), []Term{x, n},
		imply(intLtT(intLit(0), x), intLtT(intLit(0), intPowT(x, n))))
}

// intPowTwoNonneg: ⊢ &0 ≤ int_pow x 2   (PowTwoNonneg, no hyp). An even square is
// nonneg outright. READ by intProvePowSign's no-hyp fallback for literal n=2.
func intPowTwoNonneg(x Term) *prop.PropWrapper {
	return intImplyLeaf(intPowTwoNonnegThm(), []Term{x},
		intLeT(intLit(0), intPowT(x, Numeral(2))))
}

// ── Leaves: int_div/int_rem ↔ divides bridges ────────────────────────────────

// intDividesIffRemZero: ⊢ (int_rem(m,n) = &0) ⇔ int_divides(n, m)   (DividesIffRemZero). Goal-
// side simp orientation — wantL (the LHS of the produced equality) is the simp
// INPUT (`rem = &0` form) so the deep-rewrite drives `int_rem(m,n) = &0 →
// int_divides(n, m)`. READ by intDividesIffRemZeroSimp.
//
// The bound DividesIffRemZero (normal form) carries the INNER equality CNF-normalized —
// `&0 = int_rem(m,n)` (numeral on the left) — inside the iff's LHS. macroEq only
// flips the OUTER relation (EqSym on the whole iff), so it can never repair an
// equality nested inside one side; the leaf bridges that orientation itself:
// build the eq-symmetry iff ⊢ (int_rem(m,n) = &0) ⇔ (&0 = int_rem(m,n)) via Deduct
// over the two Assume+EqSym directions, then chain it into the instantiated
// bound iff with EqTrans. Real kernel composition, promise-transparent (the
// bound promise is forced only when the result is).
func intDividesIffRemZero(m, n Term) *prop.PropWrapper {
	wantL := eqT(intRemT(m, n), intLit(0))
	wantR := intDividesT(n, m)
	thm := intDividesIffRemZeroThm()
	// Direct orientation (or plain outer flip) first, in case the bound form
	// ever matches as-is.
	if w, ok := macroEq(thm, []Term{m, n}, wantL, wantR); ok {
		return w
	}
	if thm != nil {
		w := instAll(thm, []Term{m, n}) // ⊢ (&0 = int_rem(m,n)) ⇔ int_divides(n,m)
		l, r, ok := prop.MatchesEQ(w.Conclusion())
		if ok && r.AlphaEquals(wantR) && l.AlphaEquals(eqT(intLit(0), intRemT(m, n))) {
			// {&0 = rem} ⊢ rem = &0    and    {rem = &0} ⊢ &0 = rem
			fwd := prop.WrapProp(core.Assume(l)).EqSym()
			bwd := prop.WrapProp(core.Assume(wantL)).EqSym()
			// Deduct: ⊢ (int_rem(m,n) = &0) ⇔ (&0 = int_rem(m,n))
			symIff := fwd.Deduct(bwd)
			// EqTrans through the bound iff: ⊢ (int_rem(m,n) = &0) ⇔ divides.
			return symIff.EqTrans(w)
		}
	}
	return placeholderEq(thm, wantL, wantR)
}

// intDivisorBoundedByDividend: ⊢ int_divides(d, e) ⇒ ~(e = &0) ⇒ (int_abs d ≤ int_abs e)
// (DivisorBoundedByDividend). READ by intProveDivisorBound (an enrichment that injects
// `|d| ≤ |e|` when a divisibility hyp pairs with a derivable `e ≠ &0`).
func intDivisorBoundedByDividend(d, e Term) *prop.PropWrapper {
	return intImplyLeaf(intDivisorBoundedByDividendThm(), []Term{d, e},
		imply(intDividesT(d, e),
			imply(not(eqT(e, intLit(0))),
				intLeT(intAbsT(d), intAbsT(e)))))
}

// intQuotientExactOfDivides: ⊢ int_divides(q, m) ⇒ (int_div(m, q) · q = m)   (QuotientExactOfDivides).
// READ by intProveQuotientExact (enrichment under a divisibility hyp).
func intQuotientExactOfDivides(m, q Term) *prop.PropWrapper {
	return intImplyLeaf(intQuotientExactOfDividesThm(), []Term{m, q},
		imply(intDividesT(q, m), eqT(intStarT(intDivT(m, q), q), m)))
}

// intOfNumDiv: ⊢ int_div(int_of_num m, int_of_num n) = int_of_num(nat_div(m, n))
// (OfNumDiv). Bridge orientation matches the existing OfNumAdd/Mul
// pattern (wantL = the int operator side, wantR = the int_of_num-wrapped num
// expression), so intNormNatBin (nat_divmod.go's intNormNatDiv) reuses the
// same composition. macroEq flips internally if the bound statement is the
// reverse direction.
func intOfNumDiv(m, n Term) *prop.PropWrapper {
	return intEqLeaf(intOfNumDivThm(), []Term{m, n},
		intDivT(intOfNumT(m), intOfNumT(n)), intOfNumT(divT(m, n)))
}

// intOfNumRem: ⊢ int_rem(int_of_num m, int_of_num n) = int_of_num(nat_mod(m, n))
// (OfNumRem). Same orientation as intOfNumDiv.
func intOfNumRem(m, n Term) *prop.PropWrapper {
	return intEqLeaf(intOfNumRemThm(), []Term{m, n},
		intRemT(intOfNumT(m), intOfNumT(n)), intOfNumT(modT(m, n)))
}

// ── Leaves: distribution + agent-invoked + quantifier bridges ────────────────

// intDivMulAdd: ⊢ ~(n=&0) ⇒ (int_div(m + n·p, n) = int_div(m, n) + p)   (DivMulAdd).
// READ by intDivModAddMulFold — strips a `n·p` summand from the dividend.
func intDivMulAdd(m, n, p Term) *prop.PropWrapper {
	return intImplyLeaf(intDivMulAddThm(), []Term{m, n, p},
		imply(not(eqT(n, intLit(0))),
			eqT(intDivT(intPlusT(m, intStarT(n, p)), n),
				intPlusT(intDivT(m, n), p))))
}

// intRemMulAdd: ⊢ int_rem(m + n·p, n) = int_rem(m, n)   (RemMulAdd, unguarded —
// see the field doc). READ by intDivModAddMulFold — strips a `n·p` summand
// from rem's dividend.
func intRemMulAdd(m, n, p Term) *prop.PropWrapper {
	return intEqLeaf(intRemMulAddThm(), []Term{m, n, p},
		intRemT(intPlusT(m, intStarT(n, p)), n), intRemT(m, n))
}

// intDivisionAlgorithm: ⊢ ~(n=&0) ⇒ (m = int_div(m,n)·n + int_rem(m,n) ∧
//
//	&0 ≤ int_rem(m,n) ∧ int_rem(m,n) < int_abs(n))    (DivisionAlgorithm).
//
// The full bundled Euclidean-division identity. READ by IntDivisionAlgorithm (the
// exported, agent-invoked helper); NOT auto-wired in intArithSimpStep /
// intProveDecAtom (would compound with the bool/int_abs splits into expensive
// search; per README this stays demand-driven).
func intDivisionAlgorithm(m, n Term) *prop.PropWrapper {
	div := intDivT(m, n)
	rem := intRemT(m, n)
	eqId := eqT(m, intPlusT(intStarT(div, n), rem))
	remNonneg := intLeT(intLit(0), rem)
	remLtAbs := intLtT(rem, intAbsT(n))
	body := prop.And(eqId, prop.And(remNonneg, remLtAbs)) // right-assoc
	return intImplyLeaf(intDivisionAlgorithmThm(), []Term{m, n},
		imply(not(eqT(n, intLit(0))), body))
}

// intOfNumPow: ⊢ int_pow(int_of_num m, n) = int_of_num(nat_pow(m, n))
// (OfNumPow, lifted from ℝ's). The pow sibling of OfNumAdd /
// OfNumMul / OfNumDiv / OfNumRem. m: num, n: num (the exponent). READ by
// intPowSimp's OfNumPow clause — bridges `&m pow n` to num's nat_pow, which
// the num simp step then folds where it can (expSimp).
func intOfNumPow(m, n Term) *prop.PropWrapper {
	return intEqLeaf(intOfNumPowThm(), []Term{m, n},
		intPowT(intOfNumT(m), n), intOfNumT(expT(m, n)))
}

// intForallNonneg: ⊢ (∀x:int. &0 ≤ x ⇒ P x) ⇔ (∀n:num. P (int_of_num n))
// (ForallNonneg, the higher-order quantifier bridge). P is any int→bool term.
// READ by IntForallNonneg (exported), not auto-wired (quantifier handling lives
// above omega's atom-level decider).
func intForallNonneg(P Term) *prop.PropWrapper {
	x := core.Var(core.TermName("x"), dsl.IntType)
	n := core.Var(core.TermName("n"), dsl.NumType)
	lhs := ext.ForAll(x)(imply(intLeT(intLit(0), x), ext.Apply(P, x)))
	rhs := ext.ForAll(n)(ext.Apply(P, intOfNumT(n)))
	return intEqLeaf(intForallNonnegThm(), []Term{P}, lhs, rhs)
}

// intExistsNonneg: ⊢ (∃x:int. &0 ≤ x ∧ P x) ⇔ (∃n:num. P (int_of_num n))
// (ExistsNonneg, the existential dual). READ by IntExistsNonneg (exported).
func intExistsNonneg(P Term) *prop.PropWrapper {
	x := core.Var(core.TermName("x"), dsl.IntType)
	n := core.Var(core.TermName("n"), dsl.NumType)
	lhs := prop.Exists(x)(prop.And(intLeT(intLit(0), x), ext.Apply(P, x)))
	rhs := prop.Exists(n)(ext.Apply(P, intOfNumT(n)))
	return intEqLeaf(intExistsNonnegThm(), []Term{P}, lhs, rhs)
}

// IntDivisionAlgorithm is the exported, agent-invoked entry for intDivisionAlgorithm —
// returns the full `~(n=&0) ⇒ <int_div/int_rem identity-and-bounds>` implication. The
// agent calls this when a int_div/int_rem-heavy goal needs the complete identity in
// one shot; intProveDivRem (the auto-wired enrichment) splits it into smaller
// pieces for the common cases.
func IntDivisionAlgorithm(m, n Term) *prop.PropWrapper { return intDivisionAlgorithm(m, n) }

// IntForallNonneg / IntExistsNonneg export the quantifier bridges. A caller above
// omega's atom-level decider (engine / strategy layer) uses these to rewrite
// a `∀x:int. &0 ≤ x ⇒ P x` goal/hyp into the corresponding num quantifier
// before handing the body P(&n) back to num's automation.
func IntForallNonneg(P Term) *prop.PropWrapper { return intForallNonneg(P) }
func IntExistsNonneg(P Term) *prop.PropWrapper { return intExistsNonneg(P) }

// ── Leaves: abs / sgn algebraic laws ─────────────────────────────────────────

// intAbsMul: ⊢ int_abs(x·y) = int_abs x · int_abs y   (AbsMul).
func intAbsMul(x, y Term) *prop.PropWrapper {
	return intEqLeaf(intAbsMulThm(), []Term{x, y},
		intAbsT(intStarT(x, y)), intStarT(intAbsT(x), intAbsT(y)))
}

// intAbsEven: ⊢ int_abs(−x) = int_abs x   (AbsEven).
func intAbsEven(x Term) *prop.PropWrapper {
	return intEqLeaf(intAbsEvenThm(), []Term{x}, intAbsT(intNegT(x)), intAbsT(x))
}

// intAbsIdempotent: ⊢ int_abs(int_abs x) = int_abs x   (AbsIdempotent).
func intAbsIdempotent(x Term) *prop.PropWrapper {
	return intEqLeaf(intAbsIdempotentThm(), []Term{x}, intAbsT(intAbsT(x)), intAbsT(x))
}

// intOfNumAbs: ⊢ int_abs(int_of_num n) = int_of_num n   (OfNumAbs, n a num
// term).
func intOfNumAbs(n Term) *prop.PropWrapper {
	return intEqLeaf(intOfNumAbsThm(), []Term{n}, intAbsT(intOfNumT(n)), intOfNumT(n))
}

// intSgnMul: ⊢ int_sgn(x·y) = int_sgn x · int_sgn y   (SgnMul).
func intSgnMul(x, y Term) *prop.PropWrapper {
	return intEqLeaf(intSgnMulThm(), []Term{x, y},
		intSgnT(intStarT(x, y)), intStarT(intSgnT(x), intSgnT(y)))
}

// intSgnOdd: ⊢ int_sgn(−x) = −(int_sgn x)   (SgnOdd).
func intSgnOdd(x Term) *prop.PropWrapper {
	return intEqLeaf(intSgnOddThm(), []Term{x}, intSgnT(intNegT(x)), intNegT(intSgnT(x)))
}

// Integer (ℤ) ring normalizer + int_of_num norm_num bridge — the twin of
// realRing (real_lemmas.go). intRing instantiates the domain-generic ringVocab
// (ring.go) on intDomain + the int ring leaves above + the int norm bridge
// below; intNormalizeProof is what the discharge transports comparisons
// through. No sucBridge — ℤ has no successor, matching
// intDomain.matchSuc = nil.
var intRing = &ringVocab{
	dom: intDomain, plusOp: intPlus, starOp: intStar,
	commuteADD: intCommuteADD, associateADD: intAssociateADD,
	commuteMUL: intCommuteMUL, associateMUL: intAssociateMUL,
	distributeMUL: intDistributeMUL, rightDistrib: intRightDistrib,
	oneMul: intOneMul, addZeroR: intAddZeroR, zeroMul: intZeroMul,
	normAdd: intNormNatAdd, normMul: intNormNatMul,
	mulSort: intMulSort, decomposeStar: intDecomposeStar, mulZeroR: intMulZeroR,
}

// The ℤ linear extraction reads a product of atoms over the monomial basis
// (Domain.polyMul, domain.go), as num and real do. Like real it is a pure
// change of basis — intBuildAll injects no sign rows, a product of integers
// is an integer, so a monomial atom is one more free unknown — and the
// replay is intRing.normalizeProof's mirrored expansion. Wired here rather
// than in intDomain's literal: intRing names intDomain, so the literal
// naming intRing back would be an initialization cycle.
func init() { intDomain.polyMul = intRing.polyMul }

// intNormalizeProof returns (linForm of t, ⊢ t = buildTerm(linForm), ok) — the
// ℤ ring normalization the replay transports comparisons through.
func intNormalizeProof(t Term) (linForm, *prop.PropWrapper, bool) {
	return intRing.normalizeProof(t)
}

// intOfNumArgs peels `&m ⋆ &n`'s operands to their num arguments. ok=false if a
// side is not int_of_num-applied; literal-ness (bit-tree shape) is gated by the
// num evaluator the callers run BEFORE building any bridge leaf.
func intOfNumArgs(l, r Term) (m, n Term, ok bool) {
	m, okL := MatchesIntOfNum(l)
	n, okR := MatchesIntOfNum(r)
	return m, n, okL && okR
}

// intNormNatBin: ⊢ &m ⋆ &n = &k for ⋆ ∈ {+, ·} — the int_of_num bridge oriented
// to `&m ⋆ &n = &(m ⋆ n)`, then the num evaluation `⊢ m ⋆ n = k` lifted through
// int_of_num congruence. ok=false unless both sides are `&<bit-tree>` literals.
func intNormNatBin(l, r Term, intOp, numOp func(a, b Term) Term,
	bridgeThm *prop.PropWrapper, eval func(x, y Term) (*prop.PropWrapper, bool)) (*prop.PropWrapper, bool) {
	m, n, ok := intOfNumArgs(l, r)
	if !ok {
		return nil, false
	}
	inner, ok := eval(m, n) // ⊢ m ⋆ n = k
	if !ok {
		return nil, false
	}
	// ⊢ &m ⋆ &n = &(m ⋆ n)   (eqLeaf flips the bound form when it states the reverse)
	bridge := intEqLeaf(bridgeThm, []Term{m, n}, intOp(l, r), intOfNumT(numOp(m, n)))
	return bridge.EqTrans(inner.LeftApply(intOfNum)), true // ⊢ &m ⋆ &n = &k
}

// intNormNatAdd proves ⊢ &m + &n = &k (k = m+n) via OfNumAdd.
func intNormNatAdd(l, r Term) (*prop.PropWrapper, bool) {
	return intNormNatBin(l, r, intPlusT, plus, intOfNumAddThm(), NormNatAdd)
}

// intNormNatMul proves ⊢ &m * &n = &k (k = m·n) via OfNumMul.
func intNormNatMul(l, r Term) (*prop.PropWrapper, bool) {
	return intNormNatBin(l, r, intStarT, star, intOfNumMulThm(), NormNatMul)
}

// intNormNatCmp: ⊢ (&m ⋈ &n) ⇔ ⊤/⊥ — the int_of_num bridge oriented to
// `(&m ⋈ &n) ⇔ (m ⋈ n)`, closed by the num comparison verdict.
func intNormNatCmp(l, r Term, intRel, numRel func(a, b Term) Term,
	bridgeThm *prop.PropWrapper, eval func(x, y Term) (*prop.PropWrapper, bool)) (*prop.PropWrapper, bool) {
	m, n, ok := intOfNumArgs(l, r)
	if !ok {
		return nil, false
	}
	verdict, ok := eval(m, n) // ⊢ (m ⋈ n) ⇔ ⊤/⊥
	if !ok {
		return nil, false
	}
	bridge := intEqLeaf(bridgeThm, []Term{m, n}, intRel(l, r), numRel(m, n))
	return bridge.EqTrans(verdict), true // ⊢ (&m ⋈ &n) ⇔ ⊤/⊥
}

// intNormNatLt proves ⊢ (&m < &n) ⇔ ⊤/⊥ via OfNumLt.
func intNormNatLt(l, r Term) (*prop.PropWrapper, bool) {
	return intNormNatCmp(l, r, intLtT, lt, intOfNumLtThm(), NormNatLt)
}

// intNormNatLe proves ⊢ (&m ≤ &n) ⇔ ⊤/⊥ via OfNumLe.
func intNormNatLe(l, r Term) (*prop.PropWrapper, bool) {
	return intNormNatCmp(l, r, intLeT, le, intOfNumLeThm(), NormNatLe)
}

// intNormNatEq proves ⊢ (&m = &n) ⇔ ⊤/⊥ via OfNumEq.
func intNormNatEq(l, r Term) (*prop.PropWrapper, bool) {
	return intNormNatCmp(l, r, eqT, eqT, intOfNumEqThm(), NormNatEq)
}

// IntRingProve is the ℤ twin of RealRingProve: ⊢ l = r over the int linear
// semiring (AC + identity + distribution + numeral folding), or (nil,false).
func IntRingProve(l, r Term) (*prop.PropWrapper, bool) { return intRing.ringProve(l, r) }

// IntOfRealThm — the meta-derivation that lifts a proven theorem over ℝ
// to its ℤ analogue. The whole ℤ order/ring suite comes by feeding each
// ℝ theorem through this one rule — so a single proven ℝ theorem
// + the homomorphism bridges yields the corresponding ℤ one with no per-theorem
// proof search.
//
// This is the BUNDLE-DERIVATION tool, distinct from omega's int DECISION layer
// (intDomain / int_linarith.go), which is deliberately real_of_int-free.
// IntOfRealThm is what serve.InstallIntLemmaBundle calls to populate the
// lifted IntLemmaBundle fields from the real bundle's theorems.
//
// The algorithm:
//
//  1. for each ∀-bound real variable `v:real`, specialize it to
//     `real_of_int(v:int)` (so the body talks about embedded integers);
//  2. DEPTH-rewrite with the homomorphism bridges reversed — collapsing
//     `real_of_int a ⋆ real_of_int b → real_of_int(a ⋆ b)` (ops) and
//     `real_of_int a ⋈ real_of_int b → (a ⋈ b)` (comparisons), and
//     `real_of_num n → real_of_int(int_of_num n)` (literals) — until every real
//     operation has become an int operation and the real_of_int's cancel out;
//  3. re-generalize over the int variables.
//
// Conjunctions at the top level recurse on each conjunct.
//
// Soundness is the kernel's, by construction: every step is a primitive
// inference (instantiate / rewrite-via-EqMP / generalize), so whatever `Thm` this
// returns IS a theorem. The only thing to verify is that the output is the
// INTENDED statement over ℤ — a cheap `Conclusion().AlphaEquals(want)` check the
// caller (or a test) does. Replay is unnecessary: there is no emitted artifact,
// only an install-time derived cert, exactly like InstallRealBundle's
// CurryIffConj / fromGeneral / derived-LessEqOfEqSwapped adapters.
//
// Input contract: `realThm` is a hyp-free, ∀-closed `⊢ ∀reals. φ(reals)`. Bridges
// absent from `br` simply aren't applied — a `φ` that needs a missing bridge will
// not fully collapse, and the residual real operators show up in the output
// statement (caught by the caller's shape check).

// IntBridges holds the int↔real homomorphism theorems
// (int_construction's bridges) — the rewrite
// material IntOfRealThm consumes. Each is the stated orientation
// (defined-int-side = real-side); IntOfRealThm takes the symmetric form internally.
//
// Coverage: every operator/comparison that appears on either side of a
// lifted theorem needs a bridge here —
// otherwise the lift leaves residual `real_of_int(...)` wrappings around
// that operator and the output shape check trips. Today's set covers the
// linear ring + order + unary algebra + abs/max/min.
type IntBridges struct {
	// Comparison/equality definitions: `(x ⋈_int y) ⇔ (real_of_int x ⋈_real
	// real_of_int y)` for ⋈ ∈ {=, ≤, <, ≥, >}; the reversed bridge rewrites a real
	// comparison over embedded ints into the int comparison.
	Eq, Le, Lt, Ge, Gt *prop.PropWrapper

	// OfNum: `real_of_int(int_of_num n) = real_of_num n`; the
	// reversed bridge rewrites a real numeral `&n` into `real_of_int(int_of_num n)`.
	OfNum *prop.PropWrapper

	// Operator homomorphisms: `real_of_int(x ⋆_int y) = real_of_int x ⋆_real
	// real_of_int y` for ⋆ ∈ {+, ·, −} and the unary `−`; the reversed bridge folds a
	// real op over embedded ints into the embedding of the int op.
	Add, Mul, Sub, Neg *prop.PropWrapper

	// Algebraic unary bridges that the abs/max/min/sgn families of ℝ laws
	// need: `real_of_int(abs x) = abs(real_of_int x)` (Abs, REVERSED
	// orientation), `real_of_int(max x y) = max(real_of_int x)(real_of_int y)`
	// (Max), the matching Min, and
	// `real_of_int(int_sgn x) = real_sgn(real_of_int x)` (Sgn).
	// Without these, the abs / max / min / sgn content of a source ℝ
	// theorem can't collapse and the lift output shape check fails.
	Abs, Max, Min, Sgn *prop.PropWrapper

	// Pow: `real_of_int(int_pow x n) = real_pow(real_of_int x, n)`.
	// Asymmetric in arity — first arg is an int (gets the real_of_int wrapper),
	// second arg is a num exponent (no wrapper). RHS therefore does NOT match
	// structuralBridgeRewrite's "all RHS args are real_of_int(<binder>)" shape,
	// so this bridge collapses only via gsymPatternRewrite (the HO-unify path).
	Pow *prop.PropWrapper
}

// realOfInt vocabulary (the bridge embedding ℤ → ℝ). Lives here, NOT in
// domain.go, so the decision layer stays real_of_int-free.
var realOfInt = dsl.RealOfIntMeta.Term()

func realOfIntT(x Term) Term { return ext.Apply(realOfInt, x) }

// MatchesRealOfInt reports whether t is `real_of_int(x)` and returns (x, true).
func MatchesRealOfInt(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(realOfInt) {
		return a.Arg(), true
	}
	return nil, false
}

// gsymPatternRewrite turns a bridge `⊢ ∀vars. L = R` into a deep, hyp-free
// pattern rewrite that replaces instances of R with L (the reversed direction).
//
// It reuses prop's unification rewrite: strip the ∀ (keeping the vars free),
// EqSym to the R = L orientation, re-Abs the freed vars into `⊢ λvars. R =
// λvars. L`, then prop.UnifyEqRewrite. The theorem is hyp-free throughout, so
// the produced rewrites contribute no hypotheses. (This is the proven-theorem
// analogue of ContextAbsEq + unifyEqRewrite, minus the lemma-as-hyp seam.)
func gsymPatternRewrite(bridge *prop.PropWrapper) prop.Rewrite {
	body, vars := bridge.StripConclForAll() // freed binders for re-Abs
	th := body.EqSym()                      // ⊢ R = L  (symmetry)
	for i := len(vars) - 1; i >= 0; i-- {
		th = th.Abs(vars[i]) // re-abstract → ⊢ λvars. R = λvars. L
	}
	return prop.UnifyEqRewrite(th)
}

// structuralBridgeRewrite is the depth-agnostic structural sibling of
// gsymPatternRewrite for bridges shaped `∀v₁…vₙ. L(v...) = R(real_of_int(v₁),
// …, real_of_int(vₙ))` where every RHS arg is `real_of_int(<binder var>)`.
// Returns nil for bridges that don't fit the shape (e.g. OfNum, whose RHS arg
// is a num var, not a real_of_int).
//
// Motivation: gsymPatternRewrite routes the rewrite through prop.UnifyEqRewrite
// (Huet-style HO unification), which has an ad-hoc cycle guard
// (ext/unify.containsUnaryOperatorCycle) that skips imitation when the rigid
// head is a unary const at chain depth ≥ 2 — even when the chain bottoms out
// at a non-flex term, where imitation would terminate. That false-positive blocks
// the Eq bridge from collapsing `real_of_int(int_neg(int_neg(x))) =
// real_of_int(x)` (NegNeg-shaped) and `real_of_int(int_abs(int_abs(x))) =
// real_of_int(int_abs(x))` (AbsIdempotent-shaped), leaving real_of_int residue.
//
// The structural rewriter sidesteps the unifier entirely: it pattern-matches a
// target `R_head(real_of_int(A_1), ..., real_of_int(A_n))` directly, then SPECs
// the bridge with the extracted A_i and EqSyms to put the rewrite in the
// real-side → int-side direction. The A_i themselves can be arbitrarily nested
// — they're just terms passed through TermInst, not unification slots.
//
// All comparison bridges (Eq/Le/Lt/Ge/Gt) and operator/algebraic bridges that
// fit the shape (Add/Mul/Sub/Neg/Abs/Max/Min/Sgn) qualify; OfNum does not
// (its RHS is `real_of_num n`, with n a num var rather than a real_of_int).
func structuralBridgeRewrite(bridge *prop.PropWrapper) prop.Rewrite {
	body, vars := bridge.StripConclForAll() // ⊢ L(vars) = R(real_of_int(vars))
	l, r, ok := core.MatchesEQ(body.Conclusion())
	if !ok {
		return nil
	}
	rHead, rArgs := ext.MatchesApply(r)
	if len(rArgs) != len(vars) {
		return nil
	}
	// Build {arg-position → bridge-binder-var} so the substitution we apply at
	// match time mirrors the binder order rather than the arg-position order
	// (e.g. int_eq's binders are [y, x] and the RHS pattern is
	// `real_of_int y = real_of_int x` — arg 0 ↔ y, arg 1 ↔ x).
	binderForArg := make([]core.VarTerm, len(rArgs))
	for i, a := range rArgs {
		inner, ok := MatchesRealOfInt(a)
		if !ok {
			return nil
		}
		v, ok := inner.AsVar()
		if !ok {
			return nil
		}
		// Confirm this is one of the bridge's bound vars.
		found := false
		for _, bv := range vars {
			if v.EqualsVar(bv) {
				found = true
				break
			}
		}
		if !found {
			return nil
		}
		binderForArg[i] = v
	}
	_ = l // body's LHS is what we rewrite TO, materialized via body.EqSym() at fire time.
	return func(t Term) *prop.PropWrapper {
		tHead, tArgs := ext.MatchesApply(t)
		if !tHead.Equals(rHead) || len(tArgs) != len(rArgs) {
			return nil
		}
		substs := make([]core.TermSubst, len(tArgs))
		for i, ta := range tArgs {
			x, ok := MatchesRealOfInt(ta)
			if !ok {
				return nil
			}
			substs[i] = core.MakeTermSubst(binderForArg[i], x)
		}
		// body = ⊢ L(vars) = R(real_of_int(vars))
		// body.EqSym() = ⊢ R(real_of_int(vars)) = L(vars)
		// .TermInst(substs) = ⊢ R(real_of_int(args)) = L(args) — i.e. ⊢ t = result.
		return body.EqSym().TermInst(substs...)
	}
}

// condPushRealOfInt is the generic COND homomorphism completion of the bridge
// set: ⊢ COND(g, real_of_int(a), real_of_int(b)) = real_of_int(COND(g, a, b)).
//
// The bridges collapse real OPERATORS and COMPARISONS over embedded ints, but
// COND is polymorphic — not a real-vocabulary const — so there is no
// bridge row for it to bind. A piecewise real source (the real_sgn / real_max
// / real_min defs) would therefore stall mid-lift with real_of_int residue
// on the COND branches (`real_of_int(int_sgn x) = COND(g, real_of_int(&1),
// …)`), and the downstream bundle-leaf α-match (macroEq) would reject it.
// Pushing real_of_int out through COND is guard-agnostic (a function applied to a COND moves into both arms)
// and derivable on the spot: case-split on g, collapse both sides' CONDs
// under each verdict (CondClauseT/F), recombine via ByCases +
// excluded middle. With the COND pushed out, the enclosing bridge (Eq for the
// piecewise defs) fires in the same DeepRewrite fixpoint and the lift lands
// in pure int vocabulary.
//
// Literal ⊤/⊥ guards are declined — those CONDs are the trivial-collapse
// rewrites' business, and a self-rewrite of ⊤ under the ⊤-verdict would spin
// the branch fixpoint.
func condPushRealOfInt(t Term) *prop.PropWrapper {
	g, x, y, ok := ext.MatchesCond(t)
	if !ok || g.Equals(prop.T) || g.Equals(prop.F) {
		return nil
	}
	a, ok := MatchesRealOfInt(x)
	if !ok {
		return nil
	}
	b, ok := MatchesRealOfInt(y)
	if !ok {
		return nil
	}
	rhs := realOfIntT(ext.Cond(g, a, b))
	// branch: under a guard verdict `{h} ⊢ g ⇔ ⊤/⊥`, rewrite every g to its
	// truth value and fold the trivialized CONDs on BOTH sides; the two sides
	// meet at the same branch value, so EqTrans closes `{h} ⊢ t = rhs`.
	branch := func(verdict *prop.PropWrapper) *prop.PropWrapper {
		guardRule := func(s Term) *prop.PropWrapper {
			if s.AlphaEquals(g) {
				return verdict
			}
			return nil
		}
		condRule := func(s Term) *prop.PropWrapper {
			if c, u, v, ok := ext.MatchesCond(s); ok {
				if c.Equals(prop.T) {
					return prop.CondClauseT(u, v)
				}
				if c.Equals(prop.F) {
					return prop.CondClauseF(u, v)
				}
			}
			return nil
		}
		deep := prop.DeepRewrite(guardRule, condRule)
		lw := deep(t)                 // {h} ⊢ t = value
		rw := deep(rhs)               // {h} ⊢ rhs = value
		return lw.EqTrans(rw.EqSym()) // {h} ⊢ t = rhs
	}
	impT := branch(eqtIntro(prop.Assume(g))).PromoteHyp(g)           // ⊢ g ⇒ (t = rhs)
	impF := branch(eqfIntro(prop.Assume(not(g)))).PromoteHyp(not(g)) // ⊢ ¬g ⇒ (t = rhs)
	return prop.ByCases(core.Eq(t, rhs), g, not(g)).
		DeriveHypFrom(prop.ExcludedMiddle(g)).
		DeriveHypFrom(impT).
		DeriveHypFrom(impF)
}

// deepRewrite builds the combined reversed-bridge deep rewrite from the present
// bridges. Each gsymPatternRewrite is itself deep; prop.DeepRewrite stacks them
// and iterates to fixpoint, so nested forms (`real_of_int a + real_of_int b ≤
// real_of_int c`) collapse innermost-first then re-fire at the parent.
//
// For each bridge we stack BOTH the gsymPatternRewrite (HO-unification path,
// retained for backwards compatibility with shapes where it suffices) AND a
// structural rewriter (when the bridge's shape qualifies; see
// structuralBridgeRewrite). The structural rewriter is the one that fires for
// targets whose unary-const args are depth ≥ 2 — the cases the HO unifier's
// cycle guard rejects.
func (br *IntBridges) deepRewrite() prop.Rewrite {
	var rws []prop.Rewrite
	for _, b := range []*prop.PropWrapper{
		br.Eq, br.Le, br.Lt, br.Ge, br.Gt,
		br.OfNum,
		br.Add, br.Sub, br.Neg, br.Mul,
		br.Abs, br.Max, br.Min, br.Sgn,
		br.Pow,
	} {
		if b != nil {
			rws = append(rws, gsymPatternRewrite(b))
			if s := structuralBridgeRewrite(b); s != nil {
				rws = append(rws, s)
			}
		}
	}
	// The bridge-free COND homomorphism (see condPushRealOfInt): pushes
	// real_of_int out through a COND whose branches are both embedded ints,
	// so the enclosing bridge can fire in the same fixpoint.
	rws = append(rws, condPushRealOfInt)
	return prop.DeepRewrite(rws...)
}

// IntOfRealThm lifts a proven theorem over ℝ to its ℤ analogue using the
// homomorphism bridges in br. See the file header for the contract.
func IntOfRealThm(realThm *prop.PropWrapper, br *IntBridges) *prop.PropWrapper {
	return intOfReal(realThm, br.deepRewrite())
}

// installedIntBridges is the process-global bridge set used by
// Script.IntOfRealDerive — the body of every registry.Lifted member.
// Set once at startup by serve.InstallIntBundle (or equivalent),
// separately from SetIntLemmaBundle's `intLemmaBundle`. Nil by default —
// IntOfRealDerive panics with a pointed message when asked to lift
// without bridges, so a misconfiguration surfaces at the call site
// instead of as a downstream cache miss / α-mismatch.
var installedIntBridges *IntBridges

// SetIntBridges installs the IntBridges used by Script.IntOfRealDerive
// (a Lifted member's build). Pass nil to revert
// to the no-bridges-installed state. Independent of SetIntLemmaBundle:
// IntLemmaBundle drives omega's int *decision* layer, IntBridges drives
// the *library-side lift* of ℝ laws to ℤ.
func SetIntBridges(br *IntBridges) { installedIntBridges = br }

// CurrentIntBridges returns the installed bridges, or nil if none.
// Used by Script.IntOfRealDerive to keep the bridge set out of every
// call site's argument list.
func CurrentIntBridges() *IntBridges { return installedIntBridges }

// intOfReal is the recursive worker (shares one prebuilt deep rewrite across the
// conjunction recursion).
func intOfReal(th *prop.PropWrapper, deep prop.Rewrite) *prop.PropWrapper {
	// Split a top-level conjunction, lift each side, rejoin.
	if a, b, ok := prop.MatchesAND(th.Conclusion()); ok {
		c0 := intOfReal(th.DeriveTrans(prop.HypAND0(a, b)), deep) // ⊢ intOf(A)
		c1 := intOfReal(th.DeriveTrans(prop.HypAND1(a, b)), deep) // ⊢ intOf(B)
		return prop.ConclAND(c0.Conclusion(), c1.Conclusion()).
			DeriveHypFrom(c0).
			DeriveHypFrom(c1)
	}
	return intOfRealForall(th, deep)
}

// intOfRealForall handles a single (non-conjunction) statement: specialize the
// real ∀-vars to real_of_int(v:int), collapse the real structure to int, then
// re-generalize over the int vars.
//
// The per-binder instantiation target differs (a real var → real_of_int(v:int),
// any other var → itself), so this is neither a strip of every binder nor a fixed instantiation list: it
// discovers the binders term-side (DecomposesFORALL), builds the instantiation
// terms, and feeds them through ConclForAllInsts / ConclForAllList (prop_wrapper.go).
func intOfRealForall(th *prop.PropWrapper, deep prop.Rewrite) *prop.PropWrapper {
	binders, _ := ext.DecomposesFORALL(th.Conclusion())
	var insts []Term         // per-binder instantiation target
	var regen []core.VarTerm // the int vars to re-generalize over (outer→inner)
	for v := range binders.Iter() {
		if v.Type().Equals(dsl.RealType) {
			vInt := core.Var(v.Name(), dsl.IntType)
			insts = append(insts, realOfIntT(vInt)) // v:real ↦ real_of_int(v:int)
			regen = append(regen, vInt)
		} else {
			insts = append(insts, v) // non-real var: keep as itself
			regen = append(regen, v)
		}
	}
	th = th.ConclForAllInsts(insts...)
	// NOTE: only OUTER ∀-bound real vars are lifted — IntOfRealThm's
	// contract is a source in the NORMALIZED (∀-closed) form. Callers with
	// an arbitrary original surface must canonicalize first
	// (prop.Normalize), as Script.IntOfRealDerive does; teaching this
	// function individual surface shapes (free-var, nested binders, …)
	// is a coincidence-chasing dead end.
	// Collapse real ops/comparisons/literals → int, β-normalizing between passes:
	// UnifyEqRewrite leaves its result as an un-reduced redex `(λvars.L)(args)`
	// (its contract — callers β-reduce), and an un-reduced redex can block a
	// parent bridge match, so we iterate (bridge-rewrite ; DeepBeta) to a fixpoint.
	// Both steps strictly shrink (fewer real ops / fewer redexes), so it terminates.
	for {
		before := th.Conclusion()
		th = th.RewriteConcl(deep).RewriteConcl(prop.DeepBeta)
		if th.Conclusion().AlphaEquals(before) {
			break
		}
	}
	return th.ConclForAllList(regen...)
}
