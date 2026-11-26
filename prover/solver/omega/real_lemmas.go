package omega

import "github.com/euc-ai/xugo/ext/prop"

// ── Ring AC / identity / distribution leaves (consumed by realRing — the ℝ ───
// instance of the ring-normalizer vocabulary, below). Unlike num — whose
// identity leaves project out of the AddClauses/MulClauses conjunctions —
// every real leaf binds a standalone corpus theorem, so all nine are direct
// eqLeaf macros. Orientation: the bound normal forms of most of these are
// REVERSED relative to the engine shapes below (e.g. AddAssoc is `x+(y+z) = (x+y)+z`,
// MulLeftId is `x = &1·x`); eqLeaf auto-flips. Binder order matches instAll
// args except where noted (realRightDistrib).

// realCommuteADD: ⊢ a + b = b + a   (AddSym)
func realCommuteADD(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realAddSymThm(), []Term{a, b}, realPlusT(a, b), realPlusT(b, a))
}

// realAssociateADD: ⊢ (a + b) + c = a + (b + c)   (AddAssoc, reversed)
func realAssociateADD(a, b, c Term) *prop.PropWrapper {
	return realEqLeaf(realAddAssocThm(), []Term{a, b, c},
		realPlusT(realPlusT(a, b), c), realPlusT(a, realPlusT(b, c)))
}

// realCommuteMUL: ⊢ a · b = b · a   (MulSym)
func realCommuteMUL(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realMulSymThm(), []Term{a, b}, realStarT(a, b), realStarT(b, a))
}

// realAssociateMUL: ⊢ (a · b) · c = a · (b · c)   (MulAssoc, reversed)
func realAssociateMUL(a, b, c Term) *prop.PropWrapper {
	return realEqLeaf(realMulAssocThm(), []Term{a, b, c},
		realStarT(realStarT(a, b), c), realStarT(a, realStarT(b, c)))
}

// realDistributeMUL: ⊢ a · (b + c) = a·b + a·c   (LeftDistrib, reversed)
func realDistributeMUL(a, b, c Term) *prop.PropWrapper {
	return realEqLeaf(realLeftDistribThm(), []Term{a, b, c},
		realStarT(a, realPlusT(b, c)), realPlusT(realStarT(a, b), realStarT(a, c)))
}

// realRightDistrib: ⊢ (a + b) · c = a·c + b·c   (RightDistrib, reversed).
// The bound statement's binders are (a, m, b) with m the SHARED right factor —
// `a·m + b·m = (a+b)·m` — so the instAll order is [a, c, b], NOT [a, b, c].
func realRightDistrib(a, b, c Term) *prop.PropWrapper {
	return realEqLeaf(realRightDistribThm(), []Term{a, c, b},
		realStarT(realPlusT(a, b), c), realPlusT(realStarT(a, c), realStarT(b, c)))
}

// realOneMul: ⊢ &1 · a = a   (MulLeftId, reversed)
func realOneMul(a Term) *prop.PropWrapper {
	return realEqLeaf(realMulLeftIdThm(), []Term{a}, realStarT(realLit(1), a), a)
}

// realAddZeroR: ⊢ a + &0 = a   (AddRightId, reversed)
func realAddZeroR(a Term) *prop.PropWrapper {
	return realEqLeaf(realAddRightIdThm(), []Term{a}, realPlusT(a, realLit(0)), a)
}

// realZeroMul: ⊢ &0 · a = &0   (MulLeftZero, reversed)
func realZeroMul(a Term) *prop.PropWrapper {
	return realEqLeaf(realMulLeftZeroThm(), []Term{a}, realStarT(realLit(0), a), realLit(0))
}

// Real-domain leaf lemmas for the linarith certificate replay over ℝ — the mirror of
// the num leaves in nat_linarith.go. Each is the RealLemmaBundle's named theorem instantiated
// (and oriented, for the iff ones) to the stated shape, else a bundle-nil
// placeholder stand-in. The generic leaf machinery (eqLeaf / implyLeaf / macroEq
// / macroThm / instAll / placeholderConcl / placeholderEq) is domain-agnostic and
// reused verbatim; only the builders (realLeT/realLtT/realPlusT/realStarT/
// realLit, plus the type-generic eqT) and the bundle accessors differ.
//
// The theorems instantiated: NotLessThan/NotLessEq, LessEqAntisym, LessEqOfEq,
// LessEqAdd2 / LessThanAdd2 / LessEqLessThanAdd2 / LessThanLessEqAdd2,
// LessEqAddLeft / LessThanAddLeft, LessEqMulLeft / LessThanMulLeft, GtDef / GeDef.
//
// Note vs num: there is no realZeroLe — ℝ has no `0 ≤ x` default, and the real
// refutation injects no nonnegativity rows.

// ── goal-negation duality (used by RealLinProve) ─────────────────────────────

// realNotLT: ⊢ ¬(M<N) ⇔ (N≤M)   (NotLessThan)
func realNotLT(m, n Term) *prop.PropWrapper {
	return realEqLeaf(realNotLessThanThm(), []Term{m, n}, not(realLtT(m, n)), realLeT(n, m))
}

// realNotLE: ⊢ ¬(M≤N) ⇔ (N<M)   (NotLessEq)
func realNotLE(m, n Term) *prop.PropWrapper {
	return realEqLeaf(realNotLessEqThm(), []Term{m, n}, not(realLeT(m, n)), realLtT(n, m))
}

// realLessEqAntisym: ⊢ (A≤B) ⇒ (B≤A) ⇒ (A=B)   (LessEqAntisym)
func realLessEqAntisym(a, b Term) *prop.PropWrapper {
	return realImplyLeaf(realLessEqAntisymThm(), []Term{a, b},
		imply(realLeT(a, b), imply(realLeT(b, a), eqT(a, b))))
}

// ── provenance of expanded rows ──────────────────────────────────────────────

// realLessEqOfEq: ⊢ (A = B) ⇒ (A ≤ B)   (LessEqOfEq)
func realLessEqOfEq(a, b Term) *prop.PropWrapper {
	return realImplyLeaf(realLessEqOfEqThm(), []Term{a, b}, imply(eqT(a, b), realLeT(a, b)))
}

// realLessEqOfEqSwapped: ⊢ (A = B) ⇒ (B ≤ A)   (LessEqOfEq on the swapped equality)
func realLessEqOfEqSwapped(a, b Term) *prop.PropWrapper {
	return realImplyLeaf(realLessEqOfEqSwappedThm(), []Term{a, b}, imply(eqT(a, b), realLeT(b, a)))
}

// ── monotone scaling by a positive numeral (LessEqMulLeft / LessThanMulLeft) ──────
// The real scaling lemma carries a nonnegativity premise on the multiplier —
// `&0 ≤ c` for `≤` (LessEqMulLeft), strict `&0 < c` for `<` (LessThanMulLeft) — the
// scaling side condition. The bundle fields hold the curried forms
//
//	LessEqMulLeft: ∀c a b. (&0 ≤ c) ⇒ (a ≤ b) ⇒ (c·a ≤ c·b)
//	LessThanMulLeft: ∀c a b. (&0 < c) ⇒ (a < b) ⇒ (c·a < c·b)
//
// (binder order = the leaf's instAll order [c, a, b]; the corpus statements
// normalize to CNF clauses with binders (y,z,x), so install routes them through
// PromiseForGeneral, the same seam as the *Add2 family). The leaf instantiates
// at the CONCRETE Farkas multiplier and discharges the side condition
// numerically through the real norm_num bridge (realNormNatLe/Lt — c is always
// ≥ 2 here: λ=1 rows skip scaling), mirroring the nat ltScale's `c≠0` discharge.

// realScale is the shared scale-leaf body for the two strictness variants.
// side(⊢ &0 ⋈ &c verdict) comes from the norm_num bridge; falls through to the
// placeholder seam when the field is absent, mis-shaped, or the side condition
// does not evaluate to ⊤ (panics in a non-test build, bundle.go).
func realScale(thm *prop.PropWrapper, c _Integer, a, b Term,
	rel func(x, y Term) Term, side func(l, r Term) (*prop.PropWrapper, bool)) *prop.PropWrapper {
	cT := realLitOf(c)
	want := imply(rel(a, b), rel(realMonoTerm(c, a), realMonoTerm(c, b)))
	if thm != nil {
		inst := instAll(thm, []Term{cT, a, b}) // (&0⋈&c) ⇒ (a⋈b) ⇒ (c·a ⋈ c·b)
		if sd, ok := side(realLit(0), cT); ok && prop.Rhs(sd).Equals(prop.T) {
			// iffTrueElim(sd) = ⊢ &0 ⋈ &c; discharge the field's first premise.
			res := inst.DemoteHyp().DeriveHypFrom(iffTrueElim(sd))
			if res.Conclusion().AlphaEquals(want) {
				return res
			}
		}
	}
	return placeholderConcl(thm, want)
}

// realLeScale: ⊢ (A ≤ B) ⇒ (c·A ≤ c·B)   (c ≥ 1; LessEqMulLeft, `&0 ≤ &c` side)
func realLeScale(c _Integer, a, b Term) *prop.PropWrapper {
	return realScale(realLessEqMulLeftThm(), c, a, b, realLeT, realNormNatLe)
}

// realLtScale: ⊢ (A < B) ⇒ (c·A < c·B)   (c ≥ 1; LessThanMulLeft, `&0 < &c` side)
func realLtScale(c _Integer, a, b Term) *prop.PropWrapper {
	return realScale(realLessThanMulLeftThm(), c, a, b, realLtT, realNormNatLt)
}

// ── pairwise inequality addition (strictness combinations) ───────────────────

// realAddLe2: ⊢ (A≤B) ⇒ (C≤D) ⇒ (A+C ≤ B+D)   (LessEqAdd2)
func realAddLe2(a, b, c, d Term) *prop.PropWrapper {
	return realImplyLeaf(realLessEqAdd2Thm(), []Term{a, b, c, d},
		imply(realLeT(a, b), imply(realLeT(c, d), realLeT(realPlusT(a, c), realPlusT(b, d)))))
}

// realAddLt2: ⊢ (A<B) ⇒ (C<D) ⇒ (A+C < B+D)   (LessThanAdd2)
func realAddLt2(a, b, c, d Term) *prop.PropWrapper {
	return realImplyLeaf(realLessThanAdd2Thm(), []Term{a, b, c, d},
		imply(realLtT(a, b), imply(realLtT(c, d), realLtT(realPlusT(a, c), realPlusT(b, d)))))
}

// realAddLeLt: ⊢ (A≤B) ⇒ (C<D) ⇒ (A+C < B+D)   (LessEqLessThanAdd2)
func realAddLeLt(a, b, c, d Term) *prop.PropWrapper {
	return realImplyLeaf(realLessEqLessThanAdd2Thm(), []Term{a, b, c, d},
		imply(realLeT(a, b), imply(realLtT(c, d), realLtT(realPlusT(a, c), realPlusT(b, d)))))
}

// realAddLtLe: ⊢ (A<B) ⇒ (C≤D) ⇒ (A+C < B+D)   (LessThanLessEqAdd2)
func realAddLtLe(a, b, c, d Term) *prop.PropWrapper {
	return realImplyLeaf(realLessThanLessEqAdd2Thm(), []Term{a, b, c, d},
		imply(realLtT(a, b), imply(realLeT(c, d), realLtT(realPlusT(a, c), realPlusT(b, d)))))
}

// ── left cancellation of a common addend ─────────────────────────────────────

// realAddLcancelLe: ⊢ (P + x ≤ P + y) ⇔ (x ≤ y)   (LessEqAddLeft)
func realAddLcancelLe(p, x, y Term) *prop.PropWrapper {
	return realEqLeaf(realLessEqAddLeftThm(), []Term{p, x, y},
		realLeT(realPlusT(p, x), realPlusT(p, y)), realLeT(x, y))
}

// realAddLcancelLt: ⊢ (P + x < P + y) ⇔ (x < y)   (LessThanAddLeft)
func realAddLcancelLt(p, x, y Term) *prop.PropWrapper {
	return realEqLeaf(realLessThanAddLeftThm(), []Term{p, x, y},
		realLtT(realPlusT(p, x), realPlusT(p, y)), realLtT(x, y))
}

// ── `>` / `≥` definitional bridges ───────────────────────────────────────────

// realGtBridge: ⊢ (x > y) = (y < x)   (GtDef)
func realGtBridge(x, y Term) *prop.PropWrapper {
	return realEqLeaf(realGtDefThm(), []Term{x, y}, realGtT(x, y), realLtT(y, x))
}

// realGeBridge: ⊢ (x ≥ y) = (y ≤ x)   (GeDef)
func realGeBridge(x, y Term) *prop.PropWrapper {
	return realEqLeaf(realGeDefThm(), []Term{x, y}, realGeT(x, y), realLeT(y, x))
}

// ── total subtraction / negation leaves (signed normalizer, subneg.go) ───
// Each is one macro instantiation of a RealLemmaBundle subneg field, oriented to
// the direction the signed normalizer consumes (macroEq flips the bound
// statement's orientation as needed). The 4-var rearrangements are DERIVED from these.

// realSubToAddNeg: ⊢ a − b = a + (−b)   (SubDef, sub→add+neg direction)
func realSubToAddNeg(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realSubDefThm(), []Term{a, b}, realSubT(a, b), realPlusT(a, realNegT(b)))
}

// realNegAddL: ⊢ −(a + b) = (−a) + (−b)   (NegAdd)
func realNegAddL(a, b Term) *prop.PropWrapper {
	return realEqLeaf(realNegAddThm(), []Term{a, b},
		realNegT(realPlusT(a, b)), realPlusT(realNegT(a), realNegT(b)))
}

// realNegNegL: ⊢ −(−a) = a   (NegNeg)
func realNegNegL(a Term) *prop.PropWrapper {
	return realEqLeaf(realNegNegThm(), []Term{a}, realNegT(realNegT(a)), a)
}

// realNegZeroL: ⊢ −(&0) = &0   (NegZero)
func realNegZeroL() *prop.PropWrapper {
	return realEqLeaf(realNegZeroThm(), nil, realNegT(realLit(0)), realLit(0))
}

// realMulRightNegL: ⊢ c·(−b) = −(c·b)   (MulRightNeg)
func realMulRightNegL(c, b Term) *prop.PropWrapper {
	return realEqLeaf(realMulRightNegThm(), []Term{c, b}, realStarT(c, realNegT(b)), realNegT(realStarT(c, b)))
}

// ── relation-level move-across leaves (moveAcrossCmp, subneg.go) ─────────

// realLessEqSubAddRight: ⊢ (x − y ≤ z) ⇔ (x ≤ z + y)   (LessEqSubAddRight)
func realLessEqSubAddRight(x, y, z Term) *prop.PropWrapper {
	return realEqLeaf(realLessEqSubAddRightThm(), []Term{x, y, z},
		realLeT(realSubT(x, y), z), realLeT(x, realPlusT(z, y)))
}

// realLessEqSubAddLeft: ⊢ (x ≤ y − z) ⇔ (x + z ≤ y)   (LessEqSubAddLeft)
func realLessEqSubAddLeft(x, y, z Term) *prop.PropWrapper {
	return realEqLeaf(realLessEqSubAddLeftThm(), []Term{x, y, z},
		realLeT(x, realSubT(y, z)), realLeT(realPlusT(x, z), y))
}

// realLessThanSubAddRight: ⊢ (x − y < z) ⇔ (x < z + y)   (LessThanSubAddRight)
func realLessThanSubAddRight(x, y, z Term) *prop.PropWrapper {
	return realEqLeaf(realLessThanSubAddRightThm(), []Term{x, y, z},
		realLtT(realSubT(x, y), z), realLtT(x, realPlusT(z, y)))
}

// realLessThanSubAddLeft: ⊢ (x < y − z) ⇔ (x + z < y)   (LessThanSubAddLeft)
func realLessThanSubAddLeft(x, y, z Term) *prop.PropWrapper {
	return realEqLeaf(realLessThanSubAddLeftThm(), []Term{x, y, z},
		realLtT(x, realSubT(y, z)), realLtT(realPlusT(x, z), y))
}

// realEqSubRightAdd: ⊢ (x − y = z) ⇔ (x = z + y)   (EqSubRightAdd)
func realEqSubRightAdd(x, y, z Term) *prop.PropWrapper {
	return realEqLeaf(realEqSubRightAddThm(), []Term{x, y, z},
		eqT(realSubT(x, y), z), eqT(x, realPlusT(z, y)))
}

// realEqSubLeftAdd: ⊢ (x = y − z) ⇔ (x + z = y)   (EqSubLeftAdd)
func realEqSubLeftAdd(x, y, z Term) *prop.PropWrapper {
	return realEqLeaf(realEqSubLeftAddThm(), []Term{x, y, z},
		eqT(x, realSubT(y, z)), eqT(realPlusT(x, z), y))
}

// Real-domain ring-normalize and numeral-close, the proof-mirror steps the real
// replay needs. Both are REAL kernel compositions over RealLemmaBundle leaves:
//
//   - realNormalizeProof — the proof mirror of realDomain.linOf, the
//     proof-producing linear-form extraction: realRing instantiates the
//     domain-generic ring normalizer (ringVocab, ring.go) at the ℝ vocabulary,
//     with the nine ring AC/identity/distribution leaves (above) and
//     the norm_num bridge evaluators (realNormNat*) as its material.
//
//   - realNormNat* — the real norm_num. There is no real bit
//     recursion: each evaluator lifts the already-real `num` evaluator
//     (NormNatAdd/Mul/Lt/Le/Eq, nat_norm.go) through the bundle's OfNum*
//     homomorphism bridge:
//
//       &m ⋆ &n --OfNumAdd/OfNumMul--> &(m ⋆ n) --num eval + & congruence--> &k
//       &m ⋈ &n --OfNumLessThan/OfNumLessEq/OfNumEq-->  m ⋈ n  --num eval-->               ⊤/⊥
//
//     The bridge step is an eqLeaf over the OfNum* bundle field — a real kernel
//     derivation when the field is bound, the usual TestThm placeholder
//     otherwise — so each evaluator turns sound the moment its
//     OfNum{Add,Mul,LessThan,LessEq,Eq} theorem is installed (the num evaluator
//     underneath is already sound under the nat bundle).

// realRing instantiates the ring-normalizer vocabulary (ringVocab, ring.go) over ℝ:
// realDomain supplies the untrusted term vocabulary (lockstep with the model),
// the ring leaves above supply the theorems, and the norm_num bridge
// supplies coefficient folding. No sucBridge — ℝ has no successor, matching
// realDomain.matchSuc = nil.
var realRing = &ringVocab{
	dom: realDomain, plusOp: realPlus, starOp: realStar,
	commuteADD: realCommuteADD, associateADD: realAssociateADD,
	commuteMUL: realCommuteMUL, associateMUL: realAssociateMUL,
	distributeMUL: realDistributeMUL, rightDistrib: realRightDistrib,
	oneMul: realOneMul, addZeroR: realAddZeroR, zeroMul: realZeroMul,
	normAdd: realNormNatAdd, normMul: realNormNatMul,
	mulSort: realMulSort, decomposeStar: realDecomposeStar, mulZeroR: realMulZeroR,
}

// The ℝ linear extraction reads a product of atoms over the monomial basis
// (Domain.polyMul, domain.go), exactly as num does: `x·y` and `y·x` are one
// unknown, `2·(a·b)·d ≤ 2·(a·b)·(a·b)` is a linear fact over {abd, aabb},
// and a hypothesis carrying a product combines with the goal under Farkas
// instead of being dropped as "nonlinear". Sound with no further supply —
// realBuildAll injects no sign rows, so a monomial atom is just a free
// unknown — and replayed by realRing.normalizeProof's mirrored expansion.
// Wired here rather than in realDomain's literal: realRing names realDomain,
// so the literal naming realRing back would be an initialization cycle.
func init() { realDomain.polyMul = realRing.polyMul }

// realNormalizeProof returns (linForm of t, ⊢ t = buildTerm(linForm), ok) — the
// ℝ ring normalization the replay transports comparisons through.
func realNormalizeProof(t Term) (linForm, *prop.PropWrapper, bool) {
	return realRing.normalizeProof(t)
}

// realOfNumArgs peels `&m ⋆ &n`'s operands to their num arguments. ok=false if a
// side is not real_of_num-applied; literal-ness (bit-tree shape) is gated by the
// num evaluator the callers run BEFORE building any bridge leaf, so a non-literal
// `&x` declines without touching the bundle.
func realOfNumArgs(l, r Term) (m, n Term, ok bool) {
	m, okL := MatchesRealOfNum(l)
	n, okR := MatchesRealOfNum(r)
	return m, n, okL && okR
}

// realNormNatBin: ⊢ &m ⋆ &n = &k for ⋆ ∈ {+, ·} — the OfNum* bridge oriented to
// `&m ⋆ &n = &(m ⋆ n)`, then the num evaluation `⊢ m ⋆ n = k` lifted through
// real_of_num congruence. ok=false unless both sides are `&<bit-tree>` literals.
func realNormNatBin(l, r Term, realOp, numOp func(a, b Term) Term,
	bridgeThm *prop.PropWrapper, eval func(x, y Term) (*prop.PropWrapper, bool)) (*prop.PropWrapper, bool) {
	m, n, ok := realOfNumArgs(l, r)
	if !ok {
		return nil, false
	}
	inner, ok := eval(m, n) // ⊢ m ⋆ n = k
	if !ok {
		return nil, false
	}
	// ⊢ &m ⋆ &n = &(m ⋆ n)   (eqLeaf flips the bound form when it states the reverse)
	bridge := realEqLeaf(bridgeThm, []Term{m, n}, realOp(l, r), realOfNumT(numOp(m, n)))
	return bridge.EqTrans(inner.LeftApply(realOfNum)), true // ⊢ &m ⋆ &n = &k
}

// realNormNatAdd proves ⊢ &m + &n = &k (k = m+n) via OfNumAdd.
func realNormNatAdd(l, r Term) (*prop.PropWrapper, bool) {
	return realNormNatBin(l, r, realPlusT, plus, realOfNumAddThm(), NormNatAdd)
}

// realNormNatMul proves ⊢ &m * &n = &k (k = m·n) via OfNumMul.
func realNormNatMul(l, r Term) (*prop.PropWrapper, bool) {
	return realNormNatBin(l, r, realStarT, star, realOfNumMulThm(), NormNatMul)
}

// realNormNatCmp: ⊢ (&m ⋈ &n) ⇔ ⊤/⊥ — the OfNum* bridge oriented to
// `(&m ⋈ &n) ⇔ (m ⋈ n)`, closed by the num comparison verdict.
func realNormNatCmp(l, r Term, realRel, numRel func(a, b Term) Term,
	bridgeThm *prop.PropWrapper, eval func(x, y Term) (*prop.PropWrapper, bool)) (*prop.PropWrapper, bool) {
	m, n, ok := realOfNumArgs(l, r)
	if !ok {
		return nil, false
	}
	verdict, ok := eval(m, n) // ⊢ (m ⋈ n) ⇔ ⊤/⊥
	if !ok {
		return nil, false
	}
	bridge := realEqLeaf(bridgeThm, []Term{m, n}, realRel(l, r), numRel(m, n))
	return bridge.EqTrans(verdict), true // ⊢ (&m ⋈ &n) ⇔ ⊤/⊥
}

// realNormNatLt proves ⊢ (&m < &n) ⇔ ⊤/⊥ via OfNumLessThan.
func realNormNatLt(l, r Term) (*prop.PropWrapper, bool) {
	return realNormNatCmp(l, r, realLtT, lt, realOfNumLessThanThm(), NormNatLt)
}

// realNormNatLe proves ⊢ (&m ≤ &n) ⇔ ⊤/⊥ via OfNumLessEq.
func realNormNatLe(l, r Term) (*prop.PropWrapper, bool) {
	return realNormNatCmp(l, r, realLeT, le, realOfNumLessEqThm(), NormNatLe)
}

// realNormNatEq proves ⊢ (&m = &n) ⇔ ⊤/⊥ via OfNumEq.
func realNormNatEq(l, r Term) (*prop.PropWrapper, bool) {
	return realNormNatCmp(l, r, eqT, eqT, realOfNumEqThm(), NormNatEq)
}

// RealLemmaBundle is the ℝ analog of NatLemmaBundle (bundle.go): the injection seam
// through which the real proof leaves obtain their named theorems. Same
// graceful-degradation contract — a present field derives a real kernel proof, a
// nil field (the default) falls back to a placeholder stand-in fabricated by the
// test-only hook (bundle.go), so core.TestThm never enters the production
// build and the real replay skeleton stays exercisable in tests; serve.Install-
// RealBundle binds every field to a theorem over ℝ (in a non-test build
// a degrade then panics at the placeholder seam).
//
// The struct lists every theorem the real leaves instantiate. A field
// has an accessor only once a leaf reads it (AddLeftId is the one reserved slot),
// so the bundle never carries a reader without a derivation.
//
// Note the two ℝ-specific shape differences from num: there is no
// ZeroLessEq slot (real variables are free — the refutation injects no 0≤x rows), and
// the scaling lemmas LessEqMulLeft/LessThanMulLeft carry a `0 ≤ c` side-condition
// that the replay discharges on the concrete numeral coefficient.
type RealLemmaBundle struct {
	// ── Ring AC + identity/distribution — READ by the ring leaves ────────────
	// (real_lemmas.go realCommuteADD…realZeroMul, consumed by realRing /
	// realNormalizeProof). AddLeftId is the one RESERVED slot: the
	// canonical form only ever appends `+ &0` on the right (AddRightId).
	AddSym, AddAssoc, MulSym, MulAssoc            *prop.PropWrapper
	AddLeftId, AddRightId, MulLeftId, MulLeftZero *prop.PropWrapper
	LeftDistrib, RightDistrib                     *prop.PropWrapper

	// ── real_of_num homomorphism bridge — READ by the real norm_num ─────────
	// evaluators (realNormNat*: lift `&m ⋆ &n` /
	// `&m ⋈ &n` to the num evaluator).
	OfNumAdd, OfNumMul, OfNumLessThan, OfNumLessEq, OfNumEq *prop.PropWrapper

	// ── Order basics / duality — READ by the leaves now. ──────────────────────
	NotLessThan, NotLessEq, LessEqAntisym, LessEqOfEq, LessEqOfEqSwapped *prop.PropWrapper

	// LessEqTrans: ∀x y z. (x ≤ y) ⇒ (y ≤ z) ⇒ (x ≤ z). READ by the
	// two-sided product bound (realProveProductMul2), which chains its two monotone
	// scalings over the opaque product atoms (linarith cannot, having atomized them).
	LessEqTrans *prop.PropWrapper

	// ── Pairwise inequality addition — READ now (LessEqAdd2 family). ────────
	LessEqAdd2, LessThanAdd2, LessEqLessThanAdd2, LessThanLessEqAdd2 *prop.PropWrapper

	// ── Additive left cancellation — READ now (LessEqAddLeft / LessThanAddLeft). ──
	LessEqAddLeft, LessThanAddLeft *prop.PropWrapper

	// ── Monotone scaling by a positive numeral — READ now (LessEqMulLeft / ─────
	// LessThanMulLeft). Curried shapes, binder order [c, a, b] (the leaf's instAll
	// order; install adapts the corpus CNF clauses via PromiseForGeneral):
	//   LessEqMulLeft: ∀c a b. (&0 ≤ c) ⇒ (a ≤ b) ⇒ (c·a ≤ c·b)
	//   LessThanMulLeft: ∀c a b. (&0 < c) ⇒ (a < b) ⇒ (c·a < c·b)
	// The side condition is discharged on the concrete Farkas multiplier via the
	// norm_num bridge (real_lemmas.go realScale).
	LessEqMulLeft, LessThanMulLeft *prop.PropWrapper

	// ── Cancelling a positive factor OUT of a hypothesis — READ by the hyp-side
	// cancel enrichment (real_cancel.go), the converse of the scaling above.
	// Curried shapes, binder order [c, a, b] with c the cancelled factor:
	//   LessEqCancelMulLeft: ∀c a b. (&0 < c) ⇒ (c·a ≤ c·b) ⇒ (a ≤ b)
	//   LessThanCancelMulLeft: ∀c a b. (&0 < c) ⇒ (c·a < c·b) ⇒ (a < b)
	// The sign premise is STRICT in both — `&0 ≤ c` cancels nothing, since
	// `&0·a ≤ &0·b` holds for every a and b. The RIGHT-factor spellings
	// `a·c ⋈ b·c` need no field: the handler commutes
	// both sides through MulSym and reads them with these two, the derivation
	// realMonoScaleRight makes on the goal side run backwards.
	LessEqCancelMulLeft, LessThanCancelMulLeft *prop.PropWrapper

	// ── Product nonnegativity / positivity — READ by the sign-of-product handler
	// LessEqMul: ∀x y. (&0 ≤ x) ⇒ (&0 ≤ y) ⇒ (&0 ≤ x·y). Closes
	// `&0 ≤ x ∧ &0 ≤ y ⊢ &0 ≤ x·y`; curried, binder [x, y].
	// MulPos: ∀x y. (&0 < x) ⇒ (&0 < y) ⇒ (&0 < x·y)   (the strict
	// twin). With the negation reduction in realProveSignedProduct the two cover
	// all four sign combinations of `x·y ⋈ &0`.
	LessEqMul, MulPos *prop.PropWrapper

	// SquareNonneg: ∀x. &0 ≤ x·x. READ by the no-hyp square handler
	// (real_ops.go realProveSquareNonneg) — the ℝ analogue of `int`'s Image
	// square split, but a SINGLE lemma (ℝ needs no sign split: a square is nonneg
	// outright). Closes `&0 ≤ x·x` with no sign hypothesis (where realProveMonotone,
	// needing factor-sign hyps, declines).
	SquareNonneg *prop.PropWrapper

	// AbsNonneg: ∀x. &0 ≤ real_abs x. READ by the abs-nonneg
	// handler (real_ops.go realProveAbsNonneg) and by realLinProveSigned's
	// abs-aware side-condition discharge (so sign-of-product on `&0 ≤ |x|·|y|`
	// closes directly instead of falling into a 4-way case split).
	AbsNonneg *prop.PropWrapper

	// ── integral domain (no zero divisors) — READ by the MulEqZero hyp-split ─────
	// MulEqZero: ∀x y. (&0 = x·y) ⇔ (x = &0 ∨ y = &0)   (note the bound
	// form orients the equation zero-on-LEFT). A hyp `a·b = &0` becomes the splittable
	// disjunction `a=&0 ∨ b=&0` (real_ops.go realHypSplittable), so `x·x=&0 ⊢ x=&0`
	// and `x·y=&0, x≠&0 ⊢ y=&0` close. ℝ is an integral domain (a field).
	MulEqZero *prop.PropWrapper
	// MulEqCancel: ∀x y z. x·y = x·z ⇔ x = &0 ∨ y = z, as stated. READ by
	// the cancellation of a factor shown not zero from an equation
	// hypothesis (real_cancel.go).
	MulEqCancel *prop.PropWrapper

	// ── neg-order flip — READ by realProveSignedProduct's nonpositive target ──
	// The sign-mixed reduction lands on `&0 ⋈ −(x·y)`; these flip it to the goal
	// `x·y ⋈ &0` at the PROOF level (linarith cannot — it atomizes `−(x·y)` and
	// `x·y` as independent opaque atoms). Iffs, instantiated at the product atom:
	//   NegNonnegativeIffNonpositive: ∀x. (&0 ≤ −x) ⇔ (x ≤ &0)
	//   NegPositiveIffNegative: ∀x. (&0 < −x) ⇔ (x < &0)
	NegNonnegativeIffNonpositive, NegPositiveIffNegative *prop.PropWrapper

	// ── `>` / `≥` definitional bridges — READ now (GtDef / GeDef-style). ──
	GtDef, GeDef *prop.PropWrapper

	// ── Total subtraction / negation — READ by the signed normalizer ──────────
	// (subneg.go signedNorm, which makes total sub/neg first-class linear).
	// The five primitives the `P + −N` recursion stands on; the 4-var
	// rearrangements (add-of-subs, …) are DERIVED from these + the ring AC, not
	// bundled. SubDef / NegAdd / NegNeg / NegZero / MulRightNeg:
	//   SubDef:  a + (−b) = a − b      (the leaf takes the sub→add+neg
	//            orientation, macroEq flipping the bound add=sub direction)
	//   NegAdd:  −(a+b) = (−a) + (−b)
	//   NegNeg:  −(−a) = a
	//   NegZero:    −(&0) = &0
	//   MulRightNeg: a·(−b) = −(a·b)
	SubDef, NegAdd, NegNeg, NegZero, MulRightNeg *prop.PropWrapper

	// ── Relation-level move-across — READ by moveAcrossCmp (subneg.go) ─────
	// the subtraction move-across families that push a top-of-side subtraction across
	// the relation, landing in the positive two-sided form the decider eats:
	//   LessEqSubAddRight: (x − y ≤ z) ⇔ (x ≤ z + y)
	//   LessEqSubAddLeft: (x ≤ y − z) ⇔ (x + z ≤ y)
	// (Lt/Eq analogues likewise). >/≥ need none — they bridge to </≤ upstream.
	LessEqSubAddRight, LessEqSubAddLeft, LessThanSubAddRight, LessThanSubAddLeft, EqSubRightAdd, EqSubLeftAdd *prop.PropWrapper

	// ── Piecewise operator definitions — READ by the real case split (real_ops.go)
	// Each is the operator's own piecewise-by-comparison definition: the case split
	// collapses the COND under each branch's guard.
	//   AbsDef: real_abs x = COND(&0 ≤ x, x, −x)
	//   MaxDef: real_max a b = COND(a ≤ b, b, a)                       (real_max def)
	//   MinDef: real_min a b = COND(a ≤ b, a, b)                       (real_min def)
	//   SgnDef: real_sgn x = COND(&0 < x, &1, COND(x < &0, −&1, &0))   (real_sgn def)
	AbsDef, MaxDef, MinDef, SgnDef *prop.PropWrapper

	// ── abs / sgn algebraic laws — READ by the abs/sgn fold (real_ops.go) ──────
	// The homomorphism / identity rewrites that push real_abs / real_sgn toward the
	// leaves (distinct from the piecewise case split above, which eliminates a leaf
	// `abs x` / `real_sgn x` by its guard). The fold lets `|x·y| = |x|·|y|`,
	// `real_sgn(−x) = −real_sgn x`, … close as reflexivity after normalization,
	// without the cross-sign sign-of-product a brute multi-atom split would need. All
	// unconditional equalities (they hold even at the degenerate points — `inv &0 =
	// &0`).
	//   AbsMul: abs(x·y) = abs x · abs y
	//   AbsEven: abs(−x) = abs x
	//   AbsIdempotent: abs(abs x) = abs x
	//   AbsDiv: abs(x/y) = abs x / abs y
	//   AbsInv: abs(inv x) = inv(abs x)
	//   AbsPow: abs(x pow n) = abs x pow n
	//   AbsOfNum: abs(&n) = &n
	//   SgnMul: real_sgn(x·y) = real_sgn x · real_sgn y
	//   SgnOdd: real_sgn(−x) = −(real_sgn x)
	//   SgnPreservedByInv: real_sgn(inv x) = real_sgn x
	AbsMul, AbsEven, AbsIdempotent, AbsDiv, AbsInv, AbsPow, AbsOfNum *prop.PropWrapper
	SgnMul, SgnOdd, SgnPreservedByInv                                *prop.PropWrapper

	// ── inv algebraic laws — READ by the inv fold (real_ops.go realInvSimp) ──────
	// The homomorphism / identity rewrites that push real_inv toward the leaves —
	// the inv twin of the abs/sgn fold above. Unconditional (the `inv &0 =
	// &0` convention makes the equalities hold at the degenerate points).
	//   InvMul: inv(x·y) = inv x · inv y
	//   InvInv: inv(inv x) = x
	//   InvNeg: inv(−x) = −(inv x)
	//   InvDiv: inv(x/y) = y/x
	//   InvPow: inv(x pow n) = inv x pow n  (the inv twin of AbsPow,
	//           needed for SYMBOLIC n — literal n unfolds via expand_exp + InvMul)
	InvMul, InvInv, InvNeg, InvDiv, InvPow *prop.PropWrapper

	// ── inv sign monotonicity — READ by realInvSignSimp (real_ops.go) as atom ────
	// rewrites. The dual to NegNonnegativeIffNonpositive/NegPositiveIffNegative: sign is PRESERVED through inv (sign(0)=0
	// convention), so the comparison atom `&0 ⋈ inv x` rewrites straight to `&0 ⋈
	// x`, and `inv x = &0` to `x = &0`. Without these, ANY inv goal involving sign/
	// ordering or nonzero is opaque to linarith.
	//   InvPos: (&0 < inv x) ⇔ (&0 < x)
	//   InvNonneg: (&0 ≤ inv x) ⇔ (&0 ≤ x)
	//   InvEqZero:  (inv x = &0) ⇔ (x = &0)
	InvPos, InvNonneg, InvEqZero *prop.PropWrapper

	// ── pow distribution — READ by realPowLawSimp (real_ops.go). Pushes pow into ─
	// the BASE structure (the base-side dual of InvPow / AbsPow, which push the
	// unary op past pow). OnePow is the &1-literal collapse. Unconditional
	// (the pow conventions hold at degenerate points). PowPow's RHS uses NUM multiplication of the exponents.
	//   MulPowDistrib: (x·y) pow n = x pow n · y pow n
	//   DivPow: (x/y) pow n = x pow n / y pow n
	//   PowPow: (x pow m) pow n = x pow (m·n)       (m·n is num multiplication)
	//   OnePow: &1 pow n = &1
	MulPowDistrib, DivPow, PowPow, OnePow *prop.PropWrapper

	// PowAdd: ∀x p q. (x pow p) · (x pow q) = x pow (p + q)   (p+q
	// is num addition). READ by the even-literal-exponent nonneg clause in
	// realPowNonneg (real_ops.go): a goal `&0 ≤ x pow &(2k)` with literal 2k ≥ 4
	// rewrites via PowAdd at (x, k, k) — combined with NormNatAdd to fold
	// `&k + &k = &(2k)` — into `&0 ≤ x^k · x^k`, then SquareNonneg closes.
	PowAdd *prop.PropWrapper

	// OfNumPow: ∀m n. real_pow(&m, n) = &(nat_pow(m, n)). The
	// real_pow sibling of OfNumAdd/Mul — bridges a real_pow with a `&`-coerced
	// base to a num nat_pow image, where the new NormNatExp literal evaluator
	// (nat_norm.go) can then collapse `nat_pow(m, n)` for literal m, n. Wired into
	// realPowSimp's OfNumPow clause; serve.InstallRealBundle binds it to
	// real_pow.OfNumPow. The clause is GATED on this field being non-nil,
	// so a bundle that leaves it unbound keeps the agent-driven path
	// (ExpandRealPowRewrite + ring/of_num folds) in effect.
	OfNumPow *prop.PropWrapper

	// ── sgn extras — extend realSgnLaw + the literal fold in realArithSimpStep. ──
	//   SgnOfZero: real_sgn &0 = &0          (literal fold)
	//   SgnDiv:  sgn(x/y) = sgn x / sgn y
	//   SgnPow:  sgn(x pow n) = sgn x pow n
	SgnOfZero, SgnDiv, SgnPow *prop.PropWrapper

	// ── square ↔ abs interchange — three independent atom ───────────────────────
	// rewrites under realPowLawSimp (SquareOfAbs) and realInvSignSimp (SquarePos /
	// NegEqZero). Goal-side only (the hyp-side dual
	// waits on the same hyp pre-normalization pass as InvPos/InvNonneg/InvEqZero).
	//   SquareOfAbs:  abs(x) pow 2 = x pow 2          (eliminates abs
	//             when squared, only fires for the literal exponent &2)
	//   SquarePos: (&0 < x·x) ⇔ ~(x = &0)          (the iff side
	//             that realProveStrictSquare doesn't carry — derive `x ≠ &0`
	//             from `&0 < x·x`)
	//   NegEqZero:   (−x = &0) ⇔ (x = &0)            (the neg twin
	//             of InvEqZero — zero-detection through neg)
	SquareOfAbs, SquarePos, NegEqZero *prop.PropWrapper

	// ── sub-RCF + abs ordering — READ by realAbsLessEqIffPowTwoLessEqSimp (the simp) ────────
	// and the realProveAbsTriangle / realProvePowBaseMono / realProvePowExpMono
	// decide-leaf branches (real_ops.go).
	//   AbsLessEqIffPowTwoLessEq: (|x| ≤ |y|) ⇔ (x pow 2 ≤ y pow 2)   (goal-side
	//                simp `x² ≤ y² → |x| ≤ |y|` — pushes toward the
	//                canonical abs-LHS form)
	//   AbsTriangle: |x + y| ≤ |x| + |y|                  (the
	//                binary base, iterated by realProveAbsTriangle for n-ary
	//                `|Σxᵢ| ≤ Σ|xᵢ|`)
	//   PowMonoBase:      &0 ≤ x ⇒ x ≤ y ⇒ x pow n ≤ y pow n  (base
	//                monotone for SYMBOLIC n — sign-known sub-RCF)
	//   PowMonoBaseStrict:      ~(n = 0) ⇒ &0 ≤ x ⇒ x < y ⇒ x pow n < y pow n
	//                                                    (PowMonoBaseStrict; strict
	//                                                    base monotone, the
	//                                                    extra `n ≠ 0` discharges
	//                                                    via num linarith)
	//   PowMonoExp:     &1 ≤ x ⇒ m ≤ n ⇒ x pow m ≤ x pow n  (exponent
	//                monotone — discharges sign on real x, order on num m,n)
	AbsLessEqIffPowTwoLessEq, AbsTriangle, PowMonoBase, PowMonoBaseStrict, PowMonoExp *prop.PropWrapper

	// ── real trichotomy — READ by the `≠`-hyp split (real_ops.go) and the ────
	// strict-square handler (realProveStrictSquare).
	// LessThanTrichotomy: ((a<b) ∨ (b<a)) ∨ (a=b).
	LessThanTrichotomy *prop.PropWrapper

	// ── real_pow recursion — READ by the literal-exponent unfold (realPowUnfold) ─
	//   PowZero: real_pow x 0 = &1                    (real_pow's base clause)
	//   PowSuc:  real_pow x (suc n) = x · real_pow x n (its step clause)
	// serve.InstallRealBundle projects both from the real_pow definition (a
	// conjunction of both clauses).
	PowZero, PowSuc *prop.PropWrapper

	// ── real_pow sign/monotone — READ by the pow-sign handler (real_ops.go) ──
	// The sign-known power facts (NOT full RCF — the input is a base-sign fact, the
	// output a lemma instantiation), the real_pow twin of the sign-of-product layer:
	//   PowTwoNonneg: ∀x. &0 ≤ x pow 2                      (no sign hyp)
	//   PowNonneg:  ∀x n. (&0 ≤ x) ⇒ (&0 ≤ x pow n)       (symbolic n)
	//   PowPos:  ∀x n. (&0 < x) ⇒ (&0 < x pow n)
	PowTwoNonneg, PowNonneg, PowPos *prop.PropWrapper

	// ── Field layer (real_div / real_inv) — READ by the field handlers (real_ops.go) ─
	// The DivDef bridge `x/y = x·inv y` has no leaf and is not bundled: the
	// clearing uses the *DivMulLeft / *DivMulRight lemmas directly.
	//   InvOne:    inv &1 = &1
	//   DivOne:    x / &1 = x
	//   MulRightInverse: x ≠ &0 ⇒ x · inv x = &1                 (cancellation)
	//   MulLeftInverse: x ≠ &0 ⇒ inv x · x = &1
	//   DivRefl: x ≠ &0 ⇒ x / x = &1
	InvOne, DivOne, MulRightInverse, MulLeftInverse, DivRefl *prop.PropWrapper

	// DivDef: x / y = x · inv y (real_div's definition) — the quotient basis's
	// unfold (quotient_basis.go).
	DivDef *prop.PropWrapper

	// Denominator-clearing iffs. POSITIVE divisor `&0 < z ⇒ (… ⇔ …)`
	// ({Eq,LessEq,LessThan}DivMul{Left,Right}); Left = division on the comparison's RIGHT
	// (x ⋈ y/z), Right = on the LEFT (x/z ⋈ y):
	//   EqDivMulLeft: &0<z ⇒ (x = y/z ⇔ y = x·z)        LessEqDivMulLeft: &0<z ⇒ (x ≤ y/z ⇔ x·z ≤ y)
	//   LessThanDivMulLeft: &0<z ⇒ (x < y/z ⇔ x·z < y)        EqDivMulRight: &0<z ⇒ (x/z = y ⇔ x = y·z)
	//   LessEqDivMulRight: &0<z ⇒ (x/z ≤ y ⇔ x ≤ y·z)        LessThanDivMulRight: &0<z ⇒ (x/z < y ⇔ x < y·z)
	EqDivMulLeft, LessEqDivMulLeft, LessThanDivMulLeft, EqDivMulRight, LessEqDivMulRight, LessThanDivMulRight *prop.PropWrapper

	// NEGATIVE divisor `z < &0 ⇒ (… ⇔ …)` — the </≤ directions FLIP (= does not);
	// no entry states them, so serve.InstallRealBundle derives each from its
	// positive-divisor sibling:
	//   EqDivMulLeftNeg: z<&0 ⇒ (x = y/z ⇔ y = x·z)       LessEqDivMulLeftNeg: z<&0 ⇒ (x ≤ y/z ⇔ y ≤ x·z)
	//   LessThanDivMulLeftNeg: z<&0 ⇒ (x < y/z ⇔ y < x·z)       EqDivMulRightNeg: z<&0 ⇒ (x/z = y ⇔ x = y·z)
	//   LessEqDivMulRightNeg: z<&0 ⇒ (x/z ≤ y ⇔ y·z ≤ x)       LessThanDivMulRightNeg: z<&0 ⇒ (x/z < y ⇔ y·z < x)
	EqDivMulLeftNeg, LessEqDivMulLeftNeg, LessThanDivMulLeftNeg, EqDivMulRightNeg, LessEqDivMulRightNeg, LessThanDivMulRightNeg *prop.PropWrapper
}

// realLemmaBundle is the installed real bundle, or nil (placeholder mode).
var realLemmaBundle *RealLemmaBundle

// SetRealLemmaBundle installs the bundle the real leaves derive from. Pass nil to
// revert to placeholder mode. Set once at engine startup, independently of the
// num SetNatLemmaBundle. Drops the constraint extraction memos, whose entries
// carry proofs derived from the bundle in force (resetConstraintMemos).
func SetRealLemmaBundle(b *RealLemmaBundle) {
	realLemmaBundle = b
	resetConstraintMemos()
}

// realBundleField reads a field through the installed real bundle, or nil if none.
func realBundleField(f func(*RealLemmaBundle) *prop.PropWrapper) *prop.PropWrapper {
	if realLemmaBundle == nil {
		return nil
	}
	return f(realLemmaBundle)
}

// realEqLeaf / realImplyLeaf: the real-bundle analogues of eqLeaf/implyLeaf
// (bundle.go) — identical macro instantiation/orientation. A nil field falls
// back through the shared placeholder seam (bundle.go: panics in production,
// test stand-in otherwise), exactly like the nat leaves.
func realEqLeaf(thm *prop.PropWrapper, args []Term, wantL, wantR Term) *prop.PropWrapper {
	if w, ok := macroEq(thm, args, wantL, wantR); ok {
		return w
	}
	return placeholderEq(thm, wantL, wantR)
}

func realImplyLeaf(thm *prop.PropWrapper, args []Term, want Term) *prop.PropWrapper {
	if w, ok := macroThm(thm, args, want); ok {
		return w
	}
	return placeholderConcl(thm, want)
}

// Nil-safe accessors for the read-now slots. (AddLeftId stays reserved — see the
// struct doc.)
func realAddSymThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AddSym })
}
func realAddAssocThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AddAssoc })
}
func realMulSymThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulSym })
}
func realMulAssocThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulAssoc })
}
func realAddRightIdThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AddRightId })
}
func realMulLeftIdThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulLeftId })
}
func realMulLeftZeroThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulLeftZero })
}
func realLeftDistribThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LeftDistrib })
}
func realRightDistribThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.RightDistrib })
}
func realOfNumAddThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.OfNumAdd })
}
func realOfNumMulThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.OfNumMul })
}
func realOfNumLessThanThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.OfNumLessThan })
}
func realOfNumLessEqThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.OfNumLessEq })
}
func realOfNumEqThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.OfNumEq })
}
func realNotLessThanThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.NotLessThan })
}
func realNotLessEqThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.NotLessEq })
}
func realLessEqAntisymThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqAntisym })
}
func realLessEqOfEqThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqOfEq })
}
func realLessEqOfEqSwappedThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqOfEqSwapped })
}
func realLessEqAdd2Thm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqAdd2 })
}
func realLessThanAdd2Thm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanAdd2 })
}
func realLessEqLessThanAdd2Thm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqLessThanAdd2 })
}
func realLessThanLessEqAdd2Thm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanLessEqAdd2 })
}
func realLessEqAddLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqAddLeft })
}
func realLessThanAddLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanAddLeft })
}
func realLessEqMulLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqMulLeft })
}
func realLessThanMulLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanMulLeft })
}
func realGtDefThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.GtDef })
}
func realGeDefThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.GeDef })
}
func realSubDefThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SubDef })
}
func realNegAddThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.NegAdd })
}
func realNegNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.NegNeg })
}
func realNegZeroThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.NegZero })
}
func realMulRightNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulRightNeg })
}
func realLessEqSubAddRightThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqSubAddRight })
}
func realLessEqSubAddLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqSubAddLeft })
}
func realLessThanSubAddRightThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanSubAddRight })
}
func realLessThanSubAddLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanSubAddLeft })
}
func realEqSubRightAddThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.EqSubRightAdd })
}
func realEqSubLeftAddThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.EqSubLeftAdd })
}
func realLessEqTransThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqTrans })
}
func realLessEqMulThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqMul })
}
func realMulPosThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulPos })
}
func realNegNonnegativeIffNonpositiveThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.NegNonnegativeIffNonpositive })
}
func realNegPositiveIffNegativeThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.NegPositiveIffNegative })
}
func realMulEqZeroThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulEqZero })
}
func realMulEqCancelThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulEqCancel })
}
func realLessThanTrichotomyThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanTrichotomy })
}
func realPowZeroThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowZero })
}
func realPowSucThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowSuc })
}
func realSquareNonnegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SquareNonneg })
}
func realAbsNonnegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsNonneg })
}
func realPowAddThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowAdd })
}
func realOfNumPowThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.OfNumPow })
}
func realPowTwoNonnegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowTwoNonneg })
}
func realPowNonnegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowNonneg })
}
func realPowPosThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowPos })
}
func realInvOneThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvOne })
}
func realDivOneThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.DivOne })
}
func realMulRightInverseThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulRightInverse })
}
func realMulLeftInverseThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulLeftInverse })
}
func realDivDefThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.DivDef })
}
func realDivReflThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.DivRefl })
}
func realEqDivMulLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.EqDivMulLeft })
}
func realLessEqDivMulLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqDivMulLeft })
}
func realLessThanDivMulLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanDivMulLeft })
}
func realEqDivMulRightThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.EqDivMulRight })
}
func realLessEqDivMulRightThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqDivMulRight })
}
func realLessThanDivMulRightThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanDivMulRight })
}
func realEqDivMulLeftNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.EqDivMulLeftNeg })
}
func realLessEqDivMulLeftNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqDivMulLeftNeg })
}
func realLessThanDivMulLeftNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanDivMulLeftNeg })
}
func realEqDivMulRightNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.EqDivMulRightNeg })
}
func realLessEqDivMulRightNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqDivMulRightNeg })
}
func realLessThanDivMulRightNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanDivMulRightNeg })
}
func realAbsDefThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsDef })
}
func realMaxDefThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MaxDef })
}
func realMinDefThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MinDef })
}
func realSgnDefThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SgnDef })
}
func realAbsMulThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsMul })
}
func realAbsEvenThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsEven })
}
func realAbsIdempotentThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsIdempotent })
}
func realAbsDivThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsDiv })
}
func realAbsInvThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsInv })
}
func realAbsPowThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsPow })
}
func realAbsOfNumThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsOfNum })
}
func realSgnMulThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SgnMul })
}
func realSgnOddThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SgnOdd })
}
func realSgnPreservedByInvThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SgnPreservedByInv })
}
func realInvMulThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvMul })
}
func realInvInvThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvInv })
}
func realInvNegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvNeg })
}
func realInvDivThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvDiv })
}
func realInvPowThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvPow })
}
func realInvPosThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvPos })
}
func realInvNonnegThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvNonneg })
}
func realInvEqZeroThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.InvEqZero })
}
func realMulPowDistribThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.MulPowDistrib })
}
func realDivPowThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.DivPow })
}
func realPowPowThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowPow })
}
func realOnePowThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.OnePow })
}
func realSgnOfZeroThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SgnOfZero })
}
func realSgnDivThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SgnDiv })
}
func realSgnPowThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SgnPow })
}
func realSquareOfAbsThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SquareOfAbs })
}
func realSquarePosThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.SquarePos })
}
func realNegEqZeroThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.NegEqZero })
}
func realAbsLessEqIffPowTwoLessEqThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsLessEqIffPowTwoLessEq })
}
func realAbsTriangleThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.AbsTriangle })
}
func realPowMonoBaseThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowMonoBase })
}
func realPowMonoBaseStrictThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowMonoBaseStrict })
}
func realPowMonoExpThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.PowMonoExp })
}
func realLessEqCancelMulLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessEqCancelMulLeft })
}
func realLessThanCancelMulLeftThm() *prop.PropWrapper {
	return realBundleField(func(b *RealLemmaBundle) *prop.PropWrapper { return b.LessThanCancelMulLeft })
}
