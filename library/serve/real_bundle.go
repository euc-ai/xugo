package serve

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// InstallRealBundle populates omega's RealLemmaBundle (the ℝ twin of
// InstallNatBundle). No silent degrade: in a non-test build a real leaf whose
// field is nil or shape-mismatches panics at the call site rather than
// fabricating a stand-in (omega/bundle.go).
//
// ── SUPPLY: every field binds a REAL theorem — no fabricated TestThm
// anywhere; each is sourced from a corpus entry (directly or through a
// kernel-sound derivation).
//
// The const vocabulary is shared (dsl's Real*Meta are the constants
// real_add/real_lt/… the real chapters state with, ext/dsl/arith.go), so an
// entry's statement over ℝ alpha-matches an omega leaf shape directly. The
// wiring styles mirror InstallNatBundle:
// - direct fromEntry: the ring AC / identity / distribution
// leaves, the real_of_num bridge, plus every leaf whose normal form
// alpha-matches the leaf shape modulo eq/iff side-swap (realEqLeaf
// auto-orients);
// - defNorm (normalized const def): NotLessEq (real_lt's
// definition, so it carries no proof) and the `>`/`≥` bridges;
// AbsDef / MaxDef / MinDef / SgnDef are the operator definitions;
// - CurryIffConj: LessEqAntisym (iff-with-conjunction → curried implication);
// - fromGeneral (PromiseForGeneral): every leaf whose entry normalizes to a CNF
// clause / has a different binder positional order / has its OR-clause
// literals in a different binary association — the *Add2 / *AddLeft / *MulLeft
// families, LessThanTrichotomy, NegNonnegativeIffNonpositive/NegPositiveIffNegative, the
// six {LessEq,LessThan}SubAdd{Left,Right} and EqSub{Left,Right}Add move-across iffs, the curried
// pow-sign / pow-monotonicity / pos-divisor field-clearing trios;
// - HypAND0/1 + DeriveTrans: real_pow's definition is a top-level conjunction
// (∀x. pow x 0 = &1) ∧ (∀x n. pow x (suc n) = x · pow x n); the two
// conjuncts feed PowZero / PowSuc directly;
// - negDivDeriver (real_bundle_neg_div.go): the six negative-divisor field-
// clearing iffs (EqDivMulLeftNeg / LessEqDivMulLeftNeg / LessThanDivMulLeftNeg / EqDivMulRightNeg / LessEqDivMulRightNeg
// / LessThanDivMulRightNeg) have no entry of their own; each is kernel-derived from the
// matching positive-divisor sibling by instantiating at (z := -z, y := -y),
// pushing every negation outward through InvNeg / real_ring.MulLeftNeg and
// MulRightNeg / NegNeg / NegPositiveIffNegative, flipping `-A ⋈ -B → B ⋈ A` via
// real_order_ring.LessEqNeg2 (and its locally-derived `<` and `=` twins), and
// re-folding real_div.
//
// Whether this is installed in production is a separate `initEngine` decision —
// installing it makes a degraded real leaf panic (no fabricator in production),
// so it is installed only when the real arith move is meant to be live.
func InstallRealBundle() {
	InstallRecordNormal()
	// defNorm pulls a const's NORMALIZED defining theorem from the corpus env —
	// definitions carry no proof (see InstallNatBundle).
	defNorm := func(name string) *prop.PropWrapper {
		return prop.WrapProp(proof.NewScript(env()).ConstDefNormalized(name))
	}
	// fromGeneral wraps PromiseForGeneral: declare the leaf's preferred (general)
	// shape; Normalize finds the entry's key and reconstruct adapts back at force
	// time. Used for the clause-form lemmas (*Add2 / *AddLeft / *MulLeft) whose CNF normal
	// form is logically the curried implication / iff the leaf wants — same seam as the
	// nat *Add2 / SubAddCancel family.
	fromGeneral := func(general core.Term) *prop.PropWrapper {
		return prop.WrapProp(PromiseForGeneral(prop.MakeProp(general)))
	}

	// ── Term vocabulary (for the fromGeneral shapes) ─────────────────────────
	real := dsl.RealType
	realPlus := dsl.RealPlusMeta.Term()
	realStar := dsl.RealStarMeta.Term()
	realLt := dsl.RealLtMeta.Term()
	realLe := dsl.RealLeMeta.Term()
	realOfNum := dsl.RealOfNumMeta.Term()
	rplus := func(a, b core.Term) core.Term { return ext.Apply(realPlus, a, b) }
	rstar := func(a, b core.Term) core.Term { return ext.Apply(realStar, a, b) }
	rlt := func(a, b core.Term) core.Term { return ext.Apply(realLt, a, b) }
	rle := func(a, b core.Term) core.Term { return ext.Apply(realLe, a, b) }
	rlit := func(n uint64) core.Term { return ext.Apply(realOfNum, omega.Numeral(n)) }
	eqT := func(a, b core.Term) core.Term { return core.Eq(a, b) } // ⇔ is `=` at bool
	implyT := func(a, b core.Term) core.Term { return ext.Apply(prop.IMPLY, a, b) }
	rv := func(name string) *ext.TermWrapper { return ext.Var(ext.TermName(name), real) }
	ForAll := ext.ForAll

	a, b, c, d, p, x, y := rv("a"), rv("b"), rv("c"), rv("d"), rv("p"), rv("x"), rv("y")

	// add2General: ∀a b c d. (a ⋈₁ b) ⇒ (c ⋈₂ d) ⇒ (a+c ⋈₃ b+d) — the leaf's
	// curried shape (instAll order [a,b,c,d]). The entries normalize to the CNF
	// clause (whatever binder order they state); Normalize sorts clause literals,
	// so the key matches regardless of premise/binder order — the nat *Add2 seam.
	add2General := func(p1, p2, p3 func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(a, b, c, d)(
			implyT(p1(a, b), implyT(p2(c, d), p3(rplus(a, c), rplus(b, d)))))
	}
	// addLcancelGeneral: ∀p x y. ((p+x) ⋈ (p+y)) ⇔ (x ⋈ y) — addend p first (the
	// leaf's instAll order; the entry's own binder order and iff orientation are
	// canonicalized by Normalize).
	addLcancelGeneral := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(p, x, y)(eqT(rel(rplus(p, x), rplus(p, y)), rel(x, y)))
	}
	// scaleGeneral: ∀c a b. (&0 ⋈ c) ⇒ (a ⋈ b) ⇒ (c·a ⋈ c·b) — the curried
	// LessEqMulLeft/LessThanMulLeft with the side premise realScale discharges on
	// the concrete coefficient. Normalize canonicalizes the entry's binder order.
	scaleGeneral := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(c, a, b)(
			implyT(rel(rlit(0), c), implyT(rel(a, b), rel(rstar(c, a), rstar(c, b)))))
	}
	// cancelGeneral: ∀c a b. (&0 < c) ⇒ (c·a ⋈ c·b) ⇒ (a ⋈ b) — the curried
	// LessEqCancelMulLeft / LessThanCancelMulLeft, scaleGeneral read backwards. The
	// sign premise is STRICT in BOTH variants (a nonnegative factor cancels
	// nothing: `&0·a ≤ &0·b` holds for every a, b). The premises conjoined —
	// `&0 < x ∧ x·y ⋈ x·z ⇒ y ⋈ z` — normalize to the
	// same clause as the curried form, so fromGeneral resolves it by key.
	cancelGeneral := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(c, a, b)(
			implyT(rlt(rlit(0), c), implyT(rel(rstar(c, a), rstar(c, b)), rel(a, b))))
	}
	// lessEqOfEqGeneral: ∀a b. (a=b) ⇒ (a≤b) — the implication the leaf wants;
	// its normal form is the clause `(a≠b) ∨ (a≤b)`, resolved by key (and the
	// reconstruct hands back the implication DeriveRealLessEqOfEqSwapped then consumes).
	lessEqOfEqGeneral := ForAll(a, b)(implyT(eqT(a, b), rle(a, b)))
	lessEqOfEq := fromGeneral(lessEqOfEqGeneral)

	// ── For the structural handlers: case splits + sign-known nonlinear (omega/real_ops.go) ──
	realNeg := dsl.RealNegMeta.Term()
	rneg := func(a core.Term) core.Term { return ext.Apply(realNeg, a) }
	orT := func(a, b core.Term) core.Term { return ext.Apply(prop.OR, a, b) }
	z := rv("z")

	// Sign-known nonlinear + integral-domain + trichotomy general shapes (the
	// leaf's instAll binder order in brackets):
	// mulPosGeneral: ∀x y. (&0 ⋈ x) ⇒ (&0 ⋈ y) ⇒ (&0 ⋈ x·y) [x, y]
	mulPosGeneral := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(x, y)(implyT(rel(rlit(0), x), implyT(rel(rlit(0), y), rel(rlit(0), rstar(x, y)))))
	}
	// lessEqTransGeneral: ∀x y z. (x≤y) ⇒ (y≤z) ⇒ (x≤z) [x, y, z]
	lessEqTransGeneral := ForAll(x, y, z)(implyT(rle(x, y), implyT(rle(y, z), rle(x, z))))
	// mulEqZeroGeneral: ∀x y. (&0 = x·y) ⇔ (x=&0 ∨ y=&0) [x, y] (MulEqZero shape)
	mulEqZeroGeneral := ForAll(x, y)(eqT(eqT(rlit(0), rstar(x, y)), orT(eqT(x, rlit(0)), eqT(y, rlit(0)))))
	// negFlipShape: ∀x. (&0 ⋈ −x) ⇔ (x ⋈ &0) [x] (NegNonnegativeIffNonpositive/NegPositiveIffNegative, leaf-wanted)
	negFlipShape := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(x)(eqT(rel(rlit(0), rneg(x)), rel(x, rlit(0))))
	}
	// lessThanTrichotomyShape: ∀a b. ((a<b) ∨ (b<a)) ∨ (a=b) [a, b] (LessThanTrichotomy)
	lessThanTrichotomyShape := ForAll(a, b)(orT(orT(rlt(a, b), rlt(b, a)), eqT(a, b)))

	// ── Signed-normalizer (sub/neg) leaves — a PREREQUISITE the structural
	// handlers' `−x` branches (abs/sgn else-arm, sign-mixed products) flow through
	// (omega/subneg.go moveAcrossCmp → signedNorm), bound here so the real signed normalizer is
	// sound: the 5 primitives (defNorm/fromGeneral) and the 6 relation
	// move-across iffs (fromGeneral).
	realSub := dsl.RealSubMeta.Term()
	rsub := func(a, b core.Term) core.Term { return ext.Apply(realSub, a, b) }
	// negAdd: ∀a b. −(a+b) = (−a)+(−b) negNeg: ∀a. −(−a) = a
	negAddGeneral := ForAll(a, b)(eqT(rneg(rplus(a, b)), rplus(rneg(a), rneg(b))))
	negNegGeneral := ForAll(a)(eqT(rneg(rneg(a)), a))
	negZeroGeneral := eqT(rneg(rlit(0)), rlit(0))                                 // −&0 = &0
	mulRightNegGeneral := ForAll(c, b)(eqT(rstar(c, rneg(b)), rneg(rstar(c, b)))) // c·(−b) = −(c·b)
	// move-across (leaf-wanted iff shapes, [x, y, z]):
	lessEqSubAddRightShape := ForAll(x, y, z)(eqT(rle(rsub(x, y), z), rle(x, rplus(z, y))))
	lessEqSubAddLeftShape := ForAll(x, y, z)(eqT(rle(x, rsub(y, z)), rle(rplus(x, z), y)))
	lessThanSubAddRightShape := ForAll(x, y, z)(eqT(rlt(rsub(x, y), z), rlt(x, rplus(z, y))))
	lessThanSubAddLeftShape := ForAll(x, y, z)(eqT(rlt(x, rsub(y, z)), rlt(rplus(x, z), y)))
	eqSubRightAddShape := ForAll(x, y, z)(eqT(eqT(rsub(x, y), z), eqT(x, rplus(z, y))))
	eqSubLeftAddShape := ForAll(x, y, z)(eqT(eqT(x, rsub(y, z)), eqT(rplus(x, z), y)))

	// real_pow vocabulary. real_pow's definition (a top-level conjunction
	// of both recursion clauses) is bound by projecting the conjuncts — see the
	// `realPowConj` block below the shapes.
	realPow := dsl.RealPowMeta.Term()
	rpow := func(m, n core.Term) core.Term { return ext.Apply(realPow, m, n) }
	nNum := ext.Var(ext.TermName("n"), dsl.NumType)

	// real_pow sign (omega's realProvePowSign): the two curried-implication
	// shapes the leaf consumes; the entries normalize to the CNF clause form,
	// fromGeneral canonicalizes through Normalize.
	powNonnegShape := ForAll(x, nNum)(implyT(rle(rlit(0), x), rle(rlit(0), rpow(x, nNum)))) // ∀x n. (0≤x)⇒(0≤x^n)   PowNonneg
	powPosShape := ForAll(x, nNum)(implyT(rlt(rlit(0), x), rlt(rlit(0), rpow(x, nNum))))    // ∀x n. (0<x)⇒(0<x^n)   PowPos

	// Field layer (algebra/field/field, read at real_field.Field). Positive-divisor clearing wraps the iff in a
	// `(0<z) ⇒` premise that normalizes to a CNF clause — fromGeneral on
	// clearShape canonicalizes by Normalize key; the negative-divisor variants
	// are kernel-derived from the positives (see negDivDeriver below).
	rdiv := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealDivMeta.Term(), a, b) }
	posZ := rlt(rlit(0), z)
	clearShape := func(sign, goalAtom, cleared core.Term) core.Term {
		// ∀z x y. sign ⇒ (goalAtom ⇔ cleared) — the leaf's instAll order [z,x,y].
		return ForAll(z, x, y)(implyT(sign, eqT(goalAtom, cleared)))
	}

	// Sub-RCF pow monotonicity (omega/real_ops.go). Curried implication shapes
	// mirror realImplyLeaf's instAll order; the entries normalize to CNF clauses
	// with a different binder positional order — fromGeneral canonicalizes.
	notT := func(p core.Term) core.Term { return ext.Apply(prop.NOT, p) }
	natLeT := func(a, b core.Term) core.Term { return ext.Apply(dsl.NatLeMeta.Term(), a, b) }
	natZero := dsl.ZeroMeta.Term()
	mNum := ext.Var(ext.TermName("m"), dsl.NumType)
	powMonoBaseShape := ForAll(nNum, x, y)(implyT(rle(rlit(0), x), implyT(rle(x, y), rle(rpow(x, nNum), rpow(y, nNum))))) // ∀n x y. 0≤x ⇒ x≤y ⇒ xⁿ≤yⁿ
	powMonoBaseStrictShape := ForAll(nNum, x, y)(
		implyT(notT(eqT(nNum, natZero)),
			implyT(rle(rlit(0), x),
				implyT(rlt(x, y), rlt(rpow(x, nNum), rpow(y, nNum)))))) // ∀n x y. n≠0 ⇒ 0≤x ⇒ x<y ⇒ xⁿ<yⁿ
	powMonoExpShape := ForAll(mNum, nNum, x)(implyT(rle(rlit(1), x), implyT(natLeT(mNum, nNum), rle(rpow(x, mNum), rpow(x, nNum))))) // ∀m n x. 1≤x ⇒ m≤n ⇒ xᵐ≤xⁿ

	// real_pow's definition is the top-level conjunction
	// (∀x. real_pow(x, 0) = &1) ∧ (∀x n. real_pow(x, suc n) = x · real_pow(x, n))
	// Project each conjunct via HypAND0/HypAND1 + DeriveTrans to extract the
	// curried per-clause leaves PowZero/PowSuc consume. The kernel composition is
	// real (the underlying real_pow.Pow thm is real); no fabricated cert.
	realPowConj := fromEntryAsStated(real_pow.Pow)
	powZeroPart, powSucPart, okPow := prop.MatchesAND(realPowConj.Conclusion())
	if !okPow {
		panic("InstallRealBundle: real_pow.Pow is not a top-level conjunction")
	}
	realPowZero := realPowConj.DeriveTrans(prop.HypAND0(powZeroPart, powSucPart)) // ⊢ ∀x. real_pow(x, 0) = &1
	realPowSuc := realPowConj.DeriveTrans(prop.HypAND1(powZeroPart, powSucPart))  // ⊢ ∀x n. real_pow(x, suc n) = x · real_pow(x, n)

	// ── Six neg-divisor clearing lemmas ({Eq,LessEq,LessThan}DivMul{Left,Right}Neg) ──
	// No entry states a `z<&0 ⇒ ...` form: each is derivable by
	// instantiating the corresponding `&0<z ⇒ ...` positive at (z := -z, y := -y)
	// and pushing every negation outward through the neg-algebra
	// (InvNeg / MulLeftNeg / MulRightNeg / NegNeg / NegPositiveIffNegative /
	// LessEqNeg2 + its derived `<` and `=` twins). The derivation lives in
	// real_bundle_neg_div.go — kernel composition over corpus entries, so
	// the outputs are SOUND PropWrappers (no fabricated cert).
	posEqRdiv := fromGeneral(clearShape(posZ, eqT(x, rdiv(y, z)), eqT(y, rstar(x, z))))
	posLeRdiv := fromGeneral(clearShape(posZ, rle(x, rdiv(y, z)), rle(rstar(x, z), y)))
	posLtRdiv := fromGeneral(clearShape(posZ, rlt(x, rdiv(y, z)), rlt(rstar(x, z), y)))
	posEqLdiv := fromGeneral(clearShape(posZ, eqT(rdiv(y, z), x), eqT(y, rstar(x, z))))
	posLeLdiv := fromGeneral(clearShape(posZ, rle(rdiv(y, z), x), rle(y, rstar(x, z))))
	posLtLdiv := fromGeneral(clearShape(posZ, rlt(rdiv(y, z), x), rlt(y, rstar(x, z))))
	negDiv := newNegDivDeriver(
		fromEntry(real_order_ring.NegPositiveIffNegative), // (x<&0) ⇔ (&0<-x)
		fromReading(field.InvNeg, real_field.Field),       // inv(-x) = -inv(x)
		fromEntry(real_ring.MulLeftNeg),                   // -(x·y) = (-x)·y
		fromEntry(real_ring.MulRightNeg),                  // -(x·y) = x·(-y)
		fromEntry(real_ring.NegNeg),                       // x = --x
		fromEntry(real_order_ring.LessEqNeg2),             // (x≤y) ⇔ (-y ≤ -x)
		defNorm("real_lt"),                                // (x<y) ⇔ ¬(y≤x)
		defNorm("real_div"),                               // a/b = a · inv(b)
	)

	realBundle := &omega.RealLemmaBundle{
		// ── Ring AC + identity/distribution — direct binds (realEqLeaf auto-
		// orients; most of these normalize reversed). RightDistrib's
		// normal-form binders are (a, m, b) with m the shared factor — realRightDistrib
		// compensates with its [a, c, b] instAll order.
		AddSym:       fromEntry(real_construction.AddSym),
		AddAssoc:     fromEntry(real_construction.AddAssoc),
		MulSym:       fromEntry(real_construction.MulSym),
		MulAssoc:     fromEntry(real_construction.MulAssoc),
		AddLeftId:    fromEntry(real_construction.AddLeftId),
		AddRightId:   fromEntry(real_ring.AddRightId),
		MulLeftId:    fromEntry(real_construction.MulLeftId),
		MulLeftZero:  fromEntry(real_ring.MulLeftZero),
		LeftDistrib:  fromEntry(real_construction.LeftDistrib),
		RightDistrib: fromEntry(real_ring.RightDistrib),

		// ── real_of_num homomorphism bridge — direct binds (normal forms reversed). ──
		OfNumAdd:      fromEntry(real_construction.OfNumAdd),
		OfNumMul:      fromEntry(real_construction.OfNumMul),
		OfNumPow:      fromEntry(real_pow.OfNumPow),
		OfNumLessThan: fromEntry(real_order_ring.OfNumLessThan),
		OfNumLessEq:   fromEntry(real_construction.OfNumLessEq),
		OfNumEq:       fromEntry(real_construction.OfNumEq),

		// ── Order basics / duality. ───────────────────────────────────────────
		// NotLessThan binds its entry; NotLessEq is real_lt's NORMALIZED definition (a
		// definition carries no proof — pulled via the const-def
		// mechanism, like the `>`/`≥` bridges). GtDef/
		// GeDef are the real_gt/real_ge defs.
		NotLessThan: fromEntry(real_order_ring.NotLessThan),
		NotLessEq:   defNorm("real_lt"),
		GtDef:       defNorm("real_gt"),
		GeDef:       defNorm("real_ge"),
		// LessEqAntisym: the entry states the iff-with-conjunction `(a=b) ⇔ (a≤b ∧ b≤a)`;
		// CurryIffConj (generic) weakens it to the curried `(a≤b)⇒(b≤a)⇒(a=b)`.
		LessEqAntisym: omega.CurryIffConj(fromEntry(real_construction.LessEqAntisym)),
		// LessEqOfEq via the clause→implication seam; LessEqOfEqSwapped derived from it
		// (the real twin of DeriveLessEqOfEqSwapped — instantiate at the swapped pair +
		// eq-symmetry bridge), as only LessEqOfEq is stated.
		LessEqOfEq:        lessEqOfEq,
		LessEqOfEqSwapped: omega.DeriveRealLessEqOfEqSwapped(lessEqOfEq),

		// ── Pairwise inequality addition — fromGeneral (CNF-clause normal forms). ──
		LessEqAdd2:         fromGeneral(add2General(rle, rle, rle)), // (≤,≤,≤)
		LessThanAdd2:       fromGeneral(add2General(rlt, rlt, rlt)), // (<,<,<)
		LessEqLessThanAdd2: fromGeneral(add2General(rle, rlt, rlt)), // (≤,<,<) — realAddLeLt
		LessThanLessEqAdd2: fromGeneral(add2General(rlt, rle, rlt)), // (<,≤,<) — realAddLtLe

		// ── Additive left cancellation — fromGeneral (iffs, flipped). ──
		LessEqAddLeft:   fromGeneral(addLcancelGeneral(rle)),
		LessThanAddLeft: fromGeneral(addLcancelGeneral(rlt)),

		// ── Monotone scaling — fromGeneral (CNF-clause normal forms, `&0` side). ──
		LessEqMulLeft:   fromGeneral(scaleGeneral(rle)),
		LessThanMulLeft: fromGeneral(scaleGeneral(rlt)),

		// ── Cancelling a positive factor out of a hypothesis (real_cancel.go) —
		// the scaling read backwards, both with a STRICT sign premise. Conjoined or
		// curried, the two premises normalize to one clause; fromGeneral matches the
		// curried leaf shape by Normalize key. ──
		LessEqCancelMulLeft:   fromGeneral(cancelGeneral(rle)), // &0<c ⇒ c·a≤c·b ⇒ a≤b
		LessThanCancelMulLeft: fromGeneral(cancelGeneral(rlt)), // &0<c ⇒ c·a<c·b ⇒ a<b

		// ── Sign-known nonlinear fragment (omega/real_ops.go). ──
		// LessEqMul / MulPos / LessEqTrans all sourced through fromGeneral off their
		// CNF-clause normal forms.
		LessEqMul:   fromGeneral(mulPosGeneral(rle)), // ∀x y. (0≤x)⇒(0≤y)⇒(0≤x·y)
		MulPos:      fromGeneral(mulPosGeneral(rlt)), // ∀x y. (0<x)⇒(0<y)⇒(0<x·y)
		LessEqTrans: fromGeneral(lessEqTransGeneral), // ∀x y z. (x≤y)⇒(y≤z)⇒(x≤z)

		// ── Integral domain (MulEqZero) — proved, fromGeneral. ──
		MulEqZero: fromGeneral(mulEqZeroGeneral), // ∀x y. (0=x·y) ⇔ (x=0 ∨ y=0)
		// The cancellation of a factor that is not zero from an equation.
		MulEqCancel: fromEntryAsStated(real_ring.MulLeftCancel), // ∀x y z. x·y = x·z ⇔ x = 0 ∨ y = z

		// ── neg-order flip (omega/real_ops.go realFlipNeg) — NegNonnegativeIffNonpositive/NegPositiveIffNegative
		// normalize with the iff sides flipped relative to the
		// leaf shape (`(x ⋈ &0) ⇔ (&0 ⋈ −x)`), so go through fromGeneral so Normalize
		// canonicalizes the iff and matches by key.
		NegNonnegativeIffNonpositive: fromGeneral(negFlipShape(rle)), // ∀x. (&0≤−x) ⇔ (x≤&0)
		NegPositiveIffNegative:       fromGeneral(negFlipShape(rlt)), // ∀x. (&0<−x) ⇔ (x<&0)

		// ── Piecewise operator defs (omega/real_ops.go) — definitions, via defNorm. ──
		AbsDef: defNorm("real_abs"),
		MaxDef: defNorm("real_max"),
		MinDef: defNorm("real_min"),
		SgnDef: defNorm("real_sgn"),

		// ── real trichotomy (omega/real_ops.go ≠-split / strict-square) — LessThanTrichotomy
		// is proved with its three literals in OR-order (a=b, a<b, b<a); the leaf
		// wants the same disjunction in a different binary association ((a<b)∨(b<a))∨(a=b).
		// Normalize flattens the 3-literal disjunction and sorts, so the key matches.
		LessThanTrichotomy: fromGeneral(lessThanTrichotomyShape), // ∀a b. ((a<b)∨(b<a))∨(a=b)

		// ── Signed normalizer primitives — SubDef is a const def; the rest
		// resolve by Normalize key (fromGeneral). ──
		SubDef:      defNorm("real_sub"),             // a − b = a + (−b)
		NegAdd:      fromGeneral(negAddGeneral),      // −(a+b) = (−a)+(−b)
		NegNeg:      fromGeneral(negNegGeneral),      // −(−a) = a
		NegZero:     fromGeneral(negZeroGeneral),     // −&0 = &0
		MulRightNeg: fromGeneral(mulRightNegGeneral), // c·(−b) = −(c·b)

		// ── Relation move-across: {LessEq,LessThan}SubAdd{Left,Right} and EqSub{Left,Right}Add (the LessThanSubAddLeft
		// slot is the add/sub exchange law — same iff up to alpha-renaming).
		// The entries' binder order / iff orientation differ from the leaf shape;
		// fromGeneral canonicalizes by Normalize key. ──
		LessEqSubAddRight:   fromGeneral(lessEqSubAddRightShape),   // (x−y ≤ z) ⇔ (x ≤ z+y)
		LessEqSubAddLeft:    fromGeneral(lessEqSubAddLeftShape),    // (x ≤ y−z) ⇔ (x+z ≤ y)
		LessThanSubAddRight: fromGeneral(lessThanSubAddRightShape), //
		LessThanSubAddLeft:  fromGeneral(lessThanSubAddLeftShape),  //                         (the add/sub exchange law)
		EqSubRightAdd:       fromGeneral(eqSubRightAddShape),       //
		EqSubLeftAdd:        fromGeneral(eqSubLeftAddShape),        //

		// ── real_pow recursion — the definition is the top-level conjunction
		// `(∀x. pow x 0 = &1) ∧ (∀x n. pow x (suc n) = x · pow x n)`; project each
		// conjunct via HypAND0/1 + DeriveTrans to get the curried leaf shapes the
		// PowZero/PowSuc fields want. ──
		PowZero: realPowZero, // real_pow x 0 = &1
		PowSuc:  realPowSuc,  // real_pow x (suc n) = x · real_pow x n

		// ── No-hyp square / real_pow sign (omega/real_ops.go). ──
		// SquareNonneg/PowTwoNonneg are proved with the leaf-shape body and bind directly;
		// PowNonneg/PowPos are proved as CNF clauses (`¬(0⋈x) ∨ (0⋈x^n)`) — fromGeneral
		// canonicalizes against the leaf's curried implication.
		SquareNonneg: fromEntry(real_order_ring.SquareNonneg), // ∀x. &0 ≤ x·x
		AbsNonneg:    fromEntry(real_sgn_abs.AbsNonneg),       // ∀x. &0 ≤ |x| (abs-nonneg handler / sign-of-product side-cond discharge)
		PowTwoNonneg: fromEntry(real_pow.PowTwoNonneg),        // ∀x. &0 ≤ x pow 2
		PowNonneg:    fromGeneral(powNonnegShape),             // ∀x n. (&0≤x) ⇒ (&0≤x pow n)
		PowPos:       fromGeneral(powPosShape),                // ∀x n. (&0<x) ⇒ (&0<x pow n)

		// ── abs / sgn algebraic laws (omega/real_ops.go). ──
		// Eq orientations differ for the unary-`abs`/`sgn` laws (the normal form
		// reads `... = abs/sgn(...)`, the leaf wants the reverse), but realEqLeaf
		// auto-orients — fromEntry binds them directly. AbsMul/AbsDiv/AbsPow/AbsOfNum/SgnMul
		// normalize leaf-direction already.
		AbsMul:            fromEntry(real_sgn_abs.AbsMul),            // |x·y| = |x|·|y|
		AbsEven:           fromEntry(real_sgn_abs.AbsEven),           // |−x| = |x|              (normal form reversed)
		AbsIdempotent:     fromEntry(real_sgn_abs.AbsIdempotent),     // |abs x| = abs x          (normal form reversed)
		AbsDiv:            fromEntry(real_sgn_abs.AbsDiv),            // |x/y| = |x|/|y|
		AbsInv:            fromEntry(real_sgn_abs.AbsInv),            // |inv x| = inv|x|
		AbsPow:            fromEntry(real_pow.AbsPow),                // |x pow n| = |x| pow n
		AbsOfNum:          fromEntry(real_sgn_abs.AbsOfNum),          // |&n| = &n
		SgnMul:            fromEntry(real_sgn_abs.SgnMul),            // sgn(x·y) = sgn x · sgn y
		SgnOdd:            fromEntry(real_sgn_abs.SgnOdd),            // sgn(−x) = −(sgn x)        (normal form reversed)
		SgnPreservedByInv: fromEntry(real_sgn_abs.SgnPreservedByInv), // sgn(inv x) = sgn x        (normal form reversed)

		// ── inv algebraic laws (real_ops.go realInvSimp). InvPow and
		// InvPow are the same statement up to alpha; all eqs bind directly. ──
		InvMul: fromReading(field.InvMul, real_field.Field), // inv(x·y) = inv x · inv y
		InvInv: fromReading(field.InvInv, real_field.Field), // inv(inv x) = x                 (normal form reversed)
		InvNeg: fromReading(field.InvNeg, real_field.Field), // inv(−x) = −(inv x)
		InvDiv: fromReading(field.InvDiv, real_field.Field), // inv(x/y) = y/x
		InvPow: fromEntry(real_pow.InvPow),                  // inv(x pow n) = inv x pow n

		// ── inv sign monotonicity. Iff sides reversed vs leaf shape but
		// `⇔` = `=` at bool, so eqLeaf auto-orients — wrap. ──
		InvPos:    fromEntry(real_order_field.InvPos),             // (&0 < inv x) ⇔ (&0 < x)
		InvNonneg: fromEntry(real_order_field.InvNonneg),          // (&0 ≤ inv x) ⇔ (&0 ≤ x)
		InvEqZero: fromReading(field.InvEqZero, real_field.Field), // (inv x = &0) ⇔ (x = &0)

		// ── pow distribution. MulPowDistrib/DivPow/PowPow/OnePow normalize with
		// the eq reversed — eqLeaf auto-orients. ──
		MulPowDistrib: fromEntry(real_pow.MulPowDistrib), // (x·y) pow n = x^n · y^n
		DivPow:        fromEntry(real_pow.DivPow),        // (x/y) pow n = x^n / y^n
		PowPow:        fromEntry(real_pow.PowPow),        // (x pow m) pow n = x pow (m·n)
		OnePow:        fromEntry(real_pow.OnePow),        // &1 pow n = &1
		PowAdd:        fromEntry(real_pow.PowAdd),        // (x^p)·(x^q) = x^(p+q)          (even-pow nonneg handler)

		// ── sgn at zero, quotients and powers. SgnOfZero normalizes reversed (`&0 = sgn &0`). ──
		SgnOfZero: fromEntry(real_sgn_abs.SgnOfZero), // sgn &0 = &0
		SgnDiv:    fromEntry(real_sgn_abs.SgnDiv),    // sgn(x/y) = sgn x / sgn y
		SgnPow:    fromEntry(real_pow.SgnPow),        // sgn(x pow n) = sgn x pow n

		// ── square ↔ abs interchange. All iff/eq orientations resolved by
		// eqLeaf auto-orient (`x ≠ &0` ≡ `¬(x=&0)`). ──
		SquareOfAbs: fromEntry(real_pow.SquareOfAbs),      // abs(x) pow 2 = x pow 2         (eq reversed)
		SquarePos:   fromEntry(real_order_ring.SquarePos), // (&0 < x·x) ⇔ ~(x = &0)        (iff reversed)
		NegEqZero:   fromEntry(real_ring.NegEqZero),       // (−x = &0) ⇔ (x = &0)          (iff reversed)

		// ── sub-RCF pow monotonicity + abs ordering + abs triangle. The
		// pow-monotonicity trio normalizes to CNF clauses with a different binder positional
		// order than the leaf wants (curried implication ∀n x y / ∀m n x); fromGeneral
		// canonicalizes by Normalize key. ──
		AbsLessEqIffPowTwoLessEq: fromEntry(real_pow.AbsLessEqIffPowTwoLessEq), // (|x| ≤ |y|) ⇔ (x² ≤ y²)
		AbsTriangle:              fromEntry(real_sgn_abs.AbsTriangle),          // |x+y| ≤ |x|+|y|
		PowMonoBase:              fromGeneral(powMonoBaseShape),                // 0≤x ⇒ x≤y ⇒ xⁿ≤yⁿ
		PowMonoBaseStrict:        fromGeneral(powMonoBaseStrictShape),          // n≠0 ⇒ 0≤x ⇒ x<y ⇒ xⁿ<yⁿ
		PowMonoExp:               fromGeneral(powMonoExpShape),                 // 1≤x ⇒ m≤n ⇒ xᵐ≤xⁿ

		// ── Field layer (algebra/field/field read at real_field.Field). Positive-divisor clearing lemmas
		// normalize to CNF clauses (the `(0<z)⇒...` curried shape lives in the leaf);
		// the negative-divisor variants are derived from them (below). ──
		InvOne:          fromReading(field.InvOne, real_field.Field),          // inv(&1) = &1
		DivOne:          fromReading(field.DivOne, real_field.Field),          // ∀x. x/&1 = x               (normal form reversed)
		MulRightInverse: fromReading(field.MulRightInverse, real_field.Field), // ∀x. (x=&0) ∨ (&1 = x·inv x)
		MulLeftInverse:  fromEntry(real_construction.MulLeftInverse),          // ∀x. (x=&0) ∨ (&1 = inv x · x)
		DivRefl:         fromReading(field.DivRefl, real_field.Field),         // ∀x. (x=&0) ∨ (&1 = x/x)
		DivDef:          fromEntry(real_field.RealDivDef),                     // ∀x y. x/y = x·inv y
		// Positive-divisor clearing `&0<z ⇒ (… ⇔ …)`: R = div on the comparison's
		// RIGHT (x ⋈ y/z), L = on the LEFT (y/z ⋈ x). cleared = x·z form. Each maps
		// to {Eq,LessEq,LessThan}DivMul{Left,Right} — fromGeneral canonicalizes the CNF clause /
		// binder reorder.
		EqDivMulLeft:        posEqRdiv,
		LessEqDivMulLeft:    posLeRdiv,
		LessThanDivMulLeft:  posLtRdiv,
		EqDivMulRight:       posEqLdiv,
		LessEqDivMulRight:   posLeLdiv,
		LessThanDivMulRight: posLtLdiv,
		// Negative-divisor clearing `z<&0 ⇒ (… ⇔ …)`: </≤ FLIP, = does not.
		// No entry states them; each is derived by instantiating the
		// matching positive at (z := -z, y := -y) + neg-algebra rewrites (see
		// negDivDeriver above + real_bundle_neg_div.go).
		EqDivMulLeftNeg:        negDiv.derive(posEqRdiv, negDivEq),
		LessEqDivMulLeftNeg:    negDiv.derive(posLeRdiv, negDivLe),
		LessThanDivMulLeftNeg:  negDiv.derive(posLtRdiv, negDivLt),
		EqDivMulRightNeg:       negDiv.derive(posEqLdiv, negDivEq),
		LessEqDivMulRightNeg:   negDiv.derive(posLeLdiv, negDivLe),
		LessThanDivMulRightNeg: negDiv.derive(posLtLdiv, negDivLt),
	}
	omega.SetRealLemmaBundle(realBundle)
	// Explicit roots include derived negative-divisor fields, whose adapted
	// statements do not themselves identify all source theorems.
	negDivRoots := func(positive registry.EntryLike) []core.PropKey {
		return entryKeys(positive,
			real_order_ring.NegPositiveIffNegative, field.InvNeg, real_field.Field, real_ring.MulLeftNeg,
			real_ring.MulRightNeg, real_ring.NegNeg, real_order_ring.LessEqNeg2)
	}
	roots, foundation := computeBundleCapability(realBundle, map[string][]core.PropKey{
		"NotLessEq": {},
		"GtDef":     {},
		"GeDef":     {},
		"SubDef":    {},
		"AbsDef":    {},
		"MaxDef":    {},
		"MinDef":    {},
		"SgnDef":    {},
		// Fields read off the abstract field's laws at ℝ's instance: their
		// statements are no entry's, so their sources are named.
		"InvMul":                 entryKeys(field.InvMul, real_field.Field),
		"InvInv":                 entryKeys(field.InvInv, real_field.Field),
		"InvNeg":                 entryKeys(field.InvNeg, real_field.Field),
		"InvDiv":                 entryKeys(field.InvDiv, real_field.Field),
		"InvEqZero":              entryKeys(field.InvEqZero, real_field.Field),
		"InvOne":                 entryKeys(field.InvOne, real_field.Field),
		"DivOne":                 entryKeys(field.DivOne, real_field.Field),
		"MulRightInverse":        entryKeys(field.MulRightInverse, real_field.Field),
		"DivRefl":                entryKeys(field.DivRefl, real_field.Field),
		"LessEqAntisym":          entryKeys(real_construction.LessEqAntisym),
		"LessEqOfEqSwapped":      entryKeys(real_order_ring.LessEqOfEq),
		"PowZero":                entryKeys(real_pow.Pow),
		"PowSuc":                 entryKeys(real_pow.Pow),
		"EqDivMulLeftNeg":        negDivRoots(real_order_field.EqDivMulLeft),
		"LessEqDivMulLeftNeg":    negDivRoots(real_order_field.LessEqDivMulLeft),
		"LessThanDivMulLeftNeg":  negDivRoots(real_order_field.LessThanDivMulLeft),
		"EqDivMulRightNeg":       negDivRoots(real_order_field.EqDivMulLeft), // EqDivMulRight is EqDivMulLeft under a renaming; one member serves both
		"LessEqDivMulRightNeg":   negDivRoots(real_order_field.LessEqDivMulRight),
		"LessThanDivMulRightNeg": negDivRoots(real_order_field.LessThanDivMulRight),
	})
	omega.SetRealBundleFoundation(foundation)
	installCapability(proof.CapabilityArithReal, roots, foundation)
}
