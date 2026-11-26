package serve

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/integrity/dag"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	registry "github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// InstallIntBundle wires omega's IntBridges — the homomorphism theorems
// the lifting rule (omega.IntOfRealThm)
// consumes to lift a theorem over ℝ to its ℤ analogue:
//
// - int_eq / int_le / int_lt / int_ge / int_gt: comparison/equality
// definitions of the int relations in terms of real ones over
// real_of_int(...) (the embedding ℤ → ℝ);
// - OfNum: the literal bridge `real_of_int (int_of_num n) =
// real_of_num n`;
// - Add / Mul / Neg / Sub: the operator
// homomorphisms `real_of_int (a ⋆ b) = real_of_int a ⋆ real_of_int b`
// (and the unary `neg` version).
//
// Each is bound through the entry that proves it: EntryThm's promise
// declares the chapter's statement and the proof behind it runs the
// first time IntOfRealThm rewrites against the bridge. Idempotent +
// re-entrant in the same way InstallRealBundle is — nothing is forced
// at install time, so there is no eager-build re-entrancy hazard.
//
// Pairs with Script.IntOfRealDerive, which every `family.Lifted` member
// runs: it reads `omega.CurrentIntBridges()`, and this installer is what
// makes that lookup non-nil. Without it, replay of any lift panics with
// a "no IntBridges installed" message pointing the caller back here.
//
// Does NOT install RealLemmaBundle on its own — the bridge proofs
// themselves use real arith (`int_construction.AddBridge`'s proof relies
// on the ℝ embedding and AC laws). Call serve.InstallRealBundle() first
// if a bridge will be forced. TestReplayAll already does both in order.
func InstallIntBundle() {
	// defNorm pulls a const's NORMALIZED defining theorem from the corpus
	// env. Used for the four order-relation bridges, which are
	// definitions rather than theorems: a definition
	// carries no proof, so there is no theorem to bind and no chapter
	// member to bind it from. The defining equation itself IS the bridge
	// IntOfRealThm consumes
	// (e.g. `∀x y. (x <= y) ⇔ real_of_int x <= real_of_int y` for int_le).
	defNorm := func(name string) *prop.PropWrapper {
		return prop.WrapProp(proof.NewScript(env()).ConstDefNormalized(name))
	}
	// flipBridge reorients a `∀vars. A = B` bridge to `∀vars. B = A`.
	//
	// Why: omega.IntOfRealThm's deep rewrite calls gsymPatternRewrite on
	// every IntBridges field, which uniformly applies symmetry (Eq-symmetry
	// after stripping the ∀). The other homomorphism bridges (Add,
	// Max, OfNum, …) are stated in the "embedded-int-op =
	// real-op-of-embeddeds" orientation, so symmetry puts the real side on
	// the left → the rewrite collapses real → int (correct).
	//
	// Abs and Neg break the pattern: they are stated
	// "real-op-of-embedded = embedded-of-int-op" (LHS is `real_abs
	// (real_of_int x)` resp. `-real_of_int(x)`, RHS is `real_of_int
	// (int_abs x)` / `real_of_int (-x)`). After symmetry they'd rewrite
	// embedded-int-op → real-op-of-embedded, the wrong direction. Flip
	// them once at install time so the downstream symmetry lands the right
	// way round.
	flipBridge := func(b *prop.PropWrapper) *prop.PropWrapper {
		body, vars := b.StripConclForAll()
		body = body.EqSym()
		for i := len(vars) - 1; i >= 0; i-- {
			body = body.Abs(vars[i])
		}
		return body
	}
	// The bridges bind through fromEntry(): the entry's Normalize form,
	// normalize-first — the principle Script.IntOfRealDerive's source
	// canonicalization follows (a proof's stated orientation and
	// quantification are accidents that change under re-proof; the normal
	// form does not). Safe HERE because gsymPatternRewrite consumes
	// bridges as pattern rewrites (binder-order-insensitive); the
	// positional-instAll IntLemmaBundle fields below bind the normal form
	// (fromEntry) or the stated form (fromEntryAsStated), whichever the
	// leaf's instAll order reads. flipBridge calibration is against
	// NORMALIZED forms.
	intBridges := &omega.IntBridges{
		// Comparison/equality bridges: int_eq is `prove`d (theorem,
		// bridge-bound); int_le / int_lt / int_ge / int_gt are
		// plain definitions (defNorm-bound, already canonical).
		Eq: fromEntry(int_construction.RepresentativeInjective),
		Le: defNorm("int_le"),
		Lt: defNorm("int_lt"),
		Ge: defNorm("int_ge"),
		Gt: defNorm("int_gt"),
		// Literal embedding and operator homomorphisms (all `prove`d).
		OfNum: fromEntry(int_construction.OfNumBridge),
		Add:   fromEntry(int_construction.AddBridge),
		Mul:   fromEntry(int_construction.MulBridge),
		Sub:   fromEntry(int_construction.SubBridge),
		// Neg / Abs use the reversed `real-op-of-embedded
		// = embedded-int-op` orientation (also under Normalize — the
		// canonical form keeps it) — flip so the uniform symmetry path
		// inside IntOfRealThm collapses real → int the right way.
		Neg: flipBridge(fromEntry(int_construction.NegBridge)),
		Abs: flipBridge(fromEntry(int_construction.AbsBridge)),
		// max / min / sgn keep the standard orientation.
		Max: fromEntry(int_construction.MaxBridge),
		Min: fromEntry(int_construction.MinBridge),
		Sgn: fromEntry(int_construction.SgnBridge),
		// Pow: `real_of_int(int_pow x n) = real_pow(real_of_int x, n)`.
		// Needed so sources that mention real_pow (PowZero / PowSuc, OfNumPow) lift
		// without leaving a `real_pow(real_of_int(...), n)` residue.
		Pow: fromEntry(int_pow.PowBridge),
	}
	omega.SetIntBridges(intBridges)
	// The bridges are entries of their own, resolved by identity; the four
	// comparison definitions are primitive leaves. Noted for WarmBundles —
	// every lifted field forces a bridge.
	noteInstalledBundle(intBridges, map[string][]core.PropKey{"Le": {}, "Lt": {}, "Ge": {}, "Gt": {}})
	installIntOfRealCapabilities()
	// Populate omega's IntLemmaBundle now that the IntBridges (and the real
	// bundle, the lifted ℝ sources read through) are wired. The bundle is
	// what makes the int `arith` / `auto` path SOUND — every leaf derives a
	// real kernel proof instead of a placeholder.
	InstallIntLemmaBundle()
}

// installIntOfRealCapabilities installs one dependency manifest per REAL
// source rather than an all-bridges ambient dependency. IntOfRealThm
// builds every rewrite closure, but a bridge theorem is forced only when
// its real operator occurs in the source statement; declaring all bridges
// creates false graph cycles.
//
// A token names its source by the source's own identity — the entry's
// key, which registry.Lifted reads off the entry it lifts from — so
// walking every entry's declared list reaches every token, and each
// source is installed once however many members lift from it.
func installIntOfRealCapabilities() {
	bridgeByConst := map[core.TermName]registry.EntryLike{
		"real_of_num": int_construction.OfNumBridge,
		"real_add":    int_construction.AddBridge,
		"real_mul":    int_construction.MulBridge,
		"real_sub":    int_construction.SubBridge,
		"real_neg":    int_construction.NegBridge,
		"real_abs":    int_construction.AbsBridge,
		"real_max":    int_construction.MaxBridge,
		"real_min":    int_construction.MinBridge,
		"real_sgn":    int_construction.SgnBridge,
		"real_pow":    int_pow.PowBridge,
	}
	sourceStatement := func(sourceKey core.PropKey) core.Prop {
		if ce, ok := registry.ByKey(string(sourceKey)); ok {
			return ce.Statement().Prop
		}
		panic(fmt.Sprintf("InstallIntBundle: IntOfReal source %s is not an entry's own key", sourceKey))
	}
	// A single proof may call IntOfRealDerive multiple times with different
	// REAL sources — each becomes its own int_of_real:<sourceKey> capability.
	// Dedupe by sourceKey across the whole corpus so every declared capability
	// gets installed exactly once, regardless of how the proofs are grouped.
	installedSource := map[core.PropKey]bool{}
	install := func(capability string) {
		if !strings.HasPrefix(capability, proof.CapabilityIntOfReal) {
			return
		}
		sourceKey := core.PropKey(strings.TrimPrefix(capability, proof.CapabilityIntOfReal))
		if installedSource[sourceKey] {
			return
		}
		installedSource[sourceKey] = true
		// Equality is a kernel builtin, so its bridge is always a root.
		rootSet := map[core.PropKey]bool{core.PropKey(int_construction.RepresentativeInjective.Entry().Key): true}
		consts := map[core.TermKey]core.ConstTerm{}
		stmt := sourceStatement(sourceKey)
		ext.CollectConstTerms(stmt.Conclusion(), consts)
		for h := range stmt.HypIter() {
			ext.CollectConstTerms(h, consts)
		}
		for _, c := range consts {
			if bridge := bridgeByConst[c.Name()]; bridge != nil {
				rootSet[core.PropKey(bridge.Entry().Key)] = true
			}
		}
		var roots []core.PropKey
		for k := range rootSet {
			roots = append(roots, k)
		}
		installCapability(capability, roots, dag.Closure(roots))
	}
	for _, ce := range registry.All() {
		for _, capability := range ce.Build.Capabilities {
			install(capability)
		}
	}
}

// InstallIntLemmaBundle populates omega's IntLemmaBundle — the injection seam
// the integer (`int` type) decision layer reads its named theorems through.
// Sibling of InstallNatBundle / InstallRealBundle; once installed, the int
// `arith` path is sound (every leaf derives a real kernel proof; a non-test
// build panics at the placeholder seam if a field is nil).
//
// Bound material comes from four sources:
//
// - direct fromEntry() — the ℤ laws the int chapters prove, whose normal form
// matches the leaf shape (up to the auto-orient in macroEq);
// - defNorm() — the operators introduced by a plain definition (int_sub /
// int_max / int_min / int_sgn / int_divides / int_gt / int_ge) carry no
// proof; the defining equation IS the bundle leaf;
// - fromGeneral() — leaves whose entry normalizes to a CNF clause / curried-iff
// with a different binder order than the leaf wants; PromiseForGeneral's
// Normalize-key adapter canonicalizes;
// - omega.IntOfRealThm() (liftReal / liftEntry) — the install-time lift from
// a proven ℝ theorem, for
// the ℤ ones no entry states. The ring laws, NotLessEq / SquareOfAbs / AbsLessEqIffPowTwoLessEq /
// PowNonneg / PowPos / PowTwoNonneg lift this way. PowZero / PowSuc project from
// real_pow's conjunction first, then lift each conjunct.
//
// Depends on InstallRealBundle (for the lifted ℝ sources, and the four
// lift-via-real-source projections) and on the IntBridges set being installed
// (typically by InstallIntBundle running first). A nil bridge set panics with
// a pointed message in the caller (omega.IntOfRealThm).
//
// In a non-test build a degraded leaf panics at the placeholder seam (no
// fabricator). The corpus binding test (TestInstallIntLemmaBundleBindingBuilds,
// fabricator-free) is the soundness ground truth — it exercises every field
// and is the only place orientation/shape drift surfaces.
func InstallIntLemmaBundle() {
	defNorm := func(name string) *prop.PropWrapper {
		return prop.WrapProp(proof.NewScript(env()).ConstDefNormalized(name))
	}
	fromGeneral := func(general core.Term) *prop.PropWrapper {
		return prop.WrapProp(PromiseForGeneral(prop.MakeProp(general)))
	}
	// dividesDefOrdered: defNorm("int_divides") re-∀-closed in the DividesDef
	// field's contractual binder order — [divisor, dividend], i.e.
	// `∀d e. (∃z. e = d·z) ⇔ int_divides(d, e)` (see the field doc in
	// prover/solver/omega/int_lemmas.go), the order intDividesDefIff's instAll passes.
	// The raw normalized def does NOT bind in that order: Normalize's ∀-closure
	// follows first occurrence in the body, and the dividend occurs first in
	// `∃x. e = d·x`, so ConstDefNormalized yields ∀e d — instantiating it at
	// [d, e] would arg-swap the leaf's iff and every int_divides goal/hyp would
	// panic at the placeholder seam (regression-pinned in int_bundle_test.go
	// TestInstallIntLemmaBundleBindingLeafSeams). The correct order is located
	// from the int_divides application itself (not a hard-coded permutation),
	// so this is insensitive to Normalize's binder-order convention; the ⇔ is
	// oriented ∃-form-left to the same contract (EqSym if the def ever flips).
	// Pure re-generalization/orientation — kernel derivation, no new proof
	// obligations, no recorded-certificate impact.
	dividesDefOrdered := func() *prop.PropWrapper {
		body, vars := defNorm("int_divides").StripConclForAll()
		l, r, ok := prop.MatchesIFF(body.Conclusion())
		if !ok {
			panic("InstallIntLemmaBundle: normalized int_divides def is not an iff")
		}
		dArg, eArg, ok := omega.MatchesIntDivides(r)
		if !ok {
			// Convention drift: the const application ended up on the left.
			// Re-orient to the contract (∃-form ⇔ int_divides) with EqSym.
			if dArg, eArg, ok = omega.MatchesIntDivides(l); !ok {
				panic("InstallIntLemmaBundle: normalized int_divides def has no " +
					"top-level int_divides application on either side of the iff")
			}
			body = body.EqSym()
		}
		ordered := make([]core.VarTerm, 0, 2)
		for _, want := range []core.Term{dArg, eArg} {
			for _, v := range vars {
				if want.AlphaEquals(v) {
					ordered = append(ordered, v)
				}
			}
		}
		if len(ordered) != 2 {
			panic("InstallIntLemmaBundle: normalized int_divides def binders do " +
				"not match the int_divides application's two args")
		}
		return body.ConclForAllList(ordered...)
	}
	// liftReal: omega.IntOfRealThm of a proven ℝ theorem under the installed
	// IntBridges (set by InstallIntBundle). Panics if the bridges aren't
	// installed — soundness-critical, surfaces install-order misconfiguration.
	liftReal := func(realThm *prop.PropWrapper) *prop.PropWrapper {
		br := omega.CurrentIntBridges()
		if br == nil {
			panic("InstallIntLemmaBundle: no IntBridges installed; call " +
				"InstallIntBundle() before InstallIntLemmaBundle().")
		}
		return omega.IntOfRealThm(realThm, br)
	}
	// liftEntry: liftReal of a REAL source entry in its normal form
	// (fromEntry).
	liftEntry := func(source registry.EntryLike) *prop.PropWrapper { return liftReal(fromEntry(source)) }

	// ── Term vocabulary for fromGeneral shapes ───────────────────────────────
	intT := dsl.IntType
	intPlus := dsl.IntPlusMeta.Term()
	intStar := dsl.IntStarMeta.Term()
	intLt := dsl.IntLtMeta.Term()
	intLe := dsl.IntLeMeta.Term()
	intOfNum := dsl.IntOfNumMeta.Term()
	intNeg := dsl.IntNegMeta.Term()
	intSub := dsl.IntSubMeta.Term()
	intAbs := dsl.IntAbsMeta.Term()
	intDvd := dsl.IntDividesMeta.Term()
	intDiv := dsl.IntDivMeta.Term()
	intRem := dsl.IntRemMeta.Term()

	iplus := func(a, b core.Term) core.Term { return ext.Apply(intPlus, a, b) }
	istar := func(a, b core.Term) core.Term { return ext.Apply(intStar, a, b) }
	ilt := func(a, b core.Term) core.Term { return ext.Apply(intLt, a, b) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(intLe, a, b) }
	ineg := func(a core.Term) core.Term { return ext.Apply(intNeg, a) }
	isub := func(a, b core.Term) core.Term { return ext.Apply(intSub, a, b) }
	iabs := func(a core.Term) core.Term { return ext.Apply(intAbs, a) }
	idvd := func(a, b core.Term) core.Term { return ext.Apply(intDvd, a, b) }
	idiv := func(a, b core.Term) core.Term { return ext.Apply(intDiv, a, b) }
	irem := func(a, b core.Term) core.Term { return ext.Apply(intRem, a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(intOfNum, omega.Numeral(n)) }

	eqT := func(a, b core.Term) core.Term { return core.Eq(a, b) }
	implyT := func(a, b core.Term) core.Term { return ext.Apply(prop.IMPLY, a, b) }
	orT := func(a, b core.Term) core.Term { return ext.Apply(prop.OR, a, b) }
	notT := func(p core.Term) core.Term { return ext.Apply(prop.NOT, p) }
	iv := func(name string) *ext.TermWrapper { return ext.Var(ext.TermName(name), intT) }
	ForAll := ext.ForAll

	a, b, c, d, p, x, y, z := iv("a"), iv("b"), iv("c"), iv("d"), iv("p"), iv("x"), iv("y"), iv("z")
	m, n, q := iv("m"), iv("n"), iv("q")

	// Real-side vocabulary (for shapes that need fromGeneral on a real source,
	// then liftReal to int — used when the ℝ entry normalizes to a CNF
	// clause but the leaf wants a curried implication; PowNonneg / PowPos and the
	// two cancellations).
	realT := dsl.RealType
	realLeOp := dsl.RealLeMeta.Term()
	realLtOp := dsl.RealLtMeta.Term()
	realOfNum := dsl.RealOfNumMeta.Term()
	realPowOp := dsl.RealPowMeta.Term()
	realVar := func(name string) *ext.TermWrapper { return ext.Var(ext.TermName(name), realT) }
	realLit := func(n uint64) core.Term { return ext.Apply(realOfNum, omega.Numeral(n)) }
	realLe := func(a, b core.Term) core.Term { return ext.Apply(realLeOp, a, b) }
	realLt := func(a, b core.Term) core.Term { return ext.Apply(realLtOp, a, b) }
	realStar := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealStarMeta.Term(), a, b) }
	realPow := func(m, n core.Term) core.Term { return ext.Apply(realPowOp, m, n) }
	nNum := ext.Var(ext.TermName("n"), dsl.NumType)

	// ── General shapes (mirror InstallRealBundle's, instantiated for int) ────

	// add2General: ∀a b c d. (a ⋈₁ b) ⇒ (c ⋈₂ d) ⇒ (a+c ⋈₃ b+d)
	add2General := func(p1, p2, p3 func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(a, b, c, d)(
			implyT(p1(a, b), implyT(p2(c, d), p3(iplus(a, c), iplus(b, d)))))
	}
	// addLcancelGeneral: ∀p x y. ((p+x) ⋈ (p+y)) ⇔ (x ⋈ y)
	addLcancelGeneral := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(p, x, y)(eqT(rel(iplus(p, x), iplus(p, y)), rel(x, y)))
	}
	// scaleGeneral: ∀c a b. (&0 ⋈ c) ⇒ (a ⋈ b) ⇒ (c·a ⋈ c·b)
	scaleGeneral := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(c, a, b)(
			implyT(rel(ilit(0), c), implyT(rel(a, b), rel(istar(c, a), istar(c, b)))))
	}
	// lessEqOfEqGeneral: ∀a b. (a=b) ⇒ (a≤b)
	lessEqOfEqGeneral := ForAll(a, b)(implyT(eqT(a, b), ile(a, b)))
	// mulPosGeneral: ∀x y. (&0 ⋈ x) ⇒ (&0 ⋈ y) ⇒ (&0 ⋈ x·y) [x, y]
	mulPosGeneral := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(x, y)(implyT(rel(ilit(0), x), implyT(rel(ilit(0), y), rel(ilit(0), istar(x, y)))))
	}
	// lessEqTransGeneral: ∀x y z. (x≤y) ⇒ (y≤z) ⇒ (x≤z)
	lessEqTransGeneral := ForAll(x, y, z)(implyT(ile(x, y), implyT(ile(y, z), ile(x, z))))
	// mulEqZeroGeneral: ∀x y. (x·y = &0) ⇔ (x=&0 ∨ y=&0) (MulEqZero shape).
	// Orientation chosen to match the omega leaf's wantL `(a·b = &0)` directly;
	// macroEq doesn't equate IFF sides that differ only by EQ orientation, so
	// the bundle field must carry the leaf-side LHS form (`x·y = &0`, not
	// `&0 = x·y`). Normalize handles the entry↔general orientation flip.
	mulEqZeroGeneral := ForAll(x, y)(eqT(eqT(istar(x, y), ilit(0)), orT(eqT(x, ilit(0)), eqT(y, ilit(0)))))
	// negFlipShape: ∀x. (&0 ⋈ −x) ⇔ (x ⋈ &0) (NegNonneg/NegPositiveIffNegative; leaf wants flipped form)
	negFlipShape := func(rel func(core.Term, core.Term) core.Term) core.Term {
		return ForAll(x)(eqT(rel(ilit(0), ineg(x)), rel(x, ilit(0))))
	}
	// lessThanTrichotomyShape: ∀a b. ((a<b) ∨ (b<a)) ∨ (a=b) (LessThanTrichotomy, leaf-wanted order)
	lessThanTrichotomyShape := ForAll(a, b)(orT(orT(ilt(a, b), ilt(b, a)), eqT(a, b)))

	// Move-across (leaf-wanted iff shapes, [x, y, z]):
	lessEqSubAddRightShape := ForAll(x, y, z)(eqT(ile(isub(x, y), z), ile(x, iplus(z, y))))
	lessEqSubAddLeftShape := ForAll(x, y, z)(eqT(ile(x, isub(y, z)), ile(iplus(x, z), y)))
	lessThanSubAddRightShape := ForAll(x, y, z)(eqT(ilt(isub(x, y), z), ilt(x, iplus(z, y))))
	lessThanSubAddLeftShape := ForAll(x, y, z)(eqT(ilt(x, isub(y, z)), ilt(iplus(x, z), y)))
	eqSubRightAddShape := ForAll(x, y, z)(eqT(eqT(isub(x, y), z), eqT(x, iplus(z, y))))
	eqSubLeftAddShape := ForAll(x, y, z)(eqT(eqT(x, isub(y, z)), eqT(iplus(x, z), y)))

	// ── Div/rem distribution + int_div/int_rem ↔ divides shapes ──────────────────────
	// The leaf contracts for DivMulAdd / RemMulAdd, binder order
	// [residual, divisor, multiple] (intDivMulAdd / intRemMulAdd's instAll).
	// The remainder law has no guard: at a zero divisor int_rem is the
	// identity and n·p is &0 — the corpus states it unconditionally.
	//   DivMulAdd: ∀m n p. ~(n=&0) ⇒ (int_div(m + n·p, n) = int_div(m,n) + p)
	divMulAddShape := ForAll(m, n, p)(
		implyT(notT(eqT(n, ilit(0))),
			eqT(idiv(iplus(m, istar(n, p)), n), iplus(idiv(m, n), p))))
	//   RemMulAdd: ∀m n p. int_rem(m + n·p, n) = int_rem(m, n)
	remMulAddShape := ForAll(m, n, p)(
		eqT(irem(iplus(m, istar(n, p)), n), irem(m, n)))
	// mulAddLaw reads a contract above off its corpus pack. The corpus
	// states each law as a four-way pack of ∀-clauses
	// over the four spellings of the dividend (int_div_rem.DivMulAddClauses
	// / RemMulAddClauses); the leaf's spelling is the pack's FOURTH
	// clause, `p + n·m`, read with the residual first and the multiple
	// last. A fromGeneral binding cannot reach it — the pack's normalized
	// key is the pack's own, and no entry states the one clause — so the
	// clause is projected (∧-elimination, kernel-faithful and
	// promise-transparent) and re-∀-closed in the leaf's binder order; the
	// result is α-checked against the contract here, at install.
	mulAddLaw := func(pack registry.EntryLike, contract core.Term) *prop.PropWrapper {
		w := fromEntryAsStated(pack)
		for i := 0; i < 3; i++ {
			l, r, ok := prop.MatchesAND(w.Conclusion())
			if !ok {
				panic(fmt.Sprintf("InstallIntLemmaBundle: %s is not a four-way conjunction (clause %d)",
					pack.Entry().Name, i+1))
			}
			w = w.DeriveTrans(prop.HypAND1(l, r))
		}
		// ∀m n p. φ(m, n, p), read at (multiple, divisor, residual) and
		// closed as ∀residual divisor multiple — the fourth clause's m is
		// the multiple and its p the residual.
		residual, divisor, multiple := core.Var("residual", intT), core.Var("divisor", intT), core.Var("multiple", intT)
		w = w.ConclForAllInsts(multiple, divisor, residual).ConclForAllList(residual, divisor, multiple)
		if !w.Conclusion().AlphaEquals(contract) {
			panic(fmt.Sprintf("InstallIntLemmaBundle: %s's fourth clause does not read as the leaf contract:\n got  %s\n want %s",
				pack.Entry().Name, ext.PrintTerm(w.Conclusion()), ext.PrintTerm(contract)))
		}
		return w
	}
	// DivisorBoundedByDividend leaf shape: ∀d e. divides(d,e) ⇒ e≠&0 ⇒ |d|≤|e|
	divisorBoundedByDividendShape := ForAll(d, c)(
		implyT(idvd(d, c),
			implyT(notT(eqT(c, ilit(0))), ile(iabs(d), iabs(c)))))
	// ── int Euclidean int_div/int_rem shapes ─────────────────────────────────────────
	// DivisionAlgorithm: ~(n=&0) ⇒ (m = int_div(m,n)·n + int_rem(m,n) ∧ &0≤int_rem(m,n) ∧ int_rem(m,n)<|n|)
	divisionAlgorithmShape := ForAll(m, n)(
		implyT(notT(eqT(n, ilit(0))),
			prop.And(eqT(m, iplus(istar(idiv(m, n), n), irem(m, n))),
				prop.And(ile(ilit(0), irem(m, n)), ilt(irem(m, n), iabs(n))))))
	// RemUpperAbs (the general n≠0 upper bound of
	// int_div_rem.DivisionAlgorithm): ∀n m. (n=&0) ∨ (int_rem(m,n) < |n|).
	// Binder order [n, m] mirrors the omega leaf's instAll order ([n, m]).
	// Leaf is implyLeaf-wrapped.
	//
	// NOT fromGeneral: the single-clause form is no entry's statement, so
	// PromiseForGeneral's key-exact lookup would panic "no corpus theorem
	// registered" the first time a replayed Arith() step forces the leaf. It
	// is a weakening of DivisionAlgorithm — derived at bind time via
	// omega.DivisionRemUpperAbs (see the field wiring below), the same
	// adapter class as CurryIffConj / MulCancelToScale.
	// DivModUnique: ((m=q·n+r ∧ &0≤r) ∧ r<|n|) ⇒ (q=int_div(m,n) ∧ r=int_rem(m,n)).
	// Conjunction association `((A∧B)∧C)` mirrors the omega leaf's wantL exactly
	// (omega's intDivModUniqWitness builds it left-associated).
	// The entry normalizes to the 4-CNF; fromGeneral on this curried form adapts.
	divModUniqueShape := ForAll(m, q, n, c)(
		implyT(prop.And(prop.And(eqT(m, iplus(istar(q, n), c)), ile(ilit(0), c)),
			ilt(c, iabs(n))),
			prop.And(eqT(q, idiv(m, n)), eqT(c, irem(m, n)))))

	// RemBelowDivisor leaf shape: ∀n m. &0<n ⇒ int_rem(m,n) < n (binder order [n, m] mirrors
	// the omega leaf's instAll order; its normal form is the CNF clause
	// `(¬(&0<n)) ∨ (int_rem(m,n)<n)`; fromGeneral adapts by Normalize key).
	remBelowDivisorShape := ForAll(n, m)(
		implyT(ilt(ilit(0), n), ilt(irem(m, n), n)))

	// RemNonneg leaf shape: ∀n m. (n=&0) ∨ (&0 ≤ int_rem(m,n)) [binder order n, m
	// matches the omega leaf's instAll order [n, m]].
	remNonnegShape := ForAll(n, m)(
		orT(eqT(n, ilit(0)), ile(ilit(0), irem(m, n))))

	// DivByOne / RemByOne normal form: ∀n. (n = int_div(n,&1)). The leaf wants
	// (int_div(m,&1) = m) — alpha-equivalent up to orientation, macroEq
	// auto-orients. Direct fromEntry suffices; below.

	// ── Sources sourced via lift from real_pow (split + IntOfRealThm) ────────
	// real_pow is the conjunction `(∀x. real_pow x 0 = &1) ∧ (∀x ∀n. ...)`. Pull
	// each conjunct, then lift each one independently via IntOfRealThm — the
	// lift is conjunction-aware so it would lift the whole thing in one shot
	// too, but splitting at the source layer lets the per-conjunct cert flow
	// into PowZero / PowSuc separately without a post-lift split.
	realPowConj := fromEntryAsStated(real_pow.Pow)
	powZeroPart, powSucPart, okPow := prop.MatchesAND(realPowConj.Conclusion())
	if !okPow {
		panic("InstallIntLemmaBundle: real_pow is not a top-level conjunction")
	}
	realPowZero := realPowConj.DeriveTrans(prop.HypAND0(powZeroPart, powSucPart)) // ⊢ ∀x. real_pow x 0 = &1
	realPowSuc := realPowConj.DeriveTrans(prop.HypAND1(powZeroPart, powSucPart))  // ⊢ ∀x n. real_pow x (suc n) = x · real_pow x n
	intPowZero := liftReal(realPowZero)                                           // ⊢ ∀x. int_pow x 0 = int_of_num 1
	intPowSuc := liftReal(realPowSuc)                                             // ⊢ ∀x n. int_pow x (suc n) = x · int_pow x n

	// LessEqOfEq wired via fromGeneral first (the entry normalizes to a CNF
	// clause), then LessEqOfEqSwapped derived from it by the kernel composition the
	// num/real bundles use.
	lessEqOfEq := fromGeneral(lessEqOfEqGeneral)

	// QuotientExactOfDivides: the entry's normal form is `∀m n. ((m = n·int_div(m,n)) ⇔ divides(n,m)) ∧
	// ((m = int_div(m,n)·n) ⇔ divides(n,m))`.
	// The outer ∀'s wrap the conjunction (unlike real_pow, which has each
	// conjunct independently ∀-bound), so strip the ∀'s first, then project
	// the SECOND conjunct (the one with the leaf's div·n factor order), take
	// its right-to-left direction `divides ⊢ m = div·n`, EqSym to flip the
	// equality, re-discharge, re-generalize.
	mulDivConj := fromEntry(int_div_rem.DividesIffQuotientExact)
	mulDivStripped, mulDivVars := mulDivConj.StripConclForAll() // body: iff1 ∧ iff2
	aMD, bMD, okMD := prop.MatchesAND(mulDivStripped.Conclusion())
	if !okMD {
		panic("InstallIntLemmaBundle: int_div_rem.DividesIffQuotientExact's body is not a conjunction")
	}
	mulDivRightIff := mulDivStripped.DeriveTrans(prop.HypAND1(aMD, bMD)) // ⊢ (m = int_div(m,n)·n) ⇔ divides(n,m)
	// RightAssume: {divides} ⊢ (m = div·n); EqSym: {divides} ⊢ (div·n = m)
	_, dividesAtom, _ := prop.MatchesIFF(mulDivRightIff.Conclusion())
	mulDivDerived := mulDivRightIff.RightAssume().EqSym()
	// PromoteHyp to ⊢ divides ⇒ (div·n = m), then re-∀.
	mulDivImpl := mulDivDerived.PromoteHyp(dividesAtom).ConclForAllList(mulDivVars...)

	intBundle := &omega.IntLemmaBundle{
		// ── Ring AC + identity/distribution ──────────────────────────────────
		// No chapter member proves any ℤ law in this block; each is bound by
		// lifting its ℝ twin's entry (liftEntry).
		AddSym:           liftEntry(real_construction.AddSym),
		AddAssoc:         liftEntry(real_construction.AddAssoc),
		MulSym:           liftEntry(real_construction.MulSym),
		MulAssoc:         liftEntry(real_construction.MulAssoc),
		AddLeftIdentity:  liftEntry(real_construction.AddLeftId),
		AddRightIdentity: liftEntry(real_ring.AddRightId),
		MulLeftIdentity:  liftEntry(real_construction.MulLeftId),
		MulLeftZero:      liftEntry(real_ring.MulLeftZero),
		LeftDistrib:      liftEntry(real_construction.LeftDistrib),
		RightDistrib:     liftEntry(real_ring.RightDistrib),

		// ── int_of_num homomorphism bridge ───────────────────────────────────
		// Lifted from the ℝ OfNum* entries (liftEntry), which yields the
		// ∀-closed shape the leaf's macroEq instantiates at concrete numerals.
		OfNumAdd: liftEntry(real_construction.OfNumAdd),
		OfNumMul: liftEntry(real_construction.OfNumMul),
		OfNumLt:  liftEntry(real_order_ring.OfNumLessThan),
		OfNumLe:  liftEntry(real_construction.OfNumLessEq),
		OfNumEq:  liftEntry(real_construction.OfNumEq),

		// ── Order basics / duality ───────────────────────────────────────────
		// NotLessThan / LessEqAntisym are int_of_real lifts — liftEntry
		// straight off the ℝ source.
		NotLessThan: liftEntry(real_order_ring.NotLessThan),
		// NotLessEq has no entry: it is the lift of ℝ's, which itself
		// is real_lt's normalized definition (defNorm("real_lt")), so lift
		// that and the result is the desired NotLessEq.
		NotLessEq:         liftReal(defNorm("real_lt")),
		LessEqAntisym:     omega.CurryIffConj(liftEntry(real_construction.LessEqAntisym)),
		LessEqOfEq:        lessEqOfEq,
		LessEqOfEqSwapped: omega.DeriveIntLessEqOfEqSwapped(lessEqOfEq),
		LessEqTrans:       fromGeneral(lessEqTransGeneral),

		// ── Pairwise inequality addition (CNF-clause normal forms, fromGeneral) ──
		LessEqAdd2:         fromGeneral(add2General(ile, ile, ile)),
		LessThanAdd2:       fromGeneral(add2General(ilt, ilt, ilt)),
		LessEqLessThanAdd2: fromGeneral(add2General(ile, ilt, ilt)),
		LessThanLessEqAdd2: fromGeneral(add2General(ilt, ile, ilt)),

		// ── Additive left cancellation (iffs flipped, fromGeneral) ───────────
		LessEqAddLeft:   fromGeneral(addLcancelGeneral(ile)),
		LessThanAddLeft: fromGeneral(addLcancelGeneral(ilt)),

		// ── Monotone scaling (CNF-clause normal forms, fromGeneral) ──────────
		// LessEqCancelMulLeft / LessThanCancelMulLeft: ℤ states neither cancellation law,
		// so these are the REAL pair lifted — the PowNonneg/PowPos route, since
		// IntOfRealThm carries a curried implication across unchanged.
		// fromGeneral resolves the curried REAL shape against
		// real_order_ring.Less{Eq,Than}CancelMulLeft (conjoined or curried,
		// the premises normalize to the same clause), and
		// liftReal then reads it at int. Measured: the lift lands α-equal on
		// the shape the leaf instantiates, with no hypotheses. The sign
		// premise is STRICT in both — `&0 ≤ c` cancels nothing.
		LessEqCancelMulLeft: liftReal(fromGeneral(ForAll(realVar("c"), realVar("a"), realVar("b"))(
			implyT(realLt(realLit(0), realVar("c")),
				implyT(realLe(realStar(realVar("c"), realVar("a")), realStar(realVar("c"), realVar("b"))),
					realLe(realVar("a"), realVar("b"))))))),
		LessThanCancelMulLeft: liftReal(fromGeneral(ForAll(realVar("c"), realVar("a"), realVar("b"))(
			implyT(realLt(realLit(0), realVar("c")),
				implyT(realLt(realStar(realVar("c"), realVar("a")), realStar(realVar("c"), realVar("b"))),
					realLt(realVar("a"), realVar("b"))))))),

		LessEqMulLeft:   fromGeneral(scaleGeneral(ile)),
		LessThanMulLeft: fromGeneral(scaleGeneral(ilt)),

		// ── Sign-known nonlinear fragment + integral domain ─────────────────
		LessEqMul:              fromGeneral(mulPosGeneral(ile)),
		MulPos:                 fromGeneral(mulPosGeneral(ilt)),
		MulEqZero:              fromGeneral(mulEqZeroGeneral),
		NegNonneg:              fromGeneral(negFlipShape(ile)),
		NegPositiveIffNegative: fromGeneral(negFlipShape(ilt)),

		// ── `>`/`≥` definitional bridges ───────────────────────────────────
		// int_gt / int_ge are defined via real_of_int, but int_construction
		// proves the int-native bridge `(x > y) ⇔ (y < x)` directly
		// (GreaterIffLess / GreaterEqIffLessEq) — that IS the leaf shape, so fromEntry is
		// the right binding here (not defNorm, which would give the
		// real-of-int-flavored definitional iff).
		GreaterIffLess:     fromEntry(int_construction.GreaterIffLess),
		GreaterEqIffLessEq: fromEntry(int_construction.GreaterEqIffLessEq),

		// ── Total subtraction / negation primitives ──────────────────────────
		// `int_sub`'s own const def goes through real_of_int (`int_of_real(
		// real_sub(real_of_int x, real_of_int y)) = int_sub(x,y)`), NOT the
		// `a - b = a + (-b)` form the omega leaf wants. The leaf's form IS
		// real_sub's definition lifted through real_of_int — the law
		// `x - y = x + --y`, kernel-equivalent to lifting
		// real_sub's def. Source it that way.
		SubDef:      liftReal(defNorm("real_sub")),
		NegAdd:      liftEntry(real_ring.NegAdd),
		NegNeg:      liftEntry(real_ring.NegNeg),
		NegZero:     liftEntry(real_ring.NegZero),
		MulRightNeg: liftEntry(real_ring.MulRightNeg),

		// ── Relation move-across (iffs, fromGeneral by Normalize key) ────────
		LessEqSubAddRight:   fromGeneral(lessEqSubAddRightShape),
		LessEqSubAddLeft:    fromGeneral(lessEqSubAddLeftShape),
		LessThanSubAddRight: fromGeneral(lessThanSubAddRightShape),
		LessThanSubAddLeft:  fromGeneral(lessThanSubAddLeftShape), // the add/sub exchange law, up to alpha
		EqSubRightAdd:       fromGeneral(eqSubRightAddShape),
		EqSubLeftAdd:        fromGeneral(eqSubLeftAddShape),

		// ── ℤ discreteness — direct bind (normal form matches leaf shape) ───
		Discrete: fromEntry(int_embed.Discrete),

		// ── Piecewise operator definitions ───────────────────────────────────
		// AbsBySign is proved (int_construction.AbsBySign) with the exact
		// piecewise-COND shape the case-split engine wants — direct
		// fromEntry. int_max / int_min / int_sgn are defined through
		// real_of_int (not the COND form), so bind them via
		// lift-from-real-def: the lift's COND homomorphism completion
		// (omega's condPushRealOfInt) pushes real_of_int out through the
		// COND branches, landing the exact piecewise-int leaf shape.
		AbsBySign: fromEntry(int_construction.AbsBySign),
		MaxDef:    liftReal(defNorm("real_max")),
		MinDef:    liftReal(defNorm("real_min")),
		SgnDef:    liftReal(defNorm("real_sgn")),

		// ── int trichotomy (3-literal OR, different binder order) ────────────
		LessThanTrichotomy: fromGeneral(lessThanTrichotomyShape),

		// ── int_pow recursion (project real_pow conjuncts, lift each) ────────
		PowZero: intPowZero,
		PowSuc:  intPowSuc,

		// ── int order/disjunction for bounded enum ──────────────────────────
		// LessEqSplit has no chapter member of its own — lift it from
		// real_order_ring.LessEqSplit.
		LessEqSplit: liftEntry(real_order_ring.LessEqSplit),

		// ── Image sign split ────────────────────────────────────────────
		Image: fromEntry(int_embed.Image),

		// ── int_divides definition (re-∀-closed to the field's [d, e] binder
		// contract — see dividesDefOrdered above) ─────────────────────────
		DividesDef: dividesDefOrdered(),

		// ── int Euclidean int_div/int_rem ───────────────────────────────────────────
		// Mix of direct fromEntry (matching shape) and fromGeneral (curried/iff
		// reshape). RemBelowDivisor / DivByOne / RemByOne are int-native (no real twin); RemBelowDivisor's
		// normal form is `(¬(&0<n)) ∨ (int_rem(x,n)<n)` — fromGeneral
		// canonicalizes against the leaf's curried implication shape.
		DivisionIdentity: fromEntry(int_div_rem.DivisionIdentity),
		RemNonneg:        fromGeneral(remNonnegShape),
		RemBelowDivisor:  fromGeneral(remBelowDivisorShape),
		RemUpperAbs:      omega.DivisionRemUpperAbs(fromEntry(int_div_rem.DivisionAlgorithm)),
		DivModUnique:     fromGeneral(divModUniqueShape),
		DivByZero:        fromEntry(int_div_rem.DivByZero),
		RemByZero:        fromEntry(int_div_rem.RemByZero),
		DivByOne:         fromEntry(int_div_rem.DivByOne),
		RemByOne:         fromEntry(int_div_rem.RemByOne),

		// ── Square / pow-sign / abs ordering ───────────────────────────────
		// Mix of liftEntry (int_of_real lifts of ℝ entries whose normal form
		// ALREADY matches the leaf shape), and lift-of-fromGeneral for the
		// curried-implication ones (PowNonneg / PowPos) whose ℝ entry
		// normalizes to a CNF clause — fromGeneral on the curried REAL shape
		// reconstructs to the leaf-wanted implication, then liftReal carries
		// the curried shape over to int.
		SquareNonneg:             liftEntry(real_order_ring.SquareNonneg),
		SquareOfAbs:              liftEntry(real_pow.SquareOfAbs),
		NegEqZero:                liftEntry(real_ring.NegEqZero),
		AbsLessEqIffPowTwoLessEq: liftEntry(real_pow.AbsLessEqIffPowTwoLessEq),
		AbsTriangle:              fromEntry(int_real_lift.AbsTriangle),
		// PowNonneg / PowPos: the ℝ entries normalize to the CNF
		// clause `¬(0⋈x) ∨ (0⋈x^n)`; the leaf wants the curried implication
		// `(0⋈x) ⇒ (0⋈x^n)`. fromGeneral on the curried REAL shape uses the
		// PromiseForGeneral seam to reconstruct from the CNF source, then
		// liftReal carries the curried shape over to int.
		PowNonneg: liftReal(fromGeneral(ForAll(realVar("x"), nNum)(
			implyT(realLe(realLit(0), realVar("x")),
				realLe(realLit(0), realPow(realVar("x"), nNum)))))),
		PowPos: liftReal(fromGeneral(ForAll(realVar("x"), nNum)(
			implyT(realLt(realLit(0), realVar("x")),
				realLt(realLit(0), realPow(realVar("x"), nNum)))))),
		PowTwoNonneg: liftEntry(real_pow.PowTwoNonneg),

		// ── int_div/int_rem ↔ divides bridges (mostly direct; DivisorBoundedByDividend and
		// QuotientExactOfDivides need shape adapters) ──────────────────────────────────
		DividesIffRemZero:        fromEntry(int_div_rem.DividesIffRemZero),
		DivisorBoundedByDividend: fromGeneral(divisorBoundedByDividendShape),
		QuotientExactOfDivides:   mulDivImpl,
		OfNumDiv:                 fromEntry(int_div_rem.OfNumDiv),
		OfNumRem:                 fromEntry(int_div_rem.OfNumRem),

		// ── int_div/int_rem distribution + agent-invoked + quantifier ───────────────
		// DivMulAdd / RemMulAdd: the fourth clause of each pack, re-closed in
		// the leaf's binder order (mulAddLaw above). The four clauses are
		// not α-variants of one another — they differ by the commutativity
		// of + and ·, which Normalize does not apply — so the pack's key is
		// the pack's and a fromGeneral binding would resolve to no entry.
		DivMulAdd:         mulAddLaw(int_div_rem.DivMulAddClauses, divMulAddShape),
		RemMulAdd:         mulAddLaw(int_div_rem.RemMulAddClauses, remMulAddShape),
		DivisionAlgorithm: fromGeneral(divisionAlgorithmShape),
		// OfNumPow: lifted from its REAL twin's entry (liftEntry).
		OfNumPow:     liftEntry(real_pow.OfNumPow),
		ForallNonneg: fromEntry(int_embed.ForallNonneg),
		ExistsNonneg: fromEntry(int_embed.ExistsNonneg),

		// ── abs/sgn algebraic laws (int_real_lift's lifts from ℝ) ──
		AbsMul:        fromEntry(int_real_lift.AbsMul),
		AbsEven:       fromEntryAsStated(int_real_lift.AbsEven),
		AbsIdempotent: fromEntryAsStated(int_real_lift.AbsIdempotent),
		OfNumAbs:      fromEntry(int_embed.OfNumAbs),
		SgnMul:        fromEntry(int_real_lift.SgnMul),
		SgnOdd:        fromEntryAsStated(int_real_lift.SgnOdd),
	}
	omega.SetIntLemmaBundle(intBundle)
	// Lifted and derived fields declare both their REAL sources and the exact
	// bridge theorem roots; unknown identities fail closed.
	liftRoots := func(source []core.PropKey, bridges ...registry.EntryLike) []core.PropKey {
		return append(append(source, entryKeys(int_construction.RepresentativeInjective)...), entryKeys(bridges...)...)
	}
	roots, foundation := computeBundleCapability(intBundle, map[string][]core.PropKey{
		"LessEqAntisym": liftRoots(entryKeys(real_construction.LessEqAntisym)),
		// These four cannot resolve by IDENTITY: the ℤ image normalizes
		// to a statement over ℤ (NegAdd, LessEqSplit and two more) that
		// no entry proves, so there is no node to match and the bundle
		// would fail closed.
		// Naming the roots is the designed answer: what a lifted field
		// rests on IS its ℝ source plus the construction bridges for the
		// operators it mentions.
		"NegAdd":                   liftRoots(entryKeys(real_ring.NegAdd), int_construction.NegBridge, int_construction.AddBridge),
		"LessEqSplit":              liftRoots(entryKeys(real_order_ring.LessEqSplit)),
		"SquareNonneg":             liftRoots(entryKeys(real_order_ring.SquareNonneg), int_construction.MulBridge, int_construction.OfNumBridge),
		"NegEqZero":                liftRoots(entryKeys(real_ring.NegEqZero), int_construction.NegBridge, int_construction.OfNumBridge),
		"LessEqOfEqSwapped":        entryKeys(int_real_lift.LessEqOfEq),
		"SubDef":                   entryKeys(int_construction.RepresentativeInjective, int_construction.SubBridge),
		"MaxDef":                   entryKeys(int_construction.RepresentativeInjective, int_construction.MaxBridge),
		"MinDef":                   entryKeys(int_construction.RepresentativeInjective, int_construction.MinBridge),
		"SgnDef":                   entryKeys(int_construction.RepresentativeInjective, int_construction.SgnBridge),
		"PowZero":                  liftRoots(entryKeys(real_pow.Pow), int_construction.OfNumBridge, int_construction.MulBridge, int_pow.PowBridge),
		"PowSuc":                   liftRoots(entryKeys(real_pow.Pow), int_construction.OfNumBridge, int_construction.MulBridge, int_pow.PowBridge),
		"DividesDef":               {},
		"RemUpperAbs":              entryKeys(int_div_rem.DivisionAlgorithm),
		"SquareOfAbs":              liftRoots(entryKeys(real_pow.SquareOfAbs), int_construction.AbsBridge, int_pow.PowBridge),
		"AbsLessEqIffPowTwoLessEq": liftRoots(entryKeys(real_pow.AbsLessEqIffPowTwoLessEq), int_construction.AbsBridge, int_construction.MulBridge, int_pow.PowBridge),
		// The two cancellation fields are the REAL pair lifted, so what they
		// rest on is their ℝ source plus the bridges for the operators the
		// statement mentions (the product and the `&0` literal) — the
		// SquareNonneg shape. ℤ proves neither law independently, so there is no
		// ℤ node to match and the bundle would otherwise fail closed.
		"LessEqCancelMulLeft": liftRoots(entryKeys(real_order_ring.LessEqCancelMulLeft),
			int_construction.MulBridge, int_construction.OfNumBridge),
		"LessThanCancelMulLeft": liftRoots(entryKeys(real_order_ring.LessThanCancelMulLeft),
			int_construction.MulBridge, int_construction.OfNumBridge),
		"PowNonneg":              liftRoots(entryKeys(real_pow.PowNonneg), int_construction.OfNumBridge, int_pow.PowBridge),
		"PowPos":                 liftRoots(entryKeys(real_pow.PowPos), int_construction.OfNumBridge, int_pow.PowBridge),
		"PowTwoNonneg":           liftRoots(entryKeys(real_pow.PowTwoNonneg), int_construction.OfNumBridge, int_pow.PowBridge),
		"QuotientExactOfDivides": entryKeys(int_div_rem.DividesIffQuotientExact),
		"DivMulAdd":              entryKeys(int_div_rem.DivMulAddClauses),
		"RemMulAdd":              entryKeys(int_div_rem.RemMulAddClauses),
	})
	omega.SetIntBundleFoundation(foundation)
	installCapability(proof.CapabilityArithInt, roots, foundation)
}
