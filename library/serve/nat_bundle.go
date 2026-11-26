package serve

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// InstallNatBundle promise-backs omega's num NatLemmaBundle from the corpus.
// Call once at engine startup. No silent degrade: in a
// non-test build no placeholder fabricator is installed, so a leaf whose field
// is nil or shape-mismatches panics at the call site (omega/bundle.go).
//
// Each field is the corpus theorem's own (unforced) top promise: omega's
// instAll/macroEq instantiate-and-orient it at use, and closeByOmega forces it
// to a real kernel certificate on the first arith move that needs it — built
// exactly once, memoized.
func InstallNatBundle() {
	// defNorm pulls a const's NORMALIZED defining theorem (the applied iff form)
	// from the corpus env. A definition carries no proof, so there is no
	// theorem to bind: the `>` / `≥` bridges come through the const-def
	// mechanism instead.
	defNorm := func(name string) *prop.PropWrapper {
		return prop.WrapProp(proof.NewScript(env()).ConstDefNormalized(name))
	}

	// fromGeneral wraps PromiseForGeneral for the bundle: it returns a *PropWrapper
	// of the lazy promise of `general`. Forces only when omega actually consumes
	// the leaf at runtime; Normalize runs once per field at install (pure term work).
	fromGeneral := func(general core.Prop) *prop.PropWrapper {
		return prop.WrapProp(PromiseForGeneral(general))
	}
	// Omega shape primitives for the bundle's general forms. Each `Xxx2General`
	// returns the leaf's wanted ∀-form — the binder order matches the leaf's
	// instAll arg order. Only logical-equivalence adaptations go through
	// PromiseForGeneral; weakenings (CurryIffConj / MulCancelToScale) and
	// derivations (DeriveLessEqOfEqSwapped) keep manual adapters.
	num := dsl.NumType
	natPlus := dsl.NatPlusMeta.Term()
	natStar := dsl.NatStarMeta.Term()
	natLe := dsl.NatLeMeta.Term()
	natLt := dsl.NatLtMeta.Term()
	natDiv := dsl.NatDivMeta.Term()
	natMod := dsl.NatModMeta.Term()
	natMinus := dsl.NatMinusMeta.Term()
	plusT := func(a, b core.Term) core.Term { return ext.Apply(natPlus, a, b) }
	starT := func(a, b core.Term) core.Term { return ext.Apply(natStar, a, b) }
	minusT := func(a, b core.Term) core.Term { return ext.Apply(natMinus, a, b) }
	leT := func(a, b core.Term) core.Term { return ext.Apply(natLe, a, b) }
	ltT := func(a, b core.Term) core.Term { return ext.Apply(natLt, a, b) }
	divT := func(a, b core.Term) core.Term { return ext.Apply(natDiv, a, b) }
	modT := func(a, b core.Term) core.Term { return ext.Apply(natMod, a, b) }
	eqT := func(a, b core.Term) core.Term { return core.Eq(a, b) }
	implyT := func(a, b core.Term) core.Term { return ext.Apply(prop.IMPLY, a, b) }
	iffT := func(a, b core.Term) core.Term { return core.Eq(a, b) } // ⇔ is `=` at bool
	v := func(name string) *ext.TermWrapper { return ext.Var(ext.TermName(name), num) }

	// lessEqOfEq is consumed twice: the LessEqOfEq field and the LessEqOfEqSwapped derived from it
	// (DeriveLessEqOfEqSwapped is promise-transparent, so both stay unforced).
	lessEqOfEq := fromEntryAsStated(nat_order.LessEqOfEq)
	// add2-family general: ∀a b c d. (a ⋈₁ b) ⇒ (c ⋈₂ d) ⇒ (a+c ⋈₃ b+d).
	add2General := func(p1, p2, p3 func(core.Term, core.Term) core.Term) core.Prop {
		a, b, c, d := v("a"), v("b"), v("c"), v("d")
		return prop.MakeProp(ext.ForAll(a, b, c, d)(
			implyT(p1(a, b), implyT(p2(c, d), p3(plusT(a, c), plusT(b, d))))))
	}
	// addLcancel-family general: ∀p x y. ((p+x) ⋈ (p+y)) ⇔ (x ⋈ y).
	// Binder order (p,x,y) matches the leaf's args [p, x, y] — addend p first.
	addLcancelGeneral := func(rel func(core.Term, core.Term) core.Term) core.Prop {
		p, x, y := v("p"), v("x"), v("y")
		return prop.MakeProp(ext.ForAll(p, x, y)(
			iffT(rel(plusT(p, x), plusT(p, y)), rel(x, y))))
	}
	// DivModUniq general — the curried-implication shape the NormNatDiv/Mod
	// evaluator's macroThm (and roundedCut's divUniqQuotient) wants (instAll
	// order [m,n,q,r]):
	// ∀m n q r. (m = q·n + r ∧ r < n) ⇒ ((nat_div(m, n) = q) ∧ (nat_mod(m, n) = r)).
	// Its normal form is the CNF clause `(¬(r<n) ∨ (m≠q·n+r)) ∨ (…)` with a
	// different binder order, so it routes through PromiseForGeneral (same
	// shape-adapter seam as the *Add2 lemmas), NOT a direct bind.
	divModUniqGeneral := func() core.Prop {
		m, n, q, r := v("m"), v("n"), v("q"), v("r")
		ante := prop.And(eqT(m, plusT(starT(q, n), r)), ltT(r, n))
		concl := prop.And(eqT(divT(m, n), q), eqT(modT(m, n), r))
		return prop.MakeProp(ext.ForAll(m, n, q, r)(implyT(ante, concl)))
	}
	// SubAddCancel general — the IMPLICATION shape subAddCancelImp's macroThm wants (instAll
	// order [n,m], n first): ∀n m. (n≤m) ⇒ (m = (m-n)+n). Its normal form is the
	// clause `¬(n≤m) ∨ (m=(m-n)+n)`; P⇒Q Normalizes to ¬P∨Q, so it resolves by
	// key through PromiseForGeneral (same seam as the *Add2 / DivModUniq lemmas).
	subAddCancelGeneral := func() core.Prop {
		n, m := v("n"), v("m")
		return prop.MakeProp(ext.ForAll(n, m)(
			implyT(leT(n, m), eqT(m, plusT(minusT(m, n), n)))))
	}
	// ModLessThan general — implication shape (its normal form is the clause
	// `¬(m<n) ∨ (m = nat_mod(m,n))`). Same PromiseForGeneral seam.
	modLessThanGeneral := func() core.Prop {
		m, n := v("m"), v("n")
		return prop.MakeProp(ext.ForAll(m, n)(
			implyT(ltT(m, n), eqT(m, modT(m, n)))))
	}
	natBundle := &omega.NatLemmaBundle{
		// ── Ring AC + clauses + distributivity (shape-stable: bind directly). ──
		AddSym:          fromEntry(nat_arith.AddSym),
		AddAssoc:        fromEntry(nat_arith.AddAssoc),
		MulSym:          fromEntry(nat_arith.MulSym),
		MulAssoc:        fromEntry(nat_arith.MulAssoc),
		AddClauses:      fromEntry(nat_arith.AddClauses),
		MulClauses:      fromEntry(nat_arith.MulClauses),
		LeftAddDistrib:  fromEntry(nat_arith.LeftAddDistrib),
		RightAddDistrib: fromEntry(nat_arith.RightAddDistrib),
		Add1:            fromEntry(nat_arith.Add1),
		// bit0/bit1 unfolding for the DERIVED norm_num multiplication leaves.
		Bit0: fromEntry(nat_arith.Bit0),
		Bit1: fromEntry(nat_arith.Bit1),
		// norm_num bit-recursion (numeral folding + comparison parity).
		NumeralAdd:      fromEntry(nat_arith.NumeralAdd),
		NumeralSuc:      fromEntry(nat_arith.NumeralSuc),
		NumeralMul:      fromEntry(nat_arith.NumeralMul),
		NumeralLessThan: fromEntry(nat_order.NumeralLessThan),
		NumeralLessEq:   fromEntry(nat_order.NumeralLessEq),
		NumeralEq:       fromEntry(nat_arith.NumeralEq),

		// ── Linarith duality / order. ──
		// Shape-stable — corpus form already matches the leaf:
		NotLessThan: fromEntry(nat_order.NotLessThan),
		NotLessEq:   fromEntry(nat_order.NotLessEq),
		LessEqOfEq:  lessEqOfEq,
		ZeroLessEq:  fromEntry(nat_order.ZeroLessEq),
		// `>` / `≥` definitional bridges (const-def, no theorem to bind):
		GtDef: defNorm(">"),
		GeDef: defNorm(">="),
		// Derived from LessEqOfEq (no entry of its own):
		LessEqOfEqSwapped: omega.DeriveLessEqOfEqSwapped(lessEqOfEq),
		// ── Subtraction (monus) layer — the case-split engine. ──
		// AddSubLeftCancel / LessEqTotal / LessEqAdd / SubEqZero are shape-stable (normal form == the
		// leaf shape) → direct bind. SubAddCancel's normal form is the clause
		// `¬(n≤m) ∨ …`; the leaf wants the implication, so it routes through the
		// PromiseForGeneral seam (P⇒Q Normalizes to ¬P∨Q).
		AddSubLeftCancel:   fromEntry(nat_monus.AddSubLeftCancel),
		LessEqTotal:        fromEntry(nat_order.LessEqTotal),
		LessThanTrichotomy: fromEntry(nat_order.LessThanTrichotomy),
		// Parity bridge: nat_even ⇔ nat_mod-2 direct; nat_odd via OddIffNotEven
		// (oddBridge composes it with EvenIffModTwoZero to `nat_odd n ⇔ ¬(0 = nat_mod(n, 2))`).
		// EvenMul/EvenAdd decompose nonlinear parity over a product/sum.
		EvenIffModTwoZero: fromEntry(nat_parity.EvenIffModTwoZero),
		OddIffNotEven:     fromEntry(nat_parity.OddIffNotEven),
		EvenMul:           fromEntry(nat_parity.EvenMul),
		EvenAdd:           fromEntry(nat_parity.EvenAdd),
		EvenIffDouble:     fromEntry(nat_parity.EvenIffDouble),
		LessEqAdd:         fromEntry(nat_order.LessEqAdd),
		SubEqZero:         fromEntry(nat_monus.SubEqZero),
		SubAddCancel:      fromGeneral(subAddCancelGeneral()),
		// Shape-equivalent — go through the unified PromiseForGeneral seam:
		// declare the leaf shape, Normalize finds the corpus key, reconstruct
		// adapts back at force time. Zero kernel work / Normalize at install.
		LessEqAdd2:         fromGeneral(add2General(leT, leT, leT)), // (≤,≤,≤)
		LessThanAdd2:       fromGeneral(add2General(ltT, ltT, ltT)), // (<,<,<)
		LessEqLessThanAdd2: fromGeneral(add2General(leT, ltT, ltT)), // (≤,<,<) — addLeLt
		LessThanLessEqAdd2: fromGeneral(add2General(ltT, leT, ltT)), // (<,≤,<) — addLtLe
		LessEqAddCancel:    fromGeneral(addLcancelGeneral(leT)),     // (p+x ≤ p+y) ⇔ (x≤y)
		LessThanAddCancel:  fromGeneral(addLcancelGeneral(ltT)),     // strict twin
		// Shape-WEAKENED at population time — corpus is strictly stronger; the
		// adapter drops one iff direction (CurryIffConj) or one disjunct
		// (MulCancelToScale). Normalize keys do NOT match, so these stay manual.
		LessEqAntisym: omega.CurryIffConj(fromEntry(nat_order.LessEqAntisym)),       // drops (a=b) → (a≤b∧b≤a)
		LessEqMulMono: omega.MulCancelToScale(fromEntry(nat_order.LessEqMulCancel)), // drops m=0 disjunct
		// Strict scaling keeps the `m≠0` premise (2-premise form); ltScale discharges
		// it numerically on the concrete coefficient. Only a coefficient > 1 on a
		// STRICT row reaches it (lam==1 rows skip scaling). A coeff>1 goal also
		// ring-normalizes the `c·atom` products, through the mulB0/mulB1 leaves omega
		// derives from Bit0/Bit1 (bound above).
		LessThanMulMono: omega.CurryIffConj(fromEntry(nat_order.LessThanMulCancel)), // (m≠0)⇒(n<p)⇒(m·n<m·p)
		// ── Integer (Presburger) layer. ──
		// ModEqZero's normal form already matches the notDivides leaf shape
		// (`(∃q. m=q·n) ⇔ (0 = nat_mod(m, n))`), so bind directly. DivModUniq
		// normalizes to a clause → PromiseForGeneral adapts to the curried
		// implication NormNatDiv/Mod's macroThm wants. Both are pure `num`
		// (no `divides`/real); they make notDivides + NormNatDiv/Mod real, so
		// integer goals (`2a≠1`, …) close instead of declining.
		ModEqZero:  fromEntry(nat_div_mod.ModEqZero),
		DivModUniq: fromGeneral(divModUniqGeneral()),
		// ── Integer rounding cut (omega's roundedCut). ──
		// SucLessEqIffLessThan binds directly (corpus form `(m<n)⇔(suc m≤n)` == leaf shape).
		// LessEqRightDivEq binds directly: its normal form is the disjunction
		// `((n≤nat_div(b, a))⇔(a·n≤b)) ∨ (a=0)`, and roundedCut discharges the
		// `a=0` disjunct on the concrete (≠0) divisor — the leaf consumes the
		// disjunction itself, so no shape adapter. DivModUniq above is reused
		// to evaluate the symbolic nat_div.
		SucLessEqIffLessThan: fromEntry(nat_order.SucLessEqIffLessThan),
		LessEqRightDivEq:     fromEntry(nat_div_mod.LessEqRightDivEq),
		// Bounded enumeration split (omega's proveBoundedEnum). LessEqSplit peels a literal
		// bound `x ≤ c` into `x<c ∨ x=c`; LessThanSucIffLessEq bridges the `x<c` disjunct down
		// to `x ≤ c-1` for the recursion. Both normal forms == leaf shape → direct.
		LessEqSplit:          fromEntry(nat_order.LessEqSplit),
		LessThanSucIffLessEq: fromEntry(nat_order.LessThanSucIffLessEq),
		// nat_max/nat_min const defs — definitions, pulled via the const-def
		// mechanism (defNorm), like GtDef/GeDef. Power the nat_max/nat_min case-split.
		MaxDef: defNorm("nat_max"),
		MinDef: defNorm("nat_min"),
		// dist — the num distance. nat_monus.Dist is the THEOREM
		// `∀m n. nat_dist(,(m,n)) = (m-n)+(n-m)` (not the raw fst/snd const def),
		// so bind it directly; the bridge is one instantiation. Powers dist→monus.
		Dist: fromEntry(nat_monus.Dist),
		// Sub recursion — powers the predecessor→(n-1) bridge. A chapter
		// member, so bind directly.
		Sub: fromEntryAsStated(nat_monus.Sub),
		// Division — powers the nat_div/nat_mod bounded-atom enricher's
		// n≠0 conditional injections (`nat_mod(m,n) < n` and the canonical identity
		// `m = nat_div(m,n)·n + nat_mod(m,n)`). A chapter member, so bind directly.
		Division: fromEntry(nat_div_mod.Division),
		// nat_pow recursion + shortcuts — power the literal-exponent
		// unfolding (omega's expUnfold), feeding the resulting product chain into
		// RingProveFull. PowOne/PowTwo give cheaper direct shortcuts for c=1,2.
		// OnePow/ZeroPow handle the symbolic-n / special-base cases (`1^n = 1`,
		// `0^n = COND(n=0, 1, 0)` which then collapses through trivialCondRewrite).
		NatPow:  fromEntryAsStated(nat_arith.NatPow),
		PowOne:  fromEntry(nat_arith.PowOne),
		PowTwo:  fromEntry(nat_arith.PowTwo),
		OnePow:  fromEntry(nat_arith.OnePow),
		ZeroPow: fromEntry(nat_arith.ZeroPow),
		// factorial recursion — powers the literal-factorial simp leaf
		// (omega's factSimp) that folds `factorial(c)` to its numeral value c!.
		Factorial: fromEntryAsStated(nat_arith.Factorial),
		// nat_div/nat_mod layer. Direct binds for the
		// unconditional-shape lemmas (normal form == leaf shape); ModLessThan goes
		// through PromiseForGeneral because its normal form is the clause
		// `¬(m<n) ∨ (m=nat_mod(m,n))` while the leaf wants the implication
		// `(m<n) ⇒ (m=nat_mod(m,n))` — same seam as SubAddCancel.
		DivLessEq:   fromEntry(nat_div_mod.DivLessEq),
		ModLessEq:   fromEntry(nat_div_mod.ModLessEq),
		DivZero:     fromEntry(nat_div_mod.DivZero),
		ModZero:     fromEntry(nat_div_mod.ModZero),
		ModRefl:     fromEntry(nat_div_mod.ModRefl),
		DivRefl:     fromEntry(nat_div_mod.DivRefl),
		ModLessThan: fromGeneral(modLessThanGeneral()),
		DivEqZero:   fromEntry(nat_div_mod.DivEqZero),
		DivMult2:    fromEntry(nat_div_mod.DivMult2),
		// nat_div/nat_mod unconditional simp leaves (omega's modMultAdd, divDivNest):
		// affine-nat_mod reduction and nested-nat_div flattening.
		ModMultAdd: fromEntry(nat_div_mod.ModMultAdd),
		DivDiv:     fromEntry(nat_div_mod.DivDiv),
		// nat_div/nat_mod distribution.
		// • DivMulLessEq — the floor lower bound, injected by divModFacts.
		// • DivMultAdd — the conditional affine-nat_div simp leaf's
		// theorem (4-clause `(n=0)∨eq` conjunction the leaf projects + discharges).
		// • ModAddMod — the combine-direction nat_mod simp leaf; the
		// entry states the distribute orientation, eqLeaf auto-flips to the reducing one.
		// • DivAddMod — NOT wired: a relational iff with no normalizing
		// direction, so no leaf consumes it (reserved bundle field only).
		DivMulLessEq: fromEntry(nat_div_mod.DivMulLessEq),
		DivMultAdd:   fromEntry(nat_div_mod.DivMultAdd),
		ModAddMod:    fromEntry(nat_div_mod.ModAddMod),
		// PosIffNonzero powers the symbolic-n=0 case-split (`n≠0 ⇔ 0<n`).
		PosIffNonzero: fromEntry(nat_order.PosIffNonzero),
		// MulEqZero powers the zero-product hypothesis split and the
		// positivity of a product of positive factors.
		MulEqZero: fromEntryAsStated(nat_arith.MulEqZero),
		// The cancellation laws power the cancellation of the factors a
		// hypothesis's two sides share; PowPositive, the positivity of a
		// power of a positive base; PowEqZero, a hypothesis that a power
		// is zero.
		MulEqCancel:       fromEntryAsStated(nat_arith.MulEqLCancel),
		LessEqMulCancel:   fromEntryAsStated(nat_order.LessEqMulCancel),
		LessThanMulCancel: fromEntryAsStated(nat_order.LessThanMulCancel),
		PowPositive:       fromEntryAsStated(nat_order.PowPositive),
		PowEqZero:         fromEntryAsStated(nat_arith.PowEqZero),
		// nat_div/nat_mod enrichment facts for a multiple and a nested residue. The
		// multiple-is-zero fact derives from the already-bound ModEqZero (no field);
		// idempotence binds ModModRefl (`∀m n. nat_mod(m,n) = nat_mod(nat_mod(m,n),n)`)
		// directly — normal form == leaf shape (eqLeaf auto-orients).
		ModModRefl: fromEntry(nat_div_mod.ModModRefl),
	}
	omega.SetNatLemmaBundle(natBundle)
	// Canonical roots and initial closure. Shape adapters are explicit so an
	// unresolved hidden theorem edge fails during installation. The merged
	// manifest later refines this closure with all corpus edges.
	roots, foundation := computeBundleCapability(natBundle, map[string][]core.PropKey{
		// Shape adapters/derived bridges retain the named theorem as their
		// actual proof source even though the adapted statement has a different
		// normalized key. Definitions are explicit primitive leaves.
		"LessEqAntisym":     entryKeys(nat_order.LessEqAntisym),
		"LessEqMulMono":     entryKeys(nat_order.LessEqMulCancel),
		"LessThanMulMono":   entryKeys(nat_order.LessThanMulCancel),
		"LessEqOfEqSwapped": entryKeys(nat_order.LessEqOfEq),
		"GtDef":             {},
		"GeDef":             {},
		"MaxDef":            {},
		"MinDef":            {},
	})
	omega.SetNatBundleFoundation(foundation)
	installCapability(proof.CapabilityArithNat, roots, foundation)
}
