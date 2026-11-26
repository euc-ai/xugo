package omega

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// macroEq instantiates a bundle equality/iff theorem at args (leading ∀'s) and
// orients it to ⊢ wantL = wantR, flipping with EqSym when the theorem is stated
// in the reverse direction. Returns (nil,false) when thm is absent or its
// instantiation does not match the target — the caller then keeps its
// placeholder, so a shape mismatch degrades gracefully rather than breaking.
func macroEq(thm *prop.PropWrapper, args []Term, wantL, wantR Term) (*prop.PropWrapper, bool) {
	if thm == nil {
		return nil, false
	}
	w := instAll(thm, args)
	l, r, ok := prop.MatchesEQ(w.Conclusion())
	if !ok {
		return nil, false
	}
	if l.AlphaEquals(wantL) && r.AlphaEquals(wantR) {
		return w, true
	}
	if l.AlphaEquals(wantR) && r.AlphaEquals(wantL) {
		return w.EqSym(), true
	}
	return nil, false
}

// macroThm instantiates a non-equality bundle theorem (an implication lemma) at
// args and accepts it only if its conclusion α-matches want. Graceful fallback
// on absence or shape mismatch, like macroEq.
func macroThm(thm *prop.PropWrapper, args []Term, want Term) (*prop.PropWrapper, bool) {
	if thm == nil {
		return nil, false
	}
	w := instAll(thm, args)
	if w.Conclusion().AlphaEquals(want) {
		return w, true
	}
	return nil, false
}

// eqLeaf wires a macro equality/iff leaf: the bundle theorem oriented to
// ⊢ wantL = wantR, or the placeholder. implyLeaf is the implication-lemma analog.
func eqLeaf(thm *prop.PropWrapper, args []Term, wantL, wantR Term) *prop.PropWrapper {
	if w, ok := macroEq(thm, args, wantL, wantR); ok {
		return w
	}
	return placeholderEq(thm, wantL, wantR)
}

func implyLeaf(thm *prop.PropWrapper, args []Term, want Term) *prop.PropWrapper {
	if w, ok := macroThm(thm, args, want); ok {
		return w
	}
	return placeholderConcl(thm, want)
}

// Bundle-nil placeholder seam.
//
// A named-lemma leaf (eqLeaf / implyLeaf / cmpLeaf / clauseLeaf / the real
// twins) whose bundle field is nil has no real theorem to instantiate. What
// happens then is decided by ONE signal — whether a placeholder fabricator is
// installed:
//
//   - PRODUCTION (the default): no fabricator. A bundle-nil leaf is a
//     population bug — the field should have been bound — so placeholderConcl
//     PANICS rather than fabricating a cert. This is the normal, non-test state;
//     there is no "mode" to turn on.
//   - TESTS: a _test.go init installs the fabricator (SetPlaceholderFabricator),
//     the sole core.TestThm reference. A bundle-nil leaf then falls back to a
//     statement-correct stand-in, so omega's algorithm unit tests can exercise
//     the kernel composition without the higher corpus layer (which omega cannot
//     import). A test that wants production behavior in a fabricator-installed
//     package removes the fabricator for its duration.
//
// So core.TestThm never enters the production build, and "a degrade panics" is
// the default, not an opt-in.
var fabricatePlaceholder func(concl Term) *prop.PropWrapper

// SetPlaceholderFabricator installs the test stand-in fabricator. Tests call it
// from init() with a core.TestThm closure; pass nil to clear (production
// behavior — a bundle-nil leaf then panics).
func SetPlaceholderFabricator(fn func(Term) *prop.PropWrapper) { fabricatePlaceholder = fn }

// placeholderConcl returns a statement-correct stand-in ⊢ concl via the
// test-installed fabricator, or panics when none is installed (the production
// default: a degraded leaf is a population bug, never silently fabricated).
//
// `thm` is the bundle field the leaf tried to consume (nil when the leaf has
// no backing field). The panic distinguishes the two degrade causes — a field
// that was never bound vs. a field that IS bound but whose instantiation
// failed the leaf's α-match (orientation/shape drift in the binding) — the
// former points at the bundle installer, the latter at the binding's SHAPE.
func placeholderConcl(thm *prop.PropWrapper, concl Term) *prop.PropWrapper {
	if fabricatePlaceholder == nil {
		cause := "its bundle theorem field is UNBOUND (nil — the installer never populated it)"
		if thm != nil {
			cause = fmt.Sprintf("its bundle theorem field IS bound (⊢ %s) but the "+
				"instantiated theorem failed to α-match the leaf's wanted shape "+
				"(orientation/shape drift in the binding)", ext.PrintTerm(thm.Conclusion()))
		}
		panic(fmt.Sprintf("omega: degraded leaf ⊢ %s — %s, and no test placeholder "+
			"fabricator is installed (production must bind every leaf its goals reach; "+
			"SetPlaceholderFabricator is test-only)", ext.PrintTerm(concl), cause))
	}
	return fabricatePlaceholder(concl)
}

// placeholderEq is the equality/iff specialization (⊢ l = r). core.Eq is plain
// term construction, not a fabricated cert.
func placeholderEq(thm *prop.PropWrapper, l, r Term) *prop.PropWrapper {
	return placeholderConcl(thm, core.Eq(l, r))
}

// Background-derived bundle theorems: the linarith fields that have no entry
// of their own and so cannot be promise-backed by an entry's Build. The
// derivation is real kernel composition over a supplied named theorem, and is
// promise-transparent — it threads its input, forcing the dependency only when
// the result is itself forced (at closeByOmega).
//
// The adapters use prop's ∀-strip / re-generalize methods (StripConclForAll /
// ConclForAllList) directly. A field whose leaf shape is a
// pure logical EQUIVALENT of its theorem (LessEqAdd2 / LessThanAdd2 / LessEqLessThanAdd2 /
// LessThanLessEqAdd2 / LessEqAddCancel / LessThanAddCancel) needs no adapter here: it is wired
// through serve.PromiseForGeneral, the Normalize-and-reconstruct seam. The
// adapters below (CurryIffConj / MulCancelToScale / DeriveLessEqOfEqSwapped) are
// weakenings or derivations, not equivalences, so PromiseForGeneral's key-exact
// lookup can't reach them.

// CurryIffConj converts a corpus lemma from its iff-with-conjunction form
// ∀…. X ⇔ (A ∧ B) into omega's curried implication ∀…. A ⇒ B ⇒ X, via the RHS→LHS
// direction of the iff against the conjunction of the two premises. Used for
// LessEqAntisym (X = `m=n`) and LessThanMulMono (X = `m·n < m·p`, A = `m≠0`,
// B = `n<p` — the strict scaling lemma whose `m≠0` premise ltScale discharges).
func CurryIffConj(thm *prop.PropWrapper) *prop.PropWrapper {
	body, vars := thm.StripConclForAll()
	x, conj, ok := prop.MatchesIFF(body.Conclusion())
	if !ok {
		panic("CurryIffConj: conclusion is not an iff")
	}
	_ = x
	la, lb, ok := prop.MatchesAND(conj)
	if !ok {
		panic("CurryIffConj: iff RHS is not a conjunction")
	}
	// {A,B} ⊢ A∧B ⊢ X  (RightAssume turns ⊢ X⇔conj into {conj}⊢X).
	res := prop.ConclAND(la, lb).DeriveTrans(body.RightAssume())
	return res.PromoteHyp(lb).PromoteHyp(la).ConclForAllList(vars...)
}

// ReorderForall re-binds the leading ∀'s of `thm` in the order given by `perm`
// (perm[i] = index of the corpus binder to place in position i). Used to align a
// corpus lemma's binder order with the position order omega's leaf instantiates
// at; the body is unchanged, so an iff leaf still auto-orients via macroEq.
// (LessEqAddCancel / LessThanAddCancel: corpus binds (n,p,m), the leaf wants the
// addend m first → perm {2,0,1}.)
func ReorderForall(thm *prop.PropWrapper, perm ...int) *prop.PropWrapper {
	body, vars := thm.StripConclForAll()
	ordered := make([]core.VarTerm, len(perm))
	for i, j := range perm {
		ordered[i] = vars[j]
	}
	return body.ConclForAllList(ordered...)
}

// MulCancelToScale converts LessEqMulMono from its corpus cancel form
// ∀m n p. ((m*n) ≤ (m*p)) ⇔ ((n ≤ p) ∨ (m = 0)) into omega's scaling implication
// ∀m n p. (n ≤ p) ⇒ ((m*n) ≤ (m*p)) (the leScale leaf shape, leaf args [c,a,b] →
// (a≤b)⇒(c·a≤c·b)). The `m = 0` disjunct is simply dropped by ∨-introduction —
// sound here because `c·a ≤ c·b` holds for every c (including 0). The strict `<`
// twin (LessThanMulMono) keeps its `m≠0` premise — see CurryIffConj + ltScale,
// which discharges it on the concrete (always-positive) coefficient.
func MulCancelToScale(thm *prop.PropWrapper) *prop.PropWrapper {
	body, vars := thm.StripConclForAll()
	mul, disj, ok := prop.MatchesIFF(body.Conclusion())
	if !ok {
		panic("MulCancelToScale: conclusion is not an iff")
	}
	_ = mul
	np, mz, ok := prop.MatchesOR(disj)
	if !ok {
		panic("MulCancelToScale: iff RHS is not a disjunction")
	}
	// {n≤p} ⊢ (n≤p)∨(m=0) ⊢ (m*n)≤(m*p)
	res := prop.ConclOR0(np, mz).DeriveTrans(body.RightAssume())
	return res.PromoteHyp(np).ConclForAllList(vars...)
}

// DivisionRemUpperAbs projects the RemUpperAbs leaf shape
// `∀n m. (n = &0) ∨ (int_rem(m,n) < |n|)` out of int_div_rem.DivisionAlgorithm's form
// `∀n m. (n = &0) ∨ (((m = div·n+rem) ∧ (&0 ≤ rem)) ∧ (rem < |n|))` by
// dropping the two sibling conjuncts under the right disjunct — ∨-cases on
// the corpus conclusion, ∧-elim on the right branch. Same adapter class as
// MulCancelToScale (a weakening, not an equivalence): no entry states the
// single-clause form, so PromiseForGeneral's key-exact lookup can't reach it. Binder order [n, m] is inherited from the
// entry itself, matching the omega leaf's instAll order.
func DivisionRemUpperAbs(thm *prop.PropWrapper) *prop.PropWrapper {
	body, vars := thm.StripConclForAll()
	p, q, ok := prop.MatchesOR(body.Conclusion())
	if !ok {
		panic("DivisionRemUpperAbs: conclusion is not a disjunction")
	}
	ab, d, ok := prop.MatchesAND(q)
	if !ok {
		panic("DivisionRemUpperAbs: right disjunct is not a conjunction")
	}
	// {P} ⊢ P∨D and {(A∧B)∧D} ⊢ P∨D, discharged to implications for ByCases.
	fromP := prop.ConclOR0(p, d)
	fromQ := prop.ConclOR1(p, d).DeriveHypFrom(prop.HypAND1(ab, d))
	res := prop.ByCases(fromP.Conclusion(), p, q).
		DeriveHypFrom(body).
		DeriveHypFrom(fromP.PromoteHyp(p)).
		DeriveHypFrom(fromQ.PromoteHyp(q))
	return res.ConclForAllList(vars...)
}

// deriveLessEqOfEqSwapped builds ⊢ ∀a b. (a = b) ⇒ (b ≤ a) from an LessEqOfEq-shaped lemma
// (⊢ ∀m n. (m = n) ⇒ (m ≤ n)) over element type `ty`. The library states only
// that one; omega's lessEqOfEqSwapped leaf wants the b≤a orientation (LessEqOfEq on the
// swapped equality), so it instantiates at the swapped pair and bridges the
// antecedent with eq-symmetry. Each bundle's LessEqOfEqSwapped field is this derivation,
// applied by the install to the theorem its LessEqOfEq field binds.
//
// The composition is type-generic — eqT is core.Eq and the `≤` rides lessEqOfEq's
// own conclusion — so num and real differ only in the type of the two vars.
// (`ty` is a runtime core.HolType, not a static type, so this is a plain
// parameter rather than a Go type parameter.)
func deriveLessEqOfEqSwapped(lessEqOfEq *prop.PropWrapper, ty core.HolType) *prop.PropWrapper {
	a := ext.Var("a", ty)
	b := ext.Var("b", ty)
	// lessEqOfEq at (b, a):  ⊢ (b = a) ⇒ (b ≤ a)  →  (b=a) ⊢ (b≤a)
	body := lessEqOfEq.ConclForAllInst(b).ConclForAllInst(a).DemoteHyp()
	// (a = b) ⊢ (b = a)  then transport the hyp:  (a = b) ⊢ (b ≤ a)
	bodyAB := prop.WrapProp(core.Assume(eqT(a, b))).EqSym().DeriveTrans(body)
	// Discharge to ⊢ (a=b) ⇒ (b≤a), then ∀-generalize (a outer, b inner).
	return bodyAB.PromoteHyp(eqT(a, b)).ConclForAll(b.AssertVar()).ConclForAll(a.AssertVar())
}

// DeriveLessEqOfEqSwapped / DeriveRealLessEqOfEqSwapped / DeriveIntLessEqOfEqSwapped are the num / real / int
// instances.
func DeriveLessEqOfEqSwapped(lessEqOfEq *prop.PropWrapper) *prop.PropWrapper {
	return deriveLessEqOfEqSwapped(lessEqOfEq, dsl.NumType)
}
func DeriveRealLessEqOfEqSwapped(lessEqOfEq *prop.PropWrapper) *prop.PropWrapper {
	return deriveLessEqOfEqSwapped(lessEqOfEq, dsl.RealType)
}
func DeriveIntLessEqOfEqSwapped(lessEqOfEq *prop.PropWrapper) *prop.PropWrapper {
	return deriveLessEqOfEqSwapped(lessEqOfEq, dsl.IntType)
}
