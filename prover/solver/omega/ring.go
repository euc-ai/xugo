package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Abstract linear form (the ring normalizer's linear fragment): konst + Σ coeff·atom, with atoms
// sorted by Term.Compare and distinct. An "atom" is any maximal subterm that is
// not +, scalar ·, or a numeral literal — a variable, an opaque subterm like
// f(x), OR (over num) a canonical MONOMIAL: a Compare-sorted product of base
// atoms, the full ring's own atom notion.
//
// This is the UNTRUSTED model: it computes the normal form; the proof layer
// (normalizeProof below) re-derives `t = toTerm(form)` with kernel steps. A
// nonlinear product (atom·atom) is expanded over the canonical monomial basis
// when the Domain sets `polyMul` (num, real and int all do) — see
// domain.go's linOf. So `m·p` and `p·m` are the SAME atom, and linarith reads
// every comparison as a polynomial over the shared basis.

type monomialL struct {
	coeff _Integer
	atom  Term
}

type linForm struct {
	konst _Integer    // ≥ 0
	monos []monomialL // sorted by atom Compare, distinct atoms, coeff > 0
}

func linConst(n _Integer) linForm { return linForm{konst: n} }

func linAtom(a Term) linForm { return linForm{monos: []monomialL{{coeff: integerOne, atom: a}}} }

func (lf linForm) isConst() bool { return len(lf.monos) == 0 }

// atomCmp orders atoms; monos are kept in this order.
func atomCmp(a, b Term) int { return a.Compare(b) }

// addMono inserts (c·a) into a sorted mono list, combining a like atom.
func addMono(monos []monomialL, c _Integer, a Term) []monomialL {
	i, found := slices.BinarySearchFunc(monos, a, func(m monomialL, a Term) int {
		return atomCmp(m.atom, a)
	})
	if found {
		out := slices.Clone(monos)
		out[i].coeff = out[i].coeff.add(c)
		return out
	}
	return slices.Insert(slices.Clone(monos), i, monomialL{coeff: c, atom: a})
}

func linAdd(x, y linForm) linForm {
	out := linForm{konst: x.konst.add(y.konst), monos: slices.Clone(x.monos)}
	for _, m := range y.monos {
		out.monos = addMono(out.monos, m.coeff, m.atom)
	}
	return out
}

// linSub computes the ℤ-group difference x − y AS A num form, succeeding iff the
// result is representable over num — i.e. x ≥ y componentwise (every atom's
// coefficient in x is ≥ its coefficient in y, and konst_x ≥ konst_y). A
// linForm's coefficients are naturals, so "the subtraction stays non-negative"
// IS the componentwise-≥ test: ok=false the instant any component would go
// negative.
//
// This is the classifier the subtraction layer (nat_sub.go) pivots on for `a − b`:
//
//	linSub(la, lb) ok   ⇒ a ≥ b, so the monus is the genuine difference d
//	                      (subCancel rewrites a−b → d).
//	linSub(lb, la) ok   ⇒ b ≥ a, so the monus truncates to 0 (subTrunc).
//	neither             ⇒ mixed sign — truncation is value-dependent, opaque;
//	                      left for the monus case-split decision path.
func linSub(x, y linForm) (linForm, bool) {
	if x.konst.cmp(y.konst) < 0 {
		return linForm{}, false
	}
	out := linForm{konst: x.konst.sub(y.konst), monos: slices.Clone(x.monos)}
	for _, m := range y.monos {
		i, found := slices.BinarySearchFunc(out.monos, m.atom, func(o monomialL, a Term) int {
			return atomCmp(o.atom, a)
		})
		if !found || out.monos[i].coeff.cmp(m.coeff) < 0 {
			return linForm{}, false
		}
		if out.monos[i].coeff.equal(m.coeff) {
			out.monos = slices.Delete(out.monos, i, i+1) // coeff→0: drop (coeff>0 invariant)
		} else {
			out.monos[i].coeff = out.monos[i].coeff.sub(m.coeff)
		}
	}
	return out, true
}

// linScale multiplies a whole form by a numeral scalar. c==0 ⇒ zero form.
func linScale(c _Integer, x linForm) linForm {
	if c.isZero() {
		return linForm{}
	}
	out := linForm{konst: c.mul(x.konst)}
	for _, m := range x.monos {
		out.monos = append(out.monos, monomialL{coeff: c.mul(m.coeff), atom: m.atom})
	}
	return out
}

// linOf computes the linear form of t over `num` (untrusted). ok=false if t is
// nonlinear (a product of two non-constant subforms) or contains a non-literal
// numeral. The extraction logic is domain-generic and lives on *Domain
// (domain.go); this is the `num` entry point used throughout the package.
func linOf(t Term) (linForm, bool) { return natDomain.linOf(t) }

// toTerm builds the canonical (uniform) `num` term for the form (domain.go
// `buildTerm`): monomials as `coeff * atom` with coeff always explicit, sorted,
// then the constant `Numeral(konst)` appended as the final summand (always
// present), left-nested. No monomials ⇒ just the constant. Equal forms ⇒
// syntactically equal terms (the decision invariant).
func (lf linForm) toTerm() Term { return natDomain.buildTerm(lf) }

// Full multivariate ring: generalizes the linear normalizer by letting
// an "atom" be a MONOMIAL — a sorted product of base atoms (variables), with
// repetition encoding powers. A monomial is represented by its canonical product
// TERM `((a₁·a₂)·…)` (base atoms Compare-sorted), so the entire additive
// machinery (linForm/linAdd/toTerm/mergeProof/insertMonoEq/scaleProof) is reused
// verbatim with that term as the key. The ONLY new ingredient is multiplication:
// mMul (model) + mulProofFull (proof).

// monoAtomsOf flattens a monomial product term into its base-atom list
// (a single variable flattens to itself).
func monoAtomsOf(m Term) []Term { return DecomposesStar(m) }

// monoProductOf builds the canonical product term of base atoms (already in the
// desired order), left-nested. Requires ≥1 atom.
func monoProductOf(atoms []Term) Term {
	res := atoms[0]
	for _, a := range atoms[1:] {
		res = star(res, a)
	}
	return res
}

// sortMerge concatenates two base-atom lists and Compare-sorts them (stable),
// so equal monomials always yield an identical product term.
func sortMerge(xs, ys []Term) []Term {
	out := make([]Term, 0, len(xs)+len(ys))
	out = append(out, xs...)
	out = append(out, ys...)
	slices.SortStableFunc(out, func(a, b Term) int { return a.Compare(b) })
	return out
}

// monoMulTerm is the canonical product term of two monomials.
func monoMulTerm(m, n Term) Term {
	return monoProductOf(sortMerge(monoAtomsOf(m), monoAtomsOf(n)))
}

// mMul multiplies two linForms (whose atoms are monomial product terms),
// returning the canonical product linForm. Distributes over all term pairs and
// the two constants; addMono combines like monomials and folds coefficients.
func mMul(la, lb linForm) linForm {
	res := linForm{konst: la.konst.mul(lb.konst)}
	ins := func(coeff _Integer, atom Term) {
		if !coeff.isZero() {
			res.monos = addMono(res.monos, coeff, atom)
		}
	}
	for _, mi := range la.monos { // monomial_la · konst_lb
		ins(mi.coeff.mul(lb.konst), mi.atom)
	}
	for _, mj := range lb.monos { // konst_la · monomial_lb
		ins(la.konst.mul(mj.coeff), mj.atom)
	}
	for _, mi := range la.monos { // monomial · monomial
		for _, mj := range lb.monos {
			ins(mi.coeff.mul(mj.coeff), monoMulTerm(mi.atom, mj.atom))
		}
	}
	return res
}

// _polyMulMonoCap is the fuse of the monomial-basis product natPolyMul feeds
// linOf (domain.go). It bounds a pathological expansion ((a₁+…+aₙ)·(b₁+…+bₙ)
// is n² monomials) the way the FM budgets bound elimination — a resource
// policy, not a goal-class calibration; healthy corpus forms sit orders of
// magnitude below it. A fuse decline never fails the extraction: linOf falls
// back to the opaque-atom reading of the product.
const _polyMulMonoCap = 64

// natPolyMul is the Domain.polyMul instance for num (domain.go): polyMulWith
// over the num monomial product. A free function rather than natRing's method
// value because natDomain's literal initializes before natRing exists (the
// two would form an initialization cycle); the real and int instances are
// wired in inits (real_lemmas.go, int_lemmas.go).
func natPolyMul(la, lb linForm) (linForm, bool) { return polyMulWith(monoMulTerm, la, lb) }

// polyMul is this vocabulary's Domain.polyMul: polyMulWith over the
// vocabulary's own monomial product, so the untrusted extraction and the
// proof side's mulProofFull build the SAME canonical monomial atoms.
func (v *ringVocab) polyMul(la, lb linForm) (linForm, bool) {
	return polyMulWith(v.monoMulTerm, la, lb)
}

// polyMulWith is mMul under the monomial-count fuse, parameterized by the
// monomial product (num's free monoMulTerm, or a ringVocab's). Same
// distribution over the same canonical monomial atoms, so the untrusted
// extraction stays in lockstep with the proof side's mulProofFull. ok=false ⇒
// the fuse tripped; both linOf and normalizeProof then fall back to the
// opaque-atom reading of the product, taking the same branch on the same
// inputs.
func polyMulWith(monoMul func(m, n Term) Term, la, lb linForm) (linForm, bool) {
	res := linForm{konst: la.konst.mul(lb.konst)}
	ins := func(c _Integer, atom Term) bool {
		if c.isZero() {
			return true
		}
		res.monos = addMono(res.monos, c, atom)
		return len(res.monos) <= _polyMulMonoCap
	}
	for _, mi := range la.monos { // monomial_la · konst_lb
		if !ins(mi.coeff.mul(lb.konst), mi.atom) {
			return linForm{}, false
		}
	}
	for _, mj := range lb.monos { // konst_la · monomial_lb
		if !ins(la.konst.mul(mj.coeff), mj.atom) {
			return linForm{}, false
		}
	}
	for _, mi := range la.monos { // monomial · monomial
		for _, mj := range lb.monos {
			if !ins(mi.coeff.mul(mj.coeff), monoMul(mi.atom, mj.atom)) {
				return linForm{}, false
			}
		}
	}
	return res, true
}

// sameLinForm reports structural equality of two forms (same konst, same
// sorted monos, atoms α-equal). Used by normalizeProof to assert the model
// product (natPolyMul) and the proof-side product (mulProofFull) agree.
func sameLinForm(a, b linForm) bool {
	if !a.konst.equal(b.konst) || len(a.monos) != len(b.monos) {
		return false
	}
	for i := range a.monos {
		if !a.monos[i].coeff.equal(b.monos[i].coeff) ||
			!a.monos[i].atom.AlphaEquals(b.monos[i].atom) {
			return false
		}
	}
	return true
}

// mpolyOf is the untrusted multivariate normal form of t (always succeeds for
// +/*/atom/numeral terms — no linearity restriction).
func mpolyOf(t Term) linForm {
	if x, ok := asNumeral(t); ok {
		// literalValue (not the bare value): a non-canonical tower must fall
		// through to the atom case in lockstep with normalizeFull, whose literal
		// branch (via asLiteral) declines it — see the asLiteral doc (domain.go).
		if n, ok := literalValue(x); ok {
			return linConst(n)
		}
	}
	if l, r, ok := MatchesPlus(t); ok {
		return linAdd(mpolyOf(l), mpolyOf(r))
	}
	if l, r, ok := MatchesStar(t); ok {
		return mMul(mpolyOf(l), mpolyOf(r))
	}
	if x, ok := MatchesSuc(t); ok { // suc x = x + 1
		return linAdd(mpolyOf(x), linConst(integerOne))
	}
	return linAtom(t)
}

// This file instantiates ext/prop's generic, relation-agnostic AC engine
// (AssocRewrite / ArrangeChain / BinaryOpSortRewrite) for `*` over num. It is
// the ONE place omega reuses that engine directly: monoMerge calls
// MulSortRewrite to canonicalize a monomial's factor product into sorted form.
//
// The ADDITIVE normal form and the cross-term collection that `ring` proper
// needs are deliberately NOT done through this engine. They live in the
// model-then-reprove layer of this file, which computes the canonical
// Σ cᵢ·monomial form as an untrusted numeric model and then re-derives
// ⊢ t = canonical with kernel congruence. That layer
// subsumes additive AC, numeral coefficient folding, and like-term combination
// — none of which prop.BinaryOpSortRewrite can express on its own (it has no
// notion of coefficients or merging) — which is why there is no additive
// AddSortRewrite / ProveEq here: the production `ring` does not rest on the
// generic sorter, except for the monomial-factor sort below.

// noSimplify is a Rewrite that never fires. BinaryOpSortRewrite takes a
// simplifier slot (used to drop op identities while sorting); the monomial-
// factor sort needs no such folding, so it passes this no-op.
func noSimplify(prop.Term) *prop.PropWrapper { return nil }

// ── AC engine instantiated for `*` over num ──────────────────────────────────
var (
	AssocMULRewrite = prop.AssocRewrite(natStar, MatchesStar, associateMUL)
	ArrangeMULChain = prop.ArrangeChain(natStar, MatchesStar, commuteMUL, associateMUL)

	// MulSortRewrite canonicalizes a top-level `*` chain: flatten, sort the
	// factor leaves by Term.Compare, re-nest. Shallow / top-level only. Its sole
	// caller is monoMerge, which sorts a monomial's factors so the
	// proof-side product matches the model's monoMulTerm byte-for-byte.
	MulSortRewrite = prop.BinaryOpSortRewrite(
		MatchesStar, DecomposesStar, ArrangeMULChain, noSimplify, AssocMULRewrite)
)

// buildMulSort instantiates the generic `*`-monomial AC sort for a domain — the
// twin of the num MulSortRewrite above, over the domain's `*` op + matcher +
// MulSym/MulAssoc leaves. Returns the sort rewrite and the paired chain
// decomposer; they must agree so monoMerge's proof matches monoMulTerm's term.
func buildMulSort(starOp Term, matchStar func(Term) (Term, Term, bool),
	commute func(a, b Term) *prop.PropWrapper, assoc func(a, b, c Term) *prop.PropWrapper,
) (sort func(Term) *prop.PropWrapper, decompose func(Term) []Term) {
	decompose = ext.DecomposesBinaryOp(matchStar)
	arrange := prop.ArrangeChain(starOp, matchStar, commute, assoc)
	assocR := prop.AssocRewrite(starOp, matchStar, assoc)
	sort = prop.BinaryOpSortRewrite(matchStar, decompose, arrange, noSimplify, assocR)
	return
}

// Per-domain instances feeding realRing/intRing's mulSort/decomposeStar/mulZeroR
// (real_lemmas.go / int_lemmas.go). The mulZeroR leaf (⊢ x·0 = 0) is DERIVED from commuteMUL + zeroMul
// (ℝ/ℤ have no MulClauses clause leaf, unlike num's free mulZeroR).
var realMulSort, realDecomposeStar = buildMulSort(realStar, realDomain.matchStar, realCommuteMUL, realAssociateMUL)
var intMulSort, intDecomposeStar = buildMulSort(intStar, intDomain.matchStar, intCommuteMUL, intAssociateMUL)

func realMulZeroR(x Term) *prop.PropWrapper {
	return realCommuteMUL(x, realDomain.numeral(_Integer{})).EqTrans(realZeroMul(x)) // x·0 = 0·x = 0
}

func intMulZeroR(x Term) *prop.PropWrapper {
	return intCommuteMUL(x, intDomain.numeral(_Integer{})).EqTrans(intZeroMul(x)) // x·0 = 0·x = 0
}

// The ring normalizer's proof layer: proof-producing normalization of a linear expression to its
// canonical linForm term (linOf is the untrusted model that says WHAT the
// normal form is; here we re-derive `⊢ t = toTerm(linOf(t))` with kernel steps).
//
// Structure mirrors linOf: numerals → Refl, atoms → `a = 1·a + 0`, `+` →
// congruence then mergeProof, scalar `*` → congruence then scaleProof. The merge
// and scale routines are built from small insertion primitives that bubble a
// summand into sorted position (commuteADD/associateADD) and fold coefficients
// (normAdd/normMul + rightDistrib for like-term combination).
//
// The whole composition is DOMAIN-GENERIC: every step reads its term builders,
// leaf lemmas and numeral evaluators off a ringVocab — the proof-bearing twin of
// the untrusted Domain seam (domain.go). natRing is the num instance; realRing
// (real_lemmas.go) is the ℝ instance behind realNormalizeProof. The composition is real kernel work in both — each
// instance is sound exactly when its vocab's leaf closures are.

// ringVocab bundles the proof-leaf vocabulary the ring normalizer composes
// over: the untrusted Domain (term builders + matchers, shared with the model
// side so proof and model stay in lockstep), the raw operator consts (for
// LeftApply congruences), the AC/identity/distribution leaf closures, the
// proof-producing numeral evaluators, and the optional successor bridge.
type ringVocab struct {
	dom            *Domain
	plusOp, starOp Term // raw `+` / `*` consts, for congruence application

	commuteADD    func(a, b Term) *prop.PropWrapper    // ⊢ a+b = b+a
	associateADD  func(a, b, c Term) *prop.PropWrapper // ⊢ (a+b)+c = a+(b+c)
	commuteMUL    func(a, b Term) *prop.PropWrapper    // ⊢ a·b = b·a
	associateMUL  func(a, b, c Term) *prop.PropWrapper // ⊢ (a·b)·c = a·(b·c)
	distributeMUL func(a, b, c Term) *prop.PropWrapper // ⊢ a·(b+c) = a·b + a·c
	rightDistrib  func(a, b, c Term) *prop.PropWrapper // ⊢ (a+b)·c = a·c + b·c

	oneMul   func(a Term) *prop.PropWrapper // ⊢ 1·a = a
	addZeroR func(a Term) *prop.PropWrapper // ⊢ a+0 = a
	zeroMul  func(a Term) *prop.PropWrapper // ⊢ 0·a = 0

	normAdd func(l, r Term) (*prop.PropWrapper, bool) // ⊢ l+r = <literal>
	normMul func(l, r Term) (*prop.PropWrapper, bool) // ⊢ l·r = <literal>

	// sucBridge proves ⊢ suc x = x+1; nil for domains without a successor
	// (real), in lockstep with dom.matchSuc.
	sucBridge func(x Term) *prop.PropWrapper

	// Full multivariate ring extras. mulSort is this domain's
	// monomial-factor AC sort (MulSortRewrite); decomposeStar flattens its
	// `*`-chains (paired with mulSort, must agree); mulZeroR proves ⊢ x·0 = 0. A
	// nil mulSort makes monoMerge Refl-only. natRing binds the num free funcs;
	// the real/int instances are built by buildMulSort and bound where
	// realRing / intRing are declared.
	mulSort       func(Term) *prop.PropWrapper
	decomposeStar func(Term) []Term
	mulZeroR      func(Term) *prop.PropWrapper

	// powUnfold proves `⊢ pow(m, c) = dom.powChain(m, c)` for a literal c
	// within powChainMax — the proof half of the pow basis (domain.go
	// powChainOf). Set in lockstep with dom.matchPow (pow_basis.go wires
	// both); nil for num, whose nat_pow keeps its own unfold shortcuts.
	powUnfold func(m Term, c uint64) *prop.PropWrapper

	// quotientUnfold proves `⊢ u / v = u · inv(v)` — the proof half of the
	// quotient basis (domain.go quotientProduct). Set in lockstep with
	// dom.quotientProduct (quotient_basis.go wires both).
	quotientUnfold func(u, v Term) *prop.PropWrapper
	// inverseUnfold proves `⊢ inv(a·b) = inv(a)·inv(b)` — the proof half of
	// the inverse basis (domain.go inverseProduct). Set in lockstep with
	// dom.matchInverse.
	inverseUnfold func(a, b Term) *prop.PropWrapper

	// castUnfold proves `⊢ t = split` for a cast the cast basis splits
	// (domain.go castSplit) — the proof half, set in lockstep with
	// dom.castSplit (cast_basis.go wires both).
	castUnfold func(t Term) *prop.PropWrapper

	// literalBridge proves `⊢ t = dom.numeral(n)` for a literal t that
	// asLiteral read as n but that is not spelled as the canonical
	// numeral — a structure ring's `zero` and `one` components and a
	// carrier's own literal spelling (structure_ring.go), whose canonical
	// numeral is the additive power of one. nil means every literal IS
	// the canonical numeral (num, real, int), and normalizeProof bridges
	// it by Refl.
	literalBridge func(t Term, n _Integer) *prop.PropWrapper
}

// natRing is the num instance — the original ring_norm behavior, bit-for-bit.
var natRing = &ringVocab{
	dom: natDomain, plusOp: natPlus, starOp: natStar,
	commuteADD: commuteADD, associateADD: associateADD,
	commuteMUL: commuteMUL, associateMUL: associateMUL,
	distributeMUL: distributeMUL, rightDistrib: rightDistrib,
	oneMul: oneMulL, addZeroR: addZeroR, zeroMul: zeroMulNum,
	normAdd: NormNatAdd, normMul: NormNatMul,
	sucBridge:     sucAdd1,
	mulSort:       MulSortRewrite,
	decomposeStar: DecomposesStar,
	mulZeroR:      mulZeroR,
}

// plusLeft is the partial application `(head + ·)`, for rewriting the right
// operand of a sum: w.LeftApply(v.plusLeft(head)) turns ⊢ X = Y into
// ⊢ head + X = head + Y. starLeft is the multiplicative twin.
func (v *ringVocab) plusLeft(head Term) Term { return ext.Apply(v.plusOp, head) }
func (v *ringVocab) starLeft(head Term) Term { return ext.Apply(v.starOp, head) }

// monoTerm builds `c * a` with explicit numeral coeff.
func (v *ringVocab) monoTerm(c _Integer, a Term) Term { return v.dom.star(v.dom.numeral(c), a) }

// monoChainTerm builds `((c₁·a₁ + c₂·a₂) + …)` left-nested; requires ≥1 mono.
func (v *ringVocab) monoChainTerm(monos []monomialL) Term {
	res := v.monoTerm(monos[0].coeff, monos[0].atom)
	for _, m := range monos[1:] {
		res = v.dom.plus(res, v.monoTerm(m.coeff, m.atom))
	}
	return res
}

// ── like-term combination ────────────────────────────────────────────────────

// combineMono: ⊢ c₁·a + c₂·a = (c₁+c₂)·a   (folded coefficient).
func (v *ringVocab) combineMono(c1, c2 _Integer, a Term) *prop.PropWrapper {
	n1, n2 := v.dom.numeral(c1), v.dom.numeral(c2)
	// (c₁+c₂)·a = c₁·a + c₂·a  ⟹ EqSym
	split := v.rightDistrib(n1, n2, a).EqSym() // ⊢ c₁·a + c₂·a = (c₁+c₂)·a
	fold, _ := v.normAdd(n1, n2)               // ⊢ c₁+c₂ = numeral(c₁+c₂)
	// rewrite the (c₁+c₂) subterm in the RHS `(c₁+c₂)·a` to its literal
	return split.EqTrans(fold.LeftApply(v.starOp).RightApply(a))
}

// insertMonoChain inserts (c·a) into a sorted mono chain, combining a like atom:
// ⊢ monoChainTerm(monos) + c·a = monoChainTerm(addMono(monos, c, a)).
func (v *ringVocab) insertMonoChain(monos []monomialL, c _Integer, a Term) *prop.PropWrapper {
	n := len(monos)
	last := monos[n-1]
	cmp := atomCmp(a, last.atom)

	if cmp > 0 { // a sorts after the whole chain: append, no work
		return prop.Refl(v.dom.plus(v.monoChainTerm(monos), v.monoTerm(c, a)))
	}

	if cmp == 0 { // combine with the last monomial
		comb := v.combineMono(last.coeff, c, a) // ⊢ cₙ·a + c·a = (cₙ+c)·a
		if n == 1 {
			return comb
		}
		head := v.monoChainTerm(monos[:n-1])
		// (head + cₙ·a) + c·a → head + (cₙ·a + c·a) → head + (cₙ+c)·a
		assoc := v.associateADD(head, v.monoTerm(last.coeff, last.atom), v.monoTerm(c, a)) // ⊢ (head+mₙ)+ca = head+(mₙ+ca)
		return assoc.EqTrans(comb.LeftApply(v.plusLeft(head)))
	}

	// a sorts before last: bubble c·a left past last, recurse into head.
	head := monos[:n-1]
	mn := v.monoTerm(last.coeff, last.atom)
	ca := v.monoTerm(c, a)
	if n == 1 { // single mono, ca goes before it
		return v.commuteADD(mn, ca) // ⊢ m₁ + ca = ca + m₁  = chain([ca, m₁])
	}
	headT := v.monoChainTerm(head)
	// (headT + mn) + ca → headT + (mn + ca) → headT + (ca + mn) → (headT + ca) + mn
	w := v.associateADD(headT, mn, ca). // ⊢ (headT+mn)+ca = headT+(mn+ca)
						EqTrans(v.commuteADD(mn, ca).LeftApply(v.plusLeft(headT))). // → headT+(ca+mn)
						EqTrans(v.associateADD(headT, ca, mn).EqSym())              // → (headT+ca)+mn
	// recurse: headT + ca = monoChainTerm(insert into head)
	rec := v.insertMonoChain(head, c, a)
	return w.EqTrans(rec.LeftApply(v.plusOp).RightApply(mn))
}

// ── summand insertion into a full linForm (monos + constant) ─────────────────

// insertMonoEq: ⊢ toTerm(lf) + c·a = toTerm(lf ⊕ {c·a}).
func (v *ringVocab) insertMonoEq(lf linForm, c _Integer, a Term) *prop.PropWrapper {
	ca := v.monoTerm(c, a)
	k := v.dom.numeral(lf.konst)
	if len(lf.monos) == 0 {
		// numeral(k) + ca → ca + numeral(k)
		return v.commuteADD(k, ca)
	}
	m := v.monoChainTerm(lf.monos)
	// (m + k) + ca → m + (k + ca) → m + (ca + k) → (m + ca) + k
	w := v.associateADD(m, k, ca).
		EqTrans(v.commuteADD(k, ca).LeftApply(v.plusLeft(m))).
		EqTrans(v.associateADD(m, ca, k).EqSym())
	// insert ca into the mono chain (under `_ + k`)
	ins := v.insertMonoChain(lf.monos, c, a)
	return w.EqTrans(ins.LeftApply(v.plusOp).RightApply(k))
}

// insertConstEq: ⊢ toTerm(lf) + numeral(d) = toTerm(lf{konst+=d}).
func (v *ringVocab) insertConstEq(lf linForm, d _Integer) *prop.PropWrapper {
	k := v.dom.numeral(lf.konst)
	dn := v.dom.numeral(d)
	add, _ := v.normAdd(k, dn) // ⊢ k + d = numeral(konst+d)
	if len(lf.monos) == 0 {
		return add
	}
	m := v.monoChainTerm(lf.monos)
	// (m + k) + d → m + (k + d) → m + numeral(konst+d)
	return v.associateADD(m, k, dn).EqTrans(add.LeftApply(v.plusLeft(m)))
}

// ── merge two linForms ───────────────────────────────────────────────────────

type summand struct {
	isConst bool
	coeff   _Integer
	atom    Term
	konst   _Integer
}

func (v *ringVocab) summandTerm(s summand) Term {
	if s.isConst {
		return v.dom.numeral(s.konst)
	}
	return v.monoTerm(s.coeff, s.atom)
}

func applySummand(lf linForm, s summand) linForm {
	if s.isConst {
		return linForm{konst: lf.konst.add(s.konst), monos: lf.monos}
	}
	return linForm{konst: lf.konst, monos: addMono(lf.monos, s.coeff, s.atom)}
}

func (v *ringVocab) insertSummand(lf linForm, s summand) *prop.PropWrapper {
	if s.isConst {
		return v.insertConstEq(lf, s.konst)
	}
	return v.insertMonoEq(lf, s.coeff, s.atom)
}

// summandsOf lists lb's summands in toTerm order: monomials then the constant.
func summandsOf(lf linForm) []summand {
	out := make([]summand, 0, len(lf.monos)+1)
	for _, m := range lf.monos {
		out = append(out, summand{coeff: m.coeff, atom: m.atom})
	}
	return append(out, summand{isConst: true, konst: lf.konst})
}

// foldSummandTerms left-folds summand terms with `+` (≥1 element).
func (v *ringVocab) foldSummandTerms(ss []summand) Term {
	res := v.summandTerm(ss[0])
	for _, s := range ss[1:] {
		res = v.dom.plus(res, v.summandTerm(s))
	}
	return res
}

// mergeFold: ⊢ toTerm(acc) + foldSummandTerms(ss) = toTerm(acc ⊕ ss).
func (v *ringVocab) mergeFold(acc linForm, ss []summand) *prop.PropWrapper {
	if len(ss) == 1 {
		return v.insertSummand(acc, ss[0])
	}
	last := ss[len(ss)-1]
	init := ss[:len(ss)-1]
	accT := v.dom.buildTerm(acc)
	initT := v.foldSummandTerms(init)
	lastT := v.summandTerm(last)
	// accT + (initT + lastT) → (accT + initT) + lastT
	assoc := v.associateADD(accT, initT, lastT).EqSym()
	rec := v.mergeFold(acc, init) // ⊢ accT + initT = toTerm(acc⊕init)
	step := assoc.EqTrans(rec.LeftApply(v.plusOp).RightApply(lastT))
	ins := v.insertSummand(applyAll(acc, init), last)
	return step.EqTrans(ins)
}

func applyAll(lf linForm, ss []summand) linForm {
	for _, s := range ss {
		lf = applySummand(lf, s)
	}
	return lf
}

// mergeProof: ⊢ toTerm(la) + toTerm(lb) = toTerm(la ⊕ lb).
func (v *ringVocab) mergeProof(la, lb linForm) *prop.PropWrapper {
	return v.mergeFold(la, summandsOf(lb))
}

// ── scalar multiplication ────────────────────────────────────────────────────

// scaleMono: ⊢ c · (cᵢ·a) = (c·cᵢ)·a.
func (v *ringVocab) scaleMono(c, ci _Integer, a Term) *prop.PropWrapper {
	cn, cin := v.dom.numeral(c), v.dom.numeral(ci)
	// (c·cᵢ)·a = c·(cᵢ·a)  ⟹ EqSym
	assoc := v.associateMUL(cn, cin, a).EqSym() // ⊢ c·(cᵢ·a) = (c·cᵢ)·a
	fold, _ := v.normMul(cn, cin)               // ⊢ c·cᵢ = numeral(c·cᵢ)
	return assoc.EqTrans(fold.LeftApply(v.starOp).RightApply(a))
}

// scaleChain: ⊢ c · monoChainTerm(monos) = monoChainTerm(scaled).
func (v *ringVocab) scaleChain(c _Integer, monos []monomialL) *prop.PropWrapper {
	n := len(monos)
	if n == 1 {
		return v.scaleMono(c, monos[0].coeff, monos[0].atom)
	}
	head := monos[:n-1]
	last := monos[n-1]
	headT := v.monoChainTerm(head)
	mn := v.monoTerm(last.coeff, last.atom)
	cn := v.dom.numeral(c)
	// c·(headT + mn) → c·headT + c·mn → scaledHead + (c·cₙ)·aₙ
	dist := v.distributeMUL(cn, headT, mn) // ⊢ c·(headT+mn) = c·headT + c·mn
	return dist.
		EqTrans(v.scaleChain(c, head).LeftApply(v.plusOp).RightApply(v.dom.star(cn, mn))).
		EqTrans(v.scaleMono(c, last.coeff, last.atom).LeftApply(v.plusLeft(v.monoChainTerm(scaleMonos(c, head)))))
}

func scaleMonos(c _Integer, monos []monomialL) []monomialL {
	out := make([]monomialL, len(monos))
	for i, m := range monos {
		out[i] = monomialL{coeff: c.mul(m.coeff), atom: m.atom}
	}
	return out
}

// scaleProof: ⊢ numeral(c) · toTerm(lb) = toTerm(linScale(c, lb)).
func (v *ringVocab) scaleProof(c _Integer, lb linForm) *prop.PropWrapper {
	cn := v.dom.numeral(c)
	if c.isZero() {
		return v.zeroMul(v.dom.buildTerm(lb)) // ⊢ 0·X = 0 = toTerm(linForm{})
	}
	k := v.dom.numeral(lb.konst)
	if len(lb.monos) == 0 {
		mul, _ := v.normMul(cn, k) // ⊢ c·k = numeral(c·konst)
		return mul
	}
	m := v.monoChainTerm(lb.monos)
	dist := v.distributeMUL(cn, m, k) // ⊢ c·(m+k) = c·m + c·k
	mulK, _ := v.normMul(cn, k)       // ⊢ c·k = numeral(c·konst)
	return dist.
		EqTrans(v.scaleChain(c, lb.monos).LeftApply(v.plusOp).RightApply(v.dom.star(cn, k))).
		EqTrans(mulK.LeftApply(v.plusLeft(v.monoChainTerm(scaleMonos(c, lb.monos)))))
}

// ── top-level normalize / prove ──────────────────────────────────────────────

// atomProof: ⊢ a = 1·a + 0   (toTerm of a lone atom).
func (v *ringVocab) atomProof(a Term) *prop.PropWrapper {
	one := v.oneMul(a).EqSym()                            // ⊢ a = 1·a
	zero := v.addZeroR(v.monoTerm(integerOne, a)).EqSym() // ⊢ 1·a = (1·a) + 0
	return one.EqTrans(zero)
}

// normalizeProof returns (linForm, ⊢ t = toTerm(form), ok). ok=false if t is
// nonlinear (under a domain without polyMul) or has a non-literal numeral.
// Branch-for-branch in lockstep with Domain.linOf (domain.go) — the monomial
// expansion of nonlinear products and its fuse fallback included — so the
// proof side's normal forms coincide with the untrusted model's.
func (v *ringVocab) normalizeProof(t Term) (linForm, *prop.PropWrapper, bool) {
	if n, shaped, ok := v.dom.asLiteral(t); shaped {
		if !ok {
			return linForm{}, nil, false
		}
		if v.literalBridge != nil {
			return linConst(n), v.literalBridge(t, n), true // ⊢ t = numeral(n)
		}
		return linConst(n), prop.Refl(t), true // toTerm(linConst n) = numeral(n) = t (canonical literal)
	}
	if l, r, ok := v.dom.matchPlus(t); ok {
		la, wa, o1 := v.normalizeProof(l)
		lb, wb, o2 := v.normalizeProof(r)
		if !o1 || !o2 {
			return linForm{}, nil, false
		}
		cong := wa.LeftApply(v.plusOp).Apply(wb) // ⊢ l+r = toTerm(la)+toTerm(lb)
		return linAdd(la, lb), cong.EqTrans(v.mergeProof(la, lb)), true
	}
	if l, r, ok := v.dom.matchStar(t); ok {
		la, wa, o1 := v.normalizeProof(l)
		lb, wb, o2 := v.normalizeProof(r)
		if !o1 || !o2 {
			return linForm{}, nil, false
		}
		cong := wa.LeftApply(v.starOp).Apply(wb) // ⊢ l*r = toTerm(la)*toTerm(lb)
		switch {
		case la.isConst():
			return linScale(la.konst, lb), cong.EqTrans(v.scaleProof(la.konst, lb)), true
		case lb.isConst():
			// toTerm(la)*numeral(k) → numeral(k)*toTerm(la) → scale
			flip := v.commuteMUL(v.dom.buildTerm(la), v.dom.numeral(lb.konst))
			return linScale(lb.konst, la), cong.EqTrans(flip).EqTrans(v.scaleProof(lb.konst, la)), true
		default:
			if v.dom.polyMul == nil {
				return linForm{}, nil, false // nonlinear (atom·atom) under a domain without a product basis
			}
			// Nonlinear product → the canonical monomial basis, mirroring linOf
			// (domain.go): the checked model multiply supplies the SAME branch
			// decision the untrusted extraction took, and the full ring's
			// multiplication supplies the proof. On a fuse decline both sides
			// fall back to the opaque atom (`l*r = 1·(l*r) + 0` via atomProof),
			// so the discharge replay's normal forms coincide with the model's
			// in either corner. The lockstep assert is drift detection: the two
			// products are computed by different code (natPolyMul vs mulFold)
			// over the same (la, lb), and a divergence would surface later as
			// an opaque kernel mismatch in the certificate replay.
			res, mok := v.dom.polyMul(la, lb)
			if !mok {
				return linAtom(t), v.atomProof(t), true
			}
			resP, mul := v.mulProofFull(la, lb)
			if !sameLinForm(res, resP) {
				panic("omega: polyMul model diverged from mulProofFull on a nonlinear product")
			}
			return resP, cong.EqTrans(mul), true
		}
	}
	if unfold := v.fieldUnfolded(t); unfold != nil {
		// The quotient and inverse bases' proof half, mirroring linOf's
		// branch.
		lf, w, o := v.normalizeProof(prop.Rhs(unfold))
		if !o {
			return linForm{}, nil, false
		}
		return lf, unfold.EqTrans(w), true
	}
	if base, c, ok := v.dom.powLiteral(t); ok {
		// The pow basis's proof half, mirroring linOf's branch (domain.go):
		// the unfold names the chain, and the rest of this function does the
		// SAME work on that chain the model did — so the two agree branch for
		// branch, fuse fallbacks included, without a second polynomial path.
		unfold := v.powUnfold(base, c) // ⊢ pow(base, c) = chain
		if unfold == nil {
			panic("omega: the pow basis accepted an exponent its unfold declined")
		}
		chain := prop.Rhs(unfold)
		if !chain.AlphaEquals(v.dom.powChain(base, c)) {
			panic("omega: pow unfold drifted from the chain the basis reads (" +
				v.dom.name + ")")
		}
		lf, w, o := v.normalizeProof(chain)
		if !o {
			return linForm{}, nil, false
		}
		return lf, unfold.EqTrans(w), true
	}
	if v.dom.matchSuc != nil { // suc x = x + 1, then fold +1 into the constant
		if x, ok := v.dom.matchSuc(t); ok {
			lx, wx, o := v.normalizeProof(x)
			if !o {
				return linForm{}, nil, false
			}
			cong := wx.LeftApply(v.plusOp).RightApply(v.dom.numeral(integerOne)) // ⊢ x+1 = toTerm(lx)+1
			merge := v.insertConstEq(lx, integerOne)                             // ⊢ toTerm(lx)+1 = toTerm(lx⊕1)
			w := v.sucBridge(x).EqTrans(cong).EqTrans(merge)                     // ⊢ suc x = toTerm(lx⊕1)
			return linAdd(lx, linConst(integerOne)), w, true
		}
	}
	if unfold := v.castUnfolded(t); unfold != nil {
		// The cast basis's proof half, mirroring linOf's branch.
		lf, w, o := v.normalizeProof(prop.Rhs(unfold))
		if !o {
			return linForm{}, nil, false
		}
		return lf, unfold.EqTrans(w), true
	}
	if !v.dom.isElem(t) { // a non-carrier term is not a linear atom (linOf parity)
		return linForm{}, nil, false
	}
	return linAtom(t), v.atomProof(t), true // atom
}

// ringProve attempts ⊢ l = r by normalizing both sides to canonical linear form
// and checking the forms coincide. ok=false if a side is nonlinear or the forms
// differ (l ≠ r as linear polynomials).
func (v *ringVocab) ringProve(l, r Term) (*prop.PropWrapper, bool) {
	_, wl, ok1 := v.normalizeProof(l) // ⊢ l = toTerm(linOf(l))
	_, wr, ok2 := v.normalizeProof(r) // ⊢ r = toTerm(linOf(r))
	if !ok1 || !ok2 {
		return nil, false
	}
	if !prop.Rhs(wl).AlphaEquals(prop.Rhs(wr)) {
		return nil, false
	}
	return wl.EqTrans(wr.EqSym()), true // ⊢ l = toTerm = r
}

// RingProve is the num linear `ring` equality prover (the public algorithm
// entry point; see also RingProveFull for the full multivariate semiring).
func RingProve(l, r Term) (*prop.PropWrapper, bool) { return natRing.ringProve(l, r) }

// RealRingProve is the ℝ twin of RingProve: ⊢ l = r over the real linear
// fragment, via realRing (real_lemmas.go). Sound once the RealLemmaBundle ring
// slots are populated; placeholder-backed leaves otherwise.
func RealRingProve(l, r Term) (*prop.PropWrapper, bool) { return realRing.ringProve(l, r) }

// The full multivariate ring's proof layer, domain-generic over the ringVocab seam: proof-producing
// normalization of an arbitrary +/*/atom/numeral expression to its canonical
// multivariate polynomial. Reuses the entire additive machinery (mergeProof/
// scaleProof/insertMonoEq) by keying on monomial product terms; the only new
// code is multiplication, which distributes over both factors and folds each
// pairwise product into a single monomial via monoTimesMono.
//
// natRing binds the num leaves in its mulSort/decomposeStar/mulZeroR fields;
// realRing/intRing instantiate the same composition over their own `*` AC leaves
// (real_lemmas.go / int_lemmas.go), giving RealRingProveFull / IntRingProveFull.
// This layer is positive multivariate only: subtraction and negation, in
// nonlinear position too, are the signed normalizer's (subneg.go mulSigned),
// which reduces a signed product to products this layer expands.

// ── domain-generic monomial leaves ───────────────────────────────────────────

// monoProductOf builds the canonical product term of base atoms (already in the
// desired order), left-nested. Requires ≥1 atom.
func (v *ringVocab) monoProductOf(atoms []Term) Term {
	res := atoms[0]
	for _, a := range atoms[1:] {
		res = v.dom.star(res, a)
	}
	return res
}

// monoMulTerm is the canonical product term of two monomials (the base atoms of
// both, Compare-sorted, left-nested) — the proof side's twin kept in lockstep
// with monoMerge, so the linForm atom matches the proved product byte-for-byte.
func (v *ringVocab) monoMulTerm(m, n Term) Term {
	return v.monoProductOf(sortMerge(v.decomposeStar(m), v.decomposeStar(n)))
}

// monoMerge: ⊢ M · N = <canonical sorted product of M,N's atoms>. The full
// multiplicative AC sort (v.mulSort) flattens M·N and re-nests its base atoms
// Compare-sorted — exactly monoMulTerm. A nil mulSort or nil rewrite means M·N is
// already canonical, so Refl suffices.
func (v *ringVocab) monoMerge(m, n Term) *prop.PropWrapper {
	if v.mulSort != nil {
		if w := v.mulSort(v.dom.star(m, n)); w != nil {
			return w
		}
	}
	return prop.Refl(v.dom.star(m, n))
}

// mulRearrange4: ⊢ (c·M)·(d·N) = (c·d)·(M·N)   (regroup a 4-factor product). A
// fixed associativity/commutativity sequence over the domain's MulAssoc/MulSym:
//
//	(c·M)·(d·N) = c·(M·(d·N)) = c·((M·d)·N) = c·((d·M)·N) = c·(d·(M·N)) = (c·d)·(M·N)
func (v *ringVocab) mulRearrange4(c, m, d, n Term) *prop.PropWrapper {
	return v.associateMUL(c, m, v.dom.star(d, n)). // (c·M)·(d·N) = c·(M·(d·N))
							EqTrans(v.associateMUL(m, d, n).EqSym().LeftApply(v.starLeft(c))).                      // = c·((M·d)·N)
							EqTrans(v.commuteMUL(m, d).LeftApply(v.starOp).RightApply(n).LeftApply(v.starLeft(c))). // = c·((d·M)·N)
							EqTrans(v.associateMUL(d, m, n).LeftApply(v.starLeft(c))).                              // = c·(d·(M·N))
							EqTrans(v.associateMUL(c, d, v.dom.star(m, n)).EqSym())                                 // = (c·d)·(M·N)
}

// ── multiplication of canonical forms ────────────────────────────────────────

// monoTimesConst: ⊢ (c·M) · kb = (kb·c)·M.
func (v *ringVocab) monoTimesConst(c _Integer, m Term, kb _Integer) *prop.PropWrapper {
	cM := v.monoTerm(c, m)
	// (c·M)·kb → kb·(c·M) → (kb·c)·M
	return v.commuteMUL(cM, v.dom.numeral(kb)).EqTrans(v.scaleMono(kb, c, m))
}

// monoTimesMono: ⊢ (c·M) · (d·N) = (c·d)·P, P the canonical product of M,N.
func (v *ringVocab) monoTimesMono(c _Integer, m Term, d _Integer, n Term) *prop.PropWrapper {
	cN, dN := v.dom.numeral(c), v.dom.numeral(d)
	mn := v.dom.star(m, n)
	step1 := v.mulRearrange4(cN, m, dN, n)             // (c·M)(d·N) = (c·d)(M·N)
	foldCD, _ := v.normMul(cN, dN)                     // c·d = numeral(c·d)
	step2 := foldCD.LeftApply(v.starOp).RightApply(mn) // (c·d)(M·N) = (c·d folded)(M·N)
	merge := v.monoMerge(m, n)                         // M·N = P
	step3 := merge.LeftApply(ext.Apply(v.starOp, v.dom.numeral(c.mul(d))))
	return step1.EqTrans(step2).EqTrans(step3)
}

// monoTimesSummandCanon: ⊢ (c·M) · summandTerm(s) = toTerm(result) (a 1-term
// poly, constant 0, so its canonical term is `coeff·mono + 0`).
func (v *ringVocab) monoTimesSummandCanon(c _Integer, m Term, s summand) (linForm, *prop.PropWrapper) {
	if s.isConst {
		if s.konst.isZero() { // (c·M)·0 = 0 — drop, don't emit a 0-coeff monomial
			return linForm{}, v.mulZeroR(v.monoTerm(c, m))
		}
		e := s.konst.mul(c)
		res := linForm{monos: []monomialL{{coeff: e, atom: m}}}
		return res, v.monoTimesConst(c, m, s.konst).EqTrans(v.addZeroR(v.monoTerm(e, m)).EqSym())
	}
	e := c.mul(s.coeff)
	p := v.monoMulTerm(m, s.atom)
	res := linForm{monos: []monomialL{{coeff: e, atom: p}}}
	return res, v.monoTimesMono(c, m, s.coeff, s.atom).EqTrans(v.addZeroR(v.monoTerm(e, p)).EqSym())
}

// monoTimesFold: ⊢ (c·M) · foldSummandTerms(ss) = toTerm(result).
func (v *ringVocab) monoTimesFold(c _Integer, m Term, ss []summand) (linForm, *prop.PropWrapper) {
	if len(ss) == 1 {
		return v.monoTimesSummandCanon(c, m, ss[0])
	}
	cM := v.monoTerm(c, m)
	last, init := ss[len(ss)-1], ss[:len(ss)-1]
	initT, lastT := v.foldSummandTerms(init), v.summandTerm(last)
	ld := v.distributeMUL(cM, initT, lastT) // cM·(initT+lastT) = cM·initT + cM·lastT
	initRes, recI := v.monoTimesFold(c, m, init)
	lastRes, recL := v.monoTimesSummandCanon(c, m, last)
	cong := recI.LeftApply(v.plusOp).Apply(recL)
	return linAdd(initRes, lastRes), ld.EqTrans(cong).EqTrans(v.mergeProof(initRes, lastRes))
}

// summandTimesPoly: ⊢ summandTerm(s) · toTerm(lb) = toTerm(result).
func (v *ringVocab) summandTimesPoly(s summand, lb linForm) (linForm, *prop.PropWrapper) {
	if s.isConst {
		return linScale(s.konst, lb), v.scaleProof(s.konst, lb)
	}
	return v.monoTimesFold(s.coeff, s.atom, summandsOf(lb))
}

// mulFold: ⊢ foldSummandTerms(ss) · toTerm(lb) = toTerm(result).
func (v *ringVocab) mulFold(ss []summand, lb linForm) (linForm, *prop.PropWrapper) {
	if len(ss) == 1 {
		return v.summandTimesPoly(ss[0], lb)
	}
	last, init := ss[len(ss)-1], ss[:len(ss)-1]
	initT, lastT, q := v.foldSummandTerms(init), v.summandTerm(last), v.dom.buildTerm(lb)
	rd := v.rightDistrib(initT, lastT, q) // (initT+lastT)·Q = initT·Q + lastT·Q
	initRes, recI := v.mulFold(init, lb)
	lastRes, recL := v.summandTimesPoly(last, lb)
	cong := recI.LeftApply(v.plusOp).Apply(recL)
	return linAdd(initRes, lastRes), rd.EqTrans(cong).EqTrans(v.mergeProof(initRes, lastRes))
}

// mulProofFull: ⊢ toTerm(la) · toTerm(lb) = toTerm(product canonical form).
func (v *ringVocab) mulProofFull(la, lb linForm) (linForm, *prop.PropWrapper) {
	return v.mulFold(summandsOf(la), lb)
}

// normalizeFull returns (poly, ⊢ t = toTerm(poly)) for any +/*/atom/numeral term
// (no linearity restriction): a nonlinear product folds into a monomial atom.
func (v *ringVocab) normalizeFull(t Term) (linForm, *prop.PropWrapper) {
	if n, shaped, ok := v.dom.asLiteral(t); shaped && ok {
		if v.literalBridge != nil {
			return linConst(n), v.literalBridge(t, n) // ⊢ t = numeral(n)
		}
		return linConst(n), prop.Refl(t) // toTerm(linConst n) = numeral(n) = t (canonical literal)
	}
	if l, r, ok := v.dom.matchPlus(t); ok {
		la, wa := v.normalizeFull(l)
		lb, wb := v.normalizeFull(r)
		cong := wa.LeftApply(v.plusOp).Apply(wb)
		return linAdd(la, lb), cong.EqTrans(v.mergeProof(la, lb))
	}
	if l, r, ok := v.dom.matchStar(t); ok {
		la, wa := v.normalizeFull(l)
		lb, wb := v.normalizeFull(r)
		cong := wa.LeftApply(v.starOp).Apply(wb)
		res, mul := v.mulProofFull(la, lb)
		return res, cong.EqTrans(mul)
	}
	if unfold := v.fieldUnfolded(t); unfold != nil {
		lf, w := v.normalizeFull(prop.Rhs(unfold))
		return lf, unfold.EqTrans(w)
	}
	if base, c, ok := v.dom.powLiteral(t); ok && v.powUnfold != nil {
		// The pow basis's proof half, as normalizeProof reads it: the
		// power at a literal exponent IS its product chain, so a ring
		// identity between a power and a written-out product closes.
		if unfold := v.powUnfold(base, c); unfold != nil {
			lf, w := v.normalizeFull(prop.Rhs(unfold))
			return lf, unfold.EqTrans(w)
		}
	}
	if v.dom.matchSuc != nil { // suc x = x + 1, fold +1 into the constant (num only)
		if x, ok := v.dom.matchSuc(t); ok {
			lx, wx := v.normalizeFull(x)
			cong := wx.LeftApply(v.plusOp).RightApply(v.dom.numeral(integerOne)) // ⊢ x+1 = toTerm(lx)+1
			merge := v.insertConstEq(lx, integerOne)                             // ⊢ toTerm(lx)+1 = toTerm(lx⊕1)
			return linAdd(lx, linConst(integerOne)), v.sucBridge(x).EqTrans(cong).EqTrans(merge)
		}
	}
	if unfold := v.castUnfolded(t); unfold != nil {
		lf, w := v.normalizeFull(prop.Rhs(unfold))
		return lf, unfold.EqTrans(w)
	}
	return linAtom(t), v.atomProof(t)
}

// castUnfolded is `⊢ t = split` for a cast the basis splits, nil for any
// other term. The lockstep assert is drift detection: the split the proof
// names must be the split the model read.
func (v *ringVocab) castUnfolded(t Term) *prop.PropWrapper {
	if v.dom.castSplit == nil {
		return nil
	}
	split, ok := v.dom.castSplit(t)
	if !ok {
		return nil
	}
	unfold := v.castUnfold(t)
	if unfold == nil {
		panic("omega: the cast basis read a cast its unfold declined")
	}
	if !prop.Lhs(unfold).AlphaEquals(t) || !prop.Rhs(unfold).AlphaEquals(split) {
		panic("omega: cast unfold drifted from the split the basis reads (" + v.dom.name + ")")
	}
	return unfold
}

// quotientUnfolded is `⊢ t = u · inv(v)` for a quotient the basis reads, nil
// for any other term. The lockstep assert is drift detection: the product
// the proof names must be the product the model read.
func (v *ringVocab) quotientUnfolded(t Term) *prop.PropWrapper {
	if v.dom.quotientProduct == nil {
		return nil
	}
	product, ok := v.dom.quotientProduct(t)
	if !ok {
		return nil
	}
	d, n, ok := v.dom.matchQuotient(t)
	if !ok {
		panic("omega: the quotient basis read a quotient the domain's quotient matcher does not")
	}
	unfold := v.quotientUnfold(d, n)
	if unfold == nil {
		panic("omega: the quotient basis read a quotient its unfold declined")
	}
	if !prop.Rhs(unfold).AlphaEquals(product) {
		panic("omega: quotient unfold drifted from the product the basis reads")
	}
	return unfold
}

// inverseUnfolded is `⊢ t = inv(a)·inv(b)` for an inverse of a product the
// basis reads, nil for any other term, under the same drift detection.
func (v *ringVocab) inverseUnfolded(t Term) *prop.PropWrapper {
	product, ok := v.dom.inverseProduct(t)
	if !ok {
		return nil
	}
	x, _ := v.dom.matchInverse(t)
	a, b, _ := v.dom.matchStar(x)
	unfold := v.inverseUnfold(a, b)
	if unfold == nil {
		panic("omega: the inverse basis read an inverse its unfold declined")
	}
	if !prop.Lhs(unfold).AlphaEquals(t) || !prop.Rhs(unfold).AlphaEquals(product) {
		panic("omega: inverse unfold drifted from the product the basis reads")
	}
	return unfold
}

// fieldUnfolded is the proof half of Domain.fieldProduct: `⊢ t = product`
// for a quotient or an inverse of a product, nil for any other term.
func (v *ringVocab) fieldUnfolded(t Term) *prop.PropWrapper {
	if unfold := v.quotientUnfolded(t); unfold != nil {
		return unfold
	}
	return v.inverseUnfolded(t)
}

// ringProveFull attempts ⊢ l = r over the full commutative semiring (multivariate
// polynomials over the domain) by normalizing both sides and comparing canonical
// forms. ok=false if the canonical forms differ (l ≠ r as polynomials).
func (v *ringVocab) ringProveFull(l, r Term) (*prop.PropWrapper, bool) {
	_, wl := v.normalizeFull(l)
	_, wr := v.normalizeFull(r)
	if !prop.Rhs(wl).AlphaEquals(prop.Rhs(wr)) {
		return nil, false
	}
	return wl.EqTrans(wr.EqSym()), true
}

// RingProveFull (num), RealRingProveFull (ℝ), IntRingProveFull (ℤ): the full
// multivariate `ring` equality closers — ⊢ e₁ = e₂ over each domain's semiring,
// incl. nonlinear `a*b = b*a`, `(a+b)² = a²+2ab+b²`. The ⊥ side is linarith's job.
func RingProveFull(l, r Term) (*prop.PropWrapper, bool)     { return natRing.ringProveFull(l, r) }
func RealRingProveFull(l, r Term) (*prop.PropWrapper, bool) { return realRing.ringProveFull(l, r) }
func IntRingProveFull(l, r Term) (*prop.PropWrapper, bool)  { return intRing.ringProveFull(l, r) }

// The policy-gated twins. Each is identical to its ungated original when the
// caller's lexical policy allows that domain's bundle, and declines (nil,false)
// when it does not. The words channels delegate their ring residuals through
// these under the CALLER's ArithPolicy — a word-goal lowering must not become a
// laundering path for a nat/int/real bundle the current target's policy forbids
// (the ungated originals stay for legacy and low-level callers with no scope).
func RingProveFullWithPolicy(l, r Term, policy ArithPolicy) (*prop.PropWrapper, bool) {
	if !policy.Nat {
		return nil, false
	}
	return RingProveFull(l, r)
}

func RealRingProveFullWithPolicy(l, r Term, policy ArithPolicy) (*prop.PropWrapper, bool) {
	if !policy.Real {
		return nil, false
	}
	return RealRingProveFull(l, r)
}

func IntRingProveFullWithPolicy(l, r Term, policy ArithPolicy) (*prop.PropWrapper, bool) {
	if !policy.Int {
		return nil, false
	}
	return IntRingProveFull(l, r)
}
