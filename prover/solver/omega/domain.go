// Package omega is XuGo's arithmetic decision/normalization layer (ring /
// linarith / omega) for num, real, and int — every result bottoms out in a real
// kernel Thm. See README.md for the architecture.
//
// File-naming convention: a nat_/real_/int_ prefix marks that domain's
// instantiation; a bare filename (domain.go, ring.go, linarith.go, subneg.go,
// engine.go, bundle.go) is the domain-generic machinery shared by all three behind
// the Domain / ringVocab / subnegVocab seams. The .go and _test.go files mirror
// one-to-one.
package omega

import (
	"iter"
	"slices"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// Domain bundles the per-number-type term vocabulary that the UNTRUSTED model
// layer needs: linear-form extraction (linOf) and canonical-term construction
// (buildTerm). It carries NO theorems — those live in the lemma bundles.
//
// The point of the seam: linOf / the linForm algebra / buildTerm
// are type-agnostic — only the operator vocabulary (+, *, the comparisons, the
// numeral literal, the suc successor, the element-type guard) differs between
// number types. Threading a *Domain instead of hard-referencing the `nat*`
// consts lets the same untrusted model serve them all; each twin is then a
// single Domain value plus its own (theorem-bearing) proof layer.
//
// The instances are natDomain, realDomain and intDomain (below), and the
// Domain a structure ring builds at a comm_ring / field fact
// (structure_ring.go). realDomain and intDomain mirror natDomain with
// `matchSuc: nil`, the `&n` literal and their own element-type guard.
type Domain struct {
	name string

	// Term builders.
	plus    func(a, b Term) Term  // a + b
	star    func(a, b Term) Term  // a * b
	numeral func(n _Integer) Term // the canonical literal for n ≥ 0

	// Matchers (a ⋈ b → leaves). matchSuc is nil for domains without a suc
	// successor (e.g. real): linOf then skips the suc → +1 folding.
	matchPlus func(Term) (Term, Term, bool)
	matchStar func(Term) (Term, Term, bool)
	matchSuc  func(Term) (Term, bool)

	// Total subtraction / negation vocabulary — the signed-normalization seam
	// (subneg.go). nil for `num` (whose `-` is truncated monus, handled
	// separately in nat_sub.go) and set for the TOTAL `-`/`--` of real/int. linOf /
	// the positive ring stay sub/neg-free; only the signed normalizer reads these.
	sub      func(a, b Term) Term // a − b  (total)
	neg      func(a Term) Term    // − a
	matchSub func(Term) (Term, Term, bool)
	matchNeg func(Term) (Term, bool)

	// Comparison matchers (`a ⋈ b` → (a, b, true)) for the constraint
	// extraction. Equality is handled by ext.MatchesEQ (type-agnostic) plus
	// the isElem guard, so no matchEq field is needed.
	matchLt func(Term) (Term, Term, bool)
	matchLe func(Term) (Term, Term, bool)
	matchGt func(Term) (Term, Term, bool)
	matchGe func(Term) (Term, Term, bool)

	// asLiteral recognizes a numeral literal. shaped=t is numeral-shaped at all
	// (so linOf commits — never falls through to the atom case); ok=its value was
	// read AND the tower is canonical. The split matters for real `&x` shapes
	// that are numeral-headed but non-literal and for NON-CANONICAL towers
	// (e.g. bit0(_0)): those decline (shaped, !ok) because
	// the proof-producing normalizers (ring.go normalizeProof/normalizeFull)
	// return Refl(t) for a literal, which is only a valid `⊢ t = toTerm(linConst n)`
	// bridge when t IS the canonical Numeral(n). A non-canonical tower accepted
	// here diverges the untrusted linForm from the kernel proof and trips the
	// EqTrans assert during certificate replay (nat_linarith.go) — the
	// polynomial_function-session panic pinned by TestNormalizeProofDeclinesNonCanonicalNumeral.
	asLiteral func(t Term) (n _Integer, shaped, ok bool)

	// isElem reports whether t is an element of this domain's carrier type (so a
	// non-arith subterm — e.g. a bool `⇔` — is not taken as a linear atom).
	isElem func(Term) bool

	// moveAcrossHyp positivizes a comparison HYPOTHESIS carrying total sub/neg:
	// it returns `⊢ h ⇔ h'` (h' the sub/neg-free two-sided form) or nil. Set for
	// real/int (the signed-normalization layer, subneg.go), nil for num.
	// hypConstraints uses it so a hyp like `a − b ≤ c` reaches linarith as the
	// positive `a ≤ c + b`, with the iff carried as the constraint's HypProof.
	moveAcrossHyp func(Term) *prop.PropWrapper

	// unnegateHyp normalizes a NEGATED comparison hypothesis to its positive
	// equivalent: `⊢ ¬(a<b) ⇔ (b≤a)` / `⊢ ¬(a≤b) ⇔ (b<a)` (NotLessThan / NotLessEq), or
	// nil when h is not one. Set for all three domains — each has the two
	// lemmas — and consumed by hypConstraints exactly like moveAcrossHyp: the
	// carried `{h} ⊢ positive` keeps the refutation's hyps ⊆ the goal's.
	//
	// Without it the parser simply DROPS a negated comparison, so the same fact
	// decides or not depending on how it was spelled: `b ≤ a ⊢ …` closes while
	// the equivalent `¬(a < b) ⊢ …` declines. Nothing downstream is negation-
	// aware — linOf sees only the positive form — so this is the one place the
	// spelling can be reconciled.
	unnegateHyp func(Term) *prop.PropWrapper

	// liftHyp reads a hypothesis of the NUM carrier in this domain through
	// its cast: `{h} ⊢ &a ⋈ &b` for h = `a ⋈ b` over num (the OfNum*
	// bridges), and for a strict h its integrality as well,
	// `{h} ⊢ &a + &1 ≤ &b` (a < b over num is a + 1 ≤ b); nil for any other
	// h. Set for real/int, nil for num. hypConstraints then holds the num
	// layer's facts as rows over the images — a divisor `&((2k+1)·(2k+2))`
	// is bounded by what the context says of (2k+1)·(2k+2), and
	// `b < a + 1 ⊢ &b ≤ &a` is one row away — so a comparison of images
	// needs no decision of its own under the context.
	liftHyp func(Term) []*prop.PropWrapper

	// polyMul, when set, is the domain's CHECKED monomial-basis product: linOf
	// reads a nonlinear product (atom·atom, e.g. m·suc(n)) as the polynomial it
	// denotes — distributed over canonical MONOMIAL atoms (Compare-sorted
	// product terms, the full ring's own normal form; ring.go mMul/monoMulTerm)
	// — rather than rejecting the term as nonlinear. This is what lets the
	// Farkas layer combine polynomial facts: `2·A = n·suc(n)` and
	// `suc(n)·suc(suc(n))` meet in the shared basis {A, n·n, n} instead of as
	// two unrelated opaque unknowns. Sound for `num` because every term is ≥ 0
	// (the nonnegativity row buildAll injects per atom holds for a monomial
	// too). ok=false is a resource fuse (a pathological monomial count) and
	// makes linOf fall back to the pre-basis reading — the whole product as
	// ONE opaque atom, still sound.
	// Over `real` the reading is a pure change of basis — the ℝ refutation
	// injects no nonnegativity rows, so a monomial is just one more free
	// unknown and the certificate is the same Farkas combination read over
	// ℝ[atoms]; the same over `int` (a product of integers is an integer).
	// realRing.polyMul / intRing.polyMul are wired in inits (real_lemmas.go,
	// int_lemmas.go). A Domain without one declines a nonlinear product —
	// the pre-basis reading, kept so a domain under construction is still a
	// legal value.
	polyMul func(la, lb linForm) (linForm, bool)

	// matchPow recognizes this domain's exponentiation `pow(base, n)` with a
	// num exponent. Set for real and int, whose unfold (real_ops.go
	// realPowUnfold, int.go intPowUnfold) proves `pow(m, c) = powChain(m, c)`
	// for every literal c within powChainMax — the shape contract linOf and
	// normalizeProof both lean on. NOT set for num: `expUnfold` shortcuts c=1
	// and c=2 to their own shapes (`m`, `m·m`), so nat_pow has no single chain to
	// share, and a nat_pow term stays the opaque atom it has always been.
	matchPow func(Term) (Term, Term, bool)

	// quotientProduct reads a quotient by a SYMBOLIC divisor as the product
	// it denotes, `u / v ↦ u · inv(v)` — the quotient basis (quotient_basis.go).
	// nil for a domain without a field division (num, int); ok=false for a
	// literal divisor, which the literal-quotient pass reads (real_quotient.go).
	quotientProduct func(Term) (Term, bool)
	// matchQuotient recognizes the domain's quotient `u / v` → (u, v), in
	// lockstep with quotientProduct (set together; the proof half,
	// ringVocab.quotientUnfold, is instantiated at the pair it reads).
	matchQuotient func(Term) (Term, Term, bool)
	// matchInverse recognizes the domain's inverse `inv(x)` → x and inverse
	// builds it; nil for a domain without one (num, int). With them the
	// inverse of a product is read as the product of the inverses
	// (inverseProduct — the inverse basis, quotient_basis.go); the proof
	// half is ringVocab.inverseUnfold.
	matchInverse func(Term) (Term, bool)
	inverse      func(Term) Term

	// castSplit reads a cast of a num sum, product or successor as the sum
	// or product of the casts it denotes — `&(a + b) ↦ &a + &b`,
	// `&(a * b) ↦ &a * &b`, `&(suc a) ↦ &a + &1` — the cast basis
	// (cast_basis.go). One level: the readers recurse on what it returns.
	// nil for num; ok=false for a cast of anything else — a variable, a
	// truncated difference, a power — which stays the one unknown it was,
	// and where the bridge the split is proved by is not bound.
	castSplit func(Term) (Term, bool)

	// constraints memoizes hypConstraintsOf per hypothesis term — see there.
	constraints constraintMemo
}

// constraintMemo is the per-domain memo of hypConstraintsOf, and the memo
// of the rows a monomial has whatever the context: a signed normalizer's
// expansion row (subnegVocab.expansionRow) and a square's sign
// (realSquareSign, intSquareSign), each the one row or its decline.
// Extraction is
// a pure function of the hypothesis term and the installed lemma bundle
// (the HypProof it carries is derived from that bundle's NotLessThan / NotLessEq and
// move-across theorems), so the entries are keyed by the term and every
// bundle setter resets the memo (resetConstraintMemos). The hit test is
// EXACT equality on the stored term, not α-equality: an entry's HypProof
// names the term it was built from as its hypothesis, and a refutation's
// hyps must be the goal's own terms (the IsStronger contract), so an
// α-variant with different bound names inside a conjunct is a miss. The
// AlphaKey is only the bucket. Bounded: past constraintMemoCap entries the
// whole map is dropped — a decision's working set is one goal's hyps plus
// the split pins, far below the cap, so the bound never bites mid-decision.
type constraintMemo struct {
	mu      sync.Mutex
	entries map[core.TermKey]constraintMemoEntry
}

type constraintMemoEntry struct {
	hyp Term
	cs  []LinConstraint
}

const constraintMemoCap = 4096

func (m *constraintMemo) lookup(h Term) ([]LinConstraint, bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	e, ok := m.entries[h.AlphaKey()]
	if !ok || !e.hyp.Equals(h) {
		return nil, false
	}
	return e.cs, true
}

func (m *constraintMemo) store(h Term, cs []LinConstraint) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if len(m.entries) >= constraintMemoCap {
		m.entries = nil
	}
	if m.entries == nil {
		m.entries = make(map[core.TermKey]constraintMemoEntry)
	}
	m.entries[h.AlphaKey()] = constraintMemoEntry{hyp: h, cs: cs}
}

func (m *constraintMemo) reset() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.entries = nil
}

// resetConstraintMemos drops every domain's extraction memo, the expansion
// rows of the two signed normalizers (subnegVocab.expansionRow), the
// squares' signs, and the memos of one arith step (ReleaseStepMemos).
// Called by the three
// lemma-bundle setters: the memoized HypProofs are built from the
// bundle in force at extraction time, so a bundle swap (the serve install,
// a test's InstallRealBundle / SetRealLemmaBundle(nil) pair) must not be
// answered from entries derived under the previous one.
func resetConstraintMemos() {
	natDomain.constraints.reset()
	realDomain.constraints.reset()
	intDomain.constraints.reset()
	realSubneg.expansions.reset()
	intSubneg.expansions.reset()
	realSquareSigns.reset()
	intSquareSigns.reset()
	ReleaseStepMemos()
}

// ReleaseStepMemos drops the memos whose entries serve one arith step: the
// real linear prover's answers and the real decide chain's
// (real_linarith.go, real.go), the sign rows' ring equations
// (real_sign_rows.go) and the signs their monomials fold to
// (monomial_sign_memo.go), and the num linear prover's and decide chain's
// answers (nat.go). What they hold is proofs — kernel derivations, a
// hundred megabytes of them after one step on a thirteen-hypothesis ε-δ
// context, where nothing bounded them — and the questions they answer
// repeat inside a step and hardly across steps, so the step's owner
// releases them when it is done (tactic.arithRewriteTactic) and a
// long-lived process keeps nothing between steps. A step running beside
// another loses its entries to the other's release; it asks again.
func ReleaseStepMemos() {
	realSignBridgeMemo.reset()
	realMonomialSigns.reset()
	intMonomialSigns.reset()
	realLinMemo.reset()
	realDecMemo.reset()
	natLinMemo.reset()
	natDecMemo.reset()
	modulusZeroMemo.reset()
	realCancelMemo.reset()
	structureMoveMemo.reset()
}

// natDomain is the num vocabulary: the nat operator consts and the raw
// BIT-tree numeral evaluator. The helpers it names live in this file and in
// nat_norm.go.
var natDomain = &Domain{
	name:      "num",
	plus:      plus,
	star:      star,
	numeral:   numeralOf,
	matchPlus: MatchesPlus,
	matchStar: MatchesStar,
	matchSuc:  MatchesSuc,
	matchPow:  MatchesExp,
	matchLt:   MatchesLt,
	matchLe:   MatchesLe,
	matchGt:   MatchesGt,
	matchGe:   MatchesGe,
	asLiteral: func(t Term) (_Integer, bool, bool) {
		x, shaped := asNumeral(t)
		if !shaped {
			return _Integer{}, false, false
		}
		n, ok := literalValue(x)
		return n, true, ok
	},
	isElem:  isNat,
	polyMul: natPolyMul,
}

// unnegateVocab is the per-domain supply the negated-comparison normalizer
// needs: the two comparison matchers and the two NotLessThan / NotLessEq leaves. Kept
// as a value rather than four Domain fields because the three instantiations
// differ ONLY in these four functions.
type unnegateVocab struct {
	matchLt     func(Term) (Term, Term, bool)
	matchLe     func(Term) (Term, Term, bool)
	notLessThan func(m, n Term) *prop.PropWrapper // ⊢ ¬(m<n) ⇔ (n≤m)
	notLessEq   func(m, n Term) *prop.PropWrapper // ⊢ ¬(m≤n) ⇔ (n<m)
}

// wireUnnegate installs the un-negation hook, taking the comparison matchers
// from the domain itself so they can never drift from the ones parseHypConstraint
// uses. Only the two NotLessThan / NotLessEq leaves are domain-supplied.
func (d *Domain) wireUnnegate(notLessThan, notLessEq func(m, n Term) *prop.PropWrapper) {
	d.unnegateHyp = unnegateVocab{
		matchLt: d.matchLt, matchLe: d.matchLe, notLessThan: notLessThan, notLessEq: notLessEq,
	}.unnegate
}

// unnegate builds a Domain.unnegateHyp hook from the vocabulary: it returns
// `⊢ h ⇔ positive` for a negated comparison h, else nil.
//
// It deliberately handles ONLY `¬(<)` and `¬(≤)`. A negated EQUALITY `¬(a=b)`
// is a disjunction, not a comparison — it is the case-split engine's business
// (hypSplittable already ingests it), and turning it into a single linear row
// here would be unsound.
func (v unnegateVocab) unnegate(h Term) *prop.PropWrapper {
	inner := prop.MatchesNOT(h)
	if inner == nil {
		return nil
	}
	if a, b, ok := v.matchLt(inner); ok {
		return v.notLessThan(a, b) // ⊢ ¬(a<b) ⇔ (b≤a)
	}
	if a, b, ok := v.matchLe(inner); ok {
		return v.notLessEq(a, b) // ⊢ ¬(a≤b) ⇔ (b<a)
	}
	return nil
}

// literalValue reads a BIT-tower for asLiteral: value + the canonicality gate
// the proof-producing normalizers rely on (see the asLiteral field doc). A
// well-formed but non-canonical tower (bit0(_0)) declines.
func literalValue(x Term) (_Integer, bool) {
	v, ok := ext.NumeralValue(x)
	if !ok || !ext.IsCanonicalNumeral(x) {
		return _Integer{}, false
	}
	return integerOwning(v), true
}

// atomsOf is the atoms the constraint set's linear forms are written over,
// each once, in the order the sides first hold them: a constraint's left
// side before its right, the constraints in theirs. A side with no linear
// form holds none. The sign rows read their monomials and their powers off
// one such pass.
func (d *Domain) atomsOf(cs []LinConstraint) []Term {
	var atoms []Term
	add := func(t Term) {
		lf, ok := d.linOf(t)
		if !ok {
			return
		}
		for _, mono := range lf.monos {
			if !slices.ContainsFunc(atoms, mono.atom.AlphaEquals) {
				atoms = append(atoms, mono.atom)
			}
		}
	}
	for _, c := range cs {
		add(c.Lhs)
		add(c.Rhs)
	}
	return atoms
}

// linOf computes the linear form of t over this domain (untrusted; the ring
// normalizer's linear fragment). ok=false if t is nonlinear (a product of two non-constant subforms)
// or contains a numeral-shaped but non-literal subterm. The only
// domain-specific inputs are the matchers/literal/guard.
func (d *Domain) linOf(t Term) (linForm, bool) {
	if n, shaped, ok := d.asLiteral(t); shaped {
		if ok {
			return linConst(n), true
		}
		return linForm{}, false
	}
	if l, r, ok := d.matchPlus(t); ok {
		la, ok1 := d.linOf(l)
		lb, ok2 := d.linOf(r)
		if !ok1 || !ok2 {
			return linForm{}, false
		}
		return linAdd(la, lb), true
	}
	if l, r, ok := d.matchStar(t); ok {
		la, ok1 := d.linOf(l)
		lb, ok2 := d.linOf(r)
		if !ok1 || !ok2 {
			return linForm{}, false
		}
		switch {
		case la.isConst():
			return linScale(la.konst, lb), true
		case lb.isConst():
			return linScale(lb.konst, la), true
		default:
			if d.polyMul == nil {
				return linForm{}, false // nonlinear (atom·atom) under a domain without a product basis
			}
			// Nonlinear product (atom·atom, e.g. m·suc(n)): expand it over the
			// canonical monomial basis — the polynomial the product denotes,
			// with each monomial (a Compare-sorted product term) as one linear
			// atom. `m·p` and `p·m` are now the SAME unknown, and `(n+1)·(n+2)`
			// meets `n·n + 3·n + 2` in the same basis, so hypothesis equations
			// with polynomial content combine under Farkas. Sound over num —
			// every num term is ≥ 0, so the nonnegativity row buildAll injects
			// per atom (0 ≤ m·p via ZeroLessEq) holds for a monomial too — and over
			// real and int, where no such row exists and a monomial is simply
			// one more free unknown; normalizeProof's matching expansion
			// (ring.go) replays the certificate. On a fuse decline (polyMul: the
			// monomial-count cap) fall back to the pre-basis reading — the
			// whole product as ONE opaque atom — keeping that corner exactly as
			// strong as before; normalizeProof mirrors the same branch.
			if res, ok := d.polyMul(la, lb); ok {
				return res, true
			}
			return linAtom(t), true
		}
	}
	if d.matchSuc != nil { // suc x = x + 1 (successor → coefficient)
		if x, ok := d.matchSuc(t); ok {
			lx, ok := d.linOf(x)
			if !ok {
				return linForm{}, false
			}
			return linAdd(lx, linConst(integerOne)), true
		}
	}
	if product, ok := d.fieldProduct(t); ok {
		// `u / v` denotes u·inv(v), and reading it as that product puts
		// the quotient in the monomial basis a written-out `u * inv(v)`
		// lands in; `inv(a·b)` denotes inv(a)·inv(b), which puts a divisor
		// that is a product in the basis its factors' inverses land in.
		// The term is untouched — the field handlers go on meeting the
		// `/` the author wrote. normalizeProof (ring.go) recurses on the
		// SAME product behind the law's equation.
		return d.linOf(product)
	}
	if chain, ok := d.powChainOf(t); ok {
		// `pow(base, c)` denotes base·(base·(…·1)), and reading it as that
		// chain puts the power in the SAME monomial basis a written-out
		// product lands in: `real_pow(x, 2)` and `x * x` become one unknown
		// rather than two. The term itself is untouched — only its linear
		// form expands — so the pow handlers (sign, base monotonicity, the
		// of_num bridge) keep meeting the spelling the author wrote.
		// normalizeProof (ring.go) recurses on the SAME chain behind the
		// unfold's equation, so every branch below — the monomial expansion
		// and its fuse fallback alike — is taken identically on both sides.
		return d.linOf(chain)
	}
	if d.castSplit != nil {
		if split, ok := d.castSplit(t); ok {
			// `&(a + b)` denotes &a + &b, and reading it so puts a cast the
			// author wrote in the basis a lifted num hypothesis is already
			// written over (liftHyp pushes its casts to the leaves): `&m`
			// and `&(m + 1)` are then one unknown and a constant apart, not
			// two unknowns. The term is untouched. normalizeProof (ring.go)
			// recurses on the SAME split behind the bridge's equation.
			return d.linOf(split)
		}
	}
	if !d.isElem(t) { // a non-carrier term (e.g. a bool `⇔`) is not a linear atom
		return linForm{}, false
	}
	return linAtom(t), true // atom
}

// powChainMax bounds the exponent the basis expands, matching the unfold's own
// cap (expUnfoldMax): past it the unfold declines, and a model that expanded
// where the proof could not would leave the replay without a normal form.
const powChainMax = expUnfoldMax

// powChain is the product chain `base·(base·(…·numeral(1)))` with c factors —
// the shape each domain's unfold proves `pow(base, c)` equal to. It is the
// lockstep contract between the untrusted extraction and the proof: ring.go's
// normalizeProof asserts the unfold's right-hand side against it.
func (d *Domain) powChain(base Term, c uint64) Term {
	chain := d.numeral(integerOne)
	for i := uint64(0); i < c; i++ {
		chain = d.star(base, chain)
	}
	return chain
}

// powChainOf recognizes a power with a literal exponent within the cap and
// returns the chain it denotes. ok=false for any other term, for a symbolic or
// non-canonical exponent, and for a domain with no exponentiation.
func (d *Domain) powChainOf(t Term) (Term, bool) {
	base, c, ok := d.powLiteral(t)
	if !ok {
		return nil, false
	}
	return d.powChain(base, c), true
}

// carriesSubNeg reports whether t mentions this domain's total subtraction or
// negation anywhere.
//
// linOf reads neither: positivizing them is the signed normalizer's job
// (subneg.go), and that runs on HYPOTHESES only, through moveAcrossHyp. So a
// term whose sub survives into a product is read TWO ways in one refutation —
// expanded where the signed normalizer reaches it, unexpanded where it does
// not. That asymmetry predates the pow basis (a written-out `(x−w)·(x−w)`
// has it too), and the basis must not widen it: a power whose base carries a
// sub stays the opaque atom it was, so both sides go on agreeing about it.
// real_sqrt.ApproachFromAbove is the corpus witness — its `real_pow(x−w, 2)`
// is linked to the expansion by a hypothesis that the signed normalizer turns
// into a tautology the moment the power expands too.
func (d *Domain) carriesSubNeg(t Term) bool {
	if d.matchNeg != nil {
		if _, ok := d.matchNeg(t); ok {
			return true
		}
	}
	if d.matchSub != nil {
		if _, _, ok := d.matchSub(t); ok {
			return true
		}
	}
	if l, r, ok := d.matchPlus(t); ok {
		return d.carriesSubNeg(l) || d.carriesSubNeg(r)
	}
	if l, r, ok := d.matchStar(t); ok {
		return d.carriesSubNeg(l) || d.carriesSubNeg(r)
	}
	if d.matchPow != nil {
		if base, _, ok := d.matchPow(t); ok {
			return d.carriesSubNeg(base)
		}
	}
	if product, ok := d.fieldProduct(t); ok {
		return d.carriesSubNeg(product)
	}
	return false
}

// inverseProduct reads the inverse of a product as the product of the
// inverses it denotes, `inv(a·b) ↦ inv(a)·inv(b)`; ok=false for any other
// term, and in a domain without an inverse.
func (d *Domain) inverseProduct(t Term) (Term, bool) {
	if d.matchInverse == nil {
		return nil, false
	}
	x, ok := d.matchInverse(t)
	if !ok {
		return nil, false
	}
	a, b, ok := d.matchStar(x)
	if !ok {
		return nil, false
	}
	return d.star(d.inverse(a), d.inverse(b)), true
}

// fieldProduct reads a field term as the product it denotes: a quotient by
// a symbolic divisor (quotientProduct) or the inverse of a product
// (inverseProduct). The readers that must agree — linOf, the ring's two
// normalizers, the signed normalizer — all ask here.
func (d *Domain) fieldProduct(t Term) (Term, bool) {
	if d.quotientProduct != nil {
		if product, ok := d.quotientProduct(t); ok {
			return product, true
		}
	}
	return d.inverseProduct(t)
}

// powLiteral peels a power with a literal exponent within the cap, declining a
// base that carries sub/neg (carriesSubNeg).
func (d *Domain) powLiteral(t Term) (Term, uint64, bool) {
	if d.matchPow == nil {
		return nil, 0, false
	}
	base, exponent, ok := d.matchPow(t)
	if !ok {
		return nil, 0, false
	}
	if d.carriesSubNeg(base) {
		return nil, 0, false
	}
	c, ok := BitsToUint(exponent)
	if !ok || !ext.IsCanonicalNumeral(exponent) || c > powChainMax {
		return nil, 0, false
	}
	return base, c, true
}

// buildTerm renders a linForm as this domain's canonical term: monomials as
// `coeff * atom` (coeff always explicit), sorted, then the constant literal
// appended as the final summand (always present), left-nested. Equal forms ⇒
// syntactically equal terms (the decision invariant).
func (d *Domain) buildTerm(lf linForm) Term {
	summands := make([]Term, 0, len(lf.monos)+1)
	for _, m := range lf.monos {
		summands = append(summands, d.star(d.numeral(m.coeff), m.atom))
	}
	summands = append(summands, d.numeral(lf.konst))
	res := summands[0]
	for _, s := range summands[1:] {
		res = d.plus(res, s)
	}
	return res
}

// ── Comparison-constraint extraction (untrusted) ────────────────────────────
//
// These turn comparison hypotheses into the domain-agnostic LinConstraint the
// refutation core consumes. They carry no theorems — recognition + linearity
// gating only — so they work for `num` and `real` identically; only the
// comparison matchers and the element/linearity guards differ per Domain.

// isLinear reports whether t is a linear form over this domain (the gate linOf
// provides) — since the monomial basis, a polynomial over products included.
func (d *Domain) isLinear(t Term) bool {
	_, ok := d.linOf(t)
	return ok
}

// genuinelyLinear is the STRICT linearity test the enumeration gates need: t
// is linear AND its form carries no product atom. It diverges from isLinear
// exactly on products — `x·x` is isLinear (one monomial unknown) but NOT
// genuinelyLinear — so `x·x ≤ 4` is still recognized as worth enumerating
// rather than handed to a linarith that cannot relate the unknown `x·x` to
// x's bounds. (linOf never atomizes `c·a` to a product atom — that scales to
// a monomial with atom `a` — so any `*`-headed atom here is a product.)
func (d *Domain) genuinelyLinear(t Term) bool {
	lf, ok := d.linOf(t)
	if !ok {
		return false
	}
	return !slices.ContainsFunc(lf.monos, func(m monomialL) bool {
		_, _, isProduct := d.matchStar(m.atom)
		return isProduct
	})
}

// linConstraint builds a `l Op r` constraint only when both sides are linear
// over this domain, so a nonlinear (or wrong-typed) comparison is dropped rather
// than poisoning the whole refutation (extractRow would otherwise fail the set).
// The isElem guard also rejects a bool `⇔` that ext.MatchesEQ would otherwise
// accept as an "equality".
func (d *Domain) linConstraint(l, r Term, op relOp) (LinConstraint, bool) {
	if !d.isElem(l) || !d.isElem(r) {
		return LinConstraint{}, false
	}
	if !d.isLinear(l) || !d.isLinear(r) {
		return LinConstraint{}, false
	}
	return LinConstraint{Lhs: l, Rhs: r, Op: op}, true
}

// originConstraint builds a canonical `lhs Op rhs` constraint whose carried
// hypothesis is the original (swapped `>`/`≥`) term, dropping it if a side is
// nonlinear.
func (d *Domain) originConstraint(lhs, rhs Term, op relOp, hyp Term) (LinConstraint, bool) {
	c, ok := d.linConstraint(lhs, rhs, op)
	if !ok {
		return LinConstraint{}, false
	}
	c.Hyp = hyp
	return c, true
}

// parseHypConstraint reads one hypothesis as a linear constraint over this
// domain. `<`/`≤`/`=` map directly (the canonical term equals the original hyp).
// `>`/`≥` are canonicalized to the swapped `<`/`≤` but keep the original term in
// Hyp, so the refutation carries `a>b` (not the rebuilt `b<a`) and the final
// proof's hyps stay a subset of the goal's (the IsStronger contract). Returns
// ok=false for non-comparison or nonlinear hyps.
func (d *Domain) parseHypConstraint(h Term) (LinConstraint, bool) {
	if a, b, ok := d.matchLt(h); ok {
		return d.linConstraint(a, b, opLT)
	}
	if a, b, ok := d.matchLe(h); ok {
		return d.linConstraint(a, b, opLE)
	}
	if a, b, ok := ext.MatchesEQ(h); ok {
		return d.linConstraint(a, b, opEQ)
	}
	// a>b ⟝ canonical b<a; a≥b ⟝ canonical b≤a; original term kept in Hyp.
	if a, b, ok := d.matchGt(h); ok {
		return d.originConstraint(b, a, opLT, h)
	}
	if a, b, ok := d.matchGe(h); ok {
		return d.originConstraint(b, a, opLE, h)
	}
	return LinConstraint{}, false
}

// hypConstraints extracts the linear comparison constraints from the
// hypotheses, dropping any hyp that is not a linear `<`/`≤`/`=`/`>`/`≥` over
// this domain. A CONJUNCTION hyp `p ∧ q` (which parseHypConstraint alone drops —
// it ingests only top-level comparison atoms) is flattened into its comparison
// conjuncts: splitConjuncts projects each leaf out of `prop.Assume(h)`, so every
// derived constraint carries the projection `{h} ⊢ conjunct` as its HypProof and
// the refutation's hyps stay a subset of the goal's (the IsStronger contract).
//
// Per hypothesis the extraction is memoized (hypConstraintsOf): it depends
// on the one hyp alone — never on which other hyps are in the set — and the
// proof-producing part (the move-across and un-negation iffs, each a ring
// normalization with a kernel derivation behind it) is the whole cost of a
// linarith call on a wide context. The forward prover runs once per atom
// per direction per case-split level, each run re-reading the same hyps and
// pins, and without the memo the extraction was 86% of RealLinProve on a
// thirteen-hypothesis ε-δ context — the inspect / apply arith stall the
// engine's TestInspect_ArithProbeOnWideRealContext reproduces.
func (d *Domain) hypConstraints(hyps iter.Seq[Term]) []LinConstraint {
	var cs []LinConstraint
	for h := range hyps {
		cs = append(cs, d.hypConstraintsOf(h)...)
	}
	return cs
}

// hypConstraintsOf is the memoized per-hypothesis extraction — the
// constraints (zero or more) hypothesis h contributes. The returned slice is
// shared with the memo and must not be mutated; hypConstraints copies its
// elements into the fresh per-call list.
func (d *Domain) hypConstraintsOf(h Term) []LinConstraint {
	if cs, ok := d.constraints.lookup(h); ok {
		return cs
	}
	cs := d.extractHypConstraints(h)
	d.constraints.store(h, cs)
	return cs
}

// extractHypConstraints is the uncached per-hypothesis extraction behind
// hypConstraintsOf.
func (d *Domain) extractHypConstraints(h Term) []LinConstraint {
	var cs []LinConstraint
	if _, _, ok := prop.MatchesAND(h); ok {
		for _, part := range splitConjuncts(prop.Assume(h)) { // each: {h} ⊢ conjunct
			if c, ok := d.parseHypConstraint(part.Conclusion()); ok {
				c.HypProof = part
				cs = append(cs, c)
			}
		}
		return cs
	}
	// A num hypothesis is read through its cast (liftHyp, real/int): its
	// image comparison is the row, carried with `{h} ⊢ image`.
	if d.liftHyp != nil {
		if lifted := d.liftHyp(h); len(lifted) > 0 {
			for _, w := range lifted {
				if c, ok := d.parseHypConstraint(w.Conclusion()); ok {
					c.Hyp = nil
					c.HypProof = w // {h} ⊢ &a ⋈ &b
					cs = append(cs, c)
				}
			}
			return cs
		}
	}
	// A sub/neg comparison hyp must be positivized via the relation-level
	// move-across FIRST: linOf does not reject `a − b` — it ATOMIZES it (a
	// carrier-typed non-operator subterm becomes an opaque atom), so
	// parseHypConstraint would otherwise succeed with a useless `[a−b] ⋈ c`
	// constraint whose atom shares nothing with the goal. The hook self-gates
	// on hasSubNeg (nil iff no sub/neg), so a positive hyp falls straight
	// through to parseHypConstraint. The carried `{h} ⊢ positiveAtom` keeps the
	// refutation's hyps ⊆ the goal's (the IsStronger contract).
	if d.moveAcrossHyp != nil {
		if iff := d.moveAcrossHyp(h); iff != nil {
			if c, ok := d.parseHypConstraint(prop.Rhs(iff)); ok {
				c.Hyp = nil
				c.HypProof = iff.EqMP(prop.Assume(h)) // {h} ⊢ positiveAtom
				cs = append(cs, c)
			}
			return cs // h was a sub/neg comparison — handled (or dropped if nonlinear)
		}
	}
	// A NEGATED comparison hyp is un-negated the same way: rewrite it to
	// the positive equivalent and carry `{h} ⊢ positive`. parseHypConstraint
	// ingests only positive atoms, so without this the hyp is silently
	// dropped and the goal's provability depends on how the fact was
	// spelled. The positive form may itself still carry sub/neg, so it is
	// run back through moveAcrossHyp before parsing.
	if d.unnegateHyp != nil {
		if iff := d.unnegateHyp(h); iff != nil {
			positive := prop.Rhs(iff)
			proof := iff.EqMP(prop.Assume(h)) // {h} ⊢ positive
			if d.moveAcrossHyp != nil {
				if moved := d.moveAcrossHyp(positive); moved != nil {
					positive = prop.Rhs(moved)
					proof = moved.EqMP(proof)
				}
			}
			if c, ok := d.parseHypConstraint(positive); ok {
				c.Hyp = nil
				c.HypProof = proof
				cs = append(cs, c)
			}
			return cs // h was a negated comparison — handled (or dropped if nonlinear)
		}
	}
	if c, ok := d.parseHypConstraint(h); ok {
		cs = append(cs, c)
	}
	return cs
}

// Real-domain vocabulary for the untrusted model. This is the
// theorem-free half of the ℝ twin: it makes linOf / buildTerm
// work over `real` terms. The proof-producing leaves (RealLemmaBundle and the
// real normalizeProof/replay) are separate and read the theorems over ℝ the
// bundle binds — nothing here needs them.
//
// Differences from natDomain, all expressed purely through the Domain fields:
//   - matchSuc is nil — ℝ has no suc successor, so linOf skips the suc→+1 fold.
//   - the literal is `&n` = real_of_num(<bit-tree n>); asLiteral peels the
//     real_of_num head and reads the num bit-tree underneath (literalValue),
//     and numeral builds the same shape. This is the
//     real_of_num bridge the real norm_num (realNormNat*) runs on proofs, at
//     the term level.
//   - isElem guards the `real` carrier type.

var (
	realPlus  = dsl.RealPlusMeta.Term()
	realStar  = dsl.RealStarMeta.Term()
	realSub   = dsl.RealSubMeta.Term()
	realNeg   = dsl.RealNegMeta.Term()
	realOfNum = dsl.RealOfNumMeta.Term()
	realLt    = dsl.RealLtMeta.Term()
	realLe    = dsl.RealLeMeta.Term()
	realGt    = dsl.RealGtMeta.Term()
	realGe    = dsl.RealGeMeta.Term()
	realAbs   = dsl.RealAbsMeta.Term()
	realMax   = dsl.RealMaxMeta.Term()
	realMin   = dsl.RealMinMeta.Term()
	realSgn   = dsl.RealSgnMeta.Term()
	realPow   = dsl.RealPowMeta.Term()
	realDiv   = dsl.RealDivMeta.Term()
	realInv   = dsl.RealInvMeta.Term()
)

// realSubT / realNegT build real `a − b` / `−a`. MatchesRealNeg recognizes a
// real_neg application (the unary twin of ext.MatchesBinaryOp).
func realSubT(a, b Term) Term { return ext.Apply(realSub, a, b) }
func realNegT(a Term) Term    { return ext.Apply(realNeg, a) }

// MatchesRealNeg reports whether t is `real_neg(x)` and returns (x, true).
func MatchesRealNeg(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(realNeg) {
		return a.Arg(), true
	}
	return nil, false
}

// realPlusT / realStarT build real `a + b` / `a * b`; realLeT/realLtT/realGtT/
// realGeT build the real comparisons. (eqT = core.Eq is type-generic, so the
// real proof layer reuses it directly.)
func realPlusT(a, b Term) Term { return ext.Apply(realPlus, a, b) }
func realStarT(a, b Term) Term { return ext.Apply(realStar, a, b) }
func realLeT(a, b Term) Term   { return ext.Apply(realLe, a, b) }
func realLtT(a, b Term) Term   { return ext.Apply(realLt, a, b) }
func realGtT(a, b Term) Term   { return ext.Apply(realGt, a, b) }
func realGeT(a, b Term) Term   { return ext.Apply(realGe, a, b) }

// realAbsT builds `real_abs(x)`; realMaxT / realMinT build `real_max(a,b)` /
// `real_min(a,b)`; realSgnT builds `real_sgn(x)`. The matchers feed the real case
// split (real_ops.go) — the real twins of intAbsT / intMaxT / intMinT / intSgnT.
func realAbsT(x Term) Term    { return ext.Apply(realAbs, x) }
func realMaxT(a, b Term) Term { return ext.Apply(realMax, a, b) }
func realMinT(a, b Term) Term { return ext.Apply(realMin, a, b) }
func realSgnT(x Term) Term    { return ext.Apply(realSgn, x) }

// MatchesRealAbs reports whether t is `real_abs(x)` and returns (x, true).
func MatchesRealAbs(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(realAbs) {
		return a.Arg(), true
	}
	return nil, false
}

// MatchesRealMax / MatchesRealMin recognize `real_max(a,b)` / `real_min(a,b)`.
func MatchesRealMax(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(realMax)(t) }
func MatchesRealMin(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(realMin)(t) }

// MatchesRealSgn reports whether t is `real_sgn(x)` and returns (x, true).
func MatchesRealSgn(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(realSgn) {
		return a.Arg(), true
	}
	return nil, false
}

// realPowT builds `real_pow(m,n)` (the exponent n is num); MatchesRealPow is its
// matcher. The real twin of intPowT / MatchesIntPow.
func realPowT(m, n Term) Term { return ext.Apply(realPow, m, n) }

// MatchesRealPow reports whether t is `real_pow(m,n)` and returns (m, n, true).
func MatchesRealPow(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(realPow)(t) }

// realDivT / realInvT build `real_div(a,b)` (= a/b) / `real_inv(a)` (= 1/a); the
// matchers feed the field layer (real_ops.go).
func realDivT(a, b Term) Term { return ext.Apply(realDiv, a, b) }
func realInvT(a Term) Term    { return ext.Apply(realInv, a) }

// MatchesRealDiv reports whether t is `real_div(a,b)` and returns (a, b, true).
func MatchesRealDiv(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(realDiv)(t) }

// MatchesRealInv reports whether t is `real_inv(a)` and returns (a, true).
func MatchesRealInv(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(realInv) {
		return a.Arg(), true
	}
	return nil, false
}

// realOfNumT builds `real_of_num(x)` for an arbitrary num term x — the `&x`
// coercion the norm_num bridge threads its congruences through.
func realOfNumT(x Term) Term { return ext.Apply(realOfNum, x) }

// realLit builds the canonical real literal `&n` = real_of_num(<bit-tree n>),
// and realLitOf the same literal at a value of any size.
func realLit(n uint64) Term     { return realOfNumT(Numeral(n)) }
func realLitOf(n _Integer) Term { return realOfNumT(numeralOf(n)) }

// realMonoTerm / realMonoChainTerm build the real monomial `c·atom` and the
// chain `c₁·a₁ + … + cₖ·aₖ` (the variable part P, no constant), mirroring
// monoTerm / monoChainTerm over the real builders.
func realMonoTerm(c _Integer, atom Term) Term { return realStarT(realLitOf(c), atom) }

func realMonoChainTerm(monos []monomialL) Term {
	res := realMonoTerm(monos[0].coeff, monos[0].atom)
	for _, m := range monos[1:] {
		res = realPlusT(res, realMonoTerm(m.coeff, m.atom))
	}
	return res
}

// MatchesRealOfNum reports whether t is `real_of_num(x)` and returns (x, true).
func MatchesRealOfNum(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(realOfNum) {
		return a.Arg(), true
	}
	return nil, false
}

// isRealTerm reports whether t has type real.
func isRealTerm(t Term) bool { return t.Type().Equals(dsl.RealType) }

// realDomain is the ℝ instance of the untrusted-model Domain. Only the operator
// vocabulary differs from natDomain; linOf/buildTerm (domain.go) are shared.
// polyMul is wired to realRing's in an init (real_lemmas.go) — realRing
// names this value, so the literal cannot name realRing back.
var realDomain = &Domain{
	name:      "real",
	plus:      realPlusT,
	star:      realStarT,
	numeral:   realLitOf,
	matchPlus: ext.MatchesBinaryOp(realPlus),
	matchStar: ext.MatchesBinaryOp(realStar),
	matchSuc:  nil, // no suc on ℝ
	sub:       realSubT,
	neg:       realNegT,
	matchSub:  ext.MatchesBinaryOp(realSub),
	matchNeg:  MatchesRealNeg,
	matchLt:   ext.MatchesBinaryOp(realLt),
	matchLe:   ext.MatchesBinaryOp(realLe),
	matchGt:   ext.MatchesBinaryOp(realGt),
	matchGe:   ext.MatchesBinaryOp(realGe),
	matchPow:  MatchesRealPow,
	quotientProduct: func(t Term) (Term, bool) {
		u, v, ok := MatchesRealDiv(t)
		if !ok || isRealLit(v) {
			return nil, false
		}
		return realStarT(u, realInvT(v)), true
	},
	matchQuotient: MatchesRealDiv,
	matchInverse:  MatchesRealInv,
	inverse:       realInvT,
	asLiteral: func(t Term) (_Integer, bool, bool) {
		x, ok := MatchesRealOfNum(t)
		if !ok {
			return _Integer{}, false, false
		}
		// `shaped` asks whether t is a numeral LITERAL, which is a question
		// about the coerced argument and not about the coercion head. A `&n`
		// whose argument is not numeral-shaped at all — the `&N` of an
		// archimedean bound, say — is an opaque real term, so it falls
		// through to the atom case and becomes an unknown like any other,
		// where a sign row can price it (`&n` is nonnegative because n is,
		// real_sign_rows.go). Answering `shaped` on the head alone made linOf
		// DECLINE such a term, which dropped the whole constraint carrying it.
		// A numeral-shaped but MALFORMED argument (a non-canonical tower)
		// still declines as the field contract requires: there the Refl bridge
		// the normalizers build for a literal would be invalid.
		inner, numeralShaped := asNumeral(x)
		if !numeralShaped {
			return _Integer{}, false, false
		}
		n, exact := literalValue(inner)
		return n, true, exact
	},
	isElem: isRealTerm,
}

// Integer-domain vocabulary for the untrusted model — the theorem-free half of
// the ℤ twin, exactly parallel to the ℝ twin (domain.go realDomain). It makes
// linOf / buildTerm work over `int` terms; the proof-producing leaves (an
// IntLemmaBundle and an int normalizeProof/replay) are separate and gated on the
// int foundation theorems (placeholder-backed until serve.InstallIntBundle).
//
// `int` is built as a subtype of `real` (int_le x y ⇔ real_of_int x ≤
// real_of_int y, and the whole ℤ order suite is the ℝ suite lifted
// through it). omega does NOT reduce through real_of_int: it instantiates
// the same untrusted model (linOf / FM / refute, all shared) on int vocabulary
// and replays with int-native order lemmas. So the int layer is self-contained —
// no real_of_int bridge, no dependence on the real layer being installed.
//
// Like realDomain (and unlike natDomain), int variables are NOT non-negative, so
// the refutation injects no `0 ≤ x` rows and scaling carries a `&0 ≤ c` side
// condition discharged on the concrete coefficient. matchSuc is nil — ℤ has no
// suc successor. polyMul is wired to intRing's in an init (int_lemmas.go) —
// intRing names this value, so the literal cannot name intRing back.

var (
	intPlus  = dsl.IntPlusMeta.Term()
	intStar  = dsl.IntStarMeta.Term()
	intSub   = dsl.IntSubMeta.Term()
	intNeg   = dsl.IntNegMeta.Term()
	intAbs   = dsl.IntAbsMeta.Term()
	intMax   = dsl.IntMaxMeta.Term()
	intMin   = dsl.IntMinMeta.Term()
	intSgn   = dsl.IntSgnMeta.Term()
	intPow   = dsl.IntPowMeta.Term()
	intOfNum = dsl.IntOfNumMeta.Term()
	intLt    = dsl.IntLtMeta.Term()
	intLe    = dsl.IntLeMeta.Term()
	intGt    = dsl.IntGtMeta.Term()
	intGe    = dsl.IntGeMeta.Term()
	intDvd   = dsl.IntDividesMeta.Term()
	intDiv   = dsl.IntDivMeta.Term()
	intRem   = dsl.IntRemMeta.Term()
)

// intPlusT / intStarT build int `a + b` / `a * b`; intLeT/intLtT/intGtT/intGeT
// build the int comparisons. (eqT = core.Eq is type-generic, reused directly.)
func intPlusT(a, b Term) Term { return ext.Apply(intPlus, a, b) }
func intStarT(a, b Term) Term { return ext.Apply(intStar, a, b) }
func intLeT(a, b Term) Term   { return ext.Apply(intLe, a, b) }
func intLtT(a, b Term) Term   { return ext.Apply(intLt, a, b) }
func intGtT(a, b Term) Term   { return ext.Apply(intGt, a, b) }
func intGeT(a, b Term) Term   { return ext.Apply(intGe, a, b) }

// intDividesT builds `int_divides d e` (d ∣ e). MatchesIntDivides is its matcher.
func intDividesT(d, e Term) Term { return ext.Apply(intDvd, d, e) }

// MatchesIntDivides reports whether t is `int_divides(d, e)` and returns (d,e,true).
func MatchesIntDivides(t Term) (d, e Term, ok bool) {
	a, isApp := t.AsAppliedTerm()
	if !isApp {
		return nil, nil, false
	}
	inner, isApp2 := a.Fun().AsAppliedTerm()
	if !isApp2 || !inner.Fun().Equals(intDvd) {
		return nil, nil, false
	}
	return inner.Arg(), a.Arg(), true
}

// intDivT / intRemT build int Euclidean `int_div(m,n)` / `int_rem(m,n)`; MatchesIntDiv /
// MatchesIntRem are their matchers, feeding the int_div/int_rem bounded-atom enrichment
// (nat_divmod.go).
func intDivT(m, n Term) Term                  { return ext.Apply(intDiv, m, n) }
func intRemT(m, n Term) Term                  { return ext.Apply(intRem, m, n) }
func MatchesIntDiv(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(intDiv)(t) }
func MatchesIntRem(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(intRem)(t) }

// intSubT / intNegT build int `a − b` / `−a` (TOTAL subtraction/negation, the
// signed-normalization vocabulary). MatchesIntNeg is the unary matcher.
func intSubT(a, b Term) Term { return ext.Apply(intSub, a, b) }
func intNegT(a Term) Term    { return ext.Apply(intNeg, a) }

// MatchesIntNeg reports whether t is `int_neg(x)` and returns (x, true).
func MatchesIntNeg(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(intNeg) {
		return a.Arg(), true
	}
	return nil, false
}

// intAbsT builds `int_abs(x)`; MatchesIntAbs is the unary matcher feeding the
// int case split (int_split.go).
func intAbsT(x Term) Term { return ext.Apply(intAbs, x) }

// MatchesIntAbs reports whether t is `int_abs(x)` and returns (x, true).
func MatchesIntAbs(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(intAbs) {
		return a.Arg(), true
	}
	return nil, false
}

// intMaxT / intMinT build `int_max(a,b)` / `int_min(a,b)`; intSgnT builds
// `int_sgn(x)`; intPowT builds `int_pow(m,n)`. The matchers feed the int case
// split (max/min/sgn) and the literal-exponent unfold (pow).
func intMaxT(a, b Term) Term { return ext.Apply(intMax, a, b) }
func intMinT(a, b Term) Term { return ext.Apply(intMin, a, b) }
func intSgnT(x Term) Term    { return ext.Apply(intSgn, x) }
func intPowT(m, n Term) Term { return ext.Apply(intPow, m, n) }

// MatchesIntMax / MatchesIntMin recognize `int_max(a,b)` / `int_min(a,b)`.
func MatchesIntMax(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(intMax)(t) }
func MatchesIntMin(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(intMin)(t) }

// MatchesIntSgn reports whether t is `int_sgn(x)` and returns (x, true).
func MatchesIntSgn(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(intSgn) {
		return a.Arg(), true
	}
	return nil, false
}

// MatchesIntPow reports whether t is `int_pow(m,n)` and returns (m, n, true).
func MatchesIntPow(t Term) (Term, Term, bool) { return ext.MatchesBinaryOp(intPow)(t) }

// intOfNumT builds `int_of_num(x)` for an arbitrary num term x — the `&x`
// coercion the norm_num bridge threads its congruences through.
func intOfNumT(x Term) Term { return ext.Apply(intOfNum, x) }

// intLit builds the canonical int literal `&n` = int_of_num(<bit-tree n>),
// and intLitOf the same literal at a value of any size.
func intLit(n uint64) Term     { return intOfNumT(Numeral(n)) }
func intLitOf(n _Integer) Term { return intOfNumT(numeralOf(n)) }

// intMonoTerm / intMonoChainTerm build the int monomial `c·atom` and the chain
// `c₁·a₁ + … + cₖ·aₖ` (the variable part P, no constant), mirroring the real
// builders over the int operators.
func intMonoTerm(c _Integer, atom Term) Term { return intStarT(intLitOf(c), atom) }

func intMonoChainTerm(monos []monomialL) Term {
	res := intMonoTerm(monos[0].coeff, monos[0].atom)
	for _, m := range monos[1:] {
		res = intPlusT(res, intMonoTerm(m.coeff, m.atom))
	}
	return res
}

// MatchesIntOfNum reports whether t is `int_of_num(x)` and returns (x, true).
func MatchesIntOfNum(t Term) (Term, bool) {
	if a, ok := t.AsAppliedTerm(); ok && a.Fun().Equals(intOfNum) {
		return a.Arg(), true
	}
	return nil, false
}

// isIntTerm reports whether t has type int.
func isIntTerm(t Term) bool { return t.Type().Equals(dsl.IntType) }

// intDomain is the ℤ instance of the untrusted-model Domain. Only the operator
// vocabulary differs from realDomain; linOf/buildTerm (domain.go) are shared.
var intDomain = &Domain{
	name:      "int",
	plus:      intPlusT,
	star:      intStarT,
	numeral:   intLitOf,
	matchPlus: ext.MatchesBinaryOp(intPlus),
	matchStar: ext.MatchesBinaryOp(intStar),
	matchSuc:  nil, // no suc on ℤ
	sub:       intSubT,
	neg:       intNegT,
	matchSub:  ext.MatchesBinaryOp(intSub),
	matchNeg:  MatchesIntNeg,
	matchLt:   ext.MatchesBinaryOp(intLt),
	matchLe:   ext.MatchesBinaryOp(intLe),
	matchGt:   ext.MatchesBinaryOp(intGt),
	matchGe:   ext.MatchesBinaryOp(intGe),
	matchPow:  MatchesIntPow,
	asLiteral: func(t Term) (_Integer, bool, bool) {
		x, ok := MatchesIntOfNum(t)
		if !ok {
			return _Integer{}, false, false
		}
		// The real twin's reasoning, verbatim: `shaped` is a question about
		// the coerced ARGUMENT, so an `&n` that coerces a non-numeral is an
		// opaque int term and becomes an atom, where declining would drop
		// the whole constraint carrying it. A malformed numeral still
		// declines.
		inner, numeralShaped := asNumeral(x)
		if !numeralShaped {
			return _Integer{}, false, false
		}
		n, exact := literalValue(inner)
		return n, true, exact
	},
	isElem: isIntTerm,
}

// Local aliases to keep signatures readable.
type (
	Term      = core.Term
	ConstTerm = core.ConstTerm
)

// Arith operator consts, reused from the text DSL so their AlphaKey matches the
// registry's consts of the same name. meta.Term() is non-nil
// because these are all monomorphic.
var (
	natPlus  = dsl.NatPlusMeta.Term()
	natStar  = dsl.NatStarMeta.Term()
	natMinus = dsl.NatMinusMeta.Term()
	natMax   = dsl.NatMaxMeta.Term()
	natMin   = dsl.NatMinMeta.Term()
	natPre   = dsl.NatPreMeta.Term()
	natExp   = dsl.NatExpMeta.Term()
	natFact  = dsl.NatFactMeta.Term()
	natSuc   = dsl.SUCMeta.Term()
	natDiv   = dsl.NatDivMeta.Term()
	natMod   = dsl.NatModMeta.Term()
	natEven  = dsl.NatEvenMeta.Term()
	natOdd   = dsl.NatOddMeta.Term()
	natDist  = dsl.NatDistMeta.Term()
)

// Binary-op matchers: one line each over the generic factory ext.MatchesBinaryOp.
var (
	// MatchesPlus reports whether t is `a + b` and returns (a, b, true).
	MatchesPlus = ext.MatchesBinaryOp(natPlus)
	// MatchesStar reports whether t is `a * b`.
	MatchesStar = ext.MatchesBinaryOp(natStar)
	// MatchesMinus reports whether t is `a - b` (truncated num subtraction /
	// monus). It is the syntactic gate for the subtraction-cancellation leaf and
	// the monus case-split (nat_sub.go); `-` is otherwise an opaque atom to linOf.
	MatchesMinus = ext.MatchesBinaryOp(natMinus)
	// MatchesMax / MatchesMin gate the nat_max/nat_min case-split clients (nat_sub.go); both
	// are opaque atoms to linOf, decided by an LE-guard case split.
	MatchesMax = ext.MatchesBinaryOp(natMax)
	MatchesMin = ext.MatchesBinaryOp(natMin)
	// MatchesDiv / MatchesMod gate the nat_div/nat_mod layer (nat_divmod.go) — opaque atoms
	// to linOf, enriched with bounded-atom hyps (DivLessEq, ModLessEq, …) before linarith.
	MatchesDiv = ext.MatchesBinaryOp(natDiv)
	MatchesMod = ext.MatchesBinaryOp(natMod)
	// MatchesExp gates the nat_pow layer (nat_exp.go) — `nat_pow(m, c)` with literal c unfolds
	// to a `m·m·…·m` product chain feeding RingProveFull.
	MatchesExp = ext.MatchesBinaryOp(natExp)

	// DecomposesPlus flattens an `a + b + c + …` chain to its leaves.
	DecomposesPlus = ext.DecomposesBinaryOp(MatchesPlus)
	// DecomposesStar flattens an `a * b * c * …` chain to its leaves.
	DecomposesStar = ext.DecomposesBinaryOp(MatchesStar)
	// DecomposesAnd flattens a `p ∧ q ∧ r ∧ …` chain to its leaf conjuncts — the
	// term-level dual of nat_norm.go's proof-level splitConjuncts.
	DecomposesAnd = ext.DecomposesAND

	// Comparison matchers — `a ⋈ b` → (a, b, true). natLt/… are defined in
	// nat_norm.go; the consts share AlphaKey with the registry's, so
	// these match session goals/hyps built from the registry comparison consts.
	MatchesLt = ext.MatchesBinaryOp(natLt)
	MatchesLe = ext.MatchesBinaryOp(natLe)
	MatchesGt = ext.MatchesBinaryOp(natGt)
	MatchesGe = ext.MatchesBinaryOp(natGe)
)

// Unary-op matchers: one line each over the generic factory (the unary analogue
// of the binary matchers above). Each reports whether t is `c(x)` → (x, true).
var (
	// MatchesSuc — suc(x); gates the suc→x+1 linearization.
	MatchesSuc = ext.MatchesUnaryOp(natSuc)
	// MatchesPre — predecessor(x); gates the predecessor→(x−1) bridge (nat_sub.go).
	MatchesPre = ext.MatchesUnaryOp(natPre)
	// MatchesFact — factorial(x); gates the literal-factorial evaluator (nat.go).
	MatchesFact = ext.MatchesUnaryOp(natFact)
	// MatchesEven / MatchesOdd — nat_even(x) / nat_odd(x); gate the parity → nat_mod-2 bridge
	// (nat_sub.go).
	MatchesEven = ext.MatchesUnaryOp(natEven)
	MatchesOdd  = ext.MatchesUnaryOp(natOdd)
)

// MatchesDist reports whether t is `nat_dist(,(m, n))` (the num distance, applied to a
// LITERAL pair) and returns (m, n, true). The syntactic gate for the dist→monus
// bridge (nat_sub.go). The argument must be the comma constructor applied to two
// nums — dist's type only pins the arg to prod(num,num), so any two-level
// application chain of that type (e.g. a free `pair : num→num→prod` variable
// applied to (m, n)) reaches here and must be REJECTED: distBridge instantiates
// Dist at (m, n), an equation about `nat_dist(,(m,n))`, and rewriting a
// non-comma application with it would produce a witness whose LHS is not the
// goal's conclusion (caught downstream by makeSubGoalsAt's IsStronger assert as
// a "Should not happen." panic). Non-literal-pair dist stays opaque instead.
func MatchesDist(t Term) (Term, Term, bool) {
	app, ok := t.AsAppliedTerm()
	if !ok || !app.Fun().Equals(natDist) {
		return nil, nil, false
	}
	inner, ok := app.Arg().AsAppliedTerm() // (, m) n
	if !ok {
		return nil, nil, false
	}
	cm, ok := inner.Fun().AsAppliedTerm() // (, m)
	if !ok {
		return nil, nil, false
	}
	if c, isConst := cm.Fun().AsConst(); !isConst || c.Name() != ext.CommaConstMeta.Name() {
		return nil, nil, false
	}
	return cm.Arg(), inner.Arg(), true
}

// plus builds the term `a + b`.
func plus(a, b Term) Term { return ext.Apply(natPlus, a, b) }

// star builds the term `a * b`.
func star(a, b Term) Term { return ext.Apply(natStar, a, b) }

// minus builds the term `a - b` (truncated num subtraction).
func minus(a, b Term) Term { return ext.Apply(natMinus, a, b) }

// nat_max / nat_min have no builder helpers: the case-split engine only RECOGNIZES
// `nat_max a b` / `nat_min a b` (via MatchesMax / MatchesMin) and never constructs them.

// preT builds `predecessor n`.
func preT(n Term) Term { return ext.Apply(natPre, n) }

// expT builds `nat_pow m n` (= `m^n`).
func expT(m, n Term) Term { return ext.Apply(natExp, m, n) }

// divT builds the term `nat_div(a, b)`; modT builds `nat_mod(a, b)`.
func divT(a, b Term) Term { return ext.Apply(natDiv, a, b) }
func modT(a, b Term) Term { return ext.Apply(natMod, a, b) }

// evenT / oddT build `nat_even n` / `nat_odd n`.
func evenT(n Term) Term { return ext.Apply(natEven, n) }
func oddT(n Term) Term  { return ext.Apply(natOdd, n) }

// factT builds `factorial n`.
func factT(n Term) Term { return ext.Apply(natFact, n) }
