package omega

import (
	"slices"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// signFact is the shape the two domains' sign facts share (realSignFact,
// intSignFact): what the memo of their folds holds.
type signFact struct {
	term   Term
	proof  *prop.PropWrapper
	nonneg bool
	strict bool
}

// monomialSignMemo keeps, for one arith step, the sign a monomial's
// factors fold to under a list of sign facts: realMonomialSign and then
// realMonomialSignByPieces over ℝ, intMonomialSign over ℤ.
//
// The sign rows ask for it at every product monomial of every row set:
// each linear run's, and each run of the products pass's model, whose
// rows are the pairwise products of the same base differences from one
// question to the next. An arith step asks a context hundreds of
// questions that differ by one hypothesis, so the monomials and the signs
// they are read under repeat: on a thirteen-hypothesis ε-δ context whose
// quotients the basis reads as products, 448 runs of the model asked
// 35,299 times for 3,142 answers.
//
// The fold is a function of the monomial, of the sign facts in their
// order and of the lemma bundle, and of nothing else, so an answer is
// kept under exactly that: the list of facts (under), each fact's term,
// direction and strictness and the sequent of its proof compared by exact
// equality, and the monomial compared the same way; the joined AlphaKeys
// are only the bucket. A proof kept is the theorem a fresh fold would
// build, on the same hypotheses, and a decline is kept as a proof is.
// Released with the step's other memos (ReleaseStepMemos), dropped with
// them by the bundle setters, and bounded within the step.
type monomialSignMemo struct {
	mu       sync.Mutex
	contexts map[string]*signContext
	entries  map[monomialSignKey]monomialSignEntry
}

// A signContext is one list of sign facts the memo has answered under.
type signContext struct {
	signs []signFact
}

type monomialSignKey struct {
	under *signContext
	m     core.TermKey
}

type monomialSignEntry struct {
	m    Term
	fact signFact
	ok   bool
}

const monomialSignMemoCap = 8192

var (
	realMonomialSigns monomialSignMemo
	intMonomialSigns  monomialSignMemo
)

// under returns the context of the answers given under signs, a new one
// where the memo holds none for that list.
func (memo *monomialSignMemo) under(signs []signFact) *signContext {
	var bucket strings.Builder
	for _, f := range signs {
		bucket.WriteString(string(f.term.AlphaKey()))
		if f.nonneg {
			bucket.WriteByte('+')
		}
		if f.strict {
			bucket.WriteByte('<')
		}
		for _, h := range f.proof.Hyps() {
			bucket.WriteByte(',')
			bucket.WriteString(string(h.AlphaKey()))
		}
		bucket.WriteByte(';')
	}
	key := bucket.String()
	memo.mu.Lock()
	defer memo.mu.Unlock()
	if c, ok := memo.contexts[key]; ok && slices.EqualFunc(c.signs, signs, sameSignFact) {
		return c
	}
	c := &signContext{signs: slices.Clone(signs)}
	if memo.contexts == nil {
		memo.contexts = make(map[string]*signContext)
	}
	memo.contexts[key] = c
	return c
}

// sameSignFact reports two sign facts that state one sign of one term by
// one theorem: the same sequent, hypothesis for hypothesis.
func sameSignFact(a, b signFact) bool {
	return a.nonneg == b.nonneg && a.strict == b.strict && a.term.Equals(b.term) &&
		a.proof.Conclusion().Equals(b.proof.Conclusion()) &&
		slices.EqualFunc(a.proof.Hyps(), b.proof.Hyps(), Term.Equals)
}

// lookup returns the answer kept for m under c; held is false where none
// is.
func (memo *monomialSignMemo) lookup(c *signContext, m Term) (fact signFact, ok, held bool) {
	memo.mu.Lock()
	defer memo.mu.Unlock()
	e, found := memo.entries[monomialSignKey{under: c, m: m.AlphaKey()}]
	if !found || !e.m.Equals(m) {
		return signFact{}, false, false
	}
	return e.fact, e.ok, true
}

func (memo *monomialSignMemo) store(c *signContext, m Term, fact signFact, ok bool) {
	memo.mu.Lock()
	defer memo.mu.Unlock()
	if len(memo.entries) >= monomialSignMemoCap {
		memo.contexts, memo.entries = nil, nil
	}
	if memo.entries == nil {
		memo.entries = make(map[monomialSignKey]monomialSignEntry)
	}
	memo.entries[monomialSignKey{under: c, m: m.AlphaKey()}] = monomialSignEntry{m: m, fact: fact, ok: ok}
}

func (memo *monomialSignMemo) reset() {
	memo.mu.Lock()
	defer memo.mu.Unlock()
	memo.contexts, memo.entries = nil, nil
}
