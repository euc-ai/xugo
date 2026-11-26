package omega

// The step's memo of the signs monomials fold to (monomial_sign_memo.go):
// what a second ask reads, what makes another answer, and when the memo is
// dropped.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext"
)

// signRowOf is the sign row of rows about m: `&0 ⋈ m` or `m ⋈ &0`.
func signRowOf(rows []LinConstraint, m Term, zero func(Term) bool) (LinConstraint, bool) {
	for _, r := range rows {
		if (zero(r.Lhs) && r.Rhs.AlphaEquals(m)) || (zero(r.Rhs) && r.Lhs.AlphaEquals(m)) {
			return r, true
		}
	}
	return LinConstraint{}, false
}

// TestMonomialSign_KeptForTheStepUnderItsSignFacts: a monomial's sign is
// folded once under a list of sign facts. Asked again under the same facts
// it is the proof it was, and that proof is the one a fresh fold builds;
// other facts are another answer; a decline is kept as a sign is; and the
// step's release drops them all.
func TestMonomialSign_KeptForTheStepUnderItsSignFacts(t *testing.T) {
	installTestBundle(t)
	ReleaseStepMemos()
	m := rr("a * b")
	strictHyps := []Term{pb("&0 < a"), pb("&0 < b"), pb("a * b <= c")}
	rowsUnder := func(hyps []Term) []LinConstraint {
		return realMonomialSignConstraints(realDomain.hypConstraints(slices.Values(hyps)))
	}

	first, ok := signRowOf(rowsUnder(strictHyps), m, isRealZero)
	if !ok || first.Op != opLT {
		t.Fatalf("no strict sign row for %s under two positive factors", ext.PrintTerm(m))
	}
	again, ok := signRowOf(rowsUnder(strictHyps), m, isRealZero)
	if !ok || again.HypProof != first.HypProof {
		t.Error("the second ask under the same sign facts folded the sign again")
	}

	// The kept sign is the fresh fold's theorem, on the same hypotheses.
	signs := realFactorSigns(realDomain.hypConstraints(slices.Values(strictHyps)))
	fresh, ok := realMonomialSign(m, signs)
	if !ok || !fresh.proof.Conclusion().Equals(first.HypProof.Conclusion()) ||
		!slices.EqualFunc(fresh.proof.Hyps(), first.HypProof.Hyps(), Term.Equals) {
		t.Errorf("the kept sign is not the one the fold builds: %s", ext.PrintTerm(first.HypProof.Conclusion()))
	}

	// A weaker fact about one factor is another list, and another answer.
	weakHyps := []Term{pb("&0 <= a"), pb("&0 < b"), pb("a * b <= c")}
	weak, ok := signRowOf(rowsUnder(weakHyps), m, isRealZero)
	if !ok || weak.Op != opLE {
		t.Fatalf("the sign under a non-strict factor is not the non-strict one")
	}
	if still, ok := signRowOf(rowsUnder(strictHyps), m, isRealZero); !ok || still.HypProof != first.HypProof {
		t.Error("the answer under the strict facts did not survive an ask under others")
	}

	// A factor with no sign in sight: the decline is kept, and no row made.
	bareHyps := []Term{pb("&0 < a"), pb("a * b <= c")}
	if _, ok := signRowOf(rowsUnder(bareHyps), m, isRealZero); ok {
		t.Fatalf("a sign row for %s with no sign of b in sight", ext.PrintTerm(m))
	}
	bare := realFoldsUnder(realFactorSigns(realDomain.hypConstraints(slices.Values(bareHyps))))
	if _, ok, held := realMonomialSigns.lookup(bare.under, m); !held || ok {
		t.Errorf("the decline is not kept: held %v, a sign %v", held, ok)
	}

	strict := realFoldsUnder(signs)
	if _, _, held := realMonomialSigns.lookup(strict.under, m); !held {
		t.Fatal("the sign is not held before the release")
	}
	ReleaseStepMemos()
	if _, _, held := realMonomialSigns.lookup(realFoldsUnder(signs).under, m); held {
		t.Error("the sign outlived its step")
	}
}

// TestMonomialSign_AnotherProofOfAFactIsAnotherList: the facts are
// compared as theorems. A sign stated by a hypothesis and the same sign
// projected out of a conjunction rest on different hypotheses, and a fold
// under one is not served under the other.
func TestMonomialSign_AnotherProofOfAFactIsAnotherList(t *testing.T) {
	installTestBundle(t)
	ReleaseStepMemos()
	m := rr("a * b")
	rowsUnder := func(hyps []Term) []LinConstraint {
		return realMonomialSignConstraints(realDomain.hypConstraints(slices.Values(hyps)))
	}
	plain, ok := signRowOf(rowsUnder([]Term{pb("&0 < a"), pb("&0 < b"), pb("a * b <= c")}), m, isRealZero)
	if !ok {
		t.Fatal("no sign row under the plain facts")
	}
	joined, ok := signRowOf(rowsUnder([]Term{pb("&0 < a /\\ &0 < b"), pb("a * b <= c")}), m, isRealZero)
	if !ok {
		t.Fatal("no sign row under the conjunction")
	}
	if joined.HypProof == plain.HypProof ||
		slices.EqualFunc(joined.HypProof.Hyps(), plain.HypProof.Hyps(), Term.Equals) {
		t.Errorf("the sign under the conjunction rests on the plain facts' hypotheses: %d against %d",
			joined.HypProof.NumHyps(), plain.HypProof.NumHyps())
	}
}

// TestIntMonomialSign_KeptForTheStep: the ℤ fold through the same memo.
func TestIntMonomialSign_KeptForTheStep(t *testing.T) {
	installTestBundle(t)
	ReleaseStepMemos()
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	z := intLit(0)
	m := intStarT(a, b)
	hyps := []Term{intLtT(z, a), intLtT(z, b), intLeT(m, c)}
	isZero := func(t Term) bool { return t.AlphaEquals(z) }
	rows := func() []LinConstraint {
		return intMonomialSignConstraints(intDomain.hypConstraints(slices.Values(hyps)))
	}
	first, ok := signRowOf(rows(), m, isZero)
	if !ok || first.Op != opLT {
		t.Fatalf("no strict sign row for %s under two positive factors", ext.PrintTerm(m))
	}
	if again, ok := signRowOf(rows(), m, isZero); !ok || again.HypProof != first.HypProof {
		t.Error("the second ask under the same sign facts folded the int sign again")
	}
	ReleaseStepMemos()
	if again, ok := signRowOf(rows(), m, isZero); !ok || again.HypProof == first.HypProof {
		t.Error("the int sign outlived its step")
	}
}

// TestAtomsOf_EachAtomOnceInTheOrderTheSidesHoldThem: the one pass the sign
// rows read their monomials and their powers off.
func TestAtomsOf_EachAtomOnceInTheOrderTheSidesHoldThem(t *testing.T) {
	installTestBundle(t)
	cs := realDomain.hypConstraints(slices.Values([]Term{pb("a * b <= c"), pb("c + a * b < d"), pb("&0 < d")}))
	atoms := realDomain.atomsOf(cs)
	want := []Term{rr("a * b"), rr("c"), rr("d")}
	if !slices.EqualFunc(atoms, want, Term.AlphaEquals) {
		names := make([]string, len(atoms))
		for i, atom := range atoms {
			names[i] = ext.PrintTerm(atom)
		}
		t.Errorf("atoms %v", names)
	}
	if bearing := realSignAtoms(atoms); len(bearing) != 1 || !bearing[0].AlphaEquals(rr("a * b")) {
		t.Errorf("%d sign-bearing atoms, the product alone expected", len(bearing))
	}
}
