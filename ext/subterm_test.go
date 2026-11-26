package ext

import (
	"iter"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
)

func TestSubTerms(t *testing.T) {
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	z := Var("z", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeInd, TypeBool))

	dedup := func(terms ...Term) []Term {
		dedupTerms := SubTerms(terms...)
		return slices.CompactFunc(
			slices.SortedFunc(dedupTerms, Term.Compare), Term.AlphaEquals)
	}

	assert.Empty(t, dedup())

	s0 := P.Apply(x, y)
	s := dedup(s0)
	assertTermsAlphaEqual(t, s, s0, P.Apply(x), P, x, y)
	assert.True(t, utils.All(s, func(term Term) bool { return IsSub(term, s0) }))

	s0 = x.To(y.To(z.To(P.Apply(x, y).And(P.Apply(y, z)))))
	s = dedup(s0)
	assertTermsAlphaEqual(t, s, s0,
		x.To(y.To(P.Apply(x, y))), x.To(P.Apply(x)), P, x.To(x))
	assert.True(t, utils.All(s, func(term Term) bool { return IsSub(term, s0) }))

	s = dedup(P.Apply(x, y), P.Apply(x, z))
	assertTermsAlphaEqual(t, s, P.Apply(x, y), P.Apply(x, z), P.Apply(x), P, x, y, z)

	s0 = ForAll(x)(P.Apply(x, y))
	s = dedup(s0)
	forall, _ := MatchesApply(s0)
	assertTermsAlphaEqual(t, s,
		s0, x.To(P.Apply(x, y)), x.To(P.Apply(x)),
		x.To(x), forall, P, y)
	assert.True(t, utils.All(s, func(term Term) bool { return IsSub(term, s0) }))

	s = dedup(x.To(P.Apply(x, y)), P.Apply(x, z))
	assertTermsAlphaEqual(t, s,
		x.To(P.Apply(x, y)), P.Apply(x, z), P.Apply(x),
		x.To(P.Apply(x)), x.To(x), P, x, y, z)

	s0 = x.To(x.To(P.Apply(x, y)))
	s = dedup(s0)
	assertTermsAlphaEqual(t, s,
		s0, x.To(P.Apply(x, y)), x.To(P.Apply(x)), x.To(x), P, y)
	assert.True(t, utils.All(s, func(term Term) bool { return IsSub(term, s0) }))
}

// Pins SubTerms' two-regime contract and the per-path walk underneath
// it. Below the size gate SubTerms enumerates per parent path (exact —
// wrapped-variant consumers and occurrence counters see everything);
// above it, pointer-shared nodes dedupe to their first occurrence. The
// walk with a nil seen set (FrequentSubTerms' counting walk) is
// per-path unconditionally.
func TestSubTermsSharingSemantics(t *testing.T) {
	x := Var("x", TypeInd)
	Q := Var("Q", MakeFun(TypeInd, TypeInd))
	P := Var("P", MakeFun(TypeInd, TypeInd, TypeBool))
	shared := Q.Apply(x)
	root := P.Apply(shared, shared)

	count := func(seq iter.Seq[Term], want Term) int {
		n := 0
		for s := range seq {
			if s.Equals(want) {
				n++
			}
		}
		return n
	}
	perPath := func(terms ...Term) iter.Seq[Term] {
		return func(yield func(Term) bool) {
			for _, t := range terms {
				for o := range subTermsSeq(t, false, nil) {
					if !yield(o.term) {
						return
					}
				}
			}
		}
	}
	// Small regime: exact per-path enumeration, both agree.
	assert.Equal(t, 2, count(SubTerms(root), shared))
	assert.Equal(t, 2, count(perPath(root), shared))
	assert.Equal(t, 3, count(perPath(Term(shared), Term(root)), shared))

	// Gate-crossing regime: pointer dedup, one occurrence per unique
	// node — bounded on shared DAGs where per-path enumeration is
	// exponential. (A doubling chain: naive size 2^k, unique nodes k.)
	big := Term(shared.Eq(shared))
	for big.Size() <= core.NaiveWalkMemoThreshold {
		big = And(big, big)
	}
	assert.True(t, NaiveWalkNeedsMemo(big))
	assert.Equal(t, 1, count(SubTerms(big), shared))
	// The returned Seq is re-rangeable: a second iteration re-dedupes
	// from scratch rather than seeing a stale seen set.
	seq := SubTerms(big)
	assert.Equal(t, 1, count(seq, shared))
	assert.Equal(t, 1, count(seq, shared))
}

func TestIsSub(t *testing.T) {
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	z := Var("z", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeInd, TypeInd))
	Q := Var("Q", MakeFun(TypeInd, TypeInd))
	R := Var("R", MakeFun(TypeInd, TypeInd))

	assert.True(t, IsSub(P.Apply(x), P.Apply(x, R.Apply(x))))
	assert.True(t, IsSub(P.Apply(x), P.Apply(y, P.Apply(x, y))))
	assert.False(t, IsSub(P.Apply(x), P.Apply(y, R.Apply(x))))
	assert.False(t, IsSub(Q.Apply(x), P.Apply(x, R.Apply(x))))
	assert.False(t, IsSub(P.Apply(x, y), x.To(y.To(P.Apply(x, y)))))
	assert.False(t, IsSub(y.To(P.Apply(x, y)), x.To(y.To(P.Apply(x, y)))))
	assert.True(t, IsSub(y.To(P.Apply(y)), x.To(y.To(P.Apply(y)))))
	assert.False(t, IsSub(y.To(P.Apply(y)), z.To(y.To(P.Apply(x, y)))))
	assert.True(t, IsSub(y.To(P.Apply(y)), z.To(y.To(P.Apply(y, x)))))
	assert.True(t, IsSub(x.To(Q.Apply(x)), y.To(Q.Apply(y))))
	assert.False(t, IsSub(x.To(Q.Apply(x)), y.To(R.Apply(y))))
	assert.True(t, IsSub(Q.Apply(y), x.To(Q.Apply(y))))
	assert.False(t, IsSub(Q.Apply(y), y.To(Q.Apply(y))))
	assert.True(t, IsSub(x.To(Q.Apply(x)), y.To(P.Apply(Q.Apply(y)))))
	assert.False(t, IsSub(x.To(Q.Apply(y)), y.To(P.Apply(Q.Apply(y)))))
	assert.False(t, IsSub(x.To(Q.Apply(y)), x.To(P.Apply(Q.Apply(y)))))
	assert.True(t, IsSub(x.To(Q.Apply(x)), z.To(y.To(P.Apply(Q.Apply(y))))))
	assert.True(t, IsSub(x.To(Q.Apply(x)), y.To(z.To(P.Apply(Q.Apply(y))))))
	assert.False(t, IsSub(y.To(z.To(Q.Apply(y))), y.To(z.To(P.Apply(Q.Apply(y))))))
	assert.True(t, IsSub(x.To(Q.Apply(x)), Q.Apply(x.To(Q.Apply(x)).Apply(y))))
	assert.True(t, IsSub(x.To(R.Apply(x)), x.To(ForAll(x)(R.Apply(x).Eq(y)).Eq(Q.Apply(x).Eq(y)))))
	assert.True(t, IsSub(x.To(x.To(Q.Apply(x))),
		P.Eq(x.To(x.To(Q.Apply(x))))))
}

func TestFrequentSub(t *testing.T) {
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	z := Var("z", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))

	s := FrequentSubTerms(2, x.To(P.Apply(x, y)), P.Apply(x, z))
	assert.Nil(t, s)

	// P and P(x) occur only as heads of applications — spine prefixes —
	// so neither is a candidate, whatever the threshold.
	s = FrequentSubTerms(1, x.To(P.Apply(x, y)), P.Apply(x, z))
	assert.Nil(t, s)

	s = FrequentSubTerms(3, x.To(P.Apply(x, y)), x.To(P.Apply(x, z)))
	assert.Nil(t, s)

	s = FrequentSubTerms(3,
		ForAll(x)(P.Apply(x, y)),
		Exists(x)(P.Apply(x, z)))
	assert.Nil(t, s)

	// A function term that is passed as a value somewhere is a
	// candidate, and its applied occurrences count too.
	H := Var("H", MakeFun(MakeFun(TypeInd, TypeBool), TypeBool))
	s = FrequentSubTerms(2, H.Apply(P.Apply(x)), P.Apply(x, y))
	assertTermEqual(t, s, P.Apply(x))

	s = FrequentSubTerms(2,
		Q.Apply(x).Imply(ForAll(x)(P.Apply(x, y))),
		Q.Apply(y).Imply(Exists(z)(P.Apply(z, y))))
	assertTermAlphaEqual(t, s, x.To(P.Apply(x, y)))

	s = FrequentSubTerms(3,
		Q.Apply(x).Imply(ForAll(x)(P.Apply(x, y))),
		Q.Apply(y).Imply(ForAll(z)(P.Apply(z, y))))
	assertTermAlphaEqual(t, s, ForAll(x)(P.Apply(x, y)))

	s = FrequentSubTerms(3,
		ForAll(z)(P.Apply(z, y)).Imply(ForAll(x)(P.Apply(x, y))))
	assertTermAlphaEqual(t, s, ForAll(x)(P.Apply(x, y)))

	s = FrequentSubTerms(3,
		ForAll(z)(P.Apply(z, y)).Imply(ForAll(x)(Q.Apply(x).And(P.Apply(x, y)))))
	assertTermAlphaEqual(t, s, x.To(P.Apply(x, y)))
}

// Pins the AdaptiveMemo arming contract: disarmed below the visit
// budget, armed exactly once the cumulative arrival count crosses it —
// independent of any size-gate prediction.
func TestAdaptiveMemoBudgetArm(t *testing.T) {
	var a AdaptiveMemo[SeenSet]
	for i := 0; i < core.NaiveWalkMemoThreshold; i++ {
		if m := a.Arrive(); m != nil {
			t.Fatalf("armed at visit %d, below the budget", i+1)
		}
	}
	if a.Memo() != nil {
		t.Fatal("Memo() non-nil while still at the budget boundary")
	}
	if m := a.Arrive(); m == nil {
		t.Fatal("not armed after crossing the visit budget")
	}
	if a.Memo() == nil {
		t.Fatal("Memo() nil after budget arming")
	}
}

// Pins entry- and fresh-term arming against the size gate: a small root
// starts disarmed, a gate-crossing term arms via ArmFor, and ArmFor
// never disarms or replaces a live memo.
func TestAdaptiveMemoSizeArm(t *testing.T) {
	small := core.Var("x", TypeBool)
	if a := AdaptiveFor[SeenSet](small); a.Memo() != nil {
		t.Fatal("entry-armed on a small root")
	}

	// Build a term whose naive size crosses the gate: a doubling chain
	// of boolean conjunctions.
	big := Term(small)
	for big.Size() <= core.NaiveWalkMemoThreshold {
		big = And(big, big)
	}
	if !NaiveWalkNeedsMemo(big) {
		t.Fatal("test term failed to cross the size gate")
	}
	if a := AdaptiveFor[SeenSet](big); a.Memo() == nil {
		t.Fatal("not entry-armed on a gate-crossing root")
	}

	var a AdaptiveMemo[SeenSet]
	a.ArmFor(small)
	if a.Memo() != nil {
		t.Fatal("ArmFor armed on a small fresh term")
	}
	a.ArmFor(big)
	m := a.Memo()
	if m == nil {
		t.Fatal("ArmFor did not arm on a gate-crossing fresh term")
	}
	a.ArmFor(big)
	if a.Memo() != m {
		t.Fatal("ArmFor replaced a live memo")
	}
}
