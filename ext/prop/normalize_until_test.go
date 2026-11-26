package prop

import (
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/require"
)

// wideSequent is a sequent whose normal form takes seconds: binders
// hypotheses ∀x. S(x, aᵢ, aⱼ) and ground hypotheses R(aᵢ, aⱼ) over a pool
// of free variables, concluding c. With the hypotheses moved into the
// conclusion it is one disjunction of binders+ground clauses, and the
// sort of that disjunction, which simplifies it first, is most of a
// second at 332 clauses (measured: 0.6 to 0.8 s at 316); the canonical
// form runs it a dozen times. It is the shape of a set driver's unfolded
// residual, a few quantified laws among many membership facts.
func wideSequent(binders, ground int) Prop {
	const pool = 24
	a := make([]Term, pool)
	for i := range a {
		a[i] = Var(TermName(fmt.Sprintf("a%d", i)), TypeA)
	}
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
	S := Var("S", MakeFun(TypeA, TypeA, TypeA, TypeBool))
	x := Var("x", TypeA)
	var hyps []Term
	for i := range binders {
		hyps = append(hyps, ForAll(x)(S.Apply(x, a[i%pool], a[(i/pool)%pool])))
	}
	for j := range ground {
		hyps = append(hyps, R.Apply(a[j%pool], a[(j/pool)%pool]))
	}
	return MakeProp(Var("c", TypeBool), hyps...)
}

// cutOf runs call and returns the utils.Cut it panicked with, and how
// long it ran; ok is false when it returned.
func cutOf(call func()) (cut utils.Cut, ok bool, elapsed time.Duration) {
	t0 := time.Now()
	defer func() {
		elapsed = time.Since(t0)
		if r := recover(); r != nil {
			if cut, ok = utils.AsCut(r); !ok {
				panic(r)
			}
		}
	}()
	call()
	return
}

// TestNormalizeUntil_AWideSequentIsCutOffInsideItsNormalization: the
// context of a normalization reaches inside it. The normal form of this
// sequent takes nine seconds on an idle machine, eight of them in one
// stage, the canonical disjunctive form; under a deadline the run raises
// a utils.Cut that names the normalization, a unit of work after the
// deadline and not a stage after it, and the cache keeps nothing. A
// normalization that read no clock returns its normal form nine seconds
// late and raises nothing.
func TestNormalizeUntil_AWideSequentIsCutOffInsideItsNormalization(t *testing.T) {
	if testing.Short() {
		t.Skip("a nine-second normalization, cut at several deadlines")
	}
	p := wideSequent(32, 300)
	// A unit of the normalization is at most one sort of the disjunction,
	// under a second on this sequent; the slack is for a loaded machine.
	// The stage the deadlines fall in or before ends eight seconds in.
	const slack = 5 * time.Second
	for _, deadline := range []time.Duration{0, 50 * time.Millisecond, 500 * time.Millisecond, 2 * time.Second} {
		t.Run(fmt.Sprintf("deadline %v", deadline), func(t *testing.T) {
			cache := &PreCNFCache{}
			ctx, cancel := context.WithTimeout(t.Context(), deadline)
			defer cancel()
			cut, ok, elapsed := cutOf(func() { cache.NormalizeUntil(ctx, p) })
			require.True(t, ok, "the normalization returned after %v under a %v deadline", elapsed, deadline)
			require.True(t, strings.HasPrefix(cut.Where, "inside the pre-CNF normalization of the sequent"), "cut %q", cut.Where)
			require.ErrorIs(t, cut.Cause, context.DeadlineExceeded)
			require.Less(t, elapsed, deadline+slack, "the cut came %v after the deadline, %s", elapsed-deadline, cut.Where)
			require.Zero(t, cache.PropCacheSize(), "a cut normalization is cached")
			t.Logf("cut %v after the deadline, %s", elapsed-deadline, cut.Where)
		})
	}
}

// TestNormalizeUntil_ReturnsWhatNormalizeReturns: under a context that
// can end and does not, the normal form is Normalize's, binder for
// binder — the run polls and rewrites nothing else — and it is cached
// as Normalize's is. The sequents are a block whose binders the
// canonical form identifies, one with nothing to identify, and one with
// nothing to normalize.
func TestNormalizeUntil_ReturnsWhatNormalizeReturns(t *testing.T) {
	s, u := Var("s", TypeA), Var("t", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	c := Var("c", TypeBool)
	sequents := map[string]Prop{
		"a block to identify":  wideSequent(6, 20),
		"two binders, one use": MakeProp(c, ForAll(s, u)(P.Apply(s, u)), ForAll(s)(Q.Apply(s))),
		"an implication chain": MakeProp(ForAll(s)(Q.Apply(s).Imply(P.Apply(s, s).Imply(c)))),
		"already normal":       MakeProp(c),
	}
	for name, p := range sequents {
		t.Run(name, func(t *testing.T) {
			ctx, cancel := context.WithCancel(t.Context())
			defer cancel()
			want, _ := Normalize(p)
			cache := &PreCNFCache{}
			got, reconstruct := cache.NormalizeUntil(ctx, p)
			require.Zero(t, got.NumHyps())
			require.True(t, got.Conclusion().Equals(want.Conclusion()),
				"under a context: %s\nwithout one:     %s", PrintProp(got), PrintProp(want))
			require.Equal(t, 1, cache.PropCacheSize())
			// The reconstruction carries the normal form back to the
			// sequent, or to a stronger one where hypotheses merged.
			require.True(t, IsStronger(reconstruct(got), p))
			again, _ := cache.Normalize(p)
			require.True(t, again.Conclusion().Equals(got.Conclusion()), "the cached form is the one returned")
		})
	}
}
