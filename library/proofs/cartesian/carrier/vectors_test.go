package carrier

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dimtypes"
	"github.com/euc-ai/xugo/ext/dsl"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/serve/testenv"
	"github.com/euc-ai/xugo/prover/proof"
)

func mustPanicContaining(t *testing.T, want string, f func()) {
	t.Helper()
	defer func() {
		got := recover()
		if got == nil {
			t.Fatalf("expected panic containing %q", want)
		}
		if !strings.Contains(fmt.Sprint(got), want) {
			t.Fatalf("panic %q does not contain %q", got, want)
		}
	}()
	f()
}

func plus(l, r core.Term) core.Term {
	return core.Apply(core.Apply(dsl.NatPlusMeta.Term(), l), r)
}

func membership(elem core.HolType, dim, subject core.Term) core.Term {
	return core.Apply(core.Apply(tupleAt(elem), dim), subject)
}

func TestCheckedMembershipDim(t *testing.T) {
	carrierType := core.MakeFun(ext.NumType, dsl.RealType)
	x := core.Var("x_0", carrierType)
	y := core.Var("y_0", carrierType)
	n0 := core.Var("n_0", ext.NumType)
	m0 := core.Var("m_0", ext.NumType)

	if got, _ := checkedMembershipDim[dsl.Real, DimN](
		x, membership(dsl.RealType, n0, x)); !got.Equals(n0) {
		t.Fatalf("checked dimension = %s, want %s", ext.PrintTerm(got), ext.PrintTerm(n0))
	}
	mustPanicContaining(t, "membership fact says", func() {
		checkedMembershipDim[dsl.Real, DimN](x, membership(dsl.RealType, n0, y))
	})
	mustPanicContaining(t, "membership fact says", func() {
		checkedMembershipDim[dsl.Real, DimN](x, membership(dsl.RealType, m0, x))
	})
}

func TestConcatTermsUseResidentDimensions(t *testing.T) {
	carrierType := core.MakeFun(ext.NumType, dsl.RealType)
	xTerm := core.Var("x_0", carrierType)
	yTerm := core.Var("y_0", carrierType)
	n0 := core.Var("n_0", ext.NumType)
	m0 := core.Var("m_0", ext.NumType)
	letters := map[string]core.Term{"n": n0, "m": m0}
	letter := func(name string) core.Term { return letters[name] }
	x := dimtypes.AnchorVec[dsl.Real, DimN](xTerm, letter)
	y := dimtypes.AnchorVec[dsl.Real, DimM](yTerm, letter)

	sum, term := concatTerms(x, y)
	if want := plus(n0, m0); !sum.Equals(want) {
		t.Fatalf("sum = %s, want %s", ext.PrintTerm(sum), ext.PrintTerm(want))
	}
	wantTerm := core.Apply(core.Apply(core.Apply(catAt(dsl.RealType), n0), xTerm), yTerm)
	if !term.Equals(wantTerm) {
		t.Fatalf("concat term = %s, want %s", ext.PrintTerm(term), ext.PrintTerm(wantTerm))
	}
}

func TestExtensionalityAtVecRejectsDifferentResidentDimensions(t *testing.T) {
	// Two vectors of one phantom anchored at different terms: the cite's
	// dimension check (proof.SameDimension, the one AtVec writes with).
	n0 := core.Var("n_0", ext.NumType)
	n1 := core.Var("n_1", ext.NumType)
	mustPanicContaining(t, "anchored at different terms", func() {
		proof.SameDimension(n0, n1)
	})
}

func TestCheckedRecastTarget(t *testing.T) {
	n0 := core.Var("n_0", ext.NumType)
	m0 := core.Var("m_0", ext.NumType)
	oldDim := plus(n0, m0)
	newDim := plus(m0, n0)

	if got := checkedRecastTarget[dimtypes.Plus[DimN, DimM], dimtypes.Plus[DimM, DimN]](
		oldDim, core.Eq(oldDim, newDim)); !got.Equals(newDim) {
		t.Fatalf("target = %s, want %s", ext.PrintTerm(got), ext.PrintTerm(newDim))
	}
	if got := checkedRecastTarget[dimtypes.Plus[DimN, DimM], dimtypes.Plus[DimM, DimN]](
		oldDim, core.Eq(newDim, oldDim)); !got.Equals(newDim) {
		t.Fatalf("reverse equality target = %s, want %s", ext.PrintTerm(got), ext.PrintTerm(newDim))
	}

	mustPanicContaining(t, "phantoms disagree", func() {
		checkedRecastTarget[DimN, DimM](n0, core.Eq(n0, m0))
	})
	mustPanicContaining(t, "does not mention", func() {
		checkedRecastTarget[dimtypes.Plus[DimN, DimM], dimtypes.Plus[DimM, DimN]](
			oldDim, core.Eq(n0, m0))
	})
	mustPanicContaining(t, "does not denote", func() {
		checkedRecastTarget[dimtypes.Plus[DimN, DimM], dimtypes.Plus[DimM, DimN]](
			oldDim, core.Eq(oldDim, plus(n0, n0)))
	})
	mustPanicContaining(t, "expected a dimension equality", func() {
		checkedRecastTarget[dimtypes.Plus[DimN, DimM], dimtypes.Plus[DimM, DimN]](oldDim, n0)
	})
}

func TestInhabitedConcatAndRecastProof(t *testing.T) {
	env := testenv.MakeT(t)
	// The theorem itself is independently strict-replayed by the corpus
	// harness. This unit test trusts that one dependency so it can focus
	// on the typed composition seam around it.
	closedStmt := ConcatClosed.Entry().Statement().Prop
	closedHyps := make([]core.Term, closedStmt.NumHyps())
	for i := range closedHyps {
		closedHyps[i] = closedStmt.Hyp(i)
	}
	env.LibraryThms[ConcatClosed.DepName()] = core.TestThm(closedStmt.Conclusion(), closedHyps...)

	const statement = "∀n m:num. m + n = n + m ⇒ ∀x:(num → A).(tuple(n,x) ⇒ ∀y:(num " +
		"→ A).(tuple(m,y) ⇒ (tuple(m+n,tuple_cat(n,x,y)) ∧ tuple(m+n,tuple_cat(n,x,y)))))"
	env.Scope = proof.NewProofScope("test_inhabited_concat_recast")
	top, proofGraph := family.Theorem(statement,
		func(a *proof.Argument, n, m Term, dimEq Fact,
			x Term, xMem Fact, y Term, yMem Fact) {
			xVec := Inhabit[A, DimN](x, xMem)
			yVec := Inhabit[A, DimM](y, yMem)
			xy := xVec.Concat(a, yVec)
			commuted := xy.Recast[dimtypes.Plus[DimM, DimN]](a, dimEq)
			a.Do(proof.By(proof.Normalized, commuted.Evidence()))
		}).Fn(env)
	for i, section := range proofGraph.SectionThms() {
		cert, _ := core.ForceWithBoundary(
			context.Background(), section, func(core.Prop) bool { return false })
		if cert.IsZero() {
			t.Fatalf("evidence-flow section %d yielded no certificate", i)
		}
	}
	cert, _ := core.ForceWithBoundary(context.Background(), top, func(core.Prop) bool { return false })
	if cert.IsZero() {
		t.Fatal("evidence-flow theorem yielded no certificate")
	}
}

// This helper is never run: compiling it pins Go 1.27's inference of S
// through IsPlus, which is what keeps the public call site annotation-free.
func concatInferenceCompiles[Elem TypePhantom](
	a *proof.Argument,
	x *InhabitedVec[Elem, DimN], y *InhabitedVec[Elem, DimM],
) *InhabitedVec[Elem, dimtypes.Plus[DimN, DimM]] {
	return x.Concat(a, y)
}
