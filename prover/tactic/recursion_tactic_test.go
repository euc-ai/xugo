package tactic

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// ---------------------------------------------------------------------------
// Shape builders — the three corpus surface arrangements, built directly
// (the corpus-served statements themselves are pinned by the drift test
// in library/serve).
// ---------------------------------------------------------------------------

// numAxiomShape mirrors the corpus num_recursion arrangement: params
// ∀-bound, the clause binder hoisted above the conjunction, base
// equation flipped, ∃! head.
//
//	∀f e. ∃!fn. ∀n. (e = fn(_0)) ∧ (fn(suc n) = f(fn n, n))
func numAxiomShape() Prop {
	A := TypeA
	f := Var("f", MakeFun(A, MakeFun(numType, A)))
	e := Var("e", A)
	fn := Var("fn", MakeFun(numType, A))
	n := Var("n", numType)
	base := e.Eq(fn.Apply(_0))
	step := fn.Apply(ext.Apply(suc, n)).Eq(f.Apply(fn.Apply(n), n))
	return MakeProp(ForAll(f)(ForAll(e)(Unique(fn)(ForAll(n)(base.And(step))))))
}

// listRecursionShape mirrors the corpus list_recursion arrangement:
// params ∀-bound, clause binders hoisted, base equation flipped, ∃.
//
//	∀cons' nil'. ∃fn. ∀a0 a1. (nil' = fn(nil)) ∧
//	                          (fn(cons(a0,a1)) = cons'(a0, a1, fn(a1)))
func listRecursionShape() Prop {
	A, Z := TypeA, TypeB
	listT := core.MakeCompositeType(listMetaType, A)
	nilT := core.MakeConstTerm(core.MakeConstMeta("nil", listT), listT)
	consType := MakeFun(A, MakeFun(listT, listT))
	consT := core.MakeConstTerm(core.MakeConstMeta("cons", consType), consType)
	consP := Var("cons'", MakeFun(A, MakeFun(listT, MakeFun(Z, Z))))
	nilP := Var("nil'", Z)
	fn := Var("fn", MakeFun(listT, Z))
	a0, a1 := Var("a0", A), Var("a1", listT)
	base := nilP.Eq(fn.Apply(nilT))
	step := fn.Apply(ext.Apply(consT, a0, a1)).Eq(consP.Apply(a0, a1, fn.Apply(a1)))
	return MakeProp(ForAll(consP)(ForAll(nilP)(Exists(fn)(
		ForAll(a0)(ForAll(a1)(base.And(step)))))))
}

// optionRecursionShape mirrors the corpus option_recursion
// arrangement: params FREE (the sequent decl prefix), per-clause
// binders, natural orientation.
//
//	⊢ ∃fn. (fn NONE = none') ∧ (∀a. fn(SOME a) = some'(a))
func optionRecursionShape() Prop {
	A, Z := TypeA, TypeB
	optT := core.MakeCompositeType(optionMetaType, A)
	noneT := core.MakeConstTerm(core.MakeConstMeta("none", optT), optT)
	someType := MakeFun(A, optT)
	someT := core.MakeConstTerm(core.MakeConstMeta("some", someType), someType)
	noneP := Var("none'", Z)
	someP := Var("some'", MakeFun(A, Z))
	fn := Var("fn", MakeFun(optT, Z))
	a := Var("a", A)
	base := fn.Apply(noneT).Eq(noneP)
	step := ForAll(a)(fn.Apply(ext.Apply(someT, a)).Eq(someP.Apply(a)))
	return MakeProp(Exists(fn)(base.And(step)))
}

// ---------------------------------------------------------------------------
// Positive analyses
// ---------------------------------------------------------------------------

func TestAnalyzeRecursionPrincipleNumShape(t *testing.T) {
	tmpl, err := AnalyzeRecursionPrinciple(numAxiomShape())
	if err != nil {
		t.Fatal(err)
	}
	if !tmpl.Unique {
		t.Error("num_recursion shape must analyze as ∃! (Unique)")
	}
	if !tmpl.CarrierType.Equals(numType) {
		t.Errorf("carrier = %s, want num", ext.FormatType(tmpl.CarrierType))
	}
	if !tmpl.ResultType.Equals(TypeA) {
		t.Errorf("result = %s, want var:A", ext.FormatType(tmpl.ResultType))
	}
	if len(tmpl.OuterParams) != 2 {
		t.Fatalf("outer params = %d, want 2 (f, e)", len(tmpl.OuterParams))
	}
	if len(tmpl.Cases) != 2 {
		t.Fatalf("cases = %d, want 2", len(tmpl.Cases))
	}

	base := tmpl.Cases[0]
	if got := string(base.Constructor.Name()); got != "_0" {
		t.Errorf("base constructor = %q, want _0", got)
	}
	if len(base.CtorArgs) != 0 || len(base.Slots) != 0 {
		t.Errorf("base case: args=%d slots=%d, want 0/0", len(base.CtorArgs), len(base.Slots))
	}
	if got := string(base.Param.Name()); got != "e" {
		t.Errorf("base param = %q, want e", got)
	}
	if !base.ParamBound {
		t.Error("base param e must classify as ∀-bound")
	}
	if !base.Flipped {
		t.Error("base equation `e = fn(_0)` must record Flipped")
	}

	step := tmpl.Cases[1]
	if got := string(step.Constructor.Name()); got != "suc" {
		t.Errorf("step constructor = %q, want suc", got)
	}
	if len(step.CtorArgs) != 1 {
		t.Fatalf("step ctor args = %d, want 1", len(step.CtorArgs))
	}
	if step.Flipped {
		t.Error("step equation is naturally oriented; Flipped must be false")
	}
	wantSlots := []RecursionSlot{{ArgIndex: 0, Recursive: true}, {ArgIndex: 0}}
	if len(step.Slots) != len(wantSlots) {
		t.Fatalf("step slots = %v, want %v", step.Slots, wantSlots)
	}
	for i, s := range step.Slots {
		if s != wantSlots[i] {
			t.Errorf("step slot %d = %v, want %v", i, s, wantSlots[i])
		}
	}
	if got := step.RecArgIndices(); len(got) != 1 || got[0] != 0 {
		t.Errorf("step RecArgIndices = %v, want [0]", got)
	}
}

func TestAnalyzeRecursionPrincipleListShape(t *testing.T) {
	tmpl, err := AnalyzeRecursionPrinciple(listRecursionShape())
	if err != nil {
		t.Fatal(err)
	}
	if tmpl.Unique {
		t.Error("list_recursion shape is plain ∃")
	}
	if len(tmpl.OuterParams) != 2 || len(tmpl.Cases) != 2 {
		t.Fatalf("outer=%d cases=%d, want 2/2", len(tmpl.OuterParams), len(tmpl.Cases))
	}
	cons := tmpl.Cases[1]
	if got := string(cons.Constructor.Name()); got != "cons" {
		t.Errorf("constructor = %q, want cons", got)
	}
	wantSlots := []RecursionSlot{{ArgIndex: 0}, {ArgIndex: 1}, {ArgIndex: 1, Recursive: true}}
	if len(cons.Slots) != len(wantSlots) {
		t.Fatalf("cons slots = %v, want %v", cons.Slots, wantSlots)
	}
	for i, s := range cons.Slots {
		if s != wantSlots[i] {
			t.Errorf("cons slot %d = %v, want %v", i, s, wantSlots[i])
		}
	}
}

func TestAnalyzeRecursionPrincipleOptionShape(t *testing.T) {
	tmpl, err := AnalyzeRecursionPrinciple(optionRecursionShape())
	if err != nil {
		t.Fatal(err)
	}
	if len(tmpl.OuterParams) != 0 {
		t.Errorf("option params are free; outer = %d, want 0", len(tmpl.OuterParams))
	}
	if len(tmpl.Cases) != 2 {
		t.Fatalf("cases = %d, want 2", len(tmpl.Cases))
	}
	for _, c := range tmpl.Cases {
		if c.ParamBound {
			t.Errorf("param %q must classify as free", ext.PrintTerm(c.Param))
		}
		if c.Flipped {
			t.Errorf("clause %q is naturally oriented", ext.PrintTerm(c.Clause))
		}
	}
	if got := string(tmpl.Cases[0].Constructor.Name()); got != "none" {
		t.Errorf("base constructor = %q, want NONE", got)
	}
	if got := string(tmpl.Cases[1].Constructor.Name()); got != "some" {
		t.Errorf("step constructor = %q, want SOME", got)
	}
}

// ---------------------------------------------------------------------------
// Rejections — shapes outside the structural-recursion template
// ---------------------------------------------------------------------------

func TestAnalyzeRecursionPrincipleRejects(t *testing.T) {
	A := TypeA
	fn := Var("fn", MakeFun(numType, A))
	e := Var("e", A)
	n := Var("n", numType)

	pairType := MakeFun(numType, MakeFun(numType, numType))
	pairN := core.MakeConstTerm(core.MakeConstMeta("PAIRN", pairType), pairType)
	fnNum := Var("fn", MakeFun(numType, numType))

	H := Var("H", MakeFun(MakeFun(numType, A), MakeFun(numType, A)))
	fn2 := Var("fn", MakeFun(numType, MakeFun(numType, A)))
	m := Var("m", numType)
	c := Var("c", A)

	for _, tc := range []struct {
		name string
		p    Prop
		want string
	}{
		{
			"no existential head",
			MakeProp(ForAll(n)(n.Eq(n))),
			"expected ∃fn / ∃!fn",
		},
		{
			"hyp-carrying principle",
			MakeProp(Exists(fn)(fn.Apply(_0).Eq(e)), n.Eq(n)),
			"hyp-free",
		},
		{
			"WF functional shape (fn passed whole)",
			MakeProp(Exists(fn)(ForAll(n)(fn.Apply(n).Eq(H.Apply(fn, n))))),
			"constructor position",
		},
		{
			"curried extra parameter",
			MakeProp(Exists(fn2)(ForAll(m)(fn2.Apply(_0, m).Eq(e)))),
			"exactly the constructor pattern",
		},
		{
			"target head is a clause binder",
			MakeProp(Exists(fn)(ForAll(n)(ForAll(c)(fn.Apply(ext.Apply(suc, n)).Eq(c))))),
			"clause binder",
		},
		{
			"repeated constructor argument",
			MakeProp(Exists(fnNum)(ForAll(n)(fnNum.Apply(ext.Apply(pairN, n, n)).Eq(n)))),
			"must be distinct",
		},
		{
			"parameter serves two clauses",
			MakeProp(Exists(fn)(
				fn.Apply(_0).Eq(e).And(
					ForAll(n)(fn.Apply(ext.Apply(suc, n)).Eq(e))))),
			"serves two clauses",
		},
	} {
		_, err := AnalyzeRecursionPrinciple(tc.p)
		if err == nil {
			t.Errorf("%s: expected an error", tc.name)
			continue
		}
		if !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: error %q does not mention %q", tc.name, err.Error(), tc.want)
		}
	}
}

// ---------------------------------------------------------------------------
// Name candidates + type instantiation
// ---------------------------------------------------------------------------

func TestRecursionPrincipleNameCandidates(t *testing.T) {
	if got := RecursionPrincipleNameCandidates(numType); len(got) == 0 || got[0] != "num_recursion" {
		t.Errorf("num candidates = %v, want num_recursion first", got)
	}
	listA := core.MakeCompositeType(listMetaType, TypeA)
	if got := RecursionPrincipleNameCandidates(listA); len(got) != 1 || got[0] != "list_recursion" {
		t.Errorf("list candidates = %v, want [list_recursion]", got)
	}
	if got := RecursionPrincipleNameCandidates(TypeA); got != nil {
		t.Errorf("a type variable has no candidates, got %v", got)
	}
}

func TestAnalyzeRecursionPrincipleForType(t *testing.T) {
	listNum := core.MakeCompositeType(listMetaType, numType)
	tmpl, err := AnalyzeRecursionPrincipleForType(listRecursionShape(), listNum)
	if err != nil {
		t.Fatal(err)
	}
	if tmpl == nil {
		t.Fatal("polymorphic list principle must instantiate at list(num)")
	}
	if !tmpl.CarrierType.Equals(listNum) {
		t.Errorf("carrier = %s, want list(num)", ext.FormatType(tmpl.CarrierType))
	}
	// The result motive is untouched by the carrier instantiation.
	if !tmpl.ResultType.Equals(TypeB) {
		t.Errorf("result = %s, want var:B", ext.FormatType(tmpl.ResultType))
	}
	// A carrier that can't unify returns (nil, nil).
	tmpl, err = AnalyzeRecursionPrincipleForType(listRecursionShape(), TypeBool)
	if err != nil || tmpl != nil {
		t.Errorf("non-unifiable carrier: got (%v, %v), want (nil, nil)", tmpl, err)
	}
}
