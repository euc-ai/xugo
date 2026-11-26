package prop

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

func TestUniqueImpliesExists(t *testing.T) {
	// ∃!x:bool. x ⇔ ⊤ ⟹ ∃x:bool. x ⇔ ⊤. The input cert is a TestThm
	// (its truth is not the subject); the derivation chain itself runs
	// real kernel ops end-to-end.
	x := ext.Var("x", core.TypeBool())
	body := x.Eq(ext.WrapTerm(ext.T))
	unique := core.TestThm(ext.Unique(x)(body))
	got := UniqueImpliesExists(unique)
	if got == nil {
		t.Fatal("UniqueImpliesExists returned nil on an ∃!-headed theorem")
	}
	if !got.Proved() {
		t.Fatal("result is not proved")
	}
	want := MakeProp(ext.Exists(x)(body))
	if !got.AlphaEquals(want) {
		t.Fatalf("got %s, want %s", PrintProp(got), PrintProp(want))
	}
}

func TestUniqueImpliesExistsFunctionCarrier(t *testing.T) {
	// The compiler's actual use: the bound variable is FUNCTION-typed
	// (∃!fn:(bool→bool). fn(⊤) ⇔ ⊤).
	fn := ext.Var("fn", core.MakeFun(core.TypeBool(), core.TypeBool()))
	body := fn.Apply(ext.WrapTerm(ext.T)).Eq(ext.WrapTerm(ext.T))
	unique := core.TestThm(ext.Unique(fn)(body))
	got := UniqueImpliesExists(unique)
	if got == nil || !got.Proved() {
		t.Fatalf("function-carrier derivation failed: %v", got)
	}
	want := MakeProp(ext.Exists(fn)(body))
	if !got.AlphaEquals(want) {
		t.Fatalf("got %s, want %s", PrintProp(got), PrintProp(want))
	}
}

func TestUniqueImpliesExistsDeclines(t *testing.T) {
	x := ext.Var("x", core.TypeBool())
	if got := UniqueImpliesExists(MakeProp(ext.Exists(x)(x.Eq(x)))); got != nil {
		t.Fatalf("plain ∃ input must decline, got %v", got)
	}
	if got := UniqueImpliesExists(nil); got != nil {
		t.Fatal("nil input must decline")
	}
}
