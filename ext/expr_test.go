package ext_test

// expr_test.go — the descriptor seal, OBSERVED. The
// guarantees below are enforced by design (unexported probe
// interface, goType identity check, one adoption gate); this test is
// the observing step that keeps them from rotting silently — without
// it, weakening any of the checks leaves every gate green.
//
// Deliberately a BLACK-BOX test (package ext_test): the seal's claims
// are about what an OUTSIDE package can and cannot do. One claim is
// not testable because it is not even writable: an impostor type
// satisfying _ExprRuntime cannot be declared here — the method name
// AND its result type are unexported, so the compiler, not this test,
// is the guarantee. What an outside package CAN produce is the
// promotion route below.

import (
	"math/big"
	"reflect"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// embedsTyped inherits *ext.Expr[Nat]'s method set by promotion — the
// one way an outside package produces a type whose values satisfy the
// sealed probe interface. The descriptor must reject the TYPE by Go
// identity: its capabilities describe *Expr[Nat], not *embedsTyped,
// and binding it would construct a value of the wrong parameter type.
type embedsTyped struct{ *ext.Expr[ext.Nat] }

func TestDescribeExprTypeSeal(t *testing.T) {
	// The typed instantiation is described: the asserted HOL type is
	// reified, and Adopt constructs a checked value at the same Go
	// type the caller asked about.
	rt := reflect.TypeFor[*ext.Expr[ext.Nat]]()
	desc, ok := ext.DescribeExprType(rt)
	if !ok {
		t.Fatal("DescribeExprType must describe *Expr[Nat]")
	}
	if !desc.HOLType().Equals(ext.NumType) {
		t.Fatalf("described HOL type = %s, want num", ext.FormatType(desc.HOLType()))
	}
	three := ext.MakeNumeral(big.NewInt(3))
	if got := desc.Adopt(three).Type(); got != rt {
		t.Fatalf("Adopt constructed %s, want %s", got, rt)
	}

	// Adopt is CHECKED — the descriptor carries the adoption gate,
	// not a raw constructor: a bool-typed term must panic.
	func() {
		defer func() {
			if recover() == nil {
				t.Error("Adopt of a bool term at Expr[Nat] must panic in the adoption gate")
			}
		}()
		desc.Adopt(ext.Var("p", core.TypeBool()))
	}()

	// The untyped wrapper is NOT a typed parameter: it asserts
	// nothing, and being its own struct (not an Expr instantiation) it
	// lacks the probe method — rejected structurally.
	if _, ok := ext.DescribeExprType(reflect.TypeFor[*ext.TermWrapper]()); ok {
		t.Error("DescribeExprType must reject *TermWrapper")
	}

	// Non-pointers and unrelated pointers describe nothing.
	if _, ok := ext.DescribeExprType(nil); ok {
		t.Error("DescribeExprType(nil) must report false")
	}
	if _, ok := ext.DescribeExprType(reflect.TypeFor[ext.Expr[ext.Nat]]()); ok {
		t.Error("DescribeExprType must reject the non-pointer Expr type")
	}
	if _, ok := ext.DescribeExprType(reflect.TypeFor[*int]()); ok {
		t.Error("DescribeExprType must reject unrelated pointer types")
	}

	// The promotion forge: probe succeeds (the method promotes through
	// the embedded *Expr[Nat]), and the goType identity check is what
	// rejects it.
	if _, ok := ext.DescribeExprType(reflect.TypeFor[*embedsTyped]()); ok {
		t.Error("DescribeExprType must reject an embedding type by Go-type identity")
	}
}
