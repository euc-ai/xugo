package ext

import (
	"reflect"
	"testing"
)

// A typed wrapper's method set is the door to its term and the typed
// operations of its own shape, and nothing promoted: Go compiles every
// method of a generic type once per instantiation, and a family
// instantiates the wrappers at every phantom it names — the 42 methods
// a Term-embedding wrapper carried were three quarters of what a
// family compiled.
func TestTypedWrapperMethodSetStaysSmall(t *testing.T) {
	for _, c := range []struct {
		name string
		typ  reflect.Type
		want []string
	}{
		{"*Expr", reflect.TypeFor[*Expr[Nat]](), []string{"Core"}},
		{"*Arrow", reflect.TypeFor[*Arrow[Nat, Bool]](), []string{"Apply", "Core"}},
		{"*Arrow2", reflect.TypeFor[*Arrow2[Nat, Nat, Bool]](), []string{"Apply", "Core"}},
	} {
		var got []string
		for i := 0; i < c.typ.NumMethod(); i++ {
			got = append(got, c.typ.Method(i).Name)
		}
		if !reflect.DeepEqual(got, c.want) {
			t.Errorf("%s exports %v, want %v", c.name, got, c.want)
		}
	}
	var _ TermLike = (*Expr[Nat])(nil)
	if _, isTerm := any((*Expr[Nat])(nil)).(Term); isTerm {
		t.Error("*Expr is a Term: its method set carries Term's whole interface again")
	}
}
