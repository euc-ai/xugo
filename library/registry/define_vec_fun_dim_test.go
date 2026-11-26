package registry_test

// define_vec_fun_dim_test.go — DefEntry.SourceDim / TargetDim: a constant
// that reads maps between two vector spaces names the dimension its
// maps are read on and the dimension their values are read at, by
// binder, and a declaration that names neither a num binder nor governs
// a map argument is refused at the door.

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/require"
)

func TestDefine_VecFunDims(t *testing.T) {
	fam := registry.NewFamily("zz_define_vec_fun_dim_test", nil)
	const linear = "((num → A) → num → A)"

	// The dimensions are found by name among the binders behind the
	// implicit prefix, in whichever order the equation binds them there.
	fam.Define(registry.DefEntry{
		Name:      "Carries",
		Const:     "zz_reg_carries",
		Type:      "A → num → num → " + linear + " → bool",
		Implicit:  []string{"zero"},
		SourceDim: "n",
		TargetDim: "m",
		Equations: []string{"∀zero:A. ∀m n:num. ∀f:" + linear + ". zz_reg_carries⟨m, n⟩(zero, f) ⇔ m = n ∧ f = f ∧ zero = zero"},
	})
	source, target, ok := registry.VecFunDimSlots("zz_reg_carries")
	require.True(t, ok)
	require.Equal(t, [2]int{2, 1}, [2]int{source, target})

	// Maps of one space into itself: one binder is both.
	fam.Define(registry.DefEntry{
		Name:      "Undoes",
		Const:     "zz_reg_undoes",
		Type:      "num → " + linear + " → " + linear + " → bool",
		SourceDim: "n",
		TargetDim: "n",
		Equations: []string{"∀n:num. ∀L K:" + linear + ". zz_reg_undoes⟨n⟩(L, K) ⇔ n = n ∧ L = K"},
	})
	source, target, ok = registry.VecFunDimSlots("zz_reg_undoes")
	require.True(t, ok)
	require.Equal(t, [2]int{0, 0}, [2]int{source, target})

	// A constant that declares nothing has no slots.
	_, _, ok = registry.VecFunDimSlots("zz_reg_no_such_constant")
	require.False(t, ok)

	refusal := func(e registry.DefEntry) (r any) {
		defer func() { r = recover() }()
		fam.Define(e)
		return nil
	}
	entry := func(name, source, target, typ, equation string) registry.DefEntry {
		return registry.DefEntry{
			Name: name, Const: "zz_reg_" + name, Type: typ,
			SourceDim: source, TargetDim: target,
			Equations: []string{equation},
		}
	}
	const carriesType = "num → num → " + linear + " → bool"
	carries := func(name string) string {
		return "∀n m:num. ∀f:" + linear + ". zz_reg_" + name + "⟨n, m⟩(f) ⇔ n = m ∧ f = f"
	}
	for _, tc := range []struct {
		entry registry.DefEntry
		want  string
	}{
		{entry("only_source", "n", "", carriesType, carries("only_source")),
			"SourceDim/TargetDim: a map dimension declaration needs both SourceDim and TargetDim"},
		{entry("only_target", "", "m", carriesType, carries("only_target")),
			"SourceDim/TargetDim: a map dimension declaration needs both SourceDim and TargetDim"},
		{entry("no_binder", "n", "k", carriesType, carries("no_binder")),
			"SourceDim/TargetDim: k is not a ∀-binder of the equation"},
		{entry("not_num", "n", "f", carriesType, carries("not_num")),
			"SourceDim/TargetDim: f is bound at "},
		// A vector and a matrix are not maps: the declaration would
		// govern no argument.
		{entry("no_map", "n", "m", "num → num → (num → A) → (num → num → A) → bool",
			"∀n m:num. ∀u:(num → A). ∀P:(num → num → A). zz_reg_no_map⟨n, m⟩(u, P) ⇔ n = m ∧ u = u ∧ P = P"),
			"SourceDim/TargetDim: the equation binds no map between vector spaces"},
	} {
		got := fmt.Sprint(refusal(tc.entry))
		require.Contains(t, got, "registry.Define("+tc.entry.Name+"): "+tc.want)
		_, _, declared := registry.VecFunDimSlots(tc.entry.Const)
		require.False(t, declared, "%s was refused and still declares its slots", tc.entry.Const)
	}
}

// The map carrier is `(num → τ) → num → τ` over ONE element, and no
// other shape: a vector, a matrix, a functional on vectors and a map
// into sequences of another element are each something else.
func TestIsVecFunType(t *testing.T) {
	num, a, b := ext.NumType, core.MakeVarType("A"), core.MakeVarType("B")
	vector := func(elem core.HolType) core.HolType { return core.MakeFun(num, elem) }
	for _, tc := range []struct {
		name string
		typ  core.HolType
		want bool
	}{
		{"a map of sequences over A", core.MakeFun(vector(a), vector(a)), true},
		{"the same type written curried", core.MakeFun(vector(a), num, a), true},
		{"a map of sequences of naturals", core.MakeFun(vector(num), vector(num)), true},
		{"a vector", vector(a), false},
		{"a matrix", core.MakeFun(num, num, a), false},
		{"a functional on vectors", core.MakeFun(vector(a), a), false},
		{"a map into sequences of another element", core.MakeFun(vector(a), vector(b)), false},
		{"a map of two vectors", core.MakeFun(vector(a), vector(a), vector(a)), false},
		{"a map on matrices", core.MakeFun(core.MakeFun(num, num, a), vector(a)), false},
		{"a predicate on a vector and an index", core.MakeFun(vector(a), num, core.TypeBool()), false},
		{"a type that is no function", a, false},
	} {
		require.Equal(t, tc.want, registry.IsVecFunType(tc.typ), "%s: %s", tc.name, ext.FormatType(tc.typ))
	}
}
