package registry_test

// define_dimensions_test.go — DefEntry.Dimensions: a constant that reads
// spaces at dimensions no vector, matrix or map argument carries names
// those binders for the ⟨…⟩ alone. They register no slot, the text that
// writes them in the parentheses is refused as for every declared
// dimension, and a declaration that names a binder twice, names one
// another declaration names, or names no num binder is refused at the
// door.

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/require"
)

func TestDefine_Dimensions(t *testing.T) {
	fam := registry.NewFamily("zz_define_dimensions_test", nil)
	const spacesType = "num → num → (A → bool) → (B → bool) → bool"

	// The equation writes the two declared binders in the suffix: the
	// count the door registers is what lets it parse.
	fam.Define(registry.DefEntry{
		Name:       "Spaces",
		Const:      "zz_dims_spaces",
		Type:       spacesType,
		Dimensions: []string{"n", "m"},
		Equations:  []string{"∀n m:num. ∀s:(A → bool). ∀t:(B → bool). zz_dims_spaces⟨n, m⟩(s, t) ⇔ n = m ∧ s = s ∧ t = t"},
	})
	_, declared := registry.DimSlot("zz_dims_spaces")
	require.False(t, declared, "Dimensions registers no vector slot")
	_, _, declared = registry.MatrixDimSlots("zz_dims_spaces")
	require.False(t, declared, "Dimensions registers no matrix slots")
	_, _, declared = registry.VecFunDimSlots("zz_dims_spaces")
	require.False(t, declared, "Dimensions registers no map slots")

	// A later text reads the constant with the suffix.
	fam.Define(registry.DefEntry{
		Name:      "SpacesTwice",
		Const:     "zz_dims_spaces_twice",
		Type:      "num → (A → bool) → bool",
		Equations: []string{"∀n:num. ∀s:(A → bool). zz_dims_spaces_twice(n, s) ⇔ zz_dims_spaces⟨n, n⟩(s, s)"},
	})

	// Beside a Dim the binders join the suffix after it: the vector's
	// dimension keeps its slot, the space's dimension takes none.
	fam.Define(registry.DefEntry{
		Name:       "PointIn",
		Const:      "zz_dims_point_in",
		Type:       "num → num → (A → bool) → (num → A) → bool",
		Dim:        "n",
		Dimensions: []string{"m"},
		Equations:  []string{"∀n m:num. ∀s:(A → bool). ∀u:(num → A). zz_dims_point_in⟨n, m⟩(s, u) ⇔ n = m ∧ s = s ∧ u = u"},
	})
	pos, declared := registry.DimSlot("zz_dims_point_in")
	require.True(t, declared)
	require.Equal(t, 0, pos)

	refusal := func(e registry.DefEntry) (r any) {
		defer func() { r = recover() }()
		fam.Define(e)
		return nil
	}
	entry := func(name, dim string, dims []string, equation string) registry.DefEntry {
		return registry.DefEntry{
			Name: name, Const: "zz_dims_" + name, Type: spacesType,
			Dim: dim, Dimensions: dims,
			Equations: []string{equation},
		}
	}
	spaces := func(name, args string) string {
		return "∀n m:num. ∀s:(A → bool). ∀t:(B → bool). zz_dims_" + name + args + " ⇔ n = m ∧ s = s ∧ t = t"
	}
	for _, tc := range []struct {
		entry registry.DefEntry
		want  string
	}{
		{entry("in_parentheses", "", []string{"n", "m"}, spaces("in_parentheses", "(n, m, s, t)")),
			"zz_dims_in_parentheses takes its dimension in the ⟨…⟩ after its name, not in the parentheses"},
		{entry("twice", "", []string{"n", "n"}, spaces("twice", "⟨n, n⟩(s, t)")),
			"Dimensions: n is named twice"},
		{entry("empty_name", "", []string{"n", ""}, spaces("empty_name", "⟨n⟩(m, s, t)")),
			"Dimensions: entry 1 is empty"},
		{entry("also_dim", "n", []string{"n"}, spaces("also_dim", "⟨n⟩(m, s, t)")),
			"Dimensions: n is already declared by Dim"},
		{entry("no_binder", "", []string{"n", "k"}, spaces("no_binder", "⟨n, m⟩(s, t)")),
			"Dimensions: k is not a ∀-binder of the equation"},
		{entry("not_num", "", []string{"n", "s"}, spaces("not_num", "⟨n, m⟩(s, t)")),
			"Dimensions: s is bound at "},
		// The binders the suffix holds are the leading ones.
		{registry.DefEntry{
			Name: "not_leading", Const: "zz_dims_not_leading",
			Type:       "(A → bool) → num → bool",
			Dimensions: []string{"n"},
			Equations:  []string{"∀s:(A → bool). ∀n:num. zz_dims_not_leading⟨s⟩(n) ⇔ n = n ∧ s = s"},
		}, "must be the equation's binders right after its implicit prefix"},
	} {
		got := fmt.Sprint(refusal(tc.entry))
		require.Contains(t, got, "registry.Define("+tc.entry.Name+"): ")
		require.Contains(t, got, tc.want)
	}
}
