package registry_test

// define_deps_test.go — a definition's edges are read off its equation:
// DepEntries joins the declared Deps to the definers of the constants
// the equation spells, ServedDeps — what a build is served — does not,
// and registration refuses a direct or recursive
// definition that names another family's entry in Deps.

import (
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/require"
)

// definedBy is every constant the entries define.
func definedBy(entries []*registry.ProofEntry) map[string]bool {
	out := map[string]bool{}
	for _, e := range entries {
		for _, c := range e.Defines() {
			out[c] = true
		}
	}
	return out
}

func TestDefine_DepEntriesReadOffTheEquation(t *testing.T) {
	fam := registry.NewFamily("zz_define_deps_spelled_test", nil)
	entry := fam.Define(registry.DefEntry{
		Name:      "Twice",
		Const:     "zz_reg_deps_twice",
		Type:      "num → num",
		Equations: []string{"∀n:num. zz_reg_deps_twice(n) = suc(n) + n"},
	})
	require.Empty(t, entry.Deps, "the definition declares no dep")
	defined := definedBy(entry.DepEntries())
	require.True(t, defined["suc"], "the definer of suc is an edge, read off the equation: %v", defined)
	require.True(t, defined[string(dsl.NatPlusMeta.Name())],
		"so is the definer of + at num, an operator the parser builds itself: %v", defined)
	require.False(t, defined["zz_reg_deps_twice"], "the definition is no edge of its own")
	require.Equal(t, entry.DepEntries(), entry.SpelledDeps(),
		"with nothing declared, the edges are the spelled definers")
	require.Empty(t, entry.ServedDeps(), "a build is served none of them: a definition reads nothing")
}

func TestDefine_RefusesAnotherFamilysDep(t *testing.T) {
	fam := registry.NewFamily("zz_define_deps_refused_test", nil)
	defer func() {
		r := recover()
		require.NotNil(t, r, "a definition naming another family's entry in Deps is refused")
		require.Contains(t, fmt.Sprint(r), "a definition's Deps name only entries of its own family")
		require.True(t, strings.Contains(fmt.Sprint(r), peano.Recursion.Entry().Name), "the refusal names the entry")
	}()
	fam.Define(registry.DefEntry{
		Name:      "Thrice",
		Const:     "zz_reg_deps_thrice",
		Type:      "num → num",
		Equations: []string{"∀n:num. zz_reg_deps_thrice(n) = n + n + n"},
		Deps:      []registry.EntryLike{peano.Recursion},
	})
}

func TestDefine_KeepsAnOwnFamilyDep(t *testing.T) {
	fam := registry.NewFamily("zz_define_deps_own_test", nil)
	first := fam.Define(registry.DefEntry{
		Name:      "Once",
		Const:     "zz_reg_deps_once",
		Type:      "num → num",
		Equations: []string{"∀n:num. zz_reg_deps_once(n) = suc(n)"},
	})
	second := fam.Define(registry.DefEntry{
		Name:      "OnceMore",
		Const:     "zz_reg_deps_once_more",
		Type:      "num → num",
		Equations: []string{"∀n:num. zz_reg_deps_once_more(n) = zz_reg_deps_once(suc(n))"},
		Deps:      []registry.EntryLike{first},
	})
	require.Contains(t, second.DepEntries(), first, "the same-family mint stays a declared edge")
	require.Equal(t, first, second.DepEntries()[0], "declared edges come first")
}
