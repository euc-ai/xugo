package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestDefine_DirectEndToEnd drives the definition move through the
// session surface: define a boolean constant from its equation text,
// get back a PROVED definition section, and — the scope-injection
// claim — parse a later statement mentioning the new constant under
// strict resolution with no declaration plumbing.
func TestDefine_DirectEndToEnd(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	res, err := e.Define(&DefineRequest{
		SessionID: info.ID,
		Recursive: &DefineRecursive{
			Name:      "zz_xor",
			Type:      "bool → bool → bool",
			Equations: []string{"∀p q:bool. zz_xor(p, q) ⇔ (p ∨ q) ∧ ¬(p ∧ q)"},
		},
	})
	require.NoError(t, err)
	require.Equal(t, "zz_xor", res.Defined)
	require.Equal(t, "direct", res.Shape)
	require.True(t, strings.HasPrefix(res.Key, "prop_"), "key = %q", res.Key)
	require.Contains(t, res.Characterizing, "zz_xor")

	// The definition section is proved on return.
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	require.Equal(t, res.Section, len(s.sections)-1)
	require.True(t, s.sections[res.Section].root.Proved(),
		"the definition section must be proved on return")

	// Scope injection is free: a later statement naming zz_xor parses
	// under STRICT resolution through the same env registry the mint
	// fed — no declaration, no vocab plumbing.
	later := dsl.ParsePropTextInScope(
		"∀p:bool. zz_xor(p, p) ⇔ ⊥",
		&dsl.ParseScope{
			ConstResolver:    envConstResolver(s.env),
			StrictResolution: true,
		})
	require.Empty(t, later.Errors,
		"a post-define statement must resolve the new constant strictly")

	// emit-section renders the definition section 1:1 as
	// family.Define(registry.DefEntry{…}) under the Family profile —
	// transcript A9's leg for the define shape.
	emit, err := e.EmitSection(&EmitSectionRequest{
		SessionID:    info.ID,
		Section:      res.Section,
		FuncName:     "Build_XorDef",
		Family:       "zz_fam",
		IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted define member:\n%s", emit.Go)
	require.Contains(t, emit.Go, "family.Define(registry.DefEntry{")
	require.Contains(t, emit.Go, `Const: "zz_xor"`)
	require.Contains(t, emit.Go, "Equations: []string{")
	require.Contains(t, emit.Go, "zz_xor(p, q)")

	// The one-door invariant, other direction: the SAME name cannot be
	// defined twice — exclusive registration errors, never shadows.
	_, err = e.Define(&DefineRequest{
		SessionID: info.ID,
		Recursive: &DefineRecursive{
			Name:      "zz_xor",
			Type:      "bool → bool → bool",
			Equations: []string{"∀p q:bool. zz_xor(p, q) ⇔ p ∧ q"},
		},
	})
	require.Error(t, err)
	require.Contains(t, err.Error(), "already names a constant")
}

// TestDefine_Rejections: the door's error surface — each rejection
// names its repair and leaves the session without a new section.
func TestDefine_Rejections(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	for _, tc := range []struct {
		name string
		req  *DefineRequest
		want string
	}{
		{
			"no payload",
			&DefineRequest{SessionID: info.ID},
			"requires a payload",
		},
		{
			"no recursion schema for the carrier",
			&DefineRequest{SessionID: info.ID, Recursive: &DefineRecursive{
				Name: "zz_f2", Type: "bool → bool",
				Equations: []string{"zz_f2(⊤) ⇔ ⊤", "zz_f2(⊥) ⇔ ⊥"},
			}},
			"no recursion schema",
		},
		{
			"undeclared body name",
			&DefineRequest{SessionID: info.ID, Recursive: &DefineRecursive{
				Name: "zz_g", Type: "bool → bool",
				Equations: []string{"∀p:bool. zz_g(p) ⇔ p ∧ oops"},
			}},
			"oops",
		},
		{
			"recursion on a bare variable pattern",
			&DefineRequest{SessionID: info.ID, Recursive: &DefineRecursive{
				Name: "zz_h", Type: "bool → bool",
				Equations: []string{"∀p:bool. zz_h(p) ⇔ ¬zz_h(p)"},
			}},
			"no equation carries a constructor pattern",
		},
	} {
		before := len(s.sections)
		_, err := e.Define(tc.req)
		if err == nil {
			t.Errorf("%s: expected an error", tc.name)
			continue
		}
		if !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: error %q does not mention %q", tc.name, err.Error(), tc.want)
		}
		if got := len(s.sections); got != before {
			t.Errorf("%s: a rejected define must not leave a section (%d → %d)",
				tc.name, before, got)
		}
	}
}
