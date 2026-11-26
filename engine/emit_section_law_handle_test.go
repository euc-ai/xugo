package engine

import (
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// compilesInFamily type-checks src as one more file of the family
// package at familyDir (relative to this directory): the member's
// declarations are read by the compiler, which a parse or a string
// match never does — a local bound and not read fails here. The file
// is overlaid, so the family's tree is untouched.
func compilesInFamily(t *testing.T, familyDir, src string) {
	t.Helper()
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	pkgDir, err := filepath.Abs(familyDir)
	require.NoError(t, err)
	member := filepath.Join(t.TempDir(), "zz_member.go")
	require.NoError(t, os.WriteFile(member, []byte(src), 0o644))
	overlay, err := json.Marshal(map[string]map[string]string{
		"Replace": {filepath.Join(pkgDir, "zz_member.go"): member},
	})
	require.NoError(t, err)
	overlayPath := filepath.Join(t.TempDir(), "overlay.json")
	require.NoError(t, os.WriteFile(overlayPath, overlay, 0o644))
	cmd := exec.Command(goBin, "build", "-overlay="+overlayPath, "./"+filepath.ToSlash(familyDir))
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("the emitted member does not compile in its family:\n%s\n--- member: ---\n%s", out, src)
	}
}

// TestEmitSection_AReadingUnderTheLawHandleDeclaresNoLocal: a law read
// under the Law door's hypothesis prints the handle, `Law.Read(h)`, so
// the hypothesis's own text is never written — and the member binds no
// local for it. The structure predicate is held at a second type by a
// claim the proof asserts, which makes its name one a text passes as a
// scope override: a mark made for a text the rendering never prints
// bound `quasi_category := ctx.Const(…)` that nothing read, and the
// family did not compile.
func TestEmitSection_AReadingUnderTheLawHandleDeclaresNoLocal(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := boundSession(t, "simplicial/quasi_category")
	addTextGoal(t, s, "∀X:simplicial_ops(A). quasi_category(X) ⇒ simplicial_set(X)")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	// The predicate at a second carrier type, as a claim closed on itself.
	claim := "∀Y:simplicial_ops(B). quasi_category(Y) ⇒ quasi_category(Y)"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: claim})
	claimed := func(g core.Prop) bool { return strings.HasPrefix(ext.PrintTerm(g.Conclusion()), "∀Y") }
	applyTo(t, e, s, claimed, TacticReq{Type: "strip_quant"})
	stripped := func(g core.Prop) bool { return strings.HasPrefix(ext.PrintTerm(g.Conclusion()), "quasi_category(") }
	applyTo(t, e, s, stripped, TacticReq{Type: "simplify"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
		{Key: "quasi_category.QuasiSimplicialSet", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "quasi_category(X")}}}})
	src := emitSole(t, e, s, "Build_ZzReadUnderHandle")
	require.Contains(t, src, "By(QuasiSimplicialSet.Read(h))", "--- source: ---\n%s", src)
	require.NotContains(t, src, "quasi_category := ctx.Const(", "no local is bound for a hypothesis only the handle spells\n--- source: ---\n%s", src)
	compilesInFamily(t, "../library/proofs/simplicial/quasi_category", src)
}
