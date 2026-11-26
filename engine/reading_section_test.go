package engine

import (
	"context"
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// reading_section_test.go — a proved section of the session, stated
// over the structure binder, is a law `read_at` reads at an instance:
// `{"key": <the section's root id>, "read_at": …}`, the Go
// `Read(<section>, instance)`. Measured: `read_at` took a registry key
// only, so a section proved in session could not be read at a bundle
// statement (serre_duality.DualizingIsLattice).

// sectionLawSession is a session bound to the field chapter whose
// section 0 — `∀R:ring_ops(A). comm_ring(R) ⇒ ∀x:A. R.zero * (x * x) =
// R.zero` — is proved, and whose section 1, the law at the point y * y,
// is open after its strips: its resident ring fact is what the law is
// read at.
func sectionLawSession(t *testing.T) (*Engine, *Session) {
	t.Helper()
	e, s := boundSession(t, "algebra/field/field")
	addStatement(t, s, "∀R:ring_ops(A). comm_ring(R) ⇒ ∀x:A. R.zero * (x * x) = R.zero")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
		{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "comm_ring(")}}}})
	require.True(t, s.sections[0].root.Proved(), "section 0 is proved")
	addStatement(t, s, "∀R:ring_ops(A). ∀y:A. comm_ring(R) ⇒ R.zero * ((y * y) * (y * y)) = R.zero")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	return e, s
}

// sectionIDs are the two ids a section's root is named by: the one
// add-goal returned and the one inspect prints once it is closed.
func sectionIDs(s *Session, k int) (open, closed string) {
	root := s.sections[k].root
	return fmt.Sprintf("s%d_g%s", k, shortKey(root.Goal)), closedNodeID(k, root.Goal)
}

// TestReadAt_AProvedSectionIsTheLaw: a `by` premise reads section 0 at
// the resident ring fact, bare and grounded, by either id;
// and the member emits the section as a local Lemma read by the free
// function, `Read(lemma1, …)`, which compiles and replays: the Lemma's
// text and the headline each bind their own record, beside the `R₀` the
// strips declare at script scope, and the doors read a closed text
// closed (dsl.ParsePropTextAtDoor).
func TestReadAt_AProvedSectionIsTheLaw(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	for name, c := range map[string]struct {
		closedID bool
		table    map[string]string
	}{
		"bare, by the add-goal id":   {},
		"bare, by the closed id":     {closedID: true},
		"grounded, by the closed id": {closedID: true, table: map[string]string{"x": "y₀ * y₀"}},
	} {
		t.Run(name, func(t *testing.T) {
			e, s := sectionLawSession(t)
			openID, closedID := sectionIDs(s, 0)
			key := openID
			if c.closedID {
				key = closedID
			}
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
				{Key: key, ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "comm_ring(")}, TermSpecialize: c.table}}})
			require.True(t, s.sections[1].root.Proved(), "section 1 closes on the section read at its ring")
		})
	}

	t.Run("lemma, grounded", func(t *testing.T) {
		// The grounded reading is the goal: its install closes it, as
		// Go's witnessed Cite does.
		e, s := sectionLawSession(t)
		_, closedID := sectionIDs(s, 0)
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "lemma", LemmaKey: closedID,
			ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "comm_ring(")}, TermSpecialize: map[string]string{"x": "y₀ * y₀"}})
		require.True(t, s.sections[1].root.Proved(), "the grounded reading closes section 1")
	})

	e, s := sectionLawSession(t)
	_, closedID := sectionIDs(s, 0)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
		{Key: closedID, ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "comm_ring(")}}}})
	const pkg = "zzsectionread"
	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: s.ID, Section: 1, FuncName: "Build_ZzSectionRead", Family: emitScratchFamily(pkg), IncludePrior: []int{0},
	})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, "lemma1 := ctx.Lemma(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "Read(lemma1, ", "the section is read by the free function\n--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "TODO", "--- source: ---\n%s", out.Go)
	// R₀ is the lemma's bundle component and the theorem's term
	// parameter: each closure binds it, and the script declares nothing.
	assert.Contains(t, out.Go, "func(a *Argument, R Fact) {", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "func(a *Argument, R *Expr[RingOps[A]], y *Expr[A], h Fact) {", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "ctx.Var(", "--- source: ---\n%s", out.Go)
	replayEmittedWithPhantoms(t, pkg, "ZzSectionRead", out.Go, "package "+pkg+`

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
)

type RingOps[X TypePhantom] = module_record.RingOps[X]
`)
}

// TestReadAt_ASectionLawRefusals: what a section key is not — a
// section still open, and a node of a section that is not its root.
func TestReadAt_ASectionLawRefusals(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := sectionLawSession(t)
	openOne, _ := sectionIDs(s, 1)
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	for key, want := range map[string]string{
		openOne:                "section 1 (" + openOne + ") is still open",
		"s0_gprop_00000000000": "is a node inside section 0, not the section",
	} {
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: TacticReq{
			Type: "by", WithLemmas: []LemmaWithSpec{{Key: key, ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "comm_ring(")}}},
		}})
		if err == nil {
			require.False(t, res.Success, "%s is refused", key)
			err = fmt.Errorf("%v", res.Diagnostics)
		}
		assert.Contains(t, err.Error(), want, "the refusal of %s", key)
	}
}
