package engine

import (
	"context"
	"go/parser"
	"go/token"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// emitReading applies tactic to stmt (after the strips), closes what it
// leaves with `simplify`, and emits the section into `family`.
func emitReading(t *testing.T, e *Engine, family, stmt string, strips []string, tactic TacticReq) string {
	t.Helper()
	sid, gid := bareArithLeaf(t, e, stmt, strips...)
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: tactic})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	for _, left := range res.Produced {
		closed, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: left.GoalID, Tactic: TacticReq{Type: "simplify"}})
		require.NoError(t, err)
		require.True(t, closed.Success, "the residual %s: %+v", left.GoalID, closed.Diagnostics)
	}
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: sid, Section: 0, FuncName: "Build_READING", Family: family})
	require.NoError(t, err, "emit, and the re-run that collects the section's CNF keys")
	if _, perr := parser.ParseFile(token.NewFileSet(), "reading.go", out.Go, parser.AllErrors); perr != nil {
		t.Fatalf("emitted source does not parse: %v\n--- source: ---\n%s", perr, out.Go)
	}
	return out.Go
}

// TestEmitSection_ReadingRendersAsRead: a session premise or rule that
// is a law read at an instance emits as the Go value it is —
// `Law.Read(instance)` — with the instance an entry variable, the
// resident hypothesis it is under, or a reading; and the section's CNF
// collection re-runs the recorded composite, a reading under a
// hypothesis re-derived from the record.
func TestEmitSection_ReadingRendersAsRead(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	zero := 0
	law := "comm_ring.MulLeftZero"
	by := func(l LemmaWithSpec) TacticReq { return TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{l}} }

	t.Run("by, at an instance entry", func(t *testing.T) {
		src := emitReading(t, e, "real/real_field", "x:real ⊢ &0 * x = &0", nil,
			by(LemmaWithSpec{Key: law, ReadAt: &ReadAtSpec{Key: "real_ring.CommRing"}}))
		assert.Contains(t, src, "By(comm_ring.MulLeftZero.Read(real_ring.CommRing))", "--- source: ---\n%s", src)
	})
	t.Run("by, grounded", func(t *testing.T) {
		src := emitReading(t, e, "real/real_field", "x:real ⊢ &0 * x = &0", nil,
			by(LemmaWithSpec{Key: law, ReadAt: &ReadAtSpec{Key: "real_ring.CommRing"}, TermSpecialize: map[string]string{"x": "x"}}))
		assert.Contains(t, src, "By(At(comm_ring.MulLeftZero.Read(real_ring.CommRing), ", "--- source: ---\n%s", src)
	})
	t.Run("by, at a reading", func(t *testing.T) {
		src := emitReading(t, e, "real/real_field", "x:real ⊢ &0 * x = &0", nil,
			by(LemmaWithSpec{Key: law, ReadAt: &ReadAtSpec{Key: "field.Ring", ReadAt: &ReadAtSpec{Key: "real_field.Field"}}}))
		assert.Contains(t, src, "By(comm_ring.MulLeftZero.Read(field.Ring.Read(Field)))", "--- source: ---\n%s", src)
	})
	// The hypothesis a reading is under, stripped first, is the closure's
	// Fact parameter (emit_signature.go), and the reading reads at it.
	t.Run("by, under a resident hypothesis", func(t *testing.T) {
		src := emitReading(t, e, "algebra/field/field", readingRingLeaf, []string{"strip_imp"},
			by(LemmaWithSpec{Key: law, ReadAt: &ReadAtSpec{HypIndex: &zero}}))
		assert.Contains(t, src, "func(a *Argument, h Fact) {", "--- source: ---\n%s", src)
		assert.Contains(t, src, "By(comm_ring.MulLeftZero.Read(h))", "--- source: ---\n%s", src)
		assert.Equal(t, 0, strings.Count(src, "ResidentHyp("),
			"the hypothesis the reading is under is the closure's parameter, not a second premise\n--- source: ---\n%s", src)
		assert.NotContains(t, src, "TODO", "--- source: ---\n%s", src)
	})
	t.Run("by, whole law under a resident hypothesis", func(t *testing.T) {
		stmt := "R:ring_ops(A) ⊢ comm_ring(R) ⇒ ∀x:A. R.zero * x = R.zero"
		src := emitReading(t, e, "algebra/field/field", stmt, []string{"strip_imp"},
			by(LemmaWithSpec{Key: law, ReadAt: &ReadAtSpec{HypIndex: &zero}}))
		assert.Contains(t, src, "By(comm_ring.MulLeftZero.Read(h))", "--- source: ---\n%s", src)
		assert.Equal(t, 0, strings.Count(src, "ResidentHyp("), "the reading reads at the closure's parameter")
	})
	t.Run("simp_with, at an instance entry", func(t *testing.T) {
		src := emitReading(t, e, "real/real_field", "x:real, y:real ⊢ &0 * x + y = &0 + y", nil, TacticReq{
			Type:       "simp_with",
			WithLemmas: []LemmaWithSpec{{Key: law, ReadAt: &ReadAtSpec{Key: "real_ring.CommRing"}}},
		})
		assert.Contains(t, src, "Simp(Fwd(comm_ring.MulLeftZero.Read(real_ring.CommRing)))", "--- source: ---\n%s", src)
	})
	t.Run("simp_with, under a resident hypothesis", func(t *testing.T) {
		src := emitReading(t, e, "algebra/field/field", readingRingLeaf, []string{"strip_imp"}, TacticReq{
			Type:       "simp_with",
			WithLemmas: []LemmaWithSpec{{Key: law, ReadAt: &ReadAtSpec{HypIndex: &zero}}},
		})
		assert.Contains(t, src, "Simp(Fwd(comm_ring.MulLeftZero.Read(h)))", "--- source: ---\n%s", src)
	})
}
