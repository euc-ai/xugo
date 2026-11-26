package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// The ring's absorption law at a free record, its structure fact the
// hypothesis: the shape a chapter stated over a structure proves in.
const readingRingLeaf = "R:ring_ops(A), x:A ⊢ comm_ring(R) ⇒ R.zero * x = R.zero"

// byReading applies a session `by` whose one premise is the law read at
// the instance, optionally grounded.
func byReading(t *testing.T, e *Engine, sid, gid, law string, at *ReadAtSpec, table map[string]string) *StepResult {
	t.Helper()
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: law, ReadAt: at, TermSpecialize: table}}},
	})
	require.NoError(t, err)
	return res
}

// recordedBy is the `by` composite the session's one section recorded.
func recordedBy(t *testing.T, e *Engine, sid string) *proof.ByProto {
	t.Helper()
	s, err := e.getSession(sid)
	require.NoError(t, err)
	detailed := s.sections[0].root.DetailedProofProto()
	require.NotNil(t, detailed)
	for _, st := range detailed.GetSteps() {
		if by, ok := st.Step.(*proof.StepProto_By); ok {
			return by.By
		}
	}
	t.Fatalf("no `by` composite recorded")
	return nil
}

// TestByTactic_ReadingAtAnInstanceEntry: a structure law read at the
// carrier's instance entry is a `by` premise — the Go
// `comm_ring.MulLeftZero.Read(real_ring.CommRing)` — and closes what
// the law alone cannot, the instance being nowhere in the context. The
// record says what the premise was read from.
func TestByTactic_ReadingAtAnInstanceEntry(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	const stmt = "x:real ⊢ &0 * x = &0"
	at := &ReadAtSpec{Key: "real_ring.CommRing"}

	t.Run("the law alone does not close it", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, stmt)
		res := byReading(t, e, sid, gid, "comm_ring.MulLeftZero", nil, nil)
		require.False(t, res.Success, "the negative control: without the instance the law's hypothesis is unsupplied")
	})
	t.Run("bare", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, stmt)
		res := byReading(t, e, sid, gid, "comm_ring.MulLeftZero", at, nil)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, 0, res.State.NumOpen)

		by := recordedBy(t, e, sid)
		require.Len(t, by.GetPremises(), 1)
		reading := by.GetPremises()[0].GetReading()
		require.NotNil(t, reading, "the premise records what it was read from")
		assert.NotNil(t, reading.GetLaw())
		assert.NotNil(t, reading.GetInstance())
		assert.Nil(t, reading.GetUnder())
		assert.False(t, by.GetPremises()[0].GetDerived(), "at an entry the reading is a named premise")
	})
}

// TestByTactic_ReadingUnderAResidentHypothesis: the instance may be a
// resident structure fact of the goal — the Go `MulLeftZero.Read(ring)`
// in a chapter stated over the structure. The reading is that
// hypothesis's consequence, derived by the kernel and asserted inside
// the leaf with the hypothesis kept beside it; the author lists
// neither.
func TestByTactic_ReadingUnderAResidentHypothesis(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	zero := 0
	at := &ReadAtSpec{HypIndex: &zero}

	t.Run("bare", func(t *testing.T) {
		sid, root := bareArithLeaf(t, e, readingRingLeaf)
		stripped, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: root, Tactic: TacticReq{Type: "strip_imp"}})
		require.NoError(t, err)
		gid := stripped.Produced[0].GoalID
		res := byReading(t, e, sid, gid, "comm_ring.MulLeftZero", at, nil)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, 0, res.State.NumOpen)

		by := recordedBy(t, e, sid)
		var reading *proof.ReadingProto
		for _, p := range by.GetPremises() {
			if p.GetReading() != nil {
				reading = p.GetReading()
				assert.True(t, p.GetDerived(), "a bare reading under a hypothesis is asserted, its claim closed from the derived sequent")
			}
		}
		require.NotNil(t, reading)
		assert.NotNil(t, reading.GetUnder())
		assert.Nil(t, reading.GetInstance())
	})
	t.Run("grounded", func(t *testing.T) {
		sid, gid := bareArithLeaf(t, e, readingRingLeaf, "strip_imp")
		res := byReading(t, e, sid, gid, "comm_ring.MulLeftZero", at, map[string]string{"x": "x"})
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		assert.Equal(t, 0, res.State.NumOpen)
	})
}

// TestByTactic_ReadingRefusals: what a reading is not.
func TestByTactic_ReadingRefusals(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	seven := 7
	for _, row := range []struct {
		name string
		spec LemmaWithSpec
		want string
	}{
		{"an instance of another structure",
			LemmaWithSpec{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{Key: "real_field.Field"}},
			"the law's hypothesis is"},
		{"no such hypothesis",
			LemmaWithSpec{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: &seven}},
			"out of range"},
		{"two instances at once",
			LemmaWithSpec{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: &seven, Key: "real_ring.CommRing"}},
			"ONE instance"},
		{"a law given as text",
			LemmaWithSpec{Text: "∀x:real. x = x", ReadAt: &ReadAtSpec{Key: "real_ring.CommRing"}},
			"by its key, or a proved section of this session by its id"},
		{"type_specialize",
			LemmaWithSpec{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{Key: "real_ring.CommRing"},
				TypeSpecialize: map[string]string{"A": "real"}},
			"the instance's"},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, "x:real ⊢ &0 * x = &0")
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{row.spec}}})
			require.NoError(t, err)
			require.False(t, res.Success)
			require.NotEmpty(t, res.Diagnostics)
			assert.Contains(t, res.Diagnostics[0].Message, row.want)
		})
	}
}

// TestByTactic_ReadingWithALooseLetterIsTheLawBesideTheHypothesis: a law
// that carries a type letter no component fixes
// (vec_space.SubspaceIterate's index type, beside the ring's carrier)
// cannot be used as a reading under a resident hypothesis — the
// reading would be a fact of the leaf, its letters rigid. The premise
// is then the law itself cited beside the hypothesis, which is what Go
// makes of `SubspaceIterate.Read(ring)` in a By, and the record keeps
// what it was read at, so emit spells that reading back; a hypothesis
// the author already listed is not added twice.
func TestByTactic_ReadingWithALooseLetterIsTheLawBesideTheHypothesis(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, readingRingLeaf, "strip_imp")
	s, err := e.getSession(sid)
	require.NoError(t, err)
	goal := s.goalIndex[gid].node.Goal
	zero := 0
	loose := LemmaWithSpec{Key: "vec_space.SubspaceIterate", ReadAt: &ReadAtSpec{HypIndex: &zero}}

	specs, cert, source, err := e.byReadingPremises(s, goal, loose, nil)
	require.NoError(t, err)
	require.Len(t, specs, 2, "the law, then the hypothesis it is read under")
	entry, ok := registryEntry("vec_space.SubspaceIterate")
	require.True(t, ok)
	assert.True(t, specs[0].Install.AlphaEquals(entry.Statement().Prop), "the law as stated, polymorphic")
	assert.False(t, specs[0].ReadingUnder)
	require.NotNil(t, specs[0].Reading, "the record keeps what the law was read at")
	assert.True(t, specs[0].Reading.Law.AlphaEquals(entry.Statement().Prop))
	assert.True(t, specs[0].Reading.Under.AlphaEquals(goal.Hyp(0)))
	assert.True(t, specs[1].Resident)
	assert.True(t, specs[1].Install.Conclusion().AlphaEquals(goal.Hyp(0)))
	assert.Nil(t, cert, "the law's claim certifies against its entry")
	require.NotNil(t, source)

	specs, _, _, err = e.byReadingPremises(s, goal, loose, []proof.ByPremiseSpec{specs[1]})
	require.NoError(t, err)
	assert.Len(t, specs, 1, "the hypothesis is listed already")

	// The control: a law with no loose letter is read under the hypothesis.
	specs, cert, _, err = e.byReadingPremises(s, goal,
		LemmaWithSpec{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: &zero}}, nil)
	require.NoError(t, err)
	require.Len(t, specs, 1)
	assert.True(t, specs[0].ReadingUnder)
	assert.NotNil(t, cert)
}

// TestAutoWith_RefusesAReading: auto_with installs entries as stated.
func TestAutoWith_RefusesAReading(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, "x:real ⊢ &0 * x = &0")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type:       "auto_with",
		WithLemmas: []LemmaWithSpec{{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{Key: "real_ring.CommRing"}}},
	}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "read_at")
}

// TestSimpWith_ReadingFiresWhereTheLawBesideItsInstanceDoesNot: the
// field's `inv(zero) = zero` at ℂ. As two rules — the law and the
// instance — nothing fires: the law's redex is `inv(zero)` at a zero
// the matcher has to be told. As the law read at the instance it is
// the equation at ℂ's own zero, and rewrites.
func TestSimpWith_ReadingFiresWhereTheLawBesideItsInstanceDoesNot(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	const stmt = "z:complex ⊢ complex_add(complex_inv(complex_of_real(&0)), z) = complex_add(complex_of_real(&0), z)"
	simp := func(rules ...LemmaWithSpec) *StepResult {
		sid, gid := bareArithLeaf(t, e, stmt)
		res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "simp_with", WithLemmas: rules}})
		require.NoError(t, err)
		return res
	}
	assert.False(t, simp(LemmaWithSpec{Key: "field.InvZero"}, LemmaWithSpec{Key: "complex_field.Field"}).Success,
		"the control: the law beside its instance rewrites nothing here")
	read := simp(LemmaWithSpec{Key: "field.InvZero", ReadAt: &ReadAtSpec{Key: "complex_field.Field"}})
	assert.True(t, read.Success, "diagnostics: %+v", read.Diagnostics)
}
