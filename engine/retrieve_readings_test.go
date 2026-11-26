package engine

import (
	"context"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// A ring homomorphism preserves zero through its additive group
// homomorphism projection and the group homomorphism's MapOne law.
const ringHomomorphismZeroLeaf = "R:ring_ops(A), S:ring_ops(B), f:(A → B) ⊢ ring_homomorphism(R, S, f) ⇒ f(R.zero) = S.zero"

func retrieveGroups(t *testing.T, e *Engine, sid, gid string) map[string]RetrieveGroup {
	t.Helper()
	res, err := e.Retrieve(context.Background(), sid, &RetrieveRequest{Mode: RetrieveByGoal, GoalID: gid, BudgetMs: 10000})
	require.NoError(t, err)
	groups := map[string]RetrieveGroup{}
	for _, g := range res.Groups {
		groups[g.MatchedVia] = g
	}
	return groups
}

func readingHit(t *testing.T, g RetrieveGroup, law string, through ...string) RetrieveEntry {
	t.Helper()
	for _, re := range g.Entries {
		if re.Entry == law && re.Reading != nil && assert.ObjectsAreEqual(through, re.Reading.Through) {
			return re
		}
	}
	t.Fatalf("%s through %v not among the readings: %+v", law, through, g.Entries)
	return RetrieveEntry{}
}

// TestRetrieveReadings_LawThroughProjectionAtAResidentFact: with the
// homomorphism's fact a hypothesis of the goal, `f(R.zero) = S.zero` is
// met by the group law read through the ring's projection, reported in
// the readings group after the members, with the chain, the fact as its
// premise, and both spellings of the value — the session's `read_at`
// naming the hypothesis by index. The cap is above the number of
// readings the goal meets, so the group is complete.
func TestRetrieveReadings_LawThroughProjectionAtAResidentFact(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	registry.Readables() // the view is walked off the request path; the test waits for it
	sid, gid := bareArithLeaf(t, e, ringHomomorphismZeroLeaf, "strip_imp")
	res, err := e.Retrieve(context.Background(), sid, &RetrieveRequest{Mode: RetrieveByGoal, GoalID: gid, BudgetMs: 10000, MaxPerGroup: 50})
	require.NoError(t, err)
	groups := map[string]RetrieveGroup{}
	for _, g := range res.Groups {
		groups[g.MatchedVia] = g
	}
	assert.Equal(t, retrieveCorpusReadings, res.Groups[len(res.Groups)-1].MatchedVia, "the readings group comes after the members: %+v", res.Groups)

	g, ok := groups[retrieveCorpusReadings]
	require.True(t, ok, "a readings group: %v", groups)
	assert.False(t, g.Truncated)
	hit := readingHit(t, g, "group_homomorphism.MapOne", "ring_homomorphism.AdditiveHomomorphism")
	law, _ := registry.ByName("group_homomorphism.MapOne")
	assert.Equal(t, string(law.Statement().Key()), hit.Key, "the key is the law's own")
	assert.Equal(t, "algebra/group/group_homomorphism", hit.Family)
	assert.Equal(t, corpusMatchApply, hit.Match)
	assert.False(t, hit.Card)
	assert.Equal(t, "∀f:ring_homomorphism(A, B). f(R.zero) = S.zero", hit.Statement, "the reading folds through the root chapter's structure binder")
	require.Len(t, hit.Premises, 1)
	assert.Equal(t, premiseResident, hit.Premises[0].Status)
	assert.Equal(t, "ring_homomorphism(R, S, f)", hit.Premises[0].Statement)
	assert.Equal(t, "group_homomorphism.MapOne.Read(ring_homomorphism.AdditiveHomomorphism.Read(ResidentHyp("+
		"ring_homomorphism(R, S, f))))", hit.Reading.Go)
	zero := 0
	assert.Equal(t, &ReadAtSpec{Key: "ring_homomorphism.AdditiveHomomorphism", ReadAt: &ReadAtSpec{HypIndex: &zero}}, hit.Reading.ReadAt)

	// ring_homomorphism.MapZero states the goal: it is the corpus group's
	// exact hit, and the corpus group lists no reading.
	corpus, ok := groups[retrieveCorpus]
	require.True(t, ok, "a corpus group: %v", groups)
	exact := false
	for _, re := range corpus.Entries {
		assert.Nil(t, re.Reading, "%+v", re)
		if re.Match == corpusMatchExact {
			assert.Equal(t, "ring_homomorphism.MapZero", re.Entry, "%+v", re)
			exact = true
		}
	}
	assert.True(t, exact, "MapZero among the exact hits: %+v", corpus.Entries)

	// The spelling the group reports is the premise `by` takes: it
	// closes the goal.
	step := byReading(t, e, sid, gid, hit.Entry, hit.Reading.ReadAt, nil)
	require.True(t, step.Success, "diagnostics: %+v", step.Diagnostics)
	assert.Equal(t, 0, step.State.NumOpen)
}

// TestRetrieveReadings_FactHeldOnlyOpenedLeavesTheSessionSpellingOut:
// the goal as added, its hypothesis still an implication, holds the
// fact only once opened; the reading applies, its premise is resident
// in the opened form, and `read_at` is not given, since no index of
// the goal names the fact yet.
func TestRetrieveReadings_FactHeldOnlyOpenedLeavesTheSessionSpellingOut(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	registry.Readables()
	sid, gid := bareArithLeaf(t, e, ringHomomorphismZeroLeaf)
	groups := retrieveGroups(t, e, sid, gid)
	hit := readingHit(t, groups[retrieveCorpusReadings], "group_homomorphism.MapOne", "ring_homomorphism.AdditiveHomomorphism")
	require.Len(t, hit.Premises, 1)
	assert.Equal(t, premiseResident, hit.Premises[0].Status)
	assert.Nil(t, hit.Reading.ReadAt)
	assert.Contains(t, hit.Reading.Go, ".Read(ResidentHyp(")
}

// TestRetrieveReadings_NegativeControl: a goal no projection reaches —
// the transfer fixture's — answers as before: the corpus group alone,
// no readings group. Before the view is walked the group is reported
// truncated and empty, and the request does not wait.
func TestRetrieveReadings_NegativeControl(t *testing.T) {
	law := retrieveCorpusFixture().law
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	const goal = "p:bool → bool, q:bool → bool, c:bool, ∀x:bool. p(x) ⇒ q(x), q(¬c) ⊢ p(¬c)"
	registry.Readables()
	res := retrieveGoal(t, e, info.ID, goal)
	require.Len(t, res.Groups, 1, "the corpus group alone: %+v", res.Groups)
	assert.Equal(t, retrieveCorpus, res.Groups[0].MatchedVia)
	corpusHit(t, res, law.Name)

	// A fixture that is no structure law leaves the view as it stands:
	// the next request answers from the walked view.
	stub := func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }
	fam := registry.NewFamily("zz_retrieve_readings_moves", nil)
	fam.Add(registry.ProofEntry{
		Name: "Plain", Build: registry.BuildSpec{Headline: "∀P:(bool → bool). ∀a:bool. P(a) ⇒ P(a) ∨ P(a)", Fn: stub},
	})
	res = retrieveGoal(t, e, info.ID, goal)
	require.Len(t, res.Groups, 1, "%+v", res.Groups)

	// A structure and its law move the view, whose walk restarts in the
	// background: the next request answers at once with the group
	// marked truncated, and the walked view answers as above.
	point := fam.DefineStructure(registry.DefEntry{
		Name: "Point", Const: "zz_rrm_point", Type: "A → bool",
		Equations: []string{"∀e:A. zz_rrm_point(e) ⇔ e = e"},
	})
	trivial, err := point.Statement("e = e").Text()
	require.NoError(t, err)
	fam.Add(registry.ProofEntry{Name: "Trivial", Build: registry.BuildSpec{Headline: trivial, Fn: stub}})
	res = retrieveGoal(t, e, info.ID, goal)
	require.Len(t, res.Groups, 2, "%+v", res.Groups)
	assert.Equal(t, retrieveCorpusReadings, res.Groups[1].MatchedVia)
	assert.True(t, res.Groups[1].Truncated)
	assert.Empty(t, res.Groups[1].Entries)
	registry.Readables()
	res = retrieveGoal(t, e, info.ID, goal)
	require.Len(t, res.Groups, 1, "%+v", res.Groups)
}

// TestRetrieveReadings_AtAnInstanceEntry: the monoid's commutativity
// read through the ring's multiplicative monoid, at the real ring's
// instance entry — `comm_monoid.Comm.Read(comm_ring.MulMonoid.Read(
// real_ring.CommRing))` — meets `x * y = y * x` on ℝ, the instance
// offered by the corpus's facts, and the session spelling names the
// entry.
func TestRetrieveReadings_AtAnInstanceEntry(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	registry.Readables()
	sid, gid := bareArithLeaf(t, e, "x:real, y:real ⊢ x * y = y * x")
	groups := retrieveGroups(t, e, sid, gid)
	hit := readingHit(t, groups[retrieveCorpusReadings], "comm_monoid.Comm", "comm_ring.MulMonoid")
	require.Len(t, hit.Premises, 1)
	assert.Equal(t, premiseEntry, hit.Premises[0].Status)
	assert.Equal(t, "real_ring.CommRing", hit.Premises[0].Entry)
	assert.Equal(t, "comm_monoid.Comm.Read(comm_ring.MulMonoid.Read(real_ring.CommRing))", hit.Reading.Go)
	assert.Equal(t, &ReadAtSpec{Key: "comm_ring.MulMonoid", ReadAt: &ReadAtSpec{Key: "real_ring.CommRing"}}, hit.Reading.ReadAt)

	step := byReading(t, e, sid, gid, hit.Entry, hit.Reading.ReadAt, nil)
	require.True(t, step.Success, "diagnostics: %+v", step.Diagnostics)
	assert.Equal(t, 0, step.State.NumOpen)
}
