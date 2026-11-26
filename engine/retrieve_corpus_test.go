package engine

import (
	"context"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
)

// The fixture chapter: a transfer law with a predicate head, a bare
// fact, a card (a member stated without a proof), and a member citing
// the law.
//
// Registered LAZILY, on the first retrieve test that reads it: the
// proof registry is process-global and never forgets an entry, so a
// fixture registered at package init would sit in every `cards` view
// and answer every key lookup of the defer/cards tests in this package
// (a landed card they did not mint, a statement they expect unproved).
// Its statements are also spelled in
// shapes no other fixture in the package uses — `(a ⇔ b) ⇒ P(a)`, not
// the defer tests' disjunct and conjunct cards — and none normalizes
// to ⊤, so the two fixtures share no key even when both are live.
type retrieveCorpusEntries struct{ law, fact, card, citer, both, probe, freeFact *registry.ProofEntry }

var retrieveCorpusFixture = sync.OnceValue(func() retrieveCorpusEntries {
	var law, fact, card, citer, both, probe, freeFact *registry.ProofEntry
	stub := registry.Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	// Citer's dependency on Transfer is a recorded one, as a proved
	// member's is.
	fam := registry.NewFamily("zz_retrieve_corpus", recordedDepsBlob(map[string][]string{
		"zz_retrieve_corpus.Citer": {"zz_retrieve_corpus.Transfer"},
	}))
	// Every corpus entry carries its own key (a gate pastes it); the
	// fixture mints each one the same way, from the statement.
	env := testEnv()
	keyOf := func(text string) string {
		return string(registry.NewStatement(fam.ParseScript(env).MakePropText(text)).Key())
	}
	law = fam.Add(registry.ProofEntry{
		Name: "Transfer",
		// Stated as the CONVERSE transfer — a shape for retrieval, not a
		// theorem (the Build is a stub): the plain transfer normalizes to
		// ⊤, and a ⊤-keyed entry collides with every other tautological
		// fixture in the package.
		Key:   keyOf("∀P Q:(bool → bool). (∀x:bool. P(x) ⇒ Q(x)) ⇒ ∀a:bool. Q(a) ⇒ P(a)"),
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀P Q:(bool → bool). (∀x:bool. P(x) ⇒ Q(x)) ⇒ ∀a:bool. Q(a) ⇒ P(a)"},
	})
	fact = fam.Add(registry.ProofEntry{
		Name:  "PointwiseAll",
		Key:   keyOf("P:bool → bool ⊢ ∀a:bool. P(a)"),
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "P:bool → bool ⊢ ∀a:bool. P(a)"},
	})
	card = fam.Add(registry.ProofEntry{
		Name:  "Card",
		Key:   keyOf("∀P:(bool → bool). ∀x y:bool. (x ⇔ y) ⇒ P(x) ∧ P(y)"),
		Build: fam.Card("∀P:(bool → bool). ∀x y:bool. (x ⇔ y) ⇒ P(x) ∧ P(y)", "both sides of an equivalence under P"),
	})
	citer = fam.Add(registry.ProofEntry{
		Name:  "Citer",
		Key:   keyOf("P:bool → bool ⊢ ∀a b:bool. P(a) ⇒ P(b)"),
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "P:bool → bool ⊢ ∀a b:bool. P(a) ⇒ P(b)"},
	})
	both = fam.Add(registry.ProofEntry{
		Name:  "Both",
		Key:   keyOf("∀P Q:(bool → bool). ∀a:bool. Q(a) ⇒ P(a) ∧ Q(a)"),
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀P Q:(bool → bool). ∀a:bool. Q(a) ⇒ P(a) ∧ Q(a)"},
	})
	probe = fam.Add(registry.ProofEntry{
		Name:  "Probe",
		Key:   keyOf("∀z:num. suc(z) = 1 ⇒ ∀a:num. a + 0 = 0 + a"),
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀z:num. suc(z) = 1 ⇒ ∀a:num. a + 0 = 0 + a"},
	})
	// Stated over declared free variables: a member, not a fact.
	freeFact = fam.Add(registry.ProofEntry{
		Name:  "FreeFact",
		Key:   keyOf("m:num ⊢ suc(m) = 1"),
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "m:num ⊢ suc(m) = 1"},
	})
	// The corpus's statements are read here, as NewEngine reads them at
	// a server's start, and not in the first retrieve: a retrieve's
	// budget is the scan's, and the scan reads prepared statements.
	registry.ReadStatements()
	return retrieveCorpusEntries{law, fact, card, citer, both, probe, freeFact}
})

// recordedDepsBlob is a family blob holding only dependency rows —
// member name to the entries it reads — the record a fixture's proved
// member stands on, since a proved member declares no Deps.
func recordedDepsBlob(rows map[string][]string) []byte {
	cache := &proof.CNFCache{MemberDeps: map[string]*proof.EntryList{}}
	for member, deps := range rows {
		cache.MemberDeps[member] = &proof.EntryList{Names: deps}
	}
	blob, err := proto.MarshalOptions{Deterministic: true}.Marshal(cache)
	if err != nil {
		panic(err)
	}
	return blob
}

func retrieveGoal(t *testing.T, e *Engine, sid, goalText string) *RetrieveResult {
	t.Helper()
	s, _ := e.getSession(sid)
	gid := lineageText(t, s, goalText)
	res, err := e.Retrieve(context.Background(), sid, &RetrieveRequest{Mode: RetrieveByGoal, GoalID: gid})
	require.NoError(t, err)
	return res
}

func corpusHit(t *testing.T, res *RetrieveResult, entry string) RetrieveEntry {
	t.Helper()
	require.NotEmpty(t, res.Groups, "no groups at all")
	g := res.Groups[0]
	require.Equal(t, retrieveCorpus, g.MatchedVia, "the corpus group comes first")
	for _, re := range g.Entries {
		if re.Entry == entry {
			return re
		}
	}
	t.Fatalf("%s not among the corpus hits: %+v", entry, g.Entries)
	return RetrieveEntry{}
}

func TestRetrieveCorpus_ApplyReadsWitnessesAndPremises(t *testing.T) {
	law := retrieveCorpusFixture().law
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)

	res := retrieveGoal(t, e, info.ID, "p:bool → bool, q:bool → bool, c:bool, ∀x:bool. p(x) ⇒ q(x), q(¬c) ⊢ p(¬c)")
	hit := corpusHit(t, res, law.Name)
	assert.Equal(t, corpusMatchApply, hit.Match)
	assert.Equal(t, "zz_retrieve_corpus", hit.Family)
	assert.Equal(t, law.Statement().Key(), core.PropKey(hit.Key), "the key is the entry's own")
	require.Len(t, hit.Witnesses, 3, "P, Q and a are pinned: %+v", hit.Witnesses)
	assert.Equal(t, []RetrieveWitness{{"P", "p"}, {"Q", "q"}, {"a", "¬c"}}, hit.Witnesses)
	require.Len(t, hit.Premises, 2)
	for _, p := range hit.Premises {
		assert.Equal(t, premiseResident, p.Status, "%s", p.Statement)
	}
}

func TestRetrieveCorpus_ExactByKey(t *testing.T) {
	fact := retrieveCorpusFixture().fact
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)

	res := retrieveGoal(t, e, info.ID, "P:bool → bool ⊢ ∀a:bool. P(a)")
	hit := corpusHit(t, res, fact.Name)
	assert.Equal(t, corpusMatchExact, hit.Match)
	assert.Empty(t, hit.Witnesses)
	assert.Equal(t, fact.Name, res.Groups[0].Entries[0].Entry, "exact hits lead the group")
}

// A card applies like any member and is flagged as one: a close
// standing on it stands on a card.
func TestRetrieveCorpus_CardAppliesAndIsFlagged(t *testing.T) {
	card := retrieveCorpusFixture().card
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)

	res := retrieveGoal(t, e, info.ID, "p:bool → bool, u:bool, v:bool ⊢ p(u) ∧ p(v)")
	hit := corpusHit(t, res, card.Name)
	assert.Equal(t, corpusMatchApply, hit.Match)
	assert.True(t, hit.Card, "the member is a card")
	assert.Equal(t, []RetrieveWitness{{"P", "p"}, {"x", "u"}, {"y", "v"}}, hit.Witnesses)
	require.Len(t, hit.Premises, 1)
	assert.Equal(t, premiseOpen, hit.Premises[0].Status)
	assert.Contains(t, hit.Premises[0].Statement, "⇔")

	res = retrieveGoal(t, e, info.ID, "p:bool → bool, u:bool, v:bool, u ⇔ v ⊢ p(u) ∧ p(v)")
	hit = corpusHit(t, res, card.Name)
	assert.Equal(t, corpusMatchExact, hit.Match, "the goal under its hypothesis is the card's statement")
	assert.True(t, hit.Card)
}

func TestRetrieveCorpus_NameAndRelated(t *testing.T) {
	law, citer := retrieveCorpusFixture().law, retrieveCorpusFixture().citer
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	ctx := context.Background()

	res, err := e.Retrieve(ctx, "", &RetrieveRequest{Mode: RetrieveByName, NamePattern: "zz_retrieve_corpus.tr"})
	require.NoError(t, err)
	require.Len(t, res.Groups, 1)
	require.Len(t, res.Groups[0].Entries, 1)
	assert.Equal(t, law.Name, res.Groups[0].Entries[0].Entry)

	res, err = e.Retrieve(ctx, "", &RetrieveRequest{Mode: RetrieveByRelated, RelatedTo: law.Name})
	require.NoError(t, err)
	require.Len(t, res.Groups, 1, "the law cites nothing; one group of dependents")
	assert.Equal(t, retrieveCorpusDependents, res.Groups[0].MatchedVia)
	require.Len(t, res.Groups[0].Entries, 1)
	assert.Equal(t, citer.Name, res.Groups[0].Entries[0].Entry)

	res, err = e.Retrieve(ctx, "", &RetrieveRequest{Mode: RetrieveByRelated, RelatedTo: citer.Name})
	require.NoError(t, err)
	require.Len(t, res.Groups, 1)
	assert.Equal(t, retrieveCorpusDeps, res.Groups[0].MatchedVia)
	assert.Equal(t, law.Name, res.Groups[0].Entries[0].Entry)
}

// A lemma slot names a member by its registered name or its own key
// (registryEntry), and nothing else resolves.
func TestRetrieveCorpus_RegistryEntryResolves(t *testing.T) {
	law, card := retrieveCorpusFixture().law, retrieveCorpusFixture().card
	entry, ok := registryEntry(card.Name)
	require.True(t, ok)
	assert.Same(t, card, entry)

	entry, ok = registryEntry(string(law.Statement().Key()))
	require.True(t, ok, "an entry's own key resolves")
	assert.Same(t, law, entry)

	_, ok = registryEntry("zz_retrieve_corpus.Nobody")
	assert.False(t, ok)
}

func TestRetrieveCorpus_ReadsAClosedGoalOpened(t *testing.T) {
	law := retrieveCorpusFixture().law
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)

	// The goal as add-goal states it: ∀-closed, its premises still
	// implications — and an INSTANCE of the law (the point is ¬c), not
	// the law itself, which the exact group would read by key.
	res := retrieveGoal(t, e, info.ID, "p:bool → bool, q:bool → bool ⊢ ∀c:bool. (∀x:bool. p(x) ⇒ q(x)) ⇒ q(¬c) ⇒ p(¬c)")
	hit := corpusHit(t, res, law.Name)
	assert.Equal(t, corpusMatchApply, hit.Match)
	assert.Equal(t, []RetrieveWitness{{"P", "p"}, {"Q", "q"}, {"a", "¬c"}}, hit.Witnesses)
	require.Len(t, hit.Premises, 2)
	for _, p := range hit.Premises {
		assert.Equal(t, premiseResident, p.Status, "%s is a premise of the opened goal", p.Statement)
	}
}

// A law whose structure binder the goal spells only through its
// fields reads with the bare fact a member states — the premise `by`
// would name. The case is the corpus's own (the engine test binary
// links the chapters): the dot product's additivity is stated for any
// commutative ring R, and at ℝ, where the goal spells the real
// operations, R is pinned to the record of the ring instance real_ring
// states, whose fields those operations are. The law is read at R in
// the instance normal form, whose record equations the corpus installs
// (cmd/xugo installs them before the engine is built).
func TestRetrieveCorpus_AntecedentPinnedFromTheCorpus(t *testing.T) {
	serve.InstallRecordNormal()
	law, ok := registry.ByName("dot.AddLeft")
	require.True(t, ok, "the engine test binary links the chapters")
	instance, ok := registry.ByName("real_ring.CommRing")
	require.True(t, ok)
	dot, ok := registry.FamilyByName("vector/dot")
	require.True(t, ok)

	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goal := dot.ParseScript(serve.NewSeedEnv()).MakePropText(
		"∀n:num. ∀u v w:(num → real). dot⟨n⟩(real_add, real_mul, vec_add(real_add, u, v), w) = " +
			"real_add(dot⟨n⟩(real_add, real_mul, u, w), dot⟨n⟩(real_add, real_mul, v, w))")
	s.mu.Lock()
	gid := s.AddGoal(goal)
	s.mu.Unlock()
	res, err := e.Retrieve(context.Background(), info.ID, &RetrieveRequest{Mode: RetrieveByGoal, GoalID: gid})
	require.NoError(t, err)

	hit := corpusHit(t, res, law.Name)
	assert.Equal(t, corpusMatchApply, hit.Match)
	pinned := map[string]string{}
	for _, w := range hit.Witnesses {
		pinned[w.Binder] = w.Term
	}
	assert.Equal(t, map[string]string{"R": "real_ring", "n": "n", "u": "u", "v": "v", "w": "w"}, pinned)
	require.Len(t, hit.Premises, 1)
	assert.Equal(t, premiseEntry, hit.Premises[0].Status)
	assert.Equal(t, instance.Name, hit.Premises[0].Entry)
	assert.Equal(t, law.Name, res.Groups[0].Entries[0].Entry, "nothing outranks the law: %+v", res.Groups[0].Entries)
}

func TestRetrieveCorpus_OpenPremise(t *testing.T) {
	both := retrieveCorpusFixture().both
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)

	// No hypothesis: the law's antecedent is open — the agent's to supply.
	res := retrieveGoal(t, e, info.ID, "p:bool → bool, q:bool → bool, u:bool ⊢ p(u) ∧ q(u)")
	hit := corpusHit(t, res, both.Name)
	assert.Equal(t, []RetrieveWitness{{"P", "p"}, {"Q", "q"}, {"a", "u"}}, hit.Witnesses)
	require.Len(t, hit.Premises, 1)
	assert.Equal(t, premiseOpen, hit.Premises[0].Status)
	assert.Equal(t, "q(u)", hit.Premises[0].Statement)

	// With the antecedent resident the sequent IS the law up to
	// normalization (q(u) ⊢ p(u) ∧ q(u) normalizes to q(u) ⇒ p(u)): the
	// stronger reading, exact by key, is the one reported.
	res = retrieveGoal(t, e, info.ID, "p:bool → bool, q:bool → bool, u:bool, q(u) ⊢ p(u) ∧ q(u)")
	hit = corpusHit(t, res, both.Name)
	assert.Equal(t, corpusMatchExact, hit.Match)
	assert.Empty(t, hit.Premises)
}

func TestRetrieveCorpus_AMemberOverFreeVariablesIsNotAFact(t *testing.T) {
	probe := retrieveCorpusFixture().probe
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)

	// Probe's z is pinned by nothing the goal or the context spells. The
	// FreeFact member states suc(m) = 1 over a declared free m; were it
	// a fact, z would be pinned to m — a foreign variable — and the
	// premise would read suc(m) = 1. A real ground fact of the corpus
	// may still pin z; that reading is legitimate.
	res := retrieveGoal(t, e, info.ID, "c:num ⊢ c + 0 = 0 + c")
	for _, g := range res.Groups {
		for _, re := range g.Entries {
			if re.Entry != probe.Name {
				continue
			}
			for _, w := range re.Witnesses {
				assert.NotEqual(t, "m", w.Term, "pinned from a member's free variable: %+v", re)
			}
			for _, p := range re.Premises {
				assert.NotContains(t, p.Statement, "suc(m)", "%+v", re)
			}
		}
	}
}

// The scan is deadline-bounded in both passes — the facts and the
// heads; past the deadline the group reports itself truncated. The
// exact hit is a key lookup, not a scan, and stands.
func TestRetrieveCorpus_DeadlineTruncatesTheScan(t *testing.T) {
	fact := retrieveCorpusFixture().fact
	goal := fact.Family().ParseScript(testEnv()).MakePropText("P:bool → bool ⊢ ∀a:bool. P(a)")

	past := time.Now().Add(-time.Second)
	g, ok := corpusByGoal(scanGoal(goal, past), 10, past)
	require.True(t, ok)
	assert.True(t, g.Truncated)
	require.Len(t, g.Entries, 1)
	assert.Equal(t, fact.Name, g.Entries[0].Entry)
	assert.Equal(t, corpusMatchExact, g.Entries[0].Match)

	ahead := time.Now().Add(time.Minute)
	g, ok = corpusByGoal(scanGoal(goal, ahead), 10, ahead)
	require.True(t, ok)
	assert.False(t, g.Truncated, "within the deadline the scan completes")
}

// A law whose conclusion spells no constant the goal shares — the
// monoid's commutativity, `op(x, y) = op(y, x)`, against `x * y = y * x`
// on ℝ, where only the operation's slot stands against real_mul — has
// no type instance to read off the goal; the corpus's structure facts
// offer it, and the plan reads the law at the carrier the instance
// fixes, the instance the premise `by` would name. The ring's own
// absorption law reads the same way at `&0 * x = &0`, its record R the
// instance's.
func TestRetrieveCorpus_InstanceOfferedByAStructureFact(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	for _, row := range []struct {
		goal, law, instance string
		witnesses           map[string]string
	}{
		{"x:real, y:real ⊢ x * y = y * x", "comm_monoid.Comm", "real_ring.MulMonoid",
			map[string]string{"op": "real_mul", "e": "&1", "x": "x", "y": "y"}},
		{"x:real ⊢ &0 * x = &0", "comm_ring.MulLeftZero", "real_ring.CommRing",
			map[string]string{"R": "real_ring", "x": "x"}},
	} {
		sid, gid := bareArithLeaf(t, e, row.goal)
		res, err := e.Retrieve(context.Background(), sid, &RetrieveRequest{Mode: RetrieveByGoal, GoalID: gid, BudgetMs: 10000, MaxPerGroup: 50})
		require.NoError(t, err)
		hit := corpusHit(t, res, row.law)
		assert.Equal(t, corpusMatchApply, hit.Match, row.goal)
		pinned := map[string]string{}
		for _, w := range hit.Witnesses {
			pinned[w.Binder] = w.Term
		}
		assert.Equal(t, row.witnesses, pinned, row.goal)
		require.Len(t, hit.Premises, 1, row.goal)
		assert.Equal(t, premiseEntry, hit.Premises[0].Status)
		assert.Equal(t, row.instance, hit.Premises[0].Entry)
	}
}

// TestRetrieveCorpus_ByConstants: `consts` lists the members whose
// statement spells every named constant — by name, whatever the type
// instance — the ones spelling the fewest others first, and no group
// for a constant no member spells.
func TestRetrieveCorpus_ByConstants(t *testing.T) {
	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	stub := registry.Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	fam := registry.NewFamily("zz_retrieve_consts", nil)
	flip := fam.Define(registry.DefEntry{
		Name: "Flip", Const: "zz_rcc_flip", Type: "bool → bool",
		Equations: []string{"∀p:bool. zz_rcc_flip(p) ⇔ ¬p"},
	})
	fam.Define(registry.DefEntry{
		Name: "Both", Const: "zz_rcc_both", Type: "bool → bool → bool",
		Equations: []string{"∀p q:bool. zz_rcc_both(p, q) ⇔ p ∧ q"},
	})
	law := fam.Add(registry.ProofEntry{
		Name:  "FlipBoth",
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀p q:bool. zz_rcc_flip(zz_rcc_both(p, q)) ⇔ zz_rcc_flip(p) ∨ zz_rcc_flip(q)"},
	})
	retrieve := func(consts ...string) *RetrieveResult {
		res, err := e.Retrieve(context.Background(), "", &RetrieveRequest{Mode: RetrieveByConsts, Consts: consts})
		require.NoError(t, err)
		return res
	}
	names := func(res *RetrieveResult) []string {
		var out []string
		for _, g := range res.Groups {
			for _, re := range g.Entries {
				out = append(out, re.Entry)
			}
		}
		return out
	}
	res := retrieve("zz_rcc_flip")
	require.Len(t, res.Groups, 1)
	assert.Equal(t, retrieveCorpus, res.Groups[0].MatchedVia)
	assert.Equal(t, []string{flip.Name, law.Name}, names(res), "the definition spells the constant alone, the law one other")
	assert.Equal(t, law.Build.Headline, res.Groups[0].Entries[1].Statement)
	assert.Equal(t, []string{law.Name}, names(retrieve("zz_rcc_both", "zz_rcc_flip")), "every named constant")
	assert.Empty(t, retrieve("zz_rcc_neither").Groups, "a constant no member spells")
}

// TestRetrieveCorpus_EquationReadTheOtherWayRound: a member stating an
// equation applies to a goal stating it the other way round, as `by`
// fires it up to one Symm: the pre-read tries the goal's sides
// crosswise, as the plan does.
func TestRetrieveCorpus_EquationReadTheOtherWayRound(t *testing.T) {
	stub := registry.Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	fam := registry.NewFamily("zz_retrieve_flip", nil)
	for _, name := range []string{"f", "g"} {
		fam.Define(registry.DefEntry{
			Name: strings.ToUpper(name), Const: "zz_rcf_" + name, Type: "num → num",
			Equations: []string{"∀n:num. zz_rcf_" + name + "(n) = n"},
		})
	}
	law := fam.Add(registry.ProofEntry{
		Name:  "Retract",
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀n:num. zz_rcf_f(zz_rcf_g(n)) = n"},
	})
	// The goal `g(m) = f(g(g(m)))`, built from the law's own constants:
	// the law at n := g(m), the other way round.
	consts := map[core.TermKey]ext.ConstTerm{}
	ext.CollectConstTerms(ext.WrapTerm(law.Statement().Prop.Conclusion()), consts)
	var f, g ext.ConstTerm
	for _, c := range consts {
		switch c.Name() {
		case "zz_rcf_f":
			f = c
		case "zz_rcf_g":
			g = c
		}
	}
	require.False(t, f.IsZero())
	require.False(t, g.IsZero())
	m := ext.Var("m", ext.MatchesFORALL(law.Statement().Prop.Conclusion()).Var().Type())
	fw, gw := ext.WrapTerm(f), ext.WrapTerm(g)
	goal := prop.MakeProp(gw.Apply(m).Eq(fw.Apply(gw.Apply(gw.Apply(m)))))

	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.mu.Lock()
	gid := s.AddGoal(goal)
	s.mu.Unlock()
	res, err := e.Retrieve(context.Background(), info.ID, &RetrieveRequest{Mode: RetrieveByGoal, GoalID: gid})
	require.NoError(t, err)
	hit := corpusHit(t, res, law.Name)
	assert.Equal(t, corpusMatchApply, hit.Match)
	require.Len(t, hit.Witnesses, 1)
	assert.Equal(t, "zz_rcf_g(m)", hit.Witnesses[0].Term)
}

// TestRetrieveCorpus_IffReadAsItsHornClauses: a member concluding an
// ⇔ applies to a goal stating one side, the other side its premise,
// as `by` fires an ⇔ in either direction: the pre-read follows the
// plan's reading of each side.
func TestRetrieveCorpus_IffReadAsItsHornClauses(t *testing.T) {
	stub := registry.Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	fam := registry.NewFamily("zz_retrieve_iff", nil)
	for _, name := range []string{"f", "g"} {
		fam.Define(registry.DefEntry{
			Name: strings.ToUpper(name), Const: "zz_rci_" + name, Type: "num → num",
			Equations: []string{"∀n:num. zz_rci_" + name + "(n) = n"},
		})
	}
	law := fam.Add(registry.ProofEntry{
		Name:  "Sides",
		Build: registry.BuildSpec{Fn: stub.Fn, Headline: "∀n:num. zz_rci_f(n) = n ⇔ zz_rci_g(n) = n"},
	})
	// The goal `g(f(m)) = f(m)`: the right side at n := f(m), built from
	// the law's own constants.
	consts := map[core.TermKey]ext.ConstTerm{}
	ext.CollectConstTerms(ext.WrapTerm(law.Statement().Prop.Conclusion()), consts)
	var f, g ext.ConstTerm
	for _, c := range consts {
		switch c.Name() {
		case "zz_rci_f":
			f = c
		case "zz_rci_g":
			g = c
		}
	}
	require.False(t, f.IsZero())
	require.False(t, g.IsZero())
	m := ext.Var("m", ext.MatchesFORALL(law.Statement().Prop.Conclusion()).Var().Type())
	fw, gw := ext.WrapTerm(f), ext.WrapTerm(g)
	goal := prop.MakeProp(gw.Apply(fw.Apply(m)).Eq(fw.Apply(m)))

	e := lineageEngine(proof.NewMemoryCNFStore(), t.TempDir())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.mu.Lock()
	gid := s.AddGoal(goal)
	s.mu.Unlock()
	// Many corpus members apply to an equation of naturals with one
	// open premise, and the fixture's name sorts after theirs.
	res, err := e.Retrieve(context.Background(), info.ID, &RetrieveRequest{Mode: RetrieveByGoal, GoalID: gid, MaxPerGroup: 200})
	require.NoError(t, err)
	hit := corpusHit(t, res, law.Name)
	assert.Equal(t, corpusMatchApply, hit.Match)
	require.Len(t, hit.Witnesses, 1)
	assert.Equal(t, "zz_rci_f(m)", hit.Witnesses[0].Term)
	require.Len(t, hit.Premises, 1)
	assert.Equal(t, "zz_rci_f(zz_rci_f(m)) = zz_rci_f(m)", hit.Premises[0].Statement)
	assert.Equal(t, premiseOpen, hit.Premises[0].Status)
}
