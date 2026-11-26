// step_by_audit_test.go — battery row 7's encoding: the economy
// audit, pinned on the executor:
//
//  1. AVOIDABLE KEY: a By whose leaf REACHES RESOLUTION (a key is at
//     stake — tryCNFRefute past its prelude) and closes under Basic()
//     reports "spell By(Normalized, …)" where the By so respelled
//     closes on fewer rows — the success-path twin of the MISS
//     diagnostic's byClosesUnderBasic branch. A leaf the closer's
//     prelude finishes keylessly is NOT reported: a marker there saves
//     nothing (TestByAudit_NoKeyNoPrescription). Neither is a By whose
//     respelling leaves a leaf open or reads the same rows
//     (TestByAudit_AvoidableRefuteIsRunBeforeItIsAdvised).
//  2. INERT ELEMENT: a shape element, a Broadcast or a set-driver
//     premise is reported inert exactly when a recording of the By
//     without it touches no row the By with it does not — it closes at
//     the keyless rung, or on the same certificates and plans. An
//     element whose removal costs a key or a plan is not reported,
//     however readily the refuter closes the leaf without it.
//  3. REPORT-ONLY: the audit's probes write NOTHING and are served no
//     row the audited close was not — the store after an audited run is
//     identical to the store after an unaudited one (a probe that
//     persisted would turn the report into a behaviour), and so is a
//     capturing store's record of the member.
//  4. NEGATIVE CONTROL: a By with no waste reports nothing.
package proof

import (
	"context"
	"slices"
	"strings"
	"sync/atomic"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// auditEnv is a live (non-strict) env over a fresh in-memory store,
// with the audit hook collecting findings.
func auditEnv(t *testing.T, st *groundByStore, findings *[]string) *ProverEnv {
	t.Helper()
	env := groundTestEnv(t)
	st.wire(env, true)
	if findings != nil {
		env.ByAuditReport = func(f string) { *findings = append(*findings, f) }
	}
	return env
}

func residentSpec(goal Prop) BySpec {
	premises := make([]ByPremiseSpec, goal.NumHyps())
	for i := 0; i < goal.NumHyps(); i++ {
		premises[i] = ByPremiseSpec{Install: prop.MakeProp(goal.Hyp(i)), Resident: true}
	}
	return BySpec{Premises: premises}
}

// commutedConjByGoal — `b(a) ∧ q(a) ⊢ q(a) ∧ b(a)` — is a leaf the
// apply rung does NOT take (the conclusion is no α-resident fact and no
// resident implication has it as an instance), so it reaches the CNF
// closer — whose PRELUDE then finishes it, minting no key (the store
// is unchanged), so the right assertion is that the audit says nothing.
// (A sequent whose conclusion is an α-variant of its resident premise
// closes earlier still: by the rung's `exact h`, keyless, which is the
// point of that rung.)
func commutedConjByGoal() Prop {
	b := ext.Var("b", core.MakeFun(TypeInd, core.TypeBool()))
	q := ext.Var("q", core.MakeFun(TypeInd, core.TypeBool()))
	a := ext.Var("a", TypeInd)
	hyp := b.Apply(a).And(q.Apply(a))
	concl := q.Apply(a).And(b.Apply(a))
	return prop.MakeProp(concl.Core(), hyp.Core())
}

func TestByAudit_NoKeyNoPrescription(t *testing.T) {
	goal := commutedConjByGoal()
	var findings []string
	st := newGroundByStore()
	env := auditEnv(t, st, &findings)

	before := st.Len()
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), residentSpec(goal)))
	require.True(t, n.Proved())

	// The leaf reached the closer and cost nothing: the prelude closed
	// it. Probe A reads at the resolution point and so has nothing to
	// say — a `Normalized` here would be a marker that saves no key.
	assert.Equal(t, before, st.Len(), "the prelude close must mint no key")
	assert.Empty(t, findings, "no key at stake ⇒ no marker prescribed")
}

// inertFinding reports whether the audit named element as inert.
func inertFinding(findings []string, element string) bool {
	for _, f := range findings {
		if strings.Contains(f, element+" is inert") {
			return true
		}
	}
	return false
}

// TestByAudit_InertShapeFinding: a shape element that changes nothing
// the close records is reported inert, on a close that records rows as
// on one that records none. Under each of these elements the ground
// fixture costs one plan and one key, and the leaf the shaped By is
// handed spells no ε-term, no term past fifty nodes and nothing Basic()
// moves: a recording of the By without the element, made over those
// rows, applies the plan as recorded, reads the key and adds no row.
func TestByAudit_InertShapeFinding(t *testing.T) {
	goal := groundFixture(t)

	for _, tc := range []struct {
		element string
		shape   ByShape
	}{
		{"HilbertDenoted", HilbertDenoted},
		{"Denoted(50)", Denoted(50)},
		{"PreNormalized", PreNormalized},
		{"Normalized", Normalized},
	} {
		t.Run(tc.element, func(t *testing.T) {
			var findings []string
			st := newGroundByStore()
			spec := residentSpec(goal)
			spec.Shapes = []ByShape{tc.shape}
			n := CreateGoalStack(goal)
			require.True(t, ApplyByStep(n, auditEnv(t, st, &findings), t.Context(), spec))
			require.True(t, n.Proved())
			require.Len(t, st.Proofs(), 1, "fixture: the shaped spelling costs one key")
			require.Len(t, st.Plans(), 1, "fixture: and one plan")
			without := &groundByStore{copyOfStore(st.MemoryCNFStore)}
			require.True(t, ApplyByStep(CreateGoalStack(goal), auditEnv(t, without, nil), t.Context(), residentSpec(goal)))
			require.Equal(t, keysOf(st.Proofs()), keysOf(without.Proofs()), "fixture: without the element the By reads the key and adds none")
			require.Equal(t, planKeysOf(st.Plans()), planKeysOf(without.Plans()), "fixture: and the plan")
			assert.True(t, inertFinding(findings, tc.element),
				"the By without %s records the rows it records with it; findings: %v", tc.element, findings)
		})
	}
}

// TestByAudit_ElementThatSparesRowsIsNotInert: an element whose removal
// costs a key or a plan is not inert, though the refuter closes the leaf
// without it at once. `Denoted(2)` closes the ground fixture with no row
// at all; the bare spelling costs a plan and a key. "Does the ladder
// still close" is the wrong question here: it does, and the drop adds
// both rows.
//
// The warm half holds the same close against a store that already has
// the bare spelling's rows — a spelling since abandoned, its rows not
// yet collected. The close with the element reads neither, so neither
// is a row the By without it may be served: served from the whole
// store, the probe would call the element inert and the drop would
// bring both rows back into the member's record.
func TestByAudit_ElementThatSparesRowsIsNotInert(t *testing.T) {
	goal := groundFixture(t)
	shaped := residentSpec(goal)
	shaped.Shapes = []ByShape{Denoted(2)}

	t.Run("cold", func(t *testing.T) {
		var findings []string
		st := newGroundByStore()
		n := CreateGoalStack(goal)
		require.True(t, ApplyByStep(n, auditEnv(t, st, &findings), t.Context(), shaped))
		require.True(t, n.Proved())
		require.Empty(t, st.Proofs(), "fixture: with Denoted(2) the close records no key")
		require.Empty(t, st.Plans(), "fixture: and no plan")
		assert.False(t, inertFinding(findings, "Denoted(2)"),
			"dropping Denoted(2) costs a key and a plan; findings: %v", findings)
	})

	t.Run("warm", func(t *testing.T) {
		held := NewMemoryCNFStore()
		recorder := func(store CNFStore, findings *[]string) *ProverEnv {
			env := groundTestEnv(t)
			env.ProofService.CNFStore = store
			env.ByAuditReport = func(f string) { *findings = append(*findings, f) }
			return env
		}
		var findings []string
		require.True(t, ApplyByStep(CreateGoalStack(goal), recorder(held, &findings), t.Context(), residentSpec(goal)))
		require.Len(t, held.Proofs(), 1, "fixture: the abandoned bare spelling left its key")
		require.Len(t, held.Plans(), 1, "fixture: and its plan")

		// The member's recording, as the recorder captures it.
		findings = nil
		capture := NewCapturingCNFStore(held)
		n := CreateGoalStack(goal)
		require.True(t, ApplyByStep(n, recorder(capture, &findings), t.Context(), shaped))
		require.True(t, n.Proved())
		assert.False(t, inertFinding(findings, "Denoted(2)"),
			"the abandoned spelling's rows are not the close's; findings: %v", findings)
		assert.Zero(t, capture.Captured().Len(),
			"neither the close nor its audit is served the abandoned rows, so the member's record names none")
	})
}

// TestByAudit_ProbesRecordNothing is the report-only contract: the
// audited run's store (certificates AND plans) is key-for-key the
// unaudited run's, where the audit has a finding and where the By
// without the element would need a refute and a grounding the close
// never made.
func TestByAudit_ProbesRecordNothing(t *testing.T) {
	goal := groundFixture(t)
	for _, tc := range []struct {
		element string
		shape   ByShape
		finding bool
	}{
		{"HilbertDenoted", HilbertDenoted, true},
		{"Denoted(2)", Denoted(2), false},
	} {
		t.Run(tc.element, func(t *testing.T) {
			spec := residentSpec(goal)
			spec.Shapes = []ByShape{tc.shape}

			silent := newGroundByStore()
			require.True(t, ApplyByStep(CreateGoalStack(goal), auditEnv(t, silent, nil), t.Context(), spec))

			var findings []string
			audited := newGroundByStore()
			require.True(t, ApplyByStep(CreateGoalStack(goal), auditEnv(t, audited, &findings), t.Context(), spec))
			require.Equal(t, tc.finding, inertFinding(findings, tc.element), "fixture; findings: %v", findings)

			assert.Equal(t, keysOf(silent.Proofs()), keysOf(audited.Proofs()),
				"audit probes must mint no certificate rows")
			assert.Equal(t, planKeysOf(silent.Plans()), planKeysOf(audited.Plans()),
				"audit probes must mint no plan rows")
		})
	}
}

func TestByAudit_CleanByReportsNothing(t *testing.T) {
	// A real paramodulation the audit has nothing to say about: an
	// equational chain with no substitutable free-var equation (Basic()
	// closes surprisingly much — a ¬p, p∨q ⊢ q fixture here turned out
	// to be a TRUE avoidable-key positive, and a chain of two links of
	// one size closes by the rewrite that makes the conclusion a
	// hypothesis), and a spelling with no shape.
	indT := TypeInd
	fun := core.MakeFun(indT, indT)
	f := ext.Var("f", fun)
	g := ext.Var("g", fun)
	h := ext.Var("h", fun)
	k := ext.Var("k", fun)
	a := ext.Var("a", indT)
	b := ext.Var("b", indT)
	c := ext.Var("c", indT)
	d := ext.Var("d", indT)
	eq1 := f.Apply(a).Eq(g.Apply(b))
	eq2 := g.Apply(b).Eq(h.Apply(c))
	eq3 := h.Apply(c).Eq(k.Apply(d))
	concl := f.Apply(a).Eq(k.Apply(d))
	goal := prop.MakeProp(concl.Core(), eq1.Core(), eq2.Core(), eq3.Core())

	var findings []string
	env := auditEnv(t, newGroundByStore(), &findings)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), residentSpec(goal)))
	require.True(t, n.Proved())
	assert.Empty(t, findings, "a waste-free By must produce no findings")
}

func keysOf[V any](m map[core.PropKey]V) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, string(k))
	}
	slices.Sort(out)
	return out
}

func planKeysOf[V any](m map[core.PropKey]V) []string { return keysOf(m) }

// Probe A runs under byAuditProbeBudget: a context already done makes
// the Basic() oracle answer "does not close" for a goal the unbounded
// search closes, so a leaf whose Basic() case-splits for minutes costs
// the recorder a quarter second and reports nothing.
func TestByAudit_BasicProbeIsBounded(t *testing.T) {
	a := ext.Var("a", core.TypeBool())
	b := ext.Var("b", core.TypeBool())
	goal := prop.MakeProp(b.And(a).Core(), a.And(b).Core())
	assert.True(t, auditBasicCloses(context.Background(), goal))
	done, cancel := context.WithCancel(context.Background())
	cancel()
	assert.False(t, auditBasicCloses(done, goal))
}

// inertSettacGoal is the set driver's inert-premise fixture: the
// conclusion is an α-variant of the FIRST hypothesis (the load-bearing
// premise) and the second hypothesis is an
// unrelated fact the driver never reads.
func inertSettacGoal() Prop {
	predT := core.MakeFun(TypeInd, core.TypeBool())
	b := ext.Var("b", predT)
	q := ext.Var("q", predT)
	i := ext.Var("i", TypeInd)
	x := ext.Var("x", TypeInd)
	p := ext.Var("p", core.TypeBool())
	hyp := ext.ForAll(i)(b.Apply(i).Imply(q.Apply(i)))
	concl := ext.ForAll(x)(b.Apply(x).Imply(q.Apply(x)))
	return prop.MakeProp(concl.Core(), hyp.Core(), p.Core())
}

// TestByAudit_SettacInertPremise: the audit's probe C — a `BySets`
// premise the set driver closes without is named as inert, and a
// premise the close needs is not. The driver unfolds its standard
// vocabulary itself, so a cited membership law can dissolve into a
// tautology and the close succeed just as well without it; before this
// probe the success path said nothing (convex.Inter shipped
// set_basic.InInter that way, and convex.Empty nearly shipped
// set_basic.NotInEmpty).
func TestByAudit_SettacInertPremise(t *testing.T) {
	goal := inertSettacGoal()
	var findings []string
	env := auditEnv(t, newGroundByStore(), &findings)

	// A Prop keeps its hypotheses in canonical order, not the order
	// MakeProp received them, so the premises are labelled by what
	// they state rather than by index — and the negative control
	// below picks the load-bearing one the same way.
	spec := residentSpec(goal)
	loadBearing := -1
	for i := range spec.Premises {
		if !ext.MatchesFORALL(spec.Premises[i].Install.Conclusion()).IsZero() {
			spec.Premises[i].Describe = "the α-variant fact"
			loadBearing = i
		} else {
			spec.Premises[i].Describe = "an unrelated fact"
		}
	}
	require.NotEqual(t, -1, loadBearing)
	spec.Settac = true
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), spec))
	require.True(t, n.Proved())

	var inert []string
	for _, f := range findings {
		if strings.Contains(f, "is inert") {
			inert = append(inert, f)
		}
	}
	require.Len(t, inert, 1, "exactly the unrelated premise is inert; findings: %v", findings)
	assert.Contains(t, inert[0], "an unrelated fact")
	assert.NotContains(t, inert[0], "premise the α-variant fact is inert")

	// Negative control: the same close with only the load-bearing
	// premise reports nothing.
	findings = nil
	lean := BySpec{Premises: []ByPremiseSpec{spec.Premises[loadBearing]}, Settac: true}
	n = CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), lean))
	require.True(t, n.Proved())
	for _, f := range findings {
		assert.NotContains(t, f, "is inert", "a load-bearing premise must not be reported; findings: %v", findings)
	}
}

// TestByAudit_SettacPremiseThatRekeysIsNotInert: probe C names a premise
// only when the driver's close without it records no row it does not
// record with it. Here the chain `f(a) = g(b) = h(c) = k(d)` stands beside its
// own shortcut `f(a) = h(c)`: the close needs either the first two links
// or the shortcut, never both, so the refuter closes the leaf with any
// one of the three taken out — at another clause set, and so at a key
// the close does not hold. None of them is inert: each drop costs the
// member that key.
func TestByAudit_SettacPremiseThatRekeysIsNotInert(t *testing.T) {
	fun := core.MakeFun(TypeInd, TypeInd)
	f, g, h, k := ext.Var("f", fun), ext.Var("g", fun), ext.Var("h", fun), ext.Var("k", fun)
	a, b, c, d := ext.Var("a", TypeInd), ext.Var("b", TypeInd), ext.Var("c", TypeInd), ext.Var("d", TypeInd)
	link1 := f.Apply(a).Eq(g.Apply(b))
	link2 := g.Apply(b).Eq(h.Apply(c))
	link3 := h.Apply(c).Eq(k.Apply(d))
	shortcut := f.Apply(a).Eq(h.Apply(c))
	concl := f.Apply(a).Eq(k.Apply(d))
	goal := prop.MakeProp(concl.Core(), link1.Core(), link2.Core(), link3.Core(), shortcut.Core())

	var findings []string
	st := newGroundByStore()
	spec := residentSpec(goal)
	spec.Settac = true
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, auditEnv(t, st, &findings), t.Context(), spec))
	require.True(t, n.Proved())
	require.Len(t, st.Proofs(), 1, "fixture: the close is the driver's refute, one key")

	// The close without the first two links: closed, and at another key.
	lean := prop.MakeProp(concl.Core(), link3.Core(), shortcut.Core())
	leanStore := newGroundByStore()
	leanSpec := residentSpec(lean)
	leanSpec.Settac = true
	require.True(t, ApplyByStep(CreateGoalStack(lean), auditEnv(t, leanStore, nil), t.Context(), leanSpec))
	require.Len(t, leanStore.Proofs(), 1)
	require.NotEqual(t, keysOf(st.Proofs()), keysOf(leanStore.Proofs()),
		"fixture: fewer premises refute at another key")

	for _, finding := range findings {
		assert.NotContains(t, finding, "is inert", "every drop here re-keys the refute; findings: %v", findings)
	}
}

// readCountingStore counts the rows a close READS BACK from the store —
// the recorder's census: a row a member's replay reads is a row the
// family GC keeps. Only hits count; a miss touches nothing.
type readCountingStore struct {
	*MemoryCNFStore
	proofHits, planHits atomic.Int64
}

func (s *readCountingStore) ReadProof(k core.PropKey) *refuter.CNFRefuteProofProto {
	p := s.MemoryCNFStore.ReadProof(k)
	if p != nil {
		s.proofHits.Add(1)
	}
	return p
}

func (s *readCountingStore) ReadPlan(k core.PropKey) *ByConditionPlanProto {
	p := s.MemoryCNFStore.ReadPlan(k)
	if p != nil {
		s.planHits.Add(1)
	}
	return p
}

// HoldsProof / HoldsPlan are the look the census does not count
// (CNFRowHolder), as the recorder's capturing store answers it.
func (s *readCountingStore) HoldsProof(k core.PropKey) bool {
	return s.MemoryCNFStore.ReadProof(k) != nil
}

func (s *readCountingStore) HoldsPlan(k core.PropKey) bool {
	return s.MemoryCNFStore.ReadPlan(k) != nil
}

// TestByLadder_ClosesKeylessBeforeTheCache pins rung 0 (probeKeyless),
// a session's and the recorder's alike: a leaf the conditioned rung
// closes with no refuter and no grounding is closed that way BEFORE the
// store is asked, so the rows the bare spelling recorded are left unread
// and a GC retires them — and a leaf it cannot close runs the ladder as
// before and adds nothing.
//
// The fixture is one resident hypothesis `∀y w. ¬R(w, y) ∧ (R(w, y) ∨
// Q(w))` and the goal `Q(f(a))`. Bare, Basic() does not close it (the
// conjunction sits under the ∀). The bare spelling records a grounding
// plan and a key, and the audit prescribes `Normalized`; with the
// marker the conditioned leaf closes under Basic() with nothing
// grounded at all. The store still holds the bare spelling's plan under
// this leaf's key, which is the leaf before any shaping: a ladder that
// took the plan for the leaf's recorded close and went to its rung
// would read it — the read that kept a row a shaping had made
// unnecessary, and that made a re-record read the marker as inert.
func TestByLadder_ClosesKeylessBeforeTheCache(t *testing.T) {
	ind := TypeInd
	R := ext.Var("R", core.MakeFun(ind, core.MakeFun(ind, core.TypeBool())))
	Q := ext.Var("Q", core.MakeFun(ind, core.TypeBool()))
	f := ext.Var("f", core.MakeFun(ind, ind))
	y, w, a := ext.Var("y", ind), ext.Var("w", ind), ext.Var("a", ind)
	hyp := ext.ForAll(y)(ext.ForAll(w)(ext.Not(R.Apply(w, y)).And(R.Apply(w, y).Or(Q.Apply(w)))))
	goal := prop.MakeProp(Q.Apply(f.Apply(a)).Core(), hyp.Core())
	require.False(t, auditBasicCloses(context.Background(), goal),
		"fixture: Basic() must not close the BARE leaf, or the marker is not what the conditioned rung adds")

	st := &readCountingStore{MemoryCNFStore: NewMemoryCNFStore()}
	var findings []string
	recorder := func() *ProverEnv {
		env := groundTestEnv(t)
		env.ProofService.CNFStore = st
		env.ByAuditReport = func(f string) { findings = append(findings, f) }
		return env
	}
	prescribed := func() bool {
		for _, f := range findings {
			if strings.Contains(f, "spell By(Normalized") {
				return true
			}
		}
		return false
	}
	reset := func() {
		st.proofHits.Store(0)
		st.planHits.Store(0)
		findings = nil
	}

	// The bare spelling, recorded: a plan and a key, and the audit says
	// the leaf that reached the refuter wanted Basic().
	require.True(t, ApplyByStep(CreateGoalStack(goal), recorder(), t.Context(), residentSpec(goal)))
	require.Len(t, st.Proofs(), 1, "the bare spelling costs one key")
	require.Len(t, st.Plans(), 1, "and one grounding plan")
	require.True(t, prescribed(), "the audit prescribes the marker; findings: %v", findings)

	withMarker := residentSpec(goal)
	withMarker.Shapes = []ByShape{Normalized}

	// A session with the marker: closed keylessly, the store unread.
	session := groundTestEnv(t)
	session.ProofService.CNFStore = st
	reset()
	respelled := CreateGoalStack(goal)
	require.True(t, ApplyByStep(respelled, session, t.Context(), withMarker))
	require.True(t, respelled.Proved())
	assert.Zero(t, st.proofHits.Load(), "a session reads no key of the spelling before")
	assert.Zero(t, st.planHits.Load(), "and no plan of it")
	assert.Len(t, st.Proofs(), 1, "nothing is minted")
	assert.Len(t, st.Plans(), 1, "and no plan is recorded")

	// The recorder with the marker: closed keylessly, the store unread.
	reset()
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, recorder(), t.Context(), withMarker))
	require.True(t, n.Proved())
	assert.Zero(t, st.proofHits.Load(), "the recorded key is left unread, so a GC retires it")
	assert.Zero(t, st.planHits.Load(), "and so is the plan")
	assert.Len(t, st.Proofs(), 1, "nothing is minted")
	assert.Len(t, st.Plans(), 1, "and no plan is recorded")

	// The bare spelling again, warm: the keyless probe cannot close it,
	// the ladder runs as before on the recorded rows and adds nothing.
	reset()
	require.True(t, ApplyByStep(CreateGoalStack(goal), recorder(), t.Context(), residentSpec(goal)))
	assert.NotZero(t, st.proofHits.Load(), "the recorded key closes the bare spelling")
	assert.Len(t, st.Proofs(), 1, "a warm run adds no key")
	assert.Len(t, st.Plans(), 1, "and no plan")
}

// TestByAudit_BroadcastProbe: probe B′ — a `Broadcast` on a close whose
// shaping does not fan is reported inert, and one the shaping does
// fan is not. The negative is the fan the shaping makes
// (shapingFanSetup: an ⇔ goal Normalized splits into its two
// directions, each an AC-permutation the refuter alone closes); the
// positive is a conjunction, which the conditioning stage splits and
// closes conjunct by conjunct with no Broadcast — the marker is a
// leftover.
func TestByAudit_BroadcastProbe(t *testing.T) {
	broadcastInert := func(findings []string) bool {
		for _, f := range findings {
			if strings.Contains(f, "shape element Broadcast is inert") {
				return true
			}
		}
		return false
	}

	// Negative: the fan is real.
	e, sec := shapingFanSetup()
	var findings []string
	e.ctx.Env.ByAuditReport = func(f string) { findings = append(findings, f) }
	sec.Do(Derive(func(a *Argument) {
		a.Show("fans into two leaves, both closed", By(Normalized, Broadcast, e.assoc, e.sym))
	}))
	require.True(t, sec.Proved())
	assert.False(t, broadcastInert(findings), "the shaping fans here, so Broadcast is load-bearing; findings: %v", findings)

	// Positive: a conjunction the stage splits — no fan for Broadcast.
	goal := commutedConjByGoal()
	findings = nil
	env := auditEnv(t, newGroundByStore(), &findings)
	spec := residentSpec(goal)
	spec.Broadcast = true
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), spec))
	require.True(t, n.Proved())
	assert.True(t, broadcastInert(findings), "no leaf fans, so Broadcast must be reported inert; findings: %v", findings)
}

// TestByAudit_NormalizedInertAtTheKeylessRung: probe B asks of a
// `Normalized` what the recorder's ladder does without it, and the
// ladder closes a leaf at its keyless rung (probeKeyless: the conditioned
// attempt, the refuter barred, no grounding) before the bare spelling is
// tried. So a marker over a leaf that rung closes is inert — dropped, the
// member records no row — though the bare spelling, with no rung, would
// reach the refuter. A marker over a leaf whose bare spelling needs the
// grounding stage's plan is not: the plan is blob state where the marker
// was text.
func TestByAudit_NormalizedInertAtTheKeylessRung(t *testing.T) {
	normalizedInert := func(findings []string) bool {
		for _, f := range findings {
			if strings.Contains(f, "shape element Normalized is inert") {
				return true
			}
		}
		return false
	}
	rows := func(st *groundByStore) int { return len(st.Proofs()) + len(st.Plans()) }

	// Positive: `∀x. P(x) ⊢ P(a)` — the apply rung on the conditioned leaf.
	P := ext.Var("P", core.MakeFun(TypeInd, core.TypeBool()))
	x, a := ext.Var("x", TypeInd), ext.Var("a", TypeInd)
	var goal Prop = prop.MakeProp(P.Apply(a).Core(), ext.ForAll(x)(P.Apply(x)).Core())

	bare := newGroundByStore()
	require.True(t, ApplyByStep(CreateGoalStack(goal), auditEnv(t, bare, nil), t.Context(), residentSpec(goal)))
	require.Zero(t, rows(bare), "fixture: without the marker the recorder must close the leaf with no row")

	var findings []string
	marked := newGroundByStore()
	spec := residentSpec(goal)
	spec.Shapes = []ByShape{Normalized}
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, auditEnv(t, marked, &findings), t.Context(), spec))
	require.True(t, n.Proved())
	assert.True(t, normalizedInert(findings), "the keyless rung closes the leaf without the marker; findings: %v", findings)
	assert.Zero(t, rows(marked), "the probe records nothing")

	// Negative: without the marker this leaf costs a grounding plan and a key.
	goal = avoidableRefuteGoal()
	findings = nil
	spec = residentSpec(goal)
	spec.Shapes = []ByShape{Normalized}
	n = CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, auditEnv(t, newGroundByStore(), &findings), t.Context(), spec))
	require.True(t, n.Proved())
	assert.False(t, normalizedInert(findings), "the marker spares a plan and a key here; findings: %v", findings)
}

// avoidableRefuteGoal — `∀y w. ¬R(w, y) ∧ (R(w, y) ∨ Q(w)) ⊢ Q(f(a))` —
// is a leaf the bare spelling sends to the refuter (it grounds the
// hypothesis and records a key) and Basic() closes once it is grounded:
// the audit's first finding. TestByLadder_ClosesKeylessBeforeTheCache
// builds the same sequent.
func avoidableRefuteGoal() Prop {
	ind := TypeInd
	R := ext.Var("R", core.MakeFun(ind, core.MakeFun(ind, core.TypeBool())))
	Q := ext.Var("Q", core.MakeFun(ind, core.TypeBool()))
	f := ext.Var("f", core.MakeFun(ind, ind))
	y, w, a := ext.Var("y", ind), ext.Var("w", ind), ext.Var("a", ind)
	hyp := ext.ForAll(y)(ext.ForAll(w)(ext.Not(R.Apply(w, y)).And(R.Apply(w, y).Or(Q.Apply(w)))))
	return prop.MakeProp(Q.Apply(f.Apply(a)).Core(), hyp.Core())
}

// TestByAudit_PerCallReportIsTheFirstProbeAlone pins BySpec.Report, the
// session's form of the audit: with no recorder hook on the env, a call
// that carries its own sink hears that a leaf it refuted closes under
// Basic() — and hears nothing else. The probes that re-run the
// composite (an inert shape element) are the recorder's, and a close
// spelled with the marker has nothing to report.
func TestByAudit_PerCallReportIsTheFirstProbeAlone(t *testing.T) {
	prescribes := func(findings []string) bool {
		for _, f := range findings {
			if strings.Contains(f, "spell By(Normalized") {
				return true
			}
		}
		return false
	}
	run := func(goal Prop, spec BySpec) (findings []string) {
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		require.Nil(t, env.ByAuditReport, "the env carries no recorder hook")
		spec.Report = func(f string) { findings = append(findings, f) }
		n := CreateGoalStack(goal)
		require.True(t, ApplyByStep(n, env, t.Context(), spec))
		require.True(t, n.Proved())
		return findings
	}

	goal := avoidableRefuteGoal()
	bare := run(goal, residentSpec(goal))
	assert.True(t, prescribes(bare), "the refuted leaf closes under Basic(); findings: %v", bare)

	marked := residentSpec(goal)
	marked.Shapes = []ByShape{Normalized}
	assert.Empty(t, run(goal, marked), "with the marker nothing reaches the refuter that Basic() closes")

	// The inert HilbertDenoted of TestByAudit_InertShapeFinding: a finding
	// of the recorder's audit, not of the per-call probe.
	shaped := groundFixture(t)
	spec := residentSpec(shaped)
	spec.Shapes = []ByShape{HilbertDenoted}
	for _, f := range run(shaped, spec) {
		assert.NotContains(t, f, "inert", "the per-call probe does not re-run the composite")
	}
}

func TestByClosed_ReportsActualRouteWithoutChangingStore(t *testing.T) {
	goal := avoidableRefuteGoal()
	store := newGroundByStore()
	env := auditEnv(t, store, nil)
	spec := residentSpec(goal)
	var route string
	spec.Closed = func(s string) { route = s }
	run := func() {
		n := CreateGoalStack(goal)
		require.True(t, ApplyByStep(n, env, t.Context(), spec))
		require.True(t, n.Proved())
	}
	run()
	require.Contains(t, route, "cnf live refute")
	keys := keysOf(store.Proofs())
	run()
	require.Contains(t, route, "cnf cached certificate")
	require.NotContains(t, route, "live")
	require.Equal(t, keys, keysOf(store.Proofs()))

	spec.Shapes = []ByShape{Normalized}
	run()
	require.NotEmpty(t, route)
	require.NotContains(t, route, "cnf")
	require.Equal(t, keys, keysOf(store.Proofs()))
}

func TestByClosed_ReportsOnceWithEconomyAudit(t *testing.T) {
	var findings, routes []string
	env := auditEnv(t, newGroundByStore(), &findings)
	goal := groundFixture(t)
	spec := residentSpec(goal)
	spec.Shapes = []ByShape{HilbertDenoted}
	spec.Closed = func(s string) { routes = append(routes, s) }
	require.True(t, ApplyByStep(CreateGoalStack(goal), env, t.Context(), spec))
	require.NotEmpty(t, findings)
	require.Len(t, routes, 1)
	require.NotEmpty(t, routes[0])
}

func TestByClosed_PreNormalizedNamesShaping(t *testing.T) {
	goal := avoidableRefuteGoal()
	spec := residentSpec(goal)
	spec.Shapes = []ByShape{PreNormalized}
	var route string
	spec.Closed = func(s string) { route = s }
	require.True(t, ApplyByStep(CreateGoalStack(goal), auditEnv(t, newGroundByStore(), nil), t.Context(), spec))
	require.Equal(t, "shaping", route)
}

// Simplifying a conjunct inside Basic is not a separate leaf close.
// The diagnostic names the closer of the remaining working leaf.
func TestByClosed_BroadcastDistinguishesSimplificationFromClose(t *testing.T) {
	e := makeACRegroupTestEnv(false)
	hard := groundFixture(t)
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.c, e.plus.Apply(e.b, e.a))
	hyps := append(hard.Hyps(), e.assoc.Conclusion(), e.sym.Conclusion())
	goal := prop.MakeProp(ext.WrapTerm(hard.Conclusion()).And(lhs.Eq(rhs)), hyps...)
	spec := residentSpec(goal)
	spec.Shapes = []ByShape{Normalized}
	spec.Broadcast = true
	var route string
	spec.Closed = func(s string) { route = s }
	n := CreateGoalStack(goal)
	st := newGroundByStore()
	st.wire(e.ctx.Env, true)
	require.True(t, ApplyByStep(n, e.ctx.Env, t.Context(), spec))
	require.True(t, n.Proved())
	require.Equal(t, "cnf live refute", route)
}

// TestByAudit_AvoidableRefuteIsRunBeforeItIsAdvised pins the first
// probe's second half. A leaf that closes under Basic() on a fresh
// stack names a candidate; the By respelled with Normalized is then run
// through the recorder's ladder, held to the close's rows, and the
// finding is printed only where it closes on fewer of them.
func TestByAudit_AvoidableRefuteIsRunBeforeItIsAdvised(t *testing.T) {
	// residentStep is the By ApplyByStep builds from residentSpec, with
	// the audit's capture set by hand: the leaf Basic() closes need not
	// be one the respelled By closes.
	residentStep := func(goal Prop, env *ProverEnv, captured ...Prop) _ByStep {
		premises := make([]byPremise, goal.NumHyps())
		for i := range premises {
			premises[i] = byPremise{install: prop.MakeProp(goal.Hyp(i)), resident: true}
		}
		return _ByStep{premises: premises, env: env, ctx: t.Context(),
			spine: CreateGoalStack(goal), audit: &byAuditState{preClose: captured}}
	}
	// record closes goal by a bare By into a fresh store and returns the
	// env over that store with the rows the close touched.
	record := func(goal Prop) (*ProverEnv, *byCloseTrace) {
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		rows := &byCloseTrace{}
		spec := residentSpec(goal)
		spec.Records = func(keys, plans []core.PropKey) { rows.keys, rows.plans = keys, plans }
		n := CreateGoalStack(goal)
		require.True(t, ApplyByStep(n, env, t.Context(), spec))
		require.True(t, n.Proved())
		return env, rows
	}
	closable := alphaHypGoal(t)
	require.True(t, auditBasicCloses(t.Context(), closable), "fixture: Basic() closes the captured leaf")

	// Fewer rows: the respelling closes with no key, and is advised.
	avoidable := avoidableRefuteGoal()
	env, rows := record(avoidable)
	require.NotEmpty(t, rows.keys, "fixture: the bare close records a key")
	var findings []string
	report := func(f string) { findings = append(findings, f) }
	residentStep(avoidable, env, closable).reportAvoidableRefutes(avoidable, rows, report)
	require.Len(t, findings, 1)
	assert.Contains(t, findings[0], "spell By(Normalized, …)")
	assert.Contains(t, findings[0], "closes on 0 row(s)")

	// The same rows: Basic() closes nothing of this leaf, so the
	// respelled By reads every certificate the bare one does.
	hard := groundChainFixture(t)
	env, rows = record(hard)
	touched := len(rows.keys) + len(rows.plans)
	require.NotZero(t, touched, "fixture: the bare close records rows")
	step := residentStep(hard, env, closable)
	probe := step
	probe.shape = &ByShape{}
	read, closed := auditProbeRows(probe, hard, rows)
	require.True(t, closed, "fixture: the respelled By closes on the bare close's rows")
	require.Equal(t, touched, read, "fixture: and reads all of them")
	findings = nil
	step.reportAvoidableRefutes(hard, rows, report)
	assert.Empty(t, findings, "a respelling that saves no row is not advised")

	// No close: held to no row, the respelled By cannot be served the
	// certificate it needs.
	_, closed = auditProbeRows(probe, hard, &byCloseTrace{})
	require.False(t, closed, "fixture: the respelled By needs a row")
	step.reportAvoidableRefutes(hard, &byCloseTrace{}, report)
	assert.Empty(t, findings, "a respelling that does not close is not advised")

	// A By that carries a shape runs Basic() before its close already.
	shaped := residentStep(avoidable, env, closable)
	shaped.shape = &ByShape{pre: true}
	shaped.reportAvoidableRefutes(avoidable, rows, report)
	assert.Empty(t, findings, "Normalized adds nothing to a By that carries a shape")
}
