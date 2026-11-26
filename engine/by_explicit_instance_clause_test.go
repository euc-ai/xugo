package engine

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"
)

// TestEmitSection_CollectsTheExplicitInstanceClauseRoute: a key premise
// the session names at an explicit instance (term_specialize binding
// every binder) installs as Go's typed `Law.At(…)` does — in the law's
// registered clause form, Normalize first and the types after — so the
// session's close and the recorder's run of the identical Go spelling
// take one route and write one row. The leaf is TopologyIsomorphicIff's
// four-conjunct Have: the law is an ⇔ whose function equation the
// clause form states pointwise, so the close refutes, and the key is
// the one the recorder writes for `By(Normalized, framed, isomorphism,
// TopologyIsomorphismIff.At(T, S, m.map))`.
//
// Emit's CNF collector re-runs the recorded By from its record, and the
// record carries the exact premise's clause form, so the collected
// cache holds the key the session's close wrote — the row the emitted
// Go's `TopologyIsomorphismIff.At(…)` reads at replay.
func TestEmitSection_CollectsTheExplicitInstanceClauseRoute(t *testing.T) {
	env := servedEnv(t)
	env.ProofService.CNFStore = proof.NewMemoryCNFStore()
	e := newEngine(env)
	info, err := e.CreateSession(t.Context())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "topology/topology_category", nil)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	parsed := dsl.ParsePropTextInScope("∀T S:set(set(A)). ∀f:morphism_triple(set(set(A)), A → A). "+
		"f = mk_morphism(T, S, triple_map(f)) ⇒ category_isomorphism(topology_category, f) ⇒ "+
		"is_topology(T) ∧ is_topology(S) ∧ normalize_on(⋃T, junk, triple_map(f)) = triple_map(f) ∧ homeomorphic_map(T, S, triple_map(f))",
		&dsl.ParseScope{ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true})
	require.Empty(t, parsed.Errors, "%v", parsed.Errors)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, move := range []string{"strip_quant", "strip_imp"} {
		for {
			out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: move}})
			require.NoError(t, err)
			if !out.Success {
				break
			}
			gid = out.State.Goals[0].ID
		}
	}

	require.Contains(t, applyExplicitInstanceBy(t, e, info.ID, s, gid), explicitInstanceKey)
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0,
		FuncName: "Build_FramedIsomorphism", Family: "topology/topology_category"})
	require.NoError(t, err)
	var cache proof.CNFCache
	require.NoError(t, proto.Unmarshal(out.CNFCache, &cache))
	assert.Contains(t, cache.GetEntries(), string(explicitInstanceKey),
		"the collector re-runs the By by its recorded clause form and collects the session's key")
}

// explicitInstanceKey is the certificate the recorder writes for the Go
// spelling of the close of TopologyIsomorphicIff's four-conjunct Have.
const explicitInstanceKey core.PropKey = "prop_45999f82686407a2"

// applyExplicitInstanceBy applies the session's spelling of the close —
// both premises named resident, the law at every binder of the stripped
// goal, Normalized — and returns its by_records text.
func applyExplicitInstanceBy(t *testing.T, e *Engine, sid string, s *Session, gid string) string {
	t.Helper()
	framed, isomorphism := -1, -1
	s.mu.Lock()
	entry, _, err := e.resolveFocusedGoal(s, gid)
	require.NoError(t, err)
	for i, h := range entry.node.Goal.Hyps() {
		switch printed := s.Spelling().Term(h); {
		case strings.Contains(printed, "mk_morphism"):
			framed = i
		case strings.Contains(printed, "category_isomorphism"):
			isomorphism = i
		}
	}
	s.mu.Unlock()
	require.True(t, framed >= 0 && isomorphism >= 0, "the two premises are resident")

	out, err := e.ApplyStep(t.Context(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type:    "by",
		ByHyps:  []ByHypSpec{{HypIndex: &framed}, {HypIndex: &isomorphism}},
		ByShape: &ByShapeReq{Normalized: true},
		WithLemmas: []LemmaWithSpec{{
			Key:            "topology_category.TopologyIsomorphismIff",
			TermSpecialize: map[string]string{"T": "T₀", "S": "S₀", "f": "triple_map(f₀)"},
		}},
	}})
	require.NoError(t, err)
	require.True(t, out.Success, "%+v", out.Diagnostics)
	for _, d := range out.Diagnostics {
		if d.Type == DiagByRecords {
			return d.Message
		}
	}
	return ""
}
