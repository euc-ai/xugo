// clause_whistle.go — growth-chain divergence throttle for the given
// clause loop, built on the skeleton path-embedding encoding
// (ext/skeleton embed.go).
//
// Why this exists. A flat size cap on the clauses addToRecord admits
// (_CLAUSE_SIZE_LIMIT alone) has two failure modes, both visible on
// one iterated-product proof:
//
//   - It silently severs LEGITIMATE inference chains whose
//     intermediate clauses carry a large atom — a single
//     pair-comprehension atom (set_member(p, set_comprehension(λg.∃xy.comprehension_spec(…)))) is
//     ~25–35 term nodes, so any resolvent that keeps one is at or
//     over the cap.
//   - It does nothing against the actual divergence it guards
//     for BELOW the cap: self-applying unit equalities such as
//     pairs.PairSurjective's Skolemized clause `q = (skx q, sky q)` grow a
//     tower skx(p) → skx(skx(p)) → … whose early rungs are all
//     admissible.
//
// The throttle is targeted where a flat cap is indiscriminate:
//
//   - A GROWTH-CHAIN WHISTLE: a derivation step is "growing" when
//     some input clause path-embeds into the (no smaller) output —
//     the supercompilation divergence signal, computed with the same
//     skeleton.EmbPaths / skeleton.PathEmbeds encoding the rewrite
//     drivers' whistle uses. A single growing step is normal
//     (paramodulating a structured RHS into a literal). A CHAIN of
//     them — each output re-containing its input and growing — is
//     the tower signature. Chain depth is tracked per clause and the
//     clause is dropped when the chain exceeds
//     _WHISTLE_GROWTH_BACKSTOP consecutive growing steps.
//   - A POLICY-SIZED hard cap: max(_CLAUSE_SIZE_LIMIT, 2 × the
//     largest init clause) instead of a flat constant. Goals whose init
//     clauses are small keep exactly _CLAUSE_SIZE_LIMIT; comprehension-heavy
//     goals get room proportional to their own statement size (the
//     same policy-not-incident sizing as the FM byte/work fuses in
//     prover/solver/omega).
//
// Soundness: the whistle only ever DROPS derived clauses, exactly
// like the old size gate — the search stays sound, merely incomplete.
// Determinism: addToRecord runs concurrently, so two derivations of
// the same clause can race on which chain depth gets recorded; the
// whistle can therefore differ run-to-run on WHICH member of a
// divergent family is cut first. Live search is already
// schedule-dependent — saturation derives concurrently, and which
// derivation lands first is the scheduler's; stored-proof
// reconstruction does not route through addToRecord, so replay is
// unaffected.
//
// NOTE: deliberately NOT wired into skeleton.ReportWhistleFire — that
// counter is a TRIPWIRE (replay harnesses assert zero fires), whereas
// cutting junk streams during live saturation is routine throttling,
// not a bug signal. Fires are counted locally for tests/telemetry.

package refuter

import (
	"sync/atomic"

	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/utils"
)

// _WHISTLE_GROWTH_BACKSTOP is the number of CONSECUTIVE growing,
// input-embedding derivation steps a chain may take before the
// whistle cuts it. Legitimate proofs occasionally grow a clause once
// or twice in a row (rewriting with a structured RHS); towers grow on
// every step. 3 leaves headroom for the former and cuts the latter at
// its fourth rung.
const _WHISTLE_GROWTH_BACKSTOP = 3

// _clauseEnc is the cached whistle encoding of one clause: the
// skeleton embedding paths of its effective body plus the term size
// used by the embedding size gate.
type _clauseEnc struct {
	size  int
	paths []skeleton.EmbPath
}

// _ClauseWhistle carries the policy-sized cap and the per-clause
// growth-chain bookkeeping. One instance per top-level refutation,
// shared across divide-and-conquer sub-states (same lifetime and
// sharing discipline as _RefuteCache).
type _ClauseWhistle struct {
	// sizeLimit is the policy-sized hard cap on derived clause size
	// (components sum, same measure the old flat gate used).
	sizeLimit int

	// growth maps a clause key to its growth-chain depth: 0 for init
	// clauses and non-growing derivations, parent+1 for a derivation
	// step whose input embeds into a no-smaller output.
	growth utils.Map[ClauseKey, int]

	// encs caches whistle encodings by clause key.
	encs utils.Map[ClauseKey, *_clauseEnc]

	// fires counts cut clauses (local telemetry; see this file's header
	// for why this is NOT skeleton.ReportWhistleFire).
	fires atomic.Int64
}

// newClauseWhistle sizes the cap from the initial clause set.
func newClauseWhistle(initClauses ClauseMap) *_ClauseWhistle {
	maxInit := 0
	for _, c := range initClauses {
		if s := c.Size(); s > maxInit {
			maxInit = s
		}
	}
	limit := _CLAUSE_SIZE_LIMIT
	if 2*maxInit > limit {
		limit = 2 * maxInit
	}
	return &_ClauseWhistle{sizeLimit: limit}
}

// encode returns the cached whistle encoding of c.
func (w *_ClauseWhistle) encode(c *Clause) *_clauseEnc {
	key := c.Key()
	if enc, ok := w.encs.Load(key); ok {
		return enc
	}
	body := c.EffectiveTerm()
	enc := &_clauseEnc{size: body.Size(), paths: skeleton.EmbPaths(body)}
	w.encs.LoadOrStore(key, enc)
	return enc
}

// chainDepth returns the recorded growth-chain depth of c (0 when
// unrecorded — init clauses and clauses admitted as non-growing).
func (w *_ClauseWhistle) chainDepth(c *Clause) int {
	d, _ := w.growth.Load(c.Key())
	return d
}

// Rejects reports whether the derived clause should be dropped:
// either over the policy-sized cap, or the tip of a growth chain
// longer than the backstop. On admission it records the new clause's
// chain depth.
func (w *_ClauseWhistle) Rejects(clauseThm *clause.ClauseThm, newClause *Clause) bool {
	if newClause.Size() > w.sizeLimit {
		w.fires.Add(1)
		return true
	}

	enc := w.encode(newClause)
	depth := 0
	for h := range clauseThm.HypClauseIter() {
		he := w.encode(h)
		if he.size <= enc.size && skeleton.PathEmbeds(he.paths, enc.paths) {
			if d := w.chainDepth(h) + 1; d > depth {
				depth = d
			}
		}
	}
	if depth > _WHISTLE_GROWTH_BACKSTOP {
		w.fires.Add(1)
		return true
	}
	if depth > 0 {
		w.growth.LoadOrStore(newClause.Key(), depth)
	}
	return false
}

// Fires returns the number of clauses cut so far (tests/telemetry).
func (w *_ClauseWhistle) Fires() int64 { return w.fires.Load() }
