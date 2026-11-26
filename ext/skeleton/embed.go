// embed.go implements the divergence-whistle encoding: a cheap
// over-approximation of homeomorphic tree embedding, computed on the
// same root-to-leaf path idea as the structural skeleton (skeleton.go) but
// with a coarser, whistle-specific token alphabet.
//
// Purpose. A rewrite-to-fixpoint driver (prover/tactic mergeTactics)
// needs an ONLINE termination detector: given the sequence of goals a
// branch has visited, decide "this trajectory is diverging — stop".
// The classical tool is the homeomorphic-embedding whistle from
// supercompilation: stop when the current term embeds some earlier
// term of the trajectory. By Kruskal's tree theorem no infinite
// sequence of terms over a finite signature avoids embedding an
// earlier element, so the whistle is a COMPLETE termination guarantee
// — independent of which rules fire, their order, or their orientation.
//
// Encoding. Each term is encoded as the set of its root-to-leaf token
// paths, with a deliberately coarse alphabet:
//
//	C:<name>  constant (head or leaf)
//	*         any variable (bound or free — collapsed) or var head
//	LAM       λ-binder (also a λ spine head / β-redex head)
//
// Argument-position markers and arities are dropped: unlike the
// structural skeleton, the whistle never needs to discriminate WHERE a
// symbol sits, only WHETHER structure is being re-contained. Path
// length is bounded by the term's own depth (≤ Size()), so the
// recursion is intrinsically capped by the term — there is no
// truncation constant (contrast maxPathDepth in skeleton.go, which
// bounds the path set of a deeply nested term).
//
// Embedding test. PathEmbeds(small, large) holds when every path of
// `small` is a token-subsequence of some path of `large` (with `*` in
// `small` matching any single token of `large`). If tree s embeds in
// tree t homeomorphically, every root-to-leaf path of s maps to an
// in-order token chain inside some root-to-leaf path of t, so path
// embedding is an OVER-approximation: it can only fire more often than
// true tree embedding, never less. For a whistle that is the safe
// direction — a false positive merely stops a fixpoint a little early
// (the current goal is returned as-is, still sound); a false negative
// cannot persist, because finite sets of finite-alphabet sequences
// under the ∀∃-subsequence order form a WQO (Higman's lemma + finite-
// set domination), and pairing with the size gate keeps it a WQO
// (Dickson). Hence ANY infinite trajectory eventually triggers
// PathEmbeds against some ancestor, regardless of how much precision
// the coarse alphabet gives up; precision only affects how early.

package skeleton

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// Whistle-alphabet tokens. Kept as plain strings; constant tokens are
// "C:" + name.
const (
	embTokVar = "*"
	embTokLam = "LAM"
)

// EmbPath is one root-to-leaf token path in the whistle alphabet.
type EmbPath = []string

// EmbPaths returns the full path set of t in the whistle alphabet.
// Unlike ExtractPaths there is no depth cap: path length is bounded by
// t's own structure (≤ t.Size()), which is the only bound needed here.
// Duplicate paths are collapsed. Order is deterministic (depth-first,
// left-to-right, first occurrence).
func EmbPaths(t core.Term) []EmbPath {
	var out []EmbPath
	seen := make(map[string]struct{})
	var prefix []string
	embWalk(t, &prefix, seen, &out)
	return out
}

// embWalk appends t's paths to out, using *prefix as a shared
// backtracking stack (cloned only at emit points).
func embWalk(t core.Term, prefix *[]string, seen map[string]struct{}, out *[]EmbPath) {
	if _, ok := t.AsAppliedTerm(); ok {
		head, args := ext.MatchesApply(t)
		*prefix = append(*prefix, embHeadToken(head))
		for _, arg := range args {
			embWalk(arg, prefix, seen, out)
		}
		*prefix = (*prefix)[:len(*prefix)-1]
		return
	}
	if c, ok := t.AsConst(); ok {
		emitEmb(append(*prefix, "C:"+string(c.Name())), seen, out)
		return
	}
	if _, ok := t.AsVar(); ok {
		emitEmb(append(*prefix, embTokVar), seen, out)
		return
	}
	if abs, ok := t.AsAbsTerm(); ok {
		*prefix = append(*prefix, embTokLam)
		embWalk(abs.Body(), prefix, seen, out)
		*prefix = (*prefix)[:len(*prefix)-1]
		return
	}
	panic("EmbPaths: unknown term kind")
}

func embHeadToken(head core.Term) string {
	if c, ok := head.AsConst(); ok {
		return "C:" + string(c.Name())
	}
	if _, ok := head.AsVar(); ok {
		return embTokVar
	}
	if _, ok := head.AsAbsTerm(); ok {
		// β-redex head: tag only, like the path encoder — losing
		// the head's inner structure just coarsens the approximation.
		return embTokLam
	}
	panic("embHeadToken: unexpected head kind")
}

// emitEmb records one finished path (cloning the shared prefix) unless
// an identical path was already emitted.
func emitEmb(tokens []string, seen map[string]struct{}, out *[]EmbPath) {
	n := 0
	for _, tok := range tokens {
		n += len(tok) + 1
	}
	joined := make([]byte, 0, n)
	for _, tok := range tokens {
		joined = append(joined, tok...)
		joined = append(joined, '|')
	}
	key := string(joined)
	if _, dup := seen[key]; dup {
		return
	}
	seen[key] = struct{}{}
	path := make([]string, len(tokens))
	copy(path, tokens)
	*out = append(*out, path)
}

// embTokMatches reports whether a token of the SMALL (earlier) term may
// map onto a token of the LARGE (current) term under embedding: `*` in
// small matches anything (a variable position may since have been
// instantiated to arbitrary structure); constants and LAM match only
// themselves.
func embTokMatches(small, large string) bool {
	return small == embTokVar || small == large
}

// embPathSubseq reports whether small is a token-subsequence of large
// under embTokMatches (greedy scan — valid because each small token's
// match set is fixed, so earliest-match is optimal).
func embPathSubseq(small, large EmbPath) bool {
	if len(small) > len(large) {
		return false
	}
	i := 0
	for j := 0; j < len(large) && i < len(small); j++ {
		if embTokMatches(small[i], large[j]) {
			i++
		}
	}
	return i == len(small)
}

// PathEmbeds reports whether every path of small is a token-subsequence
// of some path of large — the whistle's over-approximation of
// "the term behind small homeomorphically embeds into the term behind
// large". Callers should additionally gate on term size (embedding
// implies size(small) ≤ size(large)); Trajectory.EmbedsAncestor does.
func PathEmbeds(small, large []EmbPath) bool {
	for _, s := range small {
		found := false
		for _, l := range large {
			if embPathSubseq(s, l) {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}
	return true
}
