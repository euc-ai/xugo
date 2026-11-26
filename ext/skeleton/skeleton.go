// Package skeleton reads a term's structural skeleton: each subterm
// encoded as a set of root-to-leaf paths, each path a sequence of tokens
// (the perfect-discrimination-tree encoding, Stickel 1989 / McCune Otter
// lineage). Constants and bound variables are the discriminating tokens;
// free variables are wildcards; types are absent. The prover reads
// terms through it — the type-blind bucket keys (bucket_key.go), the
// matching points the type matcher and e-matching ground at, and the
// homeomorphic-embedding whistle that cuts divergent rewrite chains
// (embed.go, whistle.go, permutation.go).
package skeleton

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// Token is a single position-token in a skeleton path.
type Token string

// PathKey is the joined string form of one root-to-leaf path. Joined by "|".
type PathKey string

// Path-depth cap during encoding: a deeply nested term would otherwise
// explode its path set.
const maxPathDepth = 10

// IndexedTerm pairs a subterm with the set of variables that were bound by
// binders stripped from above it during enumeration. The encoder uses
// BoundVars to decide whether a VarTerm should emit `*B` (bound) or `*F`
// (free). VarTerm.deBruijn is unreliable here: XuGo's de Bruijn
// convention counts from the term root, so stripping a binder shifts
// its meaning, and boundness is propagated explicitly instead.
//
// BoundVars is keyed by VarTerm.AlphaKey() (content-based), NOT pointer
// identity: deserialized props reconstruct fresh VarTerm pointers, and
// bound-var references in the body don't share
// identity with the binder's VarTerm. Within a single prop, AlphaKey
// uniquely identifies the binder by (name, type), which is sufficient
// for correct boundness decisions in all non-shadowing cases.
type IndexedTerm struct {
	Term      core.Term
	BoundVars map[core.TermKey]struct{}
}

// IsBound reports whether a variable is in the BoundVars set.
func (it IndexedTerm) IsBound(v core.VarTerm) bool {
	if it.BoundVars == nil {
		return false
	}
	_, ok := it.BoundVars[v.AlphaKey()]
	return ok
}

// ExtractPaths returns the path set of one indexed subterm. Paths are
// returned in deterministic order (insertion order of a depth-first
// left-to-right walk).
func ExtractPaths(it IndexedTerm) []PathKey {
	var out []PathKey
	walkPaths(it.Term, it.BoundVars, nil, 0, &out)
	return out
}

// walkPaths is the recursive encoder. tokens is the partial path
// accumulated so far; depth is its length.
func walkPaths(
	t core.Term,
	bound map[core.TermKey]struct{},
	tokens []Token,
	depth int,
	out *[]PathKey,
) {
	if depth >= maxPathDepth {
		emit(tokens, out)
		return
	}

	// AppliedTerm: flatten the spine via ext.MatchesApply, emit
	// HEAD:<H>/<k>, then branch into one path per argument with ARG<i>.
	if _, ok := t.AsAppliedTerm(); ok {
		head, args := ext.MatchesApply(t)
		k := len(args)
		headInner := headInnerToken(head, bound)
		headTok := Token(fmt.Sprintf("HEAD:%s/%d", headInner, k))

		// If the head is a lambda (β-redex), the head doesn't carry extra
		// inner structure — just the LAM tag — but we still enumerate the
		// args as separate paths.
		newTokens := append(tokens, headTok)
		for i, arg := range args {
			argTok := Token(fmt.Sprintf("ARG%d", i))
			extended := append(newTokens, argTok)
			walkPaths(arg, bound, extended, depth+2, out)
		}
		return
	}

	if c, ok := t.AsConst(); ok {
		final := append(tokens, Token(fmt.Sprintf("C:%s/0", c.Name())))
		emit(final, out)
		return
	}

	if v, ok := t.AsVar(); ok {
		var tok Token
		if _, isBound := bound[v.AlphaKey()]; isBound {
			tok = "*B/0"
		} else {
			tok = "*F/0"
		}
		final := append(tokens, tok)
		emit(final, out)
		return
	}

	if abs, ok := t.AsAbsTerm(); ok {
		// Extend bound set with this lambda's var and recurse into body.
		extended := extendBound(bound, abs.Var())
		final := append(tokens, "LAM")
		walkPaths(abs.Body(), extended, final, depth+1, out)
		return
	}

	panic("ExtractPaths: unknown term kind")
}

// headInnerToken returns the inner token used inside HEAD:<H>/<k>.
func headInnerToken(head core.Term, bound map[core.TermKey]struct{}) string {
	if c, ok := head.AsConst(); ok {
		return "C:" + string(c.Name())
	}
	if v, ok := head.AsVar(); ok {
		if _, isBound := bound[v.AlphaKey()]; isBound {
			return "*B"
		}
		return "*F"
	}
	if _, ok := head.AsAbsTerm(); ok {
		return "LAM"
	}
	// Should not happen: MatchesApply guarantees the head is not an AppliedTerm.
	panic("headInnerToken: unexpected head kind")
}

func emit(tokens []Token, out *[]PathKey) {
	if len(tokens) == 0 {
		return
	}
	parts := make([]string, len(tokens))
	for i, t := range tokens {
		parts[i] = string(t)
	}
	*out = append(*out, PathKey(strings.Join(parts, "|")))
}

// extendBound returns a new BoundVars map containing the union of `bound`
// and {v}. The original map is not mutated.
func extendBound(bound map[core.TermKey]struct{}, v core.VarTerm) map[core.TermKey]struct{} {
	out := make(map[core.TermKey]struct{}, len(bound)+1)
	for k := range bound {
		out[k] = struct{}{}
	}
	out[v.AlphaKey()] = struct{}{}
	return out
}
