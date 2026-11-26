package skeleton

import (
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

// SkeletonKey is a PropKey-typed bucket key used by callers (chiefly
// proof.ThmCache) to group propositions for type-match lookups. It is a
// necessary condition for the relation — no false negatives — but it
// over-approximates, and callers must confirm bucket membership with a
// per-candidate exact check.

// _SKELETON_KEY_PREFIX disambiguates SkeletonKey output from AlphaKey
// and any other PropKey-typed namespace, so the two cannot accidentally
// collide in a shared map.
const _SKELETON_KEY_PREFIX = "skel_"

// SkeletonKey returns a coarse bucket key for type-match lookup. Two
// propositions related by a TypeMatch (one is a type-instantiation of
// the other — i.e. NormalizedPropTypeMatch would succeed on them) are
// guaranteed to share this key; structurally similar but unrelated
// props may also collide (over-approximation), so callers must confirm
// bucket membership with NormalizedPropTypeMatch.
//
// Mechanism: the prop is encoded into the set of root-to-leaf paths
// produced by ExtractPaths over the conclusion and each hyp; the path
// set is sorted, joined into one signature, then hashed. The
// type-substitution invariance is NOT achieved by an erasure pass —
// it's a property of the path encoding itself (see skeleton.go's
// walkPaths): emitted tokens carry constant names, applied-spine
// arity, and bound/free var markers, but no type information at any
// position. Two props related by any HolType substitution traverse
// to the same token stream by construction.
//
// Concrete types are erased as well as type variables: (A,A)→bool and
// (bool,bool)→bool share a SkeletonKey.
//
// INVARIANT: `p` is expected to be already normalized. ExtractPaths is
// itself ordering-stable, but the thm caches only ever store normalized
// props, so passing a non-normalized prop is a caller bug.
func SkeletonKey(p core.Prop) core.PropKey {
	// Walk conclusion + each hyp directly via ExtractPaths, with no
	// prop-level decomposition: decomposing `= on bool` as ⇔ would break
	// type-substitution invariance (`x:A = x:A` stays one Eq term while
	// `x:bool = x:bool` would split into its operands). The raw
	// ExtractPaths walker treats every AppliedTerm uniformly — head +
	// args — and since its tokens carry no type info, the resulting
	// path set is identical under any HolType substitution.
	seen := make(map[PathKey]struct{})
	var paths []PathKey
	collect := func(t core.Term) {
		for _, pk := range ExtractPaths(IndexedTerm{Term: t}) {
			if _, dup := seen[pk]; dup {
				continue
			}
			seen[pk] = struct{}{}
			paths = append(paths, pk)
		}
	}
	collect(p.Conclusion())
	for _, h := range p.Hyps() {
		collect(h)
	}

	strs := make([]string, len(paths))
	for i, pk := range paths {
		strs[i] = string(pk)
	}
	sort.Strings(strs)
	sig := strings.Join(strs, "\x00")
	return core.PropKey(_SKELETON_KEY_PREFIX + utils.GenerateHash(sig))
}
