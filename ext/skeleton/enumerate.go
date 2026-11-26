package skeleton

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// MatchingPoints enumerates every const-headed subterm of `p` that could
// serve as a structural anchor for type-substitution matching against
// another prop. It is symmetric — designed to be used identically on
// both sides of a matching pair (e.g., a polymorphic lemma and a
// concretely-typed goal) so the candidate enumeration is consistent.
//
// The walk has two phases:
//
//   - **Propositional skeleton walk** — strips ∀/∃ accumulating their
//     binders into BoundVars (so they become "pattern slots" downstream),
//     and decomposes ∧/∨/⇒/⇔/¬ on BOTH sides (type matching needs
//     every reachable matching anchor regardless of logical role).
//   - **Term-level descent** — at each non-connective atom, recurses
//     through Apply.Fun / Apply.Arg emitting every const-headed subterm.
//     Does *not* descend into Abs bodies: λ-bound vars there cannot
//     serve as pattern slots (slot semantics would clash with alpha-
//     equivalence, which is how the structural matcher already handles
//     them). The whole λ-containing subterm is still emitted at one
//     level above, so binders are matched alpha-style as part of the
//     larger pattern.
//
// BoundVars on returned IndexedTerms reflects the outer ∀/∃ binders
// only. Use IndexedTerm.IsBound on a downstream pattern variable to
// decide whether to treat it as a slot.
//
// Subterms are deduplicated by AlphaKey. Order is deterministic
// (depth-first, left-to-right).
//
// For callers that also need under-λ const heads (e.g., type
// adaptation, where type vars are concrete regardless of binder depth
// and an under-λ occurrence is just as good a witness as a top-level
// one), use MatchingPointsUnderLambda.
func MatchingPoints(p core.Prop) []IndexedTerm {
	return matchingPointsImpl(p, false)
}

// MatchingPointsUnderLambda is the under-λ-inclusive variant of
// MatchingPoints. In addition to everything MatchingPoints emits, it
// descends into AbsTerm bodies and emits const-headed subterms found
// there. Under-λ subterms carry **empty** BoundVars (regardless of
// any outer ∀/∃ binders accumulated in the walk so far) — λ-bound
// vars aren't pattern slots, and outer slot tracking is conservatively
// dropped across λ boundaries to keep α-soundness in the downstream
// structural matcher.
//
// Use this when slot tracking under λ is not needed but reaching
// every const-headed witness IS — the canonical example is
// typematch.TryAdaptLemmaTypes, where type matching cares only about
// each anchor's TYPE (which is α-invariant) and the boundary semantics
// of λ-bound variables don't affect correctness.
//
// LIMITATION carried over from this design choice: an under-λ anchor
// that contains FREE references to outer ∀-bound slot vars sees those
// vars treated as RIGID by the downstream matcher (no slot
// substitution available). In practice this rarely bites because the
// type discipline pushes polymorphism out to outer const heads where
// the standard (slot-tracking) walk catches it. If it ever does bite,
// the fix is to thread BoundVars accumulation through the AbsTerm
// descent — currently we drop it to match the original
// `deepConstSubterms` behavior this function subsumes.
func MatchingPointsUnderLambda(p core.Prop) []IndexedTerm {
	return matchingPointsImpl(p, true)
}

func matchingPointsImpl(p core.Prop, includeUnderLambda bool) []IndexedTerm {
	var out []IndexedTerm
	seen := make(map[core.TermKey]struct{})
	emit := func(t core.Term, bound map[core.TermKey]struct{}) {
		head, _ := ext.MatchesApply(t)
		if _, isConst := head.AsConst(); !isConst {
			return
		}
		key := t.AlphaKey()
		if _, dup := seen[key]; dup {
			return
		}
		seen[key] = struct{}{}
		out = append(out, IndexedTerm{Term: t, BoundVars: bound})
	}

	var walk func(t core.Term, bound map[core.TermKey]struct{})
	var descend func(t core.Term, bound map[core.TermKey]struct{})

	// walk handles binder stripping (∀/∃ → bound) and propositional
	// recursion (∧/∨/⇒/⇔/¬ → recurse into both sides). At each
	// non-binder level it ALSO calls descend to emit term-level anchors
	// with the bound vars accumulated so far. The two paths cover
	// different needs: descend emits matching anchors; the connective
	// recursion exists ONLY to find ∀/∃ buried inside connectives so
	// their binders get added to BoundVars before descend runs at the
	// deeper level. Without descend at every level, a whole `A ⇔ B`
	// would not be available as a candidate when both sides are useless
	// to the matcher (e.g., bare variables).
	walk = func(t core.Term, bound map[core.TermKey]struct{}) {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			walk(abs.Body(), extendBound(bound, abs.Var()))
			return
		}
		if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
			walk(abs.Body(), extendBound(bound, abs.Var()))
			return
		}
		descend(t, bound)
		if l, r, ok := ext.MatchesAND(t); ok {
			walk(l, bound)
			walk(r, bound)
			return
		}
		if l, r, ok := ext.MatchesIFF(t); ok {
			walk(l, bound)
			walk(r, bound)
			return
		}
		if l, r, ok := ext.MatchesIMPLY(t); ok {
			walk(l, bound)
			walk(r, bound)
			return
		}
		if l, r, ok := ext.MatchesOR(t); ok {
			walk(l, bound)
			walk(r, bound)
			return
		}
		if a := ext.MatchesNOT(t); a != nil {
			walk(a, bound)
			return
		}
	}

	descend = func(t core.Term, bound map[core.TermKey]struct{}) {
		emit(t, bound)
		if a, ok := t.AsAppliedTerm(); ok {
			descend(a.Fun(), bound)
			descend(a.Arg(), bound)
			return
		}
		// AbsTerm body descent is gated by includeUnderLambda. When
		// enabled, we pass nil bound — outer slot tracking does not
		// cross λ boundaries (see MatchingPointsUnderLambda godoc for
		// the limitation this preserves).
		if includeUnderLambda {
			if a, ok := t.AsAbsTerm(); ok {
				descend(a.Body(), nil)
			}
		}
	}

	walk(p.Conclusion(), nil)
	for _, h := range p.Hyps() {
		walk(h, nil)
	}
	return out
}
