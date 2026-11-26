package tactic

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// IsSimpleDefExpandShape reports whether `lemma` has the exact shape
// `⊢ C = f` — no hyps, conclusion is an equation, LHS is a bare Const.
// When true, TryDefExpand handles the lemma authoritatively for ANY
// goal:
//   - if TryDefExpand returns non-nil SubGoals, it's the correct
//     result;
//   - if TryDefExpand returns nil, the rewrite genuinely doesn't
//     fire (the const isn't in the goal).
//
// The caller (`_LeanRwTactic.apply`) uses this to SKIP LeanRwTactic's
// slow mergeTactics fixpoint when the lemma is simple.
//
// Simple-shape lemmas cover the def_expand common case: every Type-1
// `NewConstDef` def theorem produced by the kernel has this exact shape.
func IsSimpleDefExpandShape(lemma Prop) bool {
	if lemma.NumHyps() != 0 {
		return false
	}
	l, _, ok := MatchesEQ(lemma.Conclusion())
	if !ok {
		return false
	}
	_, isConst := l.AsConst()
	return isConst
}

// TryDefExpand is a fast-path for the def_expand-specific lemma
// shape `⊢ C = f` (bare Const equated to a definition body). It walks
// the goal's CONCLUSION and each HYP directly, rewriting matching C
// occurrences as it finds them, then β-reduces only the RHSs that were
// changed so `(λv. body)(x₀)` collapses to `body[v:=x₀]`.
//
// Hypothesis coverage: an occurrence of C inside a hyp (e.g. an
// ∃-Skolemized `set_member(x, image(f, s))` produced by simplify) is expanded
// alongside conclusion occurrences. This closes the "def_expand doesn't
// touch hyps" scope gap that walled hyp-driven refutation attempts on
// STEP.A of an iterated-product proof.
//
// Polymorphism handling: at every Const-with-matching-name subterm we
// instantiate the def thm to THAT occurrence's own type via
// `constTerm.DefThm()` — which materializes `⊢ constTerm = defRhs[σ]`
// at the occurrence's specific type. This makes the fast path
// polymorphism-agnostic: the same walker handles both concrete-type
// lemmas and the polymorphic lemma that def_expand's entry point
// passes down (before `chooseTypeAdaptedStep` has adapted anything).
// That's essential because `tryAdaptLemmaTypes` can return nil when
// the goal's Const occurs at a type that involves goal-side type-var
// scaffolding (var:A, var:B, …); without per-occurrence
// re-instantiation the whole rewrite fails even though each occurrence
// is unfoldable in isolation.
//
// Returns SubGoals with a two-child shape `[lemma, rewrittenGoal]`.
// The rewrittenGoal has both concl and each hyp substituted with their
// β-reduced form (unchanged for hyps/concl that don't mention C). The
// reconstruction composes bridge equations in both directions:
//   - concl bridge: `bridge_c.EqSym().EqMP(subgoal_proof)` maps
//     rewritten concl back to original concl.
//   - each hyp bridge: `bridge_h.LeftAssume().DeriveTrans(...)`
//     replaces the rewritten hyp with the original hyp in the proof's
//     hyp set.
//
// Nil when the lemma doesn't fit the shape, when C appears in neither
// concl nor any hyp, or when no Const-with-name occurrence has a def
// thm (i.e. the meta's `.def` is nil — Type-2 typedef consts, basic
// consts). The `_LeanRwTactic.apply` caller falls through in that
// case.
//
// AUTHORITATIVE for `IsSimpleDefExpandShape` lemmas — the fast path
// covers every rewrite the general `LeanRwTactic` would find on this
// shape (per-occurrence DefThm() unfolding is the complete
// specification for def_expand). See `IsSimpleDefExpandShape`'s doc
// for the "skip LeanRwTactic on nil" contract.
//
// Why this exists: live def_expand on the residual of that proof after
// finite_set.FiniteInductStrong has been observed to hang
// indefinitely inside LeanRwTactic's mergeTactics fixpoint. Empirically
// a dedicated one-pass def walker dodges that fixpoint without making
// DeepRewrite or all AppliedTerm nodes pay a global memoization tax.
func TryDefExpand(lemma Prop, goal Prop) *SubGoals {
	return TryDefExpandReading(lemma, goal, nil)
}

// TryDefExpandReading is TryDefExpand with the record equations of the
// unfolding's normal form (InstanceNormal) read through read.
func TryDefExpandReading(lemma Prop, goal Prop, read LibraryRead) *SubGoals {
	rewriteDefThenBeta, ok := defExpandRewrite(lemma, read)
	if !ok {
		return nil
	}

	// Rewrite the conclusion.
	conclBridge := rewriteDefThenBeta(goal.Conclusion())
	// A bridge with hyps is a hypothesis-carrying rewrite (e.g. via
	// a lemma that requires side conditions); the fast path only
	// commits pure def-eq rewrites.
	if conclBridge != nil && conclBridge.NumHyps() != 0 {
		return nil
	}
	if conclBridge != nil && prop.Rhs(conclBridge).AlphaEquals(goal.Conclusion()) {
		// No structural change on the conclusion — treat as no-op there.
		conclBridge = nil
	}

	// Rewrite each hyp. rewriteDefThenBeta returns nil unless a def-eq
	// activity happened, so unrelated β-redexes are left untouched.
	numHyps := goal.NumHyps()
	hypBridges := make([]*prop.PropWrapper, numHyps)
	changedHyp := false
	for i := 0; i < numHyps; i++ {
		h := goal.Hyp(i)
		hb := rewriteDefThenBeta(h)
		if hb == nil || hb.NumHyps() != 0 {
			continue
		}
		if prop.Rhs(hb).AlphaEquals(h) {
			continue
		}
		hypBridges[i] = hb
		changedHyp = true
	}

	// If nothing structurally changed, no fast-path result to commit.
	if conclBridge == nil && !changedHyp {
		return nil
	}

	// Build the subgoal: concl and hyps replaced by their β-reduced forms
	// (or left as-is when no bridge fired at that slot).
	newConcl := goal.Conclusion()
	if conclBridge != nil {
		newConcl = prop.Rhs(conclBridge)
	}
	newHyps := make([]core.Term, numHyps)
	for i := 0; i < numHyps; i++ {
		if hypBridges[i] != nil {
			newHyps[i] = prop.Rhs(hypBridges[i])
		} else {
			newHyps[i] = goal.Hyp(i)
		}
	}
	child := makeImageProp(newConcl, newHyps)

	// Reconstruction: compose the bridges in reverse.
	//   - subgoal proof π': hyps' ⊢ concl'
	//   - concl bridge `⊢ concl_L = concl_R`: apply `.EqSym().EqMP(π')`
	//     to get `hyps' ⊢ concl_L`.
	//   - each hyp bridge `⊢ hyp_L = hyp_R`: apply
	//     `.LeftAssume().DeriveTrans(π)` — `bridge.LeftAssume() = hyp_L ⊢ hyp_R`;
	//     DeriveTrans substitutes hyp_R (present in π's hyps) with hyp_L.
	reconstruct := func(thms ...Prop) Prop {
		// child(1) carries the possibly-rewritten hyps; if it closed via ⊥
		// (contradictory hyps), the resulting ⊥-conclusion proof needs to
		// carry back to the ORIGINAL hyps for the parent, which requires
		// undoing the hyp rewrites we applied. Handle the two cases:
		if thms[1].Conclusion().Equals(F) && !changedHyp {
			return thms[1]
		}
		result := prop.WrapProp(thms[1])
		// Undo concl rewrite: concl_R → concl_L. Only when the subgoal's
		// concl is actually concl_R (not ⊥ from contradictory hyps).
		if conclBridge != nil && !thms[1].Conclusion().Equals(F) {
			result = conclBridge.EqSym().EqMP(result)
		}
		// Undo each hyp rewrite: replace hyp_R with hyp_L in result's hyps.
		for i := 0; i < numHyps; i++ {
			if hypBridges[i] == nil {
				continue
			}
			// bridge = ⊢ hyp_L = hyp_R
			// bridge.LeftAssume() = hyp_L ⊢ hyp_R
			// DeriveTrans(result) requires result to have hyp_R as a hyp:
			//   {hyp_L} ⊢ hyp_R   +   result: {hyp_R, ...} ⊢ ...
			//   → {hyp_L, ...} ⊢ ...
			// The ⊥-conclusion case (thms[1] ends in ⊥) still needs this
			// substitution when hyp rewrites happened, because the parent
			// goal has hyp_L not hyp_R.
			la := hypBridges[i].LeftAssume()
			if result.HasHyp(la.Conclusion()) {
				result = la.DeriveTrans(result)
			}
		}
		return result
	}
	// Each hypothesis descends from its own slot, opened or not; the
	// lemma child carries no provenance.
	return MakeTrackedSubGoals(goal, reconstruct, [][]int{nil, hypSuccessorsOf(child, newHyps)}, lemma.AsProp(), child)
}

func defExpandRewrite(lemma Prop, read LibraryRead) (func(core.Term) *prop.PropWrapper, bool) {
	// Shape gate: `⊢ C = f`, no hyps, LHS is a bare Const.
	if lemma.NumHyps() != 0 {
		return nil, false
	}
	l, _, ok := MatchesEQ(lemma.Conclusion())
	if !ok {
		return nil, false
	}
	lConst, isConst := l.AsConst()
	if !isConst {
		return nil, false
	}
	name := lConst.Name()
	// Type-1 gate on the LEMMA's const: when the lemma's meta carries no
	// def (Type-2 typedef abs/rep, or a basic const), the fast path can't
	// unfold ANY occurrence — decline as a whole (the caller retries via
	// the general path).
	lMeta := lConst.Meta()
	if lConst.DefThm().IsZero() {
		return nil, false
	}

	// Per-occurrence polymorphism-aware walker. At each subterm:
	//   - If the level itself is a Const with the target name, produce
	//     the type-specific def thm as the local rewrite: rebuild the
	//     const at THIS occurrence's concrete type against the LEMMA's
	//     meta (`MakeConstTerm(lMeta, t.Type()).DefThm()` — a
	//     `PropTypeInst` of the meta's stored def at exactly this
	//     occurrence's type instance).
	//   - Otherwise recurse into children and combine the sub-rewrites.
	// This deliberately does NOT do a const-name pre-filter: a direct
	// find-and-rewrite walk is cheaper for the common sweep path.
	//
	// α-INVARIANCE IS LOAD-BEARING: the per-occurrence def thm is derived
	// from (lemma meta, occurrence TYPE) only — both α-visible. It must
	// NOT go through the occurrence's own embedded `constT.DefThm()`: a
	// deserialized goal can embed a same-name ConstTerm whose meta object
	// is a def-less twin (a const nested inside another const's def
	// body, restored from a serialized record), and trusting that
	// pointer made the walk silently SKIP that occurrence — a partial,
	// committed rewrite whose residual diverged between environments on
	// α-equal (key-equal) inputs. Observed live: a replay
	// incident — def_expand(set_member) after def_expand(delete) expanded the
	// inner set_member(y,s) but skipped the outer set_member(x', set_comprehension(…)) introduced by
	// delete's pb-restored def body, committing a half-expanded residual
	// that diverged from both the recording and a fresh-env replay of
	// the same α-class. Const names are globally unique, so rebinding
	// every occurrence to the lemma's wired meta is semantics-preserving;
	// past the Type-1 gate above the rebuilt DefThm is always non-nil, so
	// no silent-skip path remains.
	//
	// The walk is a pure function of the node pointer (per-occurrence
	// DefThm depends only on the const's own type; no binder env
	// is consulted), so on gate-crossing roots a per-root PtrMemo
	// (see ext/subterm.go) collapses pointer-shared subtrees to one
	// visit — a static walk, entry size gate is the exact work bound.
	makeWalk := func(cache *ext.PtrMemo[*prop.PropWrapper]) prop.Rewrite {
		var walk prop.Rewrite
		walk = func(t core.Term) *prop.PropWrapper {
			if constT, ok := t.AsConst(); ok && constT.Name() == name {
				defThm := core.MakeConstTerm(lMeta, constT.Type()).DefThm()
				if defThm.IsZero() {
					panic("defExpandRewrite: nil DefThm past the Type-1 gate — same-name const with divergent meta")
				}
				return prop.WrapProp(defThm)
			}
			if w, ok := cache.Load(t); ok {
				return w
			}
			var w *prop.PropWrapper
			switch t := t.Core().(type) {
			case core.AppliedTerm:
				funEq := walk(t.Fun())
				argEq := walk(t.Arg())
				w = combineAppliedRewriteFast(t, funEq, argEq)
			case core.AbsTerm:
				if thm := walk(t.Body()); thm != nil {
					w = thm.Abs(t.Var())
				}
			}
			cache.Store(t, w)
			return w
		}
		return walk
	}
	rewriteDefThenBeta := func(t core.Term) *prop.PropWrapper {
		w := makeWalk(ext.PtrMemoFor[*prop.PropWrapper](t))(t)
		if w == nil {
			return nil
		}
		return w.RewriteConclRhs(InstanceNormal(read))
	}
	return rewriteDefThenBeta, true
}

// combineAppliedRewriteFast mirrors prop.combineAppliedRewrite (which is
// package-private to prop). Combines an Applied-term's fun/arg rewrites
// into a single equality via Apply / RightApply / LeftApply — a
// standard congruence rule on function application.
func combineAppliedRewriteFast(t AppliedTerm, funEq, argEq *prop.PropWrapper) *prop.PropWrapper {
	if funEq != nil && argEq != nil {
		return funEq.Apply(argEq)
	} else if funEq != nil {
		return funEq.RightApply(t.Arg())
	} else if argEq != nil {
		return argEq.LeftApply(t.Fun())
	}
	return nil
}
