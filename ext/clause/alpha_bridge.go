// alpha_bridge.go — the NESTED extension of the ALPHA-MERGE chain.
//
// A nested denote (the image of an image, an insert over a union) mints an inner
// symbol β parameterized over the enclosing Skolem function. Within one
// hypothesis, β's two occurrences use β-DISTINCT instantiations of that
// parameter — the wit side carries β(ƒ₀, g) while the intro side carries
// β(λg.g, y) — which are semantically equal (β depends on (f, h) only
// through f(h)) but out of reach of the first-order matchFlex that
// alphaDirClause drives, so the OUTER symbol pair declines to merge.
//
// The fix derives, from β's OWN wit/intro defining clauses, the
// η-expansion canonicalization equality
//
//	(λf.λh. β(λg.g, f(h))) = β
//
// and uses it to canonicalize the stuck outer wits: β(ƒ₀, g) becomes
// β(λg.g, ƒ₀(g)) — which the outer intro's pattern β(λg.g, y) matches at
// y := ƒ₀(g) — while an already-canonical β(λg.g, y) β-reduces back to
// itself (the bridge is a one-pass idempotent normalizer, so applying it
// to an already-canonical clause is a clean no-op).
//
// Chain per stuck pair (the CNF / RefuteProp / cnf_proofs cache keys are
// untouched — derivations only, per the FUNEXT lesson):
//
//	r1: resolveClause(wit_β, intro_β′@{f:=λg.g}) → ∀f,h. ¬β(f,h) ∨ β(λg.g,f(h))  [_RuleResolve]
//	r2: resolveClause(wit_β′@{f:=λg.g}, intro_β) → ∀f,h. ¬β(λg.g,f(h)) ∨ β(f,h)  [_RuleResolve]
//	br: FunextFromIffPair(r1, r2)                → (λf.λh.β(λg.g,f(h))) = β      [_RuleFunext]
//	    (partial contraction: Abs every ∀, η per side — the funextContract
//	    generalization; the λ-sided FUNCTION-typed equality is a legal
//	    clause literal, unlike the bool ∀-iff form IsDisjunctive rejects)
//	e4: eqApplyRewrite(br, wit_outer, {f↦ƒ₀})    → canonicalized twin wit        [_RuleEqApply]
//	    (NEW recipe rule, clause.proto 10: the raw r→l orientation of br is
//	    self-expanding — β occurs inside the λ-side, so EqRewrite's IsSub
//	    guard rightly refuses it, the 350eb94b9 treadmill class; applying
//	    both sides at the wit's closed instance prefix FIRST turns the
//	    shrunken side into the partial application β(ƒ₀), which genuinely
//	    occurs in the wit's spine, and the introduced β-redexes fold back
//	    through BasicRewrite)
//
// The next fixpoint round of DeriveAlphaMergeChain then merges the outer
// pair through the ORDINARY alphaDirClause path against the twin wits.
//
// The λg.g pin is not hardcoded: it is read off the CLOSED argument
// positions of the intro-side mismatch instance discovered by the
// mismatch-collecting matcher below, so variants of the class pin
// whatever closed instance their intro side carries.

package clause

import (
	"maps"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// _alphaMismatch is one same-symbol instance mismatch found while flex-
// matching an outer intro body against an outer wit body: sym(argsN) (the
// intro side, over the intro clause's binders) vs sym(argsW) (the wit
// side, over the wit clause's binders).
type _alphaMismatch struct {
	sym   VarTerm
	argsN []Term
	argsW []Term
}

// betaNormTerm β/η-normalizes a bare term (identity when already normal).
func betaNormTerm(t Term) Term {
	if w := prop.DeepBetaEta(t); w != nil {
		return Rhs(w)
	}
	return t
}

// matchFlexCollect is matchFlex with an escape hatch for the nested shape:
// when structural descent fails but both sides are FULL (bool-typed)
// applications of the SAME rigid var head accepted by isSym (a denote
// symbol with defining clauses), the pair is recorded as a mismatch and
// treated as matched, so the diagnosis can see whether the REST of the
// bodies align. Bindings accumulate exactly as in matchFlex. The IsBool
// gate keeps PARTIAL applications (β(λg.g) vs β(ƒ₀), hit while descending
// into the full instance's spine) from being recorded — the full-instance
// pair is recorded by the enclosing call instead.
func matchFlexCollect(pattern, target Term, subst map[core.TermKey]Term,
	vars map[core.TermKey]VarTerm, isFlex func(VarTerm) bool,
	isSym func(VarTerm) bool, out *[]_alphaMismatch) bool {
	if v, ok := pattern.AsVar(); ok && isFlex(v) {
		if b, seen := subst[v.AlphaKey()]; seen {
			return b.Equals(target)
		}
		subst[v.AlphaKey()] = target
		vars[v.AlphaKey()] = v
		return true
	}
	pApp, pok := pattern.AsAppliedTerm()
	tApp, tok := target.AsAppliedTerm()
	if pok && tok &&
		matchFlexCollect(pApp.Fun(), tApp.Fun(), subst, vars, isFlex, isSym, out) &&
		matchFlexCollect(pApp.Arg(), tApp.Arg(), subst, vars, isFlex, isSym, out) {
		return true
	}
	if pattern.Equals(target) {
		return true
	}
	if !IsBool(pattern) || !IsBool(target) {
		return false
	}
	pv, pargs := stripAppliedVar(pattern)
	tv, targs := stripAppliedVar(target)
	if !pv.IsZero() && !tv.IsZero() && pv.Equals(tv) && !isFlex(pv) && isSym(pv) &&
		len(pargs) == len(targs) && len(pargs) > 0 {
		*out = append(*out, _alphaMismatch{sym: pv, argsN: pargs, argsW: targs})
		return true
	}
	return false
}

// unifyFlex is a small two-sided syntactic unifier: vars accepted by
// isFlex bind on EITHER side (matchFlex binds pattern-side only, which is
// not enough for the r2 direction, where the solved positions live on the
// pinned-wit side). Bindings chain through subst as they are found; the
// caller verifies the final substitution closes the pair.
func unifyFlex(a, b Term, subst map[core.TermKey]Term,
	vars map[core.TermKey]VarTerm, isFlex func(VarTerm) bool) bool {
	a = chaseBinding(a, subst, isFlex)
	b = chaseBinding(b, subst, isFlex)
	if av, ok := a.AsVar(); ok && isFlex(av) {
		if b.Equals(av) {
			return true
		}
		if b.HasFree(av) {
			return false // occurs
		}
		subst[av.AlphaKey()] = b
		vars[av.AlphaKey()] = av
		return true
	}
	if bv, ok := b.AsVar(); ok && isFlex(bv) {
		if a.HasFree(bv) {
			return false
		}
		subst[bv.AlphaKey()] = a
		vars[bv.AlphaKey()] = bv
		return true
	}
	aApp, aok := a.AsAppliedTerm()
	bApp, bok := b.AsAppliedTerm()
	if aok && bok {
		return unifyFlex(aApp.Fun(), bApp.Fun(), subst, vars, isFlex) &&
			unifyFlex(aApp.Arg(), bApp.Arg(), subst, vars, isFlex)
	}
	return a.Equals(b)
}

// chaseBinding dereferences a flex var through the accumulated bindings.
func chaseBinding(t Term, subst map[core.TermKey]Term, isFlex func(VarTerm) bool) Term {
	for {
		v, ok := t.AsVar()
		if !ok || !isFlex(v) {
			return t
		}
		b, seen := subst[v.AlphaKey()]
		if !seen {
			return t
		}
		t = b
	}
}

// substsFromBindings renders an accumulated binding map as a deterministic
// TermSubstsGroup (sorted by the substituted var, identities dropped,
// binding chains resolved to a fixpoint — finite, unifyFlex occurs-checks).
func substsFromBindings(subst map[core.TermKey]Term,
	vars map[core.TermKey]VarTerm) TermSubstsGroup {
	for range len(subst) + 1 {
		changed := false
		for k, t := range subst {
			t2 := t
			for k2, b := range subst {
				v2 := vars[k2]
				if k2 != k && t2.HasFree(v2) {
					t2 = t2.Substitute(core.MakeTermSubst(v2, b))
				}
			}
			if !t2.Equals(t) {
				subst[k] = t2
				changed = true
			}
		}
		if !changed {
			break
		}
	}
	keys := slices.SortedFunc(maps.Keys(vars),
		func(a, b core.TermKey) int { return vars[a].Compare(vars[b]) })
	var out TermSubstsGroup
	for _, k := range keys {
		v, b := vars[k], subst[k]
		if b == nil || b.Equals(v) {
			continue
		}
		out = append(out, core.MakeTermSubst(v, b))
	}
	return out
}

// applyTermArgs applies sym to the given argument terms.
func applyTermArgs(sym VarTerm, args []Term) Term {
	t := Term(sym)
	for _, a := range args {
		t = Apply(t, a)
	}
	return t
}

// deriveCanonBridge derives β's η-expansion canonicalization equality from
// β's own wit/intro clause pair, pinned at the CLOSED intro-side instance
// args (pins[k] == nil ⇒ frame position, kept universal). Returns the
// [r1, r2, br] steps, or nil when no wit/intro combination of β discharges
// both directions.
func deriveCanonBridge(beta *_alphaGroup, pins []Term) []*ClauseThm {
	for _, wb := range beta.wits {
		if len(wb.args) != len(pins) {
			continue
		}
		for _, ib := range beta.intros {
			// The bridge pins and instantiates β's intro positionally: a
			// one-conjunct intro at binder args.
			if len(ib.bodies) != 1 || len(ib.varArgs()) != len(pins) {
				continue
			}
			if steps := tryCanonBridge(beta.sym, wb, ib, pins); steps != nil {
				return steps
			}
		}
	}
	return nil
}

func tryCanonBridge(sym VarTerm, wb _witCand, ib _introCand, pins []Term) []*ClauseThm {
	// --- r1: wit general, intro pinned at the closed positions. ---
	ibR := introCandFor(ib.c.AvoidVarsCollision(wb.c), sym)
	if ibR == nil {
		return nil
	}
	r1 := canonBridgeDir(sym, wb, *ibR, pins, false)
	if r1 == nil {
		return nil
	}
	// --- r2: wit pinned, intro general. ---
	wbR := witCandFor(wb.c.AvoidVarsCollision(ib.c), sym)
	if wbR == nil {
		return nil
	}
	r2 := canonBridgeDir(sym, *wbR, ib, pins, true)
	if r2 == nil {
		return nil
	}
	br := FunextFromIffPair(r1.ConclClause(), r2.ConclClause())
	if br == nil {
		return nil
	}
	// The bridge must be a GROUND function-typed equality with the bare β
	// on the right — the orientation canonicalizeThroughBridge relies on
	// (rewriteEqRight flips it to β = λ-form, so bare-β occurrences
	// rewrite into the pinned λ-form and β-reduce into canonical
	// instances).
	c := br.ConclClause()
	l, r, ok := MatchesEQ(c.EffectiveBody())
	if !ok || c.EffectiveNumLits() != 1 || !c.univBoundVars.Empty() ||
		!r.Equals(sym) || !l.HasFree(sym) {
		return nil
	}
	return []*ClauseThm{r1, r2, br}
}

// canonBridgeDir builds one direction of the bridge pair via resolveClause
// with a hand-computed unifier. When flip is false the intro side carries
// the pins; when flip is true the wit side does. The unsolved binder vars
// of both clauses are flex for the two-sided unifier; whatever it solves
// is recorded in the recipe substs, and the remaining binders re-generalize
// into the resolvent's ∀-prefix (the FRAME of the bridge).
func canonBridgeDir(
	sym VarTerm, wb _witCand, ib _introCand, pins []Term, flip bool) *ClauseThm {

	ibArgs := ib.varArgs()
	if ibArgs == nil {
		return nil
	}
	pinOf := func(cands []VarTerm, pinned bool) TermSubstsGroup {
		if !pinned {
			return nil
		}
		var g TermSubstsGroup
		for k, p := range pins {
			if p == nil {
				continue
			}
			g = append(g, core.MakeTermSubst(cands[k], p))
		}
		return g
	}
	wbPins := pinOf(wb.args, flip)
	ibPins := pinOf(ibArgs, !flip)

	witBody := wb.body
	if len(wbPins) > 0 {
		witBody = betaNormTerm(witBody.Substitute(wbPins...))
	}
	introBody := ib.bodies[0]
	if len(ibPins) > 0 {
		introBody = betaNormTerm(introBody.Substitute(ibPins...))
	}

	pinnedKeys := map[core.TermKey]bool{}
	for _, s := range wbPins {
		pinnedKeys[s.VarTerm.AlphaKey()] = true
	}
	for _, s := range ibPins {
		pinnedKeys[s.VarTerm.AlphaKey()] = true
	}
	isFlex := func(v VarTerm) bool {
		if pinnedKeys[v.AlphaKey()] {
			return false
		}
		return ib.c.univBoundVars.Has(v) || wb.c.univBoundVars.Has(v)
	}

	subst := map[core.TermKey]Term{}
	vars := map[core.TermKey]VarTerm{}
	if !unifyFlex(introBody, witBody, subst, vars, isFlex) {
		return nil
	}
	solved := substsFromBindings(subst, vars)

	// The unifier must really close the literal pair after β-reduction.
	if !betaNormTerm(introBody.Substitute(solved...)).
		AlphaEquals(betaNormTerm(witBody.Substitute(solved...))) {
		return nil
	}

	var substs TermSubstsGroup
	substs = append(substs, wbPins...)
	substs = append(substs, ibPins...)
	substs = append(substs, solved...)
	slices.SortFunc(substs, func(a, b TermSubst) int {
		return a.VarTerm.Compare(b.VarTerm)
	})

	// Expected resolvent literals: β at each side's args with pins and the
	// solved bindings applied.
	instArgs := func(vs []VarTerm, pinned bool) []Term {
		out := make([]Term, len(vs))
		for k, v := range vs {
			t := Term(v)
			if pinned && pins[k] != nil {
				t = pins[k]
			}
			for _, s := range substs {
				if t.HasFree(s.VarTerm) {
					t = t.Substitute(s)
				}
			}
			out[k] = betaNormTerm(t)
		}
		return out
	}
	expectNeg := applyTermArgs(sym, instArgs(wb.args, flip))
	expectPos := applyTermArgs(sym, instArgs(ibArgs, !flip))

	for _, thm := range resolveClause(wb.c, ib.c, substs, wb.litIndex, rewriteWhole) {
		lits := DecomposesOR(thm.ConclClause().EffectiveBody())
		if len(lits) != 2 {
			continue
		}
		pos, neg, ok := splitPosNeg(lits)
		if ok && pos.AlphaEquals(expectPos) && neg.AlphaEquals(expectNeg) {
			return thm.withRecipe(&deduceRecipe{
				rule:        _RuleResolve,
				inputs:      []*Clause{wb.c, ib.c},
				litIndex:    wb.litIndex,
				rewriteType: rewriteWhole,
				substs:      substs,
			})
		}
	}
	return nil
}

// eqApplyRewrite — the _RuleEqApply builder. Given the GENERAL bridge
// equality clause `(λx⃗. body) = f` (ground, 1-lit, function-typed), the
// raw r→l orientation is self-expanding (f occurs inside the λ-side, so
// EqRewrite's IsSub guard correctly refuses it — the 350eb94b9 treadmill
// class). Applying BOTH sides at the pinned λ-binder prefix first
// dissolves that: the equality becomes
//
//	(λrest. body[pins]) = f(a⃗)
//
// whose flipped lhs f(a⃗) is a PARTIAL APPLICATION that genuinely occurs
// in the target (β(ƒ₀, g) carries the β(ƒ₀) spine prefix) and does NOT
// occur in the λ-side. The EqRewrite then fires, and the β-redexes it
// introduces fold back through BasicRewrite — β(ƒ₀, g) becomes the
// canonical β(λg.g, ƒ₀(g)).
//
// Deterministic: pins are recorded in the recipe (keyed by the λ-binder
// vars, matched positionally against the λ-prefix). nil when the pins
// don't cover a λ-binder prefix, the rewrite doesn't fire, or the result
// degenerates.
func eqApplyRewrite(eqc, target *Clause, pins TermSubstsGroup) *ClauseThm {
	if len(pins) == 0 || eqc.EffectiveNumLits() != 1 ||
		!eqc.univBoundVars.Empty() || eqc.Equivalent(target) {
		return nil
	}
	if _, _, ok := MatchesEQ(eqc.EffectiveBody()); !ok {
		return nil
	}
	pinOf := func(v VarTerm) Term {
		for _, s := range pins {
			if s.VarTerm.Equals(v) {
				return s.Term
			}
		}
		return nil
	}

	// {eqc.Term} ⊢ (λx⃗.body) = f, applied at the pinned binder prefix.
	eq := eqc.Specialize(nil)
	applied := 0
	for {
		l, _, ok := MatchesEQ(eq.Conclusion())
		if !ok {
			return nil
		}
		abs, aok := l.AsAbsTerm()
		if !aok {
			break
		}
		p := pinOf(abs.Var())
		if p == nil {
			break
		}
		eq = eq.RightApply(p).RewriteConcl(prop.DeepBetaEta)
		applied++
	}
	if applied != len(pins) {
		return nil // pins must be exactly a λ-binder prefix
	}
	eq = eq.EqSym()

	// Rewrite the target's opened body through the pinned equality.
	thm := target.Specialize(nil)
	u := prop.EqRewrite(eq)(thm.Conclusion())
	if u == nil {
		return nil // no occurrence (already canonical, or no β at all)
	}
	thm = u.EqMP(thm).RewriteConcl(BasicRewrite).
		RewriteConcl(ClauseDeduceFinalize)
	if thm.Conclusion().Equals(T) {
		return nil
	}
	thm = prop.ForAllConclFreeVars(thm)
	Assert(thm.NumHyps() <= 2)

	for _, cand := range makeConclDisjunct(thm) {
		cand, conclClause := simplifyConclusion(cand)
		if conclClause.EquatesT() ||
			conclClause.Equivalent(eqc) || conclClause.Equivalent(target) {
			continue
		}
		// The canonicalization is literal-preserving: same literal count,
		// just rewritten instances. Anything else is a degenerate result.
		if len(DecomposesOR(conclClause.EffectiveBody())) != len(target.literals) {
			continue
		}
		hypClauses := make([]*Clause, 0, 2)
		if cand.HasHyp(eqc.Term()) {
			hypClauses = append(hypClauses, eqc)
		}
		if cand.HasHyp(target.Term()) {
			hypClauses = append(hypClauses, target)
		}
		return MakeClauseThm(cand.AsThmCert(), conclClause, hypClauses...).
			withRecipe(&deduceRecipe{
				rule:   _RuleEqApply,
				inputs: []*Clause{eqc, target},
				substs: pins,
			})
	}
	return nil
}

// canonicalizeThroughBridge canonicalizes one wit clause through the
// general bridge, pinned at the wit's own instance prefix (e4Args — the
// closed leading args of its β-occurrence, e.g. [ƒ₀]). nil when the
// clause is untouched.
func canonicalizeThroughBridge(bridge, target *Clause, e4Args []Term) *ClauseThm {
	l, _, ok := MatchesEQ(bridge.EffectiveBody())
	if !ok {
		return nil
	}
	vars, _ := MatchesAbs(l)
	if len(e4Args) == 0 || len(e4Args) > len(vars) {
		return nil
	}
	var pins TermSubstsGroup
	for k, a := range e4Args {
		pins = append(pins, core.MakeTermSubst(vars[k], a))
	}
	return eqApplyRewrite(bridge, target, pins)
}

// deriveNestedBridges handles a symbol pair alphaMergePair declined: it
// diagnoses each wit×intro direction for same-symbol instance mismatches,
// derives the inner symbol's canonicalization bridge, and canonicalizes
// the stuck pair's WIT clauses through it (one bridge serves both
// directions — it is fully general in the enclosing Skolem function). The
// returned steps are in dependency order; `seen` dedups emissions across
// rounds, so a pair that STILL declines after bridging stops producing
// steps and the fixpoint loop terminates.
func deriveNestedBridges(
	gi, gj *_alphaGroup, groups []*_alphaGroup,
	seen map[core.TermKey]bool) []*ClauseThm {

	groupOf := func(v VarTerm) *_alphaGroup {
		for _, g := range groups {
			if g.sym.Equals(v) && len(g.wits) > 0 && len(g.intros) > 0 {
				return g
			}
		}
		return nil
	}
	isSym := func(v VarTerm) bool { return groupOf(v) != nil }

	// Bridges are cached per (β, pins) within this call so twin steps
	// reference the SAME derived clause pointer (the proof DAG connects
	// steps by clause identity).
	bridgeCache := map[string][]*ClauseThm{}

	var out []*ClauseThm
	emit := func(steps ...*ClauseThm) {
		for _, s := range steps {
			key := s.ConclClause().Term().AlphaKey()
			if seen[key] {
				continue
			}
			seen[key] = true
			out = append(out, s)
		}
	}

	dir := func(gw, gn *_alphaGroup) {
		for _, w := range gw.wits {
			for _, n := range gn.intros {
				// Diagnose: does the intro body match the wit body modulo
				// same-symbol instance mismatches? (A one-conjunct intro;
				// the nesting this bridges sits inside its one literal.)
				if len(n.bodies) != 1 {
					continue
				}
				subst := map[core.TermKey]Term{}
				vars := map[core.TermKey]VarTerm{}
				var mms []_alphaMismatch
				diagOK := matchFlexCollect(n.bodies[0], w.body, subst, vars,
					n.c.univBoundVars.Has, isSym, &mms)
				if !diagOK || len(mms) == 0 {
					continue
				}
				for _, mm := range mms {
					beta := groupOf(mm.sym)
					if beta == nil {
						continue
					}
					// Pins: the CLOSED intro-side args (no dependence on
					// the intro clause's binders). Frame positions stay
					// universal. A fully-closed or fully-open instance has
					// nothing to canonicalize against, and the e4 step
					// needs the pinned positions to form a leading prefix
					// of the argument spine (it applies the bridge at the
					// wit instance's closed prefix).
					pins := make([]Term, len(mm.argsN))
					pinned := 0
					notIntroBound := func(v VarTerm) bool {
						return !n.c.univBoundVars.Has(v)
					}
					for k, a := range mm.argsN {
						if a.AllFree(notIntroBound) {
							pins[k] = a
							pinned++
						}
					}
					if pinned == 0 || pinned == len(pins) {
						continue
					}
					prefixOK := true
					for k := range pins {
						if (pins[k] != nil) != (k < pinned) {
							prefixOK = false
							break
						}
					}
					if !prefixOK {
						continue
					}
					// The wit's instance at the pinned prefix must be
					// closed wrt the wit clause's binders (it becomes the
					// e4 application argument).
					e4Args := mm.argsW[:pinned]
					notWitBound := func(v VarTerm) bool {
						return !w.c.univBoundVars.Has(v)
					}
					argsOK := true
					for _, a := range e4Args {
						if !a.AllFree(notWitBound) {
							argsOK = false
							break
						}
					}
					if !argsOK {
						continue
					}
					cacheKey := bridgeCacheKey(mm.sym, pins)
					steps, cached := bridgeCache[cacheKey]
					if !cached {
						steps = deriveCanonBridge(beta, pins)
						bridgeCache[cacheKey] = steps
					}
					if steps == nil {
						continue
					}
					bridge := steps[2].ConclClause()
					// Canonicalize THIS wit at ITS instance prefix (the
					// sibling direction's wit is handled by its own
					// diagnosis in dir(gj, gi), reusing the cached bridge).
					twin := canonicalizeThroughBridge(bridge, w.c, e4Args)
					if twin == nil {
						continue
					}
					emit(steps...)
					emit(twin)
				}
			}
		}
	}
	dir(gi, gj)
	dir(gj, gi)
	return out
}

// bridgeCacheKey identifies one (β, pins) bridge derivation.
func bridgeCacheKey(sym VarTerm, pins []Term) string {
	var b strings.Builder
	b.WriteString(string(sym.AlphaKey()))
	for _, p := range pins {
		b.WriteString("|")
		if p != nil {
			b.WriteString(string(p.AlphaKey()))
		}
	}
	return b.String()
}
