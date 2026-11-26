package engine

import (
	"fmt"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// This file implements type adaptation for the `instantiate` tactic: a
// polymorphic ∀-hyp (binder types over the lemma's NAMED type vars,
// e.g. `∀s:(A→bool). …`) is grounded at a goal term whose type carries
// the session's FRESH anonymous type vars (`s₀ : ?27361→bool`, minted
// by strip_quant on a session goal). Without it the author re-loads
// the lemma with `type_specialize` at a var name only discoverable
// from error text, then redoes the instantiation ladder.
//
// SOUNDNESS SHAPE — why this is an engine-level re-derivation, not a
// tactic-level hyp rewrite: a sequent's type vars are scoped across the
// WHOLE Prop (hyps + conclusion together — core.PropTypeInst
// substitutes in all of them at once; Term.AlphaEquals is type-exact).
// There is NO kernel rule `H(A) ⊢ H(σA)` for a hypothesis H — as an
// implication it is false (the assumption is at one fixed, if
// arbitrary, type). So a SubGoals reconstruction that swapped a hyp for
// its σ-instance could never discharge back to the original goal; the
// MakeSubGoals IsStronger assert would reject it. What IS sound is
// re-deriving the fact at σ from a THEOREM: when the hyp's statement is
// a registry entry's, the σ-instance is just another instance of that
// (type-polymorphic) entry. The adaptation therefore replays the exact
// machinery `lemma` + `type_specialize` uses:
//
//	clear_hyps(stale hyp)                    — weakening, always sound
//	lemma_preserve(H[σ], source=entry key)   — claim child ⊢ H[σ]
//	  closed via the type-instance channel against the entry
//	  (applyAutoMatchTypeInstanceOnRoots — same closer as
//	  tryCloseAsTypeVariantOfEntry / lemma+type_specialize)
//	specialize(H[σ] at the witnesses)
//
// All three are existing recorded ministeps — no new proto shapes, so
// emit/replay are untouched (the applyLemmaTermSpecializeChain
// precedent). A hyp no entry states (mid-ladder derived forms, ad-hoc
// asserts) fails LOUDLY with the computed σ and the manual recipe —
// never a silent partial adaptation.

// instantiateAdaptation carries the σ-adaptation computed by
// resolveInstantiateWitnesses when at least one witness required a
// hyp-side type substitution (or the agent supplied an explicit
// `type_specialize`). nil means the exact path applies (all binder
// types equal their witness types).
type instantiateAdaptation struct {
	// specialized is the hyp's statement with σ applied (residual
	// unmatched type vars keep their original names).
	specialized core.Prop
	// sigma is the display form of the substitution, keyed by the
	// hyp's ORIGINAL type-var names (for error messages / recipes).
	sigma map[string]string
}

func (a *instantiateAdaptation) sigmaRecipe() string {
	names := make([]string, 0, len(a.sigma))
	for k := range a.sigma {
		names = append(names, k)
	}
	sort.Strings(names)
	parts := make([]string, 0, len(names))
	for _, k := range names {
		parts = append(parts, fmt.Sprintf("%q:%q", k, a.sigma[k]))
	}
	return "{" + strings.Join(parts, ",") + "}"
}

// resolveInstantiateWitnesses resolves the agent's witness spellings
// against the ∀-hyp's stated binders, read through its leading
// implications as Fact.At and Specialize read them (nextStatedBinder):
// `∀c. c ∈ s ⇒ ∀ε. &0 < ε ⇒ …` takes c, then ε. Exact path: every binder
// type equals its witness's type — returns (witnesses, nil, nil) and
// the caller runs the plain ApplySpecialize. Adaptive path: when a
// witness's type differs from its binder's but the binder type MATCHES
// it under a substitution of the hyp's type vars (hyp side only — the
// witness stays rigid; core.MatchTypeInto with the hyp's type-var
// names as the instantiable set), the substitution accumulates
// across rungs and the σ-specialized hyp statement is returned for the
// re-derivation chain. An explicit typeSpec map (the `type_specialize`
// escape hatch) seeds σ up front; unknown names are a hard error.
//
// Error messages carry the exact path's wording (terms[%d] prefixes,
// singleConst bare form), so an unadaptable failure reads the same on
// either path.
func (e *Engine) resolveInstantiateWitnesses(
	goal core.Prop,
	hyp core.Term,
	spellings []string,
	singleConst bool,
	typeSpec map[string]string,
	family *familyScope,
) ([]core.Term, *instantiateAdaptation, error) {
	rungErr := func(i int, err error) error {
		if singleConst {
			return err
		}
		return fmt.Errorf("instantiate terms[%d]: %w", i, err)
	}

	hypProp := prop.MakeProp(hyp).Core()
	origNames := collectLemmaTypeVarNames(hypProp)

	// No type-var freshening here, unlike the term_specialize path
	// (freshenLemmaTypeVars): a LEMMA being loaded is a separate scope
	// where a name shared with the goal is a coincidence to be kept
	// apart, but a resident HYP's type vars ARE sequent vars — a hyp
	// var named A and a witness-type var named A are the SAME variable.
	// Matching with original names makes MatchTypeInto's name-keyed env
	// enforce exactly the right consistency: a shared var binds
	// identically (dropped by dropIdentityTypeSubsts → no adaptation),
	// and a later rung demanding a conflicting instance for an
	// already-pinned var is correctly rejected. Freshening instead
	// manufactured phantom σ entries (♭A→A) for every shared var — the
	// TestSetFoldStage_LemmaPlusInstantiate_PreservesPolyBinderType shape.
	instantiable := func(v core.VarType) bool {
		return origNames[string(v.Name())]
	}

	// Explicit escape hatch: seed σ from type_specialize. Validated
	// against the hyp's own type-var names — a typo'd name fails fast,
	// mirroring buildSpecializedLemma's contract for `lemma`.
	var σ []core.TypeSubst
	sigmaDisplay := map[string]string{}
	specNames := make([]string, 0, len(typeSpec))
	for name := range typeSpec {
		specNames = append(specNames, name)
	}
	sort.Strings(specNames)
	for _, name := range specNames {
		spelling := typeSpec[name]
		if !origNames[name] {
			return nil, nil, fmt.Errorf(
				"instantiate type_specialize: type-variable %q not found in hyp %s; available: %v",
				name, ext.PrintTerm(hyp), sortedKeys(origNames))
		}
		t, terr := dsl.ParseTypeText(spelling)
		if terr != nil {
			return nil, nil, fmt.Errorf(
				"instantiate type_specialize: cannot parse type %q for variable %q: %w",
				spelling, name, terr)
		}
		σ = append(σ, core.MakeTypeSubst(core.MakeVarType(core.TypeName(name)), t))
		sigmaDisplay[name] = ext.FormatType(t)
	}

	current := prop.WrapProp(hypProp)
	if clean := dropIdentityTypeSubsts(σ); len(clean) > 0 {
		current = prop.WrapProp(core.PropTypeInst(current.Core(), clean...))
	}

	witnesses := make([]core.Term, 0, len(spellings))
	cur := current.Conclusion()
	for i, spelling := range spellings {
		abs := nextStatedBinder(cur)
		if abs.IsZero() {
			return nil, nil, fmt.Errorf(
				"instantiate terms[%d]: the hyp's binders are exhausted (it binds %d ∀-binders, those behind its antecedents counted, got %d terms)",
				i, i, len(spellings))
		}
		binderType := abs.Var().Type()

		w, werr := e.resolveTermWithFallback(spelling, goal, binderType, family)
		if werr != nil {
			// The typed resolve failed — retry untyped. A hit means the
			// term exists in goal scope at a DIFFERENT type: the
			// adaptation candidate. A miss means the spelling is
			// genuinely bad; surface the untyped error (unbound name /
			// parse failure) rather than the misleading type-expectation
			// one.
			wu, uerr := e.resolveTermWithFallback(spelling, goal, nil, family)
			if uerr != nil {
				return nil, nil, rungErr(i, uerr)
			}
			w = wu
		}

		if !binderType.Equals(w.Type()) {
			before := len(σ)
			if !core.MatchTypeInto(binderType, w.Type(), instantiable, &σ) {
				σ = σ[:before] // MatchTypeInto may leave a partial env on failure
				return nil, nil, rungErr(i, fmt.Errorf(
					"binder type %s does not match witness %q of type %s "+
						"(and no substitution of the hyp's type vars reconciles them)",
					ext.FormatType(binderType), spelling, ext.FormatType(w.Type())))
			}
			for _, sub := range dropIdentityTypeSubsts(σ[before:]) {
				sigmaDisplay[string(sub.VarType.Name())] = ext.FormatType(sub.HolType)
			}
			if clean := dropIdentityTypeSubsts(σ); len(clean) > 0 {
				current = prop.WrapProp(core.PropTypeInst(current.Core(), clean...))
				cur = current.Conclusion()
				for range i {
					peeled := nextStatedBinder(cur)
					if peeled.IsZero() {
						panic(fmt.Sprintf(
							"instantiate type-adapt: ∀-prefix shrank under type substitution on %s",
							ext.PrintTerm(hyp)))
					}
					cur = peeled.Body()
				}
				abs = nextStatedBinder(cur)
				if abs.IsZero() {
					panic(fmt.Sprintf(
						"instantiate type-adapt: ∀-binder disappeared under type substitution on %s",
						ext.PrintTerm(hyp)))
				}
				if !abs.Var().Type().Equals(w.Type()) {
					// The σ that matched this rung must make the binder
					// type EQUAL the witness type (matching is exact
					// one-sided substitution). Anything else is a matcher
					// bug — fail the apply rather than ground at a type
					// the agent didn't ask for.
					return nil, nil, rungErr(i, fmt.Errorf(
						"internal: post-σ binder type %s still differs from witness %q of type %s",
						ext.FormatType(abs.Var().Type()), spelling,
						ext.FormatType(w.Type())))
				}
			}
		}

		witnesses = append(witnesses, w)
		cur = abs.Body()
	}

	clean := dropIdentityTypeSubsts(σ)
	if len(clean) == 0 {
		return witnesses, nil, nil
	}
	return witnesses, &instantiateAdaptation{
		specialized: core.PropTypeInst(hypProp, clean...),
		sigma:       sigmaDisplay,
	}, nil
}

// nextStatedBinder is the ∀ the stated binder order reaches next from
// t: t's own leading ∀, or the first one below its leading
// implications (skipLeadingGuards, term_specialize's reading) — the
// order Fact.At grounds a fact in and Specialize derives
// (tactic.SpecializeTactic), so a session tuple is the Go tuple. nil
// when no ∀ is reachable.
func nextStatedBinder(t core.Term) ext.AbsTerm {
	return ext.MatchesFORALL(skipLeadingGuards(t))
}

// applyInstantiateTypeAdapted runs the re-derivation chain for a
// σ-adapted instantiate on the clone:
//
//  1. clear_hyps — drop the stale hyp (its binder types cannot accept
//     the witnesses; keeping it alongside the σ-instance would only
//     poison refutation with a second wide ∀).
//  2. lemma_preserve of the σ-instance, with the backing entry's own
//     key as polymorphicSourceKey (emit's leaf resolution reads the
//     polymorphic entry, exactly like `lemma` + `type_specialize`).
//  3. specialize the installed σ-instance at the witnesses (`keep`
//     keeps the ∀-form available, mirroring the plain path's contract).
//  4. close the install's claim child (⊢ H[σ]) through the
//     type-instance channel.
//
// The chain must net EXACTLY one open subgoal — the specialize
// residual. Any other outcome (claim child failed to close, install
// consumed the lemma via a rewrite path) aborts the whole apply with a
// diagnosis; the clone is discarded by the caller, so a failed chain
// leaves no partial state.
func (e *Engine) applyInstantiateTypeAdapted(
	s *Session,
	clone *proof.GoalStackNode,
	hypIdx int,
	hyp core.Term,
	adapt *instantiateAdaptation,
	witnesses []core.Term,
	keep bool,
) error {
	notBacked := func(reason string) error {
		return fmt.Errorf(
			"instantiate: the witnesses' types require specializing the hyp's type vars "+
				"(σ = %s), which is only sound by re-deriving the hyp from a backing theorem "+
				"— a hyp's type vars are sequent-scoped, so there is no per-hyp type "+
				"instantiation rule. %s. Manual recipe: re-load the source lemma with "+
				"`type_specialize:%s` and redo its instantiation ladder (or `assert` the "+
				"σ-instance and prove it), then instantiate that hyp",
			adapt.sigmaRecipe(), reason, adapt.sigmaRecipe())
	}

	if s == nil {
		return notBacked("No session context to close the re-derivation's claim subgoal")
	}

	normalized, _ := (&prop.PreCNFCache{}).Normalize(prop.MakeProp(hyp))
	normKey := normalized.AlphaKey()
	// The backing theorem is the registry entry whose own key is the
	// hyp's normalized key — the statement the hyp was loaded from. A
	// derived or mid-ladder hyp is no entry's statement and has no
	// backing.
	entry, ok := entryByKey(string(normKey))
	if !ok {
		return notBacked(fmt.Sprintf(
			"No registry entry states this hyp (normKey=%s) — it is a derived/mid-ladder form", normKey))
	}
	entryKey := core.PropKey(entry.Key)
	entryNames := []string{entry.Name}
	srcProp := entry.Statement().Prop

	// 1. Drop the stale hyp.
	if !proof.ApplyClearHyps(clone, []int{hypIdx}) {
		return fmt.Errorf("instantiate type-adapt: internal: clear_hyps(%d) did not apply", hypIdx)
	}
	leaves := clone.UnsolvedLeaves()
	if len(leaves) != 1 {
		return fmt.Errorf("instantiate type-adapt: internal: clear_hyps left %d open leaves", len(leaves))
	}
	leaf := leaves[0]
	origHypKeys := make(map[core.TermKey]struct{}, leaf.Goal.NumHyps())
	for _, h := range leaf.Goal.Hyps() {
		origHypKeys[h.AlphaKey()] = struct{}{}
	}

	// 2. Install the σ-instance. Exact install (no speculative type
	// adaptation) — σ IS the resolved instantiation; the skip-adapt
	// rationale is the same as term_specialize's
	// (ApplyLemmaPreserveExactWithSource doc). The recorded source key
	// is the backing entry's own key, which emit's leaf resolution
	// direct-hits.
	if !proof.ApplyLemmaPreserveExactWithSource(leaf, adapt.specialized, entryKey) {
		return fmt.Errorf(
			"instantiate type-adapt: installing the σ-instance %s did not apply",
			prop.PrintProp(adapt.specialized))
	}

	// Closes the install's claim child (⊢ H[σ]) through the
	// type-instance channel — the same closer `lemma`/`lean_rw` +
	// type_specialize rely on (see runAutoMatchTypeInstance).
	closeClaim := func() {
		s.applyAutoMatchTypeInstanceOnRoots(
			[]*proof.GoalStackNode{clone}, entryKey, srcProp,
			entryNames, s.autoMatchCache)
	}

	// 3. Ground the installed σ-instance. (No free-var witnesses on this
	// path — σ-instances of entry statements are hyp-free ∀-closed props; the
	// lemma arg only enables the reproduction-child skip, a no-op here.)
	residual, installedHyp, found := findLemmaResidualLeaf(
		clone, origHypKeys, adapt.specialized, nil)
	if !found {
		// The install consumed the σ-instance directly against the goal
		// instead of landing it as a hyp. One such outcome is
		// acceptable: the σ-instance PROVES the goal outright
		// (IsStronger / backward-chain — the goal's conclusion is an
		// instance of the adapted hyp), in which case closing the claim
		// child leaves zero open leaves — strictly more progress than
		// the requested grounding, and visible to the agent as
		// Effect:"close". Any partially-rewritten residual is rejected:
		// it is not the instance-as-hyp the agent asked for.
		closeClaim()
		if len(clone.UnsolvedLeaves()) == 0 {
			return nil
		}
		return fmt.Errorf(
			"instantiate type-adapt: the σ-instance was consumed by the install's rewrite "+
				"path instead of landing as a ∀-hyp (σ = %s). Use `lean_rw` with "+
				"`type_specialize` if a rewrite is what you want, or `lemma` + "+
				"`type_specialize:%s` + `instantiate` for the hyp form",
			adapt.sigmaRecipe(), adapt.sigmaRecipe())
	}
	cur := installedHyp
	for i, w := range witnesses {
		abs := ext.MatchesFORALL(cur)
		if abs.IsZero() {
			return fmt.Errorf(
				"instantiate type-adapt: installed σ-instance exhausted its ∀-prefix at "+
					"witness %d (install may have re-generalized binders; installed form: %s)",
				i, ext.PrintTerm(installedHyp))
		}
		if !abs.Var().Type().Equals(w.Type()) {
			return fmt.Errorf(
				"instantiate type-adapt: installed σ-instance binder %d has type %s but "+
					"witness has type %s (install mutated the resolved types; installed form: %s)",
				i, ext.FormatType(abs.Var().Type()), ext.FormatType(w.Type()),
				ext.PrintTerm(installedHyp))
		}
		cur = abs.Body()
	}
	newIdx, ok := findHypIndexByKey(residual.Goal, installedHyp.AlphaKey())
	if !ok {
		return fmt.Errorf("instantiate type-adapt: internal: installed hyp vanished from the residual leaf")
	}
	if !proof.ApplySpecialize(residual,
		[]proof.SpecializeHyp{proof.InstHyp(newIdx, witnesses...)}, keep) {
		return fmt.Errorf(
			"instantiate type-adapt: specialize of the σ-instance at %d witness(es) made "+
				"no progress (the ground instance may already be in scope)", len(witnesses))
	}

	// 4. Close the claim child.
	closeClaim()

	// Net-shape invariant: at most the specialize residual stays open
	// (zero means the close pass also proved the residual — a full
	// close). More than one open leaf means the claim child did not
	// close: abort the apply rather than leave the agent an unexpected
	// `⊢ H[σ]` sibling it never asked for.
	remaining := clone.UnsolvedLeaves()
	if len(remaining) > 1 {
		open := make([]string, 0, len(remaining))
		for _, l := range remaining {
			open = append(open, prop.PrintProp(l.Goal))
		}
		return fmt.Errorf(
			"instantiate type-adapt: the σ-instance claim subgoal did not close through "+
				"the type-instance channel (backing entry %s); open leaves: %s",
			entry.Name, strings.Join(open, " | "))
	}
	return nil
}
