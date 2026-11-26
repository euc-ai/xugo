// File: quantifier.go
//
// All quantifier-handling tactics live in this file. They split into
// two pairs by direction:
//
//	"Strip" / introduce direction (no agent input — peel one outer
//	quantifier off whichever side is shape-eligible):
//	  - concl ∀x.P(x) → ⊢ P(x)   (with x freshened)
//	  - hyp  ∃x.P(x) → P(x) ⊢ C  (with x freshened)
//	Both live inside `quantifierTactic`.
//
//	"Witness" / eliminate direction (agent supplies a witness term):
//	  - concl ⊢ ∃x.P(x) → ⊢ P(t)
//	      consumes the ∃ — single-use.
//	  - concl ⊢ ∃!x.P(x) → ⊢ P(t) ∧ (∀y. P(y) ⇒ y = t)
//	      consumes the ∃! — single-use.
//	  - hyp  ∀x.P(x), Γ ⊢ C → ∀x.P(x), P(t), Γ ⊢ C
//	      adds P(t), keeps the ∀ available for further instantiation.
//	`ConclExistsWitnessTactic` and `HypForallInstantiateTactic` cover
//	the two cases.
//
// All four route through the kernel-verified primitives in the prop
// package (`prop.InstExists`, `prop.InstForAll`, `ConclForAll`,
// `HypExists`) and chain via DeriveTrans — no hand-rolled
// substitution, capture-avoidance is the kernel's responsibility.

package tactic

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// StripQuantTactic handles goals containing quantifiers by removing
// universal quantifiers (∀) in the conclusion and existential
// quantifiers (∃) in the hypotheses, thereby simplifying the goal
// structure.
//
// Transformations:
//
//  1. For conclusion ∀x. P(x): Transforms to "... ⊢ P(x)" where x
//     becomes a free variable (to prove a universally quantified
//     statement, prove it for an arbitrary value).
//
//  2. For hypothesis ∃x. P(x): Transforms to "..., P(x) ⊢ C" where x
//     becomes a free variable (to use an existential hypothesis, work
//     with a specific but arbitrary witness).
//
// The tactic ensures proper variable handling through subscript
// renaming to avoid naming conflicts when introducing new free
// variables. For each transformation, a reconstruction function
// transforms the proof of the subgoal back into a proof of the
// original goal: for ∀-conclusions it adds the ∀ back via
// ConclForAll; for ∃-hypotheses it reintroduces the ∃ via HypExists.
//
// One call performs ONE of the two: a ∀-headed conclusion is stripped
// and the hyps are left alone; otherwise the first ∃-headed hyp is
// Skolemized. StripQuantAtTactic is the hyp-targeted sibling.
func StripQuantTactic(goal Prop) *SubGoals {
	if !ext.MatchesFORALL(goal.Conclusion()).IsZero() {
		concl := goal.Conclusion()
		if w := prop.SubscriptUnivVars(goal.HasFreeName)(concl); w != nil {
			concl = Rhs(w)
		}
		vars, body := ext.DecomposesFORALL(concl)
		goal0 := MakeProp(body, goal.Hyps()...)
		reconstruct := func(thms ...Prop) Prop {
			if thms[0].Conclusion().Equals(F) {
				return thms[0]
			}
			p := WrapProp(thms[0])
			for _, v := range vars.Backward() {
				p = p.ConclForAll(v)
			}
			return p
		}
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
	}

	for i := range goal.NumHyps() {
		if sg := hypExistsTacticAt(goal, i); sg != nil {
			return sg
		}
	}
	return nil
}

// StripQuantAtTactic is the hyp-targeted variant of StripQuantTactic:
// Skolemize the leading ∃-prefix of the hypothesis at hypIdx and
// nothing else — the conclusion stands as it is, ∀-headed or not,
// because the caller named a hypothesis. A membership in a set-builder
// whose reading is ∃-headed — `x ∈ {y | ∃z. …}`, the three-part
// `x ∈ {t | x̄ | φ}` — is Skolemized through its reading
// (throughMembershipAt). Returns nil when hypIdx is out of range or the
// hyp there is neither: the same "did not apply" contract as
// HypDisjTacticAt, so the wire layer reports a clean failure instead
// of Skolemizing a different hypothesis.
func StripQuantAtTactic(goal Prop, hypIdx int) *SubGoals {
	return StripQuantAtTacticUnder(goal, hypIdx, nil)
}

// StripQuantAtTacticUnder is StripQuantAtTactic under a scope wider
// than the goal (freshenBinders): no witness it fixes is a variable
// refused reports.
func StripQuantAtTacticUnder(goal Prop, hypIdx int, refused func(VarTerm) bool) *SubGoals {
	if hypIdx < 0 || hypIdx >= goal.NumHyps() {
		return nil
	}
	return throughMembershipAt(goal, hypIdx, func(goal Prop, i int) *SubGoals {
		return hypExistsTacticUnder(goal, i, refused)
	})
}

// freshenBinders is the strips' freshening pass over t — the goal's
// conclusion, or one of its hypotheses: subscript renames the binders
// of t apart from the goal's free names, and fixed reads off the result
// the variables the strip is about to fix.
//
// Fresh for the goal is not fresh for a scope wider than the goal: a
// proof's blocks declare variables the leaf at hand need not mention,
// and a later step may bring one into it. refused, when non-nil,
// reports a variable such a scope cannot take; the pass is then run
// again with that variable's name held as the goal's free names are,
// until no variable to be fixed is refused. Each round holds a name the
// round before did not, so the rounds end with the names the scope
// refuses. A nil refused is the goal alone.
func freshenBinders(goal Prop, t Term, subscript func(prop.TermNamePredicate) prop.Rewrite,
	fixed func(Term) []VarTerm, refused func(VarTerm) bool) Term {
	var held []TermName
	for {
		fresh := t
		avoid := func(n TermName) bool { return goal.HasFreeName(n) || slices.Contains(held, n) }
		if w := subscript(avoid)(t); w != nil {
			fresh = Rhs(w)
		}
		if refused == nil {
			return fresh
		}
		settled := true
		for _, v := range fixed(fresh) {
			if refused(v) {
				held = append(held, v.Name())
				settled = false
			}
		}
		if settled {
			return fresh
		}
	}
}

// hypExistsTacticAt is the shared per-hyp body: ∃-elimination on hyp
// i. Callers guarantee the index is in range; the shape check lives
// here so the pick-first loop and the at-index entry share exactly
// one implementation.
func hypExistsTacticAt(goal Prop, i int) *SubGoals { return hypExistsTacticUnder(goal, i, nil) }

// hypExistsTacticUnder is hypExistsTacticAt whose witnesses are none
// of the variables refused reports (freshenBinders).
func hypExistsTacticUnder(goal Prop, i int, refused func(VarTerm) bool) *SubGoals {
	vars, body, ok := existsWitnesses(goal, i, refused)
	if !ok {
		return nil
	}
	images := hypImages(goal, i, body)
	goal0 := makeImageProp(goal.Conclusion(), images)
	reconstruct := func(thms ...Prop) Prop {
		p := WrapProp(thms[0])
		if p.HasHyp(body) {
			_body := body
			for _, v := range vars.Backward() {
				p = p.HypExists(v, _body)
				_body = Exists(v)(_body)
			}
		}
		return p
	}
	// The Skolemized body descends from the ∃-hypothesis.
	return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, images)}, goal0)
}

// existsWitnesses is the ∃-elimination's reading of the hypothesis at
// i: the variables it fixes, one per binder of the leading ∃-prefix in
// the prefix's order, each renamed apart from the goal's free names and
// from what refused reports (freshenBinders), and the body under them.
// ok is false where the hypothesis is no ∃.
func existsWitnesses(goal Prop, i int, refused func(VarTerm) bool) (vars ext.VarList, body Term, ok bool) {
	h := goal.Hyp(i)
	if ext.MatchesEXISTS(h).IsZero() {
		return ext.VarList{}, nil, false
	}
	h = freshenBinders(goal, h, prop.SubscriptExistsVars, func(t Term) []VarTerm {
		witnesses, _ := ext.DecomposesEXISTS(t)
		return slices.Collect(witnesses.Iter())
	}, refused)
	vars, body = ext.DecomposesEXISTS(h)
	return vars, body, true
}

// ExistsWitnessesAt are the variables StripQuantAtTacticUnder fixes at
// the hypothesis hypIdx, one per binder of its leading ∃-prefix, in the
// prefix's order: witness k stands for binder k, whatever the two are
// named. The hypothesis is read as that strip reads it, an ∃ as written
// or a set-builder membership through its reading. nil where the strip
// does not apply.
func ExistsWitnessesAt(goal Prop, hypIdx int, refused func(VarTerm) bool) []VarTerm {
	if hypIdx < 0 || hypIdx >= goal.NumHyps() {
		return nil
	}
	if vars, _, ok := existsWitnesses(goal, hypIdx, refused); ok {
		return slices.Collect(vars.Iter())
	}
	read, at := membershipReadAt(goal, hypIdx)
	if read == nil {
		return nil
	}
	vars, _, ok := existsWitnesses(read.ChildGoal(0), at, refused)
	if !ok {
		return nil
	}
	return slices.Collect(vars.Iter())
}

// StripQuant1Tactic is the bounded single-binder sibling of
// StripQuantTactic: it peels EXACTLY ONE leading ∀ off the goal's
// conclusion, Skolemizing that binder to a fixed variable and leaving
// every inner quantifier intact:
//
//	Goal:    Γ ⊢ ∀x. P(x)
//	Subgoal: Γ ⊢ P(x₀)        (x₀ fresh; inner ∀/∃ in P untouched)
//
// Conclusion side ONLY — an ∃-hyp is never Skolemized here (that stays
// with StripQuantTactic). Returns nil when the conclusion is not
// ∀-headed.
//
// The freshening pass is the SAME SubscriptUnivVars deep rewrite
// StripQuantTactic runs, so n successive single strips mint exactly
// the names one strip-everything call would (x → x_0, clash → next
// subscript) — the two tactics stay name-compatible on any prefix.
func StripQuant1Tactic(goal Prop) *SubGoals { return StripQuant1TacticUnder(goal, nil) }

// StripQuant1TacticUnder is StripQuant1Tactic under a scope wider than
// the goal (freshenBinders): the variable it fixes is none that
// refused reports.
func StripQuant1TacticUnder(goal Prop, refused func(VarTerm) bool) *SubGoals {
	abs, ok := stripQuant1Opened(goal, refused)
	if !ok {
		return nil
	}
	v := abs.Var()
	goal0 := MakeProp(abs.Body(), goal.Hyps()...)
	reconstruct := func(thms ...Prop) Prop {
		if thms[0].Conclusion().Equals(F) {
			return thms[0]
		}
		return WrapProp(thms[0]).ConclForAll(v)
	}
	return MakeSubGoals(goal, reconstruct, goal0)
}

// stripQuant1Opened is the goal's leading ∀ as StripQuant1TacticUnder
// opens it, its binder renamed to the variable the strip fixes;
// ok=false where the conclusion is not ∀-headed.
func stripQuant1Opened(goal Prop, refused func(VarTerm) bool) (abs ext.AbsTerm, ok bool) {
	if ext.MatchesFORALL(goal.Conclusion()).IsZero() {
		return abs, false
	}
	concl := freshenBinders(goal, goal.Conclusion(), prop.SubscriptUnivVars, func(t Term) []VarTerm {
		return []VarTerm{ext.MatchesFORALL(t).Var()}
	}, refused)
	return ext.MatchesFORALL(concl), true
}

// StripQuant1Fixes is the variable StripQuant1TacticUnder fixes for the
// goal's leading ∀: the one the stripped body holds free where it
// mentions the binder, and the variable of that name all the same where
// the binder is vacuous and the body mentions nothing of it. ok=false
// where the conclusion is not ∀-headed.
func StripQuant1Fixes(goal Prop, refused func(VarTerm) bool) (VarTerm, bool) {
	abs, ok := stripQuant1Opened(goal, refused)
	if !ok {
		return VarTerm{}, false
	}
	return abs.Var(), true
}

// ConclExistsWitnessTactic instantiates the top-level ∃ in the goal's
// conclusion at the supplied witness term:
//
//	Goal:    Γ ⊢ ∃x. P(x)
//	Subgoal: Γ ⊢ P(t)
//
// A top-level ∃! is first read as the ∃ of its witness form
// (prop.UniqueWitnessRewrite), so the witness leaves P at it and that P
// holds of nothing else:
//
//	Goal:    Γ ⊢ ∃!x. P(x)
//	Subgoal: Γ ⊢ P(t) ∧ (∀y. P(y) ⇒ y = t)
//
// Returns nil when the conclusion is not a top-level ∃ or ∃!, when the
// witness's type doesn't match the bound variable's, or when the
// reconstruction would produce a goal alpha-equal to the original
// (e.g. the witness collapses to no progress).
func ConclExistsWitnessTactic(witness Term) Tactic {
	return func(goal Prop) *SubGoals {
		if unique := ext.MatchesUNIQUE(goal.Conclusion()); !unique.IsZero() {
			if !unique.Var().Type().Equals(witness.Type()) {
				return nil
			}
			// The ∃ the rewrite exposes takes the witness; where it does
			// not, the step refuses and leaves the ∃! as it stood.
			rewritten := rewriteTactic(prop.UniqueWitnessRewrite)(goal)
			inner := ConclExistsWitnessTactic(witness)
			if inner(rewritten.ChildGoal(0)) == nil {
				return nil
			}
			return inner.expand(rewritten)
		}
		abs := ext.MatchesEXISTS(goal.Conclusion())
		if abs.IsZero() {
			return nil
		}
		if !abs.Var().Type().Equals(witness.Type()) {
			return nil
		}
		// intro: P(t) ⊢ ∃x.P(x). The kernel computes P(t) by beta-
		// reducing (λx.P(x))(t), which handles capture-avoiding
		// substitution correctly.
		intro := prop.InstExists(goal.Conclusion(), witness)
		// The single hyp of intro is exactly P(t) — deep-β-reduced, it
		// becomes the subgoal's conclusion: a λ witness applied inside
		// P mints redexes InstExists's own β-step does not reach, and
		// the install boundary hands over β-normal goals.
		Assert(intro.NumHyps() == 1)
		instTerm := intro.Hyp(0)
		betaEq := prop.DeepBeta(instTerm) // ⊢ P(t) = β(P(t)); nil when normal
		if betaEq != nil {
			instTerm = Rhs(betaEq)
		}
		subgoal := MakeProp(instTerm, goal.Hyps()...)
		if subgoal.AlphaEquals(goal) {
			return nil
		}
		reconstruct := func(thms ...Prop) Prop {
			// F-conclusion shortcut: a proof of `Γ' ⊢ ⊥` (with Γ'
			// ⊆ Γ — the test harness exercises this via random hyp
			// removal + ⊥-replacement) is already stronger than
			// the original ∃-goal; chaining through `intro` would
			// require `intro.HasHyp(⊥)`, which it doesn't.
			if thms[0].Conclusion().Equals(F) {
				return thms[0]
			}
			// thms[0]: Γ ⊢ β(P(t)) — lifted back through the reversed
			// β-equation when one applied, then chained:
			//   Γ ⊢ P(t)
			//   P(t) ⊢ ∃x.P(x)
			//   --------------
			//   Γ ⊢ ∃x.P(x)   ✓
			out := thms[0]
			if betaEq != nil {
				out = betaEq.EqSym().EqMP(out)
			}
			return WrapProp(out).DeriveTrans(intro)
		}
		return MakeSubGoals(goal, reconstruct, subgoal)
	}
}

// HypForallInstantiateTactic instantiates the first ∀-headed hypothesis
// at the supplied witness term, ADDING P(t) to the hypotheses while
// keeping the original ∀ available:
//
//	Goal:    Γ, ∀x. P(x) ⊢ C
//	Subgoal: Γ, ∀x. P(x), P(t) ⊢ C
//
// "First matching ∀-hyp" picks by hyp order, restricted to ∀-hyps
// whose bound-variable type matches the witness. When the goal has
// multiple ∀-hyps with the same binder type, only the first one is
// reachable here — SpecializeTactic targets a specific hyp by index.
//
// Returns nil when no hyp is a ∀ whose bound type matches, or when
// the resulting subgoal would alpha-equal the original (P(t) already
// in scope).
func HypForallInstantiateTactic(witness Term) Tactic {
	return func(goal Prop) *SubGoals {
		for i := range goal.NumHyps() {
			if sg := instantiateAt(goal, i, witness); sg != nil {
				return sg
			}
		}
		return nil
	}
}

// SpecializeSpec is one entry of SpecializeTactic's batch: ground the
// ∀-hyp at HypIndex by peeling one leading binder per witness, in
// binder order. HypIndex refers to the tactic's INPUT goal — every
// entry in a batch indexes the same hyp-list snapshot.
type SpecializeSpec struct {
	HypIndex  int
	Witnesses []Term
}

// SpecializeTactic is the index-targeted, batch composite form of
// HypForallInstantiateTactic: for each spec it peels the leading
// ∀-binders of hyps[spec.HypIndex] at spec.Witnesses and adds ONLY the
// final ground instance as a new hyp — the intermediate partial
// instantiations never appear on any goal, so a k-binder grounding is
// ONE goal transition instead of k (no index drift, no sweep-clear of
// partials afterwards). Unless keepSources is set, each grounded
// source ∀-hyp is dropped in the same step (weakening — the Lean
// `specialize h a b c` semantics; ematch-style callers that ground one
// wide ∀-hyp at several witness tuples pass keepSources=true).
//
// All HypIndex values refer to the same input goal (the
// ClearHypsTactic atomic-set convention); duplicate indices are
// allowed — with keepSources=false the source is dropped once.
//
// Returns nil (did not apply) when: the batch is empty, any spec has
// no witnesses, any index is out of range, any hyp has fewer ∀-binders
// reachable through leading implications than its witness list, any
// binder type mismatches its witness, or the resulting subgoal would
// α-equal the original.
//
// "Reachable through leading implications": a guarded lemma states its
// content behind an antecedent — `∀op. monoidal_op(op) ⇒ ∀f p s. …` — and
// grounding it at every stated binder yields the guarded instance
// `monoidal_op(w₀) ⇒ (… ⇒ …)[w₁ w₂ w₃]`, exactly what the By executor's
// witnessed install produces after its prenex lift. The rung for a
// binder under a guard is derived, never rewritten: assume the source,
// demote the guard to a hypothesis, instantiate below it, promote the
// guard back (instGuardedForAll).
func SpecializeTactic(specs []SpecializeSpec, keepSources bool) Tactic {
	return SpecializeTacticReading(specs, keepSources, nil)
}

// SpecializeTacticReading is SpecializeTactic with the record equations
// of the instances' normal form (InstanceNormal) read through read.
func SpecializeTacticReading(specs []SpecializeSpec, keepSources bool, read LibraryRead) Tactic {
	return func(goal Prop) *SubGoals {
		if len(specs) == 0 {
			return nil
		}
		// bridges[i]: hyps[specs[i].HypIndex] ⊢ P(w₁…w_k) — the composed
		// instantiation derivation, built by chaining prop.InstForAll
		// through DeriveTrans (the same kernel path instantiateAt uses,
		// k rungs fused into one ministep).
		bridges := make([]Prop, 0, len(specs))
		instances := make([]Term, 0, len(specs))
		drop := make(map[int]bool, len(specs))
		for _, sp := range specs {
			if sp.HypIndex < 0 || sp.HypIndex >= goal.NumHyps() || len(sp.Witnesses) == 0 {
				return nil
			}
			cur := goal.Hyp(sp.HypIndex)
			var bridge Prop
			for _, w := range sp.Witnesses {
				// rung: cur ⊢ cur[w] — the next ∀-binder reachable
				// through leading implications, instantiated (kernel
				// β-substitution; the guard case derives through
				// demote/promote).
				rung, ok := instGuardedForAll(cur, w)
				if !ok {
					return nil
				}
				if bridge == nil {
					bridge = rung
				} else {
					bridge = WrapProp(bridge).DeriveTrans(rung)
				}
				cur = rung.Conclusion()
			}
			// The install boundary hands over instances in the normal
			// form (InstanceNormal): a λ witness landing in applied
			// position mints a redex the binder substitution does not
			// reduce ((λi.F(i))(k) would survive into the resident hyp
			// and every clause set built from it), and a packed record
			// witness a projection the law applies to it. Extend the
			// bridge with the kernel's reduction; no-op when the
			// instance is already normal.
			bridge = WrapProp(bridge).RewriteConcl(InstanceNormal(read))
			cur = bridge.Conclusion()
			bridges = append(bridges, bridge)
			instances = append(instances, cur)
			if !keepSources {
				drop[sp.HypIndex] = true
			}
		}
		newHyps := make([]Term, 0, goal.NumHyps()+len(instances))
		for j := range goal.NumHyps() {
			if !drop[j] {
				newHyps = append(newHyps, goal.Hyp(j))
			}
		}
		newHyps = append(newHyps, instances...)
		subgoal := MakeProp(goal.Conclusion(), newHyps...)
		if subgoal.AlphaEquals(goal) {
			return nil
		}
		// A consumed source descends into its instance (Lean's
		// `specialize h w`); a source two specs ground at once has no
		// single successor, and a kept source stands as it stood.
		images := goal.Hyps()
		groundings := make([]int, goal.NumHyps())
		for _, sp := range specs {
			groundings[sp.HypIndex]++
		}
		for k, sp := range specs {
			if !drop[sp.HypIndex] {
				continue
			}
			images[sp.HypIndex] = nil
			if groundings[sp.HypIndex] == 1 {
				images[sp.HypIndex] = instances[k]
			}
		}
		reconstruct := func(thms ...Prop) Prop {
			// thms[0]: (Γ \ sources), instances ⊢ C (possibly minus
			// hyps the proof never used — the test harness exercises
			// that). Discharge each used instance back through its
			// bridge; each DeriveTrans swaps the instance hyp for the
			// source ∀-hyp (∈ Γ), so the result's hyps stay ⊆ Γ.
			out := thms[0]
			for i, inst := range instances {
				if !out.HasHyp(inst) {
					continue
				}
				// bridges[i]: source ⊢ inst.
				// out:        Γ', inst ⊢ C.
				// DeriveTrans: Γ', source ⊢ C.
				out = WrapProp(bridges[i]).DeriveTrans(out)
			}
			return out
		}
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(subgoal, images)}, subgoal)
	}
}

// instGuardedForAll instantiates, at w, the first ∀-binder reachable
// from cur through leading implications, returning the kernel bridge
// cur ⊢ cur' (cur' = cur with that binder substituted). On a bare
// ∀-chain this is prop.InstForAll; through a guard `A ⇒ R` it is
//
//	cur ⊢ cur           (assume)
//	cur, A ⊢ R          (demote the antecedent)
//	cur, A ⊢ R[w]       (transitivity with the inner rung R ⊢ R[w])
//	cur ⊢ A ⇒ R[w]      (promote the antecedent back)
//
// so the guard travels with the instance and nothing is consumed or
// reoriented. ok is false when no ∀-binder is reachable or the binder's
// type is not w's.
func instGuardedForAll(cur, w Term) (Prop, bool) {
	if abs := ext.MatchesFORALL(cur); !abs.IsZero() {
		if !abs.Var().Type().Equals(w.Type()) {
			return nil, false
		}
		return prop.InstForAll(cur, w), true
	}
	ante, rest, ok := ext.MatchesIMPLY(cur)
	if !ok {
		return nil, false
	}
	inner, ok := instGuardedForAll(rest, w)
	if !ok {
		return nil, false
	}
	return prop.Assume(cur).DemoteHyp().DeriveTrans(inner).PromoteHyp(ante), true
}

// instantiateAt is the shared kernel: try to instantiate hyps[i] at
// witness, returning the SubGoals on success or nil if the hyp isn't
// ∀-headed, the binder type mismatches, or the result is α-equal to
// the original. HypForallInstantiateTactic loops calling this.
func instantiateAt(goal Prop, i int, witness Term) *SubGoals {
	h := goal.Hyp(i)
	abs := ext.MatchesFORALL(h)
	if abs.IsZero() {
		return nil
	}
	if !abs.Var().Type().Equals(witness.Type()) {
		return nil
	}
	// app: ∀x.P(x) ⊢ P(t), conclusion deep-β-reduced — the install
	// boundary hands over β-normal instances (the SpecializeTactic
	// contract).
	app := WrapProp(prop.InstForAll(h, witness)).RewriteConcl(prop.DeepBeta)
	// Subgoal: original hyps + P(t). The ∀ is preserved (it's
	// already in goal.Hyps()); we just append the instantiated
	// fact alongside.
	newHyps := append(goal.Hyps(), app.Conclusion())
	subgoal := MakeProp(goal.Conclusion(), newHyps...)
	if subgoal.AlphaEquals(goal) {
		// P(t) already in hyps (or normalized away) — no progress.
		return nil
	}
	reconstruct := func(thms ...Prop) Prop {
		// If thms[0] doesn't have P(t) as a hyp — either
		// because the test harness randomly removed it, or
		// because the proof closed without using the new
		// fact — it's already at least as strong as the
		// original goal (its hyps are a subset of goal's,
		// since goal.Hyps ⊆ subgoal.Hyps = goal.Hyps ∪ {P(t)}).
		// Pass it through unchanged.
		if !thms[0].HasHyp(app.Conclusion()) {
			return thms[0]
		}
		// thms[0]: Γ, ∀x.P(x), P(t) ⊢ C.
		// app:     ∀x.P(x) ⊢ P(t).
		// DeriveTrans:
		//   ∀x.P(x) ⊢ P(t)   (l = P(t))
		//   Γ, ∀x.P(x), P(t) ⊢ C
		//   --------------------
		//   Γ, ∀x.P(x) ⊢ C    ✓
		return WrapProp(app).DeriveTrans(thms[0])
	}
	return MakeSubGoals(goal, reconstruct, subgoal)
}
