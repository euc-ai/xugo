// alpha_merge.go — the ALPHA-MERGE init-time deduce chain.
//
// insideDenoteRewrite (cnf_rewrite.go) mints a fresh α Skolem-abstraction
// symbol per ∃-under-λ occurrence, per hypothesis. When the same body is
// denoted in two sibling hyps (the `H, ¬H ⊢ ⊥` class), the goal-level merge
// renames the second hyp's Skolems apart (SubscriptExistsVars, cnf.go), so
// the clause set carries two logically identical but syntactically distinct
// symbol families:
//
//	wit_i:   ∀g.   ¬αᵢ(g) ∨ L(g, ƒᵢ(g))    (αᵢ ⇒ Skolemized body)
//	intro_i: ∀g,y⃗. ¬L(g, y⃗) ∨ αᵢ(g)        (body ⇒ αᵢ)
//
// α₀/α₁ are opaque to the refuter — first-order unification cannot equate
// them, and the occurrences sit under a λ in argument position of an opaque
// head (set_comprehension(λg.αᵢ(g), x)), unreachable by Resolve. The refutation of the
// complementary pair is impossible in that clause space (see
// TestNegateGoalCNF_ExistsUnderLambdaAlphaDuplication in cnf_test.go).
//
// Following the FUNEXT lesson ("enrich derivations, never the clause-set
// identity"), the merge derives the missing equality at refuter init from
// the clauses already present — the CNF, RefuteProp and cnf_proofs cache
// keys are untouched. The derivation is decomposed into a chain of ≤2-hyp
// steps so each fits the binary proof DAG (makeDeduceStep asserts
// NumHyps() <= 2) and reuses an EXISTING recipe rule — no new proto tag, no
// new replay builder:
//
//	a: resolveClause(wit_i, intro_j)  → ∀g. ¬αᵢ(g) ∨ αⱼ(g)   [_RuleResolve]
//	b: resolveClause(wit_j, intro_i)  → ∀g. ¬αⱼ(g) ∨ αᵢ(g)   [_RuleResolve]
//	   (one step each for a one-conjunct body; a chain of them for a
//	   multi-conjunct body — THE COMPOUND-WITNESS SHAPE below)
//	c: FunextFromIffPair(a, b)        → ⊢ αᵢ = αⱼ             [_RuleFunext]
//	d: c.Simplifies(target)           → rewritten twins       [_RuleSimplifies]
//
// The ordinary saturation can find a/b on its own but has no way to
// recombine them (FUNEXT enrichment only runs over initial clauses) and no
// way to use the equality (the α is under a λ; only EqRewrite-based
// Simplifies penetrates it, and its size gate rejects the same-size α→α
// substitution — hence the isVarEqVarClause exception in deduce.go). The
// twins (step d) restore first-order reachability: a rewritten
// ¬set_comprehension(λg.αⱼ(g), x) is the exact complement of the sibling hyp's unit
// clause, so findContradicts closes the goal during init, search-free.
//
// The chain iterates to a fixpoint over the derived twins: with nested
// denotes (α₂'s defining clauses referencing α₁), merging the inner pair
// rewrites the outer defining clauses, which can align the outer pair on
// the next round. A nested denote is parameterized over the enclosing
// Skolem function (αᵢ(ƒ, g)), and the wit / intro sides of ONE symbol use
// β-distinct instantiations of it (α(ƒ₀, g) vs α(λg.g, y)) — first-order
// matching cannot bridge those, so the outer pair of an
// image-of-an-image nesting declines on its own. alpha_bridge.go
// derives the bridging equality from the inner symbol's own wit and
// intro and canonicalizes the outer wits with it, after which the outer
// pair merges here on the next round.
//
// THE ONE-POINT SHAPE (the third α-duplication face): a one-point
// λ-body `∃x. B(x) ∧ g = x` (the comprehension_spec normal form)
// Skolemizes its wit side THROUGH the ∃-witness ƒ,
//
//	wit1: ∀g. ¬α(g) ∨ B(ƒ(g))
//	wit2: ∀g. ¬α(g) ∨ (gₖ = ƒ(g))     ← one-point conditional equality
//
// while the intro side is already one-point-contracted by the CNF
// normalizer (∀x. α(x) ∨ ¬B(x)). The wit body's ƒ(g) argument blocks
// alphaDirClause / FunextFromIffPair, so neither the α-pair merge nor the
// FUNEXT recombine fires — and since deriveInitFunext never revisits
// DERIVED clauses and Simplifies accepts only unit equalities, the
// saturation can never produce a unit fn-equality either: argument-position
// occurrences (K(λg.α(g)) vs K(λx.B(x))) stay unreachable at any budget.
// Two extra chain moves close the shape with existing recipe rules:
//
//	e: resolveClause(wit2, wit1)      → ∀g. ¬α(g) ∨ B(g)  [_RuleResolve]
//	   (eliminateOnePointWits — paramodulates the conditional equality,
//	   oriented ƒ(g) → gₖ, into every sibling wit)
//	f: FunextFromIffPair(e, intro)    → ⊢ α = B_fn          [_RuleFunext]
//	   (mergeSymbolDefinition — the SINGLE-symbol recombine: the symbol's
//	   own defining fn-equality, which also bridges α to a plain non-denote
//	   λ on the other side, the K(f) ⊢ K(g) / stated-equality-hyp cases)
//
// followed by the usual Simplifies twins. Tests: the OnePoint tests in
// alpha_merge_test.go (chain level) and prover/solver/refuter/alpha_merge_test.go
// (end-to-end).
//
// THE COMPOUND-WITNESS SHAPE (the fourth face): a body whose ∃ has several
// conjuncts and a compound witness, `∃x⃗. B₁(x⃗) ∧ … ∧ Bₙ(x⃗) ∧ g = t(x⃗)` —
// every product-set and sum-set comprehension, `{x · y | x, y | x ∈ M ∧
// y ∈ N}` — Skolemizes its wit side into ONE clause per conjunct,
//
//	wit_i:  ∀g. ¬α(g) ∨ Bᵢ(ƒ⃗(g))        wit_=: ∀g. ¬α(g) ∨ g = t(ƒ⃗(g))
//
// while the one-point-contracted intro has n negative literals and the
// symbol applied to the compound witness:
//
//	intro:  ∀x⃗. ¬B₁(x⃗) ∨ … ∨ ¬Bₙ(x⃗) ∨ α(t(x⃗))
//
// No single resolution yields the pointwise bridge, and the intro's symbol
// argument is not a binder, so the intro is read as a candidate of its own
// shape (introCandOf) and each direction of the bridge is derived as a
// chain (alphaDirSteps): the intro is instantiated at the one substitution
// σ that carries it onto the wits — a compound argument matched against
// the witness side of wit_=, a binder argument bound positionally, each
// conjunct matched against a wit body — then wit_= paramodulates into it
// (t(ƒ⃗(g)) → g, which also turns a conjunct that mentioned g back into
// its wit form) and each conjunct resolves against its wit, every step a
// native _RuleResolve at a recorded unifier:
//
//	a₁: resolveClause(wit_=, intro@σ) → ∀g. ¬α₀(g) ∨ ¬B₁(ƒ⃗(g)) ∨ … ∨ α₁(g)
//	a₂: resolveClause(wit_1, a₁)      → ∀g. ¬α₀(g) ∨ ¬B₂(ƒ⃗(g)) ∨ … ∨ α₁(g)
//	…
//	aₙ₊₁: resolveClause(wit_n, aₙ)    → ∀g. ¬α₀(g) ∨ α₁(g)
//
// and steps c / d follow as for the flat shape. A conjunct that contains
// the witness term itself (`N(f(x))` beside `g = f(x)`) reads N(f(ƒ(g)))
// on the wit side; move e (eliminateOnePointWits, which never required a
// bare Skolem on the witness side) rewrites it to N(g) in the round
// before, and the chain aligns against that twin. A multi-conjunct body
// with a bare witness (`∃y. P(g) ∧ R(g, y)`) is the same chain without the
// equality step. Tests: TestDeriveAlphaMergeChain_CompoundWitness and
// TestDeriveAlphaMergeChain_MultiConjunct (chain level),
// TestAlphaMergeCompoundWitnessRefutesGoal (end-to-end).

package clause

import (
	"maps"
	"slices"

	"github.com/euc-ai/xugo/core"
)

// Fixpoint round cap. Each productive round merges at least one symbol pair,
// and the number of denote symbols per goal is small (1–4 observed); the cap
// is a backstop, not a tuning knob.
const _ALPHA_MERGE_MAX_ROUNDS = 8

// _witCand is a witness-side defining clause of a symbol:
// ∀g. ¬sym(g) ∨ body, with g exactly the clause's bound vars.
type _witCand struct {
	c        *Clause
	body     Term      // L — does not contain sym
	litIndex int       // index of body in c.literals (resolveClause's ind)
	args     []VarTerm // sym's args in application order (all bound vars)
}

// _introCand is an intro-side defining clause of a symbol:
// ∀x⃗. ¬B₁ ∨ … ∨ ¬Bₙ ∨ sym(a⃗) — one positive literal, headed by sym, every
// other literal negative and sym-free. Each arg is a term over the
// clause's binders: a binder itself (aligned positionally by
// alphaDirSteps) or a compound over binders (the witness term of a
// compound-witness body, aligned through the symbol's equality wit).
type _introCand struct {
	c      *Clause
	bodies []Term // B₁…Bₙ — the stripped negative literals, in clause order
	args   []Term // sym's args in application order
}

// varArgs returns the args as distinct clause-bound vars — the shape the
// nested alpha-bridge pins and instantiates positionally — or nil when an
// arg is compound or repeated.
func (in *_introCand) varArgs() []VarTerm {
	return boundVarArgs(in.args, &in.c.univBoundVars)
}

// _alphaGroup collects all wit / intro candidates of one applied ground
// fun-typed var. A symbol is mergeable when both sides are non-empty.
type _alphaGroup struct {
	sym    VarTerm
	wits   []_witCand
	intros []_introCand
}

// stripAppliedVar decomposes t = A(a₁)…(aₙ) returning A when it is a Var,
// with the args in application order. (nil, nil) otherwise.
func stripAppliedVar(t Term) (VarTerm, []Term) {
	var args []Term
	for {
		app, ok := t.AsAppliedTerm()
		if !ok {
			break
		}
		args = append(args, app.Arg())
		t = app.Fun()
	}
	v, ok := t.AsVar()
	if !ok {
		return VarTerm{}, nil
	}
	// args were collected innermost-first; reverse to application order.
	for i, j := 0, len(args)-1; i < j; i, j = i+1, j-1 {
		args[i], args[j] = args[j], args[i]
	}
	return v, args
}

// boundVarArgs checks that every arg is a distinct clause-bound var and
// returns them. nil when the shape doesn't hold.
func boundVarArgs(args []Term, bound *VarList) []VarTerm {
	seen := map[core.TermKey]bool{}
	vars := make([]VarTerm, 0, len(args))
	for _, a := range args {
		v, ok := a.AsVar()
		if !ok || !bound.Has(v) || seen[v.AlphaKey()] {
			return nil
		}
		seen[v.AlphaKey()] = true
		vars = append(vars, v)
	}
	return vars
}

// witCandOf extracts the wit shape from c, whatever its symbol: exactly
// two literals, one ¬sym(g⃗) with g⃗ the clause's bound vars, each once,
// the other a positive sym-free body (step a resolves the body against
// the intro side's negated conjunct, so it must be positive). nil when c
// is not of that shape.
func witCandOf(c *Clause) (*_witCand, VarTerm) {
	if len(c.literals) != 2 || c.univBoundVars.Empty() {
		return nil, VarTerm{}
	}
	for k, lit := range c.literals {
		n := MatchesNOT(lit)
		if n == nil {
			continue
		}
		sym, args := stripAppliedVar(n)
		if sym.IsZero() || len(args) != c.univBoundVars.Size() {
			continue
		}
		vars := boundVarArgs(args, &c.univBoundVars)
		other := c.literals[1-k]
		if vars == nil || other.HasFree(sym) || MatchesNOT(other) != nil {
			continue
		}
		return &_witCand{c: c, body: other, litIndex: 1 - k, args: vars}, sym
	}
	return nil, VarTerm{}
}

// witCandFor is witCandOf for a given symbol.
func witCandFor(c *Clause, sym VarTerm) *_witCand {
	w, s := witCandOf(c)
	if w == nil || !s.Equals(sym) {
		return nil
	}
	return w
}

// introCandOf extracts the intro shape from c, whatever its symbol: two
// or more literals, exactly one of them positive — a ground var applied to
// one or more args, each mentioning a clause binder — and every other
// literal negative and free of that var. nil when c is not of that shape.
func introCandOf(c *Clause) (*_introCand, VarTerm) {
	if len(c.literals) < 2 || c.univBoundVars.Empty() {
		return nil, VarTerm{}
	}
	var sym VarTerm
	var args []Term
	bodies := make([]Term, 0, len(c.literals)-1)
	for _, lit := range c.literals {
		if n := MatchesNOT(lit); n != nil {
			bodies = append(bodies, n)
			continue
		}
		if !sym.IsZero() {
			return nil, VarTerm{} // a second positive literal
		}
		sym, args = stripAppliedVar(lit)
		if sym.IsZero() || len(args) == 0 || c.univBoundVars.Has(sym) {
			return nil, VarTerm{}
		}
	}
	if sym.IsZero() {
		return nil, VarTerm{}
	}
	for _, b := range bodies {
		if b.HasFree(sym) {
			return nil, VarTerm{}
		}
	}
	notBound := func(v VarTerm) bool { return !c.univBoundVars.Has(v) }
	for _, a := range args {
		if a.AllFree(notBound) {
			return nil, VarTerm{} // a closed arg has no binder to align
		}
	}
	return &_introCand{c: c, bodies: bodies, args: args}, sym
}

// introCandFor is introCandOf for a given symbol.
func introCandFor(c *Clause, sym VarTerm) *_introCand {
	in, s := introCandOf(c)
	if in == nil || !s.Equals(sym) {
		return nil
	}
	return in
}

// detectAlphaGroups scans the clauses for wit / intro shapes and groups
// the candidates per symbol, in scan order (deterministic given the input
// order).
func detectAlphaGroups(clauses []*Clause) []*_alphaGroup {
	var groups []*_alphaGroup
	find := func(sym VarTerm) *_alphaGroup {
		for _, g := range groups {
			if g.sym.Equals(sym) {
				return g
			}
		}
		g := &_alphaGroup{sym: sym}
		groups = append(groups, g)
		return g
	}
	for _, c := range clauses {
		if w, sym := witCandOf(c); w != nil {
			find(sym).wits = append(find(sym).wits, *w)
		}
		if in, sym := introCandOf(c); in != nil {
			find(sym).intros = append(find(sym).intros, *in)
		}
	}
	return groups
}

// matchFlex first-order-matches pattern against target, binding vars for
// which isFlex holds. No binders crossed (v1: a flexible var under a λ, or a
// λ-pattern, falls through to Equals). Bindings accumulate in subst, keyed
// by AlphaKey (var pointers are not interned); vars records the VarTerm per
// key so the caller can rebuild TermSubsts.
func matchFlex(pattern, target Term, subst map[core.TermKey]Term,
	vars map[core.TermKey]VarTerm, isFlex func(VarTerm) bool) bool {
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
	if pok && tok {
		return matchFlex(pApp.Fun(), tApp.Fun(), subst, vars, isFlex) &&
			matchFlex(pApp.Arg(), tApp.Arg(), subst, vars, isFlex)
	}
	return pattern.Equals(target)
}

func applyVars(sym VarTerm, vars []VarTerm) Term {
	t := Term(sym)
	for _, v := range vars {
		t = Apply(t, v)
	}
	return t
}

// alphaPairKey is the canonical (order-independent) key of a symbol pair.
func alphaPairKey(a, b VarTerm) [2]core.TermKey {
	if a.Compare(b) > 0 {
		a, b = b, a
	}
	return [2]core.TermKey{a.AlphaKey(), b.AlphaKey()}
}

// renameApart renames the binders of c that occur by name in any of the
// others, as AvoidVarsCollision does for one clause; c itself when none
// does.
func renameApart(c *Clause, others ...*Clause) *Clause {
	collides := func(n TermName) bool {
		for _, o := range others {
			if o.Term().HasName(n) {
				return true
			}
		}
		return false
	}
	renamed := c
	for v := range c.univBoundVars.Iter() {
		if !collides(v.Name()) {
			continue
		}
		if renamed == c {
			renamed = c.clone()
		}
		vp := v
		for renamed.Term().HasName(vp.Name()) || collides(vp.Name()) {
			vp = vp.Rename()
		}
		renamed = renamed.rename(v, vp)
	}
	return renamed
}

// replaceSubterm replaces every occurrence of from in t by to, descending
// through applications and through abstractions whose binder is free in
// neither (an occurrence under a binder that captures a free var of from
// is a different term).
func replaceSubterm(t, from, to Term) Term {
	if t.Equals(from) {
		return to
	}
	if app, ok := t.AsAppliedTerm(); ok {
		f := replaceSubterm(app.Fun(), from, to)
		a := replaceSubterm(app.Arg(), from, to)
		if f == app.Fun() && a == app.Arg() {
			return t
		}
		return Apply(f, a)
	}
	if abs, ok := t.AsAbsTerm(); ok {
		if from.HasFree(abs.Var()) || to.HasFree(abs.Var()) {
			return t
		}
		b := replaceSubterm(abs.Body(), from, to)
		if b == abs.Body() {
			return t
		}
		return Abs(abs.Var(), b)
	}
	return t
}

// isBridgeClause reports whether c is exactly the pointwise bridge
// ∀g⃗. ¬symI(g⃗) ∨ symJ(g⃗): a wit of symI whose body is symJ at the same
// args.
func isBridgeClause(c *Clause, symI, symJ VarTerm) bool {
	w := witCandFor(c, symI)
	return w != nil && w.body.AlphaEquals(applyVars(symJ, w.args))
}

// alphaDirSteps derives one direction of the pointwise bridge,
// ∀g⃗. ¬symI(g⃗) ∨ symJ(g⃗), from the wits of symI's group and one intro
// ∀x⃗. ¬B₁ ∨ … ∨ ¬Bₙ ∨ symJ(a⃗) of symJ, as a chain of native _RuleResolve
// steps at hand-computed unifiers; the last step's conclusion is the
// bridge. The wits are read over one binder vector g⃗ (the first wit's)
// and the intro is instantiated at the one substitution σ that carries it
// onto them:
//
//   - a compound arg aₖ matches the witness side r of an equality wit
//     ∀g⃗. ¬symI(g⃗) ∨ gₖ = r, binding the intro binders in aₖ; the step
//     paramodulates that wit into the intro, rewriting r → gₖ;
//   - a binder arg aₖ = xⱼ is bound to gₖ;
//   - each conjunct Bᵢ, read with every compound aₖ replaced by gₖ (what
//     the equality steps leave of it), matches a wit body; the step
//     resolves that wit against the conjunct.
//
// Every binder of the intro must be bound by σ; the intro is renamed
// apart from the wits first, since resolveClause applies one substitution
// to both of its inputs. The equality steps run first, then one resolution
// per conjunct, and the result is accepted only when it is exactly the
// two-literal bridge. nil when the intro does not align with the wits or a
// step declines.
func alphaDirSteps(gi *_alphaGroup, symJ VarTerm, intro _introCand) []*ClauseThm {
	symI := gi.sym
	if len(gi.wits) == 0 {
		return nil
	}
	gvars := gi.wits[0].args
	if len(intro.args) != len(gvars) {
		return nil
	}
	witClauses := make([]*Clause, 0, len(gi.wits))
	for _, w := range gi.wits {
		witClauses = append(witClauses, w.c)
	}
	in := introCandFor(renameApart(intro.c, witClauses...), symJ)
	if in == nil {
		return nil
	}
	isFlex := in.c.univBoundVars.Has

	// Every wit body read over g⃗ (a wit with other binder names is
	// substituted onto them for the matching; its step renames it apart
	// and aligns it in the recorded unifier).
	type _witOverG struct {
		w    _witCand
		body Term
	}
	wits := make([]_witOverG, 0, len(gi.wits))
	for _, w := range gi.wits {
		al, ok := alignArgs(w.args, gvars)
		if !ok {
			return nil
		}
		body := w.body
		if len(al) > 0 {
			body = body.Substitute(al...)
		}
		wits = append(wits, _witOverG{w, body})
	}

	subst := map[core.TermKey]Term{}
	substVars := map[core.TermKey]VarTerm{}
	tryMatch := func(pattern, target Term) bool {
		trial, trialVars := maps.Clone(subst), maps.Clone(substVars)
		if !matchFlex(pattern, target, trial, trialVars, isFlex) {
			return false
		}
		subst, substVars = trial, trialVars
		return true
	}

	// Compound arg positions: the equality wit and its orientation.
	type _eqStep struct {
		w  _witCand
		rt _EqRewriteType
	}
	var eqSteps []_eqStep
	compound := make([]bool, len(in.args))
	for k, a := range in.args {
		if v, ok := a.AsVar(); ok && isFlex(v) {
			continue
		}
		compound[k] = true
		matched := false
		for _, wg := range wits {
			l, r, ok := MatchesEQ(wg.body)
			if !ok {
				continue
			}
			var side Term
			var rt _EqRewriteType
			switch {
			case l.Equals(gvars[k]) && !r.Equals(gvars[k]):
				side, rt = r, rewriteEqRight // rewrite r → l = gₖ
			case r.Equals(gvars[k]) && !l.Equals(gvars[k]):
				side, rt = l, rewriteEqLeft // rewrite l → r = gₖ
			default:
				continue
			}
			if tryMatch(a, side) {
				eqSteps = append(eqSteps, _eqStep{wg.w, rt})
				matched = true
				break
			}
		}
		if !matched {
			return nil
		}
	}
	// Binder arg positions bind positionally.
	for k, a := range in.args {
		if !compound[k] && !tryMatch(a, gvars[k]) {
			return nil
		}
	}
	// Conjuncts, read as the equality steps leave them.
	var bodySteps []_witCand
	for _, b := range in.bodies {
		pattern := b
		for k, a := range in.args {
			if compound[k] {
				pattern = replaceSubterm(pattern, a, gvars[k])
			}
		}
		matched := false
		for _, wg := range wits {
			if tryMatch(pattern, wg.body) {
				bodySteps = append(bodySteps, wg.w)
				matched = true
				break
			}
		}
		if !matched {
			return nil
		}
	}
	for v := range in.c.univBoundVars.Iter() {
		if _, bound := subst[v.AlphaKey()]; !bound {
			return nil
		}
	}

	// One step: the wit's literal rewrites cur at the substitution,
	// accepting a single resolvent. A wit over other binder names is
	// renamed apart from cur and aligned onto g⃗ in the recorded unifier.
	step := func(w _witCand, cur *Clause, substs TermSubstsGroup,
		rt _EqRewriteType) *ClauseThm {
		if !slices.EqualFunc(w.args, gvars, (VarTerm).EqualsVar) {
			wr := witCandFor(w.c.AvoidVarsCollision(cur), symI)
			if wr == nil {
				return nil
			}
			al, ok := alignArgs(wr.args, gvars)
			if !ok {
				return nil
			}
			w = *wr
			substs = append(slices.Clone(substs), al...)
			slices.SortFunc(substs, func(a, b TermSubst) int {
				return a.VarTerm.Compare(b.VarTerm)
			})
		}
		thms := resolveClause(w.c, cur, substs, w.litIndex, rt)
		if len(thms) != 1 {
			return nil
		}
		return thms[0].withRecipe(&deduceRecipe{
			rule:        _RuleResolve,
			inputs:      []*Clause{w.c, cur},
			litIndex:    w.litIndex,
			rewriteType: rt,
			substs:      substs,
		})
	}
	cur := in.c
	substs := substsFromBindings(subst, substVars)
	var steps []*ClauseThm
	for _, es := range eqSteps {
		s := step(es.w, cur, substs, es.rt)
		if s == nil {
			return nil
		}
		steps, cur, substs = append(steps, s), s.ConclClause(), nil
	}
	for _, w := range bodySteps {
		s := step(w, cur, substs, rewriteWhole)
		if s == nil {
			return nil
		}
		steps, cur, substs = append(steps, s), s.ConclClause(), nil
	}
	if len(steps) == 0 || !isBridgeClause(cur, symI, symJ) {
		return nil
	}
	return steps
}

// alphaMergePair derives the [a…, b…, c] prefix of the chain for one
// symbol pair — the steps of each direction, tried per intro candidate of
// the other symbol, then the recombine — ending in the symbol equality.
// nil when either direction declines on every intro.
func alphaMergePair(gi, gj *_alphaGroup) []*ClauseThm {
	dir := func(gi, gj *_alphaGroup) []*ClauseThm {
		for _, in := range gj.intros {
			if steps := alphaDirSteps(gi, gj.sym, in); steps != nil {
				return steps
			}
		}
		return nil
	}
	a := dir(gi, gj)
	if a == nil {
		return nil
	}
	b := dir(gj, gi)
	if b == nil {
		return nil
	}
	c := FunextFromIffPair(a[len(a)-1].ConclClause(), b[len(b)-1].ConclClause())
	if c == nil {
		return nil
	}
	return append(append(a, b...), c)
}

// eliminateOnePointWits derives, per symbol group, the ƒ-eliminated
// variants of its wit clauses (chain move e — see the ONE-POINT SHAPE
// section of this file's header): a wit whose body is a one-point
// conditional equality `gₖ = t` (gₖ one of the symbol's args, t the
// ∃-witness Skolem application — which typically CONTAINS gₖ) paramodulates
// into every sibling wit, rewriting t → gₖ. The resolvent ∀g. ¬sym(g) ∨ B(g) is accepted
// only when it is itself a wit shape for the symbol (so the next round's
// detectAlphaGroups picks it up and the recombines fire); everything else
// resolveClause produces is dropped. Recipes are native _RuleResolve —
// replay re-runs the deterministic builder.
func eliminateOnePointWits(g *_alphaGroup) []*ClauseThm {
	var out []*ClauseThm
	for _, w2 := range g.wits {
		l, r, ok := MatchesEQ(w2.body)
		if !ok {
			continue
		}
		// Orient the equality toward the bound var: flexibleEq uses the
		// clause literal as-is for rewriteEqLeft (rewrites l → r) and
		// flipped for rewriteEqRight (rewrites r → l). The Skolem side
		// typically CONTAINS the var (ƒ(g) over the same binders) — that
		// direction strictly shrinks, so termination is not at risk;
		// resolveClause's own subterm guard rejects the degenerate cases.
		var rt _EqRewriteType
		if lv, lok := l.AsVar(); lok && containsVar(w2.args, lv) && !r.AlphaEquals(lv) {
			rt = rewriteEqRight // rewrite r → l = gₖ
		} else if rv, rok := r.AsVar(); rok && containsVar(w2.args, rv) && !l.AlphaEquals(rv) {
			rt = rewriteEqLeft // rewrite l → r = gₖ
		} else {
			continue
		}
		for _, w1 := range g.wits {
			if w1.c == w2.c || len(w1.args) != len(w2.args) {
				continue
			}
			// Positional binder alignment via the symbol's application
			// order: w2.args[k] := w1.args[k]. Identity entries dropped
			// (the common case — the CNF reuses the binder vars).
			substs, ok := alignArgs(w2.args, w1.args)
			if !ok {
				continue
			}
			for _, thm := range resolveClause(w2.c, w1.c, substs, w2.litIndex, rt) {
				if !isWitShapeClause(thm.ConclClause(), g.sym) {
					continue
				}
				out = append(out, thm.withRecipe(&deduceRecipe{
					rule:        _RuleResolve,
					inputs:      []*Clause{w2.c, w1.c},
					litIndex:    w2.litIndex,
					rewriteType: rt,
					substs:      substs,
				}))
			}
		}
	}
	return out
}

// mergeSymbolDefinition recombines a symbol's own wit + intro clauses into
// its defining fn-equality ⊢ sym = B_fn (chain move f). Fires only when a
// wit body directly complements an intro body at aligned binders — i.e.
// after one-point elimination (or for bodies that never went through a
// Skolem). LambdaFreeEqSides keeps the same enrichment scope as
// deriveInitFunext.
func mergeSymbolDefinition(g *_alphaGroup) *ClauseThm {
	for _, w := range g.wits {
		for _, in := range g.intros {
			if thm := FunextFromIffPair(w.c, in.c); thm != nil &&
				LambdaFreeEqSides(thm.ConclClause()) {
				return thm
			}
		}
	}
	return nil
}

// hasVarUnderAbs reports whether any of the vars occurs free under a
// λ-abstraction inside a LITERAL of c — the argument-position occurrences
// the saturation cannot reach and the defining-equality twins exist to
// bridge. The check runs on the literal matrix (EffectiveLits), NOT on
// c.Term(): the ∀-prefix is itself FORALL(λx.…), which would make every
// quantified clause "under a λ" and the filter vacuous.
func hasVarUnderAbs(c *Clause, vars []VarTerm) bool {
	var walk func(t Term) bool
	walk = func(t Term) bool {
		if abs, ok := t.AsAbsTerm(); ok {
			for _, v := range vars {
				if abs.Body().HasFree(v) {
					return true
				}
			}
			return false
		}
		if app, ok := t.AsAppliedTerm(); ok {
			return walk(app.Fun()) || walk(app.Arg())
		}
		return false
	}
	for _, lit := range c.EffectiveLits() {
		if walk(lit) {
			return true
		}
	}
	return false
}

func containsVar(vars []VarTerm, v VarTerm) bool {
	for _, u := range vars {
		if u.Equals(v) {
			return true
		}
	}
	return false
}

// alignArgs builds the positional substitution from[k] := to[k], dropping
// identities. ok is false on a type mismatch at any position.
func alignArgs(from, to []VarTerm) (TermSubstsGroup, bool) {
	var substs TermSubstsGroup
	for k, a := range from {
		b := to[k]
		if !a.Type().Equals(b.Type()) {
			return nil, false
		}
		if !a.Equals(b) {
			substs = append(substs, core.MakeTermSubst(a, b))
		}
	}
	return substs, true
}

// isWitShapeClause reports whether c qualifies as a wit clause of sym
// (the shape witCandOf accepts).
func isWitShapeClause(c *Clause, sym VarTerm) bool {
	return witCandFor(c, sym) != nil
}

// DeriveAlphaMergeChain detects α-duplicated Skolem-abstraction groups in
// the given clauses, merges each equatable pair via the a/b/c/d chain, and
// iterates over the derived twins to a fixpoint (nested denotes). The
// returned steps are in dependency order: each step's hyp clauses are input
// clauses or earlier steps' conclusions, and every step has ≤2 hyps.
// Deterministic in the input order.
func DeriveAlphaMergeChain(inits []*Clause) []*ClauseThm {
	working := slices.Clone(inits)
	var chain []*ClauseThm

	// A pair whose equality is already present (as an input hypothesis or
	// from a previous enrichment) needs no merge — Simplifies can use the
	// existing clause directly. This also makes the chain idempotent.
	mergedPairs := map[[2]core.TermKey]bool{}
	for _, c := range working {
		if isVarEqVarClause(c) {
			l, r, _ := MatchesEQ(c.EffectiveBody())
			lv, _ := l.AsVar()
			rv, _ := r.AsVar()
			mergedPairs[alphaPairKey(lv, rv)] = true
		}
	}

	// Nested-shape bookkeeping: emissions of the bridge chain are deduped
	// across rounds so a pair that STILL declines after canonicalization
	// stops producing steps (see alpha_bridge.go).
	nestedSeen := map[core.TermKey]bool{}

	// One-point bookkeeping: derived clauses are deduped by clause key
	// across rounds (an elimination that fired in round n would otherwise
	// re-derive the same clause every later round, keeping the fixpoint
	// loop alive to the cap), and each symbol's defining equality is
	// derived once.
	seen := map[ClauseKey]bool{}
	for _, c := range working {
		seen[c.Key()] = true
	}
	symMerged := map[core.TermKey]bool{}

	for range _ALPHA_MERGE_MAX_ROUNDS {
		groups := detectAlphaGroups(working)
		var complete []*_alphaGroup
		for _, g := range groups {
			if len(g.wits) > 0 && len(g.intros) > 0 {
				complete = append(complete, g)
			}
		}

		var round []*ClauseThm
		emit := func(s *ClauseThm) bool {
			if s.ConclClause().EquatesT() || seen[s.ConclClause().Key()] {
				return false
			}
			seen[s.ConclClause().Key()] = true
			round = append(round, s)
			return true
		}

		// Chain move e — one-point wit elimination (see the package
		// comment): the eliminated wits join `working` at the end of the
		// round; the recombines below pick them up on the NEXT round's
		// group scan.
		for _, g := range complete {
			for _, s := range eliminateOnePointWits(g) {
				emit(s)
			}
		}

		// Chain move f — single-symbol defining-equality recombine, plus
		// its Simplifies twins. Unlike the pair path's twins, targets are
		// restricted to λ-GUARDED occurrences of the equality's symbols:
		// the enrichment exists solely to restore reachability of
		// argument-position occurrences (K(λg.α(g))); top-level literal
		// occurrences are the saturation's ordinary business, and twinning
		// them cascades (rewritten wit/intro variants re-feed the group
		// scan every round).
		for _, g := range complete {
			if symMerged[g.sym.AlphaKey()] {
				continue
			}
			eq := mergeSymbolDefinition(g)
			if eq == nil || !emit(eq) {
				continue
			}
			symMerged[g.sym.AlphaKey()] = true
			eqCl := eq.ConclClause()
			l, r, _ := MatchesEQ(eqCl.EffectiveBody())
			var eqVars []VarTerm
			if v, ok := l.AsVar(); ok {
				eqVars = append(eqVars, v)
			}
			if v, ok := r.AsVar(); ok {
				eqVars = append(eqVars, v)
			}
			// A var=var defining equality also settles the PAIR (the
			// eliminated wit doubles as an intro of the body predicate,
			// completing its group next round — without this the pair
			// path re-derives the same equality with unfiltered twins).
			if len(eqVars) == 2 {
				mergedPairs[alphaPairKey(eqVars[0], eqVars[1])] = true
			}
			defining := map[*Clause]bool{}
			for h := range eq.HypClauseIter() {
				defining[h] = true
			}
			for _, target := range working {
				if defining[target] || !hasVarUnderAbs(target, eqVars) {
					continue
				}
				if twin := eqCl.Simplifies(target); twin != nil {
					emit(twin)
				}
			}
		}

		for i, gi := range complete {
			for _, gj := range complete[i+1:] {
				if !gi.sym.Type().Equals(gj.sym.Type()) {
					continue
				}
				pairKey := alphaPairKey(gi.sym, gj.sym)
				if mergedPairs[pairKey] {
					continue
				}
				steps := alphaMergePair(gi, gj)
				if steps == nil {
					// Nested denote: the pair may be blocked by β-distinct
					// instantiations of an INNER symbol. Derive that
					// symbol's canonicalization bridge + twin wits; the
					// next round retries the pair against the twins.
					round = append(round,
						deriveNestedBridges(gi, gj, complete, nestedSeen)...)
					continue
				}
				mergedPairs[pairKey] = true
				round = append(round, steps...)

				// Step d: rewritten twins of every other working clause that
				// mentions either symbol. Simplifies orients via the derived
				// equality's absEq and attaches its own recipe; nil results
				// (wrong direction / no occurrence) are skipped. The pair's
				// defining clauses are excluded by key: a direction chain
				// renames an input apart before resolving it, and the renamed
				// copy shares the original's key.
				eqCl := steps[len(steps)-1].ConclClause()
				defining := map[ClauseKey]bool{}
				for _, s := range steps {
					for h := range s.HypClauseIter() {
						defining[h.Key()] = true
					}
				}
				for _, target := range working {
					if defining[target.Key()] ||
						(!target.Term().HasFree(gi.sym) &&
							!target.Term().HasFree(gj.sym)) {
						continue
					}
					if twin := eqCl.Simplifies(target); twin != nil {
						round = append(round, twin)
					}
				}
			}
		}
		if len(round) == 0 {
			break
		}
		chain = append(chain, round...)
		for _, s := range round {
			working = append(working, s.ConclClause())
			// Absorb the pair/nested paths' emissions too (they append to
			// `round` directly): without this, round-2 single-symbol
			// merges re-derive a pair equality from its own bridge
			// clauses (which double as each other's wit/intro).
			seen[s.ConclClause().Key()] = true
		}
	}
	return chain
}
