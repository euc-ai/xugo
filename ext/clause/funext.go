// funext.go — the FUNEXT clause-deduce rule.
//
// FunEqRewrite (pre-CNF normalization) extensionalizes every function-typed
// equality hypothesis into pointwise form before clause extraction:
//
//	s = e : A→bool   ⟶   {∀x. e(x) ∨ ¬s(x)},  {∀x. s(x) ∨ ¬e(x)}
//	f = g : A→B      ⟶   {∀x. f(x) = g(x)}          (B non-bool)
//
// An equality under a condition is extensionalized the same way, and the
// condition's literals ride along into every clause (after ImplyToOr):
//
//	C ⇒ s = e : A→bool   ⟶   {∀x. C ∨ e(x) ∨ ¬s(x)},  {∀x. C ∨ s(x) ∨ ¬e(x)}
//	C ⇒ f = g : A→B      ⟶   {∀x. C ∨ f(x) = g(x)}
//
// The pointwise clauses connect only to APPLICATIONS s(t); occurrences of s
// in ARGUMENT position of an opaque head (set_member(x, s), finite(s),
// iterated_op(op, s, f)) are unreachable — the refutation is impossible in that
// clause space, not merely slow (the set_tac gap: function-typed equality
// hyps are extensionalized away before the clause level).
//
// FUNEXT recovers the equality as a DERIVED clause: funext is a theorem in
// HOL (core.Eta + Abs), so from the pointwise clause forms the rule derives
// the equality clause `C ∨ s = e`, which resolves against the condition's
// complement into the unit equality the existing unit-equality Simplifies
// paramodulation consumes (and is that unit clause outright when C is
// empty). The derived clause is keyed as the equality it is — clause
// normalization does not extensionalize (prop.DisjunctNormalizeRewrite) —
// so the refuter does not take it for the pointwise initial clause it came
// from. Because the derivation consumes clauses already in the set,
// nothing about the CNF (clause set, RefuteProp, cache keys) changes —
// existing stored refutation certificates and their cache rows are
// untouched. The derived clause carries a deduceRecipe (rule FUNEXT) like
// every other inference, so replay re-runs the deterministic builder below.
//
// Two input shapes, one rule (disambiguated by len(recipe.inputs)):
//
//	[c]      ∀-equality clause  ∀x. C ∨ F(x) = G(x)           → ⊢ C ∨ F = G
//	[c0,c1]  complementary pair (the bool/iff case)
//	         ∀x. C ∨ A ∨ ¬B  +  ∀x. C ∨ ¬A ∨ B                → ⊢ C ∨ A_fn = B_fn
//
// The context C is every literal of the clause beside the equality, or
// every literal the two clauses of a pair share; it mentions none of the
// binders contracted over. A binder a context literal mentions is not
// contracted: it stays universally bound around the result, so
// ∀y x. C(y) ∨ F(y, x) = G(y, x) gives ∀y. C(y) ∨ F(y) = G(y). With an
// empty context the shapes are the plain unit and 2-literal forms.
//
// Contraction scope: every contracted binder is abstracted (Abs), and
// each side η-contracts independently where it applies (see
// funextContract). Shapes that contract fully yield the prefix-free
// equality; shapes whose sides disagree on the trailing argument (the
// nested alpha-bridge class — alpha_bridge.go) yield a λ-sided
// FUNCTION-typed equality. deriveInitFunext (prover/solver/refuter)
// records the fully-contracted form and the λ-sided form whose other
// side is a variable T does not mention — a naming equation `e = λx. T`,
// the clause form of a hypothesis that names a function value, which the pointwise
// clause cannot carry to the name's argument occurrences
// (NamingEqSides). A naming equation stands beside its pointwise source
// (the refuter retires neither for the other): the source rewrites the
// name's applications, the equation folds the value into the name where
// it is an argument. A constant against a λ is a definition, not a
// name, and is not recorded. The alpha-bridge consumes the other
// partial forms.

package clause

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// LambdaFreeEqSides reports whether c carries an equality literal and no
// equality literal of c has a λ-abstraction on either side — the
// fully-contracted FUNEXT result shape, the recombined equality beside
// the context it was derived under. deriveInitFunext records this shape
// and the naming shape (NamingEqSides); the other partially-contracted
// (λ-sided) forms are consumed only by the alpha-bridge chain
// (alpha_bridge.go).
func LambdaFreeEqSides(c *Clause) bool {
	found := false
	for _, lit := range c.EffectiveLits() {
		l, r, ok := MatchesEQ(lit)
		if !ok {
			continue
		}
		if _, lok := l.AsAbsTerm(); lok {
			return false
		}
		if _, rok := r.AsAbsTerm(); rok {
			return false
		}
		found = true
	}
	return found
}

// NamingEqSides reports whether c carries an equality literal with a
// λ-abstraction on one side and, on the other, a VARIABLE the abstraction
// does not mention, and no λ-sided equality literal of another shape: the
// contracted form of
// `∀x. e(x) = T(x)`, the pointwise clause of a hypothesis `e = λx. T(x)`
// that names a function value (an obtained witness, a denotation, a
// symbol the pipeline minted). The pointwise clause reaches e through
// its applications alone; where e stands as an argument of an opaque
// head, `equivalence_class(R, e)`, `finite(e)`, only the derived
// equality connects it to the value, and the refutation is impossible
// without it. One such equality names one value, so recording it costs
// the search one unit clause. A CONSTANT against a λ is a definition,
// not a name: the set driver's residence rule
// `∀s x. set_comprehension(s, x) ⇔ s(x)` contracts to
// `set_comprehension = λs. s`, and recorded as a unit equality it
// unfolds the constant wherever the search spells it — the
// def-expansion the membership driver keeps out of the refuter. A
// λ-free equality is LambdaFreeEqSides's shape: it rewrites in both
// positions and replaces its sources. A variable standing in its own
// value, `Q = λx y. Q(y, x)` from a commutativity axiom, is a rewrite
// that makes its own redexes (the demodulator bounds the chain, the
// search still churns): the alpha-bridge's shape, not a name.
func NamingEqSides(c *Clause) bool {
	found := false
	for _, lit := range c.EffectiveLits() {
		l, r, ok := MatchesEQ(lit)
		if !ok {
			continue
		}
		_, lAbs := l.AsAbsTerm()
		_, rAbs := r.AsAbsTerm()
		switch {
		case lAbs && rAbs:
			return false
		case lAbs && !namesValue(r, l), rAbs && !namesValue(l, r):
			return false
		case lAbs || rAbs:
			found = true
		}
	}
	return found
}

// namesValue reports whether name is a variable that value does not
// mention: the shape of a hypothesis naming a function value. A
// variable standing in its own value — commutativity contracted,
// `Q = λx y. Q(y, x)` — is a rewrite that makes its own redexes, not a
// name.
func namesValue(name, value Term) bool {
	v, ok := name.AsVar()
	return ok && !value.HasFree(v)
}

// FunextFromUnitEq derives `⊢ C ∨ F = G` from a clause
// `∀x₁…xₙ. C ∨ F(x₁)…(xₙ) = G(x₁)…(xₙ)` whose context C — every literal
// but the equality — mentions none of the binders contracted over (n ≥ 1;
// a binder free in a context literal stays universally bound around the
// result). Returns nil when no equality literal mentions a binder, more
// than one does, or no binder is left to contract over; a binder that is
// not the exact trailing argument on a side leaves that side a λ
// (funextContract).
func FunextFromUnitEq(c *Clause) *ClauseThm {
	if c.univBoundVars.Empty() {
		return nil
	}
	eqInd := -1
	var context []int
	for i, lit := range c.literals {
		if _, _, ok := MatchesEQ(lit); ok && mentionsBinder(c, lit) {
			if eqInd >= 0 {
				return nil
			}
			eqInd = i
			continue
		}
		context = append(context, i)
	}
	if eqInd < 0 {
		return nil
	}
	contract, outer := funextBinders(c, context)
	if len(contract) == 0 {
		return nil
	}
	// Peel the ∀ prefix: {c.Term()} ⊢ C ∨ F(x) = G(x) with every binder free.
	w := prop.Assume(c.Term())
	for v := range c.univBoundVars.Iter() {
		w = w.DeriveTrans(prop.InstForAll(w.Conclusion(), v))
	}
	lits := DecomposesOR(w.Conclusion())
	if len(lits) != len(c.literals) {
		return nil
	}
	spelled := make([]Term, len(context))
	for k, i := range context {
		spelled[k] = lits[i]
	}
	w = dischargeContext(w, lits, context, spelled)
	if w == nil {
		return nil
	}
	w = funextContract(w, contract)
	if w == nil {
		return nil
	}
	w = restoreContext(w, spelled)
	return makeFunextClauseThm(generalizeOuter(w, outer), c)
}

// FunextFromIffPair derives `⊢ C ∨ A_fn = B_fn` from a complementary
// clause pair — the pointwise form FunEqRewrite + IffToOr leave behind for a
// bool-valued (set-typed) function equality under the condition ¬C:
//
//	c0: ∀x. C ∨ A ∨ ¬B        (order/roles detected, not assumed)
//	c1: ∀x. C ∨ ¬A ∨ B
//
// The context C is the literals the two clauses share up to their
// binders' names; it mentions none of the binders contracted over (a
// binder it mentions stays universally bound around the result), and is
// empty for the plain 2-literal pair. Under the context's negation the two
// clauses are recombined into `∀x. A = B` (each direction by rewriting the
// other clause under the assumption, then Deduct), the result
// funext-contracts exactly like the unit case, and the context returns to
// the conclusion. Returns nil when the pair doesn't match (arity/type/
// literal mismatch, a context literal mentioning every binder) or
// contraction fails.
func FunextFromIffPair(c0, c1 *Clause) *ClauseThm {
	if c0 == c1 || len(c0.literals) < 2 || len(c0.literals) != len(c1.literals) {
		return nil
	}
	n := c0.univBoundVars.Size()
	if n == 0 || c1.univBoundVars.Size() != n {
		return nil
	}
	// Peel both prefixes AT c0's binder vars, so the bodies are directly
	// alpha-comparable. Kernel instantiation is capture-avoiding; a type
	// mismatch at any position disqualifies the pair.
	for i := 0; i < n; i++ {
		if !c0.univBoundVars.Ind(i).Type().Equals(c1.univBoundVars.Ind(i).Type()) {
			return nil
		}
	}
	context0, context1, pair0, pair1 := matchContext(c0, c1)
	if pair0 == nil {
		return nil
	}
	// Complementarity up to the binders' names, before any kernel work:
	// c0 keeps A ∨ ¬B, c1 keeps B ∨ ¬A.
	pos0, neg0, ok0 := splitPosNeg([]Term{c0.literals[pair0[0]], c0.literals[pair0[1]]})
	pos1, neg1, ok1 := splitPosNeg([]Term{c1.literals[pair1[0]], c1.literals[pair1[1]]})
	if !ok0 || !ok1 ||
		closedKey(pos0, c0) != closedKey(neg1, c1) ||
		closedKey(neg0, c0) != closedKey(pos1, c1) {
		return nil
	}
	contract, outer := funextBinders(c0, context0)
	if len(contract) == 0 {
		return nil
	}
	u0 := prop.Assume(c0.Term())
	u1 := prop.Assume(c1.Term())
	for v := range c0.univBoundVars.Iter() {
		u0 = u0.DeriveTrans(prop.InstForAll(u0.Conclusion(), v))
		u1 = u1.DeriveTrans(prop.InstForAll(u1.Conclusion(), v))
	}
	lits0 := DecomposesOR(u0.Conclusion())
	lits1 := DecomposesOR(u1.Conclusion())
	if len(lits0) != len(c0.literals) || len(lits1) != len(c1.literals) {
		return nil
	}
	// The context hypotheses take c0's spelling in both clauses, so the
	// two chains meet in one hypothesis per literal.
	spelled := make([]Term, len(context0))
	for k, i := range context0 {
		spelled[k] = lits0[i]
	}
	u0 = dischargeContext(u0, lits0, context0, spelled)
	u1 = dischargeContext(u1, lits1, context1, spelled)
	if u0 == nil || u1 == nil {
		return nil
	}
	rest0 := DecomposesOR(u0.Conclusion())
	rest1 := DecomposesOR(u1.Conclusion())
	if len(rest0) != 2 || len(rest1) != 2 {
		return nil
	}
	// Classify each clause's literals: exactly one positive, one negative.
	pos0, neg0, ok0 = splitPosNeg(rest0)
	pos1, neg1, ok1 = splitPosNeg(rest1)
	if !ok0 || !ok1 {
		return nil
	}
	// Complementarity: c0 = A ∨ ¬B, c1 = B ∨ ¬A.
	A, B := pos0, neg0
	if !neg1.AlphaEquals(A) || !pos1.AlphaEquals(B) {
		return nil
	}

	// Direction A ⊢ B: assume A, rewrite u1's conclusion (¬A ∨ B) with
	// A = ⊤ and simplify; the result must be exactly B (a strict guard —
	// if A occurs inside B the rewrite would corrupt it and the shapes
	// won't match, declining the pair instead of deriving junk).
	tAB := funextDischargeDir(A, B, u1)
	if tAB == nil {
		return nil
	}
	// Direction B ⊢ A symmetric via u0 (A ∨ ¬B).
	tBA := funextDischargeDir(B, A, u0)
	if tBA == nil {
		return nil
	}
	// {c0.Term(), c1.Term(), context hyps} ⊢ A = B, then contract.
	w := funextContract(tBA.Deduct(tAB), contract)
	if w == nil {
		return nil
	}
	w = restoreContext(w, spelled)
	return makeFunextClauseThm(generalizeOuter(w, outer), c0, c1)
}

// mentionsBinder reports whether lit has one of c's binders free.
func mentionsBinder(c *Clause, lit Term) bool {
	for v := range c.univBoundVars.Iter() {
		if lit.HasFree(v) {
			return true
		}
	}
	return false
}

// funextBinders partitions c's binders around its context literals (by
// index): a binder free in a context literal is outer and stays
// universally bound around the result; every other binder is contracted
// over. Both lists keep the prefix order.
func funextBinders(c *Clause, context []int) (contract, outer []VarTerm) {
	for v := range c.univBoundVars.Iter() {
		if slices.ContainsFunc(context, func(i int) bool { return c.literals[i].HasFree(v) }) {
			outer = append(outer, v)
		} else {
			contract = append(contract, v)
		}
	}
	return contract, outer
}

// closedKey is the α-key of t abstracted over c's binders: two literals
// of two clauses with the same binder types get one key exactly when they
// agree up to the binders' names.
func closedKey(t Term, c *Clause) core.TermKey {
	for _, v := range c.univBoundVars.Backward() {
		t = Abs(v, t)
	}
	return t.AlphaKey()
}

// matchContext pairs the literals c0 and c1 share up to their binders'
// names — the context — and returns the indices of each clause's context
// literals, paired by position, and the indices of the two literals each
// clause keeps for the complementary pair. The pairs are nil when a
// clause keeps a number of literals other than two.
func matchContext(c0, c1 *Clause) (context0, context1, pair0, pair1 []int) {
	keys1 := make([]core.TermKey, len(c1.literals))
	for j, lit := range c1.literals {
		keys1[j] = closedKey(lit, c1)
	}
	matched := make([]bool, len(keys1))
	for i, lit := range c0.literals {
		key := closedKey(lit, c0)
		j := slices.IndexFunc(keys1, func(k core.TermKey) bool { return k == key })
		for j >= 0 && matched[j] {
			// A key c1 carries twice: the next unmatched carrier, if any.
			if next := slices.IndexFunc(keys1[j+1:], func(k core.TermKey) bool { return k == key }); next < 0 {
				j = -1
			} else {
				j += 1 + next
			}
		}
		if j < 0 {
			pair0 = append(pair0, i)
			continue
		}
		matched[j] = true
		context0 = append(context0, i)
		context1 = append(context1, j)
	}
	for j, m := range matched {
		if !m {
			pair1 = append(pair1, j)
		}
	}
	if len(pair0) != 2 || len(pair1) != 2 {
		return nil, nil, nil, nil
	}
	return context0, context1, pair0, pair1
}

// contextHyp is the hypothesis a context literal is discharged under and
// the equality that rewrites the literal away under it: a negative literal
// ¬m under m (m = ⊤ turns it into ¬⊤), any other literal under its
// negation (lit = ⊥). restoreContext moves the hypothesis back as the
// literal itself.
func contextHyp(lit Term) (Term, *prop.PropWrapper) {
	if m := MatchesNOT(lit); m != nil {
		return m, prop.Assume(m).Deduct(prop.DerivesTrue) // {m} ⊢ m = ⊤
	}
	return Not(lit).Core(), prop.EqualsFalse(lit).RightAssume() // {¬lit} ⊢ lit = ⊥
}

// dischargeContext moves the context literals of the peeled clause u out
// of its conclusion and into its hypotheses, each under contextHyp's
// hypothesis: {hyps} ⊢ L₁ ∨ … ∨ Lₖ ∨ rest becomes {hyps, h₁, …, hₖ} ⊢ rest.
// lits are the conclusion's literals, context the indices to discharge
// and spelled, parallel to context, the same literals in the spelling the
// hypotheses take. Each literal is rewritten away under its hypothesis and
// the remainder checked exactly — a literal that also occurs inside
// another literal declines (nil) instead of being rewritten there too.
func dischargeContext(u *prop.PropWrapper, lits []Term, context []int, spelled []Term) *prop.PropWrapper {
	dropped := make([]bool, len(lits))
	for k, i := range context {
		dropped[i] = true
		rest := make([]Term, 0, len(lits))
		for j, lit := range lits {
			if !dropped[j] {
				rest = append(rest, lit)
			}
		}
		_, eq := contextHyp(spelled[k])
		bridge := prop.ChainRewrites(prop.EqRewrite(eq), BasicRewrite)(u.Conclusion())
		if bridge == nil || !Rhs(bridge).AlphaEquals(Or(rest...)) {
			return nil
		}
		u = bridge.EqMP(u)
	}
	return u
}

// restoreContext moves the context hypotheses dischargeContext introduced
// back into the conclusion as the literals they stand for:
// {hyps, h₁, …, hₖ} ⊢ c becomes {hyps} ⊢ c ∨ L₁ ∨ … ∨ Lₖ.
func restoreContext(w *prop.PropWrapper, spelled []Term) *prop.PropWrapper {
	for _, lit := range spelled {
		hyp, _ := contextHyp(lit)
		c := w.Conclusion()
		// {hyps} ⊢ ¬hyp ∨ c
		w = prop.BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](hyp, c).EqMP(w.PromoteHyp(hyp))
		if MatchesNOT(lit) == nil {
			// ¬¬lit ∨ c  →  lit ∨ c
			w = prop.DoubleNeg(lit).LeftApply(OR).RightApply(c).EqMP(w)
		}
		w = prop.CommuteOR(lit, c).EqMP(w)
	}
	return w
}

// generalizeOuter binds the outer binders back around the conclusion, in
// prefix order.
func generalizeOuter(w *prop.PropWrapper, outer []VarTerm) *prop.PropWrapper {
	for i := len(outer) - 1; i >= 0; i-- {
		w = w.ConclForAll(outer[i])
	}
	return w
}

// funextDischargeDir derives {hyps(u), from} ⊢ to, where u's conclusion is
// the 2-literal disjunction containing ¬from and to (in either order).
// Mechanic: `from = ⊤` (Assume + Deduct DerivesTrue) rewrites u's conclusion;
// BasicRewrite collapses `¬⊤ ∨ to` to `to`. Nil when the collapsed result
// isn't exactly `to`.
func funextDischargeDir(from, to Term, u *prop.PropWrapper) *prop.PropWrapper {
	eqTrue := prop.Assume(from).Deduct(prop.DerivesTrue) // {from} ⊢ from = ⊤
	rw := prop.ChainRewrites(prop.EqRewrite(eqTrue), BasicRewrite)
	bridge := rw(u.Conclusion())
	if bridge == nil || !Rhs(bridge).AlphaEquals(to) {
		return nil
	}
	// bridge: {from} ⊢ (u.Concl) = to;  u: {hyps} ⊢ u.Concl.
	return bridge.EqMP(u)
}

// splitPosNeg classifies a 2-literal list into (positive, stripped-negative).
// ok is false unless there is exactly one of each.
func splitPosNeg(lits []Term) (pos, neg Term, ok bool) {
	n0 := MatchesNOT(lits[0])
	n1 := MatchesNOT(lits[1])
	switch {
	case n0 == nil && n1 != nil:
		return lits[0], n1, true
	case n0 != nil && n1 == nil:
		return lits[1], n0, true
	}
	return nil, nil, false
}

// funextContract contracts w: {hyps} ⊢ A = B (with the given vars free on
// both sides) toward the function-level equality, one binder at a time.
//
// Each step abstracts one remaining var x (Abs — always derivable) and
// η-contracts EACH SIDE INDEPENDENTLY where it applies (side = F(x) with
// x ∉ F). The var choice is greedy and deterministic:
//
//  1. a var that is the shared trailing argument of BOTH sides; when
//     the whole equality contracts fully (the flat FUNEXT / ALPHA-MERGE
//     shapes), every step takes this branch and the result is the
//     both-sides-η contraction;
//  2. else a var that is the trailing argument of ONE side — the partial
//     shape the nested alpha-bridge needs (∀h. β(λg.g, ƒ(h)) = β(ƒ, h)
//     contracts to (λf.λh. β(λg.g, f(h))) = β: the right side η's, the
//     left keeps its λ);
//  3. else the first remaining var in order (Abs only, no η).
//
// The contraction never fails on shape — the result may carry λ-sided
// equalities. Callers that need the fully-contracted (λ-free) form filter
// on it (deriveInitFunext does, and that is its enrichment scope); the
// alpha-bridge accepts the partial forms, which are legal FUNCTION-typed
// equality literals (unlike the bool ∀-iff, which IsDisjunctive rejects).
// Nil only when the conclusion stops being an equality (cannot happen for
// the recombine callers, kept as a guard).
func funextContract(w *prop.PropWrapper, vars []VarTerm) *prop.PropWrapper {
	remaining := make(map[core.TermKey]bool, len(vars))
	for _, v := range vars {
		remaining[v.AlphaKey()] = true
	}
	order := slices.Clone(vars)
	trailing := func(t Term) (core.AppliedTerm, VarTerm) {
		app, ok := t.AsAppliedTerm()
		if !ok {
			return core.AppliedTerm{}, VarTerm{}
		}
		x, ok := app.Arg().AsVar()
		if !ok || !remaining[x.AlphaKey()] || app.Fun().HasFree(x) {
			return core.AppliedTerm{}, VarTerm{}
		}
		return app, x
	}
	for range vars {
		l, r, ok := MatchesEQ(w.Conclusion())
		if !ok {
			return nil
		}
		lApp, lv := trailing(l)
		rApp, rv := trailing(r)
		var x VarTerm
		switch {
		case !lv.IsZero() && !rv.IsZero() && lv.Equals(rv):
			x = lv
		case !lv.IsZero():
			x = lv
		case !rv.IsZero():
			x = rv
		default:
			for _, v := range order {
				if remaining[v.AlphaKey()] {
					x = v
					break
				}
			}
		}
		delete(remaining, x.AlphaKey())
		// ⊢ λx.L = λx.R, then eta each side that has the F(x) shape.
		w = w.Abs(x)
		if !lv.IsZero() && lv.Equals(x) {
			w = WrapProp(core.Eta(lApp)).EqSym().EqTrans(w) // λx.F(x) → F
		}
		if !rv.IsZero() && rv.Equals(x) {
			w = w.EqTrans(WrapProp(core.Eta(rApp)))
		}
	}
	return w
}

// makeFunextClauseThm wraps the contracted equality proof as a derived
// ClauseThm with the FUNEXT recipe. The conclusion clause is built from the
// equality verbatim; hyps are the input clause terms (already the proof's
// hyps via the Assume-peeled chains).
func makeFunextClauseThm(w *prop.PropWrapper, inputs ...*Clause) *ClauseThm {
	concl := MakeClause(w.Conclusion())
	return MakeClauseThm(w.AsThmCert(), concl, inputs...).
		withRecipe(&deduceRecipe{rule: _RuleFunext, inputs: inputs})
}

// funextReplay reproduces a FUNEXT inference from its recipe inputs
// (search-free, deterministic — the builders take no unifier).
func funextReplay(inputs []*Clause) *ClauseThm {
	switch len(inputs) {
	case 1:
		return FunextFromUnitEq(inputs[0])
	case 2:
		return FunextFromIffPair(inputs[0], inputs[1])
	}
	return nil
}
