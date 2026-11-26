/**
 * File: normalize.go
 *
 * Implements term and proposition normalization.
 *
 * Main functions:
 * - univQuantifiersSort(t Term): Rearranges universal quantifier variables
 *   Orders variables first by type, then by occurrence in body
 *
 * - univQuantifiersSortRewrite(t Term): Rewrite of quantifier reordering
 *
 * - DisjunctNormalizeRewrite(t Term): Comprehensive normalization of disjunctive terms
 *   Performs these steps repeatedly until convergence:
 *   1. Renames quantifier variables using De Bruijn indices
 *   2. Sorts equality expressions
 *   3. Sorts disjunctive clauses
 *   4. Sorts quantifier variables by type
 *   5. Restores variable names at the end
 *
 * - Normalize(Prop): Converts proposition to canonical form
 *   Returns normalized proposition and reconstruction function
 *   Performs these transformations:
 *   1. Adds appropriate quantifiers to conclusion and hypotheses
 *   2. Removes hypotheses via removeHyps
 *   3. Simplifies the conclusion using rewrite rules
 *   4. Adds universal quantifiers to free variables
 *   5. Applies DisjunctNormalizeRewrite for canonical representation
 *
 * Specialized rewrite combinations:
 * - forAllORSimplify: Combines universal quantifier distribution and disjunct simplification
 * - disjunctConclSimplifyRewrite: Chain of rewrites for normalizing disjunctive conclusions
 * - PreCNFNormalizeRewrite: Named composition that takes a closed prop into pre-CNF normal form
 *   (NNF, implication-free, prenex where safe, sorted, β/η-reduced) without Skolemizing
 *   or distributing ∨ over ∧. The statement-identity layer.
 */

package prop

import (
	"cmp"
	"context"
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// quantifiersSort reorders one same-kind binder block (the ∀ or ∃ block
// binding vars over the body s) for canonical form. The ordering is
// determined by:
// 1. Variable type (types are sorted by their canonical ordering)
// 2. Order of appearance in the body (for variables of the same type)
// This ensures that ∀x:A.∀y:B.P(x,y) and ∀y:B.∀x:A.P(x,y) normalize to the
// same form when A and B have a defined ordering. Binders the body does
// not mention are ordered by type alone. The one rule serves the
// outermost ∀ prefix and every block below it (deepQuantifierBlockSortRewrite),
// so a block's order never depends on the order the prenex rules pulled
// its binders in.
//
// Appearance order reads the body's chain order, which the disjunct sort
// fixes from the De Bruijn indices this very order assigns; the two are
// iterated to a fixed point (DisjunctNormalizeRewrite), and a symmetric
// clause set has several. Which one is reached is decided by the order
// the iteration STARTS from — canonicalBinderStartRewrite, a labeling
// that is a function of the block's α-class — so the input's binder
// names and chain order never choose (the refute props of set_image's
// image lemmas keyed by their Skolem names before that pass existed).
func quantifiersSort(vars VarList, s Term, quantify ext.QuantifierOp) Term {
	return blockSort(vars, s, quantify, appearanceOrder)
}

// appearanceOrder is quantifiersSort's rule for the binders the body
// mentions: by type, then by first appearance in the body.
func appearanceOrder(relevant []VarTerm, s Term) []VarTerm {
	var orderedVars []VarTerm
	var varTypes []HolType
	for _, v := range relevant {
		vType := v.Type()
		i, _ := slices.BinarySearchFunc(varTypes, vType, HolType.Compare)
		varTypes = slices.Insert(varTypes, i, vType)
		orderedVars = slices.Insert(orderedVars, i, v)
	}
	return orderedVars
}

// blockSort rebuilds the block over s with the binders the body mentions
// in the order rule gives (innermost-first, as quantify wraps) and the
// binders it does not mention outside them, by type alone.
func blockSort(vars VarList, s Term, quantify ext.QuantifierOp, rule func([]VarTerm, Term) []VarTerm) Term {
	var irrelevantVars []VarTerm
	var boundVars ext.VarList
	for v := range vars.Iter() {
		if s.HasFree(v) {
			boundVars.Add(v)
		} else {
			irrelevantVars = append(irrelevantVars, v)
		}
	}
	for _, v := range rule(s.Frees(boundVars.Has), s) {
		s = quantify(v)(s)
	}
	// For irrelevant vars, only type matters, so we sort by type.
	slices.SortFunc(irrelevantVars,
		func(v0, v1 VarTerm) int { return HolType.Compare(v0.Type(), v1.Type()) })
	for _, v := range irrelevantVars {
		s = quantify(v)(s)
	}
	return s
}

// canonicalBinderStartRewrite reorders every ∀ and ∃ block of t by
// canonicalBinderOrder — innermost-first the labeling lists
// outermost-first, so the list is reversed for quantify. It runs once,
// at the entry of DisjunctNormalizeRewrite, to give the appearance-order
// iteration a start that is a function of the term's α-class; the
// iteration itself is unchanged, so a block with one fixed point still
// reaches it.
var canonicalBinderStartRewrite = blockStructureRewrite(func(t Term) *PropWrapper {
	if vars, s := DecomposesFORALL(t); !vars.Empty() {
		if _t := blockSort(vars, s, ForAll, canonicalStartOrder).Core(); !t.Equals(_t) {
			return ReorderForAll(t, _t)
		}
		return nil
	}
	if vars, s := DecomposesEXISTS(t); !vars.Empty() {
		if _t := blockSort(vars, s, Exists, canonicalStartOrder).Core(); !t.Equals(_t) {
			return ReorderExists(t, _t)
		}
	}
	return nil
})

func canonicalStartOrder(relevant []VarTerm, s Term) []VarTerm {
	order := canonicalBinderOrder(relevant, s)
	slices.Reverse(order)
	return order
}

func univQuantifiersSort(t Term) Term {
	vars, s := DecomposesFORALL(t)
	if vars.Empty() {
		return t
	}
	return quantifiersSort(vars, s, ForAll)
}

func existsQuantifiersSort(t Term) Term {
	vars, s := DecomposesEXISTS(t)
	if vars.Empty() {
		return t
	}
	return quantifiersSort(vars, s, Exists)
}

// Proves that the original and reordered quantifications are equivalent.
func univQuantifiersSortRewrite(t Term) (w *PropWrapper) {
	if _t := univQuantifiersSort(t).Core(); !t.Equals(_t) {
		return ReorderForAll(t, _t)
	}
	return nil
}

func existsQuantifiersSortRewrite(t Term) (w *PropWrapper) {
	if _t := existsQuantifiersSort(t).Core(); !t.Equals(_t) {
		return ReorderExists(t, _t)
	}
	return nil
}

// deepQuantifierBlockSortRewrite sorts every ∀ block and every ∃ block in
// the term by quantifiersSort's rule. The prenex rules pull binders in
// chain order and leave a block's order at that; without this pass a ∀
// block under an ∃ (finite_set.FiniteImageEqInj: ∃t.∀x.∀y.∀ẋ. against
// ∃t.∀ẋ.∀x.∀y.) and every ∃ block kept the order the input's conjuncts
// happened to induce, and two spellings of one statement keyed apart.
var deepQuantifierBlockSortRewrite = boolStructureRewrite(func(t Term) *PropWrapper {
	if w := univQuantifiersSortRewrite(t); w != nil {
		return w
	}
	return existsQuantifiersSortRewrite(t)
})

// boolStructureRewrite applies rule at t and at every position reachable
// from t through BOOLEAN STRUCTURE only — a quantifier's body, ¬, and the
// two sides of ∧ ∨ ⇒ ⇔ — and never through the argument of any other
// application. A quantifier block that sits inside a term the statement
// merely DENOTES is part of that term's encoding and positional to its
// readers: the paired lambda `λ(x,y). t` is
// `pattern_abstraction(λf. ∀x y. f(x,y) = t)`, the set-builder `{(x,y) | P}` is
// `set_comprehension(λv. ∃x y. comprehension_spec(v, P, (x,y)))`, and the paired-beta driver,
// the set-builder expansion and the printers all read those binders by
// position (InstantiateLambdaPair destructures them). Sorting or merging
// them is sound and destroys the encoding — measured: the block sort run
// through DeepRewrite turned the paired-lambda law's stored `∀x y` into `∀y x`, and
// the paired-beta composite stopped firing on every goal that spelled
// the encoding in the written order. So the block passes walk boolean structure and
// stop at pattern_abstraction, set_comprehension, ε and every other non-connective head.
func boolStructureRewrite(rule Rewrite) Rewrite {
	return structureRewrite(rule, false)
}

// blockStructureRewrite is boolStructureRewrite for a rule that reads a
// quantifier block as a WHOLE: at a ∀ or ∃ prefix it applies the rule to
// the maximal same-kind block and then descends under all of its
// binders at once, so the rule never sees a suffix of a prefix as a
// block of its own. A rule whose verdict on a suffix can differ from its
// verdict on the whole block — canonicalBinderStartRewrite's labeling,
// which colors the block's binders and reads a peeled binder as a free
// variable — would otherwise undo itself between a prefix and its
// suffixes without end; first-appearance order is suffix-consistent
// and never needed this.
func blockStructureRewrite(rule Rewrite) Rewrite {
	return structureRewrite(rule, true)
}

func structureRewrite(rule Rewrite, maximalBlocks bool) Rewrite {
	var deep Rewrite
	descend := func(t Term) *PropWrapper {
		if abs := MatchesFORALL(t); !abs.IsZero() {
			if maximalBlocks {
				return liftUnderPrefix(t, MatchesFORALL, deep)
			}
			return liftQuantifierBody(t, abs, deep)
		}
		if abs := MatchesEXISTS(t); !abs.IsZero() {
			if maximalBlocks {
				return liftUnderPrefix(t, MatchesEXISTS, deep)
			}
			return liftQuantifierBody(t, abs, deep)
		}
		if u := MatchesNOT(t); u != nil {
			if w := deep(u); w != nil {
				return w.LeftApply(t.Core().(AppliedTerm).Fun())
			}
			return nil
		}
		for _, matches := range []ext.BinaryOpMatcher{MatchesAND, MatchesOR, MatchesIMPLY, MatchesIFF} {
			l, r, ok := matches(t)
			if !ok {
				continue
			}
			app := t.Core().(AppliedTerm)
			wl, wr := deep(l), deep(r)
			switch {
			case wl != nil && wr != nil:
				return wl.LeftApply(app.Fun().(AppliedTerm).Fun()).Apply(wr)
			case wl != nil:
				return wl.LeftApply(app.Fun().(AppliedTerm).Fun()).RightApply(r)
			case wr != nil:
				return wr.LeftApply(app.Fun())
			}
			return nil
		}
		return nil
	}
	deep = func(t Term) *PropWrapper {
		if w := rule(t); w != nil {
			return w.RewriteConclRhsRecur(deep)
		}
		return descend(t)
	}
	return deep
}

// liftQuantifierBody rewrites the body of the quantified term t = Q(λx.body)
// with deep and lifts the equation through the binder and the quantifier.
func liftQuantifierBody(t Term, abs AbsTerm, deep Rewrite) *PropWrapper {
	w := deep(abs.Body())
	if w == nil {
		return nil
	}
	return w.Abs(abs.Var()).LeftApply(t.Core().(AppliedTerm).Fun())
}

// liftUnderPrefix rewrites the body below the maximal prefix of the
// quantifier kind matches recognizes and lifts the equation through
// every binder of the prefix; no position inside the prefix is offered
// to deep.
func liftUnderPrefix(t Term, matches func(Term) AbsTerm, deep Rewrite) *PropWrapper {
	abs := matches(t)
	if abs.IsZero() {
		return deep(t)
	}
	w := liftUnderPrefix(abs.Body(), matches, deep)
	if w == nil {
		return nil
	}
	return w.Abs(abs.Var()).LeftApply(t.Core().(AppliedTerm).Fun())
}

// blockOps is one quantifier kind as the block canonicalization sees it:
// the connective it distributes over (∧ for ∀, ∨ for ∃) and the theorems
// that distribute it, drop it when vacuous, and reorder it.
type blockOps struct {
	decompose   func(Term) (VarList, Term)
	dualMatcher ext.BinaryOpMatcher
	dualConst   ConstTerm
	// distribute(λx.l, λx.r) proves ⊢ Qx.(l op r) = (Qx.l op Qx.r).
	distribute func(Term, Term) *PropWrapper
	// moot(x, q) proves ⊢ Qx.q = q for x not free in q.
	moot     func(VarTerm, Term) *PropWrapper
	reorder  func(Term, Term) *PropWrapper
	quantify ext.QuantifierOp
}

var forAllBlockOps = blockOps{
	DecomposesFORALL, MatchesAND, AND, ForAllAND, MootForAll, ReorderForAll, ForAll}
var existsBlockOps = blockOps{
	DecomposesEXISTS, MatchesOR, OR, ExistsOR, MootExists, ReorderExists, Exists}

// closureOrder lists the binders of vars that c mentions, in c's own
// order: first appearance in c, stably by type. It is intrinsic to the
// clause — invariant under any renaming of the block's binders — which
// is what lets distributeBlock align a block's closures with its
// canonical form's for the α-comparison.
func closureOrder(vars VarList, c Term) []VarTerm {
	vs := c.Frees(vars.Has)
	slices.SortStableFunc(vs, func(a, b VarTerm) int {
		return HolType.Compare(a.Type(), b.Type())
	})
	return vs
}

// canonicalQuantifierBlockRewrite rewrites a ∀ block over an ∧ chain (or
// an ∃ block over an ∨ chain) to the form in which the chain's clauses
// share binders BY RANK. Since Qx̄.(c₁ op … op cₙ) ⇔ (Qx̄₁.c₁) op … op
// (Qx̄ₙ.cₙ), x̄ⱼ the binders cⱼ mentions, how the clauses share binders
// is representation, and a block is one theorem however its binders
// were identified on the way in — by the prenex rules, which identify
// the outermost binders of the components they pull together, so a
// premise's binder order, the premises' order and the ∨ tree a ⇒ chain
// leaves all chose (presheaf.GermActionDistributive keyed apart from
// its ∧-joined restatement); by an older normalizer's adjacency merges
// (keys recorded under it); or not at all (a restatement that closes
// each clause separately). This pass gives them one α-key: each clause
// takes its binders in the order of ONE canonical labeling of the
// distributed chain (the clauses with nothing bound: the block's free
// variables and a private copy of each clause's binders), a function
// of the block's α-class alone, and its r-th binder of type τ becomes
// the block's binder (τ, r). A clause with fewer
// binders of a type takes the first classes, so two binders of one type
// that NO clause mentions together are one binder; a binder no clause
// mentions vanishes; a binder two clauses rank apart is two binders.
// The proof distributes both the block and its canonical form into
// per-clause closures, sorts each closure to the prefix order, and
// equates the two α-equal chains. The sharing is the KEY's: a consumer
// that grounds a statement's own binders by position reads the install
// form, which keeps the statement's sharing (NormalizeKeepingSharing,
// prover/proof's NormalizedThm).
func canonicalQuantifierBlockRewrite(t Term) *PropWrapper {
	return canonicalQuantifierBlock(t, nil)
}

// canonicalQuantifierBlock is canonicalQuantifierBlockRewrite under the
// poll stop: the canonicalization of a block of many clauses is seconds
// (measured: 7 s on 186 clauses under 23 binders), so it polls inside
// (canonicalBlock).
func canonicalQuantifierBlock(t Term, stop stopper) *PropWrapper {
	for _, ops := range []*blockOps{&forAllBlockOps, &existsBlockOps} {
		vars, body := ops.decompose(t)
		if vars.Empty() {
			continue
		}
		if vars.Size() < 2 {
			return nil
		}
		components := ext.DecomposesBinaryOp(ops.dualMatcher)(body)
		if len(components) < 2 {
			return nil
		}
		return canonicalBlock(t, vars, body, components, ops, stop)
	}
	return nil
}

// canonicalBlock polls stop before each clause it keys and copies, before
// the labeling of the distributed chain, and inside each distribution
// (distributeBlock).
func canonicalBlock(
	t Term, vars VarList, body Term, components []Term, ops *blockOps, stop stopper,
) *PropWrapper {
	n := vars.Size()
	index := func(v VarTerm) int {
		for i := 0; i < n; i++ {
			if vars.Ind(i).EqualsVar(v) {
				return i
			}
		}
		panic("canonicalBlock: a clause mentions a variable the block does not bind")
	}
	var types []HolType
	typeIndex := func(ty HolType) int {
		if k := slices.IndexFunc(types, ty.Equals); k >= 0 {
			return k
		}
		types = append(types, ty)
		return len(types) - 1
	}
	// One canonical labeling of every variable of the distributed chain
	// — the block's free variables and, per clause, a private copy of
	// each binder the clause mentions: the chain with nothing bound,
	// whose α-class is the block's however the clauses share binders.
	// A tie in the labeling is an automorphism of that chain, and the
	// identifications its two branches give are one closed term up to
	// α; the input order breaks it — the free variables by name, the
	// clauses by AC-key and each clause's copies by the clause's own
	// labeling of its binders, orders the sort iteration does not move
	// — so the pass decides alike at every round.
	all := t.Frees(nil)
	slices.SortFunc(all, func(a, b VarTerm) int { return cmp.Compare(varID(a), varID(b)) })
	clauseKeys := make([]string, len(components))
	for j, c := range components {
		stop.before(cutBlockClause)
		clauseKeys[j] = openKey(c, nil).eval(nil)
	}
	clauseOrder := make([]int, len(components))
	for j := range clauseOrder {
		clauseOrder[j] = j
	}
	slices.SortStableFunc(clauseOrder, func(a, b int) int { return cmp.Compare(clauseKeys[a], clauseKeys[b]) })
	own := make([][]VarTerm, len(components))
	private := make([][]VarTerm, len(components))
	var flat Term
	for pos, j := range clauseOrder {
		stop.before(cutBlockClause)
		c := components[j]
		own[j] = canonicalBinderOrder(c.Frees(vars.Has), c)
		private[j] = make([]VarTerm, len(own[j]))
		substs := make([]TermSubst, len(own[j]))
		for i, v := range own[j] {
			name := core.TermName(fmt.Sprintf("%s%d_%d", privateBinderPrefix, pos, i))
			private[j][i] = core.Var(name, v.Type())
			substs[i] = core.MakeTermSubst(v, private[j][i])
		}
		all = append(all, private[j]...)
		clause := c.Substitute(substs...)
		if flat == nil {
			flat = clause
		} else {
			flat = Apply(ops.dualConst, flat, clause)
		}
	}
	stop.before(cutBlockLabeling)
	position := map[string]int{}
	for k, v := range canonicalBinderOrder(all, flat) {
		position[varID(v)] = k
	}
	// rank[j][i] is binder i's rank among the binders of its type that
	// clause j mentions — the labeling's order, counted within the clause
	// and the type — or -1 when j does not mention it; classes[k] is the
	// number of classes of the k-th type.
	rank := make([][]int, len(components))
	classes := map[int]int{}
	mentioned := make([]bool, n)
	for j := range components {
		rank[j] = make([]int, n)
		for i := range rank[j] {
			rank[j][i] = -1
		}
		idx := make([]int, len(own[j]))
		for i := range idx {
			idx[i] = i
		}
		slices.SortFunc(idx, func(a, b int) int {
			return cmp.Compare(position[varID(private[j][a])], position[varID(private[j][b])])
		})
		count := map[int]int{}
		for _, i := range idx {
			v := own[j][i]
			bi, k := index(v), typeIndex(v.Type())
			rank[j][bi] = count[k]
			count[k]++
			mentioned[bi] = true
			classes[k] = max(classes[k], count[k])
		}
	}
	// A class (τ, r) is represented by the first binder in prefix order
	// that some clause ranks r among its τ-binders and no class took
	// yet, else by a fresh variable. Classes are visited by type, then
	// rank, so the fresh names are deterministic.
	atRank := func(i, r int) bool {
		for j := range components {
			if rank[j][i] == r {
				return true
			}
		}
		return false
	}
	typeOrder := make([]int, len(types))
	for k := range typeOrder {
		typeOrder[k] = k
	}
	slices.SortFunc(typeOrder, func(a, b int) int { return HolType.Compare(types[a], types[b]) })
	reps := map[[2]int]VarTerm{}
	used := make([]bool, n)
	avoid := []Term{t}
	var freshReps []VarTerm
	for _, k := range typeOrder {
		for r := 0; r < classes[k]; r++ {
			var rep VarTerm
			for i := 0; i < n && rep.IsZero(); i++ {
				if !used[i] && vars.Ind(i).Type().Equals(types[k]) && atRank(i, r) {
					rep, used[i] = vars.Ind(i), true
				}
			}
			if rep.IsZero() {
				rep = core.Var("x", types[k]).RenameToAvoid(avoid...)
				avoid = append(avoid, rep)
				freshReps = append(freshReps, rep)
			}
			reps[[2]int{k, r}] = rep
		}
	}
	changed := false
	substs := make([][]TermSubst, len(components))
	for j := range components {
		for _, v := range own[j] {
			i := index(v)
			if rep := reps[[2]int{typeIndex(v.Type()), rank[j][i]}]; !rep.EqualsVar(v) {
				substs[j] = append(substs[j], core.MakeTermSubst(v, rep))
				changed = true
			}
		}
	}
	for i := 0; i < n; i++ {
		if !mentioned[i] {
			changed = true // vacuous: dropped
		}
	}
	if !changed {
		return nil
	}
	next := 0
	var rebuild func(u Term) Term
	rebuild = func(u Term) Term {
		if l, r, ok := ops.dualMatcher(u); ok {
			return Apply(ops.dualConst, rebuild(l), rebuild(r))
		}
		c, ss := components[next], substs[next]
		next++
		if len(ss) == 0 {
			return c
		}
		return c.Substitute(ss...)
	}
	canonical := rebuild(body)
	// The binders that represent a class keep their prefix order; the
	// fresh representatives follow. The block sort orders them after.
	var prefix []VarTerm
	for i := 0; i < n; i++ {
		if used[i] {
			prefix = append(prefix, vars.Ind(i))
		}
	}
	prefix = append(prefix, freshReps...)
	for _, v := range slices.Backward(prefix) {
		canonical = ops.quantify(v)(canonical)
	}
	if canonical.AlphaEquals(t) {
		return nil
	}
	w := distributeBlock(t, ops, stop)
	u := distributeBlock(canonical, ops, stop)
	if !Rhs(w).AlphaEquals(Rhs(u)) {
		panic(fmt.Sprintf("canonicalBlock: closures differ\n  t=%s\n  canonical=%s\n  dist(t)=%s\n  dist(canonical)=%s",
			ext.PrintTerm(t), ext.PrintTerm(canonical), ext.PrintTerm(Rhs(w)), ext.PrintTerm(Rhs(u))))
	}
	return w.EqTrans(u.EqSym())
}

// The units of work a cut of the normalization names (stopper.before):
// each reads after "cut off", as utils.Cut prints it.
const (
	cutStage             = "inside the pre-CNF normalization of the sequent, before a stage of it"
	cutHypothesis        = "inside the pre-CNF normalization of the sequent, before a hypothesis is simplified"
	cutSimplifyRewrite   = "inside the pre-CNF normalization of the sequent, before a rewrite of the chain that simplifies its disjunction"
	cutPrenexNode        = "inside the pre-CNF normalization of the sequent, at a node of the deep prenex walk"
	cutPreCNFPass        = "inside the pre-CNF normalization of the sequent, before a pass of its fixpoint"
	cutPreCNFRewrite     = "inside the pre-CNF normalization of the sequent, before a rewrite of a pass of its fixpoint"
	cutDisjunctStage     = "inside the pre-CNF normalization of the sequent, before a stage of its canonical disjunctive form"
	cutSort              = "inside the pre-CNF normalization of the sequent, before a sort of its canonical disjunctive form"
	cutBlockClause       = "inside the pre-CNF normalization of the sequent, before a clause of a quantifier block is labeled"
	cutBlockLabeling     = "inside the pre-CNF normalization of the sequent, before the labeling of a quantifier block's chain"
	cutBlockDistribution = "inside the pre-CNF normalization of the sequent, before a binder of a quantifier block is distributed over a clause"
)

// privateBinderPrefix heads the names of the per-clause copies of a
// block's binders in canonicalBlock's labeling; a NUL keeps them apart
// from every name a text can spell. They never enter a proof.
const privateBinderPrefix = "\x00p"

// distributeBlock proves ⊢ t = c₁ op … op cₖ for the block t = Q v̄.(chain):
// each clause closed over exactly the block binders it mentions, in the
// clause's own closure order, a vacuous binder dropped. Each binder is
// distributed over the whole chain, a step a clause, and stop is polled
// before each step.
func distributeBlock(t Term, ops *blockOps, stop stopper) *PropWrapper {
	vars, body := ops.decompose(t)
	heads := make([]Term, vars.Size())
	current := t
	for i := range heads {
		app := current.Core().(AppliedTerm)
		heads[i] = app.Fun()
		current = app.Arg().(AbsTerm).Body()
	}
	// distributeOne proves ⊢ Qv.u = u' for the chain u.
	var distributeOne func(v VarTerm, u Term) *PropWrapper
	distributeOne = func(v VarTerm, u Term) *PropWrapper {
		stop.before(cutBlockDistribution)
		if l, r, ok := ops.dualMatcher(u); ok {
			w := ops.distribute(Abs(v, l), Abs(v, r))
			wl, wr := distributeOne(v, l), distributeOne(v, r)
			return w.EqTrans(wl.LeftApply(ops.dualConst).Apply(wr))
		}
		if !u.HasFree(v) {
			return ops.moot(v, u)
		}
		return Refl(ops.quantify(v)(u))
	}
	// level(i) proves ⊢ Q vᵢ … vₙ₋₁.body = chainᵢ.
	var level func(i int) *PropWrapper
	level = func(i int) *PropWrapper {
		if i == vars.Size() {
			return Refl(body)
		}
		inner := level(i + 1)
		v := vars.Ind(i)
		return inner.Abs(v).LeftApply(heads[i]).
			EqTrans(distributeOne(v, Rhs(inner)))
	}
	w := level(0)
	sortClosure := func(closure Term) *PropWrapper {
		cVars, cBody := ops.decompose(closure)
		if cVars.Size() < 2 {
			return nil
		}
		sorted := cBody
		for _, v := range slices.Backward(closureOrder(cVars, cBody)) {
			sorted = ops.quantify(v)(sorted)
		}
		if sorted.AlphaEquals(closure) {
			return nil
		}
		return ops.reorder(closure, sorted.Core())
	}
	if u := rewriteChainLeaves(Rhs(w), ops.dualMatcher, ops.dualConst, sortClosure); u != nil {
		w = w.EqTrans(u)
	}
	return w
}

// rewriteChainLeaves lifts a rewrite of the chain's components to the
// chain; nil when no component rewrites.
func rewriteChainLeaves(
	u Term, matcher ext.BinaryOpMatcher, opConst ConstTerm, leaf Rewrite,
) *PropWrapper {
	l, r, ok := matcher(u)
	if !ok {
		return leaf(u)
	}
	wl := rewriteChainLeaves(l, matcher, opConst, leaf)
	wr := rewriteChainLeaves(r, matcher, opConst, leaf)
	switch {
	case wl != nil && wr != nil:
		return wl.LeftApply(opConst).Apply(wr)
	case wl != nil:
		return wl.LeftApply(opConst).RightApply(r)
	case wr != nil:
		return wr.LeftApply(u.Core().(AppliedTerm).Fun())
	}
	return nil
}

// deepCanonicalQuantifierBlockRewrite identifies every block's binders
// across its clauses. It walks maximal blocks: a clause's ranks read
// the block's other binders as binders, a suffix would read the peeled
// ones as free variables and could rank the rest apart.
var deepCanonicalQuantifierBlockRewrite = blockStructureRewrite(canonicalQuantifierBlockRewrite)

func assertNoReservedAbsNames(t Term) {
	if v := firstReservedAbsVar(t); !v.IsZero() {
		panic(fmt.Sprintf("reserved De Bruijn binder leak: %s in %s",
			v.Name(), ext.PrintTerm(t)))
	}
}

func firstReservedAbsVar(t Term) VarTerm {
	switch t := t.Core().(type) {
	case AppliedTerm:
		if v := firstReservedAbsVar(t.Fun()); !v.IsZero() {
			return v
		}
		return firstReservedAbsVar(t.Arg())
	case AbsTerm:
		if t.Var().DeBruijnIndex() > 0 {
			return t.Var()
		}
		return firstReservedAbsVar(t.Body())
	default:
		return VarTerm{}
	}
}

func restoreDisjunctDeBruijnVars(w *PropWrapper, vars VarList) *PropWrapper {
	// Inverse of the DeBruijn rename applied at the start of
	// DisjunctNormalizeRewrite: %i ↦ vars[i-1].
	//
	// DeBruijn rename assigns %i to the i-th binder of the original prefix
	// in outer-to-inner order (positional, 1-based). The sort that runs
	// between rename and restoration permutes the prefix in DeBruijn-name
	// space but does NOT touch the body's content — its semantics is
	// "reorder the outer ∀s while keeping the body fixed". For the
	// rename + sort + restore round-trip to be the literal inverse of the
	// rename (and thus preserve the body's content), restoration must map
	// %i back to vars[i-1] regardless of where %i ended up in the sorted
	// prefix.
	//
	// A type-grouped scheme — popping the front of varsMap[type] in the
	// sorted prefix's traversal order — is NOT the inverse of DeBruijn: it
	// re-assigns names to DeBruijn slots based on the sort's permutation,
	// silently swapping the semantic roles of same-type bound vars. The
	// resulting prop is α-equivalent to the input but syntactically
	// different. Re-applying DisjunctNormalize on that re-named form sees
	// a body with a permuted Frees walk, which drives the sort through a
	// different permutation, breaking idempotence (Bug B) and in some
	// configurations producing non-convergent cycles.
	deBruijnVars, _ := DecomposesFORALL(Rhs(w))
	if !deBruijnVars.Empty() {
		for _, v := range deBruijnVars.Backward() {
			idx := v.DeBruijnIndex()
			if idx < 1 || idx > vars.Size() {
				// DeBruijn(1 + vars.Size()) intentionally gives the
				// conversion window one spare slot beyond the original
				// prefix; a spare %-binder appearing in the top-level
				// ∀ chain has no corresponding original name. The cleanup
				// pass below gives it a fresh ordinary name instead of
				// leaking a reserved "%..." binder.
				continue
			}
			origVar := vars.Ind(idx - 1)
			Assert(origVar.Type().Equals(v.Type()))
			w = w.RewriteConclRhs(BoundVarRewrite(v, origVar))
		}
	}

	for {
		v := firstReservedAbsVar(Rhs(w))
		if v.IsZero() {
			break
		}
		w = w.RewriteConclRhs(BoundVarRewrite(v, core.Var("x", v.Type())))
	}
	assertNoReservedAbsNames(Rhs(w))
	return w
}

// disjunctSortStep is one round of the sorts; stop is polled before each
// of them.
func disjunctSortStep(w *PropWrapper, sortForAll bool, stop stopper) *PropWrapper {
	// Step 2a: Sort equality terms deeply throughout the expression.
	// This ensures a=b and b=a normalize to the same form.
	stop.before(cutSort)
	w = w.RewriteConclRhs(deepEqualitySortRewrite)

	// Step 2b: Sort disjunctive clauses deeply, including inside ∃ and
	// other binders that don't change body structure. Example:
	// (Q ∨ P) becomes (P ∨ Q) if P < Q; ∃a.(B(a) ∨ A(a)) becomes
	// ∃a.(A(a) ∨ B(a)).
	stop.before(cutSort)
	if u := deepDisjunctSortRewrite(Rhs(w)); u != nil {
		w = w.EqTrans(u)
		// After sorting, new simplifications may be possible.
		// Example: ∀x.(P(x) ∨ ¬P(x)) can now be recognized as ⊤.
		w = w.RewriteConclRhs(DeepBoolRewrite)
	}

	// Step 2c: Sort conjunctive clauses deeply, mirroring 2b. Sorting
	// inside ∃ puts `∃a. B(a) ∧ A(a)` and `∃a. A(a) ∧ B(a)` at one
	// key.
	stop.before(cutSort)
	if u := deepConjunctSortRewrite(Rhs(w)); u != nil {
		w = w.EqTrans(u)
		w = w.RewriteConclRhs(DeepBoolRewrite)
	}

	// Step 2d: Sort every quantifier block — the ∀ blocks under an ∃ and
	// the ∃ blocks — by type, then by occurrence in the (now sorted) body.
	// The outermost ∀ prefix is sorted by the same rule, so on it this
	// pass and step 3 agree; only the blocks below the prefix are new
	// here. Consistent with the body sort: CompareWithEnv ranks an outer
	// binder before an inner one, and quantifiersSort makes the first
	// occurring binder the outer one, so neither pass undoes the other.
	stop.before(cutSort)
	if u := deepQuantifierBlockSortRewrite(Rhs(w)); u != nil {
		w = w.EqTrans(u)
	}

	// Step 3: Sort quantifier variables by type for canonical ordering.
	// Variables of the same type are ordered by their occurrence in the body.
	if sortForAll {
		w = w.RewriteConclRhs(univQuantifiersSortRewrite)
	}
	return w
}

// Converts a term to canonical disjunctive normal form.
// This is the core canonicalization algorithm that ensures propositions with
// the same logical meaning have the same syntactic form.
//
// The algorithm repeatedly applies these transformations until convergence:
//  1. Rename universally quantified variables using De Bruijn indices
//     (removes dependency on variable names)
//  2. Sort equality terms (a=b becomes b=a if b<a) and disjunctive clauses
//  3. Sort every quantifier block's variables by type, then by occurrence order
//
// After convergence, variable names are restored from De Bruijn indices.
// If the algorithm doesn't converge (rare), it stops at the first repeated state.
//
// An equation between functions stays the equation: functional
// extensionality (FunEqRewrite) is a step of the pre-CNF pipeline
// (TrivialNormalize, forAllORSimplify, step0LocalRewrite), not of this
// canonical form. So at the clause layer `f = g` and its pointwise form
// `∀x. f(x) = g(x)` are two clauses with two keys: the FUNEXT rule
// (ext/clause/funext.go) derives the first from the second, and the
// refuter keeps a derived clause only under a key of its own.
//
// stop is polled before each stage of the form, before each round of the
// sorts and each sort of a round (disjunctSortStep), and inside the
// identification of each block's binders (canonicalBlock).
func disjunctNormalizeRewriteWith(identify bool, stop stopper) Rewrite {
	identifyBlocks := deepCanonicalQuantifierBlockRewrite
	if stop != nil {
		identifyBlocks = blockStructureRewrite(func(t Term) *PropWrapper {
			return canonicalQuantifierBlock(t, stop)
		})
	}
	return func(t Term) *PropWrapper {
		assertNoReservedAbsNames(t)
		stop.before(cutDisjunctStage)

		// Start with basic rewriting to get a clean starting point
		w := RewriteOrRefl(BasicRewritesWith(ImplyToOrRewrite), t)

		// Every block's clauses share binders by rank before the start
		// labeling reads the term: the labeling is a function of the term's
		// α-class, and the identification the prenex rules left is not
		// (canonicalQuantifierBlockRewrite). Once, here, and not in the
		// iteration below: the ranks read the block's free variables, and
		// under the De Bruijn names the iteration works in, two variables
		// the clauses cannot tell apart except together (f and g with x and
		// y) take the positions the start labeling's own tie-break gave
		// them, so an identification re-decided in the loop flipped with
		// every re-sort of the prefix (set_image.ImageCongruence's refute
		// prop never reached a fixed point). Decided here under the term's
		// own names, the identification breaks that symmetry, and the
		// labeling then has no tie to break.
		if identify {
			stop.before(cutDisjunctStage)
			if u := identifyBlocks(Rhs(w)); u != nil {
				w = w.EqTrans(u)
			}
		}

		// A canonical start for the sort iteration below (see quantifiersSort).
		stop.before(cutDisjunctStage)
		if u := canonicalBinderStartRewrite(Rhs(w)); u != nil {
			w = w.EqTrans(u)
		}

		vars, body := DecomposesFORALL(Rhs(w))
		Assert(vars.Empty() || vars.AllFreeIn(body))

		// Convert the original universal prefix to a De Bruijn working form once.
		// The normalization loop below stays in that working form; repeatedly
		// applying DeBruijn to an already-converted term can collide with the
		// temporary "%..." binders. We restore ordinary names exactly once after
		// the loop reaches a fixed point.
		if !vars.Empty() {
			_t := Rhs(w).DeBruijn(1 + vars.Size())
			if !_t.Equals(Rhs(w)) {
				w = w.EqTrans(Refl(_t))
			}
		}

		// Track all intermediate working forms to detect cycles.
		var appeared []Term
		for {
			before := Rhs(w)
			appeared = append(appeared, before)

			w = disjunctSortStep(w, !vars.Empty(), stop)

			// Check for convergence or cycle detection
			if before.AlphaEquals(Rhs(w)) ||
				utils.Any(appeared[:len(appeared)-1], Rhs(w).AlphaEquals) {
				break
			}
		}

		// Step 5: Restore original variable names from De Bruijn indices.
		// This ensures the output uses meaningful variable names while
		// maintaining the canonical structure achieved above

		// If there were no quantifiers, we're done
		if vars.Empty() {
			if !t.AlphaEquals(Rhs(w)) {
				return w
			}
			return nil
		}

		stop.before(cutDisjunctStage)
		w = restoreDisjunctDeBruijnVars(w, vars)
		w = disjunctSortStep(w, false, stop)
		assertNoReservedAbsNames(Rhs(w))

		// Return the normalized result if it differs from input
		if !t.AlphaEquals(Rhs(w)) {
			return w
		}
		return nil
	}
}

// DisjunctNormalizeRewrite is the canonical form: the clauses of every
// block share binders by rank (canonicalQuantifierBlockRewrite).
var DisjunctNormalizeRewrite = disjunctNormalizeRewriteWith(true, nil)

// disjunctNormalizeKeepingSharing is the same form with every block's
// binders shared as the input shares them — the install form of a
// dependency (prover/proof's NormalizedThm), which its consumers ground
// by the statement's own binders, in the statement's own roles.
var disjunctNormalizeKeepingSharing = disjunctNormalizeRewriteWith(false, nil)

var TrivialNormalize = BasicRewritesWith(
	UniqueRewrite,
	CondElimRewrite,
	CondSwapRewrite,
	FunEqRewrite,
	ImplyToOrRewrite,
	IffToOrRewrite,
	HilbertExistsRewrite)

// SkolemRewriteWorkflow is the refuter-only Skolemization stage of CNF
// preprocessing.
//
// In the prelude → middle → tail decomposition for CNF preprocessing:
//   - prelude:  PreCNFNormalize-equivalent work (statement identity / reusable);
//     see PreCNFNormalizeRewrite.
//   - middle:   SkolemRewriteWorkflow — refuter-only because Skolem symbols
//     change a prop's identity in a way that complicates equational
//     reasoning.
//   - tail:     distribute ∨ over ∧ + per-clause normalization (CNF refuter).
//
// SkolemRewriteWorkflow should not be applied to terms whose statement identity
// is being computed; use PreCNFNormalizeRewrite (which omits Skolem) for that.
//
// IndependentExistsPrenexRewrite runs ahead of SkolemRewrite at every
// node: an ∃ block rises above a ∀ block its part of the matrix never
// mentions, so its witnesses are Skolemized as constants, or as
// functions of the universals they depend on alone, and not of the
// whole prefix the prelude's ∀-outside-∃ convention put above them
// (independent_exists_prenex.go).
var SkolemRewriteWorkflow = BasicRewritesWith(
	IndependentExistsPrenexRewrite,
	SkolemRewrite,
	ExistentialPrenexRewrite)

// Handles unique quantifiers, function equality, implications, equivalences,
// and prepares for skolemization and prenex form conversion
var NormalizeRewriteWorkflow = ChainRewrites(
	TrivialNormalize,
	SkolemRewriteWorkflow,
	DeepUniversalPrenexRewrite,
)

var forAllORSimplify = ChainRewrites(
	BasicRewritesWith(
		FunEqRewrite,
		ImplyToOrRewrite,
		HilbertExistsRewrite),
	conditionalForAllORRewrite,
)

// conditionalForAllORRewrite is ForAllORRewrite gated on the follow-up
// SimplifyDisjunct / BasicRewrite actually producing a smaller term. Without
// the gate, ForAllORRewrite splits a separable ∀ onto a single disjunct (to
// expose α-equivalent merges or Bool-pattern collapses), and the chain's
// subsequent deep prenex pulls it right back out — a no-op net-of-permutation
// that drives the rewrite chain into a 2-cycle between the original prefix
// order and the post-split-permuted order on inputs where the narrow scope
// doesn't expose any simplification at all.
//
// Mathematically, ForAllORRewrite has a precondition: a follow-up rule must
// fire on the narrowed form. When that precondition fails, the rewrite isn't
// reducing toward canonical form — it's just permuting the prefix. The gate
// returns nil exactly when the precondition fails (no size reduction below
// the input), so the rest of the chain proceeds as if ForAllOR didn't fire
// and the prenex pull has nothing to undo. The two known callers that
// genuinely need the narrowing (α-equivalent ∀-disjunct merge, and the
// `∀p:Bool.¬p → ⊥` collapse via QuantifierRewrite) shrink the term, so the
// gate commits the rewrite for them.
func conditionalForAllORRewrite(t Term) *PropWrapper {
	splitTarget := forAllORRewriteTarget(t)
	if splitTarget == nil {
		return nil
	}

	var tail *PropWrapper
	fullTarget := splitTarget
	if u := SimplifyDisjunct(fullTarget); u != nil {
		tail = u
		fullTarget = Rhs(u)
	}
	if u := BasicRewrite(fullTarget); u != nil {
		if tail == nil {
			tail = u
		} else {
			tail = tail.EqTrans(u)
		}
		fullTarget = Rhs(u)
	}
	if fullTarget.Size() >= t.Size() {
		// Narrow scope didn't expose any reduction; the chain's trailing
		// prenex would just un-narrow this back. Revert.
		return nil
	}

	split := ForAllORRewrite(t)
	Assert(split != nil)
	if tail != nil {
		return split.EqTrans(tail)
	}
	return split
}

func forAllORRewriteTarget(t Term) Term {
	selectedVars, _, relevantTerm, restTerm, ok := forAllDisjunctiveGroupFirst(t)
	if !ok {
		return leftAssocOR(t)
	}

	relevantResult := relevantTerm
	for _, v := range selectedVars.Backward() {
		relevantResult = ForAll(v)(relevantResult)
	}

	vars, _ := DecomposesFORALL(t)
	restResult := restTerm
	for _, v := range vars.Backward() {
		if selectedVars.HasNo(v) {
			restResult = ForAll(v)(restResult)
		}
	}
	if u := forAllORRewriteTarget(restResult); u != nil {
		restResult = u
	}

	result := Or(relevantResult, restResult).Core()
	if u := leftAssocOR(result); u != nil {
		result = u
	}
	return result
}

func leftAssocOR(t Term) Term {
	components := DecomposesOR(t)
	if len(components) == 1 {
		return nil
	}
	target := Or(components...).Core()
	if target.AlphaEquals(t) {
		return nil
	}
	return target
}

// deepPrenexRewrite pulls both ∀ and ∃ across ∨/∧ at every position. The two
// kernel rewrites don't conflict (one matches `∀ over ∨/∧`, the other
// `∃ over ∨/∧`), and neither moves a quantifier across another quantifier of
// the opposite kind, so the relative ∀/∃ order is preserved. Bundling them
// in one DeepRewrite is what makes the statement-identity layer treat
// `(∃x.P(x)) ∨ Q` and `∃x.(P(x) ∨ Q)` (with x ∉ FV(Q)) as the same prop.
var deepPrenexRewrite = DeepRewrite(UniversalPrenexRewrite, ExistentialPrenexRewrite)

// disjunctConclSimplifyRewrite is intentionally not just "full prenex".
// The leading SimplifyDisjunct catches pre-NNF p∨¬p windows that are already
// visible after hyps have been moved into the conclusion, deepPrenexRewrite
// pulls safe ∀/∃ scopes, ForAllORRewrite briefly pushes separable ∀ groups
// back down so α-equivalent disjuncts can merge, and the final shallow
// prenex pass restores the pre-CNF boundary.
//
// The DeepUniversalPrenexRewrite pass before deepPrenexRewrite enforces a
// canonical ∀-outside-∃ convention. Without it, deepPrenexRewrite's outcome
// is path-dependent on which quantifier kind is exposed first at the
// outermost ∧/∨ boundary, so logically equivalent inputs with different
// surface shapes can converge to different (but each idempotent) fixpoints:
// e.g. `((∀x.A(x)) ∨ B) ∨ ¬(∀y.C(y))` post-NNF is
// `(∀x.A(x)) ∨ B ∨ ∃y.¬C(y)` where ∃ is exposed at the top OR but ∀ is one
// level deeper, so ExistentialPrenex fires first and locks ∃ outside ∀.
// Whereas `(∃y.¬C(y)) ∨ (∀x.A(x))` (same formula reached via a different
// path) has both at the same level and UniversalPrenex wins per rule order.
// Surfacing every safely-liftable ∀ first removes this dependence: when
// deepPrenex then fires for ∃, every ∀ is already above it.
var disjunctConclSimplifyRewrite = disjunctConclSimplifyUntil(nil)

// disjunctConclSimplifyUntil is disjunctConclSimplifyRewrite with stop
// polled before each rewrite of the chain and at each node of its deep
// prenex walk, the rewrite of the chain a wide disjunction is slow in.
func disjunctConclSimplifyUntil(stop stopper) Rewrite {
	prenex := deepPrenexRewrite
	if stop != nil {
		prenex = DeepRewrite(stop.node(cutPrenexNode), UniversalPrenexRewrite, ExistentialPrenexRewrite)
	}
	return chainRewritesUntil(stop, cutSimplifyRewrite,
		SimplifyDisjunct,
		BasicRewrite,
		DeepUniversalPrenexRewrite,
		prenex,
		conditionalForAllORRewrite,
		basicPrenexRewrite,
	)
}

// basicPrenexRewrite is the basic rewrites with both prenex rules, the
// pass that closes disjunctConclSimplifyRewrite.
var basicPrenexRewrite = BasicRewritesWith(UniversalPrenexRewrite, ExistentialPrenexRewrite)

// PreCNFNormalizeRewrite is the canonical pre-CNF normalization composition.
//
// Applied to a closed proposition, it brings the term to the pre-CNF
// invariant expected by Normalize's output:
//   - hypothesis-free / closed (assumed input)
//   - implication-free (⇒ rewritten to ¬∨)
//   - in negation normal form
//   - prenex where this can be done without Skolemization
//   - β/η reduced: a λ that is an application's argument or a λ's body
//     η-reduces (etaContextRewrite, outside ∀/∃/∃!/ε/=, whose normal
//     form is the expanded λ), so `g(λx. f(x))` and `g(f)` are one
//     normal form with one key; an equation between functions reads
//     through functional extensionality (FunEqRewrite)
//   - with deterministically ordered disjuncts/conjuncts and bound variables
//
// What it deliberately does NOT do, because those steps belong to the CNF
// refuter's tail and may blow up exponentially:
//   - Skolemize ∃ (introduces Skolem function symbols)
//   - distribute ∨ over ∧ (CNF construction)
//
// Idempotent on its own output. May return nil if the input is already in
// the pre-CNF normal form, in which case the caller should treat it as Refl.
//
// The chain `forAllORSimplify → disjunctConclSimplifyRewrite →
// DisjunctNormalizeRewrite` is not one-shot: one component's output can
// expose new rewrite sites for an earlier component. The canonical example
// is DisjunctNormalize's deep equality/conjunct sort canonicalizing
// `(∀x.A(x)) ⇔ (∀y.A(y))` so BoolRewrite then collapses it to ⊤, revealing
// a fresh ∀-prefix that DisjunctNormalize's initial DecomposesFORALL
// (which decided whether to sort the prefix) could not see. Iterating the
// chain to fixpoint is what makes it a genuine normalization.
var PreCNFNormalizeRewrite = preCNFNormalizeRewriteWith(DisjunctNormalizeRewrite)

// preCNFNormalizeKeepingSharing is PreCNFNormalizeRewrite with the
// blocks' binders shared as the input shares them.
var preCNFNormalizeKeepingSharing = preCNFNormalizeRewriteWith(disjunctNormalizeKeepingSharing)

func preCNFNormalizeRewriteWith(disjunctNormalize Rewrite) Rewrite {
	return preCNFNormalizeUntil(nil, disjunctConclSimplifyRewrite, disjunctNormalize)
}

// preCNFNormalizeUntil is the fixpoint of the chain over simplify and
// disjunctNormalize, the forms of disjunctConclSimplifyRewrite and
// DisjunctNormalizeRewrite built for stop; stop is polled before each
// pass of the fixpoint and before each rewrite of a pass.
func preCNFNormalizeUntil(stop stopper, simplify, disjunctNormalize Rewrite) Rewrite {
	return repeatRewriteToFixpointUntil(stop, chainRewritesUntil(stop, cutPreCNFRewrite,
		forAllORSimplify,
		simplify,
		disjunctNormalize,
	))
}

// repeatRewriteToFixpoint wraps a rewrite as its own fixpoint iteration.
// The result returns:
//   - nil  if the input is already at the rewrite's fixpoint (the rewrite
//     returns nil on the first call);
//   - the composed equality `t = t_fix` otherwise, where t_fix is the first
//     iterate that stops moving.
//
// "Stops moving" means either (a) the rewrite returns nil (no rule fires),
// or (b) the rewrite returns a non-nil proof but Rhs is α-equivalent to
// the previous Rhs — this happens when a ChainRewrites composition has an
// inner rewrite that fires while a later one reverts it, so the chain's
// net effect is a no-op proof.
//
// Cycle detection panics: with sound rewrites (each preserves α-equivalence
// class and is confluent on its own input), revisiting an earlier state is
// only possible when two rewrites in the chain oscillate against each
// other. That is a design bug — surfacing it via panic is preferable to
// silently picking one of the cycle states as canonical (which would be
// non-deterministic across α-equivalent inputs). The iteration count is
// implicitly bounded by the number of distinct reachable states from the
// input, a finite quantity for any fixed input.
func repeatRewriteToFixpoint(rewrite Rewrite) Rewrite {
	return repeatRewriteToFixpointUntil(nil, rewrite)
}

// repeatRewriteToFixpointUntil is repeatRewriteToFixpoint with stop
// polled before each pass.
func repeatRewriteToFixpointUntil(stop stopper, rewrite Rewrite) Rewrite {
	return func(t Term) *PropWrapper {
		var w *PropWrapper
		seen := []Term{t}
		for {
			stop.before(cutPreCNFPass)
			current := t
			if w != nil {
				current = Rhs(w)
			}
			u := rewrite(current)
			if u == nil {
				return w
			}
			next := Rhs(u)
			if next.AlphaEquals(current) {
				// α-equivalent no-op proof; treat as fixpoint.
				if w == nil {
					return u
				}
				return w.EqTrans(u)
			}
			for _, prior := range seen {
				if next.AlphaEquals(prior) {
					panic(fmt.Sprintf(
						"repeatRewriteToFixpoint: cycle detected\n  input: %s\n  cycle state: %s",
						ext.PrintTerm(t), ext.PrintTerm(next)))
				}
			}
			if w == nil {
				w = u
			} else {
				w = w.EqTrans(u)
			}
			seen = append(seen, next)
		}
	}
}

// PreCNFNormalizeTerm rewrites t at the term level to its pre-CNF normal
// form, returning ⊢ t = t_pre. It does not universally close free variables;
// ordinary simplifications may still remove free occurrences. If t is already
// in pre-CNF form, returns Refl(t).
//
// Term-level counterpart of Normalize(Prop). Used both by the CNF refuter's
// per-hyp prelude (via clause.preCNFNormalizeTerm with caching) and by the
// lemma matcher's witness-bridging path, where the kernel-level proof
// ⊢ t = t_pre is what lets normalized-but-not-raw matches be lifted back to
// kernel proofs about the original raw target.
func PreCNFNormalizeTerm(t Term) *PropWrapper {
	if w := PreCNFNormalizeRewrite(t); w != nil {
		return w
	}
	return Refl(t)
}

// PreCNFEqBridge returns ⊢ s = t when s and t share the same pre-CNF normal
// form (i.e., they are equivalent up to representation: ⇒ vs ¬∨, NNF, prenex
// order, disjunct/conjunct ordering, bound-variable renaming). Returns nil
// when their pre-CNF normal forms are not α-equal.
//
// Both s and t must have the same type. Typical use is on Bool-typed
// hyps/sub-terms in the lemma matcher to bridge "logically equal but
// syntactically different" forms without disturbing the statement-identity
// layer.
//
// Composes the term-level pre-CNF witness on each side with EqTrans:
// preS (⊢ s = s_pre) and preT.EqSym() (⊢ t_pre = t) chain through the shared
// α-equivalent pre-CNF representative — EqTrans is α-aware, so the
// composition is sound even if s_pre and t_pre differ in bound-var names.
func PreCNFEqBridge(s, t Term) *PropWrapper {
	if s.AlphaEquals(t) {
		return Refl(s)
	}
	preS := PreCNFNormalizeTerm(s)
	preT := PreCNFNormalizeTerm(t)
	if !Rhs(preS).AlphaEquals(Rhs(preT)) {
		return nil
	}
	return preS.EqTrans(preT.EqSym())
}

// SkolemNormalizeTerm rewrites t to its normal form read through the
// Skolem stage, returning ⊢ t = t_sk: NormalizeRewriteWorkflow — in which
// `∀x̄. ∃y. P` becomes `∃ƒ. ∀x̄. P[ƒ(x̄)]`, the function a bound variable,
// so no symbol is minted and the statement's identity is not disturbed —
// then the pre-CNF form of that. The order matters: ƒ takes x̄ in the
// order t binds them, which is the order a statement of the choice
// function writes its arguments in, and the pre-CNF form reorders a
// ∀-block to its canonical order, so it comes after the function has its
// arguments. Refl(t) where nothing moves.
func SkolemNormalizeTerm(t Term) *PropWrapper {
	w := NormalizeRewriteWorkflow(t)
	if w == nil {
		w = Refl(t)
	}
	if canonical := PreCNFNormalizeRewrite(Rhs(w)); canonical != nil {
		w = w.EqTrans(canonical)
	}
	return w
}

// SkolemEqBridge is PreCNFEqBridge one stage further: ⊢ s = t when s and
// t share one normal form through the Skolem stage (SkolemNormalizeTerm),
// nil when they do not. It is what identifies a fact `∀x̄. ∃y. P` with the
// statement of its choice function, `∃f. ∀x̄. P[f(x̄)]`: the stage gives the
// first the form of the second. A refutation does not meet that identity
// — it reads the second NEGATED, where f is a universal variable and the
// x̄ are Skolem functions of it, and has to find f by higher-order
// unification.
func SkolemEqBridge(s, t Term) *PropWrapper {
	if s.AlphaEquals(t) {
		return Refl(s)
	}
	normS := SkolemNormalizeTerm(s)
	normT := SkolemNormalizeTerm(t)
	if !Rhs(normS).AlphaEquals(Rhs(normT)) {
		return nil
	}
	return normS.EqTrans(normT.EqSym())
}

// TermNormalize is the term-level component of Normalize: it closes free
// variables in t under ∀, then applies the pre-CNF rewrite to canonical form
// followed by an iterative vacuous-quantifier elimination pass.
//
// Returns:
//   - the normalized term (closed and canonical)
//   - the equality proof ⊢ closed = normalized, where
//     closed = ∀ FV(t). t  (universally close every free variable in input order)
//
// The equality is from the *closed* form, not from the original t — closure is
// not an equality (`P(x)` ≠ `∀x.P(x)`). Callers that need to reconstruct from
// normalized back to t must compose this equality with a separate
// ConclForAllInst pass over the FVs they recorded before calling.
//
// Used internally by Normalize(Prop) for Steps 2-4. External callers (e.g. lemma
// matchers needing a key for representation-equivalence) can use:
//
//	n, _ := TermNormalize(t)
//	key := n.AlphaKey()  // type TermKey — clean type, no Prop wrapping
func TermNormalize(t Term) (Term, *PropWrapper) {
	return termNormalizeWith(t, PreCNFNormalizeRewrite)
}

func termNormalizeWith(t Term, preCNF Rewrite) (Term, *PropWrapper) {
	// Close free variables under ∀ in the order Frees returns them.
	closed := t
	for _, v := range t.Frees(nil) {
		closed = ForAll(v)(closed)
	}
	// The pre-CNF rewrite is itself fixpoint-iterated (see its definition);
	// one call is enough.
	if w := preCNF(closed); w != nil {
		return Rhs(w), w
	}
	return closed, Refl(closed)
}

// Normalize converts a proposition to its canonical normal form.
//
// Equivalent to (*PreCNFCache)(nil).Normalize(p). Use the receiver form on
// a shared *PreCNFCache when the same prop (or α-equivalent props) may be
// normalized more than once — the cache keys on input AlphaKey and returns
// the same normalized Prop in O(1) on repeat calls.
func Normalize(p Prop) (Prop, utils.EndoFunc[Prop]) {
	return (*PreCNFCache)(nil).Normalize(p)
}

// Normalize converts a proposition to its canonical normal form.
//
// First-principles framing: a `Prop` `Γ ⊢ φ` is, in clausal form, the
// disjunction `¬h1 ∨ … ∨ ¬hn ∨ φ`. Hypotheses and conclusion are the same
// kind of object modulo polarity, and the canonical form is a property of
// the whole clause (post-Move disjunction), not of any individual literal.
// So per-literal work BEFORE MoveHypsToConcl must stay polarity-symmetric:
// at fixpoint, the rewrite applied to `h` and then negated by Move must
// reach a form that the post-Move pipeline canonicalizes the same way as
// if we had kept `h` un-rewritten and let Move + post-Move handle
// everything.
//
// The normalization process is:
//
//	0a. ∀-close free variables that appear only in the conclusion.
//	0b. Apply local, polarity-symmetric simplifications to the conclusion
//	    (β/η, NNF, bool, ⇒→¬∨, funext (λx.l)=(λx.r) ⇔ ∀x.(l=r)). Same
//	    rewrite chain step 0c applies per-hyp; surfacing the funext ∀
//	    pre-Move is what keeps `(λn.φ) = (λn.⊤)` shapes from desyncing
//	    against their `∀n.φ` peers in the post-Move prenex pass.
//	0c. For each hyp: ∃-close hyp-only free variables, then apply the same
//	    local, polarity-symmetric rewrite chain (β/η, NNF, bool, ⇒→¬∨).
//	    DO NOT run prenex/anti-prenex rewrites in 0b or 0c: any rewrite
//	    that changes quantifier scope relative to ∧/∨ commits before Move
//	    has fixed the literal's final polarity. See normalizeHypotheses
//	    for the rationale.
//	1a. MoveHypsToConcl: Γ ⊢ φ becomes ⊢ φ ∨ ¬h1 ∨ ... ∨ ¬hn.
//	1b. disjunctConclSimplifyRewrite on the merged disjunction. The pre-NNF
//	    SimplifyDisjunct catches visible `p ∨ ¬p` windows; the post-
//	    (NNF + ForAllOR) SimplifyDisjunct dedupes α-equivalent ∀-disjuncts
//	    that came from different hyps.
//	2-4. ∀-close any remaining free variables, then TermNormalize:
//	    unconditional PreCNFNormalize plus an iterative vacuous-quantifier
//	    elimination pass with a size-monotone guard. Inside it,
//	    DisjunctNormalize has every binder block's clauses share binders
//	    by rank (canonicalQuantifierBlockRewrite) and sorts every block,
//	    so neither the input's ∧/∨ association, nor its premises' order,
//	    nor the order the prenex rules pulled binders in reaches the key.
//	    Note the closure in
//	    step 0a/2 makes free variables binders too: two free variables of
//	    one type in separate conjuncts are one binder of the key.
//
// Returns the normalized proposition and a reconstruction function that
// lifts a proof of the normalized form back to the original.
//
// On a non-nil receiver, the result Prop is keyed on input AlphaKey and
// cached for the cache's lifetime. The accompanying reconstruct callback
// is lazy: on a cache hit, it is a closure that re-runs the full pipeline
// only if the caller actually invokes it. Callers that discard the
// reconstruct (the vast majority) get O(1) repeat lookups; callers that
// use it (the session's `known` and auto-match closes) pay the same cost
// they would without the cache. A caller that will need the reconstruct
// of a prop it normalizes keeps the one its own run returned: the
// refuter does, for its refute prop (refuter's KeyForm).
func (c *PreCNFCache) Normalize(p Prop) (Prop, utils.EndoFunc[Prop]) {
	return c.normalize(p, nil)
}

// NormalizeUntil is Normalize cut off by ctx. The normalization of a wide
// sequent is a run of seconds that grows faster than the square of its
// hypotheses (measured on one shape: 1.6 s at 166, 7.9 s at 316), so
// the run polls ctx inside: before each stage, each hypothesis, each
// rewrite of its chains, each pass of its fixpoint and each sort of its
// canonical form, and inside two rewrites a wide disjunction is slow in,
// at each node of the deep prenex walk and before each step of a block's
// distribution. Elsewhere one rewrite or one sort is the unit a cut
// waits for; the longest measured is the sort of a disjunction, which
// compares its clauses pairwise, 0.6 to 0.8 s at 316 clauses. A done
// context raises a utils.Cut at a poll: nothing is returned and nothing
// is cached. Under a context that is never done it is Normalize, and
// under any context it returns what Normalize returns.
func (c *PreCNFCache) NormalizeUntil(ctx context.Context, p Prop) (Prop, utils.EndoFunc[Prop]) {
	return c.normalize(p, utils.Stopper(ctx))
}

func (c *PreCNFCache) normalize(p Prop, stop stopper) (Prop, utils.EndoFunc[Prop]) {
	// Only cache UNPROVED props. Normalize preserves the proved bit
	// (kernel ops in the pipeline lift Thm through unchanged), so a
	// cache that ignored provedness could return an unproved Prop where
	// the caller's input was proved — silently losing the kernel
	// witness and breaking downstream code that does `result.AsThm()`.
	// Proved inputs run uncached; they are also the rare path (key
	// lookups, refute prop construction, agent goals are all unproved).
	if c == nil || p.Proved() {
		return normalizeUncachedWith(p, canonicalRewrites(stop))
	}
	if cached, ok := c.propCache.Load(p.AlphaKey()); ok {
		// Lazy reconstruct: if a caller actually invokes the lift, re-run
		// the uncached pipeline against p. The cached Prop is α-equivalent
		// to whatever the uncached run would produce, and the reconstruct
		// closures' captured kernel witnesses are α-aware, so the lift
		// composes soundly with the cached prop as well.
		return cached, func(arg Prop) Prop {
			_, real := normalizeUncached(p)
			return real(arg)
		}
	}
	norm, recon := normalizeUncachedWith(p, canonicalRewrites(stop))
	if !norm.Proved() {
		// Defensive: don't cache if normalize accidentally lifted the
		// input to a proved form (shouldn't happen — the pipeline is
		// witness-preserving — but a future change could violate this
		// and we don't want to poison the cache).
		c.propCache.Store(p.AlphaKey(), norm)
	}
	return norm, recon
}

// BridgeNormalize lifts `b` to a Prop in `a`'s α-form when the two share
// the same pre-CNF normal form, by co-running the Normalize pipeline on
// both inputs and stopping at the first step where their running forms
// α-coincide. Returns nil when the pipeline runs to completion without
// convergence — they are NOT normalize-equivalent.
//
// Soundness: at any step k where a_k.AlphaEquals(b_k), b_k is a
// kernel-derived Prop (each pipeline step is witness-preserving — kernel
// rules + ConclForAll + EqMP + DeriveHypFrom, all α-aware). Applying a's
// length-k reverse reconstruct chain to b_k yields a Prop in a's α-form
// whose proved/unproved status matches b. The reconstruct closures
// captured during a's run reference α-classes, so composition through
// b's specific α-form at step k is sound.
//
// When to use over `Normalize(a)` + `Normalize(b)` + manual reconstruct:
//   - both sides will be freshly normalized (no cache hit on either),
//     because BridgeNormalize does no cache lookup. With one cached side
//     the joint run does redundant pipeline work; with both cached the
//     redundancy is total.
//   - caller has a proved Prop `b` and wants a proved Prop in `a`'s form.
//     `Thm` inputs are never cached by *PreCNFCache (proved inputs skip
//     the cache by design), so any bridge with a Thm source falls into
//     the "no cache hit on that side" category automatically.
//
// Early returns:
//   - a.AlphaEquals(b) → b directly (no pipeline work needed).
//   - pipeline finishes without α-coincidence → nil.
func BridgeNormalize(a, b Prop) Prop {
	assertNoReservedAbsNames(a.Conclusion())
	for h := range a.HypIter() {
		assertNoReservedAbsNames(h)
	}
	assertNoReservedAbsNames(b.Conclusion())
	for h := range b.HypIter() {
		assertNoReservedAbsNames(h)
	}

	if a.AlphaEquals(b) {
		return b
	}

	var aRecons []utils.EndoFunc[Prop]
	// bScratch is a throwaway: pipeline steps expect a non-nil
	// reconstructs slice to append to, but b's reverse chain is never
	// invoked — the joint convergence test is precisely what makes b's
	// chain unnecessary (b_k is materialized directly by the forward
	// run, and a's reverse chain is what we need to land in a's α-form).
	var bScratch []utils.EndoFunc[Prop]

	aw, bw := WrapProp(a), WrapProp(b)

	aw = closeConclusionOnlyFreeVars(aw, a, &aRecons)
	bw = closeConclusionOnlyFreeVars(bw, b, &bScratch)
	if aw.AlphaEquals(bw) {
		return utils.RevChainFunc(aRecons)(bw)
	}

	aw = normalizeConclusionLocally(aw, &aRecons)
	bw = normalizeConclusionLocally(bw, &bScratch)
	if aw.AlphaEquals(bw) {
		return utils.RevChainFunc(aRecons)(bw)
	}

	aw = normalizeHypotheses(aw, &aRecons, nil)
	bw = normalizeHypotheses(bw, &bScratch, nil)
	if aw.AlphaEquals(bw) {
		return utils.RevChainFunc(aRecons)(bw)
	}

	aw = moveHypsToConcl(aw, &aRecons)
	bw = moveHypsToConcl(bw, &bScratch)
	if aw.AlphaEquals(bw) {
		return utils.RevChainFunc(aRecons)(bw)
	}

	aw = simplifyMovedConclusion(aw, &aRecons, disjunctConclSimplifyRewrite)
	bw = simplifyMovedConclusion(bw, &bScratch, disjunctConclSimplifyRewrite)
	if aw.AlphaEquals(bw) {
		return utils.RevChainFunc(aRecons)(bw)
	}

	aFinal := finalizeNormalizedConclusion(aw, &aRecons)
	bFinal := finalizeNormalizedConclusion(bw, &bScratch)
	if aFinal.AlphaEquals(bFinal) {
		return utils.RevChainFunc(aRecons)(bFinal)
	}

	return nil
}

// normalizeUncached is the full prop-level pre-CNF pipeline without any
// cache lookup or store. Extracted from (*PreCNFCache).Normalize so cache
// hits can lazily replay it when (and only when) a caller invokes the
// reconstruct callback.
func normalizeUncached(p Prop) (Prop, utils.EndoFunc[Prop]) {
	return normalizeUncachedWith(p, canonicalRewrites(nil))
}

// normalizeRewrites is what one run of the prop-level pipeline rewrites
// with once the hypotheses are in the conclusion, and the poll of the
// run: simplify is disjunctConclSimplifyRewrite and preCNF the pre-CNF
// fixpoint, each as built for stop.
type normalizeRewrites struct {
	stop     stopper
	simplify Rewrite
	preCNF   Rewrite
}

// canonicalRewrites is the rewrites of the canonical form under the poll
// stop: the package's own where stop is nil, and the same compositions
// built with stop inside where a run can be cut.
func canonicalRewrites(stop stopper) normalizeRewrites {
	if stop == nil {
		return normalizeRewrites{simplify: disjunctConclSimplifyRewrite, preCNF: PreCNFNormalizeRewrite}
	}
	simplify := disjunctConclSimplifyUntil(stop)
	return normalizeRewrites{
		stop:     stop,
		simplify: simplify,
		preCNF:   preCNFNormalizeUntil(stop, simplify, disjunctNormalizeRewriteWith(true, stop)),
	}
}

// NormalizeKeepingSharing is Normalize with every block's binders
// shared as p shares them. It is the install form of a dependency
// (prover/proof's NormalizedThm): a consumer that grounds the
// statement's own binders by position reads each clause in the roles
// the statement gave them, while the canonical form, which may share a
// clause's binders otherwise, is the key and nothing more. Uncached.
func NormalizeKeepingSharing(p Prop) (Prop, utils.EndoFunc[Prop]) {
	return normalizeUncachedWith(p, normalizeRewrites{
		simplify: disjunctConclSimplifyRewrite, preCNF: preCNFNormalizeKeepingSharing})
}

func normalizeUncachedWith(p Prop, rewrites normalizeRewrites) (Prop, utils.EndoFunc[Prop]) {
	stop, preCNF := rewrites.stop, rewrites.preCNF
	assertNoReservedAbsNames(p.Conclusion())
	for h := range p.HypIter() {
		assertNoReservedAbsNames(h)
	}

	// Fast path: if the input is closed, hypothesis-free, and already at the
	// pre-CNF normal-form fixed point, return it as-is.
	if p.NumHyps() == 0 && p.Conclusion().AllFree(utils.EmptyPredicate) {
		if preCNF(p.Conclusion()) == nil {
			return p, func(p Prop) Prop { return p }
		}
	}

	var reconstructs []utils.EndoFunc[Prop]

	step0 := WrapProp(p)
	step0 = closeConclusionOnlyFreeVars(step0, p, &reconstructs)
	stop.before(cutStage)
	step0 = normalizeConclusionLocally(step0, &reconstructs)
	step0 = normalizeHypotheses(step0, &reconstructs, stop)

	stop.before(cutStage)
	step1 := moveHypsToConcl(step0, &reconstructs)
	stop.before(cutStage)
	step1 = simplifyMovedConclusion(step1, &reconstructs, rewrites.simplify)
	stop.before(cutStage)
	normalizedProp := finalizeNormalizedConclusionWith(step1, &reconstructs, preCNF)

	return normalizedProp, utils.RevChainFunc(reconstructs)
}

func closeConclusionOnlyFreeVars(
	step0 *PropWrapper,
	original Prop,
	reconstructs *[]utils.EndoFunc[Prop],
) *PropWrapper {
	for _, v := range step0.Conclusion().Frees(func(v core.VarTerm) bool {
		return NotFreeInHyps(original, v)
	}) {
		step0 = step0.ConclForAll(v)
		reconstruct := func(p Prop) Prop { return WrapProp(p).ConclForAllInst(v) }
		*reconstructs = append(*reconstructs, reconstruct)
	}
	return step0
}

func normalizeConclusionLocally(
	step0 *PropWrapper,
	reconstructs *[]utils.EndoFunc[Prop],
) *PropWrapper {
	// Step 0b: apply the same polarity-symmetric local simplifications to
	// the conclusion that step 0c (normalizeHypotheses) applies per-hyp.
	// This includes ⇔/= bool-eq collapse (via BasicRewrite), ⇒→¬∨ (via
	// ImplyToOrRewrite), and crucially funext expansion
	//   (λx.l) = (λx.r) ⇔ ∀x.(l = r)
	// via FunEqRewrite.
	//
	// Without this step, a conclusion like `(λn.P(n)) = (λn.⊤)` survives
	// step 1a Move with its `=` intact; the ¬-flip in NNF then exposes an
	// ∃ at the top OR before the funext ∀ is uncovered, and post-Move
	// prenex commits to a wrong prefix order (∀∃∀). Funext-expanding
	// pre-Move puts the conclusion's ∀ on the same footing as any other
	// concl ∀.
	//
	// Symmetric concl-side analog of step 0c's per-hyp call to
	// step0LocalRewrite. Like step 0c, it intentionally excludes
	// prenex/anti-prenex movement.
	if u := step0LocalRewrite(step0.Conclusion()); u != nil {
		step0 = u.EqMP(step0)
		reconstruct := func(p Prop) Prop { return u.EqSym().EqMP(p) }
		*reconstructs = append(*reconstructs, reconstruct)
	}
	return step0
}

func normalizeHypotheses(
	step0 *PropWrapper,
	reconstructs *[]utils.EndoFunc[Prop],
	stop stopper,
) *PropWrapper {
	// Step 0c: ∃-close hyp-only free variables, then apply only local,
	// polarity-symmetric simplifications to each hyp.
	//
	// Why this is intentionally weak — and especially why we DO NOT run
	// PreCNFNormalize per-hyp here:
	//
	// A prop `Γ ⊢ φ` is, semantically, the clause `¬h1 ∨ … ∨ ¬hn ∨ φ`.
	// Hyps and conclusion are the same kind of object modulo polarity. The
	// canonical form is a property of the whole clause (post-Move
	// disjunction), not of any individual literal. So per-hyp work must
	// stay polarity-symmetric: at fixpoint, the rewrite applied to `h` and
	// then negated by MoveHypsToConcl must reach a form post-Move
	// PreCNFNormalize converges to the same canonical shape as if we had
	// kept `h` un-rewritten and let Move + post-Move handle everything.
	//
	// PreCNFNormalize is forward-canonical (∀ outside, ∃ inside, prenex
	// pulled). Negating a pre-CNF form yields the dual `∃ outside, ∀
	// inside` shape, which is NOT in pre-CNF form for the negation, and
	// post-Move PreCNFNormalize cannot fix it without an unsound general
	// ∀-∃ swap. So `Γ, h ⊢ φ` and its contrapositive `Γ, ¬φ ⊢ ¬h` end up
	// at different syntactic shapes despite being the same clause.
	//
	// Step 1b (disjunctConclSimplifyRewrite) and Steps 2-4 (TermNormalize)
	// run on the closed disjunction post-Move where every literal is
	// treated uniformly. That's where all prenex/anti-prenex movement, deep
	// sort, and the rest of the structural canonicalization belong.
	//
	// Iterating via HypIter is required because step0 is mutated in the body.
	for h := range step0.HypIter() {
		// An earlier iteration's mutation may have merged this hyp away:
		// HypExists's TermInst substitutes v := εv.h' into hyp h', and when
		// a SIBLING hyp is exactly h'[v := εv.h'] (α-equal — the Select-
		// property instance of the same predicate, e.g. an AutoDenote
		// abbreviation hyp Φ(α) next to its ε-expansion Φ(εy.Φ(y))), the
		// substituted hyp α-collides with the sibling and the sorted hyp
		// set dedups them; the subsequent SelectExists discharge then
		// removes the merged hyp entirely. The iterator snapshot still
		// yields the absorbed hyp, but there is nothing left to normalize
		// for it — its surviving representative is processed in its own
		// iteration. (The reconstruct side already tolerates this via
		// MaybeDeriveTrans; the forward path must skip too.)
		if !step0.HasHyp(h) {
			continue
		}
		stop.before(cutHypothesis)
		for _, v := range h.Frees(func(v core.VarTerm) bool {
			// Hyp-only: not free in conclusion, not free in any other hyp.
			// ∃-closing here is polarity-symmetric: ¬∃x.h = ∀x.¬h, so the
			// post-Move disjunction sees the same closure regardless of
			// whether we apply it positively here or wait for ∀-closure to
			// pick it up after Move.
			return !step0.Conclusion().HasFree(v) && NotFreeInHyps(step0, v, h)
		}) {
			step0, h = step0.HypExists(v, h), ext.Exists(v)(h)
			reconstruct := InstExists(h, v).MaybeDeriveTrans
			*reconstructs = append(*reconstructs, reconstruct)
		}
		if u := step0LocalRewrite(h); u != nil {
			step0 = u.RightAssume().DeriveTrans(step0)
			reconstruct := u.LeftAssume().MaybeDeriveTrans
			*reconstructs = append(*reconstructs, reconstruct)
		}
	}
	return step0
}

// step0LocalRewrite is the per-component local simplification applied before
// MoveHypsToConcl. It runs on each hypothesis (step 0c) and on the conclusion
// (step 0b) — the two are symmetric components of the same clause modulo
// polarity, so they share the same rewrite chain.
//
// It intentionally excludes every prenex/anti-prenex rewrite
// (`ForAllORRewrite`, `ExistsORRewrite`, `ForAllANDRewrite`,
// `ExistsANDRewrite`, Universal/ExistentialPrenexRewrite): the final polarity
// of a hyp is negative, so scope movement before Move can commit to the wrong
// quantifier order. The post-Move pipeline sees the whole closed disjunction
// and is the single place where structural canonicalization is allowed.
//
// FunEqRewrite is essential on the concl side: a concl shape like
// `(λn.P(n)) = (λn.⊤)` must be funext-expanded to `∀n.(P(n)=⊤)` (which
// BasicRewrite then collapses to `∀n.P(n)`) BEFORE Move. Otherwise the
// resulting ∀n only surfaces after step 1b's BasicRewrite at step 5, by
// which time the ∃ flipped out of `¬(∀n.…)` on the hyp side has already
// been pulled outside the OR — locking the prefix into ∀∃∀ instead of the
// canonical ∀∀∃.
var step0LocalRewrite = ChainRewrites(
	BasicRewritesWith(
		FunEqRewrite,
		ImplyToOrRewrite,
		HilbertExistsRewrite))

func moveHypsToConcl(
	step0 *PropWrapper,
	reconstructs *[]utils.EndoFunc[Prop],
) *PropWrapper {
	// Step 1a: MoveHypsToConcl. h1, ..., hn ⊢ φ becomes ⊢ φ ∨ ¬h1 ∨ ... ∨ ¬hn.
	step1 := step0.MoveHypsToConcl(nil)
	reconstruct := func(p Prop) Prop {
		if step0.NumHyps() == 0 {
			Assert(p.AlphaEquals(step0))
			return p
		}
		// Iteratively extract each appended ¬h disjunct back into a
		// hypothesis, RIGHTMOST-first — the exact inverse of MoveHypsToConcl,
		// which appends each ¬hi as the rightmost disjunct. Peeling
		// positionally (not by searching for a ¬h that α-matches a hyp) is
		// load-bearing: when a hyp h has ¬h ALSO present as a disjunct of the
		// original conclusion φ, a search-based peel can remove φ's own ¬h
		// instead of the appended one, corrupting the reconstruction (it then
		// strands a positive disjunct that MatchesNOT can't decode and the
		// loop panics). The loop stops the moment the conclusion α-equals
		// step0's, so φ's own trailing disjuncts are never touched.
		for !p.Conclusion().AlphaEquals(step0.Conclusion()) {
			_, nh, ok := ext.MatchesOR(p.Conclusion())
			if !ok {
				// Conclusion collapsed to a single ¬h (implies ⊥).
				Assert(step0.Conclusion().Equals(F))
				h := ext.MatchesNOT(p.Conclusion())
				Assert(h != nil && step0.HasHyp(h))
				return Contradict(h).DeriveHypFrom(p)
			}
			h := ext.MatchesNOT(nh)
			Assert(h != nil && step0.HasHyp(h))
			p = WrapProp(p).MoveConclLastDisjComponentToHyp()
		}
		Assert(p.AlphaEquals(step0))
		return p
	}
	*reconstructs = append(*reconstructs, reconstruct)
	return step1
}

func simplifyMovedConclusion(
	step1 *PropWrapper,
	reconstructs *[]utils.EndoFunc[Prop],
	simplify Rewrite,
) *PropWrapper {
	// Step 1b: disjunctConclSimplifyRewrite on the merged conclusion. Two
	// distinct simplifications fire here that the post-MoveHypsToConcl term
	// can't get any other way:
	//
	//   - Pre-NNF SimplifyDisjunct catches `∀y.R(y) ∨ ¬(∀y.R(y))` → ⊤. This
	//     pattern only exists in the brief window after MoveHypsToConcl and
	//     before BasicRewrite's NNF push (which turns ¬(∀y.R(y)) into
	//     ∃y.¬R(y), losing the structural p / ¬p shape).
	//   - Post-(NNF + DeepUnivPrenex + ForAllOR-distribute) SimplifyDisjunct
	//     catches α-equivalent ∀-disjuncts originating from different
	//     hyps — e.g., ∀x.¬R(x) (from hyp h1) and ∀y.¬R(y) (from hyp h2)
	//     dedup to a single disjunct.
	//
	// TermNormalize's later PreCNFNormalize starts with forAllORSimplify,
	// which NNF-pushes before any SimplifyDisjunct, so it cannot recover the
	// first pattern. Skipping Step 1b leaves both the case-1 (`p ∨ ¬p`) and
	// case-2 (α-equivalent merge) outputs un-simplified.
	//
	// The reconstruct here runs in reverse order (RevChainFunc) before the
	// MoveHypsToConcl reconstruct above, so the latter sees the
	// pre-simplification disjunct shape.
	if u := simplify(step1.Conclusion()); u != nil {
		step1 = u.EqMP(step1)
		reconstruct := func(p Prop) Prop { return u.EqSym().EqMP(p) }
		*reconstructs = append(*reconstructs, reconstruct)
	}
	return step1
}

func finalizeNormalizedConclusion(
	step1 *PropWrapper,
	reconstructs *[]utils.EndoFunc[Prop],
) Prop {
	return finalizeNormalizedConclusionWith(step1, reconstructs, PreCNFNormalizeRewrite)
}

func finalizeNormalizedConclusionWith(
	step1 *PropWrapper,
	reconstructs *[]utils.EndoFunc[Prop],
	preCNF Rewrite,
) Prop {
	// Steps 2-4: ∀-close remaining free variables, then run TermNormalize
	// on the closed conclusion (PreCNFNormalize + vacuous-quantifier elim
	// loop). DisjunctNormalize inside TermNormalize sorts disjuncts/conjuncts
	// and DeBruijn-renames bound variables to canonical form.
	step2 := ForAllConclFreeVars(step1)
	closedFVs := step1.Conclusion().Frees(nil) // captured for reconstruct
	_, eq := termNormalizeWith(step1.Conclusion(), preCNF)
	// eq: ⊢ closed = final, where closed is α-equal to step2.Conclusion().
	normalizedProp := eq.EqMP(step2)

	reconstruct := func(p Prop) Prop {
		// Reverse the rewrite: ⊢ final → ⊢ closed.
		p = eq.EqSym().EqMP(p)
		// Reverse the FV closure: ConclForAllInst each var in reverse order.
		_p := WrapProp(p)
		for _, v := range slices.Backward(closedFVs) {
			_p = _p.ConclForAllInst(v)
		}
		return _p
	}
	*reconstructs = append(*reconstructs, reconstruct)

	return normalizedProp
}

// PreCNFCache memoises pre-CNF normalization at both the term level
// (NormalizeTerm) and the prop level (Normalize).
//
// Safe for concurrent use (sync.Map under the hood). Zero value is a usable
// empty cache. A nil receiver bypasses memoization on the cache-aware
// methods.
//
// Prop-level caching keys on input AlphaKey. Two α-equivalent inputs share
// the same cached normalized Prop — sound because Normalize is a function
// on α-classes. The reconstruct callback returned alongside is lazy: on
// cache hit, the closure re-runs the full normalize pipeline only if the
// caller actually invokes it. The vast majority of callers discard the
// reconstruct, so the cache pays for itself within the first repeat call;
// the handful of callers that use the reconstruct of a hit (the session's
// `known` and auto-match closes) pay the full cost on each call — same as
// if no cache were present.
//
// A cache made by NewPreCNFCacheOver stands in front of another one.
type PreCNFCache struct {
	termCache utils.Map[core.TermKey, *PropWrapper]
	propCache utils.Map[core.PropKey, Prop]
	// behind is the cache NormalizeTerm computes through
	// (NewPreCNFCacheOver); nil for a cache that stands alone.
	behind *PreCNFCache
}

// NewPreCNFCacheOver returns an empty cache in front of behind, for a
// caller whose cache has a shorter life than the terms it is asked for:
// the cache of one rule set, made again at each call of a tactic that a
// fixpoint calls on one goal after another, most of whose hypotheses do
// not change. behind is the cache of the whole run.
//
// The cache answers as one that stands alone does. Only how often a
// normal form is computed changes: NormalizeTerm takes a term it does not
// hold from behind, which answers a term spelled as one it holds — bound
// names included — and computes any other (NormalizeTermNameFaithful).
// The normal form is a function of the spelling, so what comes from
// behind is what the cache would have computed.
//
// A nil behind gives a cache that stands alone.
func NewPreCNFCacheOver(behind *PreCNFCache) *PreCNFCache {
	return &PreCNFCache{behind: behind}
}

// TermCacheSize returns the number of entries in the term-level pre-CNF
// cache. Provided for tests that want to observe cache population; not
// load-bearing for production code.
func (c *PreCNFCache) TermCacheSize() int {
	if c == nil {
		return 0
	}
	return c.termCache.Size()
}

// PropCacheSize returns the number of entries in the prop-level Normalize
// cache. Provided for tests that want to observe cache population; not
// load-bearing for production code.
func (c *PreCNFCache) PropCacheSize() int {
	if c == nil {
		return 0
	}
	return c.propCache.Size()
}

// NormalizeTerm rewrites t to its pre-CNF normal form, returning ⊢ t = t_pre.
// It does not universally close free variables; ordinary simplifications may
// still remove free occurrences. If t is already in pre-CNF form, returns
// Refl(t).
//
// A term the cache does not hold is computed, through the cache behind
// this one where there is one (NewPreCNFCacheOver). A nil receiver
// bypasses the cache.
func (c *PreCNFCache) NormalizeTerm(t Term) *PropWrapper {
	if c == nil {
		return PreCNFNormalizeTerm(t)
	}
	if w, ok := c.termCache.Load(t.AlphaKey()); ok {
		return w
	}
	w := c.behind.NormalizeTermNameFaithful(t)
	c.termCache.Store(t.AlphaKey(), w)
	return w
}

// NormalizeTermNameFaithful is NormalizeTerm with a NAME-FAITHFUL cache hit:
// the cached equation is reused only when its LHS Equals t SYNTACTICALLY
// (variable names included), not merely α-equal. The CNF per-hyp pipeline
// must use this variant: an α-keyed hit returns the FIRST populator's
// equation, whose binder naming determines downstream Skolem-witness names —
// reusing it for an α-variant hyp decouples the stored goal's naming (current
// binders) from the refutation cert's naming (cached binders), breaking the
// persisted CNF proof's self-consistency invariant (cold renorm of the stored
// goal must reproduce the cert's clause naming exactly; see
// refuter.ReconstructStoredProof / NegateGoalCNFResult.SelfConsistentGoal).
//
// On a name-mismatched α-hit it recomputes exactly for t WITHOUT overwriting
// the cached entry (first entry wins — no alternation thrash; α-variants are
// rare, so the lost sharing is negligible). Key-only consumers
// (NormalizeTermKey, matcher gates) keep the cheaper α-keyed NormalizeTerm.
func (c *PreCNFCache) NormalizeTermNameFaithful(t Term) *PropWrapper {
	if c == nil {
		return PreCNFNormalizeTerm(t)
	}
	if w, ok := c.termCache.Load(t.AlphaKey()); ok && Lhs(w).Equals(t) {
		return w
	}
	w := PreCNFNormalizeTerm(t)
	c.termCache.LoadOrStore(t.AlphaKey(), w)
	return w
}

// NormalizeTermKey returns the alpha key of t's pre-CNF normal form.
//
// Equivalent to `Rhs(c.NormalizeTerm(t)).AlphaKey()`. Use it for matcher
// applicability gates and cache keys when only the canonical key is needed
// — callers that need the kernel witness to bridge two terms via
// PreCNFEqBridge or to fold the rewrite into a derivation should use
// NormalizeTerm instead.
//
// A nil receiver bypasses memoization (the underlying rewrite still runs).
func (c *PreCNFCache) NormalizeTermKey(t Term) core.TermKey {
	return Rhs(c.NormalizeTerm(t)).AlphaKey()
}
