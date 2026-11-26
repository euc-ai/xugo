// set_tac MEMBERSHIP mode (SetTacMode_SET_TAC_MEMBERSHIP) — the
// membership-level driver. Where the LEGACY mode def-expands every
// vocabulary const everywhere (set operators become λ-comprehensions and
// a goal whose refute needs a composite set witness demands a λ-term the
// first-order refuter cannot synthesize — the wall `s ∩ ⋃f = ⋃{s ∩ t | t ∈ f}` meets), this
// driver reasons at the MEMBERSHIP level and keeps set operators opaque
// first-order terms everywhere except directly under a membership
// observation:
//
//	phase 0 (the statement-level rewrite): a vocabulary head unfolds
//	         where its occurrence has a bool result and only set
//	         arguments (isStatementLevelType) — subset, proper_subset and
//	         disjoint at every type — and every equality atom at a
//	         (τ→…→bool) type is read pointwise (FunEqRewrite). At an
//	         instance whose elements are themselves sets the
//	         membership-level constants pass the same test: set_member,
//	         insert, union, image at a map whose values are sets. They
//	         unfold in this phase, and the equation between sets their
//	         membership rule introduces (insert's `y = a`, image's
//	         `x = f(z)`) is read pointwise like an equation the goal
//	         states. That reading is load-bearing at a family of sets: a
//	         close that must prove the introduced equation — `(u ∩ s) ∩
//	         (v ∩ s) ∈ image(λu. u ∩ s, T)` from `u ∩ v ∈ T` — or match it
//	         against an equation a hypothesis states, which this phase
//	         reads pointwise like every stated one — `u ∈ image(λt.
//	         insert(a, t), F)` from `∃v. v ∈ F ∧ u = insert(a, v)` —
//	         fails with the introduced equation kept. What
//	         the reading does not give: an equation obtained from under
//	         an ∃ does not replace one set by the other inside an opaque
//	         predicate, so `∀x. x ∈ image(f, s) ⇒ P(x)` at a family does
//	         not reduce to its source. Kept as an equation it does not
//	         either: the refuter reads an equation between functions
//	         pointwise itself and recovers it as an equation from a
//	         standalone one (FUNEXT, ext/clause/funext.go), not from one
//	         under an ∃ or inside a disjunction (engine/xugo-engine.md,
//	         "An equation between functions"). comprehension_spec, with a bool
//	         argument, fails the test at every type, so the witness
//	         equation its body introduces (`g = intersection u t`)
//	         reaches phase 1 as an equation, where the one-point fusion
//	         (set_tac_fuse.go) substitutes the witness through; read
//	         pointwise, the witness would be a λ-term the first-order
//	         refuter cannot synthesize. Extension is rewritten once,
//	         before the membership rules.
//	phase 1 (the membership rules): membership REDEXES —
//	         bool-typed applications whose
//	         head const is a set-valued vocabulary const — rewrite to
//	         their membership formulas; plumbing (set_member,
//	         set_comprehension, comprehension_spec) keeps expanding. A
//	         set-valued const at a non-redex position stays opaque.
//	residence (the membership rules as premises): the membership ⇔-rule
//	         of every set-valued const still occurring in a residual
//	         leaf is derived from its kernel def (pure equational
//	         composition + ∀-closure — no search) and installed as a
//	         hyp, so the closing CNF refute can interpret set terms it
//	         synthesizes during search. Probes: the bare residual is
//	         NOT refutable (spent rewrites can't interpret synthesized
//	         terms), residual+rule closes in ms.
//
// SHARED EXECUTOR: like SetTacExpand, this one driver runs at record
// time, emit's CNF collection, and a member's replay — the recorded
// proto (consts + mode) fully determines behavior.
//
// Determinism contract (replay re-runs this cold; residual leaves key
// the closing refutes' CNF cache entries):
//   - per pass, ONE combined fire function walks conclusion-then-hyps in
//     preorder; at each node the rule priority is fixed (const unfold,
//     then redex unfold, then extensionalization); the walker is the
//     same deterministic structural recursion defExpandRewrite uses.
//   - def thms resolve through a per-pass anchor map (first preorder
//     occurrence of the name whose meta carries a def), then rebind
//     every occurrence via MakeConstTerm(anchorMeta, occType).DefThm() —
//     the α-invariance discipline defExpandRewrite documents. Anchor
//     choice is α-invariant: const names are globally unique, so any
//     def-carrying meta of a name materializes THE def of that name.
//   - each phase runs to its fixpoint; ctx is a live-only abort poll
//     (nil at replay). Termination is the vocabulary's structure (see
//     MembershipSetTacExpand), and a pass count past the bound a
//     converging expansion stays under panics: it is a rewrite that
//     loops, an engine defect.
//   - which heads unfold in phase 0 is a pure function of each
//     occurrence's type (isStatementLevelType); in phase 1 position
//     classifies — a bool-typed application unfolds, an occurrence at an
//     object position stays opaque and gets its membership rule by
//     residence.

package tactic

import (
	"context"
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// isStatementLevelType is phase 0's test on a vocabulary head's
// occurrence type: a bool result and every argument a set. subset,
// proper_subset and disjoint pass it at every type. A head with an
// element argument passes it exactly where the element is itself a set
// — set_member, insert, union and image at a family of sets — and there
// it unfolds in phase 0, an equation between sets its membership rule
// introduces read pointwise like the goal's own; the file header says
// why that reading is load-bearing.
// comprehension_spec, with a bool argument, fails it at every type, so
// the witness equation `v = t` its body introduces reaches phase 1 as an
// equation, for the one-point fusion to substitute through.
func isStatementLevelType(t core.HolType) bool {
	flat := ext.MatchesFun(t)
	if !flat[len(flat)-1].Equals(core.TypeBool()) {
		return false
	}
	for _, arg := range flat[:len(flat)-1] {
		argFlat := ext.MatchesFun(arg)
		if len(argFlat) < 2 || !argFlat[len(argFlat)-1].Equals(core.TypeBool()) {
			return false
		}
	}
	return true
}

// membershipAnchors builds the per-pass name→meta anchor map: for every
// vocabulary name, the meta of the first preorder occurrence (conclusion
// before hyps) whose meta carries a def, and for a declared constant no
// occurrence anchors, the meta its door minted (seedDeclaredAnchors).
// See the α-invariance note in this file's header.
func membershipAnchors(p Prop, vocab map[core.TermName]bool) map[core.TermName]core.ConstTermMeta {
	anchors := make(map[core.TermName]core.ConstTermMeta)
	scanAnchorsFromTerm(p.Conclusion(), vocab, anchors)
	for h := range p.HypIter() {
		scanAnchorsFromTerm(h, vocab, anchors)
	}
	seedDeclaredAnchors(anchors, vocab)
	return anchors
}

// scanAnchorsFromTerm extends anchors with def-carrying metas of
// vocabulary consts found in t (first occurrence wins — preorder).
func scanAnchorsFromTerm(t core.Term, vocab map[core.TermName]bool,
	anchors map[core.TermName]core.ConstTermMeta) {
	switch t := t.Core().(type) {
	case core.ConstTerm:
		if vocab[t.Name()] && anchors[t.Name()].IsZero() && !t.DefThm().IsZero() {
			anchors[t.Name()] = t.Meta()
		}
	case core.AppliedTerm:
		scanAnchorsFromTerm(t.Fun(), vocab, anchors)
		scanAnchorsFromTerm(t.Arg(), vocab, anchors)
	case core.AbsTerm:
		scanAnchorsFromTerm(t.Body(), vocab, anchors)
	}
}

// anchoredDefThm materializes `⊢ c = body` for an occurrence via the
// anchor meta at the occurrence's own type instance. Nil when the name
// has no def-carrying anchor in the current goal, or when the type
// instantiation refuses at this instance.
func anchoredDefThm(anchors map[core.TermName]core.ConstTermMeta, c core.ConstTerm) Prop {
	meta := anchors[c.Name()]
	if meta.IsZero() {
		return nil
	}
	return core.MakeConstTerm(meta, c.Type()).DefThm()
}

// appHead strips an application chain down to its head term, returning
// the head and the argument list in application order.
func appHead(t core.AppliedTerm) (core.Term, []core.Term) {
	var args []core.Term
	var cur core.Term = t
	for {
		app, ok := cur.Core().(core.AppliedTerm)
		if !ok {
			break
		}
		args = append(args, app.Arg())
		cur = app.Fun()
	}
	// args were collected outermost-first; reverse to application order.
	for i, j := 0, len(args)-1; i < j; i, j = i+1, j-1 {
		args[i], args[j] = args[j], args[i]
	}
	return cur, args
}

// membershipFire builds the per-node rule function for one pass.
// Priority at a node (first match wins; the walker does not recurse into
// a fired subtree this pass — the next fixpoint iteration rescans):
//
//  1. BOOL-typed application whose head is a vocabulary const → unfold
//     the head's def over the argument chain by congruence (β-collapse
//     happens at the pass level). This single positional rule is the
//     whole membership discipline: `set_member x s`, `subset s t`, `comprehension_spec g P
//     v`, `intersection a b x`, `set_comprehension(λ…) g` are all bool applications and
//     fire; `intersection a b` at an OBJECT position is set-typed and stays an
//     opaque first-order term. (No constant is expanded everywhere: a
//     fully-flattened type ends in bool for EVERY set const, and in
//     phase 1 position is the classifier.) In phase 0 only heads whose
//     occurrence passes isStatementLevelType fire.
//  2. [phase 0 only] equality atom at a (τ→…→bool) function type →
//     extensionalize via prop.FunEqRewrite (fires repeatedly across
//     passes until the equality is pointwise).
func membershipFire(
	vocab map[core.TermName]bool,
	anchors map[core.TermName]core.ConstTermMeta,
	phase0 bool,
) func(core.Term) *prop.PropWrapper {
	return func(t core.Term) *prop.PropWrapper {
		app, ok := t.Core().(core.AppliedTerm)
		if !ok {
			return nil
		}
		if app.Type().Equals(core.TypeBool()) {
			head, args := appHead(app)
			if c, ok := head.AsConst(); ok && vocab[c.Name()] &&
				!(phase0 && !isStatementLevelType(c.Type())) {
				if defThm := anchoredDefThm(anchors, c); defThm != nil {
					w := prop.WrapProp(defThm)
					for _, a := range args {
						w = w.RightApply(a)
					}
					return w
				}
			}
			// ∃-one-point fusion (phase 1): substitute comprehension
			// witnesses through before the refuter's pre-CNF fun-eq
			// dissolution can destroy them — see set_tac_fuse.go.
			if !phase0 {
				if w := existsOnePointFuse(t); w != nil {
					return w
				}
			}
		}
		if phase0 {
			if l, _, ok := MatchesEQ(t); ok {
				flat := ext.MatchesFun(l.Type())
				if len(flat) > 1 && flat[len(flat)-1].Equals(core.TypeBool()) {
					return prop.FunEqRewrite(t)
				}
			}
		}
		return nil
	}
}

// membershipWalk composes fire over a term by congruence — the same
// deterministic structural recursion (with per-root PtrMemo) as
// defExpandRewrite's walker, parameterized by the rule function.
func membershipWalk(root core.Term, fire func(core.Term) *prop.PropWrapper) *prop.PropWrapper {
	cache := ext.PtrMemoFor[*prop.PropWrapper](root)
	var walk prop.Rewrite
	walk = func(t core.Term) *prop.PropWrapper {
		if w := fire(t); w != nil {
			return w
		}
		if w, ok := cache.Load(t); ok {
			return w
		}
		var w *prop.PropWrapper
		switch t := t.Core().(type) {
		case core.AppliedTerm:
			w = combineAppliedRewriteFast(t, walk(t.Fun()), walk(t.Arg()))
		case core.AbsTerm:
			if thm := walk(t.Body()); thm != nil {
				w = thm.Abs(t.Var())
			}
		}
		cache.Store(t, w)
		return w
	}
	return walk(root)
}

// membershipRewriteProp runs one pass of fire over the goal's conclusion
// and hyps, β-reducing changed slots — TryDefExpand's Prop-level bridge
// plumbing without the lemma child (membership bridges are self-contained
// kernel equalities: def thms + β + congruence; there is no claim to
// track). Returns nil when nothing structurally changed.
func membershipRewriteProp(goal Prop, fire func(core.Term) *prop.PropWrapper) *SubGoals {
	// A fired slot is β-reduced and then cleared of the boolean
	// constants the unfolding put there: `x ∈ 𝕌` unfolds to ⊤ and
	// `x ∈ ∅` to ⊥, so a complement in the whole type reads
	// `⊤ ∧ ¬P(ẋ)` and a disjointness `(A(ẋ) ∧ B(ẋ)) ⇔ ⊥` until the
	// clauses `⊤ ∧ p`, `p ⇔ ⊥`, … fire (the rewrite carries
	// them beside the membership rules). The constants are born here,
	// after every author-level shaping has run, so nothing upstream can
	// remove them, and the terminal's assumption check compares terms:
	// with them in place a residual never meets the resident pointwise
	// fact of the same content and the refuter is paid for a refute
	// with no content.
	rw := func(t core.Term) *prop.PropWrapper {
		w := membershipWalk(t, fire)
		if w == nil {
			return nil
		}
		return w.RewriteConclRhs(prop.DeepBeta).RewriteConclRhs(prop.DeepBoolRewrite)
	}
	return rewritePropWith(goal, rw)
}

// rewritePropWith rewrites the goal's conclusion and each hypothesis by
// the bridge rw gives for it — a hypothesis-free kernel equality whose
// left side is the term — into one child, reconstructing the goal's
// proof from the child's through the bridges. Returns nil when no
// bridge changes anything.
func rewritePropWith(goal Prop, rw func(core.Term) *prop.PropWrapper) *SubGoals {
	conclBridge := rw(goal.Conclusion())
	if conclBridge != nil && conclBridge.NumHyps() != 0 {
		return nil
	}
	if conclBridge != nil && prop.Rhs(conclBridge).AlphaEquals(goal.Conclusion()) {
		conclBridge = nil
	}

	numHyps := goal.NumHyps()
	hypBridges := make([]*prop.PropWrapper, numHyps)
	changedHyp := false
	for i := 0; i < numHyps; i++ {
		h := goal.Hyp(i)
		hb := rw(h)
		if hb == nil || hb.NumHyps() != 0 {
			continue
		}
		if prop.Rhs(hb).AlphaEquals(h) {
			continue
		}
		hypBridges[i] = hb
		changedHyp = true
	}
	if conclBridge == nil && !changedHyp {
		return nil
	}

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
	child := MakeProp(newConcl, newHyps...)

	reconstruct := func(thms ...Prop) Prop {
		if thms[0].Conclusion().Equals(F) && !changedHyp {
			return thms[0]
		}
		result := prop.WrapProp(thms[0])
		if conclBridge != nil && !thms[0].Conclusion().Equals(F) {
			result = conclBridge.EqSym().EqMP(result)
		}
		for i := 0; i < numHyps; i++ {
			if hypBridges[i] == nil {
				continue
			}
			la := hypBridges[i].LeftAssume()
			if result.HasHyp(la.Conclusion()) {
				result = la.DeriveTrans(result)
			}
		}
		return result
	}
	return MakeSubGoals(goal, reconstruct, child)
}

// MembershipSetTacExpand is the membership-mode rewrite driver: phase 0
// to fixpoint, then phase 1 to fixpoint, under a shared size budget.
// Returns nil when no rewrite fires in either phase (the caller falls
// through to residence-or-bare-refute, mirroring SetTacExpand's nil
// contract). ctx is the live-only abort poll (nil at replay).
func MembershipSetTacExpand(ctx context.Context, goal Prop, consts []core.TermName) *SubGoals {
	vocab := make(map[core.TermName]bool, len(consts))
	for _, n := range consts {
		vocab[n] = true
	}
	oneStep := func(phase0 bool) Tactic {
		return func(p Prop) *SubGoals {
			anchors := membershipAnchors(p, vocab)
			return membershipRewriteProp(p, membershipFire(vocab, anchors, phase0))
		}
	}

	// Each phase runs to its fixpoint. A pass fires every redex it meets
	// outside an already-fired subtree, so the passes a position needs are
	// the vocabulary layers its unfolding descends through: a definition
	// never reintroduces its own constant and the vocabulary's definitions
	// are acyclic. A goal's term size does not bound that — a compact
	// constant such as preimage_on hides layers its size does not show —
	// so no size budget cuts the expansion short. What does bound a
	// converging expansion is every vocabulary application of the goal
	// descending through every layer, with one more pass each for
	// one-point fusion and extensionalization; past that bound a rewrite
	// is looping, and the driver panics rather than hand the refuter a
	// half-expanded residual.
	size := goal.Conclusion().Size()
	for h := range goal.HypIter() {
		size += h.Size()
	}
	loopBound := (size + 1) * (len(consts) + 2)

	var s *SubGoals
	for _, phase0 := range []bool{true, false} {
		step := oneStep(phase0)
		if s == nil {
			s = step(goal)
			if s == nil {
				continue
			}
		}
		for pass := 0; ; pass++ {
			if ctx.Err() != nil {
				return s
			}
			if pass > loopBound {
				panic(fmt.Sprintf("MembershipSetTacExpand: no fixpoint after %d passes on a goal of size %d — a vocabulary rewrite loops", pass, size))
			}
			next := step.expand(s)
			if next == s {
				break
			}
			s = next
		}
	}
	return s
}

// setValuedResidents collects the distinct (anchor-resolvable)
// vocabulary const instances still occurring in a leaf — the operators
// the residual's refute will need membership rules for. The rewrite
// fixpoint has already consumed every bool-application redex, so ANY
// surviving vocabulary occurrence sits at an object position (an opaque
// first-order set term like `intersection u t` inside an equation). Keyed and
// returned in deterministic first-preorder-occurrence order.
func setValuedResidents(leaf Prop, vocab map[core.TermName]bool,
	anchors map[core.TermName]core.ConstTermMeta) []core.ConstTerm {
	seen := make(map[core.TermKey]bool)
	var out []core.ConstTerm
	var scan func(t core.Term)
	scan = func(t core.Term) {
		switch t := t.Core().(type) {
		case core.ConstTerm:
			if vocab[t.Name()] && !anchors[t.Name()].IsZero() {
				if k := t.AlphaKey(); !seen[k] {
					seen[k] = true
					out = append(out, t)
				}
			}
		case core.AppliedTerm:
			scan(t.Fun())
			scan(t.Arg())
		case core.AbsTerm:
			scan(t.Body())
		}
	}
	scan(leaf.Conclusion())
	for h := range leaf.HypIter() {
		scan(h)
	}
	return out
}

// membershipTemplate derives the ∀-closed membership rule of one
// set-valued const instance from its kernel def — pure equational
// composition, no search:
//
//	⊢ ∀a₁…aₙ x. C(a₁,…,aₙ)(x) ⇔ φ
//
// where φ is the def body applied and normalized to fixpoint under the
// phase-1 rules (plumbing expanded, nested membership redexes rewritten;
// set-valued consts at object positions inside φ stay opaque — their own
// templates are derived separately by the caller's resident scan).
func membershipTemplate(c core.ConstTerm,
	vocab map[core.TermName]bool,
	anchors map[core.TermName]core.ConstTermMeta) *prop.PropWrapper {
	defThm := anchoredDefThm(anchors, c)
	if defThm == nil {
		return nil
	}
	flat := ext.MatchesFun(c.Type())
	// flat = [T₁, …, Tₙ, τ…, bool]: apply a fresh var at EVERY argument
	// position through the final bool — the last vars are the observation
	// points.
	// A def body is a CLOSED term (NewConstDef invariant), so indexed
	// fresh names cannot capture or collide.
	w := prop.WrapProp(defThm)
	vars := make([]core.VarTerm, 0, len(flat)-1)
	for i := 0; i < len(flat)-1; i++ {
		v := core.Var(core.TermName(fmt.Sprintf("x%d", i)), flat[i])
		vars = append(vars, v)
		w = w.RightApply(v)
	}
	w = w.RewriteConclRhs(prop.DeepBeta)
	// Normalize the RHS to phase-1 fixpoint. Small terms (a def body),
	// strictly descending const hierarchy — termination is structural.
	// Anchors rescan from the CURRENT RHS each iteration: the def body's
	// embedded consts (set_member inside intersection's body) carry their own
	// def-wired metas, which the leaf-level anchor map cannot supply —
	// the leaf's own set_member occurrences were consumed by the main fixpoint.
	// Without the rescan the template would speak an unexpanded set_member
	// vocabulary the application-form residual never connects to.
	w = w.RewriteConclRhsRecur(func(t core.Term) *prop.PropWrapper {
		anch := make(map[core.TermName]core.ConstTermMeta)
		scanAnchorsFromTerm(t, vocab, anch)
		seedDeclaredAnchors(anch, vocab)
		u := membershipWalk(t, membershipFire(vocab, anch, false))
		if u == nil {
			return nil
		}
		return u.RewriteConclRhs(prop.DeepBeta)
	})
	for i := len(vars) - 1; i >= 0; i-- {
		w = w.ConclForAll(vars[i])
	}
	return w
}

// MembershipResidence installs the derived membership rules of every
// set-valued vocabulary const still occurring in the leaf as hyps —
// the rules as premises, scoped per leaf. Returns nil
// when the leaf has no resident set-valued consts (nothing to install).
// The single child is the leaf plus rule hyps; reconstruction discharges
// each rule hyp with its kernel derivation (DeriveTrans — the rules are
// hyp-free theorems).
func MembershipResidence(leaf Prop, consts []core.TermName) *SubGoals {
	vocab := make(map[core.TermName]bool, len(consts))
	for _, n := range consts {
		vocab[n] = true
	}
	anchors := membershipAnchors(leaf, vocab)
	residents := setValuedResidents(leaf, vocab, anchors)
	if len(residents) == 0 {
		return nil
	}
	var templates []*prop.PropWrapper
	for _, c := range residents {
		if w := membershipTemplate(c, vocab, anchors); w != nil {
			templates = append(templates, w)
		}
	}
	if len(templates) == 0 {
		return nil
	}

	newHyps := leaf.Hyps()
	for _, w := range templates {
		if !leaf.HasHyp(w.Conclusion()) {
			newHyps = append(newHyps, w.Conclusion())
		}
	}
	child := MakeProp(leaf.Conclusion(), newHyps...)
	reconstruct := func(thms ...Prop) Prop {
		result := prop.WrapProp(thms[0])
		for _, w := range templates {
			if result.HasHyp(w.Conclusion()) {
				result = w.DeriveTrans(result)
			}
		}
		return result
	}
	return MakeSubGoals(leaf, reconstruct, child)
}
