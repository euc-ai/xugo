package tactic

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// Arithmetic automation tactics — thin adapters from the proof-producing
// procedures in prover/solver/omega to the tactic interface. Each closes its goal
// outright (no subgoals) by handing omega's proof to MakeEmptySubGoals, which
// checks IsStronger (concl α-matches, hyps ⊆ goal hyps). All return nil when
// the procedure declines, so callers can fall through to other tactics.
//
// omega's leaves come from the LemmaBundle (omega.SetLemmaBundle). When that
// bundle is filled with ThmPromises for lazy library loading, omega's output
// wrapper is an unresolved derived promise; closeByOmega threads it into the
// goal's proof, so its eventual force uses the caller's Forcer. With the
// default (placeholder) bundle the wrapper is already a certificate.
//
// Soundness: with a real bundle installed (serve.InstallNatBundle, at
// initEngine) every leaf binds its kernel theorem and these moves are sound;
// production has no placeholder fabricator, so any unbound leaf panics at the
// placeholder seam (not a mode toggle — the default). With no bundle (omega's
// own tests) the bundle-nil leaves use test-only placeholder stand-ins — never
// compiled into production (omega/bundle.go).

// closeByOmega turns an omega proof-wrapper into goal-closing SubGoals,
// retaining any promise-backed leaves as dependencies. The `ok` flag
// is the procedure's own "declined" signal (nil SubGoals → fall through to the
// next tactic). Once omega HAS produced a wrapper, forcing it must succeed; a
// proof that can't realize a real certificate is a bug — core.AsThm panics if
// the wrapper isn't proven-or-provable. It is not folded back into "declined".
func closeByOmega(goal Prop, w *PropWrapper, ok bool) *SubGoals {
	if !ok {
		return nil
	}
	return MakeEmptySubGoals(goal, core.AsThm(w))
}

// RingTactic closes `⊢ l = r` over num via the commutative-semiring normalizer
// (omega.RingProveFull — full multivariate, subsumes the linear fragment).
// Returns nil when the conclusion is not a num equality (non-num `=`, bool `⇔`,
// non-equality conclusion) or the normalizer cannot prove l = r. The num-type
// gate is load-bearing: omega's bit/AC primitives panic on non-num operands,
// so a caller like AutoExpand that runs ring on every leaf MUST get a clean
// decline (nil) on non-num equalities rather than a panic.
func RingTactic(goal Prop) *SubGoals {
	l, r, ok := MatchesEQ(goal.Conclusion())
	if !ok {
		return nil
	}
	if !l.Type().Equals(dsl.NumType) {
		return nil
	}
	w, ok := omega.RingProveFull(l, r)
	return closeByOmega(goal, w, ok)
}

// LinarithTactic closes a linear comparison goal `{Γ} ⊢ a ⋈ b` over num
// (⋈ ∈ {<, ≤, =, ≠, >, ≥}) by ℚ-Farkas refutation of the negated goal against
// the linear hypotheses (omega.LinProve). Hyps that are not linear comparisons
// are ignored. Returns nil when the goal is not a recognized linear comparison
// over num (the same num-type gate as RingTactic — non-num goals are a clean
// decline, not a panic in the omega primitives) or is not ℚ-Farkas valid given
// the hyps (e.g. it needs integer reasoning).
func LinarithTactic(goal Prop) *SubGoals {
	if !omega.IsLinComparisonGoal(goal.Conclusion()) {
		return nil
	}
	w, ok := omega.LinProve(goal.HypIter(), goal.Conclusion())
	return closeByOmega(goal, w, ok)
}

// ArithTactic is THE unified num-arithmetic move (was: separate RingTactic /
// LinarithTactic / OmegaTactic closers + separate ArithDecideTactic /
// ArithSimpTactic rewriters). It rewrites the goal through the unified
// deep+fixpoint `omega.ArithDecideWithHyps` (a single
// `prop.BasicRewritesWith` over [identity-law leaf, atom-decision leaf,
// all standard basic rewrites]):
//
//   - identity-law simplification (a+0→a, a*1→a, c₁+c₂→c, ...);
//   - decides each comparison/equality atom (`<` `≤` `>` `≥` `=`) the goal's
//     hyps make universally true/false, to ⊤/⊥;
//   - decides commutative-semiring equalities to ⊤ via RingProveFull (incl.
//     nonlinear `a*b=b*a`, `(a+b)²=a²+2ab+b²`);
//   - reaches buried atoms (under ⇒/∧/∨/¬) and atoms under a binder;
//   - bool/cond/quantifier/neg collapses happen in the SAME fixpoint pass —
//     a cascade like `a + Cond(a=a, 0, 1) → a` (decide a=a → ⊤, Cond(⊤,…)→0,
//     a+0→a) resolves in one call.
//
// Produces ONE child carrying the rewritten conclusion. When the whole
// conclusion reduces to ⊤ the child is `⊢ ⊤`, which `_TrivialSimplify` closes
// via DerivesTrue — so a fully-decidable goal closes through the composite,
// while a partial decision advances the goal. Returns nil when nothing
// reduces (clean decline).
//
// Why no outer soundness guard: omega's leaves return ok=false (never a
// fabricated cert) when they can't derive a real proof, so a contingent atom's
// failed prove attempt is left undecided and never poisons sound decisions of
// sibling atoms.
//
// reader is the proof's reading of the record equations
// (omega.LibraryReader), through which the structure ring reads every
// equation its facts compute with; nil reads through the installed
// fallback.
func ArithTactic(goal Prop, policy omega.ArithPolicy, reader *omega.LibraryReader) *SubGoals {
	sg, _ := arithRewriteTactic(goal, policy, reader, nil, false)
	return sg
}

// ArithRewrite is one firing of ArithTactic: the target it rewrote — a
// hypothesis, or the conclusion — and what it rewrote it to (⊤ for a
// hypothesis dropped as redundant).
type ArithRewrite struct {
	From, To Term
	// Conclusion says the target was the conclusion.
	Conclusion bool
}

// ArithTacticPassingOver is ArithTactic for a caller that runs it in
// rounds: the rewrites in passOver are not fired, the firing going to the
// next target as it does past a rewrite the context already spells, and
// the rewrite fired is reported beside the subgoals. The caller passes
// over a rewrite its own next step undid. The arith closer's mop-up reads
// a resident equation `n = 2 * m` term to variable where the decider
// reads it variable to term, so `2 ∣ n` rewritten to `2 ∣ (2 * m)` comes
// back as `2 ∣ n`; and it folds a conclusion's `|x| * |y|` back to
// `|x * y|` by the bridge equation the firing left beside it. Fired
// again, either would take the firing of every round, and the
// conclusion's would keep every hypothesis from its turn.
//
// The rounds are a close, and a close keeps its equations (the closing
// retention of arithRewriteTactic): a hypothesis the decider proves
// redundant is replaced by the value equations it holds.
func ArithTacticPassingOver(goal Prop, policy omega.ArithPolicy, reader *omega.LibraryReader, passOver []ArithRewrite) (*SubGoals, ArithRewrite) {
	return arithRewriteTactic(goal, policy, reader, passOver, true)
}

// passedOver reports whether the rewrite from to to — of the conclusion,
// or of a hypothesis — is one of over, up to α.
func passedOver(over []ArithRewrite, conclusion bool, from, to Term) bool {
	for _, r := range over {
		if r.Conclusion == conclusion && r.From.AlphaEquals(from) && r.To.AlphaEquals(to) {
			return true
		}
	}
	return false
}

// RingNfTactic is the `ring_nf` rewrite: every arithmetic subterm of the
// conclusion and of each hypothesis to its ring normal form
// (omega.RingNormalizeRewriteWithPolicy), one target per pass through the
// context-free rewriteTactic, to a fixpoint over the targets. nil when no
// subterm changes.
func RingNfTactic(goal Prop, policy omega.ArithPolicy) *SubGoals {
	step := rewriteTactic(omega.RingNormalizeRewriteWithPolicy(policy))
	s := step(goal)
	if s == nil {
		return nil
	}
	for range goal.NumHyps() + 1 {
		next := Tactic(step).expand(s)
		if next == s {
			break
		}
		s = next
	}
	return s
}

// arithRewriteTactic applies omega's hyp-aware arith decider to the goal with
// the CORRECT context per target. It deliberately does NOT route through the
// generic rewriteTactic, because that helper applies ONE rewrite to the
// conclusion AND every hypothesis — and a single `ArithDecideWithHyps(allHyps)`
// closed over the whole hyp set, when applied to a hypothesis, decides that
// hypothesis FROM ITSELF (a hyp under its own assumption is trivially ⊤). That
// self-justifying rewrite collapses every decidable hyp to ⊤, discarding the
// hypothesis and reporting false progress. (rewriteTactic stays correct for its
// other, context-FREE callers — BasicRewrite / ExpandEXPRewrite / … — whose
// rewrite never depends on the term being rewritten.)
//
// The standard rewrite discipline (cf. eqSimplifyUnder): a hypothesis is used
// to simplify the REST of the goal, never itself. So:
//
//   - the CONCLUSION is rewritten under ALL hypotheses;
//   - each hypothesis hyp[i] is rewritten under the OTHER hypotheses only —
//     confining hyp rewriting to the MEANINGFUL cases: a context-free identity
//     fold (`a+0 ≤ b → a ≤ b`), a hyp the other hyps make redundant (⇔⊤, safe
//     to drop) or contradictory (⇔⊥, ex-falso). A hyp can never decide itself.
//
// Subgoal / reconstruct plumbing mirrors rewriteTactic exactly; only the context
// per target differs. Conclusion first, then hyps (same precedence). A
// rewrite in passOver is not fired (ArithTacticPassingOver), and the
// rewrite fired is returned beside the subgoals.
//
// THE ATOMS FIRST (closing, the rounds of a close): a hypothesis the
// decider proves ⊤ as a whole is read atom by atom before that verdict
// drops it (readByAtoms). The decider proves a whole by assuming its
// parts — an iff by each side in turn — and so proves a law's instance
// `P ⇔ Q` outright wherever it reads the law, though the context settles
// one side and not the other: with Q false the instance is `¬P`, a fact
// the decider may reach from no hypothesis the leaf holds. So each atom
// the other hypotheses settle is put at its value, the connectives are
// folded, and what is left replaces the hypothesis; the verdict as a
// whole stands only where the atoms leave ⊤, or settle nothing. A decider
// that could not prove the instance left exactly that residue, and one
// that can must not do worse.
//
// CLOSING RETENTION (closing, the rounds of a close): the close that
// follows a firing reads the leaf's value equations as written — the
// ground-congruence pass substitutes by a compound equation's two sides,
// the mop-up rewrites by a resident equation — so a firing that loses one
// can strand a close the decider's gain in strength should have left alone.
// A hypothesis decided ⊤ as a whole that holds a value equation the decider
// proves, below a connective — `(E ⇔ P)` with both sides true, `¬g ∨ E` —
// is replaced by those equations (heldEquations), where it was dropped, or
// left wrapped and unread. A decider that could not prove E collapsed such
// a hypothesis to E; one that can must not do worse. A hypothesis that is
// the conjunction of those equations already is kept as it stands.
func arithRewriteTactic(goal Prop, policy omega.ArithPolicy, reader *omega.LibraryReader, passOver []ArithRewrite, closing bool) (*SubGoals, ArithRewrite) {
	hyps := slices.Collect(goal.HypIter())
	// Build the pre-simp'd hyp context ONCE for both the conclusion decide and
	// the per-hyp loop. The conclusion needs all hyps; each hyp[i] needs
	// hyps\i. Without the shared context, each loop iteration would re-run
	// preSimpHyps (the per-hyp deep+fixpoint hyp-free rewrite) over the N-1
	// other hyps — O(N²) work where O(N) suffices.
	ctx := omega.NewArithCtxWithPolicy(hyps, policy, reader)
	// Every decision of the step is made before this function returns; what
	// the decider memoized for it is of no use to the next.
	defer omega.ReleaseStepMemos()
	// Conclusion: context = all hypotheses.
	w := ctx.Decide(goal.Conclusion())
	if w != nil && !passedOver(passOver, true, goal.Conclusion(), Rhs(w)) {
		// No-hurt bridges (see emitArithBridges): the value-level equations
		// this rewrite consumed ride along as extra hyps of the residual, so
		// a downstream syntactic stage (CNF paramodulation) keeps its reach.
		// A conclusion decided to ⊤ closes via _TrivialSimplify — no residual
		// survives, so nothing is emitted for it (Rhs(w) ≡ ⊤ yields no
		// value-typed diffs anyway; same for ⊥, whose shape mismatch stops
		// the walk).
		bridgeEqs, bridgeCerts := emitArithBridges(
			goal.Conclusion(), Rhs(w), hyps, ctx.Decide)
		goal0 := MakeProp(Rhs(w), slices.Concat(hyps, bridgeEqs)...)
		reconstruct := func(thms ...Prop) Prop {
			res := thms[0]
			for _, cert := range bridgeCerts {
				res = cert.MaybeDeriveTrans(res)
			}
			if res.Conclusion().Equals(F) {
				return res
			}
			return w.EqSym().EqMP(res)
		}
		return MakeSubGoals(goal, reconstruct, goal0), ArithRewrite{From: goal.Conclusion(), To: Rhs(w), Conclusion: true}
	}
	// Hypotheses: each rewritten under the OTHER hyps only (never itself).
	fire := func(i int, w *PropWrapper) (*SubGoals, ArithRewrite) {
		fired := ArithRewrite{From: hyps[i], To: Rhs(w)}
		decideExcept := func(t Term) *PropWrapper { return ctx.DecideExcept(i, t) }
		bridgeEqs, bridgeCerts := emitArithBridges(hyps[i], Rhs(w), hyps, decideExcept)
		w = w.LeftAssume()
		newHyps := slices.Clone(hyps)
		newHyps[i] = w.Conclusion()
		goal0 := MakeProp(goal.Conclusion(), slices.Concat(newHyps, bridgeEqs)...)
		reconstruct := func(thms ...Prop) Prop {
			res := w.MaybeDeriveTrans(thms[0])
			for _, cert := range bridgeCerts {
				res = cert.MaybeDeriveTrans(res)
			}
			return res
		}
		return MakeSubGoals(goal, reconstruct, goal0), fired
	}
	// FIRING ORDER: content rewrites outrank redundancy drops. A drop
	// (hyp ⇔ ⊤ under the others, droppable per the retention rule below)
	// is bookkeeping; a rewrite that leaves CONTENT (an identity fold, an
	// iff collapse, an ex-falso ⊥) is what a one-shot composite —
	// Chain(Arith, TrivialSimplify), a ByArith close — spends its single
	// firing on. Under the monomial-basis extraction the decider proves
	// far more collective redundancies (an already-derived `n·a ≤ n·b`
	// re-derives from its own sources), so index order started handing
	// the firing to a drop and stranding the load-bearing rewrite (the
	// eudoxus_slope.LessEqTotal incident); deferring drops behind content keeps
	// BOTH pinned behaviors — the drop still happens when it is the only
	// firing (arith-as-simplifier, engine TestArith_HypRewriteContext),
	// and the composite's firing lands on the rewrite that advances the
	// goal.
	deferredDrop := -1
	var deferredW *PropWrapper
	for i := range hyps {
		w := ctx.DecideExcept(i, hyps[i])
		if w == nil || passedOver(passOver, false, hyps[i], Rhs(w)) {
			continue
		}
		// RETENTION: a hyp the arith decider proves redundant (⇔ ⊤) is not
		// rewritten to ⊤ and dropped unconditionally. When the redundancy
		// is EQUALITY-flavored or a collectively-true disjunction, dropping
		// destroys syntax the downstream CNF refuter feeds on and cannot
		// re-derive (it has no arithmetic): a true equation is paramodulation
		// food (`0*x = 0` via ring), and a collectively-true disjunction is a
		// case-split license (`(m=0) ∨ (0<m)` is num totality — the refuter
		// has no num axioms to case on m without it). Those hyps are retained
		// by skipping the fire — which also keeps the emitted bridge hyps
		// stable across repeated arith passes (each is a ground true non-refl
		// equation): drop-and-re-emit would ping-pong forever.
		//
		// A ⊤-hyp still DROPS when some single literal of its clause form is
		// individually arith-⊤ with a non-equality atom (`X ⇒ (r ≤ r)`,
		// `0 ≤ x`, a bounded product under its bounds): the tautology-
		// deletion case — but DEFERRED behind any content rewrite (see the
		// firing-order note above).
		if Rhs(w).Equals(T) {
			decideExcept := func(t Term) *PropWrapper { return ctx.DecideExcept(i, t) }
			// The atoms first: what a hypothesis decided ⊤ as a whole
			// still says once its settled atoms are put at their values
			// takes its place.
			if closing {
				if read := readByAtoms(hyps[i], decideExcept); read != nil && !Rhs(read).Equals(T) {
					if passedOver(passOver, false, hyps[i], Rhs(read)) {
						continue
					}
					if !spelledElsewhere(hyps, i, Rhs(read)) {
						return fire(i, read)
					}
				}
			}
			// Closing retention: the equations a redundant hypothesis
			// holds below a connective take its place, and a hypothesis
			// that is their conjunction already is kept as it stands.
			if closing {
				held, stands := heldEquations(hyps, i, w, decideExcept)
				if stands {
					continue
				}
				if held != nil && !passedOver(passOver, false, hyps[i], Rhs(held)) {
					return fire(i, held)
				}
			}
			if !droppableRedundantHyp(hyps[i], decideExcept) {
				continue
			}
			if deferredDrop < 0 {
				deferredDrop, deferredW = i, w
			}
			continue
		}
		// A rewrite whose result the context already spells — another
		// hypothesis, or for an equation its symmetric — leaves no
		// content either: it respells a fact the leaf holds, and the
		// mop-up folds the two copies back into one, so a close that
		// fires it round after round never advances. It is passed over
		// like a redundancy, and the firing goes to the next hypothesis.
		if spelledElsewhere(hyps, i, Rhs(w)) {
			continue
		}
		return fire(i, w)
	}
	if deferredDrop >= 0 {
		return fire(deferredDrop, deferredW)
	}
	// THE LEAF AT ITS DEFINITIONS (closing), where nothing else fires. A
	// decision has already been tried with the variables the hypotheses
	// define read at their definitions (omega.ArithCtx.Decide). What is
	// left to the rounds is the trivial simplifier between the firings,
	// which rewrites by the equations of every type and reads the leaf
	// as it is written — and a leaf whose hypotheses name a variable and
	// its definition side by side is two spellings to it. So the last
	// firing reads the leaf whole: every hypothesis and the conclusion
	// at the definitions, the definitions' own equations left out, the
	// variables they defined being gone. It comes last because a name
	// the author gave a term is worth keeping while anything can still
	// be done with it; and one firing reads the leaf whole, so nothing
	// is left for a later one to respell and the simplifier has no
	// equation to read back the other way.
	if closing {
		if sg, fired := leafAtDefinitions(goal, ctx); sg != nil && !passedOver(passOver, true, fired.From, fired.To) {
			return sg, fired
		}
	}
	return nil, ArithRewrite{}
}

// leafAtDefinitions is the firing that reads goal whole at the definitions
// its hypotheses hold (omega.ArithCtx.LeafAtDefinitions): the residual has
// each hypothesis and the conclusion read, and the definitions' own
// equations dropped. nil where the hypotheses hold no definition.
func leafAtDefinitions(goal Prop, ctx *omega.ArithCtx) (*SubGoals, ArithRewrite) {
	leaf, ok := ctx.LeafAtDefinitions(goal.Conclusion())
	if !ok {
		return nil, ArithRewrite{}
	}
	concl := goal.Conclusion()
	if leaf.Concl != nil {
		concl = Rhs(leaf.Concl)
	}
	var read []Term
	for _, h := range leaf.Hyps {
		if h != nil {
			read = append(read, h)
		}
	}
	reconstruct := func(thms ...Prop) Prop {
		res := thms[0]
		for _, bridge := range leaf.Bridges {
			if bridge != nil {
				res = bridge.MaybeDeriveTrans(res) // read[j] back to hyps[j] and the definitions
			}
		}
		if leaf.Concl == nil || res.Conclusion().Equals(F) {
			return res
		}
		return leaf.Concl.EqSym().EqMP(res)
	}
	return MakeSubGoals(goal, reconstruct, MakeProp(concl, read...)),
		ArithRewrite{From: goal.Conclusion(), To: concl, Conclusion: true}
}

// readByAtoms reads the hypothesis h atom by atom: `Γ ⊢ h = R`, R being h
// with each atom that decide settles put at its ⊤ or ⊥ and the boolean
// connectives folded. nil where decide settles no atom of h.
func readByAtoms(h Term, decide func(Term) *PropWrapper) *PropWrapper {
	w := settledAtoms(h, decide)
	if w == nil {
		return nil
	}
	for {
		fold := prop.DeepBoolRewrite(Rhs(w))
		if fold == nil {
			return w
		}
		w = w.EqTrans(fold)
	}
}

// settledAtoms is `Γ ⊢ t = t′`, t′ being t with each atom below its
// connectives (¬, ∧, ∨, ⇒, ⇔) that decide settles put at the value it
// settles to; nil where it settles none. An atom is what the connectives
// leave — a comparison, an equation between values, a predicate, a
// quantified formula — and is read whole.
func settledAtoms(t Term, decide func(Term) *PropWrapper) *PropWrapper {
	if inner := ext.MatchesNOT(t); inner != nil {
		w := settledAtoms(inner, decide)
		if w == nil {
			return nil
		}
		return w.LeftApply(prop.NOT) // ⊢ ¬x = ¬x′
	}
	binary := func(l, r Term) *PropWrapper {
		outer, _ := t.AsAppliedTerm()
		inner, _ := outer.Fun().AsAppliedTerm()
		op := inner.Fun()
		wl, wr := settledAtoms(l, decide), settledAtoms(r, decide)
		if wl == nil && wr == nil {
			return nil
		}
		w, left := prop.Refl(t), l
		if wl != nil {
			w = wl.LeftApply(op).RightApply(r) // ⊢ op(l, r) = op(l′, r)
			left = Rhs(wl)
		}
		if wr != nil {
			w = w.EqTrans(wr.LeftApply(ext.Apply(op, left))) // = op(l′, r′)
		}
		return w
	}
	for _, match := range []func(Term) (Term, Term, bool){prop.MatchesAND, prop.MatchesOR, ext.MatchesIMPLY} {
		if l, r, ok := match(t); ok {
			return binary(l, r)
		}
	}
	if l, r, ok := MatchesEQ(t); ok && IsBool(l) {
		return binary(l, r)
	}
	if w := decide(t); w != nil && (Rhs(w).Equals(T) || Rhs(w).Equals(F)) {
		return w
	}
	return nil
}

// spelledElsewhere reports whether a hypothesis other than hyps[i] is t,
// or for an equation t its symmetric, up to α.
func spelledElsewhere(hyps []Term, i int, t Term) bool {
	var symmetric Term
	if l, r, ok := MatchesEQ(t); ok {
		symmetric = core.Eq(r, l)
	}
	for j, h := range hyps {
		if j == i {
			continue
		}
		if h.AlphaEquals(t) || (symmetric != nil && h.AlphaEquals(symmetric)) {
			return true
		}
	}
	return false
}

// isValueEquation reports whether t is an equation between two value
// terms: not an iff, not an equation between functions.
func isValueEquation(t Term) bool {
	l, _, ok := MatchesEQ(t)
	return ok && arithValueTerm(l)
}

// heldEquations is the closing retention's rewrite of a hypothesis the
// decider proved redundant, whole: `Γ ⊢ hyps[i] = E₁ ∧ … ∧ Eₖ`, the Eⱼ the
// value equations and disequations that stand in hyps[i] below its
// connectives (∧, ∨, ⇒, ¬, ⇔), each proved by decide under the other
// hypotheses, none reflexive and none a hypothesis already. top is the
// decider's `Γ ⊢ hyps[i] = ⊤`. nil where hyps[i] is itself an equation or a
// disequation — the retention rule keeps that one as it stands — and where
// it holds none that decide proves.
//
// stands reports a hypothesis that is E₁ ∧ … ∧ Eₖ already, however its ∧
// associates. The rewrite would respell it and give a close nothing more
// to read, so none is returned, and the caller keeps the hypothesis as it
// stands. It does not ask the drop rule, which reads a conjunction as one
// atom the decider proves (droppableRedundantHyp) and would drop the
// equations with it.
func heldEquations(hyps []Term, i int, top *PropWrapper, decide func(Term) *PropWrapper) (rewrite *PropWrapper, stands bool) {
	isLiteral := func(t Term) bool {
		if inner := ext.MatchesNOT(t); inner != nil {
			return isValueEquation(inner)
		}
		return isValueEquation(t)
	}
	if isLiteral(hyps[i]) {
		return nil, false
	}
	var held []Term
	var proofs []*PropWrapper
	take := func(lit Term) {
		atom := lit
		if inner := ext.MatchesNOT(lit); inner != nil {
			atom = inner
		}
		if l, r, _ := MatchesEQ(atom); l.AlphaEquals(r) {
			return
		}
		if slices.ContainsFunc(held, lit.AlphaEquals) || spelledElsewhere(hyps, i, lit) {
			return
		}
		w := decide(lit)
		if w == nil || !Rhs(w).Equals(T) {
			return
		}
		held = append(held, lit)
		proofs = append(proofs, prop.BooleanThms["p ⇔ ⊤"](lit).EqMP(w)) // Γ ⊢ lit
	}
	var walk func(t Term)
	walk = func(t Term) {
		if isLiteral(t) {
			// Whichever of the equation and its negation holds.
			take(t)
			if inner := ext.MatchesNOT(t); inner != nil {
				take(inner)
			} else {
				take(ext.Apply(prop.NOT, t))
			}
			return
		}
		if inner := ext.MatchesNOT(t); inner != nil {
			walk(inner)
			return
		}
		for _, match := range []func(Term) (Term, Term, bool){prop.MatchesAND, prop.MatchesOR, ext.MatchesIMPLY} {
			if l, r, ok := match(t); ok {
				walk(l)
				walk(r)
				return
			}
		}
		if l, r, ok := MatchesEQ(t); ok && IsBool(l) {
			walk(l)
			walk(r)
		}
	}
	walk(hyps[i])
	if len(held) == 0 {
		return nil, false
	}
	if slices.EqualFunc(conjuncts(hyps[i]), held, Term.AlphaEquals) {
		return nil, true
	}
	conj, proof := held[0], proofs[0]
	for j := 1; j < len(held); j++ {
		both := prop.ConclAND(conj, held[j]).DeriveHypFrom(proof).DeriveHypFrom(proofs[j]) // Γ ⊢ conj ∧ Eⱼ
		conj, proof = both.Conclusion(), both
	}
	conjTrue := prop.BooleanThms["p ⇔ ⊤"](conj).EqSym().EqMP(proof) // Γ ⊢ conj = ⊤
	return top.EqTrans(conjTrue.EqSym()), false                     // Γ ⊢ hyps[i] = conj
}

// conjuncts is t read through its conjunctions, however they associate:
// the terms no ∧ joins, left to right.
func conjuncts(t Term) []Term {
	l, r, ok := prop.MatchesAND(t)
	if !ok {
		return []Term{t}
	}
	return append(conjuncts(l), conjuncts(r)...)
}

// arithValueTerm reports whether t is a first-order VALUE term — not a
// formula (bool) and not function-typed. These are the positions the CNF
// refuter can paramodulate on, hence the positions where an arith rewrite
// can destroy downstream reach.
func arithValueTerm(t Term) bool {
	return !IsBool(t) && !ext.IsFunType(t.Type())
}

// droppableRedundantHyp decides whether a hyp the arith decider proved
// redundant (⇔ ⊤ under the other hyps) may still be DROPPED — see the
// RETENTION comment in arithRewriteTactic. Droppable means the
// redundancy is visible literal-by-literal, so no downstream syntactic
// consumer loses content:
//
//   - trivially true for the logic-only simplifier (refl `t = t`, ⊤), or
//   - some single literal of the hyp's clause spine (∨-disjuncts, ⇒
//     antecedents negated) is INDIVIDUALLY arith-⊤ with a non-equality
//     atom — the tautological-clause case (`X ⇒ (r ≤ r)`, `0 ≤ x ∨ P`).
//
// NOT droppable (retained): a true value-level (dis)equality in any
// polarity/position (paramodulation food the refuter cannot re-derive),
// and a collectively-true disjunction with no individually-⊤ literal
// (a case-split license — `(m=0) ∨ (0<m)`).
func droppableRedundantHyp(hyp Term, decide func(Term) *PropWrapper) bool {
	if IsTrivial(MakeProp(hyp)) {
		return true
	}
	return hasTautologyWitness(hyp, false, decide)
}

// hasTautologyWitness walks the ∨/⇒ clause spine of t looking for a single
// literal that is individually arith-true in its polarity (negated =
// "counts as true when it decides ⊥") with a non-equality atom. Equality
// atoms never witness a drop — a true equation (or true disequation) is
// exactly the content the retention rule exists to keep.
func hasTautologyWitness(t Term, negated bool, decide func(Term) *PropWrapper) bool {
	if a, b, ok := ext.MatchesIMPLY(t); ok && !negated {
		return hasTautologyWitness(a, true, decide) ||
			hasTautologyWitness(b, false, decide)
	}
	if l, r, ok := prop.MatchesOR(t); ok && !negated {
		return hasTautologyWitness(l, false, decide) ||
			hasTautologyWitness(r, false, decide)
	}
	if inner := ext.MatchesNOT(t); inner != nil {
		return hasTautologyWitness(inner, !negated, decide)
	}
	// Literal. An equality atom never witnesses a drop.
	if l, _, ok := MatchesEQ(t); ok && arithValueTerm(l) {
		return false
	}
	w := decide(t)
	if w == nil {
		return false
	}
	if negated {
		return Rhs(w).Equals(F)
	}
	return Rhs(w).Equals(T)
}

// emitArithBridges makes the arith rewrite's information loss explicit: the
// deep rewrite orig → rewritten replaced value-typed subterms (`0*x` → `0`)
// justified by arithmetic the downstream CNF stage does not have. For each
// maximal changed value-typed position we emit the ground equation
// `orig_sub = rewritten_sub` as an extra hypothesis of the residual goal,
// certified by the SAME decider (so the emission is exactly as strong as the
// rewrite it mirrors, never a fabricated fact). The reconstruct discharges
// the added hyps via the certs, so the parent proof is unchanged.
//
// This is the no-hurt contract of `auto`'s arith fast-path made real: the
// residual is not merely logically equal to the input — it is syntactically
// RICHER, so AutoExpand/CNF reach is monotone. (The counterexample that
// forced this: `(m=0) ∨ (0<m), m*x ≠ 0*x ⊢ 0<m` — rewriting the hyp to
// `m*x ≠ 0` without the `0*x = 0` bridge strands the CNF refuter, which
// could otherwise close the goal by paramodulation + refl.)
//
// Scope: only shape-preserved value positions are recovered by the parallel
// walk (collectRewriteDiffs). An equation atom that vanishes inside a
// COLLAPSING connective (`(0*x = 0) ∧ P → P`) is not — the collapse cascade
// destroys the alignment. The flat-hyp instance of that class is covered by
// the RETENTION rule instead; the nested instance is an accepted gap.
//
// A diff the decider cannot re-certify to ⊤ is skipped (no bridge for
// that position, never blocking the rewrite).
func emitArithBridges(
	orig, rewritten Term,
	existingHyps []Term,
	decide func(Term) *PropWrapper,
) ([]Term, []*PropWrapper) {
	var diffs []Term
	collectRewriteDiffs(orig, rewritten, nil, &diffs)
	var eqs []Term
	var certs []*PropWrapper
	for _, eq := range diffs {
		if slices.ContainsFunc(existingHyps, eq.AlphaEquals) ||
			slices.ContainsFunc(eqs, eq.AlphaEquals) {
			continue
		}
		w := decide(eq)
		if w == nil || !Rhs(w).Equals(T) {
			continue
		}
		// {ctx hyps} ⊢ eq ⇔ ⊤   →   {ctx hyps} ⊢ eq
		certs = append(certs, w.EqSym().EqMP(prop.DerivesTrue))
		eqs = append(eqs, eq)
	}
	return eqs, certs
}

// collectRewriteDiffs walks orig/rewritten in parallel and appends to out
// the maximal changed value-typed subterm pairs as equations. Recursion
// descends only through preserved shape (same application spine, same
// binder); a value-typed mismatch is collected whole (its function-position
// or deeper diffs are subsumed by the maximal equation). Diffs mentioning a
// bound variable of an enclosing binder are not sequent-level facts and are
// skipped.
func collectRewriteDiffs(orig, rewritten Term, boundNames []TermName, out *[]Term) {
	if orig.AlphaEquals(rewritten) {
		return
	}
	if arithValueTerm(orig) && orig.Type().Equals(rewritten.Type()) {
		for _, n := range boundNames {
			if orig.HasName(n) || rewritten.HasName(n) {
				return
			}
		}
		*out = append(*out, Eq(orig, rewritten))
		return
	}
	if ao, ok := orig.AsAppliedTerm(); ok {
		if ar, ok := rewritten.AsAppliedTerm(); ok {
			collectRewriteDiffs(ao.Fun(), ar.Fun(), boundNames, out)
			collectRewriteDiffs(ao.Arg(), ar.Arg(), boundNames, out)
		}
		return
	}
	if bo, ok := orig.AsAbsTerm(); ok {
		if br, ok := rewritten.AsAbsTerm(); ok && bo.Var().Equals(br.Var()) {
			collectRewriteDiffs(
				bo.Body(), br.Body(), append(boundNames, bo.Var().Name()), out)
		}
		return
	}
	// Different node shapes at formula/function level: a connective collapsed
	// (`⊥ ∨ P → P`); no shape-preserved bridge to extract here.
}

// OmegaTactic is LinarithTactic over the sound integer core (omega.OmegaProve:
// ℚ-Farkas strengthened with the GCD-equality test and rank-1 rounding cuts).
// Same goal shapes as LinarithTactic, but additionally closes goals that need
// integrality, e.g. `{b < a+1} ⊢ b ≤ a` or `2*a ≠ 1`.
//
// Strategy: try ℚ-Farkas first (LinProve), then fall back to the integer
// extension (OmegaProve). The integer extension DECLINES (returns ok=false,
// no fabricated cert) for the unsupported frontier shapes — general rank-k cuts
// and general two-sided gcd-equality (the rank-1 cut + grounded-gcd common
// cases are real); pure-linear goals close because they never hit those.
func OmegaTactic(goal Prop) *SubGoals {
	// Pure ℚ-Farkas path.
	if r := LinarithTactic(goal); r != nil {
		return r
	}
	// Integer extension path: declines via ok=false on unsupported frontier shapes.
	w, ok := omega.OmegaProve(goal.HypIter(), goal.Conclusion())
	return closeByOmega(goal, w, ok)
}

// ExpandExpTactic is the agent-controlled expansion of EVERY literal-exponent
// nat_pow atom in the goal (conclusion or first matching hyp) into a product chain
// `m·m·…·m`. Decoupled from ArithTactic: unifying it into arith would expand
// `nat_pow(complex_base, c)` for c ≥ 2 BY SURPRISE, which can grow term size
// dramatically (a complex polynomial raised to a high power explodes after the
// rewrite + ring expansion) — agents need to be able to choose when to pay that
// cost. ArithTactic still auto-fires the harmless `nat_pow(_, 0)→1` and
// `nat_pow(_, 1)→_` reductions through expSimp, so notation-cleanup is automatic;
// only the size-changing c ≥ 2 expansion is gated here.
//
// Typical usage in a script: `expand_exp` then `arith` — the expansion sets up
// the product form, ring/linarith closes the resulting polynomial identity.
// Non-literal exponents and atoms beyond the cap (expUnfoldMax = 32) are left
// untouched.
func ExpandExpTactic(goal Prop) *SubGoals {
	return rewriteTactic(omega.ExpandEXPRewrite())(goal)
}
