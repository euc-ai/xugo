package prop

import (
	"fmt"
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/utils"
	"os"
)

// Verify that the result prop is indeed a rewrite of the given term.
func verifyRewrite(r Rewrite) Rewrite {
	return func(t Term) *PropWrapper {
		w := r(t)
		if w != nil {
			Assert(t.AlphaEquals(Lhs(w)) &&
				!t.AlphaEquals(Rhs(w)) &&
				w.NumHyps() == 0)
		}
		return w
	}
}

// verifyRewriteOpen is verifyRewrite for a rewrite built over CALLER-
// SUPPLIED law closures (AssocRewrite, ArrangeChain, BinaryOpSortRewrite):
// the shape is checked, the hypothesis count is not. The package's own
// rewrites are closed by construction and keep the strict check; a
// structure ring's laws are read at a resident structure fact and carry
// it as a hypothesis (prover/solver/omega/structure_ring.go), which the
// drivers compose exactly as they compose any hypothesis-carrying
// equation (DeepRewriteWithEnv's anyHyp contract).
func verifyRewriteOpen(r Rewrite) Rewrite {
	return func(t Term) *PropWrapper {
		w := r(t)
		if w != nil {
			Assert(t.AlphaEquals(Lhs(w)) && !t.AlphaEquals(Rhs(w)))
		}
		return w
	}
}

func combineAppliedRewrite(t AppliedTerm, funEq, argEq *PropWrapper) *PropWrapper {
	if funEq != nil && argEq != nil {
		return funEq.Apply(argEq)
	} else if funEq != nil {
		return funEq.RightApply(t.Arg())
	} else if argEq != nil {
		return argEq.LeftApply(t.Fun())
	}
	return nil
}

// Given a rewrite, rewrites the sub terms of the given term.
// this is not a recursive function. It just rewrite the immediate subterms.
// this is a helper function, should not be used directly.
//
// α-capture guard on the AbsTerm case: `thm.Abs(v)` requires `v ∉ FV(hyps
// of thm)` — the kernel's PropAbs side condition (core/primitives.go).
// A composed leaf rewrite (e.g. ContextEqRewrite loaded from a rule with
// un-∀-quantified top-level free variables — a lemma stated with free
// vars, like set_algebra.DoubleComplement's
// `⊢ set_difference(universe, set_difference(universe, s)) = s`) can return an eq whose hypothesis
// carries those free vars. When the enclosing AbsTerm binds a same-named
// variable, `thm.Abs(v)` would violate the side condition; skipping the
// fire is sound (semantically the leaf α-blindly matched the binder's v
// against its own free v — these are distinct under α-equivalence, so
// the correct behavior at this position IS "no rewrite"). See the
// env-aware sibling `RewriteSubTermsWithEnv` which handles the same
// hazard by α-renaming the binder before recursing; here we can't rename
// (would invalidate the memo cache keying on the outer term pointer) so
// we drop the fire.
func rewriteSubTerms(rewrite Rewrite) Rewrite {
	return func(t Term) *PropWrapper {
		switch t := t.Core().(type) {
		case AppliedTerm:
			return combineAppliedRewrite(t, rewrite(t.Fun()), rewrite(t.Arg()))
		case AbsTerm:
			if thm := rewrite(t.Body()); thm != nil {
				v := t.Var()
				if thm.AnyHyp(utils.Curry(Term.HasFree, v)) {
					return nil
				}
				return thm.Abs(v)
			}
		}
		return nil
	}
}

// Converts a term t to a thm in the form of ⊢ t = ...
// while considering the abstracted vars of the term.
// For example, if we want to rewrite P(x, y) in λx.P(x, y), then the env is [x].
// The abstracted vars are the vars that are bound by the lambda abstraction.
type RewriteWithEnv func(Term, ...VarTerm) *PropWrapper

// Given a rewrite with env, rewrites the sub terms of the given term.
// The second arg is a check to make sure that when rewriting the terms
// inside abstracted vars, those vars won't conflict with the hyps of the proposition.
// This may happen during the eq rewrite, where the eq prop usually comes with hyps.
// this is not a recursive function. It just rewrite the immediate subterms.
// this is a helper function, should not be used directly.
//
// A λ whose variable is free in a hypothesis, or is one env already holds
// (an inner binder shadowing an outer one), is entered under a fresh name:
// one that neither its body, nor the hypotheses, nor env uses. So env
// never holds a variable twice. A rewrite that reads env for the binders
// a site stands under (unifyEqRewriteGuarded wraps the site in the ones
// free in it) would count a doubled variable as two binders, find one
// more than its rule abstracts, and leave the site unrewritten.
func RewriteSubTermsWithEnv(
	rewriteWithEnv RewriteWithEnv,
	anyHyp func(func(Term) bool) bool) RewriteWithEnv {

	return func(t Term, env ...VarTerm) *PropWrapper {
		switch t := t.Core().(type) {
		case AppliedTerm:
			return combineAppliedRewrite(
				t,
				rewriteWithEnv(t.Fun(), env...),
				rewriteWithEnv(t.Arg(), env...))
		case AbsTerm:
			if anyHyp(utils.Curry(Term.HasFree, t.Var())) ||
				utils.Any(env, t.Var().EqualsVar) {
				n := t.Var().Name()
				for t.Body().HasName(n) ||
					anyHyp(utils.Curry(Term.HasName, n)) ||
					utils.Any(env, func(v VarTerm) bool { return v.Name() == n }) {
					n = utils.NextName(n)
				}
				t = t.ChangeAbsVar(n)
			}
			if thm := rewriteWithEnv(
				t.Body(),
				utils.CloneAppend(env, t.Var())...); thm != nil {
				return thm.Abs(t.Var())
			}
		}
		return nil
	}
}

// envScopeCache is the deep-rewrite instantiation of the engine's
// env-scoped shared-DAG memo (see EnvMemo in ext/subterm.go): results are
// memoized per (binder-env content, term pointer) within one top-level
// rewrite call. The memoized rewrites must be pure functions of
// (term, env).
type envScopeCache = ext.EnvMemo[*PropWrapper]

// Given a set of shallow rewrites, returns a merged rewrite that recurses through
// subterms (applying any rewrite that fires, then continuing into
// the rewritten form). Used by callers outside prop that need a
// deep-rewrite primitive without owning the merge logic themselves.
//
// Shared-DAG memoization, size-gated (see ext/subterm.go): the composed
// rewrites are PURE functions of the input term (no env, no hidden
// state), so within one top-level call the result of rewrite(t) is
// fully determined by t's pointer identity, and caching it collapses
// the naive O(2^depth) walk over pointer-shared subtrees to O(unique
// nodes). Package-level rewrites like DeepBeta run millions of times
// per sweep on small terms — the nil-cache path allocates nothing.
func DeepRewrite(rewrites ...Rewrite) Rewrite {
	return deepRewriteImpl("", rewrites...)
}

// deepRewriteCarrying is DeepRewrite over leaves that fire only on terms
// in which name occurs: a subterm without name is not entered (core
// memoizes HasName per node), so a walk costs the part of the term that
// carries name. The result is DeepRewrite's.
func deepRewriteCarrying(name core.TermName, rewrites ...Rewrite) Rewrite {
	return deepRewriteImpl(name, rewrites...)
}

// WhistledRewrite is a deep rewrite under the divergence whistle
// (DeepRewriteWhistled). cut is nil unless the whistle ended the call. w
// is then the equality the walk had built when it was cut: sound, and
// its right side a term the rules were still rewriting, which the
// normalizer among the leaves may not have reached. A caller that goes
// on from a cut goes on from no normal form.
type WhistledRewrite func(t Term) (w *PropWrapper, cut *skeleton.WhistleEvent)

// DeepRewriteWhistled is DeepRewriteWithEnv with a per-top-call divergence
// whistle on the composed leaves' FIRE events. Use it when the leaves
// are RULE-FED — lemma or unification rewrites whose
// termination nobody proved, e.g. the multi-clause LeanRw composition —
// and the result is best-effort simplification rather than a
// normalization contract. Chapter algorithmic compositions (DeepBeta,
// DeepBoolRewrite, ...) stay on plain DeepRewrite: their termination is
// by construction, and the whistle's over-approximation must not
// truncate them.
//
// A rule-fed leaf carries its rule as a hypothesis, and the walk hands it
// a binder's body, where the bound variable reads as free. anyHyp names
// those hypotheses (DeepRewriteWithEnv's contract), so a binder colliding
// with a rule's free variable is renamed before descent: a bound
// occurrence never fires as the rule's own variable, and the whistle
// never counts a fire no lift could keep.
//
// The whistle is at fire granularity, not loop granularity, because a
// self-feeding leaf diverges by NESTING — step fires once, hands the
// output to a rescan, which fires once, hands down again — so no single
// RewriteConclRhsRecur loop ever iterates twice and a loop-level check
// counts nothing. Instead every successful leaf fire in one top-level
// call passes through a shared fireWhistle with three blades (see
// fireWhistle.allow): an ordered-permutation gate (permutation-class
// fires must strictly decrease the structural order — the ordered-rewriting
// discipline, the exact cut for COMM-class
// permutative storms; see skeleton.PermutationFireAllowed) and a
// consecutive-growth chain backstop, both engaged from fire #1, plus
// the trajectory check, which engages past a budget of fires: the entry
// term's size (a chain consuming pre-existing structure fires at most
// once per node of the entry term — rwFixpoint's budget argument), and
// no fewer than two fires for each leaf (a cascade through every rule at
// one site is a fire of each rule and a normalizer's fire after it,
// whatever the entry's size). Past the budget, a fire whose RHS
// path-embeds an earlier recorded RHS is refused. The growth-chain blade
// exists because the trajectory check alone engages far too late on
// mutually-feeding expansive rule sets (the simp_with pin of
// cardinality.HasSizeClauses with comprehension membership): its budget
// window admits entry-size-many unchecked fires, each paying a full
// HO-unification walk over a growing term.
//
// The first fire the growth chain or the trajectory refuses is the
// call's CUT, and it ends the call: the walk takes no further leaf and
// enters no further node, every rescan loop on the stack exits at its
// next turn, and the equality built so far comes back with the cut's
// event. Refusing the one fire and walking on does not end a divergent
// call at a bounded cost — the leaves are deep rewrites, so the refused
// redex is found again from each node around it as a different pair of
// terms, some of which pass, and each offer pays the leaf's unification
// walk. An ordering decline of the first blade is no cut: the leaf did
// not match there, and the walk goes on.
//
// There is deliberately NO single-fire RHS-size cap: a lone fire's size
// is bounded a priori by rule-template size + captured-argument sizes,
// so a "big" single fire only witnesses a big TEMPLATE (a definitional
// expansion — set unfolds of the intersection-of / union-of class routinely
// exceed any entry-relative constant on small goals), never divergence,
// which is a property of fire SEQUENCES (the two eager blades above). A
// removed max(64, 2×entry) cap suppressed exactly such legitimate
// expansions and — whistle policy being part of replay semantics —
// baked the suppression into proofs recorded while it was live.
// Termination:
// the recorded RHSs form an antichain-like sequence in the (size,
// path-set) WQO (Higman + Dickson), hence finite, so every call that
// does not reach its fixpoint is cut; and a call costs the fires it was
// allowed, the budget and that antichain, since nothing runs after the
// cut.
//
// The cut is reported (skeleton.ReportWhistleFire) and handed to the
// caller, whose fixpoint around the call ends with it.
func DeepRewriteWhistled(anyHyp func(func(Term) bool) bool, rewrites ...Rewrite) WhistledRewrite {
	walk := DeepRewriteWhistledUnreported(anyHyp, rewrites...)
	return func(t Term) (*PropWrapper, *skeleton.WhistleEvent) {
		w, cut := walk(t)
		if cut != nil {
			skeleton.ReportWhistleFire(*cut)
		}
		return w, cut
	}
}

// DeepRewriteWhistledUnreported is DeepRewriteWhistled telling its caller
// alone of a cut: the whistle's counter, its watches and its hook hear
// nothing. It is for the reader of a cut a step has already reported —
// the wording of that step's refusal (tactic.SimpCut) — and no step
// runs it.
func DeepRewriteWhistledUnreported(anyHyp func(func(Term) bool) bool, rewrites ...Rewrite) WhistledRewrite {
	// Whistle state is per top-level call, so the closure pair is rebuilt
	// per call (the lemma-fed compositions are not the millions-per-sweep
	// hot path the plain variant serves). The memo gate is read at entry
	// only: a memo hit skips a fire's count, so the memo is part of the
	// whistle policy, which replay reproduces.
	return func(t Term) (*PropWrapper, *skeleton.WhistleEvent) {
		fw := &fireWhistle{
			budget:         max(t.Size(), 2*len(rewrites)),
			growthBackstop: max(_FIRE_GROWTH_FLOOR, len(rewrites)+1),
		}
		w := envWalk(ext.EnvMemoFor[*PropWrapper](t), fw, anyHyp, rewrites)(t)
		if !fw.cut {
			return w, nil
		}
		return w, &skeleton.WhistleEvent{
			Driver: "DeepRewriteWhistled",
			Depth:  fw.fires,
			Budget: fw.budget,
			Term:   t,
		}
	}
}

// _FIRE_GROWTH_FLOOR is the minimum growth-chain backstop — the number
// of CONSECUTIVE growing fires (fires whose LHS path-embeds into a
// no-smaller RHS) a whistled top call may always take, regardless of
// how few rules it composes. The EFFECTIVE backstop is
// max(_FIRE_GROWTH_FLOOR, len(rewrites)+1) — see fireWhistle
// construction: the longest LEGITIMATE consecutive-growth run is a
// definitional cascade (rule i's RHS exposes the head rule j unfolds —
// set_member → set_comprehension → comprehension_spec …), whose length is bounded by the longest
// acyclic path in the composition's rule-feed graph, hence by the rule
// COUNT; a run longer than that must revisit a rule on structure a
// prior fire manufactured — the mutually-feeding tower signature. The
// growth blade exists because the trajectory check below is too slow
// to engage on such towers (simp_with over
// HasSizeClauses with comprehension membership is one — each rule's RHS creates fresh
// redexes for the other, at interleaved subterm positions whose local
// RHSs almost never embed one another, so the WQO antichain stretches
// for hundreds of fires while every ALLOWED fire pays a full
// HO-unification walk over the growing term: a wall-clock pin long
// before the guaranteed Kruskal cut). That tower composes 2 rules —
// effective backstop 3, the floor, so it is cut promptly; larger rule
// sets scale their allowance with the only static quantity that bounds
// legitimate cascade depth. Scaling with len(rewrites) only ever ALLOWS
// more than the floor of 3, and the floor does not move: a recorded
// proof replays with the fires it was recorded with — whistle policy is
// part of replay semantics.
const _FIRE_GROWTH_FLOOR = 3

// fireWhistle is the shared per-top-call state of DeepRewriteWhistled.
// Single-goroutine, like the memo caches.
type fireWhistle struct {
	budget         int // fires up to this skip the trajectory check: the entry term's size, two for each leaf at least
	growthBackstop int // max(_FIRE_GROWTH_FLOOR, len(rewrites)+1) — see the floor's comment
	fires          int
	cut            bool                     // a blade refused a fire as divergent: the call is over
	growthRun      int                      // consecutive growing fires so far (reset by any non-growing fire)
	traj           *skeleton.TermTrajectory // recorded post-budget fire RHSs
}

// ended reports that the call was cut. A nil whistle, the unwhistled
// walk's, never is.
func (fw *fireWhistle) ended() bool { return fw != nil && fw.cut }

// allow reports whether a fire rewriting lhs to rhs may proceed,
// recording it if so. Three blades, cheapest first:
//
//  1. Ordered-permutation gate (from fire #1): a permutation-class fire
//     (see skeleton.PermutationFireAllowed) must strictly DECREASE the
//     total structural order — the exact cut for COMM-class permutative
//     storms, which the other blades cannot see.
//  2. Growth-chain backstop (from fire #1): more than
//     growthBackstop consecutive fires whose LHS embeds into a
//     no-smaller RHS. Any non-growing fire resets the run.
//  3. The trajectory whistle (past the budget only): completeness
//     backstop via Kruskal on the recorded-RHS antichain.
//
// A fire the first blade declines did not match: the walk goes on to the
// next leaf. A fire the second or the third refuses is the call's cut
// (fw.cut), after which the walk takes nothing more. Both are sound —
// the unrewritten subterm stands — and best-effort by contract:
// rule-fed callers are simplifiers, not normalizers.
func (fw *fireWhistle) allow(lhs, rhs Term) bool {
	fw.fires++
	if !skeleton.PermutationFireAllowed(lhs, rhs) {
		// Ordered-rewriting decline: deterministic orientation discipline,
		// not a divergence cut, and not reported as one — the corpus replay
		// harness asserts whistle-freedom, and ordering declines are part
		// of normal, replay-stable operation (a sorted position declines
		// its increasing flip on every pass), exactly like unifyEq's
		// IsSub-guard declines.
		return false
	}
	if rhs.Size() >= lhs.Size() && skeleton.PathEmbeds(skeleton.EmbPaths(lhs), skeleton.EmbPaths(rhs)) {
		fw.growthRun++
		if fw.growthRun > fw.growthBackstop {
			fw.cut = true
			return false
		}
	} else {
		fw.growthRun = 0
	}
	if fw.fires <= fw.budget {
		return true
	}
	next := fw.traj.Extend(rhs)
	if next.EmbedsAncestor() {
		fw.cut = true
		return false
	}
	fw.traj = next
	return true
}

// deepRewriteTrace is diagnostic instrumentation for the PLAIN (unwhistled)
// DeepRewrite, gated by XUGO_DEEPREWRITE_TRACE and inert otherwise:
//
//	"count" — track fires per top-level call; print a line to stderr each
//	          time a new maximum of fires/entry-size is reached (bounded
//	          volume), so a corpus replay yields the legitimate envelope.
//	"trace" — additionally print every fire (lhs head, lhs→rhs sizes) once a
//	          top call has exceeded deepRewriteTraceAfter fires, capped at
//	          deepRewriteTraceMax lines — the divergent call's own fire log.
//
// Single-goroutine per top call like the memo caches; the max is a plain
// package var because the trace is a diagnostic run, not a hot path.
var deepRewriteTraceMode = os.Getenv("XUGO_DEEPREWRITE_TRACE")

const (
	deepRewriteTraceAfter = 200
	deepRewriteTraceMax   = 400
)

var deepRewriteMaxRatio float64

type deepRewriteTraceState struct {
	size   int
	fires  int
	logged int
}

func (st *deepRewriteTraceState) fire(rule int, lhs, rhs Term) {
	st.fires++
	if deepRewriteTraceMode == "trace" && st.fires > deepRewriteTraceAfter && st.logged < deepRewriteTraceMax {
		st.logged++
		head := "?"
		if f, _ := ext.MatchesApply(lhs); f != nil {
			if c, ok := f.AsConst(); ok {
				head = string(c.Name())
			} else {
				head = "var/abs"
			}
		} else if _, ok := lhs.AsAbsTerm(); ok {
			head = "λ"
		}
		fmt.Fprintf(os.Stderr, "[deeprewrite-trace] fire#%d rule=%d head=%s lhs=%d rhs=%d\n", st.fires, rule, head, lhs.Size(), rhs.Size())
		if st.logged <= 4 {
			l, r := ext.FormatTerm(lhs, false), ext.FormatTerm(rhs, false)
			if len(l) > 260 {
				l = l[:260] + "…"
			}
			if len(r) > 260 {
				r = r[:260] + "…"
			}
			fmt.Fprintf(os.Stderr, "[deeprewrite-trace]    LHS: %s\n[deeprewrite-trace]    RHS: %s\n", l, r)
		}
	}
}

func (st *deepRewriteTraceState) finish() {
	if st.size == 0 {
		return
	}
	r := float64(st.fires) / float64(st.size)
	if r > deepRewriteMaxRatio {
		deepRewriteMaxRatio = r
		fmt.Fprintf(os.Stderr, "[deeprewrite-count] new max fires/size=%.2f fires=%d size=%d\n", r, st.fires, st.size)
	}
}

// deepRewriteImpl enters only subterms carrying name; the empty name
// enters every subterm.
func deepRewriteImpl(name core.TermName, rewrites ...Rewrite) Rewrite {
	// step is one uncached recursion level. The rewrite/subTermsRewrite
	// params select the plain or memoized recursion.
	step := func(t Term, rewrite, subTermsRewrite Rewrite) *PropWrapper {
		// check whether the current level can be rewritten.
		for _, r := range rewrites {
			if s := r(t); s != nil {
				return s.RewriteConclRhsRecur(rewrite)
			}
		}
		if s := subTermsRewrite(t); s != nil {
			return s.RewriteConclRhsRecur(rewrite)
		}
		return nil
	}

	type stepFn = func(t Term, rewrite, subTermsRewrite Rewrite) *PropWrapper

	// makeRewrite builds one recursion pair; a nil cache is the plain
	// zero-allocation path. The walk reads the memo gate at every term it
	// meets, not only at its entry: a fire rebuilds the term, a walk
	// entered below the gate can grow far past it (each COND elimination
	// copies its atom), and an unmemoized walk re-walks an ancestor's
	// whole subtree after every fire below it. So the plain path hands a
	// term above the gate to a memoized pair rooted there.
	var makeRewrite func(cache *ext.PtrMemo[*PropWrapper], step stepFn) Rewrite
	makeRewrite = func(cache *ext.PtrMemo[*PropWrapper], step stepFn) Rewrite {
		var rewrite, subTermsRewrite Rewrite
		rewrite = func(t Term) *PropWrapper {
			if name != "" && !t.HasName(name) {
				return nil
			}
			if cache == nil && ext.NaiveWalkNeedsMemo(t) {
				return makeRewrite(ext.PtrMemoFor[*PropWrapper](t), step)(t)
			}
			if w, ok := cache.Load(t); ok {
				return w
			}
			w := step(t, rewrite, subTermsRewrite)
			cache.Store(t, w)
			return w
		}
		subTermsRewrite = rewriteSubTerms(rewrite)
		return rewrite
	}

	// The plain closure pair is predefined so small-term calls (the
	// overwhelming majority) allocate nothing; a call that meets a term
	// above the memo gate builds its own memoized pair there, so the
	// cache never outlives (or races across) a call.
	plain := makeRewrite(nil, step)
	if deepRewriteTraceMode != "" {
		// Diagnostic path only: a per-call counting step. Same walk, same
		// results; the counter observes fires and never declines one.
		return func(t Term) *PropWrapper {
			st := &deepRewriteTraceState{size: t.Size()}
			counting := func(t Term, rewrite, subTermsRewrite Rewrite) *PropWrapper {
				for k, r := range rewrites {
					s := r(t)
					if s == nil {
						continue
					}
					st.fire(k, t, Rhs(s))
					return s.RewriteConclRhsRecur(rewrite)
				}
				if s := subTermsRewrite(t); s != nil {
					return s.RewriteConclRhsRecur(rewrite)
				}
				return nil
			}
			w := makeRewrite(ext.PtrMemoFor[*PropWrapper](t), counting)(t)
			st.finish()
			return w
		}
	}
	return plain
}

// DeepRewriteWithEnv is the capture-aware sibling of DeepRewrite. It threads the
// abstracted-vars env through the subterm recursion (via RewriteSubTermsWithEnv),
// renaming any binder whose bound var collides with a free var of a hypothesis
// the leaves may carry — reported by anyHyp, the same `Prop.AnyHyp`-shaped
// predicate EqRewrite passes. Use this instead of DeepRewrite when the composed
// leaves can return HYP-CARRYING equalities (e.g. a hyp-conditioned decision
// rewrite): without the renaming, lifting such an equality back through a
// colliding binder via `.Abs()` trips the kernel's `v ∉ FV(hyps)` side condition.
//
// The leaves keep the plain hyp-free Rewrite signature — env is consumed only by
// the renaming inside RewriteSubTermsWithEnv. anyHyp should over-approximate the
// hyps the leaves can carry (e.g. the whole goal hyp set); over-approximation only
// triggers extra α-renames, which are sound and fire only on an actual name clash.
// Shared-DAG memoization mirrors DeepRewrite's, except results here depend
// on the binder env too (the renaming inside RewriteSubTermsWithEnv), so
// the size-gated per-call cache is an envScopeCache keyed by (env content,
// term pointer) rather than a bare term map.
func DeepRewriteWithEnv(anyHyp func(func(Term) bool) bool, rewrites ...Rewrite) Rewrite {
	// The plain closure pair is predefined so small-term calls allocate
	// nothing; the memoized pair is rebuilt per top-level call so the
	// cache never outlives (or races across) a call.
	plain := envWalk(nil, nil, anyHyp, rewrites)
	return func(t Term) *PropWrapper {
		if cache := ext.EnvMemoFor[*PropWrapper](t); cache != nil {
			return envWalk(cache, nil, anyHyp, rewrites)(t)
		}
		return plain(t)
	}
}

// envWalk builds one recursion pair of the capture-aware deep rewrite; a
// nil cache is the unmemoized walk, a nil fw the unwhistled one. Once fw
// is cut the walk tries no leaf and enters no node: each call on the
// stack returns what it has built.
func envWalk(
	cache *envScopeCache, fw *fireWhistle,
	anyHyp func(func(Term) bool) bool, rewrites []Rewrite) RewriteWithEnv {

	var rewrite, subTermsRewrite RewriteWithEnv
	rewrite = func(t Term, env ...VarTerm) *PropWrapper {
		if fw.ended() {
			return nil
		}
		if w, ok := cache.Load(env, t); ok {
			return w
		}
		recur := func(u Term) *PropWrapper { return rewrite(u, env...) }
		var w *PropWrapper
		for _, r := range rewrites {
			if s := r(t); s != nil {
				if fw != nil && !fw.allow(t, Rhs(s)) {
					if fw.cut {
						// The fire is the call's cut: t stands.
						return nil
					}
					// An ordering decline: this leaf did not match.
					continue
				}
				w = s.RewriteConclRhsRecur(recur)
				break
			}
		}
		if w == nil {
			// The subterm-lifted result carries no new fire of its own —
			// the deeper fires were already whistle-checked inside.
			if s := subTermsRewrite(t, env...); s != nil {
				w = s.RewriteConclRhsRecur(recur)
			}
		}
		cache.Store(env, t, w)
		return w
	}
	subTermsRewrite = RewriteSubTermsWithEnv(rewrite, anyHyp)
	return rewrite
}

// If term t can be rewritten by r, returns the result equality.
// Otherwise returns ⊢ t = t.
func RewriteOrRefl(r Rewrite, t Term) *PropWrapper {
	if w := r(t); w != nil {
		return w
	}
	return Refl(t)
}

// Chains a series of rewrites in order.
func ChainRewrites(rewrites ...Rewrite) Rewrite {
	return chainRewritesUntil(nil, "", rewrites...)
}

// chainRewritesUntil is ChainRewrites with stop polled before each of
// the rewrites; unit names a rewrite of this chain to the cut.
func chainRewritesUntil(stop stopper, unit string, rewrites ...Rewrite) Rewrite {
	return func(t Term) *PropWrapper {
		var w *PropWrapper
		for _, rewrite := range rewrites {
			stop.before(unit)
			if w == nil {
				w = rewrite(t)
			} else {
				w = w.RewriteConclRhs(rewrite)
			}
		}
		return w
	}
}

// stopper is the poll of a rewrite its caller's context can end
// (utils.Stopper): called before a unit of work, it raises a utils.Cut
// naming the unit once the context is done. The nil stopper never cuts:
// it is the poll of every rewrite built at package level, and of a run
// under a context that is never done.
//
// A rewrite takes its stopper where it is built, so the rewrites of a
// run that can be cut are built for that run; what a cut unwinds through
// keeps nothing, the per-call memo of a deep walk included.
type stopper func(where string)

// before polls the stopper before the unit of work named unit.
func (stop stopper) before(unit string) {
	if stop != nil {
		stop(unit)
	}
}

// node is a leaf for a deep rewrite that fires at no term and polls the
// stopper at each term the walk offers it, so a cut waits for one node
// of the walk and not for the walk. unit names the walk.
func (stop stopper) node(unit string) Rewrite {
	return func(Term) *PropWrapper {
		stop(unit)
		return nil
	}
}

// Given a rewrite r, if r(s) = r(t) for terms s and t,
// returns a equality prop ⊢ s = t in that case.
// If r(s) and r(t) are not α-equal, returns nil.
func EqualityFromRewrite(rewrite Rewrite) func(Term, Term) *PropWrapper {
	return func(s, t Term) *PropWrapper {
		if t.AlphaEquals(s) {
			return Refl(s)
		}
		var thm *PropWrapper
		if u := rewrite(s); u != nil {
			thm, s = u, Rhs(u)
			if t.AlphaEquals(s) {
				return thm
			}
		}
		if u := rewrite(t); u != nil && Rhs(u).AlphaEquals(s) {
			if thm == nil {
				return u.EqSym()
			}
			return thm.EqTrans(u.EqSym())
		}
		return nil
	}
}

// Given a rewrite and a binary op decomposer, returns a rewrite that
// rewrites each decomposed term then chains together in the original order.
func decomposeMapRewrite(
	opConst ConstTerm,
	m ext.BinaryOpMatcher,
	rewrite Rewrite) Rewrite {
	var rewriteMap Rewrite
	rewriteMap = func(t Term) *PropWrapper {
		if l, r, ok := m(t); ok {
			// we don't concurrently run because the number of decomposed
			// terms is usually small.
			sl, sr := rewriteMap(l), rewriteMap(r)
			if sl != nil && sr != nil {
				return sl.LeftApply(opConst).Apply(sr)
			} else if sl != nil {
				return sl.LeftApply(opConst).RightApply(r)
			} else if sr != nil {
				return sr.LeftApply(t.Core().(AppliedTerm).Fun())
			}
			return nil
		}
		return rewrite(t)
	}
	return rewriteMap
}

// Normalizes equality by ensuring the smaller term appears first.
// For example: b = a becomes a = b if a < b according to comparison.
// This is a shallow rewrite parameterised by the abstracted-vars env: when
// composed deeply via deepSortRewriteWithEnv, comparisons inside binders use
// binder position (α-invariant) rather than raw variable name. Without
// env, sorting `h(a) = h(b)` inside `∃a.…` would key off the bound-var name
// `a`, so the α-rename `∃z.h(z) = h(b)` would sort the operands the other
// way and break α-invariance of the deep sort.
func equalitySortRewriteWithEnv(env []core.VarPair) Rewrite {
	return func(t Term) *PropWrapper {
		if l, r, ok := MatchesEQ(t); ok && l.CompareWithEnv(r, env) > 0 {
			// Build proof that (l = r) ⇔ (r = l) using symmetry of equality
			w := CommuteEQ(l, r)
			Assert(t.Equals(Lhs(w)) && w.NumHyps() == 0)
			return w
		}
		return nil
	}
}

var deepEqualitySortRewrite = deepSortRewriteWithEnv(equalitySortRewriteWithEnv)

// Deep variants that descend through ∃ (and other binders that don't change
// the boolean structure of their body), so conjunct/disjunct order inside
// quantifier bodies is canonicalized. The shallow versions only sort at the
// FORALL body level, which leaves a gap: `∃a. B(a) ∧ A(a)` and
// `∃a. A(a) ∧ B(a)` (semantically the same) reach distinct canonical forms.
var deepDisjunctSortRewrite = deepSortRewrite(
	MatchesOR, DecomposesOR, ArrangeORChain, SimplifyDisjunct, AssocORRewrite)
var deepConjunctSortRewrite = deepSortRewrite(
	MatchesAND, DecomposesAND, ArrangeANDChain, SimplifyConjunct, AssocANDRewrite)

// deepSortRewrite lifts a binary-op chain sorter (for ∨ / ∧) into a deep,
// binder-aware rewrite. The generated shallow sorter compares terms with
// CompareWithEnv, so sorting under λ / quantifiers is α-invariant rather
// than depending on the concrete names of bound variables.
func deepSortRewrite(
	matcher ext.BinaryOpMatcher,
	decompose ext.BinaryOpDecomposer,
	chainArrangement ChainArrangement,
	simplifyRewrite, assocRewrite Rewrite,
) Rewrite {
	return deepSortRewriteWithEnv(func(env []core.VarPair) Rewrite {
		return binaryOpSortRewriteWithCompare(
			matcher, decompose, chainArrangement, simplifyRewrite, assocRewrite,
			func(t0, t1 Term) int { return t0.CompareWithEnv(t1, env) })
	})
}

// Lifts an env-aware shallow rewrite to a deep rewrite that descends through
// λ-binders carrying the abstracted-vars env. Mirrors DeepRewrite's recursion
// shape, while reusing the shallow rewrite within each binder scope so subterm
// comparisons inside binders stay α-invariant without per-node closure churn.
func deepSortRewriteWithEnv(makeShallow func([]core.VarPair) Rewrite) Rewrite {
	rootShallow := makeShallow(nil)

	var rewrite func(Rewrite, Term, []core.VarPair) *PropWrapper
	rewrite = func(shallow Rewrite, t Term, env []core.VarPair) *PropWrapper {
		if w := shallow(t); w != nil {
			return w.RewriteConclRhsRecur(func(t Term) *PropWrapper {
				return rewrite(shallow, t, env)
			})
		}

		switch t := t.Core().(type) {
		case core.AppliedTerm:
			return combineAppliedRewrite(
				t,
				rewrite(shallow, t.Fun(), env),
				rewrite(shallow, t.Arg(), env))
		case core.AbsTerm:
			nextEnv := append(env, core.VarPair{V0: t.Var(), V1: t.Var()})
			if thm := rewrite(makeShallow(nextEnv), t.Body(), nextEnv); thm != nil {
				return thm.Abs(t.Var())
			}
		}
		return nil
	}

	return func(t Term) *PropWrapper { return rewrite(rootShallow, t, nil) }
}

// Rewrites the hyps and conclusion of the prop using the given Rewrite.
// Never panic.
// If nothing to Rewrite, just return the original prop.
func (t *PropWrapper) Rewrite(r Rewrite) *PropWrapper {
	t = t.RewriteConcl(r)
	for h := range t.HypIter() {
		if rh := r(h); rh != nil {
			t = rh.RightAssume().DeriveTrans(t)
		}
	}
	return t
}

// Rewrites the prop conclusion using the given rewrite.
// Never panic.
// If nothing to rewrite, just return the original prop.
func (t *PropWrapper) RewriteConcl(r Rewrite) *PropWrapper {
	if u := r(t.Conclusion()); u != nil {
		return u.EqMP(t)
	}
	return t
}

// Rewrites the rhs of the prop conclusion using the given rewrite.
// Never panic.
// If nothing to rewrite, just return the original prop.
func (t *PropWrapper) RewriteConclRhs(r Rewrite) *PropWrapper {
	if u := r(Rhs(t)); u != nil {
		return t.EqTrans(u)
	}
	return t
}

// Recursively rewrites the rhs of the prop conclusion using the given rewrite
// until nothing can be rewritten.
//
// It is the caller's responsibility to guarantee termination — this
// variant is for ALGORITHMIC normalizers that carry their own
// termination proof AND whose output is a contract downstream code
// depends on (CNF distribution's decreasing non-clausal measure, AC
// sort's decreasing inversion count, ε-denote's decreasing ε count,
// binder renaming's structural recursion). Such chains legitimately run
// far past any input-derived budget (CNF blowup is exponential, sorting
// is quadratic) while their intermediate states embed each other, so an
// embedding whistle here would truncate a CORRECT normalization and
// break the caller's contract — "stop early" is kernel-sound but not
// contract-sound. For rule-fed rewrites (lemmas, unification
// rewrites) where termination is genuinely unknown, use
// RewriteConclRhsRecurWhistled.
func (t *PropWrapper) RewriteConclRhsRecur(r Rewrite) *PropWrapper {
	for u := r(Rhs(t)); u != nil; u = r(Rhs(t)) {
		t = t.EqTrans(u)
	}
	return t
}

// RewriteConclRhsRecurWhistled is RewriteConclRhsRecur with the
// divergence whistle: for RULE-FED rescans — lemma /
// unification rewrites whose termination nobody proved — driven by a
// FLAT rewrite function iterated in THIS loop.
//
// CAVEAT: the whistle counts iterations of this one loop. A
// self-nesting composition (a driver whose r internally rescans its
// own output, like DeepRewrite's step) diverges by nesting one-shot
// loops, which this counter never sees — compose through
// DeepRewriteWhistled instead, whose whistle sits at fire granularity.
//
// The backstop before the whistle engages is the ENTRY TERM'S SIZE,
// not a tuned constant: a chain consuming pre-existing structure
// rewrites at most one pattern occurrence per iteration, and the entry
// term cannot host more occurrences than it has nodes (the same budget
// argument as rwFixpoint's pass cap in prover/tactic). Iterations
// beyond that are only reachable by a rule manufacturing its own
// redexes.
//
// Past the backstop, an RHS that path-embeds an earlier post-backstop
// RHS (skeleton.TermTrajectory — over-approximated homeomorphic
// embedding, size-gated) ends the loop; the equality chain built so
// far is returned, which is sound (rule-fed callers are best-effort
// simplifiers, not normalization contracts). Kruskal's tree theorem
// makes the cut inevitable for any infinite chain
// (ext/skeleton/embed.go); shrinking chains are never touched (the
// size gate), so terminating simplification runs of any length
// complete exactly as before.
func (t *PropWrapper) RewriteConclRhsRecurWhistled(r Rewrite) *PropWrapper {
	backstop := Rhs(t).Size()
	n := 0
	var traj *skeleton.TermTrajectory
	for u := r(Rhs(t)); u != nil; u = r(Rhs(t)) {
		t = t.EqTrans(u)
		n++
		if n > backstop {
			traj = traj.Extend(Rhs(t))
			if traj.EmbedsAncestor() {
				skeleton.ReportWhistleFire(skeleton.WhistleEvent{
					Driver: "RewriteConclRhsRecurWhistled",
					Depth:  n,
					Budget: backstop,
					Term:   Rhs(t),
				})
				break
			}
		}
	}
	return t
}

// Recursively rewrites the term using the given rewrite only if
// the new term is smaller than the original term
// until nothing can be rewritten.
func ReduceSizeRewriteRecur(r Rewrite, t Term) *PropWrapper {
	w := r(t)
	if w != nil && Rhs(w).Size() < t.Size() {
		for u := r(Rhs(w)); u != nil && Rhs(u).Size() < Rhs(w).Size(); u = r(Rhs(w)) {
			w = w.EqTrans(u)
		}
		return w
	}
	return nil
}

// Rewrites the prop using the given equality.
func (t *PropWrapper) eqRewrite(eq Prop) *PropWrapper {
	return t.Rewrite(EqRewrite(eq))
}

// Rewrites the rhs of the conclusion using the given equality.
func (t *PropWrapper) eqRewriteConclRhs(eq Prop) *PropWrapper {
	return t.RewriteConclRhs(EqRewrite(eq))
}

// Given an equality ⊢ l = r, replaces l in the conclusion by r.
func (t *PropWrapper) eqReplacementConcl(eq Prop) *PropWrapper {
	return t.RewriteConcl(EqReplacementRewrite(eq))
}

// Given an equality ⊢ l = r, replaces l in the rhs of the conclusion by r.
func (t *PropWrapper) eqReplacementConclRhs(eq Prop) *PropWrapper {
	return t.RewriteConclRhs(EqReplacementRewrite(eq))
}
