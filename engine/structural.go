package engine

import (
	"context"
	"fmt"
	"runtime/debug"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// _StructuralTacticSpec is the single source of truth for the parameterless
// structural tactics in the agent's vocabulary. Each spec drives both:
//
//   - applyTacticOnClone (engine.go): dispatches `apply` calls by name.
//   - collectStructuralMoves (engine.go): enumerates which ones fit the
//     current goal so explore can surface them under `structural_moves`.
//
// Adding a new structural tactic = one entry here; dispatch and enumeration
// pick it up automatically. Without this table the two stayed in sync only
// by convention — easy to drift, easy to add a tactic to dispatch and
// forget the enumerator (or vice versa).
type _StructuralTacticSpec struct {
	name        string
	description string

	// shape, when non-nil, gates BOTH enumeration and direct apply. Used
	// when the underlying tactic technically succeeds on shapes outside
	// what the description claims — `cond_rewrite` is the motivating
	// example: it's `BasicRewritesWith(CondElim, CondSwap)` under the
	// hood, so it fires on any goal where basic rewrite makes progress
	// (e.g. A⇒A → T) even when there's no COND. The shape predicate
	// keeps agent-facing semantics aligned with the description: the
	// enumerator only lists it when COND is present, and direct apply
	// from the agent fails-with-diagnostic on non-COND goals instead of
	// silently doing basic rewrites under a misleading tactic name.
	shape func(core.Prop) bool

	apply func(*proof.GoalStackNode) bool

	// until stands in for apply where one run of the tactic can outlast
	// any budget: it runs under a context and is cut off by it (a
	// utils.Cut), in the dispatch and in the enumeration alike.
	until func(context.Context, *proof.GoalStackNode) bool
}

// run applies the tactic to n, under ctx where the tactic reads one.
func (spec *_StructuralTacticSpec) run(ctx context.Context, n *proof.GoalStackNode) bool {
	if spec.until != nil {
		return spec.until(ctx, n)
	}
	return spec.apply(n)
}

var structuralTacticSpecs = []_StructuralTacticSpec{
	{
		name:        "strip_imp",
		description: "concl is A ⇒ B (move antecedent into hypotheses)",
		apply:       proof.ApplyStripImp,
	},
	{
		name:        "split_conj",
		description: "concl is A ∧ B (split into two subgoals)",
		apply:       proof.ApplySplitConj,
	},
	{
		name:        "split_conj_all",
		description: "concl is A ∧ B ∧ … (flatten the whole ∧-spine into N flat subgoals at once)",
		// Shape-gated to ≥3 leaf conjuncts: on a plain binary A∧B it
		// would produce exactly what split_conj does, so suppress it
		// there to keep `inspect` free of a redundant move. The agent
		// still gets split_conj for the binary case.
		shape: conclIsWideConj,
		apply: proof.ApplySplitConjAll,
	},
	{
		name:        "split_disj",
		description: "a hypothesis is A ∨ B (case-analyze the disjunction)",
		apply:       proof.ApplySplitDisj,
	},
	{
		name:        "strip_quant",
		description: "concl is ∀x. … or a hypothesis is ∃x. … (peels the WHOLE leading ∀-prefix of the conclusion in one apply, or Skolemizes the first ∃-hypothesis; with hyp_index, Skolemizes THAT ∃-hypothesis and leaves the conclusion alone)",
		apply:       proof.ApplyStripQuant,
	},
	{
		name:        "split_iff",
		description: "concl is A ⇔ B (split into A ⊢ B and B ⊢ A)",
		shape:       conclIsIff,
		apply:       proof.ApplySplitIff,
	},
	{
		name:        "split_hyp_iff",
		description: "a hypothesis is A ⇔ B (case-analyze: A,B ⊢ C and ¬A,¬B ⊢ C)",
		shape:       hypHasIff,
		apply:       proof.ApplySplitHypIff,
	},
	{
		name:        "split_hyp_imply",
		description: "a hypothesis is A ⇒ B (case-analyze: ¬A ⊢ C and B ⊢ C)",
		shape:       hypHasImply,
		apply:       proof.ApplySplitHypImply,
	},
	{
		name:        "cond_rewrite",
		description: "goal contains COND(c,a,b) (eliminate or push out)",
		shape:       goalContainsCond,
		apply:       proof.ApplyCondRewrite,
	},
	// LEAN-style additions. `assumption` / `refl` / `left` / `right` /
	// `funext` / `symm` / `congr` are parameterless and shape-gated — each
	// fires on a specific equality/disjunction shape that the agent might
	// reach for by its LEAN name. `by_contra` is intentionally NOT in this
	// table (its shape predicate would fire on essentially every non-⊥
	// goal, drowning out higher-signal facts in `inspect`); it is dispatched
	// via the parameterized arm in runTacticOnClone instead.
	{
		name:        "assumption",
		description: "concl α-equals some hypothesis (close immediately)",
		shape:       conclMatchesHyp,
		apply:       proof.ApplyAssumption,
	},
	{
		name:        "refl",
		description: "concl is `t = t` (close by reflexivity)",
		shape:       conclIsReflEq,
		apply:       proof.ApplyRefl,
	},
	{
		name:        "left",
		description: "concl is A ∨ B (introduce A)",
		shape:       conclIsOr,
		apply:       proof.ApplyLeft,
	},
	{
		name:        "right",
		description: "concl is A ∨ B (introduce B)",
		shape:       conclIsOr,
		apply:       proof.ApplyRight,
	},
	{
		name:        "funext",
		description: "concl holds an equation f = g between functions (extensionality, every such equation at once)",
		shape:       conclHoldsFunEq,
		apply:       proof.ApplyFunext,
	},
	{
		name:        "symm",
		description: "concl is a = b (flip to ⊢ b = a)",
		shape:       conclIsNonReflEq,
		apply:       proof.ApplySymm,
	},
	{
		name:        "congr",
		description: "concl is s = t with s ≢ t (decompose structurally)",
		shape:       conclIsNonReflEq,
		apply:       proof.ApplyCongr,
	},
	{
		// THE unified num-arithmetic move (prover/solver/omega/README.md). A composite
		// `_Arith + _TrivialSimplify` recorded under ONE proto tag (`arith=42`):
		// a fully-decidable goal collapses to `⊢ ⊤` and TrivialSimplify closes
		// it, a partial decision advances the conclusion as a simpler child.
		//
		// What `_Arith` is. ONE deep+fixpoint `prop.Rewrite` over the conclusion
		// (and a hypothesis, on a match) — `prop.BasicRewritesWith(arithSimpStep,
		// arithDecideLeaf(hyps))` driving `prop.DeepRewrite`. Two arith shallow
		// leaves stacked on the standard basic rewrites (bool / cond / quantifier
		// / neg / hilbert), all iterating to fixpoint together so cascades like
		// `a + Cond(a=a, 0, 1) → a` resolve in one move.
		//
		// What the arith leaves cover (everything sound + cheap; nothing that
		// surprises agents with size growth):
		//   • Identity laws + numeral folding: `a+0→a`, `a*1→a`, `2+3→5`, etc.
		//   • Atom decision: every `<` / `≤` / `>` / `≥` / `=` / `≠` atom the
		//     hyps make universally true/false collapses to ⊤/⊥, via
		//     `LinProve`→`OmegaProve` for linear and `RingProveFull` for
		//     nonlinear semiring equalities (`a*b=b*a`, `(a+b)²=a²+2ab+b²`).
		//     A per-atom prove that can't derive a real cert returns ok=false
		//     (no fabricated cert), so a contingent atom's failed prove is left
		//     undecided and never poisons sound siblings.
		//   • Truncated subtraction (monus): `subCancel` cancellation
		//     (`n+m−n→m`, `(n+m+k)−n→m+k`), `subTrunc` truncation (`0−n→0`,
		//     `n−(n+m)→0`), and the LessEqTotal case-split engine for irreducible
		//     `a−b` (pins `0=a−b` / `a=(a−b)+b` per branch, recurses).
		//   • nat_max / nat_min: idempotence (`nat_max a a→a` via CondId) and the
		//     excluded-middle case-split (pins `nat_max a b = b` / `= a` per guard
		//     branch via the def + COND collapse).
		//   • predecessor: bridge `predecessor n → n − 1` (derived from the Sub recursion), so
		//     `predecessor(suc n)` and `predecessor(n+1)` collapse via subCancel and a symbolic
		//     `predecessor m` is decided by the monus case-split.
		//   • nat_div / nat_mod: trivial simp (`nat_div(m, 0)/1`, `nat_mod(m, 0)/1`, `nat_mod(n,n)`),
		//     bounded-atom enrichment per opaque atom (ModLessEq / DivLessEq
		//     unconditional; Division's `nat_mod(m,n)<n` + identity when n≠0
		//     discharges; ModLessThan pin when m<n discharges; DivRefl / DivEqZero
		//     when their side conditions discharge), and common-factor
		//     cancellation `nat_div(c·a, c·b) → nat_div(a, b)` for literal nonzero c.
		//   • nat_pow (deliberately partial): `nat_pow(_, 0)→1` and `nat_pow(_, 1)→_` only
		//     — strictly term-shrinking notation cleanups. Higher exponents are
		//     NOT auto-expanded here; `nat_pow(complex_base, c)` for c≥2 can blow
		//     up term size dramatically, and that's a deliberate proof-step
		//     decision an agent should drive via the separate `expand_exp`
		//     action (rewriteTactic over `omega.ExpandEXPRewrite()`), then
		//     follow with `arith` to close.
		//
		// What `_Arith` deliberately does NOT do (the contract: nothing inside
		// `arith` ever grows term size):
		//   • nat_pow unfolding for c ≥ 2 — see above; use `expand_exp` first.
		//   • Cooper QE / gray-shadow case-splits — the open integer-completeness frontier.
		//   • Anything the agent shouldn't lose control over.
		//
		// Backing supply: the corpus-installed `NatLemmaBundle` (serve.InstallNatBundle)
		// provides every named lemma the layers reach (AddSym / LessEqTotal /
		// SubEqZero / Division / NatPow / …). In production there is no placeholder
		// fabricator, so any leaf that falls back to a placeholder panics at the
		// seam — population bugs surface at the call site, never silently.
		name:        "arith",
		description: "simplify-or-decide arithmetic over num, int and real, each atom by its operand type — identity laws, atom decision (linarith + ring over the monomial basis, the integer layer, the pairwise products of the context's differences), monus (cancel + case split), nat_max/nat_min, predecessor bridge, nat_div/nat_mod (bounded-atom enrichment + common-factor cancel), a literal-exponent power read as its monomial (nat_pow, real_pow, int_pow; the term stays as written — ring_nf or nat_arith.PowTwo to spell it out), int/real sub and neg, abs/max/min/COND splits, the real field layer (one symbolic divisor per atom); closes when the conclusion reduces to ⊤",
		shape:       goalHasArithContent,
		until:       proof.ApplyArithSimplify,
	},
	{
		name:        "ring_nf",
		description: "rewrite every arithmetic subterm of the conclusion and the hypotheses (num, int, real) to its ring normal form — a sum of monomials, each a numeral coefficient times a sorted product of atoms, the constant last, unit coefficients and a zero constant elided — so two spellings of one polynomial meet as one term; subtraction and negation stay atoms; progress-or-fail",
		shape:       goalHasArithContent,
		until:       proof.ApplyRingNf,
	},
}

// There is no `word_arith` move — a lowering engine that would translate
// a machine-word goal away (bitwise equations per-bit, ring equations via
// ℤ congruence, comparisons via ℕ). No member declares `arith:word`,
// because the corpus's word statements are born at the `val` layer, where
// such a kit's one job — peeling the word TYPE — has no work object. A
// word-domain target is attacked as its term-level T-image.

// goalHasArithContent gates the unified `arith` move's enumeration: some
// subterm of the goal carries num-arithmetic content the tactic can act on —
// a `+`/`*` (the identity simplifier might reduce it) or a comparison/equality
// atom over num (the decider might collapse it; this also catches every
// equation involving monus/nat_max/nat_min/predecessor/nat_div/nat_mod/nat_pow since they all carry an
// outer `=`/`≤`/etc. when they're the goal of a proof step). Over-approximation
// by design — the tactic still declines cleanly when nothing actually reduces,
// so the gate errs toward offering the move.
//
// Leading ∀/⇒ on the conclusion are peeled first: ApplyArithSimplify strips
// those wrappers (antecedent → hyp, ∀ → fresh var) before deciding, so the gate
// must see the arith atoms they bury. Without the peel they are invisible —
// ext.SubTerms surfaces only CLOSED subterms, never an atom whose vars are
// bound by an enclosing ∀ (`∀a b. (a≤b)⇒…`). DecomposesFORALL frees the bound
// vars, so the matrix and peeled antecedents then scan as closed terms.
func goalHasArithContent(goal core.Prop) bool {
	terms := append(goal.Hyps(), goal.Conclusion())
	concl := goal.Conclusion()
	for {
		if !ext.MatchesFORALL(concl).IsZero() {
			_, concl = ext.DecomposesFORALL(concl)
			continue
		}
		if a, b, ok := ext.MatchesIMPLY(concl); ok {
			terms = append(terms, a)
			concl = b
			continue
		}
		break
	}
	terms = append(terms, concl)
	// Real content counts only when real dispatch is live (a real bundle is
	// installed): with none, a real goal does not pass the gate, so the move
	// is not offered and then declined. With one, the move is offered on real
	// `+`/`*`/comparison content too — the unified ArithDecideWithHyps then
	// dispatches it per atom.
	realOn := omega.RealArithEnabled()
	intOn := omega.IntArithEnabled()
	structureOn := omega.StructureRingEnabled()
	hyps := goal.Hyps()
	for s := range ext.SubTerms(terms...) {
		if _, _, ok := omega.MatchesPlus(s); ok {
			return true
		}
		if _, _, ok := omega.MatchesStar(s); ok {
			return true
		}
		if omega.IsLinComparisonGoal(s) {
			return true
		}
		if realOn && omega.IsRealArithContent(s) {
			return true
		}
		if intOn && omega.IsIntArithContent(s) {
			return true
		}
		// An equation at a carrier that is a ring by a resident
		// comm_ring_on, comm_ring or field fact or an installed instance
		// — the structure ring's content (omega/structure_ring.go).
		if structureOn && omega.IsStructureRingContent(hyps, s) {
			return true
		}
	}
	return false
}

// conclMatchesHyp returns true iff the goal's conclusion α-equals some
// hypothesis. Mirrors the AssumptionTactic shape predicate exactly.
func conclMatchesHyp(goal core.Prop) bool {
	concl := goal.Conclusion()
	for _, h := range goal.Hyps() {
		if h.AlphaEquals(concl) {
			return true
		}
	}
	return false
}

// conclIsReflEq returns true iff the goal's conclusion is `t = t` (both
// sides α-equal).
func conclIsReflEq(goal core.Prop) bool {
	l, r, ok := ext.MatchesEQ(goal.Conclusion())
	return ok && l.AlphaEquals(r)
}

// conclIsNonReflEq returns true iff the goal's conclusion is `a = b`
// with the two sides distinct (modulo α). Used for `symm` and `congr`,
// which would only loop on a refl-shaped goal.
func conclIsNonReflEq(goal core.Prop) bool {
	l, r, ok := ext.MatchesEQ(goal.Conclusion())
	return ok && !l.AlphaEquals(r)
}

// conclIsOr returns true iff the goal's conclusion is A ∨ B at the top
// level. Used by `left` / `right`.
func conclIsOr(goal core.Prop) bool {
	_, _, ok := ext.MatchesOR(goal.Conclusion())
	return ok
}

// conclHoldsFunEq reports whether the goal's conclusion holds an
// equation between functions, at its top or anywhere inside, under a
// binder its sides mention included: the domain of
// tactic.FunextTactic, whose rewrite is deep and makes every such
// equation pointwise in one step.
func conclHoldsFunEq(goal core.Prop) bool {
	return holdsFunEq(goal.Conclusion())
}

func holdsFunEq(t core.Term) bool {
	if l, _, ok := ext.MatchesEQ(t); ok && len(ext.MatchesFun(l.Type())) > 1 {
		return true
	}
	switch x := t.Core().(type) {
	case core.AppliedTerm:
		return holdsFunEq(x.Fun()) || holdsFunEq(x.Arg())
	case core.AbsTerm:
		return holdsFunEq(x.Body())
	}
	return false
}

// conclIsIff returns true iff the goal's conclusion is a top-level A ⇔ B.
// The underlying tactic has the same precondition (and a degenerate-form
// guard against A ⇔ A which simplify already trivializes), so gating
// enumeration on the same predicate keeps inspect's structural_facts
// aligned with what apply will actually accept.
func conclIsIff(goal core.Prop) bool {
	a, b, ok := ext.MatchesIFF(goal.Conclusion())
	if !ok {
		return false
	}
	// Match the underlying tactic's degenerate-shape filter: A ⇔ A
	// reduces via simplify and surfacing a "split" move on it would
	// just repeat A ⊢ A and A ⊢ A (useless).
	return !a.AlphaEquals(b)
}

// hypHasIff returns true iff some hypothesis is a top-level A ⇔ B.
func hypHasIff(goal core.Prop) bool {
	for _, h := range goal.Hyps() {
		if a, b, ok := ext.MatchesIFF(h); ok && !a.AlphaEquals(b) {
			return true
		}
	}
	return false
}

// hypHasImply returns true iff some hypothesis is a top-level A ⇒ B.
func hypHasImply(goal core.Prop) bool {
	for _, h := range goal.Hyps() {
		if a, b, ok := ext.MatchesIMPLY(h); ok && !a.AlphaEquals(b) {
			return true
		}
	}
	return false
}

// structuralTacticByName is the name → spec lookup used by applyTacticOnClone
// to dispatch `apply` calls. Built once from structuralTacticSpecs.
var structuralTacticByName = func() map[string]*_StructuralTacticSpec {
	m := make(map[string]*_StructuralTacticSpec, len(structuralTacticSpecs))
	for i := range structuralTacticSpecs {
		m[structuralTacticSpecs[i].name] = &structuralTacticSpecs[i]
	}
	return m
}()

// conclIsWideConj returns true iff the goal's conclusion flattens to
// ≥3 leaf conjuncts (a genuinely wide ∧-spine). Used as the shape
// predicate for `split_conj_all`: on a binary A∧B it would just
// reproduce `split_conj`, so we only surface the n-ary move when it
// actually differs (saves the agent an N-1-deep binary peel).
func conclIsWideConj(goal core.Prop) bool {
	return len(ext.DecomposesAND(goal.Conclusion())) >= 3
}

// goalContainsCond returns true iff some subterm of the goal (any hyp or
// the conclusion) is a COND(c, a, b). Used as the shape predicate for
// `cond_rewrite` in structuralTacticSpecs.
func goalContainsCond(goal core.Prop) bool {
	for s := range ext.SubTerms(append(goal.Hyps(), goal.Conclusion())...) {
		if _, _, _, ok := ext.MatchesCond(s); ok {
			return true
		}
	}
	return false
}

// Caps for case-split position enumeration. Bounded by goal shape is fine
// for parameterless moves and induction vars (the universe is small), but
// case-split positions are unbounded in general — every bool subterm is a
// candidate. We cap on three axes:
//
//   - inspectCaseTermSizeMax: skip bool subterms whose tree is "too large"
//     to be a useful case-split (the agent would do better to expand a
//     definition first).
//   - inspectCaseTotalCap: total positions returned across all types.
//   - inspectCaseTotalCap doubles as the per-type cap for now (we don't
//     break out per-type since the only case-split target type currently
//     surfaced is bool).
//
// The values are permissive defaults, to be tuned in practice. The
// *presence* of caps + the truncated flag in the
// response is non-negotiable.
const (
	inspectCaseTermSizeMax = 50
	inspectCaseTotalCap    = 12
)

// printTermCappedSize bounds the terms we render into fact descriptions.
// Generous — a 2048-node term prints to a few KB, which an agent can
// still read. Beyond it (or on Size() overflow) rendering is actively
// harmful: PrintTerm expands pointer-shared DAGs, so a deep set_comprehension/COND
// goal yields an exponential-length string that dominates Inspect
// wall-clock and bloats the RPC payload.
const printTermCappedSize = 2048

// printTermCapped renders t for a StructuralFact description, replacing
// oversized terms with a size note instead of an exponential dump.
func printTermCapped(t core.Term) string {
	if s := t.Size(); s < 0 || s > printTermCappedSize {
		return fmt.Sprintf("<term too large to print (size %d)>", s)
	}
	return ext.PrintTerm(t)
}

// _ProbeBudget is the budget the probes of a structural pass run under.
// A probe one run of which can outlast any budget (the arith move, an
// rw) gets a deadline of its own: budget after it starts, and never past
// ctx's. The other probes read no clock and run to their end.
type _ProbeBudget struct {
	ctx context.Context
	// budget is the time one probe has; zero is no deadline but ctx's.
	budget time.Duration
	// overran, when set, is told of a probe that ended past its
	// deadline: what the probe was, the deadline, and the stack of the
	// cut that ended it ("" for a probe that returned).
	overran func(what string, deadline time.Time, stack string)
}

// unbudgeted runs every probe to its end.
var unbudgeted = _ProbeBudget{ctx: context.Background()}

// under runs probe under a deadline of its own. cut is "" for a probe
// that answered. For one its context ended it is the reason to report
// beside the move: the probe did not answer, which says nothing of
// whether the move applies.
func (b _ProbeBudget) under(what string, probe func(context.Context) bool) (applies bool, cut string) {
	ctx := b.ctx
	var deadline time.Time
	if b.budget > 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(b.ctx, b.budget)
		defer cancel()
		deadline, _ = ctx.Deadline()
	}
	start := time.Now()
	defer func() {
		r := recover()
		stack := ""
		if r != nil {
			c, isCut := utils.AsCut(r)
			if !isCut {
				panic(r)
			}
			stack = string(debug.Stack())
			applies = false
			elapsed := time.Since(start).Milliseconds()
			if b.ctx.Err() != nil {
				cut = fmt.Sprintf("the probe was cut off after %d ms %s: the request's context is done (%v). "+
					"It did not answer, so the move is neither verified nor ruled out",
					elapsed, c.Where, b.ctx.Err())
			} else {
				cut = fmt.Sprintf("the probe was cut off at inspect's %d ms probe budget (after %d ms, %s). "+
					"It did not answer, so the move is neither verified nor ruled out: `probe` the tactic with a "+
					"larger budget_ms, or `inspect` with one",
					b.budget.Milliseconds(), elapsed, c.Where)
			}
		}
		if b.overran != nil && !deadline.IsZero() && time.Since(deadline) > overrunRecordAfter {
			b.overran(what, deadline, stack)
		}
	}()
	return probe(ctx), ""
}

// enumerateStructuralFacts produces the StructuralFact list for a goal.
// Returns the list and a "truncated" flag indicating whether any cap
// trimmed the result (currently only the case-split position cap can fire).
//
// Order of emission is stable: parameterless moves (lex-sorted by kind),
// then def_expand (lex-sorted by const name), then induction (lex-sorted
// by var name), then case_split positions (AST preorder).
//
// The probes run under budget. A probe it cuts off is a fact with its
// Unverified set, in the place the verified fact would have: it is
// never left out, and never read as a move that does not apply.
func enumerateStructuralFacts(budget _ProbeBudget, goal core.Prop, env *proof.ProverEnv) ([]StructuralFact, bool) {
	var facts []StructuralFact
	truncated := false

	// 1. Parameterless structural moves.
	for _, m := range collectStructuralMovesUnder(budget, goal) {
		facts = append(facts, StructuralFact{
			Kind:        m.Tactic,
			Description: m.Description,
			Unverified:  m.Unverified,
		})
	}

	// 2. def_expand candidates — every definable const that the
	// expansion tactic actually accepts on this goal.
	//
	// CollectDefinableConsts keys by TermKey (which includes type
	// instantiation), so a single printed name like `$` can appear
	// multiple times when it occurs in the goal at distinct type
	// instantiations (e.g. `$⟨A,M⟩` and `$⟨A,N⟩`). The agent's
	// `def_expand const="$"` dispatches by string name only — both
	// instances would route to the same DefAction.Apply call — so
	// listing both would produce a duplicate fact that adds no signal.
	// Dedupe by printed const name; first applicable instance wins.
	seenDefName := make(map[string]struct{})
	for _, c := range ext.CollectDefinableConsts(goal) {
		name := string(c.Name())
		if _, dup := seenDefName[name]; dup {
			continue
		}
		// Use the rewrite-only predicate (mirrors ApplyDefExpand exactly):
		// inspect must agree with what `apply def_expand` will actually do.
		// TryDefTactic admits the lemmaHypMatchTactic fallback, which the
		// agent-facing apply path rejects — listing facts under that
		// fallback would over-approximate and waste agent rounds on
		// tactics that apply will immediately reject in <300ms.
		if _, ok := proof.TryDefTacticRewrite(goal, c); !ok {
			continue
		}
		// An inductively minted relation's closure form is not a proof
		// surface — `apply def_expand` refuses it by name — so offering
		// the move here would invite exactly the failure the door
		// prevents. (The printed closure form is also the ∀-predicate
		// hypothesis the Playbook's refute-poisoning lesson is about.)
		if proof.InductiveUnfoldRefusal(c) != nil {
			continue
		}
		seenDefName[name] = struct{}{}
		facts = append(facts, StructuralFact{
			Kind:        "def_expand",
			Params:      map[string]string{"const": name},
			Description: fmt.Sprintf("expand definition of %s", ext.PrintTerm(c)),
		})
	}

	// 2b. def_eq — surface a constant's DEFINING equation(s), which the agent
	// never sees from def_expand and would otherwise have no reason to recall:
	//
	//   - NewConstDef Hilbert/ε consts (nat_mod, nat_div, HD, +, *): the point-free
	//     `c = εx.…` — const-meta-only (no registry entry); def_expand yields
	//     only the weaker property P(c). The agent closes a pointwise goal
	//     `∀x. c(x) = f(x)` by reducing via congr to the head `c = f`, then
	//     `known` (const-def fallback) closes it.
	//
	//   - NewTypeDef abs/rep consts (mk_option, mk_prod, …): the type-def
	//     axioms `abs(rep a)=a` and `P(r) ⇔ rep(abs r)=r`. Nothing in the goal
	//     points the agent at them — and their shape is tricky (not
	//     `c = …`). Surfacing them is the reminder "this is how the
	//     type is defined; maybe it helps."
	//
	// Both kinds come from proof.ConstDefDefiningHints (NewConstDef via the
	// const-meta def thm; abs/rep via TypeDefExpand on the unproved defSource —
	// text only).
	seenDefEq := make(map[string]struct{})
	for _, c := range ext.CollectDefinableConsts(goal) {
		name := string(c.Name())
		if _, dup := seenDefEq[name]; dup {
			continue
		}
		hints, _ := proof.ConstDefDefiningHints(c)
		if len(hints) == 0 {
			continue
		}
		// Same reason as the def_expand arm above: an inductive
		// definition's constant has a defining equation, but it is the
		// closure form, and no proof may read it.
		if proof.InductiveUnfoldRefusal(c) != nil {
			continue
		}
		seenDefEq[name] = struct{}{}
		for _, h := range hints {
			eqText := ext.PrintTerm(h.Prop.Conclusion())
			params := map[string]string{"const": name, "equation": eqText}
			if h.Role != "def" {
				params["role"] = h.Role
			}
			facts = append(facts, StructuralFact{
				Kind:   "def_eq",
				Params: params,
				Description: fmt.Sprintf("defining equation of %s is `%s`; to prove a goal "+
					"mentioning %s, cite it (bridge a pointwise `%s(…)=…` via congr_fun)",
					name, eqText, name, name),
			})
		}
	}

	// 3a. witness — applicable when the conclusion is a top-level ∃. The
	// agent supplies the witness term at apply time; we surface only the
	// applicability + bound-var name as a hint about which position the
	// witness will substitute for.
	if abs := ext.MatchesEXISTS(goal.Conclusion()); !abs.IsZero() {
		v := abs.Var()
		facts = append(facts, StructuralFact{
			Kind:        "witness",
			Params:      map[string]string{"var": string(v.Name())},
			Description: fmt.Sprintf("supply a witness term for ∃%s in the conclusion (consumes the ∃)", v.Name()),
		})
	}
	// A top-level ∃! takes a witness too: what is left is the body at the
	// witness and that the body holds of nothing else.
	if abs := ext.MatchesUNIQUE(goal.Conclusion()); !abs.IsZero() {
		v := abs.Var()
		facts = append(facts, StructuralFact{
			Kind:   "witness",
			Params: map[string]string{"var": string(v.Name())},
			Description: fmt.Sprintf(
				"supply the witness term t for ∃!%s in the conclusion: leaves the body at t and that every %s it holds of is t",
				v.Name(), v.Name()),
		})
	}

	// 3b. instantiate — applicable for each ∀-headed hypothesis. Witness
	// term comes from the agent. Each ∀-hyp gets its own fact with a
	// `hyp_index` param so the agent can target a specific hyp instead
	// of falling back to "first ∀-hyp matching the witness type" — which
	// makes the second-or-later ∀-hyp unreachable when several share the
	// same binder type.
	//
	// `var` (the bound-variable name) is preserved as a human-readable
	// hint, but is not the canonical selector: bound names get freshened
	// during proof flow and may collide across hyps. `hyp_index` (the
	// 0-based position in goal.Hyps()) is what apply consumes — same
	// string-stringified convention as `subst`'s hyp_index and
	// `case_split`'s `term`.
	//
	// No applicability gate here: applicability depends on the witness, which
	// inspect doesn't have. The shape predicate ("hyp is ∀-headed") is
	// the brick we expose; the agent picks a witness and either probes
	// or applies to verify.
	for i, h := range goal.Hyps() {
		abs := ext.MatchesFORALL(h)
		if abs.IsZero() {
			continue
		}
		v := abs.Var()
		facts = append(facts, StructuralFact{
			Kind: "instantiate",
			Params: map[string]string{
				"hyp_index": fmt.Sprintf("%d", i),
				"var":       string(v.Name()),
			},
			Description: fmt.Sprintf("instantiate hyp %d (∀%s. …) at a witness term (the ∀ stays available)", i, v.Name()),
		})
	}

	// 3c. subst — applicable for each hyp that is an equality AND for
	// which the underlying SubstTactic actually makes progress on the
	// current goal. Verifying via ApplySubst on a clone matches the
	// discipline used by collectStructuralMoves (parameterless specs)
	// and the def_expand / induction enumerators above: structural
	// facts are facts about applicability, not guesses about shape.
	// Without this gate, an enumerated subst that fails on apply with
	// "had no effect" would break the inspect/apply contract — the
	// agent picks a hyp_index from inspect, runs apply, and gets a
	// failure where the engine itself promised success.
	for i, h := range goal.Hyps() {
		l, r, ok := ext.MatchesEQ(h)
		if !ok {
			continue
		}
		// `t = t` is useless to substitute — eqSimplify would skip
		// it anyway, but bail early for clarity.
		if l.AlphaEquals(r) {
			continue
		}
		testNode := proof.CreateGoalStack(goal)
		if !proof.ApplySubst(testNode, i) {
			continue
		}
		facts = append(facts, StructuralFact{
			Kind:        "subst",
			Params:      map[string]string{"hyp_index": fmt.Sprintf("%d", i)},
			Description: fmt.Sprintf("substitute using hyp %d: %s", i, printTermCapped(h)),
		})
	}

	// 3c'. rw — the fixpoint, direction-controlled sibling of subst:
	// rewrite with the equality hyp across the conclusion and all other
	// hyps. Same probe-gated discipline as 3c (facts are facts about
	// applicability). One fact per equality hyp, carrying the first
	// direction that applies; the description notes when the reverse
	// direction also fires so the agent knows `flip` is available.
	for i, h := range goal.Hyps() {
		l, r, ok := ext.MatchesEQ(h)
		if !ok || l.AlphaEquals(r) {
			continue
		}
		rw := func(flip bool) (bool, string) {
			what := fmt.Sprintf("the rw probe by hypothesis %d", i)
			if flip {
				what += ", flipped"
			}
			return budget.under(what, func(ctx context.Context) bool {
				return proof.ApplyRw(ctx, proof.CreateGoalStack(goal), i, flip)
			})
		}
		forward, forwardCut := rw(false)
		backward, backwardCut := rw(true)
		if !forward && !backward && forwardCut == "" && backwardCut == "" {
			continue
		}
		written := fmt.Sprintf("rewrite everywhere with hyp %d: %s → %s", i, printTermCapped(l), printTermCapped(r))
		flipped := fmt.Sprintf("rewrite everywhere with hyp %d (flipped): %s → %s", i, printTermCapped(r), printTermCapped(l))
		// The fact carries the first direction that applies; where
		// neither was seen to apply, the first one that was cut off,
		// unverified.
		flip, desc, unverified := "false", written, ""
		switch {
		case forward && backward:
			desc += " (flip:true reverses the direction)"
		case forward && backwardCut != "":
			desc += " (flip:true was not verified: " + backwardCut + ")"
		case forward:
		case backward:
			flip, desc = "true", flipped
			if forwardCut != "" {
				desc += " (the written direction was not verified: " + forwardCut + ")"
			}
		case forwardCut != "":
			unverified = forwardCut
		default:
			flip, desc, unverified = "true", flipped, backwardCut
		}
		facts = append(facts, StructuralFact{
			Kind: "rw",
			Params: map[string]string{
				"hyp_index": fmt.Sprintf("%d", i),
				"flip":      flip,
			},
			Description: desc,
			Unverified:  unverified,
		})
	}

	// 3d. trans — applicable when the conclusion is `a = c`. Agent
	// supplies the middle term; we surface the move so it shows up in
	// inspect alongside symm/congr (the three ways to chip at an
	// equality goal).
	if l, r, ok := ext.MatchesEQ(goal.Conclusion()); ok && !l.AlphaEquals(r) {
		facts = append(facts, StructuralFact{
			Kind:        "trans",
			Description: fmt.Sprintf("split %s via a middle term (agent supplies the term)", printTermCapped(goal.Conclusion())),
		})
	}

	// 4. induction vars — one fact per variable whose type has an
	// induction principle the env serves, RESOLVED AT THAT VARIABLE'S
	// TYPE the way the apply path resolves it
	// (tactic.PrincipleNameCandidates + AnalyzePrincipleForType). Two
	// earlier shapes of this enumeration were wrong in the same
	// direction, and each left a move the tactic accepts unadvertised:
	// reading `num_induction` alone missed every datatype, and analyzing
	// each served principle ONCE yields a template at the principle's
	// own index type (`list(A)`), which no goal variable in a
	// monomorphic chapter has — a goal carries `l : list(num)`.
	// GeneralInductionTactic asserts the template's index type EQUALS
	// the variable's, so the resolution belongs per variable.
	for _, v := range inductionCandidateVars(goal) {
		tmpl := principleForVarType(env, v.Type())
		if tmpl == nil {
			continue
		}
		if _, _, ok := proof.TryInductionTactic(goal, v, tmpl); !ok {
			continue
		}
		facts = append(facts, StructuralFact{
			Kind:        "induction",
			Params:      map[string]string{"const": string(v.Name())},
			Description: fmt.Sprintf("induction on %s", ext.PrintTerm(v)),
		})
	}

	// 4. case_split positions — bool subterms in the goal whose value the
	// agent might want to branch on. Skip:
	//
	//   - Whole hypotheses and the goal conclusion. Splitting on the
	//     thing we're proving (or already assume) is `goal ⊢ goal ∨ ¬goal`
	//     — useless. A dedicated structural move (split_conj / split_iff /
	//     split_hyp_*) handles the real decomposition for those.
	//
	//   - Subterms whose head is a logical connective (∧/∨/⇒/⇔/¬).
	//     Splitting on `A ∧ B` gives `A∧B ⊢ … and ¬(A∧B) ⊢ …` — strictly
	//     worse than split_conj on the conjunction (which gives
	//     `⊢ A and ⊢ B`). Same for the others; the dedicated structural
	//     facts above cover them.
	//
	// What remains: atomic / arithmetic / equality / function-application
	// bool subterms — exactly the shapes where case_split is the right
	// tactic (e.g. `m = suc n`, `m ≤ 0`).
	skipKeys := make(map[core.TermKey]struct{})
	skipKeys[goal.Conclusion().AlphaKey()] = struct{}{}
	for _, h := range goal.Hyps() {
		skipKeys[h.AlphaKey()] = struct{}{}
	}
	count := 0
	seen := make(map[core.TermKey]struct{})
	for s := range ext.SubTerms(append(goal.Hyps(), goal.Conclusion())...) {
		if !ext.IsBool(s) {
			continue
		}
		if s.Size() > inspectCaseTermSizeMax {
			continue
		}
		if _, top := skipKeys[s.AlphaKey()]; top {
			continue
		}
		if hasLogicalHead(s) {
			continue
		}
		key := s.AlphaKey()
		if _, dup := seen[key]; dup {
			continue
		}
		seen[key] = struct{}{}
		if count >= inspectCaseTotalCap {
			truncated = true
			break
		}
		facts = append(facts, StructuralFact{
			Kind:        "case_split",
			Params:      map[string]string{"term": ext.PrintTerm(s)},
			Description: fmt.Sprintf("boolean case split on %s", ext.PrintTerm(s)),
		})
		count++
	}

	return facts, truncated
}

// hasLogicalHead reports whether the term's outermost connective is a
// boolean-shape one that already has a dedicated structural decomposition
// (and / or / imply / iff / not). Surfacing such terms as case_split
// candidates would always be strictly worse than the dedicated move.
func hasLogicalHead(t core.Term) bool {
	if _, _, ok := ext.MatchesAND(t); ok {
		return true
	}
	if _, _, ok := ext.MatchesOR(t); ok {
		return true
	}
	if _, _, ok := ext.MatchesIMPLY(t); ok {
		return true
	}
	if _, _, ok := ext.MatchesIFF(t); ok {
		return true
	}
	if ext.MatchesNOT(t) != nil {
		return true
	}
	return false
}

// inductionCandidateVars lists the variables an induction could run on:
// the goal's free variables, and — only when it has none — the ∀-bound
// variables of its conclusion. It mirrors proof.CollectInductionVars'
// priority without its type filter, because the type decides which
// PRINCIPLE applies and that is resolved per variable by
// principleForVarType.
func inductionCandidateVars(goal core.Prop) []core.VarTerm {
	var out []core.VarTerm
	insert := func(v core.VarTerm) {
		for _, seen := range out {
			if seen.Compare(v) == 0 {
				return
			}
		}
		out = append(out, v)
	}
	all := func(core.VarTerm) bool { return true }
	for _, fv := range goal.Conclusion().Frees(all) {
		insert(fv)
	}
	goal.AnyHyp(func(h core.Term) bool {
		for _, fv := range h.Frees(all) {
			insert(fv)
		}
		return false
	})
	if len(out) == 0 {
		vars, _ := ext.DecomposesFORALL(goal.Conclusion())
		for v := range vars.Iter() {
			insert(v)
		}
	}
	return out
}

// principleForVarType resolves the induction principle for a variable's
// type into a template AT that type — the read the engine's apply path
// performs (lookupInductionTemplate), without its per-engine cache. nil
// when the type is not inductive, the env serves no principle for it, or
// the principle's shape does not analyze.
func principleForVarType(env *proof.ProverEnv, t core.HolType) *tactic.InductionTemplate {
	if env == nil || env.LibraryThms == nil || t == nil {
		return nil
	}
	for _, name := range tactic.PrincipleNameCandidates(t) {
		thm, ok := env.LookupLibraryThm(name)
		if !ok || thm == nil {
			continue
		}
		tmpl, err := tactic.AnalyzePrincipleForType(thm, t)
		if err != nil || tmpl == nil {
			continue
		}
		return tmpl
	}
	return nil
}
