/** File: step.go
 *
 * This file defines the atomic Step layer (interface _Step, exported as
 * the alias Step) and its concrete implementations.
 *
 * A Step is the smallest unit of proof work: a function that takes a
 * Prop and returns a SubGoals. It is "atomic" — it wraps a single
 * tactic.Tactic and is blind to the surrounding proof tree (it sees
 * only one Prop). Contrast with the compound Macro layer (macro.go),
 * which sees the whole GoalStackNode and orchestrates several Steps.
 * Both satisfy the umbrella Action interface (action.go) so either can be
 * passed to Script.Prove.
 *
 * Available steps:
 * - _AxiomDefStep: apply an axiom definition to a goal.
 * - _KnownThmStep: apply a known theorem to a goal.
 * - _TrivialSimplify: apply a trivial tactic to a goal.
 * - _AutoDenote: automatically denote a subterm whose size is larger than
 *   a threshold, or denote a Hilbert-operator subterm.
 * - _LemmaTactic: apply a lemma tactic to a goal.
 * - _CNFRefute: apply a cnf refute tactic to a goal.
 * - _TypeInstStep: apply a polymorphic source theorem to a goal via type
 *   instantiation.
 */

package proof

import (
	"context"
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
	"google.golang.org/protobuf/types/known/emptypb"
)

// cnfRefuterTimeoutCtxKey is a private context key whose value
// (time.Duration) overrides env.CnfRefuterTimeout for one CNF refute
// call. See CnfRefuterTimeoutCtxKey for the exported alias used by
// callers (engine.ApplyStep / engine.Probe).
type cnfRefuterTimeoutKey struct{}

// CnfRefuterTimeoutCtxKey is the context-value key by which a caller
// can override the per-call CNF refuter timeout for the duration of
// the call. The value must be a positive time.Duration. Designed for
// the agent-facing path: an apply/probe with budget_ms set stamps the
// ctx so the inner CNF refuter respects the agent's budget instead of
// the env default. Programmatic search callers do not set this and
// continue to get per-call CnfRefuterTimeout capping.
var CnfRefuterTimeoutCtxKey = cnfRefuterTimeoutKey{}

// MaxEffectiveCnfTimeoutMs hard-caps the per-call CNF refuter timeout
// that an agent-supplied budget_ms (stamped via CnfRefuterTimeoutCtxKey)
// can request. The refuter has a sharp diminishing-returns curve:
// refutations that exist are found well under 5s; beyond that the search
// is almost certainly in a hopeless branch and a larger budget only burns
// CPU (measured: budget_ms 5000, 10000 and 15000 all failed with
// identical elapsed-bounded behavior). So even when a caller stamps a
// larger budget on the ctx, the inner CNF call is clamped here. The
// surrounding apply/probe ctx deadline still honors the caller's full
// budget for other components (lemma search, retrieve, type
// unification); only the CNF refuter caps.
const MaxEffectiveCnfTimeoutMs = 5000

const (
	_AXIOM_DEF      = "Axiomatic definition."
	_TRIVIAL_TACTIC = "Trivial Simplify Tactic."
	_BASIC_TACTIC   = "Basic Tactics."
	_AUTO_DENOTE    = "Auto Denote."
	_CNF_REFUTE     = "CNF Refute."
)

type _Step interface {
	proto(b *ext.PoolBuilder) isStepProto_Step
	apply(Prop) *SubGoals

	// applyAction makes every concrete Step type satisfy the umbrella
	// Action interface (see action.go). Delegates to Script.Do internally.
	applyAction(s *Script, root *GoalStackNode)
}

type _AxiomDefStep struct {
	constTerm ConstTerm
}

func (_AxiomDefStep) String() string { return _AXIOM_DEF }

func (step _AxiomDefStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	if !step.constTerm.IsZero() {
		return &StepProto_AxiomDef{&AxiomDefProto{
			Type: &AxiomDefProto_Const{
				b.TermRef(step.constTerm)}}}
	}
	panic("Empty axiom def step.")
}

func (step _AxiomDefStep) apply(p Prop) *SubGoals {
	Assert(!step.constTerm.IsZero())
	// Route through getDefThm (the single const-def materialization
	// point) rather than reading meta.DefThm() / meta.TypeDefExpand
	// inline, so the thm here is α-identical to the one the def_expand
	// composite (computeDefExpandSubGoals) used to build the leaf this
	// step closes. getDefThm handles both NewConstDef (Type 1) and NewTypeDef abs/rep
	// (Type 2) dispatch internally and returns the type-specialized def;
	// makeAxiomDefSubGoals' IsTypeMatchOf tolerates that (substs empty
	// when the leaf is already at the same instance).
	thm := getDefThm(step.constTerm)
	if thm.IsZero() {
		return nil
	}
	return makeAxiomDefSubGoals(p, thm)
}

// makeAxiomDefSubGoals closes the lemma-child goal `p` with the const's
// resolved def-axiom `thm`, recovering the type substitution σ that
// makes `thm[σ]` α-equal to `p`.
//
// At commit-time, ApplyLemma / ApplyLeanRw may select a type-adapted
// def theorem, and that selected lemma is what _LeanRwTactic /
// _LemmaTactic record as `child(0).Goal`. By the kernel-side contract
// this Goal is always a structural type-instance of `thm` — so σ is
// recoverable purely from `(thm, p)` via `IsTypeMatchOf`.
//
// We deliberately do NOT re-run `adaptLemmaIfPolymorphic` here. That
// helper is an anchor-driven heuristic whose output depends on the
// goal's structure; given the SAME thm but a DIFFERENT goal (n.Goal
// at commit time vs child(0).Goal at replay), it can pick a different
// σ — concretely, after the pointer-identity isInstantiable change in
// `7918289f`, polymorphic def-thm replay for compound function types
// (the vector-pasting and pairing constants) hits this case: the second adaptation
// aliases two named type vars to one and IsStronger fails. The
// structural matcher IsTypeMatchOf doesn't have that pitfall — it
// reverse-engineers σ from the literal positional shape of (thm, p).
//
// On IsTypeMatchOf failure we return nil rather than panicking — that
// would mean `p` is not a type-instance of `thm` at all, which would
// signal a broken commit-side invariant rather than a normal failure.
func makeAxiomDefSubGoals(p Prop, thm core.ThmCert) *SubGoals {
	substs, ok := prop.IsTypeMatchOf(thm, p, utils.FullPredicate[core.VarType])
	if !ok {
		// Normalize-bridge fallback. The goal may be the def axiom modulo
		// normalization (conjunct/equality reorder) rather than
		// a clean type-instance — e.g. a `congr`/`funext`-reduced pointwise
		// definitional equation `c(ẋ)=f(ẋ)` collapsed to the point-free head
		// `c = f`, whose stored def thm prints identically but isn't α-equal.
		// BridgeNormalize lifts the proved def thm into p's α-form when the two
		// normalize-coincide (nil otherwise → genuine no-op, so a goal merely
		// containing c still falls through untouched). This keeps the
		// _AxiomDefStep recording (and its emit / dep-extraction) usable for
		// const-definition closes that the strict type-match path can't reach.
		bridged := prop.BridgeNormalize(p, thm)
		if bridged == nil {
			return nil
		}
		return tactic.MakeEmptySubGoals(p, bridged.AsThmCert())
	}
	resolved := thm
	if len(substs) != 0 {
		resolved = core.PropTypeInst(thm, substs...).AsThmCert()
	}
	if !IsStronger(resolved, p) {
		return nil
	}
	return tactic.MakeEmptySubGoals(p, resolved)
}

type _KnownThmStep struct {
	strongerGoal Prop

	// This is recorded only for logging and demonstration.
	// If the stronger goal itself has been proved, this is nil.
	equivalentThm Prop

	// sourceEntryKey carries the key of the registry entry this close
	// matched, when the committer knew it (engine auto-match /
	// sourceKey-channel closes via ApplyKnownWithKey). Emit reads this
	// field via GoalStackNode.PolymorphicSourceKeys() and resolves the
	// close's external leaf through it directly, instead of re-deriving
	// the key from the SESSION-form payload above.
	//
	// In-memory only; NOT serialized to the proto (same convention as
	// _LemmaTactic.polymorphicSourceKey). Empty when the close came from
	// a plain cache hit with no registry identity in hand — emit then
	// falls back to the payload Normalize+AlphaKey lookup.
	sourceEntryKey core.PropKey

	// reading says what strongerGoal (or equivalentThm) was read from
	// when it is a structure law read at an instance — the session's
	// `lemma {key, read_at}` closing a goal the reading states, or the
	// claim child of the reading's install (ApplyCiteReading).
	// Serialized (KnownThmProto.reading) so emit spells the cite
	// `Cite(Law.Read(instance))`; nil otherwise, and then nothing is
	// serialized for it.
	reading *ReadingRecord
}

func (step _KnownThmStep) String() string {
	if step.equivalentThm == nil {
		return fmt.Sprintf("Goal %s \nhas been proved",
			prop.PrintProp(step.strongerGoal))
	}
	return fmt.Sprintf("Goal %s \nis Equivalent to proved thm:\n%s",
		prop.PrintProp(step.strongerGoal), prop.PrintProp(step.equivalentThm))
}

func (step _KnownThmStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	if step.equivalentThm == nil {
		return &StepProto_KnownThm{&KnownThmProto{
			StrongerGoal: b.PropRef(step.strongerGoal),
			Reading:      step.reading.proto(b)}}
	}
	// Store-time backstop: equivalentThm is the legacy normalized-hit
	// annotation, so the two statements must be the SAME proposition
	// modulo Normalize. A mismatch means some producer recorded a
	// per-goal INSTANCE with its polymorphic source as the annotation —
	// the shape emit cannot resolve (no reference tier can classify a
	// per-session instance statement; it panics at
	// externalLeafExprCtx). Both live occurrences of that shape — the
	// paired-beta term instance of pairs.PairedLambda and the tier-3 fst type
	// instance, both in cardinality.HasSizeProduct — were recorded silently and
	// only caught at emit time, far from the producer. Panic HERE, at
	// serialization, so the next producer is
	// caught at store time with a stack pointing at itself. Producers
	// that close via an instance of a polymorphic source must record
	// the SOURCE instead: _TypeInstStep (type instances) or a
	// composite like paired_beta (term instances).
	nSG, _ := Normalize(step.strongerGoal)
	nEQ, _ := Normalize(step.equivalentThm)
	if nSG.AlphaKey() != nEQ.AlphaKey() {
		panic(fmt.Sprintf(
			"_KnownThmStep.proto: equivalentThm is not normalize-equal to "+
				"strongerGoal — a per-instance KnownThm payload is unresolvable "+
				"at emit; record the polymorphic source via _TypeInstStep (or a "+
				"composite step) instead.\n  strongerGoal: %s\n  equivalentThm: %s",
			prop.PrintProp(step.strongerGoal), prop.PrintProp(step.equivalentThm)))
	}
	return &StepProto_KnownThm{&KnownThmProto{
		StrongerGoal:  b.PropRef(step.strongerGoal),
		EquivalentThm: b.PropRef(step.equivalentThm),
		Reading:       step.reading.proto(b)}}
}

func (step _KnownThmStep) apply(p Prop) *SubGoals {
	// strongerGoal may be a promise (a cited promise-backed lemma); thread it
	// as a Prop into the empty SubGoals so it reaches provedThm unforced. A
	// realized closer is Proved(); a promise is on-track (IsPromised).
	Assert(step.strongerGoal.Proved() || core.IsPromised(step.strongerGoal))
	return tactic.MakeEmptySubGoals(p, step.strongerGoal)
}

// _TrivialNormalizedStep closes a goal whose normalized form has conclusion ⊤.
// Normalize folds hypotheses into the conclusion as disjuncts, so a goal
// whose CNF reduces to truth comes back as a hyp-free `⊢ ⊤` regardless of
// how many hyps it started with. The closing thm is `prop.DerivesTrue` (a
// proved `⊢ ⊤`), reconstructed through Normalize's callback to produce a
// Thm stronger than the original goal.
type _TrivialNormalizedStep struct{}

func (_TrivialNormalizedStep) String() string { return "Trivial Normalized." }

func (_TrivialNormalizedStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_TrivialNormalized{TrivialNormalized: &emptypb.Empty{}}
}

func (_TrivialNormalizedStep) apply(p Prop) *SubGoals {
	normalized, reconstruct := Normalize(p)
	if !normalized.Conclusion().Equals(T) {
		return nil
	}
	Assert(normalized.NumHyps() == 0)
	reconstructed := reconstruct(prop.DerivesTrue).AsThmCert()
	Assert(IsStronger(reconstructed, p))
	return tactic.MakeEmptySubGoals(p, reconstructed)
}

// _RecordRead reads every record projection of a packed value the leaf
// spells — in the conclusion and the hypotheses — as the part, through
// the record equations (prover/tactic, InstanceNormalTactic; the form a
// cited instance is handed over in): the apply rung's move where the
// context holds a statement up to that reading, run on the leaf it
// closes, before the assumption step, as _MembershipRead is for the
// membership reading. The equations are read as the proof's cites, so
// its recorded dependencies hold them. One child; refused where the
// leaf spells no such projection.
type _RecordRead struct{}

func (_RecordRead) String() string { return "RecordRead" }

func (_RecordRead) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_RecordRead{RecordRead: &emptypb.Empty{}}
}

func (_RecordRead) apply(p Prop) *SubGoals {
	return tactic.InstanceNormalTactic(nil)(p)
}

func (_RecordRead) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	return tactic.InstanceNormalTactic(libraryRead(scope))(p)
}

func (x _RecordRead) applyAction(s *Script, root *GoalStackNode) { s.Do(root, x) }

// _NumeralRead reads the leaf at its numerals — the conclusion and the
// hypotheses — through the arithmetic closer's evaluators (prover/tactic,
// NumeralReadTactic; omega, numeral_reading.go): a numeral term with no
// variable is its value, a comparison with none ⊤ or ⊥. It is the apply
// rung's move where the context holds a statement up to that reading,
// run on the leaf it closes, before the assumption step, as
// _MembershipRead and _RecordRead are for theirs; and it closes a leaf
// whose conclusion reads ⊤ or one of whose hypotheses reads ⊥. It runs
// under the proof's arithmetic policy, and a reading that fired is a use
// of the bundles it evaluated with, recorded as the Arith step's is. One
// child, or none where it closes; refused where the leaf spells nothing
// it reads.
type _NumeralRead struct{}

func (_NumeralRead) String() string { return "NumeralRead" }

func (_NumeralRead) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_NumeralRead{NumeralRead: &emptypb.Empty{}}
}

func (_NumeralRead) apply(p Prop) *SubGoals {
	return tactic.NumeralReadTactic(omega.UnscopedArithPolicy())(p)
}

func (x _NumeralRead) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	if scope == nil {
		return x.apply(p)
	}
	out := tactic.NumeralReadTactic(scope.numeralPolicy())(p)
	if out != nil {
		scope.recordNumeralRead(p)
	}
	return out
}

func (x _NumeralRead) applyAction(s *Script, root *GoalStackNode) { s.Do(root, x) }

// _RecordParts installs, for every record value the leaf spells and
// every projection of its type the leaf spells, the part equation the
// record reading computes (prover/tactic, RecordPartsTactic): the
// instance normal form at the refuter's own instantiations, which the
// By stage runs for the refuter before the search. The equations are
// read as the proof's cites, so its recorded dependencies hold them.
// One child; refused where no equation is new to the leaf.
type _RecordParts struct{}

func (_RecordParts) String() string { return "RecordParts" }

func (_RecordParts) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_RecordParts{RecordParts: &emptypb.Empty{}}
}

func (_RecordParts) apply(p Prop) *SubGoals {
	return tactic.RecordPartsTactic(nil)(p)
}

func (_RecordParts) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	return tactic.RecordPartsTactic(libraryRead(scope))(p)
}

func (x _RecordParts) applyAction(s *Script, root *GoalStackNode) { s.Do(root, x) }

type _TrivialSimplify struct{}

func (_TrivialSimplify) String() string { return _TRIVIAL_TACTIC }

func (_TrivialSimplify) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_TrivialSimplify{&emptypb.Empty{}}
}

func (_TrivialSimplify) apply(p Prop) *SubGoals {
	return tactic.TrivialSimplifyTactic(p)
}

type _BasicTactic struct{}

func (_BasicTactic) String() string { return _BASIC_TACTIC }

func (_BasicTactic) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Basic{&emptypb.Empty{}}
}

func (_BasicTactic) apply(p Prop) *SubGoals {
	return tactic.BasicTactics(p)
}

// runBasicUntil is runStep(_BasicTactic{}) with the fixpoint abandoned
// once ctx is done (tactic.BasicTacticsUntil). The step it commits is
// _BasicTactic, the one a replay runs with no deadline. cut reports the
// abandon: the node is then left as it was, and its caller does not go
// on as if Basic() had nothing to do.
func (n *GoalStackNode) runBasicUntil(ctx context.Context) (applied, cut bool) {
	sg, abandoned := tactic.BasicTacticsUntil(ctx, n.Goal)
	if abandoned {
		return false, true
	}
	return n.commitStep(_BasicTactic{}, sg), false
}

// _CondRewrite normalizes COND subterms via tactic.CondRewriteTactic:
// at bool level, expand P(Cond(c,x,y)) → (c ⇒ P(x)) ∧ (¬c ⇒ P(y));
// at non-bool level, push outward as Cond(c, P(x), P(y)).
// Includes basic rewrites for cleanup. Used in AutoExpand to ensure
// search/refute see goals with CONDs eliminated.
type _CondRewrite struct{}

func (_CondRewrite) String() string { return "Cond Rewrite." }

func (_CondRewrite) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_CondRewrite{&emptypb.Empty{}}
}

func (_CondRewrite) apply(p Prop) *SubGoals {
	return tactic.CondRewriteTactic(p)
}

// Structural sub-tactics — individual components of BasicTactics exposed
// as first-class agent moves. Each is a deterministic pure function of
// the input goal (no parameters, no environment), so its proto is just
// the oneof tag. Replay re-runs the function and the surrounding
// StepProto fields (goal/proved_thm/sub_goals) verify the output.

type _Rewrite struct{}

func (_Rewrite) String() string { return "Rewrite" }
func (_Rewrite) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Rewrite{Rewrite: &emptypb.Empty{}}
}
func (_Rewrite) apply(p Prop) *SubGoals { return tactic.RewriteTactic(p) }

// _SplitConj, _SplitDisj, _SplitIff, _SplitHypIff, _SplitHypImply
// each carry an optional `cases []Case` slice. The slice is empty
// unless the caller passes Case bodies (proto doesn't carry case
// info); emitted members populate it via the variadic Case
// arguments on the package-level constructors. Script.Do dispatches
// each Case body against the corresponding child subgoal after
// runStep produces children. See action.go for the dispatch
// machinery.

type _SplitConj struct{ cases []Case }

func (_SplitConj) String() string { return "SplitConj" }
func (_SplitConj) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_SplitConj{SplitConj: &emptypb.Empty{}}
}
func (_SplitConj) apply(p Prop) *SubGoals { return tactic.ConclConjTactic(p) }
func (x _SplitConj) caseBodies() []Case   { return x.cases }

// _SplitConjAll is the n-ary sibling of _SplitConj: it flattens the
// whole ∧-spine into N FLAT subgoals in one ministep (vs N-1 nested
// binary _SplitConj steps). Same empty-proto / shape-driven-replay
// contract as _SplitConj — the N children live in
// StepProto.sub_goals; apply re-derives them from the goal shape.
type _SplitConjAll struct{ cases []Case }

func (_SplitConjAll) String() string { return "SplitConjAll" }
func (_SplitConjAll) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_SplitConjAll{SplitConjAll: &emptypb.Empty{}}
}
func (_SplitConjAll) apply(p Prop) *SubGoals { return tactic.ConclConjAllTactic(p) }
func (x _SplitConjAll) caseBodies() []Case   { return x.cases }

// _SplitDisj carries an optional 0-based hyp index. When nil (legacy
// / proto-deserialized-from-Empty), the tactic picks the first ∨-hyp.
// When set, it targets that specific hyp — same replay contract as
// the legacy Empty form byte-decodes to hypIndex=nil, so old records
// are byte-stable and behave identically.
type _SplitDisj struct {
	cases    []Case
	hypIndex *int
}

func (_SplitDisj) String() string { return "SplitDisj" }
func (x _SplitDisj) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_SplitDisj{SplitDisj: makeHypIndexProto(x.hypIndex)}
}
func (x _SplitDisj) apply(p Prop) *SubGoals {
	if x.hypIndex != nil {
		return tactic.HypDisjTacticAt(p, *x.hypIndex)
	}
	return tactic.HypDisjTactic(p)
}
func (x _SplitDisj) caseBodies() []Case { return x.cases }

// _OpenTelescope opens the goal's statement in the order a section's
// closure binds it (tactic.OpenTelescopeTactic): each binder, and each
// hypothesis after the binders it mentions, the rest left as a
// statement (section_binding.go).
type _OpenTelescope struct{ items []tactic.TelescopeItem }

func (_OpenTelescope) String() string { return "OpenTelescope" }
func (x _OpenTelescope) proto(b *ext.PoolBuilder) isStepProto_Step {
	items := make([]*TelescopeItemProto, len(x.items))
	for i, it := range x.items {
		pieces := make([]*PieceRefProto, len(it.Pieces))
		for j, ref := range it.Pieces {
			pieces[j] = &PieceRefProto{Block: int32(ref.Block), Index: int32(ref.Index)}
		}
		items[i] = &TelescopeItemProto{Binder: int32(it.Binder), Pieces: pieces}
	}
	return &StepProto_OpenTelescope{OpenTelescope: &TelescopeProto{Items: items}}
}
func (x _OpenTelescope) apply(p Prop) *SubGoals { return tactic.OpenTelescopeTactic(p, x.items) }

type _StripImp struct{}

func (_StripImp) String() string { return "StripImp" }
func (_StripImp) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_StripImp{StripImp: &emptypb.Empty{}}
}
func (_StripImp) apply(p Prop) *SubGoals { return tactic.ConclImplyTactic(p) }

// _SplitHypConj is the premise split of By's conditioning stage: ONE
// conjunctive hyp — top-level ∧, or ∀-prefixed with the prefix
// distributed — replaced by its two conjuncts (first matching hyp; the
// stage loops to fixpoint). It runs only inside the By composite, which replays by
// re-running the stage; the proto tag exists for the composite's subtree
// walk, not for standalone dispatch.
type _SplitHypConj struct{}

func (_SplitHypConj) String() string { return "SplitHypConj" }
func (_SplitHypConj) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_SplitHypConj{SplitHypConj: &emptypb.Empty{}}
}
func (_SplitHypConj) apply(p Prop) *SubGoals {
	if sg := tactic.HypConjTactic(p); sg != nil {
		return sg
	}
	return tactic.HypForallConjTactic(p)
}

type _SplitIff struct{ cases []Case }

func (_SplitIff) String() string { return "SplitIff" }
func (_SplitIff) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_SplitIff{SplitIff: &emptypb.Empty{}}
}
func (_SplitIff) apply(p Prop) *SubGoals {
	return namedIffSplit(tactic.ConclIffTactic(p), func(sg *SubGoals) { assertIffGoalChildOrder(p, sg) })
}
func (x _SplitIff) caseBodies() []Case { return x.cases }

// _SplitHypIff carries the same optional hyp index as _SplitDisj —
// see that struct's comment for the wire-compat rationale.
type _SplitHypIff struct {
	cases    []Case
	hypIndex *int
}

func (_SplitHypIff) String() string { return "SplitHypIff" }
func (x _SplitHypIff) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_SplitHypIff{SplitHypIff: makeHypIndexProto(x.hypIndex)}
}

// apply splits the ⇔-hypothesis at hypIndex, or without one the first
// ⇔-hypothesis whose split stands: one whose sides are α-equal, or
// whose two branches merge into one (namedIffSplit), is passed over for
// the next.
func (x _SplitHypIff) apply(p Prop) *SubGoals {
	at := func(i int) *SubGoals {
		return namedIffSplit(tactic.HypIffTacticAt(p, i), func(sg *SubGoals) { assertIffHypChildOrder(p, sg, i) })
	}
	if x.hypIndex != nil {
		return at(*x.hypIndex)
	}
	for i := range p.NumHyps() {
		if sg := at(i); sg != nil {
			return sg
		}
	}
	return nil
}
func (x _SplitHypIff) caseBodies() []Case { return x.cases }

// _SplitHypImply — see _SplitDisj's comment for the wire-compat
// rationale for the optional hyp index.
type _SplitHypImply struct {
	cases    []Case
	hypIndex *int
}

func (_SplitHypImply) String() string { return "SplitHypImply" }
func (x _SplitHypImply) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_SplitHypImply{SplitHypImply: makeHypIndexProto(x.hypIndex)}
}
func (x _SplitHypImply) apply(p Prop) *SubGoals {
	if x.hypIndex != nil {
		return tactic.HypImplyTacticAt(p, *x.hypIndex)
	}
	return tactic.HypImplyTactic(p)
}
func (x _SplitHypImply) caseBodies() []Case { return x.cases }

// makeHypIndexProto builds a HypIndexProto from an optional 0-based
// hyp index. hypIdx=nil → empty message (byte-identical to the
// pre-payload google.protobuf.Empty encoding, so legacy records
// round-trip stably). hypIdx set → payload carries the int32.
func makeHypIndexProto(hypIdx *int) *HypIndexProto {
	if hypIdx == nil {
		return &HypIndexProto{}
	}
	v := int32(*hypIdx)
	return &HypIndexProto{HypIndex: &v}
}

// _StripQuant carries an optional 0-based hyp index, on the same wire
// contract as _SplitDisj. nil — the StripQuant() constructor, and every
// record whose payload is empty, the pre-payload google.protobuf.Empty
// form included — is the strip-everything tactic: the conclusion's
// whole ∀-prefix, else the first ∃-hypothesis. Set (StripQuantAt), it
// is ∃-elimination on THAT hypothesis alone; the conclusion is not
// touched.
//
// refused is RUNTIME-ONLY, and read by the hypothesis form alone: the
// variables the scope of the Argument running the step cannot take as
// witnesses (Script.declaredOtherwise). nil — every other caller —
// fixes names fresh for the goal.
type _StripQuant struct {
	hypIndex *int
	refused  func(core.VarTerm) bool
}

func (_StripQuant) String() string { return "StripQuant" }
func (x _StripQuant) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_StripQuant{StripQuant: makeHypIndexProto(x.hypIndex)}
}
func (x _StripQuant) apply(p Prop) *SubGoals {
	if x.hypIndex != nil {
		return tactic.StripQuantAtTacticUnder(p, *x.hypIndex, x.refused)
	}
	return tactic.StripQuantTactic(p)
}

// _StripQuant1 is the bounded single-binder strip (proto tag 54):
// peels EXACTLY ONE leading conclusion ∀, leaving inner quantifiers
// intact. Conclusion side only — never touches ∃-hyps. See
// tactic.StripQuant1Tactic for the transition and the name-
// compatibility contract with the strip-everything _StripQuant.
//
// refused is RUNTIME-ONLY: the variables the scope of the Argument
// running the step cannot take as the fixed one
// (Script.declaredOtherwise). nil — every other caller — fixes a name
// fresh for the goal.
type _StripQuant1 struct{ refused func(core.VarTerm) bool }

func (_StripQuant1) String() string { return "StripQuant1" }
func (_StripQuant1) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_StripQuant1{StripQuant1: &emptypb.Empty{}}
}
func (x _StripQuant1) apply(p Prop) *SubGoals { return tactic.StripQuant1TacticUnder(p, x.refused) }

// _WitnessStep instantiates the concl-level ∃ at the supplied witness
// term, producing one subgoal `⊢ P(t)`; on a concl-level ∃! the subgoal
// is `⊢ P(t) ∧ (∀y. P(y) ⇒ y = t)` (tactic.ConclExistsWitnessTactic). The
// proto carries the witness term so the step is replayable.
type _WitnessStep struct{ witness Term }

func (step _WitnessStep) String() string {
	return fmt.Sprintf("Witness: %s", ext.PrintTerm(step.witness))
}
func (step _WitnessStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Witness{Witness: b.TermRef(step.witness)}
}
func (step _WitnessStep) apply(p Prop) *SubGoals {
	return tactic.ConclExistsWitnessTactic(step.witness)(p)
}

// _InstantiateStep instantiates a ∀-headed hypothesis at the supplied
// witness term, adding `P(t)` to the hyps while keeping the original ∀
// available. Picks the first ∀-hyp whose binder type matches the
// witness. Go-only: a session grounds through the composite
// `specialize` step, so this step has no wire form.
type _InstantiateStep struct{ witness Term }

func (step _InstantiateStep) String() string {
	return fmt.Sprintf("Instantiate: %s", ext.PrintTerm(step.witness))
}
func (step _InstantiateStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	panic("_InstantiateStep has no wire form: a recorded grounding is the " +
		"composite `specialize` ministep — route it through Specialize/SpecializeTactic")
}
func (step _InstantiateStep) apply(p Prop) *SubGoals {
	return tactic.HypForallInstantiateTactic(step.witness)(p)
}

// _SpecializeStep is the index-targeted grounding composite:
// each SpecializeSpec grounds one ∀-hyp's leading binders at a witness
// list in ONE goal transition, adding only the final ground instance
// (no drifting-index chain of partial instances and sweep clears
// materializes). Sources are consumed unless
// keepSources (Lean `specialize` semantics; ematch passes keep). All
// hyp indices refer to this step's own input goal — the ClearHyps
// atomic-set convention. Proto tag `specialize`; replay re-runs the
// same driver (tactic.SpecializeTactic), record/emit/replay-reuse.
type _SpecializeStep struct {
	specs       []tactic.SpecializeSpec
	keepSources bool
}

func (step _SpecializeStep) String() string {
	var b strings.Builder
	b.WriteString("Specialize")
	if step.keepSources {
		b.WriteString(" (keep)")
	}
	for i, sp := range step.specs {
		if i > 0 {
			b.WriteString(";")
		}
		fmt.Fprintf(&b, " hyp %d at [", sp.HypIndex)
		for j, w := range sp.Witnesses {
			if j > 0 {
				b.WriteString(", ")
			}
			b.WriteString(ext.PrintTerm(w))
		}
		b.WriteString("]")
	}
	return b.String()
}
func (step _SpecializeStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	hyps := make([]*SpecializeProto_Hyp, len(step.specs))
	for i, sp := range step.specs {
		witnesses := make([]uint32, len(sp.Witnesses))
		for j, w := range sp.Witnesses {
			witnesses[j] = b.TermRef(w)
		}
		hyps[i] = &SpecializeProto_Hyp{
			HypIndex:  int32(sp.HypIndex),
			Witnesses: witnesses,
		}
	}
	return &StepProto_Specialize{Specialize: &SpecializeProto{
		Hyps:        hyps,
		KeepSources: step.keepSources,
	}}
}
func (step _SpecializeStep) apply(p Prop) *SubGoals {
	return tactic.SpecializeTactic(step.specs, step.keepSources)(p)
}

// applyScoped reads the record equations of the instances' normal form
// as the proof's cites (libraryRead).
func (step _SpecializeStep) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	return tactic.SpecializeTacticReading(step.specs, step.keepSources, libraryRead(scope))(p)
}

// LEAN-style ministeps. Each is a thin wrapper around a tactic in
// prover/tactic/lean_tactics.go (or, for `subst` and `trans`, a tactic
// constructor parameterized by the value carried in the proto).

type _Assumption struct{}

func (_Assumption) String() string { return "Assumption" }
func (_Assumption) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Assumption{Assumption: &emptypb.Empty{}}
}
func (_Assumption) apply(p Prop) *SubGoals { return tactic.AssumptionTactic(p) }

type _Refl struct{}

func (_Refl) String() string { return "Refl" }
func (_Refl) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Refl{Refl: &emptypb.Empty{}}
}
func (_Refl) apply(p Prop) *SubGoals { return tactic.ReflTactic(p) }

// _MembershipRead reads every membership in an identity-form set-builder
// the leaf spells — in the conclusion and the hypotheses — as its
// condition at the point, `x ∈ {p | φ}` as φ[x/p], through the kernel's
// bridge (tactic.MembershipReadTactic): the apply rung's move where the
// context holds a statement up to that reading, run on the leaf it
// closes, before the assumption step. One child; refused where the leaf
// spells no such membership.
type _MembershipRead struct{}

func (_MembershipRead) String() string { return "MembershipRead" }
func (_MembershipRead) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_MembershipRead{MembershipRead: &emptypb.Empty{}}
}
func (_MembershipRead) apply(p Prop) *SubGoals { return tactic.MembershipReadTactic(p) }

type _Left struct{}

func (_Left) String() string { return "Left" }
func (_Left) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Left{Left: &emptypb.Empty{}}
}
func (_Left) apply(p Prop) *SubGoals { return tactic.LeftTactic(p) }

type _Right struct{}

func (_Right) String() string { return "Right" }
func (_Right) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Right{Right: &emptypb.Empty{}}
}
func (_Right) apply(p Prop) *SubGoals { return tactic.RightTactic(p) }

type _Funext struct{}

func (_Funext) String() string { return "Funext" }
func (_Funext) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Funext{Funext: &emptypb.Empty{}}
}
func (_Funext) apply(p Prop) *SubGoals { return tactic.FunextTactic(p) }

type _ByContra struct{}

func (_ByContra) String() string { return "ByContra" }
func (_ByContra) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_ByContra{ByContra: &emptypb.Empty{}}
}
func (_ByContra) apply(p Prop) *SubGoals { return tactic.ByContraTactic(p) }

type _Symm struct{}

func (_Symm) String() string { return "Symm" }
func (_Symm) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Symm{Symm: &emptypb.Empty{}}
}
func (_Symm) apply(p Prop) *SubGoals { return tactic.SymmTactic(p) }

// _SubstStep substitutes using the equality at hyps[hypIndex]. The
// proto carries hyp_index so the step is replayable.
type _SubstStep struct{ hypIndex int }

func (step _SubstStep) String() string {
	return fmt.Sprintf("Subst on hyp %d", step.hypIndex)
}
func (step _SubstStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Subst{Subst: int32(step.hypIndex)}
}
func (step _SubstStep) apply(p Prop) *SubGoals {
	return tactic.SubstTactic(step.hypIndex)(p)
}

// _RwStep is the directed rewrite-to-fixpoint on the equality at
// hyps[hypIndex]: rewrites the oriented LHS to the oriented RHS across
// the conclusion and all other hyps (flip reverses the orientation).
// The proto carries both the index and the flag so replay is
// deterministic — the tactic is a pure function of (goal, hypIndex,
// flip); structural matching only (no unify budget).
type _RwStep struct {
	hypIndex int
	flip     bool
	// ctx is runtime-only: a session's step is cut off by it, between
	// the passes of the fixpoint (tactic.RwHypTacticUntil). nil for a
	// step that is recorded or replayed, which runs to its end.
	ctx context.Context
}

func (step _RwStep) String() string {
	if step.flip {
		return fmt.Sprintf("Rw on hyp %d (flipped)", step.hypIndex)
	}
	return fmt.Sprintf("Rw on hyp %d", step.hypIndex)
}
func (step _RwStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Rw{Rw: &RwProto{
		HypIndex: int32(step.hypIndex),
		Flip:     step.flip,
	}}
}
func (step _RwStep) apply(p Prop) *SubGoals {
	return tactic.RwHypTacticUntil(step.ctx, step.hypIndex, step.flip)(p)
}

// _TransStep splits ⊢ a = c via the agent-supplied middle term.
type _TransStep struct{ middle Term }

func (step _TransStep) String() string {
	return fmt.Sprintf("Trans via: %s", ext.PrintTerm(step.middle))
}
func (step _TransStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Trans{Trans: b.TermRef(step.middle)}
}
func (step _TransStep) apply(p Prop) *SubGoals {
	return tactic.TransTactic(step.middle)(p)
}

type _Congr struct{}

func (_Congr) String() string { return "Congr" }
func (_Congr) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Congr{Congr: &emptypb.Empty{}}
}
func (_Congr) apply(p Prop) *SubGoals { return tactic.CongrTactic(p) }

// _CongrArgStep is forward congruence on an equality hyp: hyps[hypIndex]
// `a = b` plus the agent-supplied function `fn` yields the added hyp
// `fn(a) = fn(b)` (Lean congrArg). The proto carries both
// the function term and the index so replay is deterministic.
type _CongrArgStep struct {
	fn       Term
	hypIndex int
}

func (step _CongrArgStep) String() string {
	return fmt.Sprintf("CongrArg hyp %d via: %s", step.hypIndex, ext.PrintTerm(step.fn))
}
func (step _CongrArgStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_CongrArg{CongrArg: &CongrArgProto{
		Function: b.TermRef(step.fn),
		HypIndex: int32(step.hypIndex),
	}}
}
func (step _CongrArgStep) apply(p Prop) *SubGoals {
	return tactic.CongrArgTactic(step.fn, step.hypIndex)(p)
}

// _CongrFunStep is the dual of _CongrArgStep: function-equality hyp
// `f = g` at hyps[hypIndex] plus the agent-supplied argument `arg`
// yields the added hyp `f(arg) = g(arg)` (Lean congrFun).
type _CongrFunStep struct {
	arg      Term
	hypIndex int
}

func (step _CongrFunStep) String() string {
	return fmt.Sprintf("CongrFun hyp %d via: %s", step.hypIndex, ext.PrintTerm(step.arg))
}
func (step _CongrFunStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_CongrFun{CongrFun: &CongrFunProto{
		Argument: b.TermRef(step.arg),
		HypIndex: int32(step.hypIndex),
	}}
}
func (step _CongrFunStep) apply(p Prop) *SubGoals {
	return tactic.CongrFunTactic(step.arg, step.hypIndex)(p)
}

// _ClearHypsStep drops the SET of hyps at hypIndices in ONE step (one
// child `Γ\{dropped} ⊢ G`). Sound by weakening (the child has a subset
// of the hyps), so reconstruction is the identity. All indices refer to
// this step's own goal — the set is removed atomically, so there is no
// sequential index shifting and the step is replayable from the index
// list alone. One ministep / one tree node however many hyps are swept.
type _ClearHypsStep struct{ hypIndices []int }

func (step _ClearHypsStep) String() string {
	return fmt.Sprintf("ClearHyps %v", step.hypIndices)
}
func (step _ClearHypsStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	indices := make([]int32, len(step.hypIndices))
	for i, idx := range step.hypIndices {
		indices[i] = int32(idx)
	}
	return &StepProto_ClearHyps{ClearHyps: &ClearHypsProto{HypIndices: indices}}
}
func (step _ClearHypsStep) apply(p Prop) *SubGoals {
	return tactic.ClearHypsTactic(step.hypIndices)(p)
}

// _Arith is THE unified num-arithmetic ministep. Deep-rewrites the goal via
// tactic.ArithTactic, whose body is the unified deep+fixpoint
// `omega.ArithDecideWithHyps`: a single `prop.BasicRewritesWith` invocation
// over [identity-law leaf, atom-decision leaf, all the standard basic
// rewrites] — bool/cond/quantifier/neg collapses are part of the same
// fixpoint pass, so cascades like `a + Cond(a=a, 0, 1) → a` happen in one
// call (decide `a=a→⊤`, Cond(⊤,0,1)→0, a+0→a). Produces ONE child with the
// rewritten conclusion; a fully-decidable goal becomes `⊢ ⊤` which
// `_TrivialSimplify` closes via DerivesTrue, so the standard composite
// (`ApplyArithSimplify`) is just _Arith + _TrivialSimplify.
//
// It is ONE ministep where four could stand: (a) a close-only ring →
// linarith dispatch, (b) a hyp-free comparison rewriter, (c) the identity
// laws, (d) a composite chaining them. The single ministep records every
// successful arith application under one proto tag (`arith=42`); the rule
// cascade is encoded in the rewrite, not in the ministep chain.
//
// The proof is determined by the goal. Soundness rides on omega's leaves
// returning ok=false (never a fabricated cert) when they can't derive a
// real proof, so a contingent atom is left undecided and never poisons its
// siblings.
type _Arith struct {
	// rounds is runtime-only and set by a caller that runs the step in
	// rounds, the By composite's arith closer: nil for a step that stands
	// alone, which is what is recorded and replayed.
	rounds *_ArithRounds
	// ctx is runtime-only: the decision is cut off by it, before a leaf
	// of the decider (omega.ArithPolicy.Stop). nil for a step that is
	// recorded or replayed, which runs to its end.
	ctx context.Context
}

// _ArithRounds is what the rounds of one arith close share with their
// Arith firings: the rewrites a firing passes over, and the rewrite the
// latest firing made, of a hypothesis or of the conclusion.
type _ArithRounds struct {
	passOver []tactic.ArithRewrite
	fired    tactic.ArithRewrite
}

func (_Arith) String() string { return "Arith" }
func (_Arith) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Arith{Arith: &emptypb.Empty{}}
}
func (x _Arith) apply(p Prop) *SubGoals {
	policy := omega.UnscopedArithPolicy()
	policy.Stop = x.ctx
	return x.applyWithPolicy(p, policy, nil)
}

func (x _Arith) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	if scope == nil {
		return x.apply(p)
	}
	policy := scope.ArithPolicy()
	policy.Stop = x.ctx
	out := x.applyWithPolicy(p, policy, libraryReader(scope))
	if out != nil {
		// A step that fired is a use the proof's family recorder writes
		// as the member's capability edges.
		scope.RecordArith(p)
	}
	return out
}

func (x _Arith) applyWithPolicy(p Prop, policy omega.ArithPolicy, reader *omega.LibraryReader) *SubGoals {
	if x.rounds == nil {
		return tactic.ArithTactic(p, policy, reader)
	}
	out, fired := tactic.ArithTacticPassingOver(p, policy, reader, x.rounds.passOver)
	x.rounds.fired = fired
	return out
}

// _RingNormalize is the `ring_nf` ministep — the ring normal form as a
// REWRITE, beside the Arith step's closer: every arithmetic subterm of the
// conclusion and of each hypothesis is rewritten to the sum of monomials
// the ring normalizer reads, unit coefficients and a zero constant elided
// (omega.RingNormalizeRewrite), to a fixpoint over the targets, so two
// spellings of one polynomial meet as one term for every step that
// follows. Parameterless and deterministic, so replay re-runs it; no CNF
// key. Its leaves are the ring vocabulary's own identities, which the
// Arith step's closer rests on too, so it runs under the same policy
// gate and records the same capability edge.
type _RingNormalize struct {
	// ctx is runtime-only: the rewrite is cut off by it, before a
	// subterm is normalized (omega.ArithPolicy.Stop). nil for a step
	// that is recorded or replayed, which runs to its end.
	ctx context.Context
}

func (_RingNormalize) String() string { return "RingNf" }
func (_RingNormalize) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_RingNormalize{RingNormalize: &emptypb.Empty{}}
}
func (x _RingNormalize) apply(p Prop) *SubGoals {
	policy := omega.UnscopedArithPolicy()
	policy.Stop = x.ctx
	return tactic.RingNfTactic(p, policy)
}

func (step _RingNormalize) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

func (x _RingNormalize) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	if scope == nil {
		return x.apply(p)
	}
	policy := scope.ArithPolicy()
	policy.Stop = x.ctx
	out := tactic.RingNfTactic(p, policy)
	if out != nil {
		scope.RecordArith(p)
	}
	return out
}

// _AutoDenote is the abbreviation ministep — "let x = ⟨term⟩". It runs
// in one of two modes:
//
//   - EXPLICIT (term != nil): name THAT subterm by THAT variable. What a
//     hand-written proof spells, and what every fresh recording replays
//     as. A term the goal does not contain panics at this step.
//   - SEARCH (term == nil): the selection heuristic picks the subterm —
//     ext.FrequentSubTerms at sizeThreshold, or the leading ε-term when
//     hilbert. This is the stage auto / expand run, and the mode every
//     proto recorded before the explicit form decodes into.
//
// A SEARCH firing RECORDS its choice: applyRecording hands the selected
// term and minted name back, and proto() writes them, so the persisted
// step is what was decided rather than a recipe replay must re-derive
// against a goal that may have drifted. The search itself is unchanged.
type _AutoDenote struct {
	sizeThreshold int
	hilbert       bool
	// comprehension is the conditioning stage's extended trigger for
	// denotation: search mode picks a set_comprehension-headed application
	// regardless of size. IN-MEMORY ONLY — applyRecording converts every
	// search firing to the explicit form, so no proto carries it.
	comprehension bool
	// term / name carry the explicit choice. term == nil ⇒ search mode.
	term core.Term
	name string
	// let is the DEFINITIONAL mode (LetTerm / Argument.Let): the
	// equation joins the hypotheses and the goal keeps its form, the
	// term needing no occurrence. Explicit only.
	let bool
	// optional relaxes the explicit mode's absent-term panic into a
	// plain "tactic did not apply". IN-MEMORY ONLY, never serialized
	// (same convention as _LemmaTactic.polymorphicSourceKey): it is a
	// property of the CALLER, not of the step — By's shaping preamble
	// runs the same denote across a fan of leaves and only some of them
	// carry the term. A step that did apply records without it, so
	// replay gets the strict contract, which is correct: at replay the
	// term is there by construction.
	optional bool
}

func (step _AutoDenote) String() string {
	if step.let {
		return "Let."
	}
	return _AUTO_DENOTE
}

func (step _AutoDenote) proto(b *ext.PoolBuilder) isStepProto_Step {
	p := &AutoDenoteProto{Hilbert: step.hilbert, Let: step.let}
	if !step.hilbert {
		// Kept populated in both modes: it is what emit renders as
		// `Denote(n)`, and a size-only decode is exactly the legacy
		// heuristic mode.
		p.SizeThreshold = int32(step.sizeThreshold)
	}
	if step.term != nil {
		p.Term = b.TermRef(step.term)
		p.Name = step.name
	}
	return &StepProto_Denote{p}
}

func (step _AutoDenote) apply(p Prop) *SubGoals {
	if step.term != nil {
		switch {
		case step.let:
			return tactic.LetTermTactic(step.term, step.name)(p)
		case step.hilbert && step.optional:
			return tactic.HilbertDenoteTermTacticOptional(step.term, step.name)(p)
		case step.hilbert:
			return tactic.HilbertDenoteTermTactic(step.term, step.name)(p)
		case step.optional:
			return tactic.DenoteTermTacticOptional(step.term, step.name)(p)
		default:
			return tactic.DenoteTermTactic(step.term, step.name)(p)
		}
	}
	if step.hilbert {
		return tactic.HilbertDenoteTactic(p)
	}
	if step.comprehension {
		return tactic.DenoteComprehensionTactic()(p)
	}
	return tactic.DenoteTactic(step.sizeThreshold)(p)
}

// applyRecording is the optional Step hook (see GoalStackNode.runStep)
// that lets a step record what its apply DID rather than what it was
// asked to do. A search-mode denote comes back explicit — same subgoals,
// same minted variable, now with the choice written down.
func (step _AutoDenote) applyRecording(p Prop, _ *ProofScope) (_Step, *SubGoals) {
	if step.term != nil {
		subGoals := step.apply(p)
		// The caller's tolerance is not part of the record — see the
		// `optional` field.
		step.optional = false
		return step, subGoals
	}
	var sel tactic.DenoteSelection
	var subGoals *SubGoals
	switch {
	case step.hilbert:
		subGoals = tactic.HilbertDenoteTacticRecording(p, &sel)
	case step.comprehension:
		subGoals = tactic.DenoteComprehensionTacticRecording(&sel)(p)
	default:
		subGoals = tactic.DenoteTacticRecording(step.sizeThreshold, &sel)(p)
	}
	if subGoals == nil || sel.Term == nil {
		return step, subGoals
	}
	step.term, step.name = sel.Term, sel.Name
	return step, subGoals
}

type _LemmaTactic struct {
	lemma Prop
	cases []Case
	// polymorphicSourceKey carries the key (lemmaSourceKey) of the
	// PRE-adaptation lemma when applyLemma / ApplyLemma's
	// tryAdaptLemmaTypes substituted the lemma's type-vars to fit the
	// goal's type context. The `lemma` field above is the POST-adaptation
	// form (used at session/replay runtime); the polymorphic source from
	// which it was derived is what a registry entry is keyed by, so emit's
	// leaf resolution must resolve against this key — never against the
	// adapted form, whose key generally keys no entry (and in pathological
	// cases — e.g. when the goal IS the def-axiom's type-instance —
	// equals the goal's own key, producing a self-reference rejection).
	//
	// In-memory only; NOT serialized to the proto. Emit reads this
	// field via GoalStackNode.PolymorphicSourceKeys() to resolve the
	// step's external leaf, which is the only path that needs it.
	//
	// Empty when no adaptation happened (the `lemma` field IS the
	// pre-adaptation form). In that case emit falls back to the
	// Normalize+AlphaKey lookup on `lemma`, which works because no
	// type-substitution was applied.
	polymorphicSourceKey core.PropKey
}

func (step _LemmaTactic) String() string {
	return fmt.Sprintf("Thm:\n%s", prop.PrintProp(step.lemma))
}

func (step _LemmaTactic) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Lemma{Lemma: b.PropRef(step.lemma)}
}

func (step _LemmaTactic) apply(p Prop) *SubGoals {
	return tactic.LemmaTactic(step.lemma)(p)
}

func (step _LemmaTactic) caseBodies() []Case { return step.cases }

// _LemmaPreserveTactic is the hypothesis-preserving counterpart of
// _LemmaTactic, used by the agent-facing session `lemma` dispatch.
// Same wire payload (the lemma prop), but replay uses
// tactic.LemmaPreserveTactic — the full LemmaTactic chain whose result
// is accepted only when every pre-existing goal hyp survives, falling
// back to a plain add-as-hyp otherwise (no simplifyNewGoal whole-
// context re-normalization). This is the engine-side fix for
// `lemma` re-normalizing the hyp context and dropping previously-built
// ground instantiations.
//
// Carrying its own ministep tag (rather than changing _LemmaTactic)
// keeps the two chains distinct and replay deterministic: a `lemma`
// step replays through LemmaTactic (destructive simplify included),
// while an agent session's `lemma` records `lemma_preserve` and replays
// through the preserving chain.
type _LemmaPreserveTactic struct {
	lemma Prop
	// polymorphicSourceKey — same role as _LemmaTactic.polymorphicSourceKey.
	// See the comment there.
	polymorphicSourceKey core.PropKey
}

func (step _LemmaPreserveTactic) String() string {
	return fmt.Sprintf("LemmaPreserve:\n%s", prop.PrintProp(step.lemma))
}

func (step _LemmaPreserveTactic) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_LemmaPreserve{LemmaPreserve: b.PropRef(step.lemma)}
}

func (step _LemmaPreserveTactic) apply(p Prop) *SubGoals {
	return tactic.LemmaPreserveTactic(step.lemma)(p)
}

// _LeanRwTactic is the explicit equational-rewrite counterpart of
// _LemmaTactic. Same wire payload (the lemma prop) and same dispatch
// signature, but replay uses tactic.LeanRwTactic — only the rewrite
// path, with the size-decrease guard inside eqSimplify bypassed.
//
// Carrying its own ministep tag (rather than overloading _LemmaTactic
// with a flag) lets serialized session proofs replay deterministically:
// LemmaTactic and LeanRwTactic can produce different SubGoals for the
// same lemma+goal (LemmaTactic falls back to conclMatch / hypMatch
// when eq-rewrite is rejected by the size guard; LeanRwTactic bypasses
// the guard and never falls back), so the wire tag must record which
// dispatch was used.
type _LeanRwTactic struct {
	lemma Prop
	// polymorphicSourceKey — same role as _LemmaTactic.polymorphicSourceKey.
	// See the comment there.
	polymorphicSourceKey core.PropKey
}

func (step _LeanRwTactic) String() string {
	return fmt.Sprintf("LeanRw:\n%s", prop.PrintProp(step.lemma))
}

func (step _LeanRwTactic) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_LeanRw{LeanRw: b.PropRef(step.lemma)}
}

func (step _LeanRwTactic) apply(p Prop) *SubGoals {
	// ORDER IS LOAD-BEARING for replay compatibility. The whole corpus of
	// recorded LeanRw protos was produced by the general LeanRwTactic
	// path, so it must stay the FIRST responder: TryDefExpand in front
	// changes the SubGoals shape on every `⊢ C = f` lemma (two-child
	// [lemma, rewrittenGoal] + hyp coverage vs the recorded
	// conclusion-rewrite) and breaks recorded proofs' replays with
	// `leaf goal AlphaKey diverges`. The general path does not hang on
	// an identity-shaped def: the flipped identity def
	// `⊢ (λp.p) = set_comprehension` is a variable-LHS rule whose peeled
	// unify pattern would absorb any (A→bool)-typed subterm, wrapping it
	// `t → set_comprehension(λx.t̃(x))` (t̃ a βη-variant that dodges the
	// IsSub self-embed check) and re-firing the mergeTactics fixpoint on
	// its own output forever; prop.unifyEq bans variable-LHS rules
	// (ext/prop/eq_rewrite.go), so on such defs the general path yields
	// nil and the TryDefExpand fallback below handles the unfold.
	// prop.TestUnifyEqRewrite_RefusesVariableLHSRule pins the ban.
	if sg := tactic.LeanRwTactic(step.lemma)(p); sg != nil {
		return sg
	}
	// Capability fallback, NOT a fast path: fires only where the general
	// path yields nothing, which is exactly the two def_expand walls —
	//   - polymorphic `⊢ C = f` lemmas on goals with type-var scaffolding
	//     (tryAdaptLemmaTypes returns nil; TryDefExpand re-instantiates
	//     the def thm per occurrence via constTerm.DefThm()), and
	//   - the target const occurring ONLY in hyps (the general path
	//     rewrites the conclusion).
	// Deterministic on (lemma, goal), so new recordings that commit a
	// fallback result replay through the same nil-then-fallback route.
	return tactic.TryDefExpand(step.lemma, p)
}

// _TypeInstStep closes a goal that is a type instantiation of a polymorphic
// source theorem. The source is carried as a proved Thm wrapped in a Prop
// field; apply() runs PropTypeMatch against the current goal to recover the
// type substitution, then core.PropTypeInst produces the ground
// thm. Returns nil if the goal is not actually a type instance of the source.
type _TypeInstStep struct {
	source Prop // polymorphic parent; must be Proved()

	// sourceEntryKey — the key of the registry entry `source` was loaded
	// from, when the committer knew it (ApplyTypeInstWithKey). Same role
	// and same in-memory-only convention as
	// _KnownThmStep.sourceEntryKey: emit resolves the leaf through it
	// directly instead of re-deriving the key from `source`.
	sourceEntryKey core.PropKey
}

func (step _TypeInstStep) String() string {
	return fmt.Sprintf("TypeInst from:\n%s", prop.PrintProp(step.source))
}

func (step _TypeInstStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_TypeInst{TypeInst: b.PropRef(step.source)}
}

func (step _TypeInstStep) apply(p Prop) *SubGoals {
	// source may be a promise (a cited sibling member's result on the
	// define-then-run path): a realized source is Proved(), a deferred one
	// IsPromised(). The type-match below is statement-level, and
	// core.PropTypeInst threads a promise into a derived promise (deriveProp),
	// so the cite closes p without forcing the source.
	Assert(step.source != nil && (step.source.Proved() || core.IsPromised(step.source)))
	tiDebug := os.Getenv("TYPEINST_DEBUG") != ""
	// `step.source` is usually in its normalized form (a ThmCache tier-3
	// hit hands the normalized polymorphic source; the exceptions are
	// below). We need a type substitution σ such
	// that step.source[σ] closes `p`. Two ways to discover σ:
	//
	//   1. Structural type-match against raw `p`. Uses the underlying
	//      prop.IsTypeMatchOf directly — that's the pure
	//      structural α-match (no normalization assumption on either
	//      side, no contract about canonical equality orientation /
	//      quantifier ordering / etc). When this succeeds the returned
	//      σ satisfies step.source[σ] α= p, so the instantiated Thm
	//      proves `p` directly — no reconstruct callback needed.
	//
	//      Critical for engine.go::runAutoMatchTypeInstance's
	//      extensionality-divergence fallback: when a type-var was
	//      bound to a function type, Normalize expands `a = b` via
	//      funext into `∀x. a(x) = b(x)`, destroying the type-skeleton.
	//      Source (at abstract type-var A) never had that expansion,
	//      so normalized-vs-normalized misses the match while
	//      raw-vs-raw structural still succeeds.
	//
	//   2. NormalizedPropTypeMatch on `Normalize(p)` vs `step.source`.
	//      Both sides are then in canonical form per the function's
	//      contract. Used when the raw structural match misses —
	//      typically because `p` carries hyps (Normalize moves them
	//      into the conclusion as ¬h ∨ … ∨ φ) or uses a non-canonical
	//      orientation that Normalize canonicalizes. The instantiated
	//      source proves the normalized form; reconstruct lifts that
	//      back to a proof of `p`.
	if substs, ok := prop.IsTypeMatchOf(step.source, p, utils.FullPredicate); ok && len(substs) > 0 {
		// Statement-level: source[σ] α= p by the structural match, so the
		// instantiation (a derived promise when source is one) closes p. No
		// .AsThm() — forcing is deferred to the top promise.
		instantiated := core.PropTypeInst(step.source, substs...)
		if IsStronger(instantiated, p) {
			return tactic.MakeEmptySubGoals(p, instantiated)
		}
		if tiDebug {
			fmt.Fprintf(os.Stderr, "[TYPEINST] attempt1 matched but IsStronger failed\n  inst: %s\n", prop.PrintProp(instantiated))
		}
	} else if tiDebug {
		fmt.Fprintf(os.Stderr, "[TYPEINST] attempt1 IsTypeMatchOf miss (ok=%v, nsubsts=%d)\n", ok, len(substs))
	}
	// Attempt 1.5: NORMALIZED source vs RAW goal. A recorded TypeInst goal is
	// often the source's normalized image verbatim (the session's auto-match
	// produced it from Normalize(source)[σ]); re-normalizing that goal in
	// attempt 2 can SHIFT it (Normalize's ∀-binder order is type-dependent,
	// so the already-normalized instance is not a Normalize fixpoint at its
	// concrete types), losing a match that the normalized source finds
	// directly against the raw goal. It is its own attempt because emit
	// hands the source in RAW form (which attempt 1 needs for the
	// binder-merge class — see typeInstSourceExpr).
	normSource, _ := Normalize(step.source)
	if substs, ok := prop.IsTypeMatchOf(normSource, p, utils.FullPredicate); ok && len(substs) > 0 {
		instantiated := core.PropTypeInst(normSource, substs...)
		if IsStronger(instantiated, p) {
			return tactic.MakeEmptySubGoals(p, instantiated)
		}
	} else if tiDebug {
		fmt.Fprintf(os.Stderr, "[TYPEINST] attempt1.5 miss; normSource: %s\n", prop.PrintProp(normSource))
	}
	// Attempt 1.6: INSTALL-FORM source vs RAW goal. A premise claim is the
	// dep's install form (InstallForm: the statement's own binder
	// sharing) at a type instance, verbatim; the canonical source of
	// attempt 1.5 may share a clause's binders otherwise and so not
	// type-match it, and attempt 2's structural search below must then
	// derive σ across two differently identified forms. The install form
	// of the source type-matches its own image directly.
	installSource := InstallForm(step.source)
	if substs, ok := prop.IsTypeMatchOf(installSource, p, utils.FullPredicate); ok && len(substs) > 0 {
		instantiated := core.PropTypeInst(installSource, substs...)
		if IsStronger(instantiated, p) {
			return tactic.MakeEmptySubGoals(p, instantiated)
		}
	} else if tiDebug {
		fmt.Fprintf(os.Stderr, "[TYPEINST] attempt1.6 miss; installSource: %s\n", prop.PrintProp(installSource))
	}
	// Attempt 1.7: the source's PREFIX TELESCOPE vs RAW goal. A By grounds
	// a witnessed premise in its stated form read at the tuple (step_by.go:
	// prop.PrefixTelescope at the tuple's length, the hypotheses about the
	// grounded binders ahead of the binders left), so a polymorphic
	// premise's claim obligation is that telescope at the tuple's type
	// instance. The normalized attempts below see through the telescope
	// but not through every instance: Normalize funext-expands an
	// equation at a letter instantiated to a function type
	// (finite_set.FiniteInductSupport's `x = a` at A := set(A)), and the
	// instance's normal form is then no type instance of the source's.
	// The goal's own ∀-prefix is the telescope's length, so one telescope
	// is the candidate, matched raw as in attempt 1; the source's own
	// form comes back where it has no telescope at that length.
	if pVars, _ := ext.DecomposesFORALL(p.Conclusion()); !pVars.Empty() {
		telescope := prop.PrefixTelescope(step.source, pVars.Size())
		if substs, ok := prop.IsTypeMatchOf(telescope, p, utils.FullPredicate); ok && len(substs) > 0 {
			instantiated := core.PropTypeInst(telescope, substs...)
			if IsStronger(instantiated, p) {
				return tactic.MakeEmptySubGoals(p, instantiated)
			}
		} else if tiDebug {
			fmt.Fprintf(os.Stderr, "[TYPEINST] attempt1.7 miss; telescope: %s\n", prop.PrintProp(telescope))
		}
	}
	normP, reconstruct := Normalize(p)
	if tiDebug {
		fmt.Fprintf(os.Stderr, "[TYPEINST] normP: %s\n", prop.PrintProp(normP))
		sv, _ := ext.DecomposesFORALL(normSource.Conclusion())
		pv, _ := ext.DecomposesFORALL(normP.Conclusion())
		fmt.Fprintf(os.Stderr, "[TYPEINST] binder counts: normSource=%d normP=%d\n", sv.Size(), pv.Size())
	}
	// NormalizedPropTypeMatch requires BOTH args already normalized (it does
	// not canonicalize internally). The doc above assumes step.source is
	// pre-normalized — true when it comes from a cache lookup, but
	// NOT on a member's replay path, where a TypeInst source is a prior
	// SECTION's ProvedThm carrying its text α-form (e.g. snd's lemma2 proves
	// the `∃-inside` text `∀P.∀x.((∃y...)∨...)` while its key —
	// and the recorded TypeInst source — is the `∃-outside` normalized form
	// `∀P.∀x.∃y.(...)`). Without normalizing the source, the match against
	// normP misses and the step fails even though the goal IS a type instance
	// of the source's normal form. Normalize preserves provedness (see
	// PreCNFCache.Normalize), so normSource is a proved normalized prop we can
	// type-instantiate; reconstruct then lifts normP back to p. Idempotent for
	// already-normalized sources (no behavior change for the cache path).
	// (normSource computed once above, for attempt 1.5.)
	substs, ok := NormalizedPropTypeMatch(normSource, normP)
	if !ok {
		// Attempt 3: normalized-vs-normalized modulo ∀-prefix PERMUTATION.
		// Normalize's ∀-binder canonical order is TYPE-dependent, so a type
		// INSTANCE can normalize with a different binder order than its
		// polymorphic source: Normalize(source)[σ] ≠ Normalize(source[σ]) in
		// binder order (the engine-side auto-match documents the same wart —
		// see applyAutoMatchTypeInstanceOnRoots's binder-order-divergence
		// fallback, which the SESSION escaped through by matching the RAW
		// original source; replay gets the dep's NORMALIZED statement from
		// emit and has no raw form to fall back to). Strip both prefixes,
		// type-match the bodies with the source's binders as term slots, and
		// rebuild in the target's binder order — the final α-check guards
		// the whole derivation, so a miss degrades to the old panic path.
		if bridged := typeInstMatchModuloBinderOrder(normSource, normP); bridged != nil {
			return tactic.MakeEmptySubGoals(p, reconstruct(bridged))
		}
		// Attempt 4: Normalize's disjunct order is type-dependent too, so
		// the instance can list the source's literals in another order as
		// well as its binders.
		if bridged := typeInstMatchModuloDisjunctOrder(normSource, normP); bridged != nil {
			return tactic.MakeEmptySubGoals(p, reconstruct(bridged))
		}
		return nil
	}
	instantiated := core.PropTypeInst(normSource, substs...)
	// reconstruct lifts the normalized instantiation back to p's α-form; both
	// are statement-level (Prop in/out) and thread a promise dependency
	// through as a derived promise — forced only when the top promise is.
	reconstructed := reconstruct(instantiated)
	return tactic.MakeEmptySubGoals(p, reconstructed)
}

// typeInstMatchModuloBinderOrder recovers a _TypeInstStep close when source
// and goal are both normalized but their ∀-prefixes are PERMUTED relative to
// each other (Normalize's binder order is type-dependent; it does not commute
// with type instantiation). Returns the source-derived Prop in the target's
// exact α-form, or nil when the two are not prefix-permuted type instances.
//
// Statement-level throughout (PropWrapper ops thread a promise-backed source
// as a derived promise). Soundness: the returned prop is derived from
// `normSource` by PropTypeInst, instantiation of every binder and re-generalization only, and the final
// AlphaEquals(normP) check rejects anything that isn't exactly the goal.
func typeInstMatchModuloBinderOrder(normSource, normP Prop) Prop {
	sVars, sBody := ext.DecomposesFORALL(normSource.Conclusion())
	pVars, pBody := ext.DecomposesFORALL(normP.Conclusion())
	if sVars.Empty() || sVars.Size() != pVars.Size() {
		if os.Getenv("TYPEINST_DEBUG") != "" {
			fmt.Fprintf(os.Stderr, "[TYPEINST] attempt3 bail: sVars=%d pVars=%d\n", sVars.Size(), pVars.Size())
		}
		return nil
	}
	// The source's stripped binders are the term slots; its type vars are
	// the instantiable ones (FullPredicate — same footing as the two match
	// attempts above).
	substs, ok := typematch.TypeOnlyMatch(sBody, pBody,
		func(v core.VarTerm) bool { return sVars.Has(v) },
		utils.FullPredicate)
	if !ok {
		if os.Getenv("TYPEINST_DEBUG") != "" {
			fmt.Fprintf(os.Stderr, "[TYPEINST] attempt3 TypeOnlyMatch miss\n")
		}
		return nil
	}
	inst := prop.WrapProp(core.PropTypeInst(normSource, substs...))
	stripped, _ := inst.StripConclForAll()
	regen := make([]core.VarTerm, 0, pVars.Size())
	for v := range pVars.Iter() {
		regen = append(regen, v)
	}
	out := stripped.ConclForAllList(regen...)
	if out == nil || !out.AlphaEquals(normP) {
		return nil
	}
	return out
}

// typeInstMatchModuloDisjunctOrder recovers a _TypeInstStep close when the
// goal's normal form lists the source's disjuncts in another order:
// Normalize sorts the literals of a clause, as it sorts the ∀-prefix, by
// type-dependent keys, so Normalize(source)[σ] and Normalize(source[σ])
// can differ in both. σ is found by type-matching the source's literals
// against the goal's under some bijection, the instantiated source is
// normalized again, and only a result α-equal to the goal is returned —
// derived from `normSource` by PropTypeInst and Normalize alone.
// Statement-level throughout, as typeInstMatchModuloBinderOrder.
func typeInstMatchModuloDisjunctOrder(normSource, normP Prop) Prop {
	sVars, sBody := ext.DecomposesFORALL(normSource.Conclusion())
	pVars, pBody := ext.DecomposesFORALL(normP.Conclusion())
	if sVars.Size() != pVars.Size() {
		return nil
	}
	sLits, pLits := ext.DecomposesOR(sBody), ext.DecomposesOR(pBody)
	if len(sLits) < 2 || len(sLits) != len(pLits) {
		return nil
	}
	slot := func(v core.VarTerm) bool { return sVars.Has(v) }
	// Each source literal is placed at a goal position it type-matches
	// alone; a full placement is accepted only when the whole reordered
	// body matches with one substitution. The budget bounds the
	// placements tried on a clause of many look-alike literals.
	placed := make([]core.Term, len(pLits))
	used := make([]bool, len(sLits))
	budget := 1 << 12
	var found []core.TypeSubst
	var search func(j int) bool
	search = func(j int) bool {
		if j == len(pLits) {
			budget--
			substs, ok := typematch.TypeOnlyMatch(ext.Or(placed...).Core(), pBody, slot, utils.FullPredicate)
			found = substs
			return ok
		}
		for i, literal := range sLits {
			if used[i] || budget <= 0 {
				continue
			}
			if _, ok := typematch.TypeOnlyMatch(literal, pLits[j], slot, utils.FullPredicate); !ok {
				continue
			}
			used[i], placed[j] = true, literal
			if search(j + 1) {
				return true
			}
			used[i] = false
		}
		return false
	}
	if !search(0) || len(found) == 0 {
		return nil
	}
	instance, _ := Normalize(core.PropTypeInst(normSource, found...))
	if !instance.AlphaEquals(normP) {
		return nil
	}
	return instance
}

type _CNFRefute struct {
	env *ProverEnv
	ctx context.Context
	// missReadByCaller is set by a caller whose own failure message
	// answers, for a strict cache MISS, whether the leaf closes under
	// Basic() — the By executor's CNF closer. Every other refute (a
	// Calc leg, a kit's terminal, the set driver's own) has the answer
	// appended to the MISS here. Runtime-only.
	missReadByCaller bool
}

func (_CNFRefute) String() string { return _CNF_REFUTE }

func (_CNFRefute) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_CnfRefute{&emptypb.Empty{}}
}

func (step _CNFRefute) apply(p Prop) *SubGoals {
	if !step.missReadByCaller && !cnfCacheOnlyProbe(step.ctx) {
		// A cache-only probe's MISS is recovered and read by no one; a
		// strict replay's is the author's next decision.
		defer func() {
			if r := recover(); r != nil {
				panic(cnfMissWithBasicCheck(r, p))
			}
		}()
	}
	if thm := step.env.tryCNFRefute(step.ctx, p); thm != nil {
		return tactic.MakeEmptySubGoals(p, thm)
	}
	return nil
}

// cnfMissWithBasicCheck answers, on a strict CNF-cache MISS, the one
// question the MISS leaves open: does the goal want the refuter at all.
// A goal a plain Basic() closes never did — recording its key ships a
// certificate for a step with no search in it — and one Basic() does
// not close is a refute to record, or a divergence to debug, as the
// MISS says. The By executor asks the same of its own leaf
// (byClosesUnderBasic); this is the answer for a refute reached any
// other way. Any other panic passes through unchanged.
func cnfMissWithBasicCheck(r any, goal Prop) any {
	text := fmt.Sprint(r)
	if !strings.Contains(text, "CNF cache MISS") {
		return r
	}
	if auditBasicCloses(context.Background(), goal) {
		return text + "\n  (Checked: this goal closes under Basic(), so the refuter was never wanted here and NO " +
			"key should be recorded for it — close it with Basic(), or state the step as By(Normalized, …).)"
	}
	return text + "\n  (Checked: this goal does NOT close under Basic(), so no shaping stands in for this refute.)"
}

// effectiveCnfTimeout is the live-search budget one tryCNFRefute call
// runs under: env.CnfRefuterTimeout, unless an agent caller stamped a
// per-call override on ctx (clamped to MaxEffectiveCnfTimeoutMs). A
// result <= 0 is the replay-mode sentinel — no live search happens.
//
// Split out of cnfRefuteContexts so the `by` failure diagnostic can
// name the budget the closer actually ran under without restating the
// rule; a second copy of the override+clamp would drift.
func (env *ProverEnv) effectiveCnfTimeout(parentCtx context.Context) time.Duration {
	timeout := env.CnfRefuterTimeout
	if v := parentCtx.Value(CnfRefuterTimeoutCtxKey); v != nil {
		if d, ok := v.(time.Duration); ok && d > 0 {
			if maxD := MaxEffectiveCnfTimeoutMs * time.Millisecond; d > maxD {
				d = maxD
			}
			timeout = d
		}
	}
	return timeout
}

// cnfRefuteContexts derives the two contexts one tryCNFRefute call uses, from
// parentCtx and the effective per-call timeout. The caller MUST defer the
// returned cancel.
//
// Timeout: env.CnfRefuterTimeout by default (the programmatic-search caller caps
// each AutoExpand attempt individually). An agent caller (apply/probe with
// budget_ms) stamps a CnfRefuterTimeoutCtxKey override on ctx to land the whole
// budget on one call; it is clamped to MaxEffectiveCnfTimeoutMs.
//
// Two contexts, distinguished only when timeout <= 0:
//   - preludeCtx bounds the pre-CNF wave (CreateRefuterFromPreNormalized) and
//     the cache-hit reconstruction. With a positive budget it is the timeout ctx
//     (so the agent's budget caps the prelude too); with timeout <= 0 it is
//
// parentCtx — unbounded but fast — so a cached proof can still emit.
//   - proveCtx bounds the live refuter search (r.Prove). With a positive budget
//     it is the same timeout ctx; with timeout <= 0 it is an already-cancelled
//     ctx so a cache MISS aborts immediately.
//
// timeout <= 0 is the replay-mode sentinel (env.CnfRefuterTimeout = 0): cache
// hits reconstruct under parentCtx, misses abort at once. Collapsing both into
// one WithTimeout(parentCtx, 0) — an already-expired context — would kill cache
// hits too (the regression from "fix engine timeout passing").
func (env *ProverEnv) cnfRefuteContexts(parentCtx context.Context) (preludeCtx, proveCtx context.Context, cancel func()) {
	// Strict replay (RequireCNFCacheHit) never runs a live search — a cache miss
	// or a stored-proof reconstruction failure panics rather than falling back to
	// the refuter. So the CnfRefuterTimeout (a live-SEARCH budget) has nothing
	// legitimate to bound here; applying it would only impose a wall-clock
	// deadline on the DETERMINISTIC pre-CNF normalization wave and the stored-proof
	// reconstruction. Under CPU contention (e.g. the parallel TestReplayAll fan-
	// out) that deadline spuriously expires and turns a perfectly valid cached
	// proof into a bogus "stale cnf_proofs row / FAILED to reconstruct" panic —
	// the long-mislabeled "nondeterministic CNF reconstruction". Force the
	// replay-mode sentinel regardless of the env's nominal timeout (testenv sets
	// 5s): prelude/reconstruction run under parentCtx (unbounded but deterministic
	// and fast), proveCtx is pre-cancelled since no live search is reached. This is
	// the same return as the timeout<=0 branch below.
	if env.RequireCNFCacheHit || cnfCacheOnlyProbe(parentCtx) {
		expired, cancel := context.WithCancel(parentCtx)
		cancel()
		return parentCtx, expired, func() {}
	}
	timeout := env.effectiveCnfTimeout(parentCtx)
	if timeout > 0 {
		ctx, cancel := context.WithTimeout(parentCtx, timeout)
		return ctx, ctx, cancel
	}
	expired, cancel := context.WithCancel(parentCtx)
	cancel() // already-cancelled prove ctx aborts a MISS immediately
	return parentCtx, expired, func() {}
}

// captureOnlyClosePromise is the CNFCacheCaptureOnly close for a CNF cache
// HIT: an honest IOU whose statement is the refute goal and whose builder
// reconstructs the stored proof on Force — never a fabricated cert. In the
// capture pass (emit's CollectCNFCache) the goal stacks are throwaway and
// nothing forces the close, so the reconstruction cost stays zero —
// exactly the capture-only contract. If something ever DOES force it, it runs the real
// reconstruction and fails loudly on a stale blob instead of standing on a
// forged kernel cert.
//
// reconstruct runs under the FORCE-time context (the Forcer's), never the
// capture-time preludeCtx — that one is cancelled when tryCNFRefute returns.
func captureOnlyClosePromise(goal Prop, cnfKey core.PropKey,
	reconstruct func(context.Context) ThmCert) Thm {
	return core.Promise(goal, func(f core.Forcer) core.ThmCert {
		thm := reconstruct(f.Context())
		if thm.IsZero() {
			panic(fmt.Sprintf("captureOnlyClosePromise: stored CNF proof for %s "+
				"FAILED to reconstruct at force — stale cnf_proofs row", cnfKey))
		}
		bridged := prop.WeakenTo(thm, goal)
		if bridged == nil {
			panic(fmt.Sprintf("captureOnlyClosePromise: reconstructed thm for %s "+
				"does not weaken to the refute goal", cnfKey))
		}
		return bridged.AsThmCert()
	})
}

// choiceFunctionOfHypothesis proves a goal `Γ ⊢ ∃f. ∀x̄. P[f(x̄)]` from a
// hypothesis `∀x̄. ∃y. P` of Γ: the two share one normal form through the
// Skolem stage (prop.SkolemEqBridge), and the bridge carries the
// hypothesis to the goal — no search and no key. The refuter is the
// wrong tool for this goal: it reads the conclusion negated, where f is a
// universal variable and the x̄ are Skolem functions of it, and finds f by
// higher-order unification, once for every literal that reads it.
//
// Only a conclusion that binds a function, against a ∀-headed
// hypothesis, is normalized; nil for every other goal, and where no
// hypothesis's form is the conclusion's.
func choiceFunctionOfHypothesis(goal Prop) Thm {
	conclusion := goal.Conclusion()
	witness := ext.MatchesEXISTS(conclusion)
	if witness.IsZero() || !ext.IsFunType(witness.Var().Type()) {
		return nil
	}
	for h := range goal.HypIter() {
		if ext.MatchesFORALL(h).IsZero() {
			continue
		}
		if bridge := prop.SkolemEqBridge(h, conclusion); bridge != nil {
			return core.AsThm(bridge.EqMP(prop.Assume(h)))
		}
	}
	return nil
}

func (env *ProverEnv) tryCNFRefute(parentCtx context.Context, goal Prop) Thm {
	// Per-hypothesis CNF preprocessing is split into
	// prelude (PreCNFNormalizeTerm, cached on raw key) → middle
	// (Skolemization) → tail (denote + distribute + per-clause). The
	// two-level cache lives on env.CnfNormalizeCache; an opportunistic
	// shape check in cnfNormalizeWorkFlowFromPreNormalized further skips
	// TrivialNormalize when the pre-CNF hyp has no ⇔/∃!/COND/Hilbert/
	// FunEq gap patterns left to rewrite.
	//
	// preludeCtx caps the pre-CNF wave + cache-hit reconstruction, proveCtx the
	// live search; both honor the agent's budget. See cnfRefuteContexts.
	preludeCtx, proveCtx, cancel := env.cnfRefuteContexts(parentCtx)
	defer cancel()

	// A goal that states the choice function of a hypothesis is that
	// hypothesis, read through the Skolem stage: closed on the two
	// normalizations, before a refuter that would have to find the
	// function is built.
	if thm := choiceFunctionOfHypothesis(goal); thm != nil {
		noteByClose(parentCtx, "choice function of a hypothesis (no key)")
		return thm
	}

	cnfNormalizeCache := env.cnfNormalizeCache()
	r := refuter.CreateRefuterFromPreNormalized(preludeCtx, goal, cnfNormalizeCache)
	if r == nil {
		return nil
	}

	// refuted directly by cnf maker.
	if r.Refuted() {
		noteByClose(parentCtx, "cnf prelude (no key)")
		return r.ProvedThm()
	}

	// env.CnfNormalizeCache.PreCNF (a *prop.PreCNFCache, alias) backs both
	// the per-hyp term-level pre-CNF rewrites consumed by the refuter
	// prelude AND the prop-level Normalize result below — the same cache
	// instance amortizes both, so a RefuteProp this caller normalizes
	// twice (here vs. its caller's key lookup, etc.) only pays the
	// pipeline cost once.
	// RESOLUTION IS REACHED: the prelude above closed nothing, and the
	// next line computes the key a refute here would need. This is the
	// one point where "the refuter was needed" is true, so both halves
	// of the By economy audit read it here and nowhere earlier — the
	// stage's entry and the step's entry each precede a prelude that
	// closes leaves keylessly, and probes placed there disagreed with
	// the cold recorder (seven "load-bearing" markers that cost no key).
	//   - Probe A's capture: the leaf as it reaches resolution.
	//   - The keyless rung: reaching here IS failure.
	//   - The audit's replay probe: reaching here at a key the audited
	//     close did not touch is failure, before the store serves it.
	if st := byAuditStateOf(parentCtx); st != nil {
		st.preClose = append(st.preClose, goal)
	}
	if noRefuteProbe(parentCtx) {
		panic("tryCNFRefute[noRefuteProbe]: the leaf reached resolution — not closed without the refuter")
	}
	// The key is the normal form of the whole refute prop, a run of
	// seconds on a wide leaf — every hypothesis moved into one disjunction,
	// whose quantifier block is then canonicalized — and it polls the
	// request's context inside (PreCNFCache.NormalizeUntil): a request
	// that ended raises a utils.Cut there, which unwinds to the owner of
	// the run with no key computed and nothing kept. The refuter's own
	// budget does not cut it: the key is what a stored certificate is
	// served under, whatever time the search is given. The refuter keeps
	// the form (KeyForm), so the reading of a certificate found under the
	// key does not compute it again.
	storage := env.ProofService
	var store CNFStore
	if storage != nil {
		store = storage.CNFStore
	}
	// The exact key is asked first: the refute prop's own AlphaKey, which
	// costs nothing beside the CNF just built. The store's exact-key table
	// names the certificate recorded for this very refute prop, and a
	// certificate that closes the leaf here costs no normal form at all —
	// the reading of a certificate of the refuter's own clauses normalizes
	// nothing (refuter.ReconstructStoredProof). Where the table has no
	// row, or its row's certificate is gone or does not reconstruct, the
	// key is computed below as it is without the table: the table is an
	// index of the certificates, and nothing is decided on what it lacks.
	// The audit's replay probe is held to the rows of the close it audits,
	// by their keys, and takes the key's route alone.
	exactKey := r.CNF().RefuteProp().AlphaKey()
	if store != nil && auditReplayOf(parentCtx) == nil {
		if key := store.ReadExactKey(exactKey); key != "" {
			if proof := store.ReadProof(key); proof != nil {
				// The capture-only path, as at the key's lookup below.
				if env.CNFCacheCaptureOnly {
					noteCNFGoal(store, key, goal)
					noteByClose(parentCtx, "cnf cached certificate")
					proofBlob, meta := proof, env.ProofService.LoadConstMeta
					return captureOnlyClosePromise(goal, key,
						func(ctx context.Context) ThmCert {
							return r.ReconstructStoredProof(ctx, proofBlob, cnfNormalizeCache, meta)
						})
				}
				if thm := r.ReconstructStoredProof(
					preludeCtx, proof, cnfNormalizeCache, env.ProofService.LoadConstMeta); !thm.IsZero() {
					noteCNFGoal(store, key, goal)
					noteByClose(parentCtx, "cnf cached certificate")
					noteRecordKey(parentCtx, key)
					return thm
				}
			}
		}
	}
	// A rung asked on exact keys alone ends here, with nothing normalized
	// (exactKeysOnlyKey).
	if exactKeysOnly(parentCtx) {
		panic("tryCNFRefute[exactKeysOnly]: no certificate closes the leaf under its refute prop's own key")
	}
	normalizedCNFProp := r.KeyForm(parentCtx, cnfNormalizeCache)
	cnfKey := normalizedCNFProp.AlphaKey()
	if replay := auditReplayOf(parentCtx); replay != nil {
		if !replay.rows.holdsKey(cnfKey) {
			// A recording of this spelling would be served the row, if the
			// store holds it, or search for it and write it: either way a
			// row the audited close does not touch.
			if store != nil && cnfStoreHoldsProof(store, cnfKey) {
				replay.offRows = true
			}
			panic("tryCNFRefute[auditReplayProbe]: the leaf needs a certificate the audited close does not read")
		}
		// A row of the audited close's that the probe's spelling reads too.
		replay.read.addKey(cnfKey)
	}

	// Look up the stored CNF refute proof and (on a hit) replay it. The
	// reconstruction tolerates a stale stored proof whose clause inferences
	// no longer reproduce by returning nil (any panic inside is recovered
	// to nil). `cacheHit` distinguishes a genuine MISS (key absent) from a
	// HIT-but-reconstruction-failure — the two have different meanings and
	// the strict path below reports them distinctly.
	cacheHit := false
	var cachedThm ThmCert
	if store != nil {
		if proof := store.ReadProof(cnfKey); proof != nil {
			cacheHit = true
			noteCNFGoal(store, cnfKey, goal)
			// Capture-only path (emit's CollectCNFCache). The blob has now
			// been read — and CollectCNFCache's CapturingCNFStore has
			// captured it. emit must NOT reconstruct: reconstruction is the
			// REPLAY oracle's job (TestReplayAll), where a failure is a
			// real, correctly-located signal. Running it at emit (a) makes
			// emit needlessly invoke the refuter on a cache hit and (b)
			// would surface any reconstruction nondeterminism as a
			// misleading "the stored proof is broken" emit failure, when
			// emit in fact did everything right (correct key, correct
			// blob). So on a hit we close the
			// Auto/CnfRefute step with a reconstruct-at-force promise
			// (captureOnlyClosePromise) — nothing forces it in the capture
			// pass, so no reconstruction runs here; the emitted Go is
			// verified at replay. A genuine MISS still falls through to the
			// RequireCNFCacheHit panic below.
			if env.CNFCacheCaptureOnly {
				noteByClose(parentCtx, "cnf cached certificate")
				proofBlob, meta := proof, env.ProofService.LoadConstMeta
				return captureOnlyClosePromise(goal, cnfKey,
					func(ctx context.Context) ThmCert {
						return r.ReconstructStoredProof(ctx, proofBlob, cnfNormalizeCache, meta)
					})
			}
			// Replay the stored proof against r (built from this goal). Returns
			// nil if the stored proof is stale / no longer reconstructs; the
			// strict path below distinguishes that from a key miss.
			cachedThm = r.ReconstructStoredProof(
				preludeCtx, proof, cnfNormalizeCache, env.ProofService.LoadConstMeta)
		}
	}

	// Strict mode (member replay with the family blob installed, or emit's
	// CollectCNFCache against the session's store): a refute that reaches
	// the resolution stage MUST be served from the stored cache. There is
	// NO live-refute fallback here — a cache MISS or a reconstruction
	// FAILURE is a real signal, not something to silently paper over by
	// re-proving. See ProverEnv.RequireCNFCacheHit.
	if env.RequireCNFCacheHit || cnfCacheOnlyProbe(parentCtx) {
		if !cacheHit {
			panic(fmt.Sprintf("tryCNFRefute[RequireCNFCacheHit]: CNF cache MISS for %s — "+
				"the proof needs a CNF refute the store this env reads does not hold. Either the "+
				"key was never written there (member replay: a new or changed member — run the "+
				"family CNF recorder; emit-section: the session's refute left no certificate "+
				"under this key), or the goal reaching this step differs from the one recorded "+
				"(a divergence: debug it — recording over it masks the bug). Do NOT live-refute.\n"+
				"  goal key: %s\n  goal: %s", cnfKey, goal.AlphaKey(), prop.PrintProp(goal)))
		}
		if cachedThm.IsZero() {
			panic(fmt.Sprintf("tryCNFRefute[RequireCNFCacheHit]: cached CNF proof for %s FAILED "+
				"to reconstruct — the stored clause inference no longer reproduces (stale "+
				"cnf_proofs row). Reprove; do NOT live-refute.", cnfKey))
		}
		noteByClose(parentCtx, "cnf cached certificate")
		noteRecordKey(parentCtx, cnfKey)
		return cachedThm
	}

	// Non-strict (live prover / session): use the cache
	// when it reconstructs, else run a live refute and cache the result.
	if !cachedThm.IsZero() {
		noteByClose(parentCtx, "cnf cached certificate")
		noteRecordKey(parentCtx, cnfKey)
		return cachedThm
	}
	// Prove returns nil either when the refutation itself failed (ProvedThm
	// also nil) or when its self-consistency write gate rejected persisting
	// (ProvedThm non-nil — the in-process refutation is sound, only the row
	// is withheld). Persist only with a proto; succeed whenever the
	// refutation did.
	if proof := r.Prove(proveCtx); proof != nil {
		// An economy-audit probe answers a question and records NOTHING —
		// its refutes must not mint certificate rows (step_by.go's
		// byAuditProbeKey; a probe that persisted would turn the
		// report-only stage into a behaviour).
		if store != nil && !byAuditProbe(parentCtx) {
			// The certificate and, with it, the row that names it by the
			// refute prop it was searched for.
			store.WriteProof(cnfKey, proof)
			store.WriteExactKey(exactKey, cnfKey)
			noteCNFGoal(store, cnfKey, goal)
		}
	}
	// Explicit nil on failure: the return type is the Thm interface, and a
	// typed-nil ThmCert wrapped in it would defeat the callers' nil checks.
	if thm := r.ProvedThm(); !thm.IsZero() {
		noteByClose(parentCtx, "cnf live refute")
		noteRecordKey(parentCtx, cnfKey)
		return thm
	}
	noteRefuteCutOff(parentCtx, proveCtx, env.effectiveCnfTimeout(parentCtx))
	return nil
}

// _ByCaseStep performs boolean case analysis on caseTerm, producing two
// subgoals on the term under one leading ¬ — p for the case term ¬p,
// the term itself where it has none (tactic.ByCaseSides):
//
//	child(0) = p  ⊢ X
//	child(1) = ¬p ⊢ X
//
// Which child the case term HOLDS on is therefore the term's own
// polarity's to say; ByCaseBranch reads it for every named branch.
type _ByCaseStep struct {
	caseTerm Term
	cases    []Case
}

// ByCaseBranch is the child of a case split on caseTerm on which the
// term holds (holds true) or fails, with the hypothesis that child
// received. The term itself is child 0's hypothesis where it has no
// leading ¬ and child 1's where it has one (tactic.ByCaseSides); the
// child on which it fails is the other, its hypothesis the other side —
// p for the term ¬p, the ¬ contracted rather than stacked. Every named
// branch reads its child here: a.When / a.Otherwise, Assuming / Unless
// and the Facts a.Assuming / a.Unless bind, emit's branch tags.
func ByCaseBranch(caseTerm Term, holds bool) (child int, hyp Term) {
	caseTerm = ext.CoreOf(caseTerm)
	pos, neg := tactic.ByCaseSides(caseTerm)
	sides := [2]Term{pos, neg}
	if !pos.Equals(caseTerm) {
		Assert(neg.Equals(caseTerm))
		child = 1
	}
	if !holds {
		child = 1 - child
	}
	return child, sides[child]
}

func (step _ByCaseStep) String() string {
	return fmt.Sprintf("ByCase on: %s", ext.PrintTerm(step.caseTerm))
}

func (step _ByCaseStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_ByCase{ByCase: b.TermRef(step.caseTerm)}
}

func (step _ByCaseStep) apply(p Prop) *SubGoals {
	return tactic.ByCaseTactic(step.caseTerm)(p)
}

func (step _ByCaseStep) caseBodies() []Case { return step.cases }

// _AssertStep introduces a hyp-free boolean claim φ as a sub-claim of
// the current goal, producing two subgoals:
//
//	child(0) = claim:    Γ ⊢ φ
//	child(1) = residual: Γ, φ ⊢ G
//
// φ must be a hyp-free Prop; the kernel-level invariant is enforced by
// tactic.AssertTactic. The proto carries φ as a HolPropProto so the
// step is replayable. Distinct from _ByCaseStep — assert is a single
// directional sub-claim (Coq `assert` / Lean `have h : φ := …`); it
// does NOT introduce ¬φ on a second branch.
type _AssertStep struct {
	claim Prop // hyp-free; conclusion is the asserted term
	cases []Case
}

func (step _AssertStep) String() string {
	return fmt.Sprintf("Assert: %s", prop.PrintProp(step.claim))
}

func (step _AssertStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Assert{Assert: b.PropRef(step.claim)}
}

func (step _AssertStep) apply(p Prop) *SubGoals {
	return tactic.AssertTactic(step.claim)(p)
}

func (step _AssertStep) caseBodies() []Case { return step.cases }

// _ExistentialConstDefStep reads a const `c` whose definition is a
// choice, `⊢ c = εx.P(x)`, by its two obligations, through
// prop.ExistentialConstDef:
//
//	child(0) = Γ ⊢ ∃x.P(x)       (existence claim)
//	child(1) = Γ, P(c) ⊢ G        (residual with P(c) as a free hyp)
//
// c stays folded on both children. The def-expand composite is the
// other reading of the same definition: it opens c to its ε-term and
// its tidy closes P(c) against a resident existence (step_composite.go).
// This step is for the author who wants the two obligations as cases —
// the choice pair of peano's indSucSpec, or P(c) as a hypothesis toward
// a goal that is not P(c) itself.
//
// Wire payload is just the const; replay re-runs
// prop.ExistentialConstDef to rebuild the bridge thm.
type _ExistentialConstDefStep struct {
	constTerm ConstTerm
	cases     []Case
}

func (step _ExistentialConstDefStep) String() string {
	return fmt.Sprintf("ExistentialConstDef: %s", ext.PrintTerm(step.constTerm))
}

func (step _ExistentialConstDefStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	Assert(!step.constTerm.IsZero())
	return &StepProto_ExistentialConstDef{
		ExistentialConstDef: b.TermRef(step.constTerm),
	}
}

func (step _ExistentialConstDefStep) apply(p Prop) *SubGoals {
	Assert(!step.constTerm.IsZero())
	bridge := prop.ExistentialConstDef(step.constTerm)
	return tactic.ExistentialConstDefTacticFromBridge(bridge)(p)
}

func (step _ExistentialConstDefStep) caseBodies() []Case { return step.cases }

// _InductionStep applies structural induction on inductVar using the
// inductive type's induction principle (template). For num/list/option
// this produces 2 subgoals (base + step with IH for the recursive
// constructor); for sum this also produces 2 (no IH on either case);
// types with multiple recursive constructors would produce more.
//
// template must be non-nil at apply() time. getStep returns a
// template-less placeholder for proto roundtrip / inspection; a replay
// resolves the template from its ProverEnv (Script.InductStep /
// ApplyInduction) before applying.
type _InductionStep struct {
	inductVar core.VarTerm
	template  *tactic.InductionTemplate

	cases []Case
}

func (step _InductionStep) caseBodies() []Case { return step.cases }

func (step _InductionStep) String() string {
	return fmt.Sprintf("Induction on: %s", ext.PrintTerm(step.inductVar))
}

func (step _InductionStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_Induction{Induction: b.TermRef(step.inductVar)}
}

func (step _InductionStep) apply(p Prop) *SubGoals {
	if step.template == nil {
		return nil
	}
	return tactic.GeneralInductionTactic(step.inductVar, step.template)(p)
}
