package proof

import (
	"context"
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/bridge"
	"github.com/euc-ai/xugo/prover/reify"
	"github.com/euc-ai/xugo/prover/tactic"
)

// _ElementarityStep is the elementarity step, a composite: ByElementarity's
// call, run by the one executor (prover/bridge.Elementarity) on the leaf.
// The goal is read as a first-order sentence, its bridge proved from the
// reifier's plan, and the sentence transferred from the source. The
// payload is the call: the source entry by its registered name or the
// resident family fact by its statement, the resident facts by their
// statements, the library facts by their registered names. The mode and
// theory the executor derives are recorded beside them and checked when
// the step runs again. Every library theorem the executor reads is the
// proof's own cite (the scope's), so the member's recorded dependencies
// hold it; the arithmetic it settles runs under the scope too, and
// records arith:nat there.
type _ElementarityStep struct {
	entry       string
	family      core.Term
	facts       []core.Term
	factEntries []string
	params      []core.Term

	recorded bool
	mode     bridge.Mode
	theory   bridge.Theory

	// library is the session's reading of a corpus theorem by its
	// registered name; nil in a proof, which reads through its scope
	// or the env.
	library func(name string) (core.Prop, error)

	env   *ProverEnv
	ctx   context.Context
	scope *ProofScope
}

func (step _ElementarityStep) String() string {
	var parts []string
	switch {
	case step.entry != "":
		parts = append(parts, step.entry)
	case step.family != nil:
		parts = append(parts, ext.PrintTerm(step.family))
	default:
		parts = append(parts, "nil")
	}
	for _, f := range step.facts {
		parts = append(parts, ext.PrintTerm(f))
	}
	parts = append(parts, step.factEntries...)
	call := fmt.Sprintf("ByElementarity(%s)", strings.Join(parts, ", "))
	if len(step.params) > 0 {
		var params []string
		for _, t := range step.params {
			params = append(params, ext.PrintTerm(t))
		}
		call += fmt.Sprintf(".At(%s)", strings.Join(params, ", "))
	}
	return call
}

func (step _ElementarityStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	payload := &ElementarityProto{
		Mode:        ElementarityProto_Mode(step.mode),
		Theory:      ElementarityProto_Theory(step.theory),
		FactEntries: step.factEntries,
	}
	switch {
	case step.entry != "":
		payload.Source = &ElementarityProto_Entry{Entry: step.entry}
	case step.family != nil:
		payload.Source = &ElementarityProto_Family{Family: b.PropRef(core.MakeProp(step.family))}
	}
	for _, f := range step.facts {
		payload.Facts = append(payload.Facts, b.PropRef(core.MakeProp(f)))
	}
	for _, t := range step.params {
		payload.Params = append(payload.Params, b.TermRef(t))
	}
	return &StepProto_Elementarity{Elementarity: payload}
}

func (step _ElementarityStep) apply(p Prop) *SubGoals { return step.applyScoped(p, nil) }

func (step _ElementarityStep) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	Assert(step.env != nil)
	if p.NumHyps() > 0 && p.Conclusion().Equals(ext.F) {
		panic("ByElementarity: the leaf is a ⊥-refutation; the elementarity step proves a proposition about a closed field")
	}
	call := bridge.Call{Goal: p.Conclusion(), Params: step.params}
	resident := func(who string, t core.Term) core.Prop {
		idx, err := findHypIndex(p, t)
		if err != nil {
			panic(fmt.Sprintf("ByElementarity: the %s %s names no hypothesis of this leaf\n  on leaf goal: %s", who, ext.PrintTerm(t), prop.PrintProp(p)))
		}
		return core.Assume(p.Hyp(idx))
	}
	for _, f := range step.facts {
		call.Facts = append(call.Facts, resident("fact", f))
	}
	lib := &_ElementarityLibrary{step: step, scope: scope}
	for _, name := range step.factEntries {
		call.Facts = append(call.Facts, lib.Theorem(name))
	}
	switch {
	case step.entry != "":
		call.Source = bridge.Source{Entry: step.entry}
	case step.family != nil:
		call.Source = bridge.Source{Family: resident("family of models", step.family)}
	}
	vocabulary, err := reify.NewVocabulary(lib.Constant)
	if err != nil {
		panic(fmt.Sprintf("ByElementarity: %v", err))
	}
	outcome, err := bridge.Elementarity(call, vocabulary, lib)
	if err != nil {
		panic(err.Error())
	}
	if step.recorded && (outcome.Mode != step.mode || outcome.Theory != step.theory) {
		panic(fmt.Sprintf("ByElementarity: the record says mode %d, theory %d; the executor derives mode %d, theory %d",
			step.mode, step.theory, outcome.Mode, outcome.Theory))
	}
	thm := outcome.Theorem
	return tactic.MakeSubGoals(p, func(...Prop) Prop { return thm })
}

func (step _ElementarityStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// _ElementarityLibrary is the executor's library: a theorem is the proof's
// own cite, read through the scope where the proof has one (its
// recorded dependencies then hold it), through the session's reading
// in a session, and through the env's library otherwise; a constant is
// the env's; arithmetic is the arith closer on a private goal under
// the scope.
type _ElementarityLibrary struct {
	step  _ElementarityStep
	scope *ProofScope
}

func (l *_ElementarityLibrary) Theorem(name string) core.Prop {
	if l.scope != nil && l.scope.cite != nil {
		return l.scope.cite(name)
	}
	if l.step.library != nil {
		thm, err := l.step.library(name)
		if err != nil {
			panic(fmt.Sprintf("ByElementarity: %v", err))
		}
		return thm
	}
	thm, ok := l.step.env.LookupLibraryThm(name)
	if !ok {
		panic(fmt.Sprintf("ByElementarity: no library theorem %q is bound in this env", name))
	}
	return thm
}

// StatingEntry names the corpus entry whose statement is p: the
// registry's key index, which library/registry installs. Nil where no
// corpus is loaded, and then no entry states anything.
var StatingEntry func(p core.Prop) (name string, ok bool)

func (l *_ElementarityLibrary) Stating(fact core.Term) core.Prop {
	if StatingEntry == nil {
		return nil
	}
	name, ok := StatingEntry(core.MakeProp(fact))
	if !ok {
		return nil
	}
	return l.Theorem(name)
}

func (l *_ElementarityLibrary) Constant(name core.TermName) core.ConstTermMeta {
	meta, ok := l.step.env.ProofService.LoadConstMeta(name)
	if !ok {
		return core.ConstTermMeta{}
	}
	return meta
}

func (l *_ElementarityLibrary) Arith(goal core.Prop) core.Prop {
	root := CreateGoalStack(goal)
	root.SetProofScope(l.scope)
	ctx := l.step.ctx
	if ctx == nil {
		ctx = context.Background()
	}
	ApplyArithSimplify(ctx, root)
	if !root.Proved() {
		return nil
	}
	return root.PromisedThm()
}

// ByElementarity proves the leaf, a proposition about a closed field, by
// elementarity: the proposition is read as a first-order sentence and
// carried over from source by elementary equivalence, or, with no
// source, the leaf is an iff read on both sides of an elementary
// embedding. source is a library entry stating the property at a
// concrete structure (its typed var), a resident fact giving a model of
// every prime characteristic (∀p. nat_prime(p) ⇒ ∃G.
// algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ Φ(G)),
// or nil. facts are what the step's obligations are discharged from:
// resident facts and library entries, the structure's closed-field fact
// among them, and the embedding's ring_homomorphism fact.
func ByElementarity(source any, facts ...any) ElementarityAction {
	return ElementarityAction{source: source, facts: facts}
}

// ElementarityAction is a ByElementarity call, an Action closing the leaf.
type ElementarityAction struct {
	source any
	facts  []any
	params []TermLike
}

// At is the fixed-parameter form: the source's property, unfolded,
// is instantiated at params, in the order of its ∀ binders, and its
// consequent there is the leaf. The property is transferred at a
// common degree bound of the polynomial parameters, taken from their
// membership facts among the call's facts; its other guards are
// facts too.
func (t ElementarityAction) At(params ...TermLike) ElementarityAction {
	t.params = append(t.params, params...)
	return t
}

func (t ElementarityAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("ByElementarity: no unsolved leaves remaining (section already proved — extra ByElementarity call?)" + closedLeafNote(root))
	}
	step := _ElementarityStep{}
	if t.source != nil {
		if dep, ok := t.source.(NamedDep); ok {
			step.entry = dep.DepName()
		} else {
			step.family = residentStatement("the source", premiseFact(t.source), anchor)
		}
	}
	for _, f := range t.facts {
		if dep, ok := f.(NamedDep); ok {
			step.factEntries = append(step.factEntries, dep.DepName())
			continue
		}
		step.facts = append(step.facts, residentStatement("a fact", premiseFact(f), anchor))
	}
	for _, p := range t.params {
		step.params = append(step.params, p.Core())
	}
	s.Do(root, step)
}

// residentStatement is the hypothesis of the leaf a resident fact names.
func residentStatement(what string, f Fact, anchor *GoalStackNode) core.Term {
	switch {
	case f.handle != nil:
		return anchor.Goal.Hyp(f.handle.resolveOrPanic("ByElementarity", anchor))
	case f.residentContent != nil:
		return contentHypTerm("ByElementarity", f.residentContent)
	}
	panic(fmt.Sprintf("ByElementarity: %s is neither a library entry nor a resident fact", what))
}

// ElementaritySpec is a session's ByElementarity call: the source entry by its
// registered name or the resident family fact by its statement, the
// resident facts by their statements, the library facts by their
// registered names, and the parameters of the fixed-parameter form
// .At. Library reads a corpus theorem by its registered name, as the
// session serves it.
type ElementaritySpec struct {
	Entry       string
	Family      core.Term
	Facts       []core.Term
	FactEntries []string
	Params      []core.Term
	Library     func(name string) (core.Prop, error)
}

// ApplyElementarityStep runs the elementarity step on n — the session's
// entry, the step Go's ByElementarity records. A refusal is returned as the
// error, its text the one a chapter author reads; a fault is no refusal,
// and is raised (rungFailure).
func ApplyElementarityStep(n *GoalStackNode, env *ProverEnv, ctx context.Context, spec ElementaritySpec) (err error) {
	defer func() {
		if r := rungFailure(recover()); r != nil {
			err = fmt.Errorf("elementarity: %v", r)
		}
	}()
	step := _ElementarityStep{entry: spec.Entry, family: spec.Family, facts: spec.Facts, factEntries: spec.FactEntries, params: spec.Params, library: spec.Library, env: env, ctx: ctx}
	if !n.runStep(step) {
		return fmt.Errorf("elementarity: the composite did not apply")
	}
	return nil
}
