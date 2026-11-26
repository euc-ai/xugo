package engine

import (
	"context"
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ElementarityRef names one thing an `elementarity` call reads: a registered
// corpus entry, by its registered name or its own key, or a hypothesis
// of the focused goal, by index.
type ElementarityRef struct {
	Key      string `json:"key,omitempty"`
	HypIndex *int   `json:"hyp_index,omitempty"`
}

// applyElementarityOnClone runs the elementarity step as a session move —
// Go's ByElementarity — recorded as ONE `elementarity` ministep
// (StepProto_Elementarity), which emit renders back as the ByElementarity call.
// The source is an entry stating the property at a concrete structure,
// a resident family of models by prime, or absent; the facts are
// resident hypotheses and entries, the structure's closed-field fact
// among them. The terms are the parameters of the fixed-parameter
// form .At, parsed against the goal. Close-or-fail: a refusal names
// what the call lacks.
func (e *Engine) applyElementarityOnClone(ctx context.Context, s *Session, clone *proof.GoalStackNode, req TacticReq) error {
	goal := clone.Goal
	var spec proof.ElementaritySpec
	hyp := func(what string, i int) error {
		if i < 0 || i >= goal.NumHyps() {
			return fmt.Errorf("elementarity: %s names hypothesis %d of a goal with %d", what, i, goal.NumHyps())
		}
		return nil
	}
	entry := func(what, keyOrName string) (string, error) {
		if d, ok := registry.ByName(keyOrName); ok {
			return d.Name, nil
		}
		if d, ok := registry.ByKey(keyOrName); ok {
			return d.Name, nil
		}
		return "", fmt.Errorf("elementarity: %s %q names no corpus entry: %w", what, keyOrName, e.lemmaKeyMiss(keyOrName))
	}
	if src := req.ElementaritySource; src != nil {
		switch {
		case src.Key != "" && src.HypIndex != nil:
			return fmt.Errorf("elementarity: the source names an entry or a hypothesis, not both")
		case src.Key != "":
			name, err := entry("the source", src.Key)
			if err != nil {
				return err
			}
			spec.Entry = name
		case src.HypIndex != nil:
			if err := hyp("the source", *src.HypIndex); err != nil {
				return err
			}
			spec.Family = goal.Hyp(*src.HypIndex)
		}
	}
	for i, f := range req.ElementarityFacts {
		switch {
		case f.Key != "" && f.HypIndex != nil:
			return fmt.Errorf("elementarity: facts[%d] names an entry or a hypothesis, not both", i)
		case f.Key != "":
			name, err := entry(fmt.Sprintf("facts[%d]", i), f.Key)
			if err != nil {
				return err
			}
			spec.FactEntries = append(spec.FactEntries, name)
		case f.HypIndex != nil:
			if err := hyp(fmt.Sprintf("facts[%d]", i), *f.HypIndex); err != nil {
				return err
			}
			spec.Facts = append(spec.Facts, goal.Hyp(*f.HypIndex))
		default:
			return fmt.Errorf("elementarity: facts[%d] names nothing — give key or hyp_index", i)
		}
	}
	for i, text := range req.Terms {
		t, err := e.resolveTermWithFallback(text, goal, nil, s.familyScope())
		if err != nil {
			return fmt.Errorf("elementarity: terms[%d], the parameter %q: %w", i, text, err)
		}
		spec.Params = append(spec.Params, t)
	}
	spec.Library = func(name string) (core.Prop, error) {
		p, err, ok := e.registryLemma(s, name)
		if !ok {
			return nil, fmt.Errorf("the corpus has no entry %s: %w", name, e.lemmaKeyMiss(name))
		}
		if err != nil {
			return nil, err
		}
		if p.Proved() || core.IsPromised(p) {
			return p, nil
		}
		backed, _ := s.corpusBackedInjection(core.PropKey(name), p, func(q core.Prop) core.Prop { return q })
		return backed, nil
	}
	return proof.ApplyElementarityStep(clone, s.env, ctx, spec)
}
