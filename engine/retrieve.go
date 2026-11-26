package engine

import (
	"context"
	"fmt"
	"time"
)

// Default per-strategy cap. Caller can override via MaxPerGroup.
const retrieveDefaultPerGroup = 10

// Retrieve answers a lemma lookup over the corpus. The agent picks one
// mode (goal / consts / name_pattern / related_to); the engine returns
// the proof registry's members grouped by the strategy that produced
// them (retrieve_corpus.go), reported by their registered names. There
// is no global ranking — per-strategy scores are not comparable across
// groups, and a fused ranking is a fiction the agent should not rely
// on.
func (e *Engine) Retrieve(ctx context.Context, sessionID string, req *RetrieveRequest) (*RetrieveResult, error) {
	if req == nil {
		return nil, fmt.Errorf("retrieve request is required")
	}
	limit := req.MaxPerGroup
	if limit <= 0 {
		limit = retrieveDefaultPerGroup
	}
	start := time.Now()
	res := &RetrieveResult{Groups: []RetrieveGroup{}}

	switch req.Mode {
	case RetrieveByGoal, "":
		// Default mode is "by goal", against the session's focused goal.
		if sessionID == "" {
			return nil, fmt.Errorf("retrieve mode=goal requires session_id")
		}
		s, err := e.getSession(sessionID)
		if err != nil {
			return nil, err
		}
		s.mu.Lock()
		entry, focusedID, err := e.resolveFocusedGoal(s, req.GoalID)
		s.mu.Unlock()
		if err != nil {
			return nil, err
		}
		if entry == nil {
			return res, nil
		}
		res.GoalID = focusedID

		budgetMs := req.BudgetMs
		if budgetMs <= 0 {
			budgetMs = 3000
		}
		deadline := start.Add(time.Duration(budgetMs) * time.Millisecond)
		scan := scanGoal(entry.node.Goal, deadline)
		if g, ok := corpusByGoal(scan, limit, deadline); ok {
			res.Groups = append(res.Groups, g)
		}
		if g, ok := corpusReadings(scan, limit, deadline); ok {
			res.Groups = append(res.Groups, g)
		}
	case RetrieveByConsts:
		if len(req.Consts) == 0 {
			return nil, fmt.Errorf("retrieve mode=consts requires non-empty consts list")
		}
		if g, ok := corpusByConsts(req.Consts, limit); ok {
			res.Groups = append(res.Groups, g)
		}
	case RetrieveByName:
		if req.NamePattern == "" {
			return nil, fmt.Errorf("retrieve mode=name_pattern requires non-empty name_pattern")
		}
		if g, ok := corpusByName(req.NamePattern, limit); ok {
			res.Groups = append(res.Groups, g)
		}
	case RetrieveByRelated:
		if req.RelatedTo == "" {
			return nil, fmt.Errorf("retrieve mode=related_to requires non-empty related_to (an entry name or key)")
		}
		res.Groups = append(res.Groups, corpusRelated(req.RelatedTo, limit)...)
	default:
		return nil, fmt.Errorf("unknown retrieve mode %q (expected goal | consts | name_pattern | related_to)", req.Mode)
	}

	res.ElapsedMs = int(time.Since(start).Milliseconds())
	return res, nil
}
