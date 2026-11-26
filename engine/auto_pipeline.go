package engine

// runAutoPipeline is the post-commit auto pass every tactic step,
// session setup and checkpoint restore runs: it closes the leaves a
// PROVED sibling section states (runAutoMatch). It never cites the
// library — a registry entry enters a proof only where the author names
// it (`lemma`, a by / auto_with / simp_with premise, `known`), so what a
// session records does not depend on which theorems happen to be
// registered.
func (s *Session) runAutoPipeline() []AutoMatchedGoal {
	return s.runAutoMatch()
}
