package engine

// focusedGoalIDForTest returns the id of the one open goal, for tests
// that step a goal twice; "" when there is not exactly one.
func (s *Session) focusedGoalIDForTest() string {
	found := ""
	for id, entry := range s.goalIndex {
		if entry.node.Proved() {
			continue
		}
		if found != "" {
			return ""
		}
		found = id
	}
	return found
}
