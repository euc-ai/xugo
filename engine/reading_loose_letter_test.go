package engine

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
)

// The chains' module over a ring at A: a module_on whose vectors are
// D → A, with the chapter's own D, and a sum indexed by num.
const looseLetterChainsLeaf = "R:ring_ops(A), M:module_ops(A, D → A), s:set(num), F:(num → (D → A)) ⊢ " +
	"module_on(R, M) ⇒ finite(s) ⇒ (∀x:num. x ∈ s ⇒ F(x) ∈ M.carrier) ⇒ " +
	"module_sum(M.add, M.zero, s, F) ∈ M.carrier"

// TestByTactic_LooseReadingUnderAHypothesisSpellingItsLetter:
// module.ModuleSumIn's index letter D is loose, and the chains' module
// spells D in its vectors' type. Read at that hypothesis and grounded at
// s, a set of num, the law is cited beside the hypothesis with the two
// records prefixed, and the witness table resolves: the reading's loose
// letter is the law's, not the vectors'.
func TestByTactic_LooseReadingUnderAHypothesisSpellingItsLetter(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, looseLetterChainsLeaf, "strip_imp", "strip_imp", "strip_imp")
	s, err := e.getSession(sid)
	require.NoError(t, err)
	goal := s.goalIndex[gid].node.Goal
	// The kernel orders hypotheses; the structure fact is found by its head.
	structure := -1
	for i := range goal.NumHyps() {
		if strings.HasPrefix(ext.PrintTerm(goal.Hyp(i)), "module_on(") {
			structure = i
		}
	}
	require.NotEqual(t, -1, structure)
	loose := LemmaWithSpec{Key: "module.ModuleSumIn", ReadAt: &ReadAtSpec{HypIndex: &structure},
		TermSpecialize: map[string]string{"s": "s", "F": "F"}}

	specs, _, _, err := e.byReadingPremises(s, goal, loose, nil)
	require.NoError(t, err)
	require.Len(t, specs, 2, "the law grounded, then the hypothesis it is read under")
	assert.Len(t, specs[0].Witnesses, 4, "the two records, then s and F")
	assert.True(t, specs[1].Resident)
}
