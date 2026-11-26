// dump_section.go — the `dump-section` RPC: the preorder step+goal walk
// of one section's proof tree. Proved interiors are invisible to the
// open-leaf goal index, so this is how a section's proof is READ — a
// resumed lineage's sections, or the author's own closed section when
// its leaves need mathematical labels (the curate phase's labeling
// pass).

package engine

import (
	"fmt"

	"github.com/euc-ai/xugo/prover/proof"
)

// SectionDumpNode is one node of a section's proof tree, preorder.
type SectionDumpNode struct {
	// Path addresses the node from the section root (child indices),
	// matching GoalStackNode.NodeAt. Empty = the root itself.
	Path      []int  `json:"path"`
	Depth     int    `json:"depth"`
	Step      string `json:"step,omitempty"` // ministep that expanded this node; "" = unexpanded leaf
	Statement string `json:"statement"`
	// StatementTyped is the parse-faithful rendering of the node's goal
	// (binder types + free-var declaration prefix), present only when
	// the print → parse → α-key round-trip closes; paste it into
	// `add-goal {text}` verbatim. The plain Statement display drops
	// those annotations and does NOT round-trip. See FormatStatementTyped.
	StatementTyped string `json:"statement_typed,omitempty"`
	Proved         bool   `json:"proved"`
}

// SectionDump is the DumpSection result.
type SectionDump struct {
	SectionID int               `json:"section_id"`
	Proved    bool              `json:"proved"`
	NumNodes  int               `json:"num_nodes"` // total nodes in the tree (pre-truncation)
	Truncated bool              `json:"truncated"`
	Nodes     []SectionDumpNode `json:"nodes"`
	// Cards lists the cards the section's leaves closed by (defer.go).
	Cards []DeferredCard `json:"cards,omitempty"`
}

// defaultSectionDumpCap bounds the dump size; a large case body runs to
// thousands of nodes and the agent should page through it deliberately
// rather than receive a context-blowing wall.
const defaultSectionDumpCap = 400

// DumpSection returns the preorder step+goal walk of one section's
// proof tree. maxNodes <= 0 selects the default cap; the dump reports
// Truncated when the tree exceeds it.
func (e *Engine) DumpSection(sessionID string, sectionIdx, maxNodes int) (*SectionDump, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if sectionIdx < 0 || sectionIdx >= len(s.sections) {
		return nil, fmt.Errorf("section %d out of range (session has %d sections)", sectionIdx, len(s.sections))
	}
	if maxNodes <= 0 {
		maxNodes = defaultSectionDumpCap
	}
	sec := s.sections[sectionIdx]
	dump := &SectionDump{
		SectionID: sectionIdx,
		Proved:    sec.root.Proved(),
		Cards:     sec.status(sectionIdx, s.Spelling()).Cards,
	}
	var walk func(n *proof.GoalStackNode, path []int, depth int)
	walk = func(n *proof.GoalStackNode, path []int, depth int) {
		dump.NumNodes++
		if len(dump.Nodes) < maxNodes {
			typed, _ := s.Spelling().Typed(n.Goal)
			dump.Nodes = append(dump.Nodes, SectionDumpNode{
				Path:           append([]int(nil), path...),
				Depth:          depth,
				Step:           n.StepDescription(),
				Statement:      s.Spelling().Prop(n.Goal),
				StatementTyped: typed,
				Proved:         n.Proved(),
			})
		}
		for i, c := range n.Children() {
			walk(c, append(path, i), depth+1)
		}
	}
	walk(sec.root, nil, 0)
	dump.Truncated = dump.NumNodes > len(dump.Nodes)
	return dump, nil
}
