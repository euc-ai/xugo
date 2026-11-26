// The lemma key slot's miss diagnostic.
//
// TacticReq.LemmaKey (and the WithLemmas[].Key slots that feed it —
// by / auto_with / simp_with) names a proof-registry entry by its own
// key (prop_<hash>) or its registered name (`nat_order.LessEqRefl`).
// Nothing else is citable there. lemmaKeyMiss says which spellings were
// consulted; a key that is a node of the session gets
// sessionNodeKeyMiss, which names the spelling that cites a proved
// section.
//
// Name matching is EXACT and case-sensitive.

package engine

import (
	"fmt"
	"regexp"
	"strconv"
	"strings"

	"github.com/euc-ai/xugo/library/registry"
)

// sessionNodeKeyMiss answers a key slot that holds a node of the
// session — a section's root id, open (`s0_gprop_…`) or closed
// (`s0_cprop_…`), which `inspect` prints beside every goal and which
// reads like a key. The slot names registry entries; a proved section
// is cited by its STATEMENT, as a text premise: the claim that premise
// leaves certifies against the section, and emit renders the cite as
// `At(<section>, w…)`. The message carries the statement to paste.
// Returns nil when the key is no node of the session.
func (e *Engine) sessionNodeKeyMiss(s *Session, key string) error {
	if s == nil {
		return nil
	}
	m := sessionNodeID.FindStringSubmatch(key)
	if m == nil {
		return nil
	}
	secIdx, err := strconv.Atoi(m[1])
	if err != nil || secIdx < 0 || secIdx >= len(s.sections) {
		return nil
	}
	root := s.sections[secIdx].root
	if root == nil {
		return nil
	}
	node, proved := root, root.Proved()
	if closed, _, ok := s.lookupClosedNode(key); ok {
		node, proved = closed, true
	} else if key != closedNodeID(secIdx, root.Goal) && key != fmt.Sprintf("s%d_g%s", secIdx, shortKey(root.Goal)) {
		return nil
	}
	if !proved {
		return fmt.Errorf("lemma_key %s is a node of this session that is still open — a premise is a registry "+
			"entry (its own key or registered name) or a PROVED section of the session, cited by its statement "+
			"(with_lemmas:[{\"text\":\"…\"}])", key)
	}
	statement, ok := s.Spelling().Typed(node.Goal)
	if !ok {
		statement = s.Spelling().Prop(node.Goal)
	}
	return fmt.Errorf("lemma_key %s is a node of this session, not a registry entry. A proved section is cited "+
		"by its STATEMENT, as a text premise: with_lemmas:[{\"text\":%q}] — add term_specialize as for any "+
		"premise. Its claim certifies against the section, and emit renders the cite as At(<section>, w…); "+
		"cite_node is not needed. A section stated over a structure binder is read at an instance by its id: "+
		"{\"key\":%q,\"read_at\":…}", key, statement, key)
}

// sessionNodeID is the shape of a session node id: section index, then
// an open (`g`) or closed (`c`) goal's short key.
var sessionNodeID = regexp.MustCompile(`^s(\d+)_[gc]`)

// lemmaKeyMiss builds the diagnostic for a lemma key slot the registry
// does not resolve.
func (e *Engine) lemmaKeyMiss(keyOrName string) error {
	msg := fmt.Sprintf("lemma_key %s names no proof-registry entry: not an entry's own key (prop_…) "+
		"and not a registered name.", keyOrName)
	if hint := e.lemmaNameMissHint(keyOrName); hint != "" {
		msg += " " + hint
	} else {
		msg += " (A member landed after this serve was built also misses — rebuild and restart the serve.)"
	}
	return fmt.Errorf("%s", msg)
}

// lemmaNameMissHint checks the near-miss shape that is individually
// actionable: a bare entry name whose registered form carries the
// family prefix.
func (e *Engine) lemmaNameMissHint(keyOrName string) string {
	suffix := "." + keyOrName
	for _, entry := range registry.All() {
		if strings.HasSuffix(entry.Name, suffix) {
			return fmt.Sprintf("Did you mean the entry %q? The slot takes the FULL registered name.",
				entry.Name)
		}
	}
	return ""
}
