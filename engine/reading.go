// reading.go — a structure law read at an instance, as a session
// premise: `{"key": law, "read_at": …}` on a `by` premise or a
// `simp_with` rule, the Go `law.Read(instance)` (prover/proof/reading.go).
//
// A structure's law is a Horn theorem `∀comps. S(comps) ⇒ body`. Read
// at an instance `S(c)` it is `body[comps := c]`: the components pinned
// to the instance's, the structure hypothesis discharged. The law is a
// registry entry by its key, or a PROVED section of the session by its
// root's id — a section stated over the structure binder, the Go
// `Read(<section>, instance)`. The instance is one of three things, as
// in Go:
//
//   - an instance ENTRY, `{"key": "real_ring.CommRing"}` — the reading
//     is a closed theorem;
//   - a RESIDENT hypothesis of the focused goal, `{"hyp_index": i}` —
//     the structure fact a chapter stated over the structure holds; the
//     reading is the sequent `S(c) ⊢ body[comps := c]`, used where that
//     hypothesis is resident;
//   - a READING, `{"key": projection law, "read_at": …}` — a projection
//     law read at an instance states the sub-structure at its
//     components, and the outer law is read at that.
//
// The kernel derives the reading from the two theorems
// (proof.ReadLawAt): nothing about it is taken on trust, it reaches no
// refuter, and the premise or rule it becomes is the one the Go
// spelling becomes, executed by the same code.

package engine

import (
	"fmt"
	"slices"
	"strconv"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	extprop "github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
)

// ReadAtSpec names the instance a law is read at. Exactly one form:
// `key` alone (an instance entry), `hyp_index` alone (a resident
// hypothesis of the focused goal), or `key` with `read_at` (the law
// `key` read at that instance — a reading as the instance).
type ReadAtSpec struct {
	Key      string      `json:"key,omitempty"`
	HypIndex *int        `json:"hyp_index,omitempty"`
	ReadAt   *ReadAtSpec `json:"read_at,omitempty"`
}

// sessionReading is a law read at an instance, resolved at a goal.
type sessionReading struct {
	// theorem is the kernel-derived reading: `⊢ body[comps := c]` at an
	// entry, `S(c) ⊢ body[comps := c]` under a resident hypothesis.
	theorem core.Prop
	// instance is the immediate structure theorem read by this law.
	// For a nested reading it is the inner theorem, under its own hypotheses.
	instance core.Prop
	inner    *sessionReading
	// record is what it was read from, for the wire.
	record *proof.ReadingRecord
	// law is the law's own theorem and lawKey the spelling that cited
	// it: what a reading with a loose type letter is expanded to.
	law    core.Prop
	lawKey string
	// section is set when the law is a proved section of the session,
	// named by its root's id: its theorem certifies what the law's
	// install leaves, as no entry does.
	section bool
	// describe names the reading in diagnostics, in the author's
	// spelling.
	describe string
}

// lawSource is what certifies the claim the law's own install leaves
// when the reading is cited as the law beside its hypothesis (a loose
// type letter): an entry by its key and statement, a section by its
// theorem.
func (r *sessionReading) lawSource(statement core.Prop) *byInstallSource {
	if r.section {
		return &byInstallSource{prop: r.law}
	}
	return &byInstallSource{key: core.PropKey(r.lawKey), prop: statement}
}

// hypothesis is the resident hypothesis the reading is taken under,
// nil for a reading at an entry.
func (r *sessionReading) hypothesis() core.Term { return r.record.Hypothesis() }

// statement is what the reading states, without the hypothesis it may
// be under: the form whose binders a term_specialize table names.
func (r *sessionReading) statement() core.Prop { return core.MakeProp(r.theorem.Conclusion()) }

// renamedBinders maps each binder of the law that the reading holds
// under another name to that name. The reading is the law's body at the
// instance's components, so its binders are the law's without the ones
// the instance fixes, in the law's order (proof.ReadingLawBinders); the
// kernel renames one apart where the instance spells a free variable of
// its name — a record over a term the session has since named by a
// `let` — and the name it picks is not derived from the binder's (N
// becomes Kʹ). The law's own name is the one its statement and `query
// member` show, so a term_specialize table may spell either
// (byPremiseTable). A pairing is offered only where every binder that
// differs is the kernel's rename of its law binder; otherwise the
// reading is addressed by the names it holds, and nothing is mapped.
func (r *sessionReading) renamedBinders() map[string]string {
	kept, err := proof.ReadingLawBinders(r.law, r.instance.Conclusion())
	if err != nil {
		panic(fmt.Sprintf("%s was derived from a law that does not read at its instance: %v", r.describe, err))
	}
	held := guardedForAllBinderOrder(r.statement())
	if len(kept) != len(held) {
		return nil
	}
	var renamed map[string]string
	for i, name := range held {
		lawName := string(kept[i].Name())
		if lawName == name {
			continue
		}
		if !renamedApart(lawName, name) || slices.Contains(held, lawName) {
			return nil
		}
		if renamed == nil {
			renamed = map[string]string{}
		}
		renamed[lawName] = name
	}
	return renamed
}

// renamedApart reports whether to is a name the kernel's rename reaches
// from from (core.VarTerm.RenameToAvoid steps by utils.NextName until
// no name of the terms it avoids is met).
func renamedApart(from, to string) bool {
	const steps = 64
	for range steps {
		if from = utils.NextName(from); from == to {
			return true
		}
	}
	return false
}

// citedTheorem is the certificate a key cite stands for, with the name
// the entry is registered under: a registry entry's statement as its
// replay promise (serve.EntryThm — what the harness serves under the
// name), or a card this session minted, as its axiom. An entry the
// session's family cannot cite is refused (Session.citeRefusal).
func (s *Session) citedTheorem(keyOrName string) (core.Prop, string, bool, error) {
	if entry, ok := registryEntry(keyOrName); ok {
		if err := s.citeRefusal(entry); err != nil {
			return nil, "", true, err
		}
		return serve.EntryThm(s.env, entry), entry.Name, true, nil
	}
	if card := s.cardFor(keyOrName); card != nil {
		return card.axiom, card.entry, true, nil
	}
	return nil, "", false, nil
}

// resolveReading derives the law `lawKey` read at the instance `at`
// names, at the focused goal.
func (e *Engine) resolveReading(s *Session, goal core.Prop, lawKey string, at *ReadAtSpec) (*sessionReading, error) {
	if lawKey == "" {
		return nil, fmt.Errorf("read_at reads a LAW at an instance, and the law is a registry entry or a proved section " +
			"of this session: give the entry's key or the section's id")
	}
	law, lawName, ok, err := s.citedTheorem(lawKey)
	if err != nil {
		return nil, err
	}
	section := false
	if !ok {
		var named bool
		law, lawName, named, err = s.sectionLaw(lawKey)
		if err != nil {
			return nil, err
		}
		if !named {
			return nil, e.lemmaKeyMiss(lawKey)
		}
		section = true
	}
	if law.NumHyps() != 0 {
		return nil, fmt.Errorf("%s states an open sequent; a reading needs a closed law `∀comps. S(comps) ⇒ body`", lawName)
	}
	record := &proof.ReadingRecord{Law: core.MakeProp(law.Conclusion())}
	var instance core.Prop
	var innerReading *sessionReading
	var where string
	switch {
	case at == nil:
		return nil, fmt.Errorf("read_at is missing")
	case at.HypIndex != nil:
		if at.Key != "" || at.ReadAt != nil {
			return nil, fmt.Errorf("read_at names ONE instance: an entry {\"key\":…}, a resident hypothesis " +
				"{\"hyp_index\":…}, or a reading {\"key\":…,\"read_at\":…}")
		}
		idx := *at.HypIndex
		if idx < 0 || idx >= goal.NumHyps() {
			return nil, fmt.Errorf("read_at.hyp_index %d out of range [0, %d)", idx, goal.NumHyps())
		}
		hyp := goal.Hyp(idx)
		instance = core.Assume(hyp)
		record.Under = hyp
		where = fmt.Sprintf("hyp %d", idx)
	case at.Key == "":
		return nil, fmt.Errorf("read_at names an instance: an entry {\"key\":…}, a resident hypothesis " +
			"{\"hyp_index\":…}, or a reading {\"key\":…,\"read_at\":…}")
	case at.ReadAt != nil:
		inner, err := e.resolveReading(s, goal, at.Key, at.ReadAt)
		if err != nil {
			return nil, err
		}
		instance = inner.theorem
		innerReading = inner
		record.Inner = inner.record
		where = "(" + inner.describe + ")"
	default:
		entry, name, ok, err := s.citedTheorem(at.Key)
		if err != nil {
			return nil, err
		}
		if !ok {
			return nil, e.lemmaKeyMiss(at.Key)
		}
		if entry.NumHyps() != 0 {
			return nil, fmt.Errorf("the instance %s states an open sequent; an instance entry states `S(c)` outright", name)
		}
		instance = entry
		record.Instance = core.MakeProp(entry.Conclusion())
		where = name
	}
	theorem, err := proof.ReadLawAt(law, instance)
	if err != nil {
		return nil, fmt.Errorf("%s read at %s: %v\n  the law:      %s\n  the instance: %s",
			lawName, where, err, ext.PrintTerm(law.Conclusion()), ext.PrintTerm(instance.Conclusion()))
	}
	return &sessionReading{
		theorem:  theorem,
		instance: instance,
		inner:    innerReading,
		record:   record,
		law:      law,
		lawKey:   lawKey,
		section:  section,
		describe: lawName + " read at " + where,
	}, nil
}

// sectionLaw resolves a read_at law key that names a section of the
// session by its root's id — the id add-goal returned (`s<k>_g…`) or
// the one inspect prints once the section is closed (`s<k>_c…`) — to
// the section's theorem, the law a Go `Read(<section>, …)` reads.
// named is false when the key is no section of the session; an open
// section, or a node inside one, is refused by name.
func (s *Session) sectionLaw(key string) (law core.Prop, name string, named bool, err error) {
	m := sessionNodeID.FindStringSubmatch(key)
	if m == nil {
		return nil, "", false, nil
	}
	k, aerr := strconv.Atoi(m[1])
	if aerr != nil || k < 0 || k >= len(s.sections) || s.sections[k].root == nil {
		return nil, "", false, nil
	}
	root := s.sections[k].root
	closedID, openID := closedNodeID(k, root.Goal), fmt.Sprintf("s%d_g%s", k, shortKey(root.Goal))
	if key != closedID && key != openID {
		return nil, "", true, fmt.Errorf("read_at: %s is a node inside section %d, not the section — a law is read "+
			"from a proved section, named by its root's id (%s)", key, k, closedID)
	}
	if !root.Proved() {
		return nil, "", true, fmt.Errorf("read_at: section %d (%s) is still open — a section is read as a law once it is proved", k, key)
	}
	// The theorem in the statement's spelling: its bound names are the
	// ones a term_specialize table names, not those the proof left.
	law = extprop.WeakenTo(root.PromisedThm(), root.Goal)
	if law == nil {
		panic(fmt.Sprintf("read_at: section %d's theorem does not state its goal (engine invariant)", k))
	}
	return law, fmt.Sprintf("section %d", k), true, nil
}

// closeOnCertificates closes the open leaves of roots that one of certs
// proves — the claim children a reading leaves behind, which no entry
// states: a leaf the certificate is stronger than (the reading itself,
// or the reading under its hypothesis at a leaf holding it), a leaf
// the certificate's telescope at the leaf's ∀-prefix is stronger than
// (a reading grounded at fewer witnesses than it has binders), a leaf
// that is the certificate's normal form (a bare premise installs in the
// closer's clause form), and a leaf that is a type instance of it (a
// reading with a loose type letter, adapted to the goal). The
// certificates sit in a scratch cache: a reading is derived, not
// registered, and must not enter the session's dep-bounded pool.
func (s *Session) closeOnCertificates(roots []*proof.GoalStackNode, certs []core.Prop) []AutoMatchedGoal {
	if len(certs) == 0 {
		return nil
	}
	cache := &proof.ThmCache{}
	for _, cert := range certs {
		if cert.NumHyps() == 0 {
			normalized, _ := proof.Normalize(cert)
			cache.SaveThm(cert, normalized)
		}
	}
	for _, root := range roots {
		for _, leaf := range root.UnsolvedLeaves() {
			closed := false
			prefix, _ := ext.DecomposesFORALL(leaf.Goal.Conclusion())
			for _, cert := range certs {
				if proof.ApplyCiteKnown(leaf, cert) {
					closed = true
					break
				}
				// A premise grounded at a tuple shorter than its binders
				// is installed as its telescope at the tuple's prefix
				// (extprop.PrefixTelescope), so its claim is that telescope
				// of the certificate; the leaf's own ∀-prefix is the
				// telescope's length, and the telescope a theorem derived
				// from the certificate.
				telescope := extprop.PrefixTelescope(cert, prefix.Size())
				if !telescope.Conclusion().AlphaEquals(cert.Conclusion()) && proof.ApplyCiteKnown(leaf, telescope) {
					closed = true
					break
				}
			}
			if !closed {
				proof.ApplyKnown(leaf, cache)
			}
		}
	}
	// What is left can only be a type instance, and only of a reading
	// that still has a type variable to instantiate.
	var matched []AutoMatchedGoal
	for _, cert := range certs {
		if cert.NumHyps() == 0 && ext.PropHasTypeVars(cert) {
			matched = append(matched, s.applyAutoMatchTypeInstanceOnRoots(roots, "", cert, nil, cache)...)
		}
	}
	return matched
}
