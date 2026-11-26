package proof

// member_evidence.go — a Member's evidence at the By that consumes it.
//
// A Member handed to At is a term to the instance, and a grounding takes
// nothing else: the evidence stays behind. Where the member's membership
// is one of the instance's guards, that evidence is what discharges it,
// and a By consuming the premise without it fails at its closer, far
// from the cite, with nothing pointing at the member. So each evidence
// carrier an At takes is recorded on the fact; a path that carries the
// evidence with the cite (WithMembers, Member.With, a closure law's
// ReadMember) drops the record; and the By reads what is left: a member
// whose membership is a guard of the instance has its evidence in the
// list — the member itself, a fact of its evidence, or a resident fact
// stating the membership — or the By is refused, naming the member.

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// memberWitness is an evidence carrier an At took as a witness.
type memberWitness struct {
	carrier _EvidenceCarrier
	point   core.Term
}

// withoutCarried is ws without the witnesses whose evidence travels with
// the cite.
func withoutCarried(ws []memberWitness, carried []_EvidenceCarrier) []memberWitness {
	if len(ws) == 0 {
		return ws
	}
	var out []memberWitness
	for _, w := range ws {
		kept := true
		for _, c := range carried {
			if c == w.carrier {
				kept = false
				break
			}
		}
		if kept {
			out = append(out, w)
		}
	}
	return out
}

// checkMemberEvidence refuses a By premise grounded at a member whose
// membership is a guard of the instance when the list does not hold the
// member's evidence. facts and premises are parallel; listedHandles are
// the resident handles the list names, listedCarriers the evidence
// carriers it names as themselves; read is the rung's reader in the
// proof the By is of.
func checkMemberEvidence(read rungReader, goal Prop, facts []Fact, premises []byPremise, described []string,
	listedHandles map[*HypHandle]bool, listedCarriers map[_EvidenceCarrier]bool) {
	for i, f := range facts {
		if len(f.members) == 0 || premises[i].install == nil {
			continue
		}
		pr := premises[i]
		stated := pr.install
		if !pr.resident && !pr.exact && ext.PropHasTypeVars(stated) {
			stated = typedForMembers(stated, pr.witnesses, goal)
		}
		guards := instanceGuards(stated.AsProp().Conclusion(), pr.witnesses)
		for _, m := range f.members {
			set := memberSet(m)
			guard := memberGuard(read, guards, m.point, set)
			if guard == nil || memberEvidenceListed(read, facts, i, m, guard, listedHandles, listedCarriers) {
				continue
			}
			panic(fmt.Sprintf("By: premise %s is grounded at the member %s, whose membership %s is a guard of the "+
				"instance, and the list does not hold the member's evidence — At takes the point and leaves the "+
				"evidence behind. List the member beside the premise (By(…, member, premise)), or carry it with "+
				"the premise: member.With(premise), WithMembers(premise, members…)",
				described[i], ext.PrintTerm(m.point), ext.PrintTerm(guard)))
		}
	}
}

// typedForMembers is the stated form at the types the tuple forces, or
// the stated form itself where the witnesses do not fix them: where the
// typing reports a failure (rungFailure, which raises a fault again).
func typedForMembers(stated Prop, witnesses []Term, goal Prop) (typed Prop) {
	defer func() {
		if rungFailure(recover()) != nil {
			typed = stated
		}
	}()
	return witnessTypedForm(stated, witnesses, goal)
}

// instanceGuards are the antecedents along the stated form's ∀/⇒
// telescope with the witnesses in place of the binders they ground, in
// stated order through the leading implications — the order At reads a
// tuple in. A witness whose type is not its binder's grounds nothing
// here, so no guard about it is read.
func instanceGuards(stated core.Term, witnesses []core.Term) []core.Term {
	var subs []core.TermSubst
	var guards []core.Term
	t, i := stated, 0
	for {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			if i < len(witnesses) {
				if abs.Var().Type().Equals(witnesses[i].Type()) {
					subs = append(subs, ext.MakeTermSubst(abs.Var(), witnesses[i]))
				}
				i++
			}
			t = abs.Body()
			continue
		}
		ante, rest, ok := ext.MatchesIMPLY(t)
		if !ok {
			break
		}
		guards = append(guards, ante)
		t = rest
	}
	for k := range guards {
		guards[k] = guards[k].Substitute(subs...)
	}
	return guards
}

// memberSet is the set the member's evidence says its point lies in, nil
// where no fact of the evidence states it (a closure law's member, whose
// evidence ends in the reading at its points).
func memberSet(m memberWitness) core.Term {
	for _, e := range m.carrier.evidencePremises() {
		f, ok := e.(Fact)
		if !ok {
			continue
		}
		content, bound := f.BoundContent()
		if !bound {
			continue
		}
		for _, c := range conjuncts(content) {
			if point, set, isMember := membershipSet(c); isMember && point.AlphaEquals(m.point) {
				return set
			}
		}
	}
	return nil
}

// memberGuard is the guard conjunct that is the member's membership: its
// point in its set, or, where the set is not known, its point in any —
// both read as the apply rung reads a guard (rungReader.same), so a
// carrier the reading spells η-expanded is the member's own.
func memberGuard(read rungReader, guards []core.Term, point, set core.Term) core.Term {
	for _, g := range guards {
		for _, c := range conjuncts(g) {
			p, s, ok := membershipSet(c)
			if ok && read.same(p, point) && (set == nil || read.same(s, set)) {
				return c
			}
		}
	}
	return nil
}

// memberEvidenceListed reports whether the list holds the member's
// evidence for guard: the member itself, a resident fact of its
// evidence, or a resident fact (or a conjunct of one) stating guard.
func memberEvidenceListed(read rungReader, facts []Fact, self int, m memberWitness, guard core.Term,
	listedHandles map[*HypHandle]bool, listedCarriers map[_EvidenceCarrier]bool) bool {
	if listedCarriers[m.carrier] {
		return true
	}
	for _, e := range m.carrier.evidencePremises() {
		if f, ok := e.(Fact); ok && f.handle != nil && listedHandles[f.handle] {
			return true
		}
	}
	for j, f := range facts {
		if j == self {
			continue
		}
		var content core.Term
		switch {
		case f.handle != nil && len(f.witnesses) == 0 && f.handle.term != nil:
			content = f.handle.content()
		case f.residentContent != nil && len(f.witnesses) == 0:
			content = contentHypTerm("By", f.residentContent)
		default:
			continue
		}
		for _, c := range conjuncts(content) {
			if read.same(c, guard) {
				return true
			}
		}
	}
	return false
}
