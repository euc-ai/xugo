// emit_hypothesis_verbs.go — the Argument verbs that read ONE resident
// fact, rendered from the ministeps they record:
//
//   - a.Unfolded(fact, <c's definition>): an assert whose claim child is one
//     def_expand of c that closes it, the claim what a hypothesis of the
//     assert's goal states once c is opened in it (derive.go Unfolded;
//     the session's `def_expand {const, hyp_index}`);
//   - a.Conjuncts(fact, labels…): a run of asserts down the continuation
//     spine, one per flat conjunct of a resident conjunction in its
//     order — of a membership in a set-builder, its reading's
//     (proof.FactConjuncts) — each claim child a `By(Normalized, fact)`
//     leaf whose one premise is that fact (derive.go Conjuncts; the
//     session's `split_conj {hyp_index}`).
//
// Both records are asserts, so the Derive block reads them as its Haves
// (collectAssertStaircase, haveHandleIdents) and renders them as the
// verbs (renderDeriveStatements → renderFactVerb). The fact a verb reads
// is the Go value of the statement that introduced it in the block, a
// Given branch's or a Law door's handle, or the machine spelling
// `ResidentHyp(<statement>)`.

package emit

import (
	"fmt"
	"strings"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// _UnfoldedFact is what an a.Unfolded record opened: the hypothesis, by
// index in the assert's goal, and the constant's name.
type _UnfoldedFact struct {
	hypIndex  int
	constName string
}

// _ConjunctsRun is an a.Conjuncts record: its asserts in the
// conjunction's order, the conjunction by index in the first assert's
// goal, and the premise of the first claim's By, which names it.
type _ConjunctsRun struct {
	steps    []*proof.StepProto
	hypIndex int
	premise  *proof.ByPremiseProto
	parts    []core.Prop
}

// planHypothesisVerbs finds, in every section, the records of
// a.Unfolded (unfoldedAt) and a.Conjuncts (conjunctsRunAt) before the
// symbol passes run: neither prints the claims it asserts. Rendering
// only: the steps are untouched.
func (e *_Emitter) planHypothesisVerbs() {
	e.unfolded = map[*proof.StepProto]_UnfoldedFact{}
	e.conjuncts = map[*proof.StepProto]*_ConjunctsRun{}
	for _, s := range e.sections {
		e.reader = s.reader
		var visit func(n *msNode)
		visit = func(n *msNode) {
			if n == nil {
				return
			}
			if _, inRun := e.conjuncts[n.step]; !inRun {
				if run := e.conjunctsRunAt(n); run != nil {
					for _, step := range run.steps {
						e.conjuncts[step] = run
					}
				}
			}
			if u, ok := e.unfoldedAt(n); ok {
				e.unfolded[n.step] = u
			}
			for _, c := range n.children {
				visit(c)
			}
		}
		visit(e.foldFinallyTails(buildMSTree(s.detailedSteps)))
	}
}

// statementAssert reports whether n is an assert a Derive block reads
// as a statement of its own: two children, no Finally fold, neither a
// cite of an earlier section nor an obligation of an induction by a
// cited principle (collectAssertStaircase's guards).
func (e *_Emitter) statementAssert(n *msNode) (core.Prop, bool) {
	assert, isAssert := n.step.Step.(*proof.StepProto_Assert)
	if !isAssert || len(n.children) != 2 || n.finallyFold > 0 {
		return nil, false
	}
	if _, cited := e.sectionCites[n.step]; cited || e.byInductions[n.step] != nil || e.byInductionAsserts[n.step] {
		return nil, false
	}
	claim, _ := e.reader.Prop(assert.Assert)
	return claim, claim != nil
}

// unfoldedAt reads the record a.Unfolded makes off n: an assert whose
// claim child is one `def_expand` that closes it, the claim being what
// a hypothesis of the assert's goal states once that constant is opened
// in it (proof.UnfoldedHypothesis). That hypothesis is the fact; the
// first that fits is taken. An assert whose ∃ claim its continuation
// opens at once is an Obtain (obtainStrip), and stays one.
func (e *_Emitter) unfoldedAt(n *msNode) (_UnfoldedFact, bool) {
	claim, ok := e.statementAssert(n)
	if !ok || e.obtainStrip(n) != nil {
		return _UnfoldedFact{}, false
	}
	claimNode := n.children[0]
	unfold, isUnfold := claimNode.step.Step.(*proof.StepProto_DefExpand)
	if !isUnfold || len(claimNode.children) != 0 || claimNode.finallyFold > 0 {
		return _UnfoldedFact{}, false
	}
	ct := e.constAt(unfold.DefExpand)
	goal, _ := e.reader.Prop(n.step.Goal)
	if ct.IsZero() || goal == nil {
		return _UnfoldedFact{}, false
	}
	for i := range goal.NumHyps() {
		hyp := goal.Hyp(i)
		if !prop.ContainsConstName(core.MakeProp(hyp), ct.Name()) {
			continue
		}
		if opened, err := proof.UnfoldedHypothesis(hyp, ct, nil); err == nil && opened.AlphaEquals(claim.Conclusion()) {
			return _UnfoldedFact{hypIndex: i, constName: string(ct.Name())}, true
		}
	}
	return _UnfoldedFact{}, false
}

// conjunctsRunAt reads the record a.Conjuncts makes, starting at n: one
// conjunctAssert per flat conjunct of the conjunction n's claim is
// closed from, in the conjunction's order, each the continuation of the
// last. nil for anything else, and for a run whose last conjunct its
// continuation opens at once (an Obtain).
func (e *_Emitter) conjunctsRunAt(n *msNode) *_ConjunctsRun {
	conjunction, idx, premise, ok := e.conjunctAssert(n)
	if !ok {
		return nil
	}
	parts := proof.FactConjuncts(conjunction)
	if len(parts) < 2 {
		return nil
	}
	run := &_ConjunctsRun{hypIndex: idx, premise: premise}
	cur := n
	for k, part := range parts {
		if k > 0 {
			cur = cur.children[1]
		}
		from, _, _, ok := e.conjunctAssert(cur)
		claim, _ := e.statementAssert(cur)
		if !ok || !from.AlphaEquals(conjunction) || !claim.Conclusion().AlphaEquals(part) {
			return nil
		}
		run.steps = append(run.steps, cur.step)
		run.parts = append(run.parts, claim)
	}
	if e.obtainStrip(cur) != nil {
		return nil
	}
	return run
}

// conjunctAssert reports whether n is one assert of an a.Conjuncts
// record: a statementAssert whose claim child is a `By(Normalized, f)`
// leaf with the one premise f, a resident hypothesis of n's goal,
// ungrounded and unscaled. It returns that hypothesis, its index in n's
// goal, and the premise.
func (e *_Emitter) conjunctAssert(n *msNode) (core.Term, int, *proof.ByPremiseProto, bool) {
	if _, ok := e.statementAssert(n); !ok {
		return nil, 0, nil, false
	}
	claimNode := n.children[0]
	by, isBy := claimNode.step.Step.(*proof.StepProto_By)
	if !isBy || by.By == nil || len(claimNode.children) != 0 || claimNode.finallyFold > 0 {
		return nil, 0, nil, false
	}
	b := by.By
	if b.GetArith() || b.GetSettac() || b.GetChase() || b.GetBroadcast() ||
		b.GetShape() == nil || !proto.Equal(b.GetShape(), &proof.ByShapeProto{}) || len(b.GetPremises()) != 1 {
		return nil, 0, nil, false
	}
	p := b.GetPremises()[0]
	if !namesResidentHypothesis(p) || len(p.GetWitnesses()) > 0 || len(p.GetNamed()) > 0 || p.GetScaled() {
		return nil, 0, nil, false
	}
	install, _ := e.reader.Prop(p.GetInstall())
	goal, _ := e.reader.Prop(n.step.Goal)
	if install == nil || goal == nil {
		return nil, 0, nil, false
	}
	for i := range goal.NumHyps() {
		if goal.Hyp(i).AlphaEquals(install.Conclusion()) {
			return goal.Hyp(i), i, p, true
		}
	}
	return nil, 0, nil, false
}

// factVerbAssert reports whether step is an assert a verb's rendering
// prints no claim of: an a.Unfolded's, or one of an a.Conjuncts run.
func (e *_Emitter) factVerbAssert(step *proof.StepProto) bool {
	_, unfolded := e.unfolded[step]
	return unfolded || e.conjuncts[step] != nil
}

// walkUnfoldedFact registers the vocabulary of the fact an a.Unfolded
// opens, which factExpr prints where no Go value names it.
func (e *_Emitter) walkUnfoldedFact(step *proof.StepProto) {
	u, ok := e.unfolded[step]
	if !ok {
		return
	}
	goal, _ := e.reader.Prop(step.Goal)
	e.walkProp(core.MakeProp(goal.Hyp(u.hypIndex)))
}

// loneUnfolded is a Derive block of one statement for an a.Unfolded
// no other assert follows: the verb has no AssertStep spelling a chapter
// writes, so a run holding one is a block however short.
func (e *_Emitter) loneUnfolded(n *msNode) ([]*msNode, *msNode, bool) {
	if _, ok := e.unfolded[n.step]; !ok || len(n.children) != 2 || n.finallyFold > 0 {
		return nil, nil, false
	}
	return []*msNode{n}, n.children[1], true
}

// hypAddressedByStep is hypAddressedBy with the verbs' records: an
// a.Unfolded addresses the hypothesis it opens, an a.Conjuncts run's
// first assert the conjunction it splits.
func (e *_Emitter) hypAddressedByStep(step *proof.StepProto) (int, bool) {
	if u, ok := e.unfolded[step]; ok {
		return u.hypIndex, true
	}
	if run := e.conjuncts[step]; run != nil && run.steps[0] == step {
		return run.hypIndex, true
	}
	return hypAddressedBy(step)
}

// factVerbHandles completes, for a Derive block holding the verbs, the
// Go values haveHandleIdents bound. The fact a verb reads is a value of
// the block where an earlier statement introduced it: that statement is
// bound (an ident allocated where nothing else used it), and the verb's
// own step is recorded as its use. An a.Conjuncts run's facts are one
// value, the slice the verb returns: the run's first statement is bound
// to `partsN`, and every use of a conjunct names `partsN[k]`.
func (e *_Emitter) factVerbHandles(chain []*msNode, handles []string) {
	fresh := func(base string) string {
		taken := e.declSet()
		for _, id := range e.hypHandleByUse {
			taken[id] = true
		}
		for _, id := range handles {
			taken[id] = true
		}
		e.factHandleCount++
		return e.freshIdent(fmt.Sprintf("%s%d", base, e.factHandleCount), taken)
	}
	for j, node := range chain {
		idx, reads := e.hypAddressedByStep(node.step)
		if !reads || !e.factVerbAssert(node.step) {
			continue
		}
		use := _HypUse{step: node.step}
		if _, named := e.hypHandleByUse[use]; named {
			continue
		}
		goal, _ := e.reader.Prop(node.step.Goal)
		fact := goal.Hyp(idx)
		for i := j - 1; i >= 0; i-- {
			if claim := e.statementClaim(chain[i]); claim == nil || !claim.Conclusion().AlphaEquals(fact) {
				continue
			}
			if handles[i] == "" {
				handles[i] = fresh("fact")
			}
			if e.hypHandleByUse == nil {
				e.hypHandleByUse = map[_HypUse]string{}
			}
			e.hypHandleByUse[use] = handles[i]
			break
		}
	}
	for h := 0; h < len(chain); h++ {
		run := e.conjuncts[chain[h].step]
		if run == nil || run.steps[0] != chain[h].step {
			continue
		}
		bound := false
		for k := range run.steps {
			bound = bound || handles[h+k] != ""
		}
		if !bound {
			continue
		}
		parts := fresh("parts")
		for k := range run.steps {
			if id := handles[h+k]; id != "" {
				for use, named := range e.hypHandleByUse {
					if named == id {
						e.hypHandleByUse[use] = fmt.Sprintf("%s[%d]", parts, k)
					}
				}
			}
			handles[h+k] = ""
		}
		handles[h] = parts
		h += len(run.steps) - 1
	}
}

// statementClaim is the fact a Derive block's statement leaves resident:
// an Obtain's instance, every other statement's claim.
func (e *_Emitter) statementClaim(n *msNode) core.Prop {
	if strip := e.obtained[n.step]; strip != nil {
		return e.obtainedInstance(strip)
	}
	claim, _ := e.reader.Prop(n.step.Step.(*proof.StepProto_Assert).Assert)
	return claim
}

// renderFactVerb renders a Derive-block statement that is a verb's
// record and reports whether node was one:
//
//	fact2 := b.Unfolded(fact1, CDef)
//	parts3 := b.Conjuncts(h, "<conjunct>", …)
//
// handle is the ident the block bound the statement to, "" for a fact
// nothing later addresses. A Conjuncts run renders at its first assert,
// and its other asserts render nothing. The labels are the conjuncts'
// goal texts — placeholders, as a Have's label is: naming a fact for
// what it means is the author's.
func (e *_Emitter) renderFactVerb(b *strings.Builder, chain []*msNode, node *msNode, handle, recv, inner string) bool {
	bind := ""
	if handle != "" {
		bind = handle + " := "
	}
	if run := e.conjuncts[node.step]; run != nil {
		if run.steps[0] != node.step {
			return true
		}
		at := -1
		for i, n := range chain {
			if n == node {
				at = i
			}
		}
		for k, step := range run.steps {
			if at+k >= len(chain) || chain[at+k].step != step {
				panic(fmt.Sprintf("emit: an a.Conjuncts record split across Derive statements (conjunct %d of %d)", k+1, len(run.steps)))
			}
		}
		labels := make([]string, len(run.parts))
		for k, part := range run.parts {
			labels[k] = fmt.Sprintf("%q", e.goalComment(part))
		}
		fmt.Fprintf(b, "%s%s%s.Conjuncts(%s, %s)\n", inner, bind, recv,
			e.factExpr(node, run.hypIndex, run.premise), strings.Join(labels, ", "))
		return true
	}
	if u, ok := e.unfolded[node.step]; ok {
		fmt.Fprintf(b, "%s%s%s.Unfolded(%s, %s)\n", inner, bind, recv, e.factExpr(node, u.hypIndex, nil), e.definitionExpr(u.constName))
		return true
	}
	return false
}

// factExpr is the Go value of the hypothesis at idx of n's goal, for a
// verb that reads it: the value its use was bound to — the statement of
// the block that introduced it (factVerbHandles), a Given branch's
// handle (renderGivenBranch), or, for a Conjuncts, the Have the
// premise of its first By names (haveHandleIdents) — then a Law door's
// handle, else the machine spelling `ResidentHyp(<statement>)`, whose
// identifiers are marked used here as a resident premise's are.
func (e *_Emitter) factExpr(n *msNode, idx int, premise *proof.ByPremiseProto) string {
	if id, ok := e.hypHandleByUse[_HypUse{step: n.step}]; ok {
		return id
	}
	if premise != nil {
		if id, ok := e.hypHandleByUse[_HypUse{premise: premise}]; ok {
			return id
		}
	}
	goal, _ := e.reader.Prop(n.step.Goal)
	hyp := core.MakeProp(goal.Hyp(idx))
	if handle := e.lawHandleFor(hyp); handle != "" {
		return handle
	}
	return e.residentHypExpr(hyp)
}
