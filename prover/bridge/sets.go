package bridge

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/reify"
)

// The set lemmas membership is read through, as family.Member.
const (
	lemmaSetMemberDef        = "set_basic.SetMemberDef"
	lemmaSetComprehensionDef = "set_basic.SetComprehensionDef"
	lemmaComprehensionSpec   = "set_basic.ComprehensionSpecDef"
	lemmaMemberNotEmpty      = "set_basic.MemberNotEmpty"
)

// memberEq is ⊢ (x ∈ S) = P(x) for a set the reifier reads through: a
// set-builder {y | P(y)}, as the text parser lowers it, or a defined
// constant whose definition is one; nil for any other set.
func (b *_Builder) memberEq(x, S core.Term) *prop.PropWrapper {
	if eq := b.comprehensionMember(x, S); eq != nil {
		return eq
	}
	def := unfoldTheorem(S)
	if def == nil {
		return nil
	}
	_, body, _ := core.MatchesEQ(def.Conclusion())
	inner := b.memberEq(x, body)
	if inner == nil {
		return nil
	}
	member := b.call("set_member", x, S)
	return replace(member, def).EqTrans(inner)
}

// comprehensionMember is ⊢ (x ∈ {y | P(y)}) = P(x): membership is the
// set applied, the set-builder its predicate, the specification the
// conjunction of P(y) with x = y, and that holds of some y exactly when
// P(x) does.
func (b *_Builder) comprehensionMember(x, S core.Term) *prop.PropWrapper {
	head, args := ext.MatchesApply(S)
	c, ok := head.AsConst()
	if !ok || c.Name() != "set_comprehension" || len(args) != 1 {
		return nil
	}
	generator, ok := args[0].AsAbsTerm()
	if !ok {
		return nil
	}
	existential := ext.MatchesEXISTS(generator.Body())
	if existential.IsZero() {
		return nil
	}
	_, spec := ext.MatchesApply(existential.Body())
	if len(spec) != 3 || !spec[0].Equals(generator.Var()) || !spec[2].Equals(existential.Var()) {
		return nil
	}
	read := b.instance(lemmaSetMemberDef, x, S)
	applied := replace(rhsOf(read), b.instance(lemmaSetComprehensionDef, args[0]))
	reduced := prop.RewriteOrRefl(prop.BetaRewrite, rhsOf(applied))
	opened := rhsOf(reduced)
	inner := ext.MatchesEXISTS(opened)
	_, specArgs := ext.MatchesApply(inner.Body())
	specified := b.instance(lemmaComprehensionSpec, specArgs...)
	spelled := replace(opened, specified)
	// ∃y. P(y) ∧ x = y ⇔ P(x)
	conj := rhsOf(spelled)
	body := ext.MatchesEXISTS(conj)
	p, eq, _ := ext.MatchesAND(body.Body())
	px := p.Substitute(core.MakeTermSubst(body.Var(), x))
	given := assume(body.Body())
	equal := given.DeriveTrans(prop.HypAND1(p, eq))
	forward := replace(p, equal.EqSym()).EqMP(given.DeriveTrans(prop.HypAND0(p, eq)))
	forward = sameAt(forward, px).HypExists(body.Var(), body.Body())
	witness := conjoin(assume(px), prop.Refl(x))
	backward := witness.DeriveTrans(prop.InstExists(conj, x))
	onePoint := backward.Deduct(forward)
	return read.EqTrans(applied).EqTrans(reduced).EqTrans(spelled).EqTrans(onePoint)
}

// sameAt asserts t concludes the expected term.
func sameAt(t *prop.PropWrapper, expected core.Term) *prop.PropWrapper {
	sameConclusion(t, expected, "a set-builder's one-point reading")
	return t
}

func rhsOf(t *prop.PropWrapper) core.Term {
	_, r, ok := core.MatchesEQ(t.Conclusion())
	if !ok {
		panic(fmt.Sprintf("bridge: %s is not an equation", prop.PrintProp(t)))
	}
	return r
}

// membership proves a membership node: x ∈ S is the set's predicate at
// x, which the child reads.
func (b *_Builder) membership(n *reify.Node, c *_Context) *prop.PropWrapper {
	_, args := ext.MatchesApply(n.Source)
	eq := b.memberEq(args[0], args[1])
	if eq == nil {
		panic(fmt.Sprintf("bridge: no reading of the membership %s", ext.PrintTerm(n.Source)))
	}
	return eq.EqTrans(b.node(n.Children[0], c, nil))
}

// nonempty proves ¬(S = ∅) by the child ∃x. x ∈ S (set_basic.MemberNotEmpty).
func (b *_Builder) nonempty(n *reify.Node, c *_Context) *prop.PropWrapper {
	S := setOfNonempty(n.Source)
	law := b.instance(lemmaMemberNotEmpty, S)
	return law.EqSym().EqTrans(b.node(n.Children[0], c, nil))
}

// emptiness proves S = ∅ as the negation of the child ¬(S = ∅):
// S = ∅ is ¬¬(S = ∅), the negation of what the child reads.
func (b *_Builder) emptiness(n *reify.Node, c *_Context) *prop.PropWrapper {
	inner := b.node(n.Children[0], c, nil)
	_, args := ext.MatchesApply(n.Term)
	negated := unary(ext.Not(n.Children[0].Source).Core(), inner)
	sem := b.evalClause(1, c.sigma, args[0])
	return prop.DoubleNeg(n.Source).EqSym().EqTrans(negated).EqTrans(sem.EqSym())
}

// setOfNonempty reads S off ¬(S = ∅).
func setOfNonempty(t core.Term) core.Term {
	inner := ext.MatchesNOT(t)
	l, _, ok := core.MatchesEQ(inner)
	if !ok {
		panic(fmt.Sprintf("bridge: %s is not a nonemptiness", ext.PrintTerm(t)))
	}
	return l
}
