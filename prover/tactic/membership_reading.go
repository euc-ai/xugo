// membership_reading.go — the reading of a membership in a set-builder
// as its condition at the point: `x ∈ {p | φ}` is φ[x/p], and in the
// three-part form `x ∈ {t | x̄ | φ}` is `∃x̄. φ ∧ x = t`. It is the
// spelling the set driver's unfolding reaches (set_member,
// set_comprehension and comprehension_spec unfolded by their
// definitions, β, and for the identity form the one-point rule of
// set_tac_fuse.go on the point's equation), taken as ONE normalization
// a reader applies on both sides of an identity, with the kernel bridge
// that carries a statement across it. The apply rung's identity
// (prover/proof, apply_close.go) is βη and this reading: a guard
// `u ∈ {p | polynomial_over(c, p)}` is
// supplied by a resident `polynomial_over(c, u)`, a guard `x ∈ {i | i ≤
// n}` by a resident `x ≤ n`, a goal `P(a)` closes on a resident `a ∈ {p
// | P(p)}`, and a goal `∃s m. (s ∈ S ∧ m ∈ M) ∧ x = s * m` closes on a
// resident `x ∈ {s * m | s, m | s ∈ S ∧ m ∈ M}`.
//
// What is read is a set-builder — `set_comprehension(λv. ∃x̄.
// comprehension_spec(v, φ, t))`, the identity form where x̄ is one
// binder and t that binder, the point itself the member — whose three
// constants carry their definitions (the registry's metas; a surface
// constant without one is not read, and the pure reading and the bridge
// decline together). The three-part reading stops at the ∃: a witness
// is the author's, as it is everywhere on the rung. A membership in a
// constant declared to read its membership (membership_declared.go),
// `x ∈ ⟦a, b⟧` for `real_closed_interval(a, b) = {x | a ≤ x ∧ x ≤ b}`,
// is read as the set-builder its definiens is at the arguments: the
// bridge opens the constant by its definition first.
//
// Two faces of one function. MembershipNormal is the pure reading, a
// term's membership normal form, read innermost first on the
// β-collapsed term without the kernel — what a comparison costs.
// MembershipBridge is the kernel's `⊢ t = MembershipNormal(t)`,
// composed from the definitions, β and the fusion, built once where a
// close commits. The two agree up to βη by construction — the rewrite
// `x ∈ {p | φ} → φ[x/p]` has no overlapping instances, so every order
// reaches one normal form — and the bridge checks that it does: a
// disagreement is an engine invariant broken, and panics.
//
// The hypothesis-side moves read one membership, at a hypothesis's top,
// the same way: MembershipAtomReading is that atom's pure reading,
// ReadAsShape the statement a move opens of a hypothesis, and
// throughMembershipAt runs the index-targeted splits of an ∨, ∃, ⇔ or
// ⇒ on it through the atom's bridge (a conjunction's parts are closed
// by the By closer's own reading, prover/proof Conjuncts).

package tactic

import (
	"context"
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// The three constants a set-builder membership is spelled with, by the
// names the set_basic chapter mints them under.
const (
	setMemberName         core.TermName = "set_member"
	setComprehensionName  core.TermName = "set_comprehension"
	comprehensionSpecName core.TermName = "comprehension_spec"
)

// comprehensionMembership is an atom `x ∈ {t | x̄ | φ}` taken apart: the
// three constants at the occurrence's types, each carrying its
// definition, the point, the set-builder, its predicate
// `λv. ∃x̄. comprehension_spec(v, φ, t)` and the condition φ. In the
// identity form bound is the one binder, which is the output; in the
// three-part form binders are x̄ and out is t. An atom `x ∈ c(ā)` at a
// declared constant (membership_declared.go) is read through its
// definiens: opened is set, declared and args are the constant and its
// arguments as written, and set is the set-builder c names at them.
type comprehensionMembership struct {
	member, comprehension, spec core.ConstTerm
	point, set                  core.Term
	pred                        core.AbsTerm
	bound                       core.VarTerm
	body                        core.Term
	general                     bool
	binders                     []core.VarTerm
	out                         core.Term
	opened                      bool
	declared                    core.ConstTerm
	args                        []core.Term
}

// matchComprehensionMembership reads t as a membership in a set-builder
// whose three constants carry their definitions, or in a declared
// constant applied at its arity, whose definiens is one
// (openDeclaredSet).
func matchComprehensionMembership(t core.Term) (comprehensionMembership, bool) {
	head, args := ext.MatchesApply(t)
	c, ok := head.AsConst()
	if !ok || c.Name() != setMemberName || len(args) != 2 || c.DefThm().IsZero() {
		return comprehensionMembership{}, false
	}
	declared, declaredArgs, opened, isDeclared := openDeclaredSet(args[1])
	set := args[1]
	if isDeclared {
		set = opened
	}
	m, ok := matchSetBuilder(set)
	if !ok {
		if isDeclared {
			panic(fmt.Sprintf("matchComprehensionMembership: %s, declared to read its membership, opens to no set-builder: %s (engine invariant)",
				declared.Name(), ext.PrintTerm(opened)))
		}
		return m, false
	}
	m.member, m.point = c, args[0]
	m.opened, m.declared, m.args = isDeclared, declared, declaredArgs
	return m, true
}

// matchSetBuilder reads set as a set-builder whose three constants carry
// their definitions. The form is read structurally: the predicate's
// λ-variable is the first argument of comprehension_spec and occurs
// nowhere else, the ∃-chain between the λ and comprehension_spec is the
// binder list, and the output is the third argument — the one binder
// itself in the identity form.
func matchSetBuilder(set core.Term) (comprehensionMembership, bool) {
	var m comprehensionMembership
	m.set = set
	shead, sargs := ext.MatchesApply(set)
	sc, ok := shead.AsConst()
	if !ok || sc.Name() != setComprehensionName || len(sargs) != 1 || sc.DefThm().IsZero() {
		return m, false
	}
	pred, ok := sargs[0].AsAbsTerm()
	if !ok {
		return m, false
	}
	var binders []core.VarTerm
	body := pred.Body()
	for {
		ex := ext.MatchesEXISTS(body)
		if ex.IsZero() {
			break
		}
		binders = append(binders, ex.Var())
		body = ex.Body()
	}
	if len(binders) == 0 {
		return m, false
	}
	phead, pargs := ext.MatchesApply(body)
	pc, ok := phead.AsConst()
	if !ok || pc.Name() != comprehensionSpecName || len(pargs) != 3 || pc.DefThm().IsZero() {
		return m, false
	}
	v := pred.Var()
	if !pargs[0].Equals(v) || pargs[1].HasFree(v) || pargs[2].HasFree(v) {
		return m, false
	}
	m.comprehension, m.spec, m.pred, m.body = sc, pc, pred, pargs[1]
	if len(binders) == 1 && pargs[2].Equals(binders[0]) {
		m.bound = binders[0]
		return m, true
	}
	m.general, m.binders, m.out = true, binders, pargs[2]
	return m, true
}

// mentionsSetBuilderMembership reports whether t spells the constants a
// membership the reading opens is read from: set_member, and either the
// two a set-builder is spelled with or a declared constant. β-collapse
// spells no constant, so a term without them is its own membership
// normal form, and the reading is not begun on it: a scan asks the
// form of every antecedent piece and every hypothesis it meets.
func mentionsSetBuilderMembership(t core.Term) bool {
	if !mentionsConst(t, setMemberName) {
		return false
	}
	return mentionsConst(t, setComprehensionName) && mentionsConst(t, comprehensionSpecName) || mentionsDeclared(t)
}

// mentionsConst reports whether t spells a constant of the name.
func mentionsConst(t core.Term, name core.TermName) bool {
	switch x := t.Core().(type) {
	case core.ConstTerm:
		return x.Name() == name
	case core.AppliedTerm:
		return mentionsConst(x.Fun(), name) || mentionsConst(x.Arg(), name)
	case core.AbsTerm:
		return mentionsConst(x.Body(), name)
	}
	return false
}

// MembershipNormal is a term's membership normal form: the β-collapsed
// term with every membership in a set-builder read — the identity form
// as its condition at the point, the three-part form as the ∃ over its
// binders of the condition and the point's equation with the output —
// innermost first, to a fixpoint. A term in
// which nothing is read is returned as it is, redexes and all: the
// reading is what the form is for, and a comparison that wants βη
// normalizes on its own.
func MembershipNormal(t core.Term) core.Term {
	if !mentionsSetBuilderMembership(t) {
		return t
	}
	collapsed := ext.BetaCollapse(context.Background(), t)
	read := readMemberships(collapsed)
	if read.Equals(collapsed) {
		return t
	}
	return read
}

// readMemberships is MembershipNormal on a β-normal term: the subterms
// first, then the node, and a condition the reading substitutes the
// point into is read again — the point may itself be a set-builder the
// condition tests a member of. The reading descends in the element
// type, so it terminates.
func readMemberships(t core.Term) core.Term {
	switch x := t.Core().(type) {
	case core.AppliedTerm:
		fun, arg := readMemberships(x.Fun()), readMemberships(x.Arg())
		read := t
		if !fun.Equals(x.Fun()) || !arg.Equals(x.Arg()) {
			read = core.Apply(fun, arg)
		}
		m, ok := matchComprehensionMembership(read)
		if !ok {
			return read
		}
		return readMemberships(atomReading(m))
	case core.AbsTerm:
		body := readMemberships(x.Body())
		if body.Equals(x.Body()) {
			return t
		}
		return core.Abs(x.Var(), body)
	}
	return t
}

// atomReading is the pure reading of one membership, β-collapsed: the
// identity form's condition at the point, the three-part form's ∃ over
// its binders. A membership the reading exposes is left as written.
func atomReading(m comprehensionMembership) core.Term {
	if m.general {
		return ext.BetaCollapse(context.Background(), generalReading(m))
	}
	return ext.BetaCollapse(context.Background(), m.body.Substitute(core.MakeTermSubst(m.bound, m.point)))
}

// MembershipAtomReading is the reading of t where t itself is a
// membership in a set-builder (atomReading); false where t is no such
// membership at its top. The memberships its condition tests are not
// read: `a ∈ {p | p ∈ s ∧ P(p)}` reads as `a ∈ s ∧ P(a)`.
func MembershipAtomReading(t core.Term) (core.Term, bool) {
	m, ok := matchComprehensionMembership(t)
	if !ok {
		return nil, false
	}
	return atomReading(m), true
}

// SetBuilderAtPoint reports whether t is a set-builder applied to a
// point, `{p | φ}(x)`: what set_member's definition unfolds
// `x ∈ {p | φ}` to, and what the pointwise form of an equation between
// set-builders spells (FunextTactic). The readings of this file read the
// membership and not this form, which spells no set_member.
func SetBuilderAtPoint(t core.Term) bool {
	head, args := ext.MatchesApply(t)
	c, ok := head.AsConst()
	if !ok || c.Name() != setComprehensionName || len(args) != 2 {
		return false
	}
	_, ok = matchSetBuilder(core.Apply(head, args[0]))
	return ok
}

// HoldsSetBuilderAtPoint reports whether t holds a set-builder applied
// to a point (SetBuilderAtPoint) at its top or anywhere inside, under
// a binder the point is bound by included.
func HoldsSetBuilderAtPoint(t core.Term) bool {
	if SetBuilderAtPoint(t) {
		return true
	}
	switch x := t.Core().(type) {
	case core.AppliedTerm:
		return HoldsSetBuilderAtPoint(x.Fun()) || HoldsSetBuilderAtPoint(x.Arg())
	case core.AbsTerm:
		return HoldsSetBuilderAtPoint(x.Body())
	}
	return false
}

// ReadAsShape is the statement a hypothesis-side move opens of hyp: hyp
// itself where it has the shape the move opens, else — where hyp is a
// membership in a set-builder whose reading has it — that reading, the
// statement the index-targeted splits read hyp through
// (throughMembershipAt). nil where neither has the shape. A hypothesis
// that is the shape as written is opened as written, so the reading
// adds an opening and changes none.
func ReadAsShape(hyp core.Term, shaped func(core.Term) bool) core.Term {
	if shaped(hyp) {
		return hyp
	}
	if read, ok := MembershipAtomReading(hyp); ok && shaped(read) {
		return read
	}
	return nil
}

// membershipReadAt is the read of one hypothesis: `Γ, m ⊢ C` to the one
// child `Γ, r ⊢ C`, where m, the hypothesis at i, is a membership in a
// set-builder and r its reading through the atom's bridge `⊢ m = r`
// (comprehensionMembershipBridge), the parent's proof rebuilt through
// the bridge; with the index of r in the child. nil where the
// hypothesis is no such membership.
func membershipReadAt(goal Prop, i int) (*SubGoals, int) {
	bridge := comprehensionMembershipBridge(goal.Hyp(i))
	if bridge == nil {
		return nil, 0
	}
	read := prop.Rhs(bridge)
	images := hypImages(goal, i, read)
	child := makeImageProp(goal.Conclusion(), images)
	reconstruct := func(thms ...Prop) Prop {
		result := prop.WrapProp(thms[0])
		if read := bridge.LeftAssume(); result.HasHyp(read.Conclusion()) {
			return read.DeriveTrans(result)
		}
		return result
	}
	return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(child, images)}, child), hypIndexOf(child, read)
}

// throughMembershipAt is split, a split of the hypothesis at i, and
// where split declines that hypothesis as written and it is a
// membership in a set-builder, split run on its reading
// (membershipReadAt): the read and the split as one step, the
// hypotheses' provenance composed through both. nil where split
// declines the hypothesis and its reading.
func throughMembershipAt(goal Prop, i int, split func(Prop, int) *SubGoals) *SubGoals {
	if sg := split(goal, i); sg != nil {
		return sg
	}
	read, at := membershipReadAt(goal, i)
	if read == nil {
		return nil
	}
	sg := split(read.ChildGoal(0), at)
	if sg == nil {
		return nil
	}
	return Tactic(func(Prop) *SubGoals { return sg }).expand(read)
}

// generalReading is the pure reading of a three-part membership:
// `x ∈ {t | x̄ | φ}` is `∃x̄. φ ∧ x = t` — the predicate's body at the
// point with comprehension_spec written out. The substitution renames
// the binders apart from the point's free variables.
func generalReading(m comprehensionMembership) core.Term {
	at := m.pred.Body().Substitute(core.MakeTermSubst(m.pred.Var(), m.point))
	var rebuild func(t core.Term) core.Term
	rebuild = func(t core.Term) core.Term {
		if ex := ext.MatchesEXISTS(t); !ex.IsZero() {
			head, _ := ext.MatchesApply(t)
			return core.Apply(head, core.Abs(ex.Var(), rebuild(ex.Body())))
		}
		_, args := ext.MatchesApply(t)
		return ext.WrapTerm(args[1]).And(ext.WrapTerm(args[0]).Eq(ext.WrapTerm(args[2]))).Core()
	}
	return rebuild(at)
}

// MembershipBridge is the kernel's reading: `⊢ t = MembershipNormal(t)`,
// nil where t spells no set-builder membership. Each atom is read by
// its own bridge (comprehensionMembershipBridge), outermost first by
// congruence, pass after pass to the fixpoint; the right side is
// checked against the pure reading up to βη.
func MembershipBridge(t core.Term) *prop.PropWrapper {
	if !mentionsSetBuilderMembership(t) {
		return nil
	}
	ctx := context.Background()
	acc := prop.WrapProp(core.Refl(t)).RewriteConclRhs(prop.DeepBeta)
	// Every pass reads at least one membership, and a reading removes
	// one set-builder from a membership position while the ones it
	// copies in stand lower in the element type, or — a declared
	// constant opened — lower in the definitions' order, which is
	// acyclic; a pass count past the term's size times that depth is a
	// reading that loops, an engine defect.
	bound := (t.Size() + 1) * (len(membershipReads()) + 1)
	read := false
	for pass := 0; ; pass++ {
		w := membershipWalk(prop.Rhs(acc), comprehensionMembershipBridge)
		if w == nil {
			break
		}
		if pass > bound {
			panic(fmt.Sprintf("MembershipBridge: no fixpoint after %d passes on %s — the membership reading loops", pass, ext.PrintTerm(t)))
		}
		acc = acc.EqTrans(w)
		read = true
	}
	if !read {
		return nil
	}
	if acc.NumHyps() != 0 {
		panic("MembershipBridge: the bridge carries hypotheses (engine invariant)")
	}
	if !ext.BetaEtaNormalize(ctx, prop.Rhs(acc)).AlphaEquals(ext.BetaEtaNormalize(ctx, MembershipNormal(t))) {
		panic(fmt.Sprintf("MembershipBridge: the kernel's reading %s is not the pure reading %s (engine invariant)",
			ext.PrintTerm(prop.Rhs(acc)), ext.PrintTerm(MembershipNormal(t))))
	}
	return acc
}

// comprehensionMembershipBridge is the bridge of one atom:
//
//	⊢ x ∈ {p | φ} = {p | φ}(x)                      set_member's definition, β
//	            = ∃p. comprehension_spec(x, φ, p)    set_comprehension's definition, β
//	            = ∃p. φ ∧ (x = p)                    comprehension_spec's definition, β
//	            = φ[x/p]                             the one-point rule on x = p
//
// and for the three-part form the same three definitions, stopping at
// `∃x̄. φ ∧ (x = t)`. An atom `x ∈ c(ā)` at a declared constant first
// opens c: `⊢ x ∈ c(ā) = x ∈ {p | φ}` by c's definition at ā, β and
// congruence. nil where t is not such an atom. In the identity form the
// set-builder's binders are first renamed apart from the point's free
// variables: the fusion declines a point that spells a free variable of
// the bound variable's name, where the pure reading substitutes it
// capture-free.
func comprehensionMembershipBridge(t core.Term) *prop.PropWrapper {
	m, ok := matchComprehensionMembership(t)
	if !ok {
		return nil
	}
	read := setBuilderMembershipBridge(m)
	if !m.opened {
		return read
	}
	open := prop.WrapProp(declaredDefThm(m.declared))
	for _, a := range m.args {
		open = open.RightApply(a)
	}
	open = open.RewriteConclRhs(prop.DeepBeta).LeftApply(core.Apply(m.member, m.point))
	return open.EqTrans(read)
}

// setBuilderMembershipBridge is the bridge of m's set-builder atom,
// `⊢ x ∈ {p | φ} = φ[x/p]` (comprehensionMembershipBridge).
func setBuilderMembershipBridge(m comprehensionMembership) *prop.PropWrapper {
	pred := m.pred
	if !m.general {
		pred = bindersApartFrom(m.pred, m.point)
	}
	set := core.Apply(m.comprehension, pred)
	member := prop.WrapProp(m.member.DefThm()).RightApply(m.point).RightApply(set).RewriteConclRhs(prop.DeepBeta)
	compr := prop.WrapProp(m.comprehension.DefThm()).RightApply(pred).RightApply(m.point).RewriteConclRhs(prop.DeepBeta)
	acc := member.EqTrans(compr)
	spec := membershipWalk(prop.Rhs(acc), func(u core.Term) *prop.PropWrapper {
		head, args := ext.MatchesApply(u)
		c, ok := head.AsConst()
		if !ok || c.Name() != comprehensionSpecName || len(args) != 3 {
			return nil
		}
		w := prop.WrapProp(c.DefThm())
		for _, a := range args {
			w = w.RightApply(a)
		}
		return w
	})
	if spec == nil {
		panic(fmt.Sprintf("comprehensionMembershipBridge: comprehension_spec vanished under the ∃ (engine invariant): %s", ext.PrintTerm(prop.Rhs(acc))))
	}
	acc = acc.EqTrans(spec.RewriteConclRhs(prop.DeepBeta))
	if m.general {
		return acc
	}
	fused := fusePointEquation(prop.Rhs(acc))
	if fused == nil {
		panic(fmt.Sprintf("comprehensionMembershipBridge: the one-point fusion declined %s (engine invariant)", ext.PrintTerm(prop.Rhs(acc))))
	}
	return acc.EqTrans(fused)
}

// fusePointEquation is the one-point rule on the point's equation that
// comprehension_spec adds, `∃p. φ ∧ (x = p) ⇔ φ[x/p]` — on that equation
// and no other. The set driver's fusion (existsOnePointFuse) also fuses
// on an equation the condition ends in under an ∃ of its own, `∃p. (∃g.
// … ∧ g(1) = p) ∧ x = p` to `∃g. … ∧ x = g(1)`, a reading the pure one
// (φ[x/p], `∃g. … ∧ g(1) = x`) does not reach. nil where t is not the
// shape.
func fusePointEquation(t core.Term) *prop.PropWrapper {
	wAbs := ext.MatchesEXISTS(t)
	if wAbs.IsZero() {
		return nil
	}
	l, r, ok := ext.MatchesAND(wAbs.Body())
	if !ok {
		return nil
	}
	return tryFuseBareEq(t, wAbs, wAbs.Var(), r, l, true)
}

// bindersApartFrom is the set-builder's predicate `λv. ∃p. …` with v
// and p renamed away from the free variables of the point, where either
// spells one of them; the predicate itself otherwise.
func bindersApartFrom(pred core.AbsTerm, point core.Term) core.AbsTerm {
	v := pred.Var()
	ex := ext.MatchesEXISTS(pred.Body())
	p := ex.Var()
	if !point.HasFreeName(v.Name()) && !point.HasFreeName(p.Name()) {
		return pred
	}
	fresh := func(old core.VarTerm, apart ...core.Term) core.VarTerm {
		name := old.Name()
		taken := func() bool {
			for _, a := range apart {
				if a.HasFreeName(name) {
					return true
				}
			}
			return false
		}
		for taken() {
			name = utils.NextName(name)
		}
		return core.Var(name, old.Type())
	}
	np := fresh(p, point, ex.Body())
	inner := core.Abs(np, ex.Body().Substitute(core.MakeTermSubst(p, np)))
	exHead, _ := ext.MatchesApply(pred.Body())
	body := core.Apply(exHead, inner)
	nv := fresh(v, point, body, np)
	return core.Abs(nv, body.Substitute(core.MakeTermSubst(v, nv)))
}

// MembershipReadTactic reads every membership in a set-builder the goal
// spells, in the conclusion and the hypotheses, as its condition at the
// point — the three-part form as the ∃ over its binders: one child, the
// goal in its membership normal form; nil where the goal spells none.
func MembershipReadTactic(goal Prop) *SubGoals {
	return rewritePropWith(goal, MembershipBridge)
}
