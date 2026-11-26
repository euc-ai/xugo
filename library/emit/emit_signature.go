// emit_signature.go — the section boundary as the emitter writes it:
// the strips a session's proof opens with, lifted into the closure
// signature the chapter binds them with (prover/proof/section.go).
//
// A session proves a statement by stripping its prefix — `strip_quant`
// mints every leading ∀-binder at once, `strip_imp` moves the
// antecedent into the hypotheses — and the recorded tree opens with
// those steps. A chapter's member binds the same prefix on the
// boundary: `func(a *Argument, x *Expr[A], h Fact)` fixes x and
// assumes the antecedent before the body runs, the Skolems minted
// under the same names the strip mints them, each binder aliased by
// its own name for the claim texts. The lift reads the opening strips
// against the statement, one parameter per slot: a ∀-binder a typed
// term parameter where its type has a phantom in the family's scope
// (`*Expr[Set[A]]`, `*Arrow[Nat, B]`, `*Arrow2[A, A, A]`) and `Term`
// otherwise; a ⇒-antecedent a `Fact`, or the typed structure fact
// where the antecedent applies a structure with a phantom at carriers
// the `on` vocabulary names (`module.ModuleFact[on.R, on.M]`); and a
// bundle binder — a run of ∀-binders and the antecedent that applies
// their structure to exactly them, what `∀φ:ring_homomorphism(A, B).`
// states — ONE structure-fact parameter named after the bundle
// (`φ ring_homomorphism.RingHomomorphismFact[on.R, on.S]`), as
// the boundary's bundleSlotAt binds it. The body renders from the
// first step after the lifted strips; a resident premise or a reading
// at a bound antecedent is its parameter; a Go expression over a
// bound Skolem is its parameter; a claim text spells the binder's own
// name where the statement does.

package emit

import (
	"context"
	"fmt"
	"slices"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/typedgen"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
)

// chapterImportPath is the import path every chapter package lives
// under.
const chapterImportPath = "github.com/euc-ai/xugo/library/proofs/"

// onImportPath is the carrier phantom vocabulary a typed structure fact
// names its carriers in, imported qualified (ext/on).
const onImportPath = "github.com/euc-ai/xugo/ext/on"

// boundParam is one parameter group of a lifted signature: the names,
// grouped Go-style where consecutive parameters of one kind share a
// type, and the type; term marks a group of ∀-binders.
type boundParam struct {
	names  []string
	goType string
	term   bool
}

// boundHyp is a ⇒-antecedent a Fact parameter binds: its statement as
// a hyp-free prop, the parameter's name, and whether a rendered step
// names it (an unnamed one is written `_`).
type boundHyp struct {
	stated core.Prop
	handle string
	used   bool
}

// boundSkolem is a ∀-binder the boundary fixes: the statement's binder
// name, the variable the session's strip minted for it, and the Go name
// of the term parameter that binds it — "" for a bundle's component or
// a Law door's, which no term parameter binds.
type boundSkolem struct {
	binder string
	skolem core.VarTerm
	ident  string
}

// sectionBinding is the lift of a section's opening strips: the
// parameters in order, the hypotheses the Fact parameters bind, the
// binders the term parameters bind, the node the body renders from,
// and the packages the signature spells.
type sectionBinding struct {
	params  []boundParam
	hyps    []*boundHyp
	skolems []boundSkolem
	rest    *msNode
	imports []string
}

// bound reports whether the lift found a slot to bind.
func (b *sectionBinding) bound() bool { return b != nil && len(b.params) > 0 }

// signature is the closure's parameter list after the receiver,
// written with its leading ", ".
func (b *sectionBinding) signature() string {
	var sb strings.Builder
	for _, p := range b.params {
		fmt.Fprintf(&sb, ", %s %s", strings.Join(p.names, ", "), p.goType)
	}
	return sb.String()
}

// liftSlot is one slot of the opening strips: a ∀-binder (name, type,
// the Skolem the strip minted) or a ⇒-antecedent.
type liftSlot struct {
	forall bool
	binder string
	typ    core.HolType
	skolem core.VarTerm
	ante   core.Term
	// applied is the most arguments the statement applies the binder to
	// (appliedArity), 0 where it is only handed whole.
	applied int
}

// readSectionBinding reads the strips a section's tree opens with at
// root against the goal each step saw, and lifts them into parameters.
// statement is what the root's goal states as the headline spells it
// — its binders carry the statement's names, where a goal's may be
// renamed apart by an earlier strip — and is walked beside the tree,
// each bound binder replaced by the variable its strip minted. A strip
// the lift cannot read as the boundary binds it — a partial strip, a
// Skolem it cannot match to its binder — ends the lift there; a tree
// that opens with no strip lifts nothing. taken are the Go names the
// member already declares.
func (e *_Emitter) readSectionBinding(root *msNode, statement core.Term, taken map[string]bool) *sectionBinding {
	var slots []liftSlot
	node := root
	for node != nil && len(node.children) == 1 && node.finallyFold == 0 && !e.sectionCitedSteps[node.step] {
		goal, _ := e.reader.Prop(node.step.Goal)
		next, _ := e.reader.Prop(node.children[0].step.Goal)
		if goal == nil || next == nil {
			break
		}
		switch st := node.step.Step.(type) {
		case *proof.StepProto_StripQuant:
			if st.StripQuant != nil && st.StripQuant.HypIndex != nil {
				return e.liftSlots(root, slots, node, taken)
			}
			binders, matrix := stripLeadingForalls(goal.Conclusion())
			stated, body := stripLeadingForalls(statement)
			if len(binders) == 0 || len(stated) != len(binders) || len(stripLeadingForallsOf(next.Conclusion())) != 0 {
				return e.liftSlots(root, slots, node, taken)
			}
			minted := mintedSkolems(goal, next)
			images, ok := strippedBinderImages(binders, matrix, next.Conclusion(), minted)
			if !ok {
				return e.liftSlots(root, slots, node, taken)
			}
			var run []liftSlot
			var substs []core.TermSubst
			for i, v := range binders {
				w := images[i]
				if !stated[i].Type().Equals(v.Type()) {
					return e.liftSlots(root, slots, node, taken)
				}
				run = append(run, liftSlot{forall: true, binder: string(stated[i].Name()), typ: v.Type(), skolem: w, applied: appliedArity(body, stated[i])})
				substs = append(substs, core.MakeTermSubst(stated[i], w))
			}
			slots = append(slots, run...)
			statement = body.Substitute(substs...)
		case *proof.StepProto_StripImp:
			ante, _, ok := ext.MatchesIMPLY(goal.Conclusion())
			stated, concl, isImply := ext.MatchesIMPLY(statement)
			if !ok || !isImply || !stated.AlphaEquals(ante) || !next.AnyHyp(ante.AlphaEquals) {
				return e.liftSlots(root, slots, node, taken)
			}
			slots = append(slots, liftSlot{ante: ante})
			statement = concl
		default:
			return e.liftSlots(root, slots, node, taken)
		}
		node = node.children[0]
	}
	return e.liftSlots(root, slots, node, taken)
}

// opensWithStrip reports whether the body a lift leaves opens with a
// strip of the conclusion: an opening strip the lift did not read as
// the boundary binds it, which runs as a step against the statement as
// the section states it.
func (b *sectionBinding) opensWithStrip() bool {
	if b == nil || b.rest == nil {
		return false
	}
	switch st := b.rest.step.Step.(type) {
	case *proof.StepProto_StripQuant:
		return st.StripQuant == nil || st.StripQuant.HypIndex == nil
	case *proof.StepProto_StripQuant1, *proof.StepProto_StripImp:
		return true
	}
	return false
}

// planSectionLifts reads each section's lift (readSectionBinding)
// against the member's declarations: the signature its closure binds,
// and what decides its headline (decideSectionForms). In a member of
// several sections a Skolem is one variable of the kernel and may be
// two things in the Go: the parameter of a closure whose strips minted
// it, and a declaration of the script in a section that mentions it
// and binds it by no parameter — a strip further down its proof minted
// the same name, or it opens with a strip the lift does not read. A
// Skolem every section that mentions it binds under one Go name is
// that name throughout the member (bindLift); any other is split
// (splitSkolems): its parameter inside each closure that binds it
// (enterLift) and its declaration everywhere else. The variables the
// sections' goals hold free are the proof's own (goalFrees).
func (e *_Emitter) planSectionLifts() {
	e.sectionLifts = make([]*sectionBinding, len(e.sections))
	e.splitSkolems = nil
	mentions := make([]map[_VarKey]bool, len(e.sections))
	for i, s := range e.sections {
		e.reader = s.reader
		root := e.foldFinallyTails(buildMSTree(s.detailedSteps))
		e.sectionLifts[i] = e.readSectionBinding(root, e.sectionInitGoal(s).Conclusion(), e.declSet())
		mentions[i] = e.sectionVarKeys(s)
	}
	e.goalFrees = map[_VarKey]bool{}
	for _, mentioned := range mentions {
		for key := range mentioned {
			e.goalFrees[key] = true
		}
	}
	if len(e.sections) < 2 {
		return
	}
	binders := map[_VarKey]map[int]string{}
	for i, lift := range e.sectionLifts {
		if !lift.bound() {
			continue
		}
		for _, sk := range lift.skolems {
			key := _VarKey{sk.skolem.Name(), sk.skolem.Type().Key()}
			if binders[key] == nil {
				binders[key] = map[int]string{}
			}
			binders[key][i] = sk.ident
		}
	}
	for key, bySection := range binders {
		if !boundAlike(key, bySection, mentions) {
			if e.splitSkolems == nil {
				e.splitSkolems = map[_VarKey]bool{}
			}
			e.splitSkolems[key] = true
		}
	}
}

// boundAlike reports whether every section that mentions key
// (mentions) binds it, all under one Go name; bySection is the name
// each binding section binds it under.
func boundAlike(key _VarKey, bySection map[int]string, mentions []map[_VarKey]bool) bool {
	name, named := "", false
	for i, mentioned := range mentions {
		if !mentioned[key] {
			continue
		}
		ident, binds := bySection[i]
		if !binds || named && ident != name {
			return false
		}
		name, named = ident, true
	}
	return true
}

// sectionVarKeys is the free variables of the goals section s's
// rendered steps see. The steps of a claim an earlier section's cite
// stands for (sectionCitedSteps) render nothing, and the Skolems only
// they mint are named nowhere.
func (e *_Emitter) sectionVarKeys(s *_SectionEmit) map[_VarKey]bool {
	keys := map[_VarKey]bool{}
	note := func(t core.Term) {
		for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
			keys[_VarKey{v.Name(), v.Type().Key()}] = true
		}
	}
	for _, step := range s.detailedSteps {
		if e.sectionCitedSteps[step] {
			continue
		}
		goal, _ := e.reader.Prop(step.Goal)
		if goal == nil {
			continue
		}
		note(goal.Conclusion())
		for i := range goal.NumHyps() {
			note(goal.Hyp(i))
		}
	}
	return keys
}

// stripLeadingForallsOf is the binders of t's leading ∀s.
func stripLeadingForallsOf(t core.Term) []core.VarTerm {
	binders, _ := stripLeadingForalls(t)
	return binders
}

// mintedSkolems are the variables free in next and not in goal — what
// the strip between them minted.
func mintedSkolems(goal, next core.Prop) []core.VarTerm {
	before := map[string]bool{}
	note := func(t core.Term) {
		for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
			before[string(v.Name())+"\x00"+string(v.Type().Key())] = true
		}
	}
	note(goal.Conclusion())
	for i := range goal.NumHyps() {
		note(goal.Hyp(i))
	}
	var out []core.VarTerm
	seen := map[string]bool{}
	for _, v := range next.Conclusion().Frees(func(core.VarTerm) bool { return true }) {
		k := string(v.Name()) + "\x00" + string(v.Type().Key())
		if !before[k] && !seen[k] {
			seen[k] = true
			out = append(out, v)
		}
	}
	return out
}

// strippedBinderImages reads each binder's freshly minted variable
// from its occurrence in the stripped conclusion. Names cannot pair
// them: the renamer's suffix is an authored subscript's spelling (`A₀`
// renamed apart is `A_1`, which is how `A₁` parses), so the binders
// are matched against the stripped conclusion, each image a fresh
// variable of the binder's type, no two alike, and the substitution
// they make is checked to give that conclusion exactly.
func strippedBinderImages(binders []core.VarTerm, matrix, next core.Term, minted []core.VarTerm) ([]core.VarTerm, bool) {
	names := unify.TermNameSet{}
	for _, v := range binders {
		names.Add(v.Name())
	}
	bindings, ok := unify.TermMatchApprox(matrix, next, names)
	if !ok {
		return nil, false
	}
	ctx := context.Background()
	images := make([]core.VarTerm, len(binders))
	var substs []core.TermSubst
	seen := map[_VarKey]bool{}
	for i, v := range binders {
		image, found := bindings[v.Name()]
		if !found {
			return nil, false
		}
		w, isVar := ext.EtaCollapse(ctx, ext.BetaCollapse(ctx, image)).AsVar()
		if !isVar || !w.Type().Equals(v.Type()) {
			return nil, false
		}
		fresh := false
		for _, candidate := range minted {
			if candidate.Equals(w) {
				fresh = true
				break
			}
		}
		key := _VarKey{w.Name(), w.Type().Key()}
		if !fresh || seen[key] {
			return nil, false
		}
		seen[key] = true
		images[i] = w
		substs = append(substs, core.MakeTermSubst(v, w))
	}
	return images, matrix.Substitute(substs...).AlphaEquals(next)
}

// liftSlots groups the slots into parameters, the body starting at
// rest. A parameter name a constant's identifier or a reserved name
// holds, or a second binder's name, lifts nothing: the closure would
// bind one Go name twice, so the tree renders from root with its
// strips as steps. A name a variable's identifier holds — the
// statement's own binder, a λ-binder of a cited statement, a Skolem
// of another type, which the symbol walk registers alike — is the
// parameter's, and that variable takes another identifier
// (installBinding).
func (e *_Emitter) liftSlots(root *msNode, slots []liftSlot, rest *msNode, taken map[string]bool) *sectionBinding {
	b := &sectionBinding{rest: rest}
	if len(slots) == 0 {
		return b
	}
	used := map[string]bool{}
	for n := range taken {
		used[n] = true
	}
	bound := map[string]bool{}
	takes := func(name string) bool {
		if bound[name] || e.reservedIdent(name) && name != "a" || used[name] && !e.movableIdent(name) {
			return false
		}
		bound[name], used[name] = true, true
		return true
	}
	for _, sl := range slots {
		if sl.forall && !takes(e.binderParamName(sl.binder)) {
			return &sectionBinding{rest: root}
		}
	}
	imports := map[string]bool{}
	facts := 0
	factName := func() string {
		facts++
		name := "h"
		if facts > 1 {
			name = fmt.Sprintf("h%d", facts)
		}
		for n := 2; used[name] || e.reservedIdent(name); n++ {
			name = fmt.Sprintf("h%d", n)
		}
		used[name] = true
		return name
	}
	var skolemBinder = map[string]string{}
	for i := 0; i < len(slots); {
		if !slots[i].forall {
			hyp := &boundHyp{stated: core.MakeProp(slots[i].ante), handle: factName()}
			goType := "Fact"
			if typed, home, ok := e.structureFactType(slots[i].ante, skolemBinder); ok {
				goType = typed
				if home != "" {
					imports[home] = true
				}
				imports[onImportPath] = true
			}
			b.hyps = append(b.hyps, hyp)
			if n := len(b.params); n > 0 && !b.params[n-1].term && b.params[n-1].goType == goType {
				b.params[n-1].names = append(b.params[n-1].names, hyp.handle)
			} else {
				b.params = append(b.params, boundParam{names: []string{hyp.handle}, goType: goType})
			}
			i++
			continue
		}
		j := i
		for j < len(slots) && slots[j].forall {
			j++
		}
		run := slots[i:j]
		if j < len(slots) {
			if name, goType, home, ok := e.bundleParam(run, slots[j].ante); ok {
				// A bundle named by its letter binds a name no binder took.
				if !bound[name] && !takes(name) {
					return &sectionBinding{rest: root}
				}
				hyp := &boundHyp{stated: core.MakeProp(slots[j].ante), handle: name}
				b.hyps = append(b.hyps, hyp)
				b.params = append(b.params, boundParam{names: []string{name}, goType: goType})
				// The components are fixed under their own names and bound
				// by no Go parameter: a Go expression over one keeps the
				// local the member declares.
				for _, sl := range run {
					b.skolems = append(b.skolems, boundSkolem{binder: sl.binder, skolem: sl.skolem})
					skolemBinder[string(sl.skolem.Name())] = sl.binder
				}
				if home != "" {
					imports[home] = true
				}
				if goType != "Fact" {
					imports[onImportPath] = true
				}
				i = j + 1
				continue
			}
		}
		for _, sl := range run {
			ident := e.binderParamName(sl.binder)
			goType := e.termParamType(sl.typ, sl.applied)
			b.skolems = append(b.skolems, boundSkolem{binder: sl.binder, skolem: sl.skolem, ident: ident})
			skolemBinder[string(sl.skolem.Name())] = sl.binder
			if n := len(b.params); n > 0 && b.params[n-1].goType == goType && b.params[n-1].term {
				b.params[n-1].names = append(b.params[n-1].names, ident)
				continue
			}
			b.params = append(b.params, boundParam{names: []string{ident}, goType: goType, term: true})
		}
		i = j
	}
	for p := range imports {
		b.imports = append(b.imports, p)
	}
	sort.Strings(b.imports)
	return b
}

// binderParamName is the Go parameter a statement binder is bound by:
// the binder's name, a subscript in ASCII digits (`x₁` binds x1, as
// the closure-name lint reads it), a prime as Prime (`c'` binds
// cPrime, as the carrier vocabulary spells it).
func (e *_Emitter) binderParamName(binder string) string {
	name := string(utils.FormatSubscript(binder))
	name = strings.Map(func(r rune) rune {
		if r >= '₀' && r <= '₉' {
			return '0' + (r - '₀')
		}
		return r
	}, name)
	name = strings.ReplaceAll(name, "'", "Prime")
	return sanitizeIdent(name)
}

// termParamType is the typed parameter a ∀-binder of type t is bound
// as, the spellings the corpus's closures use: a set as
// `*Expr[Set[X]]`, a one-argument function as an Arrow, a
// two-argument one — an operation, a relation — as an Arrow2, any
// other type with a phantom in the family's scope as `*Expr[…]`, and
// `Term` where no phantom spells it. applied is the most arguments the
// statement applies the binder to: a two-argument type the statement
// applies to one argument only is a family of values — X:(num → set(A))
// read at X(n), whose type is num → A → bool as a relation's is — and
// binds as an Arrow into its values' phantom, `*Arrow[Nat, Set[A]]`,
// the parameter's Apply then taking the one argument the body gives it.
func (e *_Emitter) termParamType(t core.HolType, applied int) string {
	if ext.IsFunType(t) {
		spine := ext.MatchesFun(t)
		args, result := spine[:len(spine)-1], spine[len(spine)-1]
		if len(args) == 2 && applied == 1 {
			dom, okDom := e.phantomInScope(args[0])
			values, okValues := e.phantomInScope(core.MakeFun(args[1], result))
			if !okDom || !okValues {
				return "Term"
			}
			return fmt.Sprintf("*Arrow[%s, %s]", dom, values)
		}
		if len(args) == 2 || len(args) == 1 && !result.Equals(core.TypeBool()) {
			parts := make([]string, 0, len(spine))
			for _, s := range spine {
				p, ok := e.phantomInScope(s)
				if !ok {
					return "Term"
				}
				parts = append(parts, p)
			}
			if len(args) == 1 {
				return fmt.Sprintf("*Arrow[%s]", strings.Join(parts, ", "))
			}
			return fmt.Sprintf("*Arrow2[%s]", strings.Join(parts, ", "))
		}
	}
	if ph, ok := e.phantomInScope(t); ok {
		return fmt.Sprintf("*Expr[%s]", ph)
	}
	return "Term"
}

// familyImportPath is the import path of the family the member lands
// in.
func (e *_Emitter) familyImportPath() string {
	dir := e.opts.Family
	if fam, ok := registry.FamilyByName(e.opts.Family); ok && fam.Dir != "" {
		dir = fam.Dir
	}
	return chapterImportPath + dir
}

// structureFactType is the typed fact a ⇒-antecedent binds as, where
// the antecedent applies a structure with a phantom and every carrier
// argument is a bound binder the `on` vocabulary has a letter for;
// skolemBinder maps a minted variable's name to its binder. home is
// the defining family's import path, "" where that is the member's own.
func (e *_Emitter) structureFactType(ante core.Term, skolemBinder map[string]string) (goType, home string, ok bool) {
	head, args := ext.MatchesApply(ante)
	c, isConst := head.AsConst()
	if !isConst {
		return "", "", false
	}
	alias, home, carriers, ok := typedgen.StructureFactAlias(string(c.Name()), e.familyImportPath())
	if !ok {
		return "", "", false
	}
	letters := make([]string, 0, len(carriers))
	for _, pos := range carriers {
		if pos >= len(args) {
			return "", "", false
		}
		v, isVar := args[pos].AsVar()
		if !isVar {
			return "", "", false
		}
		binder, bound := skolemBinder[string(v.Name())]
		if !bound {
			return "", "", false
		}
		letter, ok := on.Letter(binder)
		if !ok {
			return "", "", false
		}
		letters = append(letters, "on."+letter)
	}
	if home == e.familyImportPath() {
		home = ""
	}
	return fmt.Sprintf("%s[%s]", alias, strings.Join(letters, ", ")), home, true
}

// bundleParam reads a run of ∀-binders and the antecedent after it as
// a bundle binder: the antecedent applies a structure that names its
// bundle — by a subject component or a letter (dsl.BundleSyntax) — to
// exactly the run's minted variables, in order. The parameter is
// named after the bundle and typed as the structure's fact at the
// carriers among the run, or `Fact` where the vocabulary has no letter
// for one; home is the typed fact's package, "" for an untyped one or
// the member's own.
func (e *_Emitter) bundleParam(run []liftSlot, ante core.Term) (name, goType, home string, ok bool) {
	head, args := ext.MatchesApply(ante)
	c, isConst := head.AsConst()
	if !isConst || len(args) != len(run) {
		return "", "", "", false
	}
	syntax := registry.GetConstMetaManager().ConstSyntax(string(c.Name()))
	if syntax == nil || syntax.Bundle == nil || !syntax.Bundle.Structure {
		return "", "", "", false
	}
	for i, sl := range run {
		v, isVar := args[i].AsVar()
		if !isVar || !v.Equals(sl.skolem) {
			return "", "", "", false
		}
	}
	switch {
	case syntax.Bundle.Subject >= 0 && syntax.Bundle.Subject < len(run):
		name = run[syntax.Bundle.Subject].binder
	case syntax.Bundle.Letter != "":
		name = syntax.Bundle.Letter
	default:
		return "", "", "", false
	}
	skolemBinder := map[string]string{}
	for _, sl := range run {
		skolemBinder[string(sl.skolem.Name())] = sl.binder
	}
	goType, home, typed := e.structureFactType(ante, skolemBinder)
	if !typed {
		goType = "Fact"
	}
	return e.binderParamName(name), goType, home, true
}

// installBinding makes a lift the member's (bindLift) and opens the
// closure it binds (enterLift): a member of one section, or a door's
// own binding.
func (e *_Emitter) installBinding(b *sectionBinding) {
	e.bindLift(b)
	e.enterLift(b)
}

// enterLift opens the closure a section renders in under its lift: the
// Fact parameters are the handles a premise or a reading at their
// antecedents renders as, the receiver is `a` — `arg` where a parameter
// is named a — and a claim text spells each bound binder under its own
// name. A lift that binds nothing opens a closure with no parameter.
func (e *_Emitter) enterLift(b *sectionBinding) {
	e.boundHyps, e.closureReceiver, e.surfaceSkolems = nil, "", nil
	e.readUnderLift(b)
	if !b.bound() {
		return
	}
	e.boundHyps = b.hyps
	e.closureReceiver = "a"
	for _, p := range b.params {
		if slices.Contains(p.names, "a") {
			e.closureReceiver = "arg"
		}
	}
	e.surfaceSkolems = slices.Clone(b.skolems)
}

// readUnderLift names the split Skolems (planSectionLifts) by the
// parameters of the closure b binds, for the steps read from here on —
// marked or rendered: inside that closure a split Skolem is its
// parameter, where the member's table holds its declaration. A lift
// that binds none, or nil, names none.
func (e *_Emitter) readUnderLift(b *sectionBinding) {
	e.closureIdents = nil
	if !b.bound() {
		return
	}
	for _, sk := range b.skolems {
		key := _VarKey{sk.skolem.Name(), sk.skolem.Type().Key()}
		if sk.ident == "" || !e.splitSkolems[key] {
			continue
		}
		if e.closureIdents == nil {
			e.closureIdents = map[_VarKey]string{}
		}
		e.closureIdents[key] = sk.ident
	}
}

// bindLift makes a lift's names the member's: the term parameters are
// the Go names of the Skolems they bind — declared by no ctx.Var, since
// the boundary registers them — no other declaration takes a name the
// signature binds, and a step rewriting with a bound antecedent
// addresses it through its parameter. A member of several sections
// binds every section's lift before any body renders. A split Skolem
// (planSectionLifts) keeps its declaration, for the sections that
// mention it outside the closures that bind it, and is its parameter
// only while such a closure is read (readUnderLift).
func (e *_Emitter) bindLift(b *sectionBinding) {
	for _, p := range b.params {
		for _, n := range p.names {
			e.reserveBoundName(n)
		}
	}
	for _, p := range b.params {
		for _, n := range p.names {
			e.evictIdent(n)
		}
	}
	for _, sk := range b.skolems {
		e.bindSurface(sk)
		key := _VarKey{sk.skolem.Name(), sk.skolem.Type().Key()}
		if sk.ident == "" || e.splitSkolems[key] {
			continue
		}
		if old, declared := e.varIdent[key]; declared {
			delete(e.varDecl, old)
		}
		e.varIdent[key] = sk.ident
	}
	for _, p := range b.imports {
		e.addImport(p)
	}
	// A step rewriting with a bound antecedent addresses it through the
	// parameter, as a Given branch's steps address its hypothesis.
	var visit func(n *msNode)
	visit = func(n *msNode) {
		if n == nil || e.sectionCitedSteps[n.step] {
			return
		}
		if idx, ok := hypAddressedBy(n.step); ok {
			if goal, _ := e.reader.Prop(n.step.Goal); goal != nil && idx < goal.NumHyps() {
				for _, h := range b.hyps {
					if goal.Hyp(idx).AlphaEquals(h.stated.Conclusion()) {
						if e.hypHandleByUse == nil {
							e.hypHandleByUse = map[_HypUse]string{}
						}
						if _, bound := e.hypHandleByUse[_HypUse{step: n.step}]; !bound {
							e.hypHandleByUse[_HypUse{step: n.step}] = h.handle
							h.used = true
						}
						break
					}
				}
			}
		}
		for _, c := range n.children {
			visit(c)
		}
	}
	visit(b.rest)
}

// movableIdent reports whether name is a variable's identifier — one
// the signature may take, the variable moving to another (evictIdent).
func (e *_Emitter) movableIdent(name string) bool {
	_, held := e.varDecl[name]
	return held
}

// evictIdent moves the variable declared under the identifier name,
// where one is, to a fresh identifier: the closure's signature binds
// name, and the variable the symbol walk registered under it keeps its
// declaration under another Go name. The Skolem a term parameter
// binds is not among them: bindLift points it at the parameter.
func (e *_Emitter) evictIdent(name string) {
	v, held := e.varDecl[name]
	if !held {
		return
	}
	delete(e.varDecl, name)
	taken := e.declSet()
	taken[name] = true
	ident := e.freshIdent(name, taken)
	e.varDecl[ident] = v
	e.varIdent[_VarKey{v.Name(), v.Type().Key()}] = ident
}

// reserveBoundName records a Go name the closure's signature binds: no
// other ident, receiver or handle the member allocates takes it.
func (e *_Emitter) reserveBoundName(name string) {
	if e.boundNames == nil {
		e.boundNames = map[string]bool{}
	}
	e.boundNames[name] = true
}

// bindSurface records a binder the boundary fixes under its own name:
// the Skolem and the binder name are the boundary's declarations, which
// no registration-only ctx.Var repeats (boundVars), and the statement's
// bound variable of that name, where the symbol table holds it under a
// Go name the signature binds, takes another ident. That a claim text
// spells the Skolem under the binder's name is the closure's
// (enterLift, surfaceNamed). A split Skolem (planSectionLifts) is the
// boundary's declaration in the closures that bind it only: a text
// another section's script reads it in registers it as any other.
func (e *_Emitter) bindSurface(sk boundSkolem) {
	if e.boundVars == nil {
		e.boundVars = map[string]bool{}
	}
	if e.registerableVarNames == nil {
		e.registerableVarNames = map[string]bool{}
	}
	bound := _VarKey{core.TermName(sk.binder), sk.skolem.Type().Key()}
	if old, declared := e.varIdent[bound]; declared && e.boundNames[old] {
		v := e.varDecl[old]
		delete(e.varDecl, old)
		ident := e.freshIdent(old, e.declSet())
		e.varIdent[bound], e.varDecl[ident] = ident, v
	}
	if !e.splitSkolems[_VarKey{sk.skolem.Name(), sk.skolem.Type().Key()}] {
		e.boundVars[string(sk.skolem.Name())] = true
	}
	e.boundVars[sk.binder] = true
	e.registerableVarNames[sk.binder] = true
}

// boundHandleFor is the parameter a bound antecedent renders as where
// stated is that antecedent, "" elsewhere; a use marks the parameter
// named.
func (e *_Emitter) boundHandleFor(stated core.Prop) string {
	if stated == nil {
		return ""
	}
	for _, h := range e.boundHyps {
		if stated.Conclusion().AlphaEquals(h.stated.Conclusion()) {
			h.used = true
			return h.handle
		}
	}
	return ""
}

// surfaceNamed is p with every Skolem a term parameter binds spelled
// under its binder's name — the name the closure aliases it by, so a
// claim text reads as the statement spells it. A Skolem whose binder
// name p holds free already keeps its minted spelling.
func (e *_Emitter) surfaceNamed(p core.Prop) core.Prop {
	if p == nil || len(e.surfaceSkolems) == 0 {
		return p
	}
	terms := append([]core.Term{p.Conclusion()}, p.Hyps()...)
	substs := e.surfaceSubsts(terms...)
	if len(substs) == 0 {
		return p
	}
	hyps := make([]core.Term, 0, p.NumHyps())
	for i := range p.NumHyps() {
		hyps = append(hyps, p.Hyp(i).Substitute(substs...))
	}
	return core.MakeProp(p.Conclusion().Substitute(substs...), hyps...)
}

// surfaceNamedTerm is surfaceNamed for one term: a witness or a case
// term the Argument reads, where every bound binder is aliased by its
// own name.
func (e *_Emitter) surfaceNamedTerm(t core.Term) core.Term {
	if t == nil || len(e.surfaceSkolems) == 0 {
		return t
	}
	substs := e.surfaceSubsts(t)
	if len(substs) == 0 {
		return t
	}
	return t.Substitute(substs...)
}

// surfaceSubsts is the renaming surfaceNamed applies over terms: each
// Skolem the boundary fixes, free in them, to its binder's name, except
// where the binder's name is free in them already.
func (e *_Emitter) surfaceSubsts(terms ...core.Term) []core.TermSubst {
	free := map[string]bool{}
	for _, t := range terms {
		for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
			free[string(v.Name())] = true
		}
	}
	var substs []core.TermSubst
	for _, sk := range e.surfaceSkolems {
		if sk.binder == string(sk.skolem.Name()) || free[sk.binder] || !free[string(sk.skolem.Name())] {
			continue
		}
		substs = append(substs, core.MakeTermSubst(sk.skolem, ext.Var(ext.TermName(sk.binder), sk.skolem.Type()).Core()))
	}
	return substs
}

// componentSkolem reports whether v is a Skolem the boundary fixes
// under its binder's name and no term parameter binds — a bundle's
// component, a Law door's.
func (e *_Emitter) componentSkolem(v core.VarTerm) bool {
	for _, sk := range e.surfaceSkolems {
		if sk.ident == "" && sk.skolem.Equals(v) {
			return true
		}
	}
	return false
}

// definitionExpr is the definition an Unfold or an Unfolded names for
// the constant it opens: the entry var of the definition
// (EmitOptions.DefinitionOf), with its package among the file's
// imports and its entry among the member's unfolds; and the constant's
// quoted name where no entry defines it — neither verb takes it, so the
// file does not compile: a definition is landed first, and a constant
// the logic defines (∃!) is opened by Unpack or read by a closer,
// never by Unfold.
func (e *_Emitter) definitionExpr(constant string) string {
	if e.opts.DefinitionOf != nil {
		if ref, entry, ok := e.opts.DefinitionOf(constant); ok && ref.Expr != "" {
			if ref.ImportPath != "" {
				e.addImport(ref.ImportPath)
			}
			if e.unfoldNames == nil {
				e.unfoldNames = map[string]bool{}
			}
			e.unfoldNames[entry] = true
			return ref.Expr
		}
	}
	return fmt.Sprintf("%q", constant)
}

// sortedUnfoldNames is EmitResult.UnfoldNames.
func (e *_Emitter) sortedUnfoldNames() []string {
	names := make([]string, 0, len(e.unfoldNames))
	for name := range e.unfoldNames {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

// addImport records a package the file spells beyond its deps. A
// reference within the member's own family imports nothing, and its
// callers pass no path for it.
func (e *_Emitter) addImport(p string) {
	if p == "" {
		panic("addImport: empty import path")
	}
	if e.extraImports == nil {
		e.extraImports = map[string]bool{}
	}
	e.extraImports[p] = true
}

// extraImportList is the recorded packages, sorted.
func (e *_Emitter) extraImportList() []string {
	out := make([]string, 0, len(e.extraImports))
	for p := range e.extraImports {
		out = append(out, p)
	}
	sort.Strings(out)
	return out
}

// appliedArity is the most arguments v stands applied to in t, as the
// head of an application; 0 where t applies it nowhere.
func appliedArity(t core.Term, v core.VarTerm) int {
	most := 0
	for sub := range ext.SubTerms(t) {
		head, args := ext.MatchesApply(sub)
		if len(args) > most && head.Equals(v) {
			most = len(args)
		}
	}
	return most
}
