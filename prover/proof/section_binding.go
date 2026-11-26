// section_binding.go — what a section closure's parameters bind, read
// off the statement's dependencies.
//
// A statement is binders and hypotheses: `∀x₁ … xₙ. H₁ ∧ … ∧ Hₘ ⇒ C`, a
// hypothesis depending on the binders it mentions. The closure's
// parameters, in order, are one order of opening it, and any order
// that respects the dependencies is the same theorem:
//
//   - a term parameter (Term, *TermWrapper, a typed term, a vector, a
//     member) binds the statement's next binder, in the statement's
//     order;
//   - a fact parameter binds hypotheses whose binders are all bound —
//     with nothing to take there, the bundle: the run of binders next
//     in order that a structure fact mentions, fixed under their own
//     names, and that fact (a typed fact: the fact of its predicate);
//   - a member's evidence is its membership, assumed once the member
//     run it stands in is bound.
//
// A run of fact parameters takes the hypotheses available — those whose
// binders are all bound and no earlier parameter took — by content,
// never by position: a typed fact the first one of its predicate at the
// carriers its phantoms name (a plain Fact a structure door marks with
// its predicate, WithPredicate, likewise); a plain fact standing alone
// all the rest; plain facts standing together one each, in the
// statement's order, as long as they last. More hypotheses than facts
// standing together is ambiguous, and refused: the author moves a fact
// parameter to stand right after the binders its hypotheses mention.
//
// A fact with nothing available binds a bundle: the binders next in
// order, as many as make a structure fact at them available — a
// hypothesis applying a constant to every binder of the run directly,
// what a bundle binder `∀G:group_on(A).` states — and takes those; a
// hypothesis that merely mentions a binder of the run, `∀x. g(f(x)) =
// x` beside `lrs_morphism(Y, X, g, g_ψ)`, is left for the facts after,
// however early it becomes available. Where no run has a structure fact,
// the bundle is the shortest run with any hypothesis mentioning every
// binder of it, and takes those. A binder of the run no hypothesis
// mentions is refused: it is bound by a term parameter.
//
// What the parameters leave stays in the goal as a statement:
// `∀(the binders not bound). (the hypotheses not taken) ⇒ C`. A closure
// that binds a prefix of a statement sees the rest as the statement says
// it — an induction on a binder left unbound generalizes over the
// binders left with it.
//
// A curried statement — the elaboration of a bundle binder among them,
// `∀G. group_on(G) ⇒ ∀x. …` — is a telescope of such blocks, each its
// binders and one antecedent. The planner reads it as the one scope its
// standard form is: every binder in order, every piece of every
// antecedent a hypothesis, with no notion of which block holds what. The
// order the parameters give is laid out by one step (_OpenTelescope, the
// kernel's), which merges the blocks the parameters reach and is
// recorded only where it differs from the statement; a statement whose
// blocks cannot merge, a later block binding a name an earlier
// hypothesis mentions free, is refused — rename the binder. The binding
// then walks the opened goal one ∀ and one ⇒ at a time.

package proof

import (
	"fmt"
	"reflect"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dimtypes"
	"github.com/euc-ai/xugo/prover/tactic"
)

// _SectionPlan is how a closure binds its statement: the order the
// statement opens in, nil where it opens as it stands, and one slot per
// move of the opened goal — a parameter's binder, hypothesis or bundle,
// or a member run's evidence.
type _SectionPlan struct {
	items []tactic.TelescopeItem
	slots []binderSlot
}

// _BindingPlanner is planSectionBinding's state over the statement's
// telescope: the binders bound (a prefix, bound), the pieces taken, the
// members whose evidence is still to come, and the predicates a door
// marked plain fact parameters with (WithPredicate), by parameter.
type _BindingPlanner struct {
	g          Prop
	tel        tactic.Telescope
	bound      int
	taken      map[tactic.PieceRef]bool
	pending    []int
	predicates map[int]string
	items      []tactic.TelescopeItem
	slots      []binderSlot
}

// WithPredicate marks the fact parameter at param — counting from 1
// after the Argument — of a section's body as the fact of predicate: it
// binds that predicate's hypothesis, as a typed structure fact of the
// predicate does, where a plain Fact would take every hypothesis
// available. A structure door hands the plain Fact of a law's closure
// its predicate so.
func WithPredicate(body any, param int, predicate string) any {
	return _PredicateBody{body: body, param: param, predicate: predicate}
}

type _PredicateBody struct {
	body      any
	param     int
	predicate string
}

// unwrapPredicates reads the predicates WithPredicate marked body's fact
// parameters with, and the body underneath.
func unwrapPredicates(body any) (any, map[int]string) {
	predicates := map[int]string{}
	for {
		pb, ok := body.(_PredicateBody)
		if !ok {
			return body, predicates
		}
		predicates[pb.param-1] = pb.predicate
		body = pb.body
	}
}

// _FactWant is what a fact parameter asks for: the predicate of a typed
// structure fact, with the binders its carrier phantoms name at the
// predicate's carrier positions; the predicate alone for a plain Fact a
// door marked; nothing for a plain Fact.
type _FactWant struct {
	predicate string
	carriers  []int
	binders   []string
}

// matches reports whether piece is a hypothesis w asks for: any, for a
// plain fact; the predicate applied, its carriers the binders the
// phantoms name, for a typed one.
func (w _FactWant) matches(piece core.Term) bool {
	if w.predicate == "" {
		return true
	}
	head, args := ext.MatchesApply(piece)
	c, isConst := head.AsConst()
	if !isConst || string(c.Name()) != w.predicate {
		return false
	}
	for i, pos := range w.carriers {
		if pos >= len(args) {
			return false
		}
		v, isVar := args[pos].AsVar()
		if !isVar || string(v.Name()) != w.binders[i] {
			return false
		}
	}
	return true
}

// planSectionBinding checks body's signature against the statement and
// plans the binding (the file header). Every failure is an authoring
// error reported before a single proof step runs.
func planSectionBinding(g Prop, body any) (_SectionPlan, error) {
	body, predicates := unwrapPredicates(body)
	if body == nil {
		return _SectionPlan{}, fmt.Errorf("body is nil")
	}
	ft := reflect.TypeOf(body)
	if ft.Kind() != reflect.Func {
		return _SectionPlan{}, fmt.Errorf("body must be a func(*Argument, …); got %s", ft)
	}
	if ft.IsVariadic() {
		return _SectionPlan{}, fmt.Errorf("body must not be variadic — declare one parameter per bound binder")
	}
	if ft.NumOut() != 0 {
		return _SectionPlan{}, fmt.Errorf("body must not return anything; got %d result(s)", ft.NumOut())
	}
	if ft.NumIn() == 0 || ft.In(0) != dedPtrType {
		return _SectionPlan{}, fmt.Errorf("body's first parameter must be *Argument; got %s", ft)
	}
	n := ft.NumIn() - 1
	p := &_BindingPlanner{g: g, tel: tactic.ReadTelescope(g.Conclusion()), taken: map[tactic.PieceRef]bool{}, predicates: predicates}
	paramSlot := make([]int, n)
	for k := 0; k < n; {
		pt := ft.In(k + 1)
		if !IsStructureFactType(pt) {
			if _, isMember := describeMemberType(pt); !isMember {
				if err := p.flush(); err != nil {
					return _SectionPlan{}, err
				}
			}
			si, err := p.bindBinder(k)
			if err != nil {
				return _SectionPlan{}, err
			}
			paramSlot[k] = si
			if _, isMember := describeMemberType(pt); isMember {
				p.pending = append(p.pending, si)
			}
			k++
			continue
		}
		if err := p.flush(); err != nil {
			return _SectionPlan{}, err
		}
		end := k
		for end < n && IsStructureFactType(ft.In(end+1)) {
			end++
		}
		if err := p.bindFacts(ft, k, end, paramSlot); err != nil {
			return _SectionPlan{}, err
		}
		k = end
	}
	if err := p.flush(); err != nil {
		return _SectionPlan{}, err
	}
	if len(p.pending) > 0 {
		return _SectionPlan{}, fmt.Errorf("no hypothesis states the membership of %s — a member's evidence is its membership\n(statement: %s)",
			p.slots[p.pending[0]].name, PrintProp(g))
	}
	if err := p.checkParams(ft, paramSlot); err != nil {
		return _SectionPlan{}, err
	}
	items := p.items
	if opened, err := p.tel.Open(items, g.Conclusion()); err != nil {
		return _SectionPlan{}, fmt.Errorf("the parameters open the statement in an order it does not admit: %v — rename the binder\n(statement: %s)",
			err, PrintProp(g))
	} else if opened.AlphaEquals(g.Conclusion()) {
		items = nil
	}
	return _SectionPlan{items: items, slots: p.slots}, nil
}

// bindBinder plans parameter k at the statement's next binder.
func (p *_BindingPlanner) bindBinder(k int) (int, error) {
	if p.bound >= len(p.tel.Binders) {
		return 0, fmt.Errorf("parameter %d binds a binder, but the statement offers none there: it binds %d, every one bound before it\n(statement: %s)",
			k+1, len(p.tel.Binders), PrintProp(p.g))
	}
	v := p.tel.Binders[p.bound]
	p.items = append(p.items, tactic.TelescopeItem{Binder: p.bound})
	p.bound++
	p.slots = append(p.slots, binderSlot{kind: slotForAll, name: string(v.Name()), typ: v.Type()})
	return len(p.slots) - 1, nil
}

// available are the pieces not taken whose binders are all bound, in
// the statement's order.
func (p *_BindingPlanner) available() []tactic.PieceRef { return p.availableWith(p.bound) }

// availableWith is available were the first bound binders bound.
func (p *_BindingPlanner) availableWith(bound int) []tactic.PieceRef {
	var out []tactic.PieceRef
	for b := range p.tel.Pieces {
		for i, piece := range p.tel.Pieces[b] {
			ref := tactic.PieceRef{Block: b, Index: i}
			if !p.taken[ref] && p.boundAll(piece, b, bound) {
				out = append(out, ref)
			}
		}
	}
	return out
}

// boundAll reports whether every binder a term of block b mentions is
// among the first bound binders.
func (p *_BindingPlanner) boundAll(t core.Term, b, bound int) bool {
	for _, d := range p.tel.Deps(t, b) {
		if d >= bound {
			return false
		}
	}
	return true
}

// piece is the term ref names.
func (p *_BindingPlanner) piece(ref tactic.PieceRef) core.Term {
	return p.tel.Pieces[ref.Block][ref.Index]
}

// take plans the hypothesis joining refs, for the slot to bind it.
func (p *_BindingPlanner) take(refs []tactic.PieceRef, slot binderSlot) int {
	terms := make([]core.Term, len(refs))
	for i, ref := range refs {
		p.taken[ref] = true
		terms[i] = p.piece(ref)
	}
	p.items = append(p.items, tactic.TelescopeItem{Binder: -1, Pieces: refs})
	slot.kind = slotImp
	slot.ante = joinedTerms(terms)
	p.slots = append(p.slots, slot)
	return len(p.slots) - 1
}

// joinedTerms conjoins ts to the left, in order.
func joinedTerms(ts []core.Term) core.Term {
	t := ts[0]
	for _, u := range ts[1:] {
		t = ext.WrapTerm(t).And(u).Core()
	}
	return t
}

// flush plans the evidence of the members bound since the last flush:
// the memberships among the pieces whose binders are all bound, one
// hypothesis, every member it states carrying it.
func (p *_BindingPlanner) flush() error {
	if len(p.pending) == 0 {
		return nil
	}
	var refs []tactic.PieceRef
	var members, waiting []int
	for _, si := range p.pending {
		ref, found := p.membership(p.slots[si].name)
		if !found {
			waiting = append(waiting, si)
			continue
		}
		if !p.taken[ref] && !containsRef(refs, ref) {
			refs = append(refs, ref)
		}
		members = append(members, si)
	}
	p.pending = waiting
	if len(refs) > 0 {
		sortRefs(refs)
		p.take(refs, binderSlot{evidence: members})
	}
	return nil
}

// membership is the available piece stating that the binder named lies
// in a set.
func (p *_BindingPlanner) membership(name string) (tactic.PieceRef, bool) {
	for _, ref := range p.available() {
		member, _, ok := membershipSet(p.piece(ref))
		if v, isVar := member.(core.VarTerm); ok && isVar && string(v.Name()) == name {
			return ref, true
		}
	}
	return tactic.PieceRef{}, false
}

func containsRef(refs []tactic.PieceRef, ref tactic.PieceRef) bool {
	for _, r := range refs {
		if r == ref {
			return true
		}
	}
	return false
}

// sortRefs orders refs as the statement does.
func sortRefs(refs []tactic.PieceRef) {
	for i := 1; i < len(refs); i++ {
		for j := i; j > 0 && (refs[j].Block < refs[j-1].Block ||
			refs[j].Block == refs[j-1].Block && refs[j].Index < refs[j-1].Index); j-- {
			refs[j], refs[j-1] = refs[j-1], refs[j]
		}
	}
}

// bindFacts plans the fact parameters from k up to end, a run of them,
// in turn: each takes the hypotheses available where it stands (the
// file header), or binds a bundle where none is.
func (p *_BindingPlanner) bindFacts(ft reflect.Type, k, end int, paramSlot []int) error {
	for i := k; i < end; i++ {
		w := p.want(ft, i)
		avail := p.available()
		var mine []tactic.PieceRef
		if w.predicate != "" {
			for _, ref := range avail {
				if w.matches(p.piece(ref)) {
					mine = []tactic.PieceRef{ref}
					break
				}
			}
		} else {
			reserved := p.reserved(ft, i+1, end, avail)
			var left []tactic.PieceRef
			for _, ref := range avail {
				if !reserved[ref] {
					left = append(left, ref)
				}
			}
			plain := 0
			for j := i; j < end; j++ {
				if p.want(ft, j).predicate == "" {
					plain++
				}
			}
			switch {
			case len(left) == 0:
			case plain == 1:
				mine = left
			case len(left) <= plain:
				mine = left[:1]
			default:
				return fmt.Errorf("parameters %d to %d: %d fact parameters stand together where %d hypotheses are available"+
					" — one fact standing alone takes them all, facts standing together take one each; place each fact"+
					" parameter right after the binders its hypotheses mention\n(statement: %s)",
					i+1, end, plain, len(left), PrintProp(p.g))
			}
		}
		if len(mine) == 0 {
			if err := p.bindBundle(w, i, paramSlot); err != nil {
				return err
			}
			continue
		}
		paramSlot[i] = p.take(mine, binderSlot{})
	}
	return nil
}

// want is what the fact parameter i asks for.
func (p *_BindingPlanner) want(ft reflect.Type, i int) _FactWant {
	if pred, marked := p.predicates[i]; marked {
		return _FactWant{predicate: pred}
	}
	if info, typed := describeStructureFactType(ft.In(i + 1)); typed {
		return _FactWant{predicate: info.predicate, carriers: info.carriers, binders: info.binders}
	}
	return _FactWant{}
}

// reserved are the pieces of avail the typed facts from i up to end
// will take: for each, the first that matches it and no earlier one
// reserved.
func (p *_BindingPlanner) reserved(ft reflect.Type, i, end int, avail []tactic.PieceRef) map[tactic.PieceRef]bool {
	out := map[tactic.PieceRef]bool{}
	for j := i; j < end; j++ {
		w := p.want(ft, j)
		if w.predicate == "" {
			continue
		}
		for _, ref := range avail {
			if !out[ref] && w.matches(p.piece(ref)) {
				out[ref] = true
				break
			}
		}
	}
	return out
}

// bindBundle plans fact parameter k as a bundle (the file header): the
// shortest run of binders next in order with a structure fact at them
// available — a hypothesis w asks for, applying a constant to every
// binder of the run — or, with none, with any hypothesis w asks for
// mentioning every binder of the run; those hypotheses (the first, for a
// predicate) are the fact's.
func (p *_BindingPlanner) bindBundle(w _FactWant, k int, paramSlot []int) error {
	start := p.bound
	run, mine := p.bundleRun(w, start, true)
	if run == 0 {
		run, mine = p.bundleRun(w, start, false)
	}
	if run == 0 {
		return p.bundleRefused(w, k, start)
	}
	for j := start; j < start+run; j++ {
		p.items = append(p.items, tactic.TelescopeItem{Binder: j})
	}
	p.bound = start + run
	names := make([]string, 0, run)
	for _, v := range p.tel.Binders[start:p.bound] {
		names = append(names, string(v.Name()))
	}
	terms := make([]core.Term, len(mine))
	for i, ref := range mine {
		p.taken[ref] = true
		terms[i] = p.piece(ref)
	}
	p.items = append(p.items, tactic.TelescopeItem{Binder: -1, Pieces: mine})
	p.slots = append(p.slots, binderSlot{kind: slotBundle, names: names, ante: joinedTerms(terms)})
	paramSlot[k] = len(p.slots) - 1
	return nil
}

// bundleRun is the shortest run of binders from start that makes a
// hypothesis w asks for available, mentioning every binder of the run —
// applied to each directly, when direct — and the hypotheses it takes:
// the first, for a predicate. 0 when no run does.
func (p *_BindingPlanner) bundleRun(w _FactWant, start int, direct bool) (int, []tactic.PieceRef) {
	for bound := start + 1; bound <= len(p.tel.Binders); bound++ {
		var mine []tactic.PieceRef
		for _, ref := range p.availableWith(bound) {
			piece := p.piece(ref)
			if !w.matches(piece) || !p.mentionsRun(piece, start, bound) {
				continue
			}
			if direct && !p.appliedToRun(piece, start, bound) {
				continue
			}
			mine = append(mine, ref)
			if w.predicate != "" {
				break
			}
		}
		if len(mine) > 0 {
			return bound - start, mine
		}
	}
	return 0, nil
}

// bundleRefused is the refusal of a fact parameter no run binds as a
// bundle: for a typed fact, the hypothesis of its predicate whose
// carriers are not the binders its phantoms name, or that the statement
// has no hypothesis of its predicate; otherwise the first binder no
// hypothesis it could bind mentions, or, every binder mentioned, nothing
// to bind.
func (p *_BindingPlanner) bundleRefused(w _FactWant, k, start int) error {
	if w.predicate != "" {
		if msg := p.predicateMismatch(w, k); msg != "" {
			return fmt.Errorf("%s\n(statement: %s)", msg, PrintProp(p.g))
		}
	}
	for j := start; j < len(p.tel.Binders); j++ {
		v := p.tel.Binders[j]
		mentioned := false
		for b := range p.tel.Pieces {
			for i, piece := range p.tel.Pieces[b] {
				if !p.taken[tactic.PieceRef{Block: b, Index: i}] && w.matches(piece) && freeIn(v, piece) {
					mentioned = true
				}
			}
		}
		if !mentioned {
			return fmt.Errorf("parameter %d is a Fact at the binder %s, which no hypothesis it could bind mentions"+
				" — a Fact parameter binds the hypotheses whose binders are bound before it, or a bundle: the binders"+
				" next in order with a hypothesis that mentions each of them; bind %s with a term parameter\n(statement: %s)",
				k+1, v.Name(), v.Name(), PrintProp(p.g))
		}
	}
	what := "no hypothesis is available where it stands, and binding the binders left makes none available"
	if w.predicate != "" {
		what = fmt.Sprintf("no hypothesis of %s is available where it stands, and binding the binders left makes none available", w.predicate)
	}
	return fmt.Errorf("parameter %d is a fact, but %s\n(statement: %s)", k+1, what, PrintProp(p.g))
}

// appliedToRun reports whether piece is a constant applied to arguments
// among which every binder from start up to bound stands.
func (p *_BindingPlanner) appliedToRun(piece core.Term, start, bound int) bool {
	head, args := ext.MatchesApply(piece)
	if _, isConst := head.AsConst(); !isConst {
		return false
	}
	for j := start; j < bound; j++ {
		found := false
		for _, arg := range args {
			if arg.Equals(p.tel.Binders[j]) {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}
	return true
}

// predicateMismatch names, for the typed fact parameter k that found no
// hypothesis of its predicate at its carriers, what the statement has
// instead: a hypothesis of the predicate whose carriers are other
// binders, or none of the predicate at all. "" where a hypothesis of
// the predicate stands at the carriers the phantoms name.
func (p *_BindingPlanner) predicateMismatch(w _FactWant, k int) string {
	for b := range p.tel.Pieces {
		for i, piece := range p.tel.Pieces[b] {
			if p.taken[tactic.PieceRef{Block: b, Index: i}] || !headNamed(piece, w.predicate) {
				continue
			}
			if w.matches(piece) {
				return ""
			}
			_, args := ext.MatchesApply(piece)
			for j, pos := range w.carriers {
				if pos < len(args) {
					if v, isVar := args[pos].AsVar(); !isVar || string(v.Name()) != w.binders[j] {
						return fmt.Sprintf("parameter %d is a fact of %s, and the statement's %s places carrier %d at %s, which is not the binder %s the parameter's phantom names",
							k+1, w.predicate, ext.PrintTerm(piece), j+1, ext.PrintTerm(args[pos]), w.binders[j])
					}
				}
			}
		}
	}
	return fmt.Sprintf("parameter %d is a fact of %s, but no hypothesis of the statement is one", k+1, w.predicate)
}

// mentionsRun reports whether piece mentions every binder from start up
// to bound.
func (p *_BindingPlanner) mentionsRun(piece core.Term, start, bound int) bool {
	for j := start; j < bound; j++ {
		if !freeIn(p.tel.Binders[j], piece) {
			return false
		}
	}
	return true
}

// freeIn reports whether v occurs free in t.
func freeIn(v core.VarTerm, t core.Term) bool {
	for _, f := range t.Frees(nil) {
		if f.Equals(v) {
			return true
		}
	}
	return false
}

// headNamed reports whether t is the constant pred applied.
func headNamed(t core.Term, pred string) bool {
	head, _ := ext.MatchesApply(t)
	c, isConst := head.AsConst()
	return isConst && string(c.Name()) == pred
}

// checkParams checks each parameter's type against the slot it binds,
// and records on the slot what binding it needs.
func (p *_BindingPlanner) checkParams(ft reflect.Type, paramSlot []int) error {
	g := p.g
	slots := p.slots
	for i := 0; i < ft.NumIn()-1; i++ {
		pt := ft.In(i + 1)
		si := paramSlot[i]
		slot := slots[si]
		if info, ok := describeMemberType(pt); ok {
			// A member parameter (*Member[Elem, Car]): binds a binder of the
			// element type, and its membership is its evidence. The carrier
			// phantom must name a binder.
			if !info.holType.Equals(slot.typ) {
				return fmt.Errorf("parameter %d asserts type %s but the statement's binder is %s\n(statement: %s)",
					i+1, ext.FormatType(info.holType), slot.describe(), PrintProp(g))
			}
			if info.binder == "" {
				return fmt.Errorf("parameter %d is a member at on.Any, which names no carrier — a structure law's member names its carrier's letter (on.C, on.M, …)\n(statement: %s)",
					i+1, PrintProp(g))
			}
			slots[si].member = &info
			continue
		}
		if info, ok := describeStructureFactType(pt); ok {
			// A typed structure fact: binds the hypothesis of its predicate,
			// or the bundle a bundle binder states (`∀S:comm_ring_on(B).`);
			// the carriers are checked at bind time, where the binders their
			// phantoms name are in scope.
			if !headNamed(slot.ante, info.predicate) {
				return fmt.Errorf("parameter %d is a fact of %s but binds %s\n(statement: %s)",
					i+1, info.predicate, ext.PrintTerm(slot.ante), PrintProp(g))
			}
			slots[si].structure = &info
			continue
		}
		if desc, ok := ext.DescribeExprType(pt); ok {
			// A typed term parameter (*ext.Expr[T]): binds a binder like a
			// Term parameter, and ASSERTS its type — checked here, before
			// any proof step runs. Reflection cannot give parameter NAMES
			// but it gives TYPES, so a cross-typed swap the untyped spelling
			// would silently run is a plan-time error.
			if !desc.HOLType().Equals(slot.typ) {
				return fmt.Errorf("parameter %d asserts type %s but the statement's binder is %s\n(statement: %s)",
					i+1, ext.FormatType(desc.HOLType()), slot.describe(), PrintProp(g))
			}
			slots[si].expr = &desc
			continue
		}
		if desc, ok := dimtypes.DescribeVecType(pt); ok {
			// A dimension-refined vector parameter (*dimtypes.Vec[Elem, D]):
			// binds a binder of the carrier type, and its letters must be
			// binders bound BEFORE it — the anchor is resolved at bind time.
			if !desc.HOLType().Equals(slot.typ) {
				return fmt.Errorf("parameter %d asserts carrier %s but the statement's binder is %s\n(statement: %s)",
					i+1, ext.FormatType(desc.HOLType()), slot.describe(), PrintProp(g))
			}
			if desc.AtSomeDim() {
				return fmt.Errorf("parameter %d is a vector at SomeDim, which a closure parameter cannot anchor"+
					" — spell its dimension letter, or adopt the binder with a.VecAt in the body\n(statement: %s)",
					i+1, PrintProp(g))
			}
			for _, letter := range desc.Letters() {
				if !earlierNumBinder(slots[:si], letter) {
					return fmt.Errorf("parameter %d is a vector at dimension letter %s, which no earlier parameter binds as a num binder"+
						" — declare the dimension parameter before the vectors\n(statement: %s)",
						i+1, letter, PrintProp(g))
				}
			}
			slots[si].vec = &desc
			continue
		}
		if desc, ok := dimtypes.DescribeMatType(pt); ok {
			// A dimension-refined matrix parameter (*dimtypes.Mat[Elem, R, C]):
			// the vector case with two phantoms, so both letter sets must be
			// bound before it.
			if !desc.HOLType().Equals(slot.typ) {
				return fmt.Errorf("parameter %d asserts carrier %s but the statement's binder is %s\n(statement: %s)",
					i+1, ext.FormatType(desc.HOLType()), slot.describe(), PrintProp(g))
			}
			if desc.AtSomeDim() {
				return fmt.Errorf("parameter %d is a matrix at SomeDim, which a closure parameter cannot anchor"+
					" — spell its dimension letters, or adopt the binder with a.MatAt in the body\n(statement: %s)",
					i+1, PrintProp(g))
			}
			for _, letter := range desc.Letters() {
				if !earlierNumBinder(slots[:si], letter) {
					return fmt.Errorf("parameter %d is a matrix at dimension letter %s, which no earlier parameter binds as a num binder"+
						" — declare the dimension parameters before the matrices\n(statement: %s)",
						i+1, letter, PrintProp(g))
				}
			}
			slots[si].mat = &desc
			continue
		}
		if desc, ok := dimtypes.DescribeVecFunType(pt); ok {
			// A dimension-refined map parameter (*dimtypes.VecFun[Elem, Source,
			// Target]): the matrix case over the map's carrier, both letter
			// sets bound before it.
			if !desc.HOLType().Equals(slot.typ) {
				return fmt.Errorf("parameter %d asserts carrier %s but the statement's binder is %s\n(statement: %s)",
					i+1, ext.FormatType(desc.HOLType()), slot.describe(), PrintProp(g))
			}
			if desc.AtSomeDim() {
				return fmt.Errorf("parameter %d is a map at SomeDim, which a closure parameter cannot anchor"+
					" — spell its dimension letters, or adopt the binder with a.VecFunAt in the body\n(statement: %s)",
					i+1, PrintProp(g))
			}
			for _, letter := range desc.Letters() {
				if !earlierNumBinder(slots[:si], letter) {
					return fmt.Errorf("parameter %d is a map at dimension letter %s, which no earlier parameter binds as a num binder"+
						" — declare the dimension parameters before the maps\n(statement: %s)",
						i+1, letter, PrintProp(g))
				}
			}
			slots[si].mapping = &desc
			continue
		}
		if !paramWantsTerm(pt) && pt != factType {
			return fmt.Errorf("parameter %d has type %s — a bound parameter must be Term (or *ext.TermWrapper), a typed term, vector or member for a binder,"+
				" or Fact or a typed structure fact for hypotheses", i+1, pt)
		}
	}
	return nil
}

// callSectionClosure opens the statement in the planned order, binds
// each slot on a, in turn, and calls the closure with the Argument
// context and the bound values.
func callSectionClosure(verb, text string, fn reflect.Value, plan _SectionPlan, a *Argument) {
	if plan.items != nil {
		a.s.Do(a.cur, _OpenTelescope{items: plan.items})
		a.advance("OpenTelescope")
	}
	args := make([]reflect.Value, 0, len(plan.slots)+1)
	args = append(args, reflect.ValueOf(a))
	members := map[int]*boundMember{}
	param := 0
	for i, slot := range plan.slots {
		if slot.evidence != nil {
			bindEvidence(verb, text, slot, members, a)
			continue
		}
		param++
		if slot.member != nil {
			m := bindMember(verb, text, param, slot, a)
			members[i] = m
			args = append(args, m.value)
			continue
		}
		args = append(args, bindSlot(verb, text, param-1, slot, a))
	}
	fn.Call(args)
}

// bindEvidence assumes the memberships of a member run and checks, for
// each member, that a conjunct says it lies in the set its carrier
// phantom names; the assumed fact is each member's evidence.
func bindEvidence(verb, text string, slot binderSlot, members map[int]*boundMember, a *Argument) {
	defer func() {
		if r := recover(); r != nil {
			panic(fmt.Sprintf("Script.%s(%q): binding the memberships %s: %v", verb, text, slot.describe(), r))
		}
	}()
	evidence := a.Assume()
	content, ok := evidence.BoundContent()
	if !ok {
		panic("the assumed memberships carry no content")
	}
	sets := map[string]core.Term{}
	for _, c := range conjunctTerms(content) {
		member, set, isMembership := membershipSet(c)
		if !isMembership {
			continue
		}
		if v, isVar := member.AsVar(); isVar {
			sets[string(v.Name())] = set
		}
	}
	for _, i := range slot.evidence {
		m := members[i]
		v, _ := m.term.AsVar()
		set, found := sets[string(v.Name())]
		if !found {
			panic(fmt.Sprintf("no conjunct of %s states the membership of %s", ext.PrintTerm(content), ext.PrintTerm(m.term)))
		}
		if want := a.carrierSet(m.carrier); !set.Equals(want) {
			panic(a.withAliasLegend(fmt.Sprintf("%s lies in %s, but its parameter's carrier phantom names %s, which is %s",
				ext.PrintTerm(m.term), ext.PrintTerm(set), m.carrier, ext.PrintTerm(want))))
		}
		m.prove(evidence)
	}
}
