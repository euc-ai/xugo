// section.go — opening a section: how a statement's own binders reach
// the Go code that proves it.
//
// A section statement IS a λ, and both halves of this file exist so the
// proof body never has to RE-DECLARE what the statement already binds.
// Script.Theorem / Script.Lemma flow the statement's leading binders
// LEXICALLY into the proving closure; Script.Skolemize covers the case
// where a body strips its own ∀-prefix mid-proof, handing back the
// minted frees keyed by the binder names the statement spells rather
// than by the tactic's subscript-freshening internals.
//

package proof

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dimtypes"
	"github.com/euc-ai/xugo/ext/dsl"
)

// =======================================================================
// The section boundary as a binding form
// =======================================================================
//
// The section boundary as a binding form.
//
// A section statement IS a λ: `∀A B C. body` binds A, B and C, and the
// proof of it works under those binders. Before this file the Go side
// had to REBUILD what the statement already declared — a `ctx.Var("A_0",
// NumType)` wall aligned to the Skolem mint by nothing but a naming
// convention and a "declaration order == strip order" comment, plus an
// opening `StripQuant()/StripImp()` choreography that spelled out the
// arity a second time.
//
// Script.Theorem / Script.Lemma close that gap: the statement's leading
// binders flow LEXICALLY into the Go closure that proves it.
//
//	s.Theorem("∀A B C:num. (∀n:num. A * n ≤ B * n + C) ⇔ A ≤ B",
//	    func(a *Argument, A, B, C Term) { … })
//
// # The rule: the parameters say what is bound
//
// Parameters after the leading `*Argument` bind the statement's binders
// and hypotheses by their dependencies (section_binding.go):
//
//	Term param  ↔  the next binder in order — a.Fix: strip, mint the
//	               Skolem, register it in the ParseScope, pass the term in
//	Fact param  ↔  the hypotheses whose binders are bound before it —
//	               a.Assume: move them into the hyps, pass the Fact in;
//	               or, with none, a bundle: the binders next in order up
//	               to the hypothesis that mentions them
//
// What the parameters leave stays in the goal as a statement: an
// induction proof that must NOT pre-strip its induction variable writes
// the parameters before it and reaches for a.Induct in the body:
//
//	family.Theorem("∀m n p:num. m + n = m + p ⇔ n = p",
//	    func(a *Argument) { a.Induct("m", Case(…), Case(…)) })
//
// A body whose FIRST move must run before the
// binding — an unfold that changes what the antecedent says — wraps in
// Opening (below): the move runs on the section root, and the
// signature is then read against the goal it leaves.
//
// # Position, and what checks it
//
// Go reflection cannot read parameter NAMES, so the binding is
// positional: two same-typed parameters written in the wrong order
// (A/B swapped) type-check and run. Everything else is checked here and
// loudly — arity, kind (a Fact where the goal has no ⇒), and shape — and
// the names are checked statically by TestLintBinderClosureNames
// (gates/lint_test.go), which reads the closure's parameter names off
// the AST and requires them to match the statement's binder names
// positionally. That is strictly more than the naming convention it
// replaces, which nothing checked at all.
//
// # A statement is closed
//
// A section states a closed theorem: its variables ∀-bound, its
// premises ⇒-antecedents, so that every premise is a slot the closure
// binds. A statement text with hypotheses left of ⊢ panics at
// SectionText, naming the closed spelling.
//
// # pb consequences
//
// A Term parameter emits StripQuant1 (a.Fix's ministep), so a converted
// member's tree differs from a hand-written `StripQuant()` strip-all and
// its recorded refutations may re-key. That is accepted: re-recording is
// routine maintenance, and buying tree-compatibility would mean a
// strip-all special case whose only job is to look like the code it
// replaces.

// Theorem opens a section on the statement text, binds its leading
// binders to body's parameters (see the file header), runs body against
// the resulting Argument context, and Qeds the section. Returns the section node so
// the caller can return its PromisedThm or cite it from a later section.
//
// body's type is checked by reflection, not by the compiler: it must be
// `func(*Argument, …)` with no results, its parameters after the Argument context being
// Term (or *ext.TermWrapper) and Fact in any order. A malformed body
// panics before any proof step runs.
//
// A body may instead be a single Action — the ONE-ACTION section, for a
// statement that closes in one move (`By(dep)`, `BySets()`, `Cite(dep)`)
// with no binder to bind and no intermediate fact to name:
//
//	family.Theorem("∀s t:(A → bool). s ∪ t = t ∪ s", BySets())
//
// It runs exactly as the expanded `func(a *Argument) { a.Do(action) }`
// would — same spine, same goal state at the action — so the two
// spellings are interchangeable; the closure form remains the one that
// can bind binders or sequence further moves.
// The variadic sectionConsts are SectionText's per-section const
// overrides, for a statement that must read a non-default instance of
// an overloaded const (the polymorphic A/B-flavour case). Omit them
// unless the statement genuinely needs one.
//
// The statement is a string, or a dsl.Statement written in parts,
// whose abbreviations are in scope for the section's texts beside the
// script's own (a name declared by both panics).
func (s *Script) Theorem(statement any, body any, sectionConsts ...Term) *GoalStackNode {
	return s.openSection("Theorem", statement, body, sectionConsts)
}

// Lemma is Theorem for an intermediate section — mechanically
// identical, documentary in intent: Theorem states the member's
// headline, Lemma the steps it is assembled from.
func (s *Script) Lemma(statement any, body any, sectionConsts ...Term) *GoalStackNode {
	return s.openSection("Lemma", statement, body, sectionConsts)
}

// sectionStatement reads a section's statement argument: the text,
// and the entries of the parts' abbreviation table where it was written
// in parts. The entries are read under the script's table
// (withSectionAbbreviations), not here.
func sectionStatement(verb string, statement any) (string, dsl.Abbrev) {
	switch st := statement.(type) {
	case string:
		return st, nil
	case dsl.Statement:
		return sectionStatementParts(verb, &st)
	case *dsl.Statement:
		if st == nil {
			panic(fmt.Sprintf("Script.%s: a nil *Statement — write the statement as a string or as a Statement literal", verb))
		}
		return sectionStatementParts(verb, st)
	}
	panic(fmt.Sprintf("Script.%s: the statement is a string or a Statement{Binders, Hypotheses, Conclusion, Abbrev}, not %T", verb, statement))
}

func sectionStatementParts(verb string, st *dsl.Statement) (string, dsl.Abbrev) {
	text, err := st.Text()
	if err != nil {
		panic(fmt.Sprintf("Script.%s: %v", verb, err))
	}
	return text, st.Abbrev
}

// withSectionAbbreviations runs open with a section's own entries read
// under the script's table — the member's, and the chapter's under it
// — as one table (dsl.AbbreviationTable.Extend), so an entry of the
// section may spell an entry of theirs; the section's leading binders
// are exempt from the capture check, and the script's scope is restored
// after. A name both declare panics: one name, one meaning. A section
// with no entries of its own, under a script's table — a lemma of a
// member whose statement or chapter declares the abbreviations its
// lemmas spell — reads under the script's, its own leading binders
// exempt.
func (s *Script) withSectionAbbreviations(verb, text string, entries dsl.Abbrev, open func()) {
	saved, savedBinders := s.ParseScope.Abbreviations, s.ParseScope.AbbreviationBinders
	if len(entries) == 0 && saved == nil {
		open()
		return
	}
	merged, err := saved.Extend(entries)
	if err != nil {
		panic(fmt.Sprintf("Script.%s(%q): the section's abbreviations, read under the member's and its chapter's: %v",
			verb, text, err))
	}
	binders := map[string]bool{}
	for _, name := range dsl.LeadingBinderNames(text) {
		binders[name] = true
	}
	s.UseAbbreviations(merged, binders)
	defer s.UseAbbreviations(saved, savedBinders)
	open()
}

// Opening wraps a section body with ONE opening action that runs on
// the section root BEFORE any binder is bound — the OPENED section.
//
//	family.Theorem(
//	    "∀s:set(A). ∀f:(A → real). finite(s) ⇒ …",
//	    Opening(Unfold(RealSumDef), func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], finite Fact) { … }))
//
// The binders of the closure form are bound before the body's first
// action, so a member whose proof must REWRITE first — unfold a
// defined constant so that the hypothesis it is handed is the unfolded
// one — could not use them at all: it had to open zero-parameter and
// rebuild the prefix with a.Fix()/a.Assume() walls, which also gave
// up the typed binder parameters. Opening runs the rewrite first and
// keeps the binders on the boundary, typed.
//
// The rule: `open` runs through a.Do on the section root, and the
// body is then bound against the goal AS IT STANDS AFTER the opening
// action — a closure's parameters plan against that goal (an Unfold
// that rewrites inside an antecedent hands the closure the unfolded
// Fact; a binder the opening consumed is no longer a slot, and the
// plan error says so against the OPENED goal), a one-Action body runs
// on it. Several opening moves are spelled as one Chain(…). The
// opening action is an ordinary recorded step — no new proto, nothing
// changes in record/replay — and typed parameters adopt after it
// exactly as they do at an unopened boundary. An unwrapped body is
// untouched by all this: the unopened path is the same code it was.
//
// Panics, naming Opening: a nil opening action; a wrapper nested in a
// wrapper (spell the moves as one Chain); a body that is neither a
// closure nor an Action (nil included).
func Opening(open Action, body any) _OpeningBody {
	if open == nil {
		panic("Opening: the opening action is nil — pass the move that runs before the binders are bound (Unfold(…), or a Chain(…) of several)")
	}
	switch body.(type) {
	case _OpeningBody:
		panic("Opening: nested in Opening — spell several opening moves as ONE Chain(…) inside a single Opening")
	case nil:
		panic("Opening: the body is nil — pass the section body (a binder closure or one Action)")
	case Action:
	default:
		if reflect.TypeOf(body).Kind() != reflect.Func {
			panic(fmt.Sprintf("Opening: the body must be a binder closure (func(*Argument, …)) or one Action; got %T", body))
		}
	}
	return _OpeningBody{open: open, body: body}
}

// _OpeningBody is what Opening returns: the opening action and the
// body it fronts. Recognized by openSection alone.
type _OpeningBody struct {
	open Action
	body any
}

func (s *Script) openSection(verb string, statement any, body any, sectionConsts []Term) *GoalStackNode {
	text, table := sectionStatement(verb, statement)
	var sec *GoalStackNode
	s.withSectionAbbreviations(verb, text, table, func() {
		sec = s.openSectionText(verb, text, body, sectionConsts)
	})
	return sec
}

// openSectionText is openSection on the statement's text, under the
// scope openSection prepared.
func (s *Script) openSectionText(verb, text string, body any, sectionConsts []Term) *GoalStackNode {
	sec := s.SectionText(text, sectionConsts...)
	if ob, ok := body.(_OpeningBody); ok {
		// The opened section (see Opening): the opening action runs on
		// the section root, and the body — closure or one action — is
		// bound against the goal it leaves, inside the same block.
		Derive(func(a *Argument) { ob.run(verb, text, a) }).applyAction(s, sec)
		sec.Qed()
		return sec
	}
	if act, ok := body.(Action); ok {
		// The one-action section (see Theorem's doc). Run through the
		// same Derive wrapper as the closure form so the two spellings
		// are one code path from the spine's point of view.
		Derive(func(a *Argument) { a.Do(act) }).applyAction(s, sec)
		sec.Qed()
		return sec
	}
	plan, err := planSectionBinding(sec.Goal, body)
	if err != nil {
		panic(fmt.Sprintf("Script.%s(%q): %v", verb, text, err))
	}
	closure, _ := unwrapPredicates(body)
	fn := reflect.ValueOf(closure)
	Derive(func(a *Argument) { callSectionClosure(verb, text, fn, plan, a) }).applyAction(s, sec)
	sec.Qed()
	return sec
}

// run is the opened section's block: the opening move, then the body
// against the goal it left. The plan is computed HERE, from a.cur's
// goal after the opening, rather than from the statement — that is
// the whole point of the wrapper (see Opening).
func (ob _OpeningBody) run(verb, text string, a *Argument) {
	ob.runOpening(verb, text, a)
	if a.closed {
		panic(fmt.Sprintf("Script.%s(%q): Opening — the opening action closed the section; there is nothing left for the body to prove", verb, text))
	}
	if act, ok := ob.body.(Action); ok {
		a.Do(act)
		return
	}
	plan, err := planSectionBinding(a.cur.Goal, ob.body)
	if err != nil {
		panic(fmt.Sprintf("Script.%s(%q): Opening — the closure's parameters bind against the goal AS OPENED"+
			" (the statement after the opening action), which does not match them: %v", verb, text, err))
	}
	closure, _ := unwrapPredicates(ob.body)
	callSectionClosure(verb, text, reflect.ValueOf(closure), plan, a)
}

// runOpening runs the opening action through a.Do, attributing a
// failure to the opening move — the panics inside are specific about
// WHAT failed; this adds WHERE.
func (ob _OpeningBody) runOpening(verb, text string, a *Argument) {
	defer func() {
		if r := recover(); r != nil {
			panic(fmt.Sprintf("Script.%s(%q): Opening — the opening action failed: %v", verb, text, r))
		}
	}()
	a.Do(ob.open)
}

// boundMember is a member parameter between its binding and its
// guard's: the value handed to the closure, the variable fixed, the
// binder its carrier phantom names, and the setter of its evidence.
type boundMember struct {
	value   reflect.Value
	term    core.Term
	carrier string
	prove   func(Fact)
}

// bindMember fixes a member parameter's binder and adopts it; its
// evidence is the guard's, set when the guard slot binds.
func bindMember(verb, text string, param int, slot binderSlot, a *Argument) *boundMember {
	defer func() {
		if r := recover(); r != nil {
			panic(fmt.Sprintf("Script.%s(%q): binding parameter %d (%s): %v", verb, text, param, slot.describe(), r))
		}
	}()
	w := a.fixImpl(slot.name)
	value, prove := slot.member.adopt(w)
	return &boundMember{value: value, term: w.Core(), carrier: slot.member.binder, prove: prove}
}

// conjunctTerms flattens a ∧-tree into its leaves, in order.
func conjunctTerms(t core.Term) []core.Term {
	if l, r, isConj := matchesAnd(t); isConj {
		return append(conjunctTerms(l), conjunctTerms(r)...)
	}
	return []core.Term{t}
}

var matchesAnd = ext.MatchesBinaryOp(ext.AND)

// bindSlot performs the one goal move a slot calls for and returns the
// value to pass in. The panics inside the Argument verbs are already
// specific; this wrapper adds which PARAMETER was being bound, which is
// the part the author needs to fix.
func bindSlot(verb, text string, i int, slot binderSlot, a *Argument) reflect.Value {
	defer func() {
		if r := recover(); r != nil {
			panic(fmt.Sprintf("Script.%s(%q): binding parameter %d (%s): %v",
				verb, text, i+1, slot.describe(), r))
		}
	}()
	switch slot.kind {
	case slotForAll:
		// The STATEMENT's binder name is the authoritative surface name
		// for the fixed variable (derive.go §"Surface names") — the
		// goal's own binder spelling may already be α-renamed by an
		// earlier slot's strip.
		w := a.fixImpl(slot.name)
		if slot.expr == nil && slot.vec == nil && slot.mat == nil && slot.mapping == nil {
			return reflect.ValueOf(w)
		}
		// A typed parameter: same goal move, same term — adopted at
		// the parameter's own instantiation through the descriptor's
		// checked constructor (the storage is sealed, so reflection
		// cannot construct an Expr; the descriptor carries the one
		// adoption gate as a closure). The phantom was checked against
		// the statement's binder at plan time; the constructor
		// re-checks the minted variable's actual type at bind time.
		if slot.vec != nil {
			return slot.vec.Anchor(w, a.dimensionLetter)
		}
		if slot.mat != nil {
			return slot.mat.Anchor(w, a.dimensionLetter)
		}
		if slot.mapping != nil {
			return slot.mapping.Anchor(w, a.dimensionLetter)
		}
		return slot.expr.Adopt(w)
	case slotImp:
		f := a.Assume()
		if slot.structure == nil {
			return reflect.ValueOf(f)
		}
		content, ok := f.BoundContent()
		if !ok {
			panic("the assumed structure fact carries no content")
		}
		a.checkStructureFact(*slot.structure, content)
		return slot.structure.adopt(f, content)
	case slotBundle:
		for _, name := range slot.names {
			a.fixImpl(name)
		}
		f := a.Assume()
		if slot.structure == nil {
			return reflect.ValueOf(f)
		}
		content, ok := f.BoundContent()
		if !ok {
			panic("the assumed structure fact carries no content")
		}
		a.checkStructureFact(*slot.structure, content)
		return slot.structure.adopt(f, content)
	}
	panic(fmt.Sprintf("unknown binder slot kind %d", slot.kind))
}

// ---------------------------------------------------------------------------
// Slots — what a statement offers to bind
// ---------------------------------------------------------------------------

type _SlotKind int

const (
	slotForAll _SlotKind = iota // a leading ∀ binder — consumed by a.Fix
	slotImp                     // a leading ⇒ antecedent — consumed by a.Assume
	// slotBundle is a run of ∀ binders and the ⇒-antecedent that closes
	// it, the antecedent mentioning every binder of the run — what a
	// bundle binder `∀S:comm_ring_on(B).` states (ext/dsl/bundle.go). One
	// Fact parameter binds it: the binders are fixed under their own
	// names, and the antecedent assumed.
	slotBundle
)

type binderSlot struct {
	kind _SlotKind
	// expr, when non-nil, is the closure parameter's TYPED wrapper
	// instantiation, described (ext.DescribeExprType): the parameter
	// asserted the binder's HOL type, planSectionBinding verified the
	// assertion against the statement, and bindSlot constructs the
	// typed value through the descriptor's checked constructor. nil
	// for the untyped spellings (Term, *TermWrapper).
	expr *ext.ExprDescriptor
	// vec, when non-nil, is the parameter's dimtypes.Vec instantiation:
	// the binder is fixed like a Term parameter and ANCHORED at the
	// phantom's letters, each resolved to the binder of that name fixed
	// before it (vec.go). mat is the same for a dimtypes.Mat, whose two
	// phantoms contribute both letter sets, and mapping for a
	// dimtypes.VecFun, a map between two vector spaces.
	vec     *dimtypes.VecDescriptor
	mat     *dimtypes.MatDescriptor
	mapping *dimtypes.VecFunDescriptor
	// member, when non-nil, is the parameter's Member instantiation: the
	// binder is fixed like a typed term, and its evidence is the
	// membership the evidence slot after it assumes. structure is a typed
	// structure fact at a ⇒ slot: the antecedent is assumed and checked
	// against the structure's predicate and the carriers its phantoms name.
	member    *_MemberRuntimeInfo
	structure *_StructureFactRuntimeInfo
	// evidence, on a ⇒ slot no parameter binds, are the plan indices of
	// the members whose memberships it states.
	evidence []int
	name     string       // ∀-binder name (slotForAll only)
	typ      core.HolType // ∀-binder type (slotForAll only)
	ante     core.Term    // the antecedent (slotImp, slotBundle)
	// names are the run's binders, in order (slotBundle only).
	names []string
}

func (b binderSlot) describe() string {
	switch b.kind {
	case slotForAll:
		return fmt.Sprintf("∀%s:%s", b.name, ext.FormatType(b.typ))
	case slotImp:
		if b.ante != nil {
			return "the hypothesis " + ext.PrintTerm(b.ante)
		}
		return "⇒-antecedent"
	case slotBundle:
		return fmt.Sprintf("bundle ∀%s. %s ⇒", strings.Join(b.names, " "), ext.PrintTerm(b.ante))
	}
	return "?"
}

var matchesImply = ext.MatchesBinaryOp(ext.IMPLY)

// sectionSlots lists the statement's bindable slots, in parameter
// order, stopping once `max` are found: the conclusion's leading ∀/⇒
// chain.
func sectionSlots(g Prop, max int) []binderSlot {
	out := make([]binderSlot, 0, max)
	t := g.Conclusion()
	for len(out) < max {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			v := abs.Var()
			out = append(out, binderSlot{kind: slotForAll, name: string(v.Name()), typ: v.Type()})
			t = abs.Body()
			continue
		}
		if ante, concl, ok := matchesImply(t); ok {
			out = append(out, binderSlot{kind: slotImp, ante: ante})
			t = concl
			continue
		}
		break
	}
	return out
}

// ---------------------------------------------------------------------------
// The signature check
// ---------------------------------------------------------------------------

var (
	dedPtrType  = reflect.TypeFor[*Argument]()
	factType    = reflect.TypeFor[Fact]()
	termType    = reflect.TypeFor[core.Term]()
	wrapperType = reflect.TypeFor[*ext.TermWrapper]()
)

// paramWantsTerm reports whether a parameter type receives a bound
// term. Both spellings are legal: `Term` reads as mathematics and is
// all a body needs to pass the variable into At(…) / Cite(…);
// `*TermWrapper` is the spelling for a body that uses the variable as a
// RECEIVER (x.Apply(…), x.Eq(…)).
func paramWantsTerm(t reflect.Type) bool { return t == wrapperType || t == termType }

// earlierNumBinder reports whether one of the slots binds a num ∀-binder
// of the given name.
func earlierNumBinder(slots []binderSlot, name string) bool {
	for _, s := range slots {
		if s.kind == slotForAll && s.name == name && s.typ.Equals(ext.NumType) {
			return true
		}
	}
	return false
}

// SectionBinderNames returns the statement's leading ∀-binder names in
// slot order, with "" for each non-∀ slot. The param-name lint
// compares this against the closure's declared parameter names; it is
// exported so the check runs against the PARSED statement rather than
// against a second, textual reading of it.
func SectionBinderNames(g Prop, n int) []string {
	slots := sectionSlots(g, n)
	out := make([]string, len(slots))
	for i, s := range slots {
		if s.kind == slotForAll {
			out[i] = s.name
		}
	}
	return out
}

// =======================================================================
// Script.Skolemize — the named-Skolem strip sugar
// =======================================================================
//
// Script.Skolemize, the named-Skolem strip sugar.
//
// The corpus convention it replaces: a proof body that needs the frees
// StripQuant mints must declare them by their MINTED names —
// `Var("m_0", NumType)` for a binder spelled `m` — coupling the proof
// text to the tactic's subscript-freshening internals, and every file
// re-explains the convention ("Skolems from the ∀m n. prefix,
// declaration order == strip order"). Skolemize runs the SAME
// StripQuant ministep (tree-identical: converting a call site never
// re-records a pb) and hands back the minted frees keyed by the
// binder names the statement actually spells:
//
//	sk := ctx.Skolemize(goal, "m", "n")     // strips ∀m n. …
//	m0, n0 := sk[0], sk[1]                  // the minted m₀, n₀
//
// Types come off the binders — no type re-spelling at the site — and
// each free is registered in the Script's parse scope (Script.Var), so
// claim texts resolve the names without decl prefixes.

// Skolemize strips the current leaf's leading ∀-prefix (one StripQuant
// ministep) and returns the minted Skolem frees, one per requested
// binder name, in binder order.
//
// Contract, panicking loudly on each violation:
//   - the leaf's conclusion must be ∀-headed and names must list the
//     FULL prefix's binder names in order (the checked form of the
//     "declaration order == strip order" lore);
//   - every requested binder must actually occur in the body — a dead
//     binder's Skolem never appears among the frees, so it cannot be
//     resolved (declare it by hand in that rare case);
//   - the minted name must resolve unambiguously (binder name, or the
//     binder name plus a `_N` subscript, free after the strip and not
//     free before).
func (s *Script) Skolemize(node *GoalStackNode, names ...string) []*ext.TermWrapper {
	leaf := node.unsolvedLeaf(0)
	if leaf == nil {
		panic("Script.Skolemize: no unsolved leaves remaining" + closedLeafNote(node))
	}
	binders, _ := ext.DecomposesFORALL(leaf.Goal.Conclusion())
	if binders.Size() != len(names) {
		panic(fmt.Sprintf("Script.Skolemize: %d name(s) for a %d-binder ∀-prefix — "+
			"names must cover the full prefix in order", len(names), binders.Size()))
	}
	for i, name := range names {
		if got := string(binders.Ind(i).Name()); got != name {
			panic(fmt.Sprintf("Script.Skolemize: binder %d is %q, not %q — "+
				"names follow the statement's binder order", i, got, name))
		}
	}

	freeBefore := goalFreeNames(leaf.Goal)
	s.Do(node, StripQuant())
	after := node.unsolvedLeaf(0)
	if after == nil {
		panic("Script.Skolemize: StripQuant closed the section — nothing to return")
	}
	freeAfter := goalFreeNames(after.Goal)

	out := make([]*ext.TermWrapper, len(names))
	for i, name := range names {
		var minted core.VarTerm
		for _, v := range freeAfter {
			if !SkolemNameOf(string(v.Name()), name) {
				continue
			}
			if hasVar(freeBefore, v) {
				continue // already free before the strip — not this mint
			}
			if !minted.IsZero() && !minted.Equals(v) {
				panic(fmt.Sprintf("Script.Skolemize: binder %q resolves ambiguously "+
					"(%s and %s) — declare the Skolem by hand", name, minted.Name(), v.Name()))
			}
			minted = v
		}
		if minted.IsZero() {
			panic(fmt.Sprintf("Script.Skolemize: no minted free found for binder %q "+
				"(dead binder, or an unexpected freshening?) — declare the Skolem by hand", name))
		}
		out[i] = s.Var(string(minted.Name()), minted.Type())
	}
	return out
}

// goalFreeNames collects the free variables of a goal's conclusion and
// hypotheses (each occurrence once per (name, type) identity).
func goalFreeNames(p Prop) []core.VarTerm {
	var frees []core.VarTerm
	add := func(t core.Term) {
		for _, v := range t.Frees(nil) {
			if !hasVar(frees, v) {
				frees = append(frees, v)
			}
		}
	}
	add(p.Conclusion())
	for _, h := range p.Hyps() {
		add(h)
	}
	return frees
}

func hasVar(vs []core.VarTerm, v core.VarTerm) bool {
	for _, w := range vs {
		if w.Equals(v) {
			return true
		}
	}
	return false
}

// SkolemNameOf reports whether minted is the Skolem spelling of binder
// name: the name itself, or the name plus one `_N` digit suffix (the
// StripQuant subscript-freshening convention). Exported as the ONE
// authority on that convention — a surface that must recognize "the
// binder the statement spells m" in a live section (the carrier
// chapter's dimension-phantom gate) checks names through this, never
// through a convention of its own.
func SkolemNameOf(minted, name string) bool {
	if minted == name {
		return true
	}
	if len(minted) <= len(name)+1 || minted[:len(name)] != name || minted[len(name)] != '_' {
		return false
	}
	for _, r := range minted[len(name)+1:] {
		if r < '0' || r > '9' {
			return false
		}
	}
	return true
}
