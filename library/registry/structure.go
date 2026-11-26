// structure.go — family.DefineStructure / Structure.Law /
// Structure.Axiom / family.Instance: the form of a STRUCTURE,
// of the laws stated over it, and of its instances; and
// ProofEntry.Conjunct / ProofEntry.Law, the axiom's and the law's
// doors for a predicate definition that is not a structure.
//
// A structure is a predicate over explicit COMPONENTS — operations,
// distinguished elements, relations — on a free carrier, and the corpus
// already writes structures this way: iterate/monoidal's `monoidal_op(op)`
// with its laws `∀op. monoidal_op(op) ⇒ …`, its instance `monoidal_op(real_add)`
// proved once in a chapter of the carrier, and every consumer citing a law
// at the instance BARE (`By(monoidal.Union, real_ring.MonoidalAdd)` — the
// apply rung reads the components off the goal and the rest off the
// instance). This file names that shape and gives it a door, so a
// chapter that defines a structure states its laws without restating
// the components on every line:
//
// - the DEFINITION is a Define entry whose one direct equation applies
// the predicate to its components on the left —
// `∀op:(A → A → A). ∀e:A. comm_monoid(op, e) ⇔ C₁ ∧ … ∧ Cₙ`. The
// components and their types are read from it, once.
// - a LAW is a member stating `∀<components>. <pred>(<components>) ⇒
// <body>`; the author writes Law(body, proof) and the proof closure
// receives the structure hypothesis as a Fact — the components are
// in scope under their own names, so claim texts spell them.
// - an AXIOM is the law whose body is one conjunct of the definition,
// written Axiom(body): the definition is unfolded and the conjunct
// read off, so the structure's axioms are its first laws and every
// later proof cites them at the hypothesis like any other law.
// - an INSTANCE is an ordinary member of a chapter of the carrier stating
// `<pred>(<concrete components>)`, written Instance(S, stmt, cases…):
// the predicate unfolded, one Case per conjunct. A carrier builds its
// instances bottom-up — the monoid, then the group citing it, then
// the ring citing both — so each conjunct is the carrier's own law or
// the instance already in hand; a consumer holding only the ring's
// instance reaches a sub-structure's through the projection law
// (`By(comm_ring.AddGroupOn, CommRing)`). The instance graph is that set
// of named theorems — nothing is searched, and a consumer names the
// instance its law wants.
//
// A structure whose predicate a plain `Define` mints — the fold
// mechanism's `monoidal_op`, minted by iterate/monoidal's
// MonoidalOpDef — has no DefineStructure entry to read the components
// off: family.StructureOf names it from the predicate and the
// components as the author spells them (`"op:(B → B → B)"`), and its
// laws are stated through the same Law/Axiom door, with no
// structure-definition entry to declare.
//
// Law returns the BuildSpec Theorem returns, its statement assembled
// from the definition; the section is the ordinary binder-closure
// section. The author's closure either names the components itself,
// before the hypothesis — the plain Theorem closure for the statement,
// for a proof that builds at them — or receives only the hypothesis,
// in which case a closure fabricated here binds the component slots
// positionally and forwards the rest.

package registry

import (
	"fmt"
	"reflect"
	"sort"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
)

// structurePredicates records every structure a family defines or
// names (DefineStructure, StructureOf) under its predicate: the
// constants whose application to variables makes those variables a
// structure's components.
var structurePredicates sync.Map

// structureGeneration counts the structures recorded, so that the
// readings view, which reads which predicates are structures, is
// recomputed when one is added.
var structureGeneration atomic.Uint64

// recordStructure records s under its predicate.
func recordStructure(pred string, s *Structure) {
	structurePredicates.Store(pred, s)
	structureGeneration.Add(1)
	GetConstMetaManager().MarkStructurePredicate(core.TermName(pred))
}

// IsStructurePredicate reports whether name is a structure predicate
// some family defines or names.
func IsStructurePredicate(name string) bool {
	_, ok := structurePredicates.Load(name)
	return ok
}

// StructureByPredicate returns the structure a family defined or named
// over the predicate name. Its ProofEntry is the definition entry of a
// DefineStructure'd structure — whose Go var is the structure itself,
// in the typed wrapper the family generator renders for that entry —
// and nil for one StructureOf names.
func StructureByPredicate(name string) (*Structure, bool) {
	v, ok := structurePredicates.Load(name)
	if !ok {
		return nil, false
	}
	return v.(*Structure), true
}

// Structures lists the structures f defines (DefineStructure), in
// predicate order — what the family generator declares a structure
// phantom for. A structure StructureOf names has no definition entry
// and is not listed.
func (f *Family) Structures() []*Structure {
	var out []*Structure
	structurePredicates.Range(func(_, v any) bool {
		if s := v.(*Structure); s.family == f && s.ProofEntry != nil {
			out = append(out, s)
		}
		return true
	})
	sort.Slice(out, func(i, j int) bool { return out[i].Const < out[j].Const })
	return out
}

// Family is the family that defines or names the structure.
func (s *Structure) Family() *Family { return s.family }

// Structure is a defined structure predicate: its definition entry and
// what a law over it needs — the components, in the predicate's
// application order, each with the type spelling the definition gave it.
type Structure struct {
	// The definition entry (Definition == proof.DefinitionDirect), the
	// member a consumer cites to unfold the predicate. nil for a
	// structure StructureOf names: its predicate unfolds through its
	// plain Define, resolved at replay like any Define'd constant, and
	// no entry is cited for it.
	*ProofEntry
	// Const is the predicate's name.
	Const string

	family *Family
	comps  []structureComponent
	// wholeTypeView marks a predicate whose record's carrier field is
	// ignored: its laws apply to every value of the component type.
	wholeTypeView bool

	// lawBinders is what a law's statement opens with (lawPrefix): the
	// structure's bundle binder, or, for a predicate the bundle syntax
	// does not fold, its components bound one by one with lawHypothesis
	// the predicate at them. componentBinders and predicate are that
	// component form whichever the statement takes.
	lawOnce          sync.Once
	lawBinders       string
	lawHypothesis    string
	componentBinders string
	predicate        string

	// axioms are the entries its Axiom door built, in registration
	// order: the parts Parts reads at a fact.
	axioms []*ProofEntry
}

// IsWholeTypeView reports whether s has a record-based view at 𝕌.
// Such a predicate does not refine membership in its record's carrier.
func (s *Structure) IsWholeTypeView() bool { return s.wholeTypeView }

// DefinedConstant is the structure's predicate: a structure is a
// proof.Definition, opened by Unfold whether its own door defined the
// predicate or StructureOf names one a plain Define did.
func (s *Structure) DefinedConstant() core.ConstTermMeta {
	owner := s.Const
	if s.ProofEntry != nil {
		owner = s.ProofEntry.Name
	}
	return mintedConstant(owner, s.Const)
}

// StructureLike is a structure as a chapter's var holds it: the
// *Structure DefineStructure or StructureOf returns, or the typed
// wrapper the family generator puts around a DefineStructure'd one
// (`var Group = groupThm{family.DefineStructure(…)}`), which embeds
// the *Structure, so its laws, axioms and fields read through the var
// and its definition entry has the typed Inst / At / Cite every other
// entry has. The doors that take a structure as an argument —
// Instance, WithInstance, AtUniverse — take either.
type StructureLike interface{ structure() *Structure }

func (s *Structure) structure() *Structure { return s }

// structureOf is the structure s holds; nil for a nil s, or for a
// typed wrapper around a nil *Structure.
func structureOf(s StructureLike) *Structure {
	if s == nil {
		return nil
	}
	return s.structure()
}

// structureComponent is one component binder: its kernel name (`N_0`,
// the identifier a text's `N₀` reads as) and its type as the
// definition's Type field spelled it.
type structureComponent struct{ name, typeText string }

// spelled is the component's name as a text writes it, the printer's
// spelling of the kernel name: `N_0` is written `N₀`.
func (c structureComponent) spelled() string { return utils.FormatSubscript(c.name) }

// DefineStructure registers a structure definition: Define on e, plus the
// component reading. e must be the DIRECT shape — one equation whose
// left side applies the constant to distinct variables, and whose Type
// spells the components' types curried in that order, ending in bool.
// The family generator wraps the var in the definition entry's typed
// wrapper, as it wraps a family.Define var (StructureLike).
func (f *Family) DefineStructure(e DefEntry) *Structure {
	if len(e.Equations) != 1 || e.Measure != "" {
		panic(fmt.Sprintf("registry.DefineStructure(%s): a structure is ONE direct equation — "+
			"the predicate applied to its components on the left", e.Name))
	}
	entry, dd := f.define(e)
	if dd == nil {
		panic(fmt.Sprintf("registry.DefineStructure(%s): the equation is not the direct shape", e.Name))
	}
	types, err := componentTypeTexts(e.Type, len(dd.Args))
	if err != nil {
		panic(fmt.Sprintf("registry.DefineStructure(%s): %v", e.Name, err))
	}
	s := &Structure{ProofEntry: entry, Const: e.Const, family: f}
	recordStructure(e.Const, s)
	syntax, err := directBundleSyntax(dd, e.Subject)
	if err == nil && e.Letter != "" {
		err = declareLetter(syntax, e.Letter)
	}
	if err != nil {
		panic(fmt.Sprintf("registry.DefineStructure(%s): %v", e.Name, err))
	}
	GetConstMetaManager().SetBundleSyntax(core.TermName(e.Const), syntax)
	for i, v := range dd.Args {
		s.comps = append(s.comps, structureComponent{name: string(v.Name()), typeText: types[i]})
	}
	return s
}

// componentTypeTexts splits a curried arrow type text into its
// components' type spellings: n arguments and a bool result, split at
// the arrows outside parentheses.
func componentTypeTexts(typeText string, n int) ([]string, error) {
	var segs []string
	depth, start := 0, 0
	rs := []rune(typeText)
	for i, r := range rs {
		switch r {
		case '(':
			depth++
		case ')':
			depth--
		case '→':
			if depth == 0 {
				segs = append(segs, strings.TrimSpace(string(rs[start:i])))
				start = i + 1
			}
		}
	}
	segs = append(segs, strings.TrimSpace(string(rs[start:])))
	if len(segs) != n+1 || segs[n] != "bool" {
		return nil, fmt.Errorf("Type %q must spell %d component type(s) then bool, curried", typeText, n)
	}
	return segs[:n], nil
}

// StructureOf names a predicate defined by a plain equation — a
// `Define` entry rather than a DefineStructure one, such as the fold
// mechanism's `monoidal` — as a structure. Unfold of the structure
// opens the predicate at replay as it opens any Define'd constant;
// the door itself reads no equation, so the author spells the
// components as the definition binds them — `"op:(B → B → B)"`, name
// and type, in application order, the two facts DefineStructure reads
// from its DefEntry, a name read as the text DSL reads it (`N₀` is
// `N_0`) — and no structure-definition entry is declared as a dep. The
// predicate itself is vocabulary: the family's Vocab hook declares it,
// as it declares any constant a statement spells.
func (f *Family) StructureOf(pred string, components ...string) *Structure {
	if pred == "" || len(components) == 0 {
		panic("registry.StructureOf: the predicate and at least one component (name:type) are required")
	}
	s := &Structure{Const: pred, family: f}
	recordStructure(pred, s)
	seen := map[string]bool{}
	for _, c := range components {
		name, typeText, ok := strings.Cut(c, ":")
		name, typeText = dsl.IdentifierName(strings.TrimSpace(name)), strings.TrimSpace(typeText)
		if !ok || name == "" || typeText == "" || strings.ContainsAny(name, " ()→") {
			panic(fmt.Sprintf("registry.StructureOf(%s): component %q is not name:type", pred, c))
		}
		if seen[name] {
			panic(fmt.Sprintf("registry.StructureOf(%s): component %s is named twice", pred, name))
		}
		seen[name] = true
		s.comps = append(s.comps, structureComponent{name: name, typeText: typeText})
	}
	params := make([]dsl.BundleParam, len(s.comps))
	for i, c := range s.comps {
		t, err := dsl.ParseTypeText(c.typeText)
		if err != nil {
			panic(fmt.Sprintf("registry.StructureOf(%s): component %s: %v", pred, c.name, err))
		}
		params[i] = dsl.BundleParam{Name: c.name, Type: t}
	}
	syntax, err := structureBundleSyntax(pred, params, nil, "")
	if err != nil {
		panic(fmt.Sprintf("registry.StructureOf(%s): %v", pred, err))
	}
	GetConstMetaManager().SetBundleSyntax(core.TermName(pred), syntax)
	return s
}

// Statement returns the law statement for body in the standard form:
// the structure's bundle binder (`∀G:group_on(A).`, which binds the
// components under their own names and states the predicate at them),
// then body's binders, hypotheses and conclusion. body is a statement
// over the components in the standard form — a dsl.Statement in parts
// with its abbreviations where it has a premise, a string where it has
// none — and a body in any other form panics, dsl.StandardParts saying
// how to write it. A
// predicate the bundle syntax does not fold (a definition that is no
// structure, Conjunct's) binds its components one by one, in
// application order, and states the predicate at them as the first
// hypothesis.
func (s *Structure) Statement(body any) dsl.Statement {
	parts := s.bodyParts("Statement", body)
	binders, hypothesis := s.lawPrefix()
	stmt := dsl.Statement{
		Binders:    strings.TrimSpace(binders + " " + parts.Binders),
		Hypotheses: parts.Hypotheses,
		Conclusion: parts.Conclusion,
		Abbrev:     parts.Abbrev,
	}
	if hypothesis != "" {
		stmt.Hypotheses = append([]string{hypothesis}, parts.Hypotheses...)
	}
	return stmt
}

// bodyParts reads a law's body, a string or a dsl.Statement, in the
// standard form; anything else panics naming verb.
func (s *Structure) bodyParts(verb string, body any) dsl.Statement {
	var text string
	var parts dsl.Statement
	switch b := body.(type) {
	case string:
		text = b
	case dsl.Statement:
		parts = b
		var err error
		if text, err = b.Text(); err != nil {
			panic(fmt.Sprintf("registry.%s.%s: %v", s.Const, verb, err))
		}
	default:
		panic(fmt.Sprintf("registry.%s.%s: the body is a string or a Statement, not %T", s.Const, verb, body))
	}
	split, err := dsl.StandardParts(text)
	if err != nil {
		panic(fmt.Sprintf("registry.%s.%s: the body %v", s.Const, verb, err))
	}
	if _, isParts := body.(dsl.Statement); isParts {
		return parts
	}
	return split
}

// lawPrefix is what a law's statement opens with: the structure's
// bundle binder, as the chapter spelling folds the components and the
// predicate at them; or, where nothing folds, the components bound one
// by one (adjacent ones of one type grouped) and the predicate at them.
func (s *Structure) lawPrefix() (binders, hypothesis string) {
	s.lawOnce.Do(func() {
		var b strings.Builder
		names := make([]string, len(s.comps))
		for i, c := range s.comps {
			names[i] = c.spelled()
		}
		for i := 0; i < len(s.comps); {
			j := i + 1
			for j < len(s.comps) && s.comps[j].typeText == s.comps[i].typeText {
				j++
			}
			fmt.Fprintf(&b, "∀%s:%s. ", strings.Join(names[i:j], " "), s.comps[i].typeText)
			i = j
		}
		s.lawBinders = strings.TrimSpace(b.String())
		s.lawHypothesis = fmt.Sprintf("%s(%s)", s.Const, strings.Join(names, ", "))
		s.componentBinders, s.predicate = s.lawBinders, s.lawHypothesis
		if !IsStructurePredicate(s.Const) {
			return
		}
		spelled, err := dsl.ChapterSpelling(s.lawBinders+" "+s.lawHypothesis+" ⇒ ⊤", GetConstMetaManager(), nil)
		if folded, ok := strings.CutSuffix(spelled, " ⊤"); err == nil && ok && !strings.Contains(folded, "⇒") {
			s.lawBinders, s.lawHypothesis = folded, ""
		}
	})
	return s.lawBinders, s.lawHypothesis
}

// Law returns the Build of a member stating one law of the structure —
// Statement(body) — proved by proof, which is either a closure
// `func(a *Argument, h Fact, …)` receiving the structure hypothesis
// and then, optionally, the body's own leading ∀-binders as Term /
// *TermWrapper / typed parameters (the section boundary's rule, in the
// body's binder order), or one Action run with the hypothesis resident:
//
//	var RightIdentity = family.Add(registry.ProofEntry{
//	 Name: "RightIdentity", Key: "…",
//	 Build: CommMonoid.Law("∀x:A. op(x, e) = x",
//	 func(a *Argument, monoid Fact) {
//	 a.Show("commute the left identity", By(Comm, LeftIdentity, monoid))
//	 }),
//	})
//
//	Build: AbelianGroup.Law("∀x y z:A. add(x, y) = add(x, z) ⇔ y = z",
//	 func(a *Argument, group Fact, x, y, z Term) { a.Iff(…) }),
//
// The components are bound to their own names before the closure runs,
// so claim texts inside it spell `op(x, e)` as the statement does. A
// proof that BUILDS at a component — grounds a cite at the operation,
// applies it inside a λ — names the components itself, typed, before
// the hypothesis, in application order; that closure is the statement's
// plain Theorem closure and is bound as one:
//
//	Build: Monoidal.Law("∀f:(A → B). ∀x:A. iterated_op(op, insert(x, empty_set), f) = f(x)",
//	 func(a *Argument, op *Arrow2[B, B, B], mon Fact, f *Arrow[A, B], x *Expr[A]) {
//	 … By(mon, oneStep, At(MonoidalAC, op)) …
//	 }),
func (s *Structure) Law(body any, proof any) BuildSpec {
	spec := s.family.Theorem(s.Statement(body), s.bindHypothesis("Law", body, proof))
	// A law depends on the definition it states the components of: the
	// dependency is the constructor's to declare, once. A structure
	// StructureOf names has no such entry.
	if s.ProofEntry != nil {
		spec.Deps = []EntryLike{s.ProofEntry}
	}
	return spec
}

// Axiom returns the Build of the law whose body is one conjunct of the
// definition. Its proof is the predicate unfolded at the hypothesis:
// the conjunct is then resident, and the goal — the conjunct at the
// section's own terms, every binder fixed and every other hypothesis
// assumed — closes as its instance (unfoldedConjunct). The structure's
// axioms are its first laws; every later law cites them at the
// hypothesis.
func (s *Structure) Axiom(body any) BuildSpec {
	spec := s.Law(body, unfoldedConjunct(s))
	spec.axiomOf = s
	return spec
}

// Intro is the step that proves the structure's predicate at the goal's
// components from its parts: the goal alone opened by the definition,
// Simp(Fwd(<definition>)) — no resident hypothesis is rewritten, so a
// handle on a resident structure fact survives, where Unfold would open
// it too — then either one Case per conjunct of the definition, in its
// order, as an instance proves them (family.Instance), or the actions
// given, run on the opened conjunction as a whole:
//
//	real_closed_field.RealClosedField.Intro(
//		Case("the order orders the copy", By(ordered)),
//		Case("a sign change has a root between", Derive(…)))
//	first_order.QuantifierFreeEquivalent.Intro(
//		Simp(Fwd(WellFormedDef), …),
//		By(Normalized, first_order.QuantifierFreeEquivalent.Parts(equivalent)))
//
// A structure StructureOf names has no definition entry to open the goal
// by, and Cases mixed with other steps are refused.
func (s *Structure) Intro(steps ...any) proof.Action {
	if s.ProofEntry == nil {
		panic(fmt.Sprintf("%s.Intro: the structure has no definition entry to open the goal by (StructureOf names it); Unfold of the structure opens %s", s.Const, s.Const))
	}
	var cases []proof.Case
	var actions []proof.Action
	for i, step := range steps {
		switch v := step.(type) {
		case proof.Case:
			cases = append(cases, v)
		case proof.Action:
			actions = append(actions, v)
		default:
			panic(fmt.Sprintf("%s.Intro: step %d is a %T; it takes one Case per conjunct of the definition, or actions on the opened goal", s.Const, i+1, step))
		}
	}
	open := proof.Simp(proof.Fwd(s.ProofEntry))
	switch {
	case len(cases) > 0 && len(actions) > 0:
		panic(fmt.Sprintf("%s.Intro: Cases and other steps mixed; give one Case per conjunct, or the actions that close the opened goal", s.Const))
	case len(cases) > 0:
		return proof.Chain(open, proof.SplitConjAll(cases...))
	}
	return proof.Chain(append([]proof.Action{open}, actions...)...)
}

// Parts is every axiom of the structure read at fact — a resident
// structure fact, a typed fact, an instance entry or a reading of one —
// as one premise group, which a By list takes in place of the readings
// one by one: `By(Normalized, QuantifierFreeEquivalent.Parts(eq))` for
// `By(Normalized, EquivalentWellFormed.Read(eq), …, EquivalentAgreement.Read(eq))`.
// The fact is read, never unfolded, so its handle survives.
func (s *Structure) Parts(fact any) proof.PremiseGroup {
	if len(s.axioms) == 0 {
		panic(fmt.Sprintf("%s.Parts: the structure states no axioms (Axiom) to read at the fact", s.Const))
	}
	readings := make([]any, len(s.axioms))
	for i, axiom := range s.axioms {
		readings[i] = proof.Read(axiom, fact)
	}
	return proof.GroupPremises(readings...)
}

// unfoldedConjunct is the proof of a law that is one conjunct of the
// predicate c's definition: c unfolded, which makes the conjunct
// resident and closes a goal that spells it as the definition does; a
// goal spelling it otherwise — its binders grouped another way, its
// hypotheses in another order — closes as its instance once opened
// (proof.ApplyResident).
func unfoldedConjunct(c proof.Definition) proof.Action {
	return proof.Chain(proof.Unfold(c), proof.CloseIfOpen(proof.ApplyResident()))
}

// definedPredicate is a direct definition's left side — the constant
// and the variables it is applied to — with the Type text that spells
// their types, recorded by Define for Conjunct and Law.
type definedPredicate struct {
	constName, typeText string
	args                []string
}

// predicateLaws reads a predicate DEFINITION that is not a structure as
// the components its laws are stated over: the left side's variables,
// each with the type the definition's Type spells for it. The view is
// not registered, so the predicate stays a plain definition. A
// structure's entry, and an entry that is not a direct predicate
// definition, panic naming verb.
func (e *ProofEntry) predicateLaws(verb, structureDoor string) *Structure {
	d := e.predicate
	if d == nil {
		panic(fmt.Sprintf("registry.%s(%s): not a direct definition — %s reads a Define entry's one equation", verb, e.Name, verb))
	}
	if IsStructurePredicate(d.constName) {
		panic(fmt.Sprintf("registry.%s(%s): %s is a structure — %s", verb, e.Name, d.constName, structureDoor))
	}
	types, err := componentTypeTexts(d.typeText, len(d.args))
	if err != nil {
		panic(fmt.Sprintf("registry.%s(%s): %v", verb, e.Name, err))
	}
	s := &Structure{ProofEntry: e, Const: d.constName, family: e.family}
	for i, name := range d.args {
		s.comps = append(s.comps, structureComponent{name: name, typeText: types[i]})
	}
	return s
}

// Conjunct returns the Build of the law whose body is one conjunct of a
// predicate DEFINITION that is not a structure — a Define entry whose one
// direct equation reads `∀x₁ … xₙ. p(x₁, …, xₙ) ⇔ C₁ ∧ … ∧ Cₖ` — stated
// `∀x₁ … xₙ. p(x₁, …, xₙ) ⇒ Cᵢ` and proved as a structure's axiom is:
// the predicate unfolded at the hypothesis, where the conjunct is then
// resident and the goal its instance. A subgroup is such a predicate — it reads a set against a
// group's operations — and its closure conditions are the laws a proof
// cites instead of unfolding the definition and picking a conjunct:
//
//	var SubgroupOne = family.Add(registry.ProofEntry{
//	 Name: "SubgroupOne", Key: "…",
//	 Build: SubgroupDef.Conjunct("one ∈ h"),
//	})
//
// The statement spells the left side's variables as the definition binds
// them, adjacent ones of one type grouped (Structure.Statement); the
// definition is the law's dep by construction. A body that is not one of
// the conjuncts fails at replay, where the unfolded hypothesis does not
// close it. A structure's conjunct is its Axiom, and an entry that is not
// a direct predicate definition has no conjuncts: both panic here.
func (e *ProofEntry) Conjunct(body any) BuildSpec {
	s := e.predicateLaws("Conjunct", "its conjuncts are its Axioms")
	return s.Law(body, unfoldedConjunct(s))
}

// Law returns the Build of any other law over a predicate definition that
// is not a structure: the statement Conjunct renders, `∀x₁ … xₙ. p(x₁, …,
// xₙ) ⇒ body`, proved by proof, which takes the forms Structure.Law takes
// — the hypothesis alone (then the body's leading binders), the
// components first, or one Action. A law read through a conjunct binds
// only the hypothesis the reading is taken at:
//
//	var SubmoduleZero = family.Add(registry.ProofEntry{
//	 Name: "SubmoduleZero", Key: "…",
//	 Build: SubmoduleDef.Entry().Law("M.zero ∈ N",
//	 func(a *Argument, sub Fact) {
//	 a.Show("…", By(group.SubgroupOne.Read(SubmoduleSubgroup.Read(sub))))
//	 }),
//	})
//
// The definition is the law's dep by construction. A structure's entry
// states its laws through the structure (Structure.Law shadows this
// method on a Structure), and an entry that is not a direct predicate
// definition has no components to state a law over: both panic here.
func (e *ProofEntry) Law(body any, proof any) BuildSpec {
	return e.predicateLaws("Law", "state its laws through the structure's own Law").Law(body, proof)
}

// Instance returns the Build of a member of THIS family (the carrier's
// chapter) stating that concrete components form the structure s:
// the predicate unfolded, then one Case per conjunct of the definition,
// in the definition's order, each closed from the carrier's own laws
// (or, for a sub-structure conjunct, from the instance already in hand):
//
//	var AddMonoid = family.Add(registry.ProofEntry{
//	 Name: "AddMonoid", Key: "…",
//	 Build: family.Instance(comm_monoid.CommMonoid, "comm_monoid(real_add, &0)",
//	 Case("addition commutes", Cite(real_construction.AddSym)),
//	 Case("addition associates", Cite(real_construction.AddAssoc)),
//	 Case("zero is a left identity", Cite(real_construction.AddLeftId))),
//	})
//
// A PARAMETRIC instance states the predicate under a ∀-prefix — the
// n-vectors at every dimension, the metric topology of every distance:
//
//	Build: family.Instance(metric_space.MetricSpace, "∀n:num. metric_space({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩)",
//	 Case("two n-vectors are at distance zero exactly when they are equal", …),
//	 …),
//
// The prefix is bound as the section's binders, under their own names,
// before the predicate is unfolded — the closure a Theorem would bind
// the same statement to, so a case body spells `n` and builds at it.
//
// The obligations are exactly the axioms — an instance that must prove
// more is a framework leak. The definition entry is declared as a dep
// by construction, as for a law.
func (f *Family) Instance(s StructureLike, statement string, cases ...proof.Case) BuildSpec {
	structure := structureOf(s)
	if structure == nil {
		panic(fmt.Sprintf("registry.Instance(%q): nil structure", statement))
	}
	if len(cases) == 0 {
		panic(fmt.Sprintf("registry.Instance(%s, %q): one Case per conjunct of the definition is required",
			structure.Const, statement))
	}
	binders, body := instancePrefix(statement)
	if !strings.HasPrefix(body, structure.Const+"(") {
		panic(fmt.Sprintf("registry.Instance(%s, %q): an instance statement applies the structure's predicate "+
			"to its concrete components, under a ∀-prefix or none", structure.Const, statement))
	}
	var proofBody any = proof.Chain(proof.Unfold(structure), proof.SplitConjAll(cases...))
	if binders > 0 {
		proofBody = parametricInstanceBody(binders, structure, cases)
	}
	spec := f.Theorem(statement, proofBody)
	if structure.ProofEntry != nil {
		spec.Deps = []EntryLike{structure.ProofEntry}
	}
	return spec
}

// instancePrefix splits an instance statement into the count of its
// leading ∀-binders and the body that follows them: `∀n:num.
// metric_space(…)` binds one, a group `∀x y:A.` two. A type annotation
// never contains the `.` that ends a group.
func instancePrefix(statement string) (binders int, body string) {
	body = strings.TrimSpace(statement)
	for strings.HasPrefix(body, "∀") {
		end := strings.Index(body, ".")
		if end < 0 {
			return binders, body
		}
		group := body[len("∀"):end]
		if at := strings.Index(group, ":"); at >= 0 {
			group = group[:at]
		}
		binders += len(strings.Fields(group))
		body = strings.TrimSpace(body[end+1:])
	}
	return binders, body
}

// parametricInstanceBody is the section closure a parametric instance
// binds its ∀-prefix to: one Term slot per binder, then the concrete
// instance's own body — the predicate unfolded, one Case per axiom.
func parametricInstanceBody(binders int, predicate proof.Definition, cases []proof.Case) any {
	in := make([]reflect.Type, 0, binders+1)
	in = append(in, structureArgType)
	for range binders {
		in = append(in, structureWrapperType)
	}
	return reflect.MakeFunc(reflect.FuncOf(in, nil, false), func(args []reflect.Value) []reflect.Value {
		a := args[0].Interface().(*proof.Argument)
		a.Do(proof.Unfold(predicate), proof.SplitConjAll(cases...))
		return nil
	}).Interface()
}

var (
	structureArgType     = reflect.TypeFor[*proof.Argument]()
	structureWrapperType = reflect.TypeFor[*ext.TermWrapper]()
)

// bindHypothesis turns the author's proof — a closure over the
// hypothesis (and, optionally, the body's leading binders), a closure
// naming the components before the hypothesis, or one Action — into
// the closure the section boundary binds (prover/proof,
// section_binding.go): the components, the predicate's fact right after
// them, then whatever the author's closure binds after the hypothesis. A
// closure that names the components is already that closure and passes
// through; so is a hypothesis-first closure where the statement opens
// with the bundle binder, whose fact parameter binds the components with
// the predicate. Otherwise the fabricated closure forwards the Argument,
// the hypothesis Fact and the trailing parameters; the component terms
// are bound under their own names by the boundary and need no parameter.
func (s *Structure) bindHypothesis(verb string, body any, authored any) any {
	n := len(s.comps)
	bad := func(got string) {
		panic(fmt.Sprintf("registry.%s(%s, %q): the proof must be func(a *Argument, h Fact, <the body's leading binders>…) — h may be the structure's typed fact — "+
			"func(a *Argument, <the %d component(s)>…, h Fact, …) or one Action; got %s", verb, s.Const, body, n, got))
	}
	_, hypothesis := s.lawPrefix()
	if act, ok := authored.(proof.Action); ok {
		authored = func(a *proof.Argument, _ proof.Fact) { a.Do(act) }
	}
	if authored == nil {
		bad("nil")
	}
	closureType := reflect.TypeOf(authored)
	if closureType.Kind() != reflect.Func || closureType.IsVariadic() || closureType.NumOut() != 0 ||
		closureType.NumIn() < 2 || closureType.In(0) != structureArgType {
		bad(closureType.String())
	}
	if !proof.IsStructureFactType(closureType.In(1)) {
		// The components-first form: the hypothesis sits after exactly
		// the component slots.
		if closureType.NumIn() < n+2 || !proof.IsStructureFactType(closureType.In(n+1)) {
			bad(closureType.String())
		}
		return s.markedPredicate(authored, n+1)
	}
	if hypothesis != "" {
		// The predicate is the statement's first hypothesis: the
		// hypothesis parameter binds the components with it, as the
		// bundle the section boundary reads there.
		return s.markedPredicate(authored, 1)
	}
	closure := reflect.ValueOf(authored)
	in := make([]reflect.Type, 0, n+closureType.NumIn())
	in = append(in, structureArgType)
	for range s.comps {
		in = append(in, structureWrapperType)
	}
	for i := 1; i < closureType.NumIn(); i++ {
		in = append(in, closureType.In(i))
	}
	fn := reflect.MakeFunc(reflect.FuncOf(in, nil, false), func(args []reflect.Value) []reflect.Value {
		forward := make([]reflect.Value, 0, closureType.NumIn())
		forward = append(forward, args[0])
		forward = append(forward, args[n+1:]...)
		closure.Call(forward)
		return nil
	})
	return s.markedPredicate(fn.Interface(), n+1)
}

// markedPredicate marks the hypothesis parameter of a law's closure —
// at param, counting from 1 after the Argument — as the fact of the
// structure's predicate where it is a plain Fact (proof.WithPredicate):
// it then binds the predicate's hypothesis, and not every hypothesis
// over the components. A typed fact names its predicate itself.
func (s *Structure) markedPredicate(closure any, param int) any {
	if reflect.TypeOf(closure).In(param) != reflect.TypeFor[proof.Fact]() {
		return closure
	}
	return proof.WithPredicate(closure, param, s.Const)
}

// UniverseView is a whole-type structure read as the view at 𝕌 of its
// CARRIER form — the structure on a set, one more component, the
// carrier, first, and every axiom guarded by membership in it. The
// bridge `S(comps) ⇔ S_on(𝕌, comps)` says the whole type is the carrier 𝕌,
// and a law of S is then the law of S_on read at c = 𝕌 with every
// guard discharged by a universe law — `∀x. x ∈ 𝕌` for a membership
// guard, `∀s. s ⊆ 𝕌` for an inclusion guard: one proof per law, on the
// carrier, and the whole-type member a view of it, stating the law
// unguarded at a key of its own.
type UniverseView struct {
	whole   *Structure
	carrier *Structure
	bridge  EntryLike // S(comps) ⇔ S_on(𝕌, comps)
	// recordAtUniverse replaces a record's carrier by 𝕌 while keeping
	// its operations. Empty for the separate-component form.
	recordAtUniverse string
	// universe is the laws that close a guard at 𝕌, each with the
	// relation glyph its statement puts before 𝕌: `∈` for `∀x. x ∈ 𝕌`,
	// `⊆` for `∀s. s ⊆ 𝕌`.
	universe []universeLaw
}

type universeLaw struct {
	law   EntryLike
	glyph string
}

// universeGlyphs are the relations a guard on the carrier is stated
// with, and so the relations a universe law may state against 𝕌.
var universeGlyphs = []string{"∈", "⊆"}

// AtUniverse declares s the view at 𝕌 of carrier: carrier's components
// are the carrier set followed by s's; bridge is the member stating
// `S(comps) ⇔ S_on(𝕌, comps)`; universe the members that close
// a guard at 𝕌, each stating one relation to 𝕌 — `∀x. x ∈ 𝕌` for the
// membership guards, `∀s. s ⊆ 𝕌` for the inclusion guards a law over
// subsets of the carrier carries. All are the chapter's to supply — the
// registry names no member of the corpus — and a view law depends on
// the ones its guards need.
//
//	var CommMonoidAtUniverse = CommMonoid.AtUniverse(CommMonoidOn, CommMonoidOnUniverse, set_basic.InUniv)
func (s *Structure) AtUniverse(carrier StructureLike, bridge EntryLike, universe ...EntryLike) *UniverseView {
	on := structureOf(carrier)
	if on == nil || bridge == nil || bridge.Entry() == nil || len(universe) == 0 {
		panic(fmt.Sprintf("registry.AtUniverse(%s): the carrier structure, the bridge member and at least one universe law are all required", s.Const))
	}
	if len(on.comps) != len(s.comps)+1 {
		panic(fmt.Sprintf("registry.AtUniverse(%s): %s has %d component(s), not %s's %d plus the carrier",
			s.Const, on.Const, len(on.comps), s.Const, len(s.comps)))
	}
	if !strings.HasPrefix(on.comps[0].typeText, "set(") {
		panic(fmt.Sprintf("registry.AtUniverse(%s): %s's first component %s:%s is not a set; the carrier comes first",
			s.Const, on.Const, on.comps[0].name, on.comps[0].typeText))
	}
	for i, c := range s.comps {
		if on.comps[i+1] != c {
			panic(fmt.Sprintf("registry.AtUniverse(%s): component %d of %s is %s:%s, not %s's %s:%s",
				s.Const, i+2, on.Const, on.comps[i+1].name, on.comps[i+1].typeText, s.Const, c.name, c.typeText))
		}
	}
	v := &UniverseView{whole: s, carrier: on, bridge: bridge}
	return v.withUniverseLaws(universe)
}

// AtUniverseRecord declares the same view for predicates of one record.
// The bridge states S(R) ⇔ S_on(recordAtUniverse), where the supplied
// record expression retains R's operations and has carrier 𝕌. Whole-type
// laws keep their unguarded interface; the view discharges the carrier
// law's membership and inclusion conditions with the supplied laws.
func (s *Structure) AtUniverseRecord(carrier StructureLike, bridge EntryLike, recordAtUniverse string, universe ...EntryLike) *UniverseView {
	on := structureOf(carrier)
	if on == nil || on == s || bridge == nil || bridge.Entry() == nil || len(universe) == 0 || strings.TrimSpace(recordAtUniverse) == "" {
		panic(fmt.Sprintf("registry.AtUniverseRecord(%s): distinct structures, a bridge, a whole-carrier record and universe laws are required", s.Const))
	}
	if len(s.comps) != 1 || len(on.comps) != 1 || s.comps[0] != on.comps[0] {
		panic(fmt.Sprintf("registry.AtUniverseRecord(%s): both predicates must bind the same record", s.Const))
	}
	typeName, _, _ := strings.Cut(s.comps[0].typeText, "(")
	record := GetConstMetaManager().StructSyntax(typeName)
	hasCarrier := false
	if record != nil {
		for _, field := range record.Fields {
			hasCarrier = hasCarrier || field.Name == "carrier"
		}
	}
	if !hasCarrier {
		panic(fmt.Sprintf("registry.AtUniverseRecord(%s): %s has no declared carrier field", s.Const, typeName))
	}
	v := &UniverseView{whole: s, carrier: on, bridge: bridge, recordAtUniverse: recordAtUniverse}
	v.withUniverseLaws(universe)
	s.wholeTypeView = true
	return v
}

func (v *UniverseView) withUniverseLaws(universe []EntryLike) *UniverseView {
	s := v.whole
	seen := map[string]bool{}
	for _, u := range universe {
		if u == nil || u.Entry() == nil {
			panic(fmt.Sprintf("registry.AtUniverse(%s): a nil universe law", s.Const))
		}
		headline := u.Entry().Build.Headline
		glyph := ""
		for _, g := range universeGlyphs {
			if strings.Contains(headline, g+" 𝕌") {
				glyph = g
			}
		}
		if glyph == "" {
			panic(fmt.Sprintf("registry.AtUniverse(%s): %s states no relation to 𝕌 (one of %s) — not a universe law: %q",
				s.Const, u.Entry().Name, strings.Join(universeGlyphs, " "), headline))
		}
		if seen[glyph] {
			panic(fmt.Sprintf("registry.AtUniverse(%s): two universe laws for %s 𝕌", s.Const, glyph))
		}
		seen[glyph] = true
		v.universe = append(v.universe, universeLaw{law: u, glyph: glyph})
	}
	return v
}

// Law returns the Build of the whole-type law whose body is body, as
// the view at 𝕌 of onLaw, the same law stated and proved on the
// carrier: `∀comps. S(comps) ⇒ body`, proved by one fixed argument —
// the carrier form at 𝕌 is had from the hypothesis through the bridge,
// and the carrier law read at that fact closes the body, each guard
// supplied by the universe law of its relation: a guard `x ∈ c` by the
// membership law, `h ⊆ c` by the inclusion law, read off the carrier
// law's statement (a law whose guards need a universe law the view was
// not declared with panics here, naming it). body is onLaw's body with
// its guards gone; a body that is not fails at replay, where the read
// law does not meet the goal.
//
//	var Assoc = family.Add(registry.ProofEntry{
//	 Name: "Assoc", Key: "…",
//	 Build: CommMonoidAtUniverse.Law("∀x y z:A. x * (y * z) = (x * y) * z", AssocOn),
//	})
//
// The deps are the constructor's: the carrier law, the bridge, the
// universe laws the guards need and the whole-type definition.
func (v *UniverseView) Law(body any, onLaw EntryLike) BuildSpec {
	if onLaw == nil || onLaw.Entry() == nil {
		panic(fmt.Sprintf("registry.%s.Law(%q): the carrier law is required", v.whole.Const, body))
	}
	names := make([]string, len(v.whole.comps))
	for i, c := range v.whole.comps {
		names[i] = c.spelled()
	}
	carrier := v.carrier.comps[0]
	onUniverse := fmt.Sprintf("%s(𝕌, %s)", v.carrier.Const, strings.Join(names, ", "))
	carrierName := carrier.name
	if v.recordAtUniverse != "" {
		onUniverse = fmt.Sprintf("%s(%s)", v.carrier.Const, v.recordAtUniverse)
		carrierName += ".carrier"
	}
	// The headline read as the text DSL reads it, so a carrier `c₀` is
	// found under its kernel name however the headline spells it.
	statement, _ := dsl.NormalizeTextSymbols(onLaw.Entry().Build.Headline)
	var guards []EntryLike
	for _, g := range universeGlyphs {
		if !strings.Contains(statement, g+" "+carrierName) {
			continue
		}
		found := false
		for _, u := range v.universe {
			if u.glyph == g {
				guards = append(guards, u.law)
				found = true
			}
		}
		if !found {
			panic(fmt.Sprintf("registry.%s.Law(%q): %s carries a guard `%s %s`, and the view was declared with no universe law for %s 𝕌",
				v.whole.Const, body, onLaw.Entry().Name, g, carrier.spelled(), g))
		}
	}
	spec := v.whole.Law(body, func(a *proof.Argument, h proof.Fact) {
		at := a.Have("the structure on the whole type is its carrier form at 𝕌", onUniverse, proof.By(h, v.bridge))
		if v.recordAtUniverse != "" {
			law := proof.Read(onLaw.Entry(), at)
			if len(guards) > 0 {
				rules := make([]proof.SimpRule, len(guards))
				for i, guard := range guards {
					rules[i] = proof.Fwd(guard.Entry())
				}
				law = a.Simplified(law, rules...)
			}
			a.Show("the carrier law at 𝕌 has no remaining carrier conditions", proof.By(law))
			return
		}
		premises := append([]any{onLaw, at}, toAny(guards)...)
		a.Show("the law on the carrier, read at 𝕌: every guard holds there", proof.By(premises...))
	})
	spec.Deps = append(append(spec.Deps, onLaw, v.bridge), guards...)
	return spec
}

func toAny(laws []EntryLike) []any {
	out := make([]any, len(laws))
	for i, l := range laws {
		out[i] = l
	}
	return out
}
