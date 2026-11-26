// build.go — Build-constructor helpers for the corpus's
// dominant proof shapes.
//
// Layer rationale: a single-section member written out by hand carries
// a ~30-line ceremony (a proof struct, dep claiming, a Build function)
// around ~25 lines of mathematics. The ceremony is CURATED-FRAMEWORK
// contract, not Script API: the entry-armed Script (NewScriptForEntry
// reads the identity the replay harness placed in env.Scope) and the
// (Thm, *Proof) return ARE the ProofEntry.Build contract — which is why
// the helper lives here, in the package that defines that contract, and
// not in prover.

package registry

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// BuildFunc is the proof-building half of the ProofEntry.Build contract.
type BuildFunc = func(*proof.ProverEnv) (proof.Thm, *proof.Proof)

// BuildSpec is the ProofEntry.Build payload: the build function plus —
// for the member shapes whose statement is a constructor argument — the
// member's HEADLINE, the checked statement literal the constructor
// parses as its section goal. Carrying it here is what lets the dep
// model serve a cited entry in the form its own file signs (the
// statement's binder order included), instead of a machine-recorded
// normal form; see ProofEntry.Statement.
//
// Members whose headline is not statically known (hand-written builds)
// carry only Fn — Bare wraps those.
type BuildSpec struct {
	Fn BuildFunc
	// Headline is the statement literal the member's constructor
	// (Theorem / Sections / Derived) parses, with the per-section const
	// overrides it parses under. Empty when the member shape does not
	// state its headline as a constructor argument. The one string is
	// held on one line (dsl.OneLine), as a text the chapter lays out over
	// lines reads; a statement written in parts (dsl.Statement) is
	// assembled into this text, and the parts stay in Statement.
	Headline       string
	HeadlineConsts []ext.Term
	// Statement is the member's statement as its author wrote it in
	// parts — binders, hypotheses, conclusion, abbreviations — for the
	// doors that render a member as written (emit, the index); nil for
	// a headline written as one string.
	Statement *dsl.Statement
	// abbrev is the member's abbreviation table as the member and its
	// build share it (memberAbbrev); nil for a Bare build.
	abbrev *memberAbbrev

	// Capabilities the constructor KNOWS the body needs, because the
	// constructor is what writes the body. Only Lifted sets this: it
	// emits the one `IntOfRealDerive` step, so it also knows the
	// `int_of_real:<source key>` token that step must declare — and it
	// reads that key off the source entry, so no proof file pastes the
	// hash by hand.
	//
	// Family.Add copies this onto the entry when the entry declares
	// none, and panics on a disagreement rather than silently choosing.
	Capabilities []string

	// Deps the constructor KNOWS the member has, because the constructor
	// wrote the statement or the body from them: a structure's Law and
	// Axiom depend on the structure's definition entry, whose equation
	// they state the components of and unfold. Family.Add merges these
	// into the entry's own Deps, so the dependency is declared once, by
	// the constructor that creates it, never per member.
	Deps []EntryLike

	// Card marks a member stated without a proof (Family.Card): Fn is
	// nil, Headline is the statement, and the member is served as an
	// axiom until its proof lands. Nil for every proved member.
	Card *CardSpec

	// axiomOf is the structure whose Axiom built this spec: the
	// registered entry is then one of its axioms (Structure.Parts).
	axiomOf *Structure

	// Postulate marks the corpus's one permanent axiom
	// (Family.Postulate): Fn is nil, Headline is the statement, and the
	// member is served as the axiom its Term builds. Nil for every other
	// member.
	Postulate *PostulateSpec
}

// CardSpec is what a card carries beyond its statement.
type CardSpec struct {
	// Note says why the member deserves to exist and what its proof
	// must establish — the brief its prover reads. Required.
	Note string
}

// PostulateSpec is what the postulate carries beyond its statement: the
// nullary type it introduces, and the axiom's term, built by the
// chapter with ext's Go constructors. The type is known to every
// statement from the postulate's registration on (ConstMetaManager.
// TypeArity). The statement text is the member's surface (its key, the
// index, the typed wrapper); the term is what the kernel is handed, and
// the mint panics unless the two are α-equal.
type PostulateSpec struct {
	Type string
	Term func() ext.Term
}

// Bare wraps a hand-written build function into a BuildSpec with no
// statically-known headline.
func Bare(fn BuildFunc) BuildSpec { return BuildSpec{Fn: fn} }

// memberAbbrev is a member's abbreviation table as the member and its
// build share it: own, the entries the author declared on the
// statement; merged, the table every text of the member reads — the
// chapter's (Family.WithAbbrev) with own under it, bound when the
// member registers (bindChapter), since a structure door builds a
// member's spec with the structure's family and the member registers
// in the chapter that states it; binders, the names the headline's
// leading ∀-prefix binds, which the entries are written over. One
// cell, pointed to: the constructor's build closure and the registered
// entry's copy of the spec read the one binding.
type memberAbbrev struct {
	own     dsl.Abbrev
	merged  *dsl.AbbreviationTable
	binders map[string]bool
}

// headlineSpec reads a constructor's statement argument — the one
// string, or a dsl.Statement written in parts — into the BuildSpec
// fields that carry it: the assembled text, the parts, the entries the
// parts declare and the leading binders. The table the member reads
// under is bound when it registers (bindChapter). Any other value
// panics naming the constructor: the statement is what a member IS,
// and it is written as text or as parts.
func headlineSpec(constructor string, statement any) BuildSpec {
	var spec BuildSpec
	switch s := statement.(type) {
	case string:
		spec = BuildSpec{Headline: dsl.OneLine(s), abbrev: &memberAbbrev{}}
	case dsl.Statement:
		spec = statementSpec(constructor, &s)
	case *dsl.Statement:
		if s == nil {
			panic(fmt.Sprintf("registry.%s: a nil *Statement — write the statement as a string or as a Statement literal", constructor))
		}
		spec = statementSpec(constructor, s)
	default:
		panic(fmt.Sprintf("registry.%s: the statement is a string or a Statement{Binders, Hypotheses, Conclusion, Abbrev}, not %T", constructor, statement))
	}
	spec.abbrev.binders = leadingBinderSet(spec.Headline)
	return spec
}

// statementSpec is headlineSpec for a statement written in parts.
func statementSpec(constructor string, s *dsl.Statement) BuildSpec {
	text, err := s.Text()
	if err != nil {
		panic(fmt.Sprintf("registry.%s: %v", constructor, err))
	}
	return BuildSpec{Headline: text, Statement: s, abbrev: &memberAbbrev{own: s.Abbrev}}
}

// bindChapter binds the member's table to the chapter it registers in:
// the chapter's table with the member's own entries under it, an entry
// of the member's spelling the chapter's, a name both declare refused
// — one name, one meaning. A Bare build has no table to bind.
func (b *BuildSpec) bindChapter(f *Family, member string) {
	if b.abbrev == nil {
		return
	}
	merged, err := f.AbbrevTable().Extend(b.abbrev.own)
	if err != nil {
		panic(fmt.Sprintf("proof registry: %s: %v", member, err))
	}
	b.abbrev.merged = merged
}

// installAbbreviations gives ctx the member's abbreviation table — the
// chapter's with the member's own under it — and leading binders, for
// every text the member's statement and proof spell. A member under no
// table installs none.
func (b *BuildSpec) installAbbreviations(ctx *proof.Script) {
	if b.abbrev == nil || b.abbrev.merged == nil {
		return
	}
	ctx.UseAbbreviations(b.abbrev.merged, b.abbrev.binders)
}

// Abbreviations is the table every text of the member reads: the
// chapter's entries, then the member's own; nil for a member under
// none, and before the member registers.
func (b *BuildSpec) Abbreviations() dsl.Abbrev {
	return b.AbbreviationTable().Entries()
}

// AbbreviationTable is the member's table parsed, the chapter's with
// the member's own under it; nil for a member under none, and before
// the member registers.
func (b *BuildSpec) AbbreviationTable() *dsl.AbbreviationTable {
	if b.abbrev == nil {
		return nil
	}
	return b.abbrev.merged
}

// Card returns a ProofEntry.Build for a member stated WITHOUT a proof:
// the statement in the family's vocabulary, exactly as Theorem reads
// its headline, and a note saying why it is a member and what its
// proof must establish. The member registers, is cited and retrieved
// like any other, and is served as the axiom `⊢ <statement>` — by the
// corpus seam (library/serve) in a session, by the replay harness as
// a trusted dep — until a proof lands: its Build becomes
// family.Theorem(<the same statement>, body), nothing else changes.
//
//	Build: family.Card(Statement{
//		Binders:    "∀m n:num.",
//		Hypotheses: []string{"m ∣ n", "n ∣ m"},
//		Conclusion: "m = n",
//	}, "antisymmetry of divisibility; each divides the other, so each is at most the other"),
//
// A card states a closed theorem: ∀-bound variables, ⇒ premises, no
// turnstile — the axiom minted for it is the statement itself. The
// corpus is sound relative to its cards; `xugo cards` lists them,
// leaves first, and a card's narrative Deps (the entries its proof is
// expected to cite) order that list without being replayed.
//
// The statement is written as every member's is: in parts — its
// binders, its hypotheses one per line, its conclusion, and the
// abbreviations its texts spell as «Name» (dsl.Statement) — where it
// has a premise, and as one string where it has none. A law of a
// structure is stated through the structure's door, its body written
// the same way:
//
//	Build: family.Card("∀m n:num. m ∣ n ⇔ ∃k:num. n = m * k", "…"),
//	Build: family.Card(IsTopology.Statement(Statement{
//		Binders:    "∀s:set(A).",
//		Hypotheses: []string{"connected_in(s)"},
//		Conclusion: "connected_in(closure(s))",
//	}), "…"),
func (f *Family) Card(statement any, note string, sectionConsts ...ext.Term) BuildSpec {
	spec := headlineSpec("Card", statement)
	spec.HeadlineConsts = sectionConsts
	spec.Card = &CardSpec{Note: note}
	return spec
}

// Postulate returns a ProofEntry.Build for the corpus's one permanent
// axiom: a new nullary type, and a statement about it assumed outright
// and never to be proved — the type of individuals and the axiom of
// infinity, which the construction of `num` rests on. Unlike a card it
// is no debt and no proof replaces it. The member registers, is cited
// and retrieved like any other, and is served as the axiom `⊢ <term>`
// by the corpus seam and the replay harness, exactly where a card is
// served as its statement.
//
//	Build: family.Postulate("ind", "∃f:(ind → ind). …", func() ext.Term { … }),
//
// The type is introduced by the postulate and by nothing else: no rule
// of the logic and no definition mentions it, so declaring it adds
// nothing, and the axiom is what gives it content. A definition that
// spells the type names the postulate in its Deps, which orders the
// two. The term is built in Go, from ext's constructors, so what the
// kernel trusts is assembled without the statement parser; the
// statement text is the member's surface, and the mint panics unless
// the term it builds is α-equal to the statement. The registry admits
// one postulate: a second panics at registration, naming the first.
func (f *Family) Postulate(typeName, statement string, term func() ext.Term) BuildSpec {
	spec := headlineSpec("Postulate", statement)
	spec.Postulate = &PostulateSpec{Type: typeName, Term: term}
	return spec
}

// Theorem returns a ProofEntry.Build for a single-section member whose
// body is a BINDER CLOSURE: the statement's leading ∀/⇒ binders flow
// into the closure's parameters (prover/proof/section.go), so the
// member reads as its statement and its mathematics with no ceremony
// in between — inline in the entry literal, metadata fields first,
// Build last (one declaration per entry):
//
//	Build: family.Theorem(
//	 "∀A B C:num. (∀n:num. A * n ≤ B * n + C) ⇔ A ≤ B",
//	 func(a *Argument, A, B, C Term) { … }),
//
// A member that closes in ONE action passes the Action itself as the
// body (Script.Theorem's one-action form):
//
//	Build: family.Theorem("∀s t:(A → bool). s ∪ t = t ∪ s", BySets()),
//
// The family is the receiver because the statement parses against the
// FAMILY's vocabulary (WithVocab): the consts and the standard free
// variables a chapter's statements are written in are chapter-level
// facts, not per-proof declarations.
//
// The variadic sectionConsts are Script.SectionText's per-section const
// overrides, for a statement that must read a non-default instance of
// an overloaded const (the polymorphic A/B-flavour case). Omit them
// unless the statement genuinely needs one.
//
// The statement is a string, or a Statement written in parts (as
// Card's doc shows); the parts assemble to one text, the hypotheses
// ∧-joined into the one antecedent the closure's Fact parameter
// binds, and the abbreviations the parts spell as «Name» are in scope
// for every claim and term text of the body.
func (f *Family) Theorem(statement any, body any, sectionConsts ...ext.Term) BuildSpec {
	spec := headlineSpec("Theorem", statement)
	spec.HeadlineConsts = sectionConsts
	spec.Fn = func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
		ctx := f.NewScript(env)
		spec.installAbbreviations(ctx)
		goal := ctx.Theorem(spec.Headline, body, sectionConsts...)
		return goal.PromisedThm(), &ctx.Proof
	}
	return spec
}

// Sections returns a ProofEntry.Build for a MULTI-section member. The
// HEADLINE — the statement the entry registers, and the form a citing
// consumer is served — is the constructor's first argument, exactly as
// in Theorem; the body receives it back as its second parameter and
// MUST open its top section with it:
//
//	Build: family.Sections(
//	 "∀P Q:(num → num). …",
//	 func(ctx *Script, headline string) *GoalStackNode {
//	 extend := ctx.Lemma("∀N B:num. …", func(a *Argument, N, B Term, h Fact) { … })
//	 return ctx.Theorem(headline, func(a *Argument, P, Q Term) {
//	 … Cite(extend) … // cross-section reference = closure capture
//	 })
//	 }),
//
// Hoisting the literal is what closes the machine-form dep gap: with
// the headline inside the closure the constructor could not see it, so
// the registry could not read it and consumers were served the machine-recorded
// (normalized, Skolem-prenex) form — a `∀P.…` member cited at
// `∀n.∀P.∃kʹ.…`, witness tuples included. The closure parameter keeps
// the statement stated ONCE, and the α-guard below makes a divergent
// top-section literal a loud authoring error rather than a silent
// served-vs-proved split.
//
// Bindings and section handles are Go locals in the one closure scope,
// shared across the proof natively — no per-proof struct.
//
// The headline is a string, or a Statement written in parts (as
// Card's doc shows); the body receives the assembled text, and the
// abbreviations the parts spell are in scope for every section of the
// body and every text of their proofs.
func (f *Family) Sections(headline any, body func(ctx *proof.Script, headline string) *proof.GoalStackNode, sectionConsts ...ext.Term) BuildSpec {
	spec := headlineSpec("Sections", headline)
	spec.HeadlineConsts = sectionConsts
	spec.Fn = func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
		ctx := f.NewScript(env)
		spec.installAbbreviations(ctx)
		top := body(ctx, spec.Headline)
		if top == nil {
			panic("registry.Sections: body returned no headline section — return the section whose theorem the entry registers")
		}
		if got, want := top.PromisedThm().AlphaKey(), ctx.MakePropText(spec.Headline, sectionConsts...).AlphaKey(); got != want {
			panic(fmt.Sprintf("registry.Sections: the returned top section does not prove the DECLARED headline — "+
				"open the top with the headline parameter (ctx.Theorem(headline, …)), not a divergent literal "+
				"(top %s, declared %s)", got, want))
		}
		return top.PromisedThm(), &ctx.Proof
	}
	return spec
}

// Derived is Sections for a member whose headline is not a section at
// all but a DERIVED theorem: the body returns the Thm a Script derive
// yields. Its one client is Lifted below, whose body is the ℝ-to-ℤ
// transport `ctx.IntOfRealDerive(…)`:
//
//	Build: family.Derived(headline,
//	 func(ctx *Script) Thm {
//	 return ctx.IntOfRealDerive(ctx.Dep(source), ctx.MakePropText(headline))
//	 }),
//
// A constant's defining theorem is not a client: a definition enters
// through the definition doors (Define, DefineSpec and their kin),
// which mint the constant and derive its characterizing statement in
// one step.
//
// The headline is the constructor's first argument exactly as in
// Theorem / Sections, and it is what the entry registers and a citing
// consumer is served. Unlike Sections, the body cannot open a section
// with it — the top's raw α-form is fixed by the derive (merged binder
// prefixes, the orientation it leaves an equation in), not authored —
// so the guard is a BRIDGE rather than an exact α-check: the
// constructor lifts the derived theorem into the headline's α-form via
// prop.BridgeNormalize, which is statement-level and so carries a
// promise through, and panics when the two are not
// normalize-equivalent. The registered theorem therefore IS the
// headline form: served form, built form, and the file's checked
// statement never diverge.
//
// Same closure-local shape as Sections, for the one member shape whose
// Build contract ends in a Thm rather than in a `*GoalStackNode`. The
// headline is a string, or a Statement written in parts (as Card's doc
// shows).
func (f *Family) Derived(headline any, body func(ctx *proof.Script) proof.Thm, sectionConsts ...ext.Term) BuildSpec {
	spec := headlineSpec("Derived", headline)
	spec.HeadlineConsts = sectionConsts
	text := spec.Headline
	spec.Fn = func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
		ctx := f.NewScript(env)
		spec.installAbbreviations(ctx)
		top := body(ctx)
		if top == nil {
			panic("registry.Derived: body returned no theorem — return the Thm the entry registers")
		}
		hp := ctx.MakePropText(text, sectionConsts...)
		lifted := prop.BridgeNormalize(hp, top)
		if lifted == nil {
			panic(fmt.Sprintf("registry.Derived: the DECLARED headline is not normalize-equivalent "+
				"to the derived theorem — fix the headline literal, never the derive\n  derived:  %s\n  declared: %s",
				prop.PrintProp(top), prop.PrintProp(hp)))
		}
		return core.AsThm(lifted), &ctx.Proof
	}
	return spec
}

// Lifted is Derived specialised to the transport members: a theorem
// whose whole proof is "this is its ℝ twin, carried across the
// embedding". ℤ is carved out of ℝ and every operation on it is defined
// by transport along real_of_int, so its ring, order and absolute-value
// laws are not re-proved — one `IntOfRealDerive` step each.
//
// The member is then pure data: a headline and a source. Spelling that
// data as a body was costing every such member four lines of identical
// ceremony PLUS a hand-pasted machine token, because the capability the
// step declares is the SOURCE's own key. Lifted closes both: it writes
// the body, and it reads the key off the source entry.
//
//	Build: family.Lifted(mulAssoc, real_construction.MulAssoc),
//
// The source must be a landed entry — Go initializes an
// imported package's vars first, so its Key is set by the time this
// runs. Every ℝ source a lift needs is a chapter member, so there is
// no form of this constructor for a source with no chapter member. The
// headline is a string, or a Statement written in parts, as Derived's.
func (f *Family) Lifted(headline any, sourceEntry EntryLike) BuildSpec {
	if sourceEntry == nil {
		panic("registry.Lifted: nil source — pass the entry this member lifts from")
	}
	source := sourceEntry.Entry()
	if source.Key == "" || strings.HasPrefix(source.Key, UnmintedKeyPrefix) {
		panic(fmt.Sprintf("registry.Lifted: source %q has no Key yet — a lift's capability IS the "+
			"source's own key, so the source entry must be initialized first (import order) "+
			"and must carry its Key in source", source.Name))
	}
	text := headlineSpec("Lifted", headline).Headline
	spec := f.Derived(headline, func(ctx *proof.Script) proof.Thm {
		return ctx.IntOfRealDerive(ctx.Dep(source), ctx.MakePropText(text))
	})
	spec.Capabilities = []string{proof.CapabilityIntOfReal + source.Key}
	return spec
}

// NewScript returns an entry-armed Script preloaded with the family's
// vocabulary. Exported for the rare member that needs the Script before
// its first section (a TypeDefExpand pair, a dep cert hoisted for reuse)
// and cannot use Theorem / Sections / Derived.
func (f *Family) NewScript(env *proof.ProverEnv) *proof.Script {
	ctx := proof.NewScriptForEntry(env)
	f.applyVocab(ctx)
	return ctx
}
