package engine

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
)

// Spelling is the output door: how a goal, a hypothesis, a term or a
// statement the engine serves is spelled. The kernel printers
// (prop.PrintProp, ext.PrintTerm) print a term as the kernel holds it
// — `vec_norm(n, u)`, `vec_add(real_add, u, v)` — and stay that way;
// the door reads their text back through the chapter's spelling
// (dsl.ChapterSpelling, served as dsl.DisplaySpelling) under the
// instance bindings of the family the text is served for, so what is
// served is what the chapter writes: `‖u‖_n`, `u + v`, `Σ_{i<n} f(i)`.
// A session's door is its family's (Session.Spelling); a text derived
// from a registry entry — a rule its definition installs — goes
// through its family's (familySpelling); the nil door
// spells under no bindings — the notations the registry declares still
// fold, a structure's components stay spelled — which is what a session
// bound to no family serves. The parse-faithful text (Typed) is the
// same spelling checked to parse back to the statement at the family's
// statement door (StatementDoorScope); a display has no key, so there
// the spelling's own soundness is the check.
//
// A session's door also folds a term back into the abbreviations its
// goals were stated with (dsl.FoldAbbreviations): a subterm an entry
// names is displayed as «Name», as the member's statement spells it.
// The typed text is not folded — it is checked against a key at the
// statement door, which reads a text under no session's table.
//
// A member's own statement does not come through here: it has an
// authored text, and every door serves that one
// (registry.ProofEntry.StatementText); its typed text is Typed at its
// family's door, as a goal's is.
type Spelling struct {
	family        *registry.Family
	abbreviations *dsl.AbbreviationTable
}

// Spelling is the session's output door: its family's, no family's for
// a session bound to none, folding its goals' abbreviations.
func (s *Session) Spelling() *Spelling {
	if s == nil {
		return &Spelling{}
	}
	return &Spelling{family: s.family, abbreviations: s.abbreviationTable()}
}

// familySpelling is the door for a text derived from a registry
// entry: its family's.
func familySpelling(f *registry.Family) *Spelling {
	if f == nil {
		return nil
	}
	return &Spelling{family: f}
}

// boundFamily is the family the door spells for, nil for the door of
// no family.
func (sp *Spelling) boundFamily() *registry.Family {
	if sp == nil {
		return nil
	}
	return sp.family
}

// implicit is the family's instance bindings, the ones a display is
// read back under.
func (sp *Spelling) implicit() map[string]core.Term {
	if f := sp.boundFamily(); f != nil {
		return f.ImplicitBindings()
	}
	return nil
}

// Prop is a statement's display (prop.PrintProp) in the chapter's
// spelling, its abbreviations folded.
func (sp *Spelling) Prop(p core.Prop) string {
	return dsl.DisplaySpelling(prop.PrintProp(sp.foldProp(p)), constSyntax(), sp.implicit())
}

// Term is a term's display (ext.PrintTerm) in the chapter's spelling,
// its abbreviations folded.
func (sp *Spelling) Term(t core.Term) string {
	return dsl.DisplaySpelling(ext.PrintTerm(sp.fold(t)), constSyntax(), sp.implicit())
}

// Hyp is a hypothesis as a goal listing serves it — a polymorphic
// binder spelling its type letter (ext.PrintTermWithPolyBinders) — in
// the chapter's spelling, its abbreviations folded.
func (sp *Spelling) Hyp(t core.Term) string {
	return dsl.DisplaySpelling(ext.PrintTermWithPolyBinders(sp.fold(t)), constSyntax(), sp.implicit())
}

// Typed is a statement's parse-faithful text in the chapter's
// spelling (FormatStatementTypedUnder): "" and false when the
// statement door of a session bound to the family reads no print of
// it back.
func (sp *Spelling) Typed(p core.Prop) (string, bool) {
	return FormatStatementTypedUnder(p, sp.boundFamily())
}

// foldProp is p with every part folded into the door's abbreviations.
func (sp *Spelling) foldProp(p core.Prop) core.Prop {
	if sp == nil || sp.abbreviations == nil || p == nil {
		return p
	}
	parts := append([]core.Term{p.Conclusion()}, p.Hyps()...)
	terms := sp.abbreviationTerms(dsl.StatementScopeVars(p), parts)
	if len(terms) == 0 {
		return p
	}
	hyps := make([]core.Term, 0, p.NumHyps())
	for i := range p.NumHyps() {
		hyps = append(hyps, dsl.FoldAbbreviations(p.Hyp(i), terms))
	}
	return prop.MakeProp(dsl.FoldAbbreviations(p.Conclusion(), terms), hyps...)
}

// fold is t folded into the door's abbreviations, the entries read
// over t's own free variables — a term the door prints on its own, a
// hypothesis or a witness, at any type.
func (sp *Spelling) fold(t core.Term) core.Term {
	if sp == nil || sp.abbreviations == nil || t == nil {
		return t
	}
	ctx := map[string]core.HolType{}
	for _, v := range t.Frees(nil) {
		ctx[string(v.Name())] = v.Type()
	}
	return dsl.FoldAbbreviations(t, sp.abbreviationTerms(ctx, []core.Term{t}))
}

// abbreviationTerms reads the door's entries as terms over the
// variables ctx types — the free variables of the terms printed, and a
// statement's own leading binders — the surface names their minted
// spellings stand for (surface_alias.go) resolved to the minted
// variables, so an entry written over the statement's `L` is the term
// over the goal's `L₀`. The constants the printed terms hold pin the
// entries' instances as a goal's do.
func (sp *Spelling) abbreviationTerms(ctx map[string]core.HolType, printed []core.Term) []dsl.AbbreviationTerm {
	substs := seedSurfaceAliases(ctx, termsSurfaceAliases(printed...))
	scope := &dsl.ParseScope{
		ConstResolver:      registryConstResolver,
		TypeResolver:       registryTypeResolver,
		Syntax:             constSyntax(),
		FreshenMetaLetters: true,
		ImplicitBindings:   sp.implicit(),
	}
	if f := sp.boundFamily(); f != nil {
		scope.CoerceDomain = f.CoerceDomain()
	}
	if cs := termsConstScope(printed...); cs != nil {
		scope.Consts, scope.ConstMetas = cs.Consts, cs.ConstMetas
	}
	terms := sp.abbreviations.Terms(ctx, scope)
	if len(substs) > 0 {
		for i := range terms {
			terms[i].Term = terms[i].Term.Substitute(substs...)
		}
	}
	return terms
}

// SessionSpelling is the output door of a live session, for the wire
// layer's texts that are not part of an engine view (a parse preview).
func (e *Engine) SessionSpelling(sessionID string) (*Spelling, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	return s.Spelling(), nil
}
