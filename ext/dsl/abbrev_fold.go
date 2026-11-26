// abbrev_fold.go — the printer's half of an abbreviation table: a term
// the engine prints for a reader folds its subterms back into the
// names the author gave them, so a goal, a hypothesis or a rendered
// claim spells «R» where the member's statement does.

package dsl

import (
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// AbbreviationTerm is one entry read as a term: the name, the term its
// text parses to under the scope the fold runs in, and the letters an
// instance of it may take another type at.
type AbbreviationTerm struct {
	Name string
	Term core.Term
	// Letters are the type letters the entry is written at that no
	// free variable of Term fixes: a use instantiates each
	// (abbreviation.go, instantiateLetters), and the fold reads an
	// instance at another type back with the use's tie.
	Letters []core.TypeName
}

// Terms reads the table's entries as terms under scope, the free
// names typed by ctx (a goal's free variables), in table order. An
// entry whose text does not read there — it spells a variable the
// term in hand does not carry, say — is left out: the fold then folds
// the others.
func (t *AbbreviationTable) Terms(ctx map[string]core.HolType, scope *ParseScope) []AbbreviationTerm {
	if t == nil {
		return nil
	}
	var with ParseScope
	if scope != nil {
		with = *scope
	}
	with.Abbreviations = t
	with.AbbreviationBinders = nil
	out := make([]AbbreviationTerm, 0, len(t.entries))
	for _, e := range t.entries {
		res := ParseTermTextInScope(e.Text, ctx, &with, nil)
		if len(res.Errors) > 0 || res.Term == nil {
			continue
		}
		frees := res.Term.Frees(nil)
		if slices.ContainsFunc(frees, func(v core.VarTerm) bool { _, known := ctx[string(v.Name())]; return !known }) {
			continue // a name the parse freshened: not a term of this scope
		}
		fixed := map[core.TypeName]bool{}
		for _, v := range frees {
			for _, tv := range v.Type().TypeVars() {
				fixed[tv.Name()] = true
			}
		}
		var letters []core.TypeName
		for _, letter := range e.letters {
			if !fixed[core.TypeName(letter)] {
				letters = append(letters, core.TypeName(letter))
			}
		}
		out = append(out, AbbreviationTerm{Name: e.Name, Term: res.Term, Letters: letters})
	}
	return out
}

// FoldAbbreviations replaces in term every subterm that is an entry's
// term — at the letters it is written at, or at others — by a variable
// spelled «Name», with the tie `⟨A:T⟩` of each letter it is read at
// another type, later entries first, so an entry built on an earlier
// one folds whole; and every instance of an entry whose term is a λ,
// the body at some arguments, by «Name» applied to them, tied at the
// letters its arguments do not fix: the application the expansion
// reduced (abbreviation.go, astApp.reduced), read back. The entries are
// read over the statement's variables (StatementScopeVars: its free
// variables and its leading binders), so a subterm under the
// statement's own ∀x that an entry over x names folds; a text that
// rebinds a name an entry spells under an inner binder never parsed
// (the expansion refuses the capture), so no inner binder's variable is
// an entry's. The result is for printing: the lexer reads «Name» back
// as the abbreviation, and the parse scope's table expands it.
//
// A fold is made only where it reads back as the subterm it replaces.
// An entry whose term is a λ, applied, reads as its body at the
// arguments, reduced; so a λ the term applies as written — the head of
// a redex, `(λx. f(x))(a)` — is not that entry's «Name» there, and
// keeps its spelling, its body folded as any subterm is.
func FoldAbbreviations(term core.Term, entries []AbbreviationTerm) core.Term {
	if term == nil || len(entries) == 0 {
		return term
	}
	// applied says t stands applied to an argument.
	var fold func(t core.Term, applied bool) core.Term
	fold = func(t core.Term, applied bool) core.Term {
		for i := len(entries) - 1; i >= 0; i-- {
			e := entries[i]
			_, lambda := e.Term.AsAbsTerm()
			if !(applied && lambda) {
				if σ, ok := typeInstance(e, t); ok {
					return core.Var(core.TermName(e.spelling(σ, nil)), t.Type())
				}
			}
			if at, args, σ, ok := abbreviationInstance(e, t); ok {
				written := peelLambda(e.Term).binders[:len(args)]
				folded := core.Term(core.Var(core.TermName(e.spelling(σ, written)), at.term.Type()))
				for _, arg := range args {
					folded = core.Apply(folded, fold(arg, false))
				}
				return folded
			}
		}
		switch x := t.(type) {
		case core.AppliedTerm:
			fun, arg := fold(x.Fun(), true), fold(x.Arg(), false)
			if fun == x.Fun() && arg == x.Arg() {
				return t
			}
			return core.Apply(fun, arg)
		case core.AbsTerm:
			body := fold(x.Body(), false)
			if body == x.Body() {
				return t
			}
			return core.Abs(x.Var(), body)
		}
		return t
	}
	return fold(term, false)
}

// spelling is «Name» with the tie of each of the entry's letters σ
// reads at another type and the written types of the given binders —
// the ones the use applies the entry to, whose arguments fix the
// letters they mention — do not mention: the text that reads back as
// the instance.
func (e AbbreviationTerm) spelling(σ []core.TypeSubst, applied []core.VarTerm) string {
	name := string(abbrevOpen) + e.Name + string(abbrevClose)
	fixed := map[core.TypeName]bool{}
	for _, b := range applied {
		for _, v := range b.Type().TypeVars() {
			fixed[v.Name()] = true
		}
	}
	var ties []string
	for _, letter := range e.Letters {
		for _, s := range σ {
			if s.VarType.Name() == letter && !fixed[letter] && !s.HolType.Equals(s.VarType) {
				ties = append(ties, string(letter)+":"+ext.FormatType(s.HolType))
			}
		}
	}
	if len(ties) == 0 {
		return name
	}
	return name + "⟨" + strings.Join(ties, ", ") + "⟩"
}

// typeInstance reads t as the entry's term at a type for each of its
// letters — the term itself, σ empty, or the term with σ — up to α.
func typeInstance(e AbbreviationTerm, t core.Term) ([]core.TypeSubst, bool) {
	if e.Term.AlphaEquals(t) {
		return nil, true
	}
	if len(e.Letters) == 0 {
		return nil, false
	}
	σ, ok := letterTypes(e, e.Term, t, nil)
	if !ok || len(σ) == 0 {
		return nil, false
	}
	return σ, e.Term.TypeSubstitute(σ...).AlphaEquals(t)
}

// letterTypes is the types the entry's letters take where pattern —
// the entry's term or its body — stands at t: the two walked in step,
// each variable's and constant's type matched, an application of one
// of holes (the λ's binders, which an argument fills) matched at its
// result alone. False where the shapes part or a letter would take two
// types.
func letterTypes(e AbbreviationTerm, pattern, t core.Term, holes []core.VarTerm) ([]core.TypeSubst, bool) {
	instantiable := func(v core.VarType) bool { return slices.Contains(e.Letters, v.Name()) }
	var σ []core.TypeSubst
	isHole := func(p core.Term) bool {
		head, _ := ext.MatchesApply(p)
		v, isVar := head.AsVar()
		return isVar && slices.ContainsFunc(holes, v.EqualsVar)
	}
	var walk func(p, q core.Term) bool
	walk = func(p, q core.Term) bool {
		if !core.MatchTypeInto(p.Type(), q.Type(), instantiable, &σ) {
			return false
		}
		switch x := p.Core().(type) {
		case core.VarTerm:
			if isHole(p) {
				return true
			}
			_, ok := q.AsVar()
			return ok
		case core.ConstTerm:
			c, ok := q.AsConst()
			return ok && x.Name() == c.Name()
		case core.AppliedTerm:
			// As written first; a hole's application the expansion
			// reduced is matched at its result alone.
			if app, ok := q.AsAppliedTerm(); ok {
				saved := slices.Clone(σ)
				if walk(x.Fun(), app.Fun()) && walk(x.Arg(), app.Arg()) {
					return true
				}
				σ = saved
			}
			return isHole(p)
		case core.AbsTerm:
			abs, ok := q.AsAbsTerm()
			return ok && core.MatchTypeInto(x.Var().Type(), abs.Var().Type(), instantiable, &σ) && walk(x.Body(), abs.Body())
		}
		return false
	}
	if !walk(pattern, t) {
		return nil, false
	}
	return slices.DeleteFunc(σ, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) }), true
}

// lambdaEntry is an entry's λ-term read at σ: the term, its binders
// and its body.
type lambdaEntry struct {
	term    core.Term
	binders []core.VarTerm
	body    core.Term
}

func peelLambda(term core.Term) lambdaEntry {
	at := lambdaEntry{term: term, body: term}
	for {
		abs, ok := at.body.AsAbsTerm()
		if !ok {
			return at
		}
		at.binders = append(at.binders, abs.Var())
		at.body = abs.Body()
	}
}

// abbreviationInstance reads t as an instance of an entry's λ-term
// `λx₁ … xₖ. body` — body with a term for each binder, reduced as the
// expansion reduces it (SubstituteReducing), at a type for each of the
// entry's letters — and returns the entry at those types, the terms in
// binder order and the types. The candidates are read off t at the
// binders' positions in body (instanceArguments) and the instance is
// checked by substitution: body at the candidates is t up to α, or t
// is no instance. A λ of no binders, a partial instance (fewer
// arguments than binders) and a term of another type are none.
func abbreviationInstance(e AbbreviationTerm, t core.Term) (lambdaEntry, []core.Term, []core.TypeSubst, bool) {
	at := peelLambda(e.Term)
	if len(at.binders) == 0 {
		return lambdaEntry{}, nil, nil, false
	}
	var σ []core.TypeSubst
	if !at.body.Type().Equals(t.Type()) || len(e.Letters) > 0 {
		var ok bool
		if σ, ok = letterTypes(e, at.body, t, at.binders); !ok {
			return lambdaEntry{}, nil, nil, false
		}
		if len(σ) > 0 {
			at = peelLambda(e.Term.TypeSubstitute(σ...))
		}
	}
	if !at.body.Type().Equals(t.Type()) {
		return lambdaEntry{}, nil, nil, false
	}
	args := make([]core.Term, len(at.binders))
	if !instanceArguments(at.body, t, at.binders, args) {
		return lambdaEntry{}, nil, nil, false
	}
	for _, a := range args {
		if a == nil {
			return lambdaEntry{}, nil, nil, false
		}
	}
	if !substituteAllReducing(at.body, at.binders, args).AlphaEquals(t) {
		return lambdaEntry{}, nil, nil, false
	}
	return at, args, σ, true
}

// instanceArguments walks pattern and t together and records, for each
// binder the pattern spells free, the subterm of t at its position —
// the same subterm at every position, up to α. Constants and the other
// variables must agree; an abstraction pairs its binder with t's and
// descends. A binder applied to distinct bound variables of the pattern,
// `g(i)`, stands where the expansion reduced its argument's body: its
// candidate is t's subterm abstracted over the variables t binds there.
// False where the shapes or the types part, so a candidate has its
// binder's type. A candidate is only a candidate: abbreviationInstance
// checks the instance by substitution.
func instanceArguments(pattern, t core.Term, binders []core.VarTerm, args []core.Term) bool {
	type pair struct{ p, t core.VarTerm }
	var bound []pair
	record := func(i int, q core.Term) bool {
		if args[i] == nil {
			args[i] = q
			return true
		}
		return args[i].AlphaEquals(q)
	}
	binderOf := func(x core.VarTerm) int {
		for i := len(bound) - 1; i >= 0; i-- {
			if bound[i].p.EqualsVar(x) {
				return -1
			}
		}
		for i, b := range binders {
			if b.EqualsVar(x) {
				return i
			}
		}
		return -1
	}
	// reducedApplication reads p = g(v₁, …, vₙ), g a binder and the vᵢ
	// distinct bound variables of the pattern, as the reduced redex q:
	// g's candidate is λw₁ … wₙ. q, the wᵢ the variables t binds there.
	reducedApplication := func(p, q core.Term) (bool, bool) {
		head, pargs := ext.MatchesApply(p)
		v, isVar := head.AsVar()
		if !isVar || len(pargs) == 0 {
			return false, false
		}
		i := binderOf(v)
		if i < 0 {
			return false, false
		}
		ws := make([]core.VarTerm, len(pargs))
		for k, a := range pargs {
			av, ok := a.AsVar()
			if !ok {
				return false, false
			}
			for j := len(bound) - 1; j >= 0; j-- {
				if bound[j].p.EqualsVar(av) {
					ws[k] = bound[j].t
					break
				}
			}
			if ws[k].IsZero() || slices.ContainsFunc(ws[:k], ws[k].EqualsVar) {
				return false, false
			}
		}
		cand := q
		for k := len(ws) - 1; k >= 0; k-- {
			cand = core.Abs(ws[k], cand)
		}
		if !cand.Type().Equals(binders[i].Type()) {
			return true, false
		}
		return true, record(i, cand)
	}
	var walk func(p, q core.Term) bool
	walk = func(p, q core.Term) bool {
		if !p.Type().Equals(q.Type()) {
			return false
		}
		switch x := p.Core().(type) {
		case core.VarTerm:
			for i := len(bound) - 1; i >= 0; i-- {
				if bound[i].p.EqualsVar(x) {
					v, ok := q.AsVar()
					return ok && v.EqualsVar(bound[i].t)
				}
			}
			if i := binderOf(x); i >= 0 {
				return record(i, q)
			}
			v, ok := q.AsVar()
			return ok && v.EqualsVar(x)
		case core.ConstTerm:
			c, ok := q.AsConst()
			return ok && x.Equals(c)
		case core.AppliedTerm:
			// The application as written first, so a binder the
			// argument filled with a name reads back as the name; a
			// reading that fails leaves no candidate behind.
			if app, ok := q.AsAppliedTerm(); ok {
				saved := slices.Clone(args)
				if walk(x.Fun(), app.Fun()) && walk(x.Arg(), app.Arg()) {
					return true
				}
				copy(args, saved)
			}
			read, ok := reducedApplication(p, q)
			return read && ok
		case core.AbsTerm:
			abs, ok := q.AsAbsTerm()
			if !ok {
				return false
			}
			bound = append(bound, pair{x.Var(), abs.Var()})
			defer func() { bound = bound[:len(bound)-1] }()
			return walk(x.Body(), abs.Body())
		}
		return false
	}
	return walk(pattern, t)
}

// StatementScopeVars is the variables a statement's abbreviations are
// read over, by name: the free variables of p, and the variables its
// conclusion's leading ∀-prefix binds — the statement's own binders,
// which its entries are written over.
func StatementScopeVars(p core.Prop) map[string]core.HolType {
	vars := map[string]core.HolType{}
	note := func(t core.Term) {
		for _, v := range t.Frees(nil) {
			vars[string(v.Name())] = v.Type()
		}
	}
	note(p.Conclusion())
	for _, h := range p.Hyps() {
		note(h)
	}
	for name, v := range leadingBinders(p) {
		if _, taken := vars[name]; !taken {
			vars[name] = v.Type()
		}
	}
	return vars
}

// StatementBinderNames is the names a statement's conclusion binds in its
// leading ∀-prefix — what a text printed of the statement binds as the
// statement's own (ParseScope.AbbreviationBinders), so the door that
// reads the print back exempts them from the capture check.
func StatementBinderNames(p core.Prop) map[string]bool {
	out := map[string]bool{}
	for name := range leadingBinders(p) {
		out[name] = true
	}
	return out
}

func leadingBinders(p core.Prop) map[string]core.VarTerm {
	out := map[string]core.VarTerm{}
	for body := p.Conclusion(); ; {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			return out
		}
		if _, taken := out[string(abs.Var().Name())]; !taken {
			out[string(abs.Var().Name())] = abs.Var()
		}
		body = abs.Body()
	}
}
