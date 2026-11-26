package dsl

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// The type vocabulary of a statement text.
//
// A type position names one of four things: a type variable (a single
// uppercase letter, or the `var:<name>` form), a type the engine itself
// mints (BuiltinTypeArity: bool, num, prod and the arithmetic
// carriers the parser dispatches on), a spelling the DSL defines (the
// alias below), or a type constructor some chapter minted — `list(A)`,
// `option(A)`, a datatype. The last kind is the corpus's vocabulary,
// not the DSL's: a ParseScope's TypeResolver answers for it (the
// process ConstMetaManager, where a type name is known exactly when a
// registered constant's type mentions it, at that constant's arity).
// Under a resolver an unknown name is an ERROR, never a fresh
// composite type — before this check `∀s:set(A). …` parsed to a type
// constructor named set with every downstream gate green, a statement
// about a phantom type. Without a resolver (bare tests, the emit
// round-trip probes) the check keeps only the DSL's own facts: the
// alias's arity and the built-in types' arities.

// typeAliasSet is the DSL's one type alias: `set(τ)` spells `τ → bool`.
// It is a spelling, not a type — resolveType lowers it, so keys,
// matching and the printers never see a type named set. A set and a
// predicate are one type in the logic; the alias lets an author say
// which one a binder is, and the applied-set check (setspelling.go)
// holds the author to it: a binder declared `set(τ)` is used with ∈,
// never applied.
const typeAliasSet = "set"

// TypeAliasArity reports whether name is a spelling the DSL defines —
// a name no chapter may mint a type under — and the arity it takes.
func TypeAliasArity(name string) (arity int, ok bool) {
	if name == typeAliasSet {
		return 1, true
	}
	return 0, false
}

// builtinTypes is every type the engine mints for itself, read off the
// metatypes so the table cannot drift from them: the logic's bool, num
// (ext's numeral encoding), prod (ext's pairs), and the arithmetic
// carriers this parser dispatches operators on.
var builtinTypes = func() map[string]int {
	out := map[string]int{}
	for _, m := range []core.MetaType{
		core.MetaTypeBool(), ext.NumMetaType, ext.MetaTypeProd,
		RealMetaType, IntMetaType, HrealMetaType, NaddMetaType,
	} {
		out[string(m.Name())] = m.Arity()
	}
	return out
}()

// BuiltinTypeArity reports whether name is a type the engine mints for
// itself, and its arity. Such a name is known in every process — with
// or without the chapters that state theorems about it.
func BuiltinTypeArity(name string) (arity int, ok bool) {
	arity, ok = builtinTypes[name]
	return arity, ok
}

// isTypeVarName: a single uppercase letter, or the `var:` form
// (multi-letter variables, and the lexer's Skolem `var:?N`).
func isTypeVarName(name string) bool {
	if strings.HasPrefix(name, "var:") {
		return true
	}
	return len(name) == 1 && name[0] >= 'A' && name[0] <= 'Z'
}

// checkTypeNames validates every named type node of a parse against
// the DSL's own vocabulary and, when resolver is non-nil, the corpus's.
func checkTypeNames(names []*astTypeNamed, resolver func(string) (int, bool)) []InputDiagnostic {
	var out []InputDiagnostic
	for _, n := range names {
		nargs := len(n.args)
		if nargs == 0 && isTypeVarName(n.name) {
			continue
		}
		if arity, ok := TypeAliasArity(n.name); ok {
			if nargs != arity {
				out = append(out, typeNameDiag(n, CodeArityMismatch,
					fmt.Sprintf("type %s takes %d argument, got %d", n.name, arity, nargs),
					"write set(τ) for the type of sets of τ"))
			}
			continue
		}
		if arity, ok := BuiltinTypeArity(n.name); ok {
			if nargs != arity {
				out = append(out, typeNameDiag(n, CodeArityMismatch,
					fmt.Sprintf("type %s takes %d argument(s), got %d", n.name, arity, nargs), ""))
			}
			continue
		}
		if resolver == nil {
			continue
		}
		arity, ok := resolver(n.name)
		if !ok {
			out = append(out, typeNameDiag(n, CodeUnknownType,
				fmt.Sprintf("unknown type %q: no registered constant's type mentions it", n.name),
				"spell a registered type (num, real, list(A), …), a type variable (A, B), or set(τ) for τ → bool"))
			continue
		}
		if arity != nargs {
			out = append(out, typeNameDiag(n, CodeArityMismatch,
				fmt.Sprintf("type %s takes %d argument(s), got %d", n.name, arity, nargs), ""))
		}
	}
	return out
}

func typeNameDiag(n *astTypeNamed, code, message, suggestion string) InputDiagnostic {
	return InputDiagnostic{Position: n.pos, Length: n.end - n.pos, Code: code, Message: message, Suggestion: suggestion}
}

func scopeTypeResolver(scope *ParseScope) func(string) (int, bool) {
	if scope == nil {
		return nil
	}
	return scope.TypeResolver
}

// typeText renders a surface type for a diagnostic: the author's
// spelling, alias included (`set(A)`, `A → set(B)`, `list(A)`).
func typeText(t astType) string {
	switch t := t.(type) {
	case *astTypeNamed:
		if len(t.args) == 0 {
			return t.name
		}
		parts := make([]string, len(t.args))
		for i, a := range t.args {
			parts[i] = typeText(a)
		}
		return t.name + "(" + strings.Join(parts, ", ") + ")"
	case *astTypeFun:
		dom := typeText(t.domain)
		if _, isFun := t.domain.(*astTypeFun); isFun {
			dom = "(" + dom + ")"
		}
		return dom + " → " + typeText(t.codomain)
	case *astTypeVar:
		return t.name
	}
	return "?"
}
