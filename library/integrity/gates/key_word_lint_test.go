package gates

import (
	"fmt"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
)

// keyWords are the words a key is spelled with, one before each kind of
// term and of type, and typeKeyMarks the marks that punctuate a type's
// key (TestKeyWordsAreTheOnesCoreSpells holds both to core).
var (
	keyWords     = []string{"type_", "var_", "const_", "apply_", "abs_"}
	typeKeyMarks = []string{":", "[", "]", "|"}
)

// NO NAME SPELLS A PIECE OF A KEY. A key is a name's own text between
// the key's words — var_x_type_bool — so a name holding one of those
// words can make two terms that are not α-equal spell one key: the
// variable p_type_boolvar_p reads as p ⊢ p run together, and a type
// constant var_A reads as the type variable A (core.TermKey). With no
// such name, a key is parsed back one way only, and two terms of the
// library share a key by a collision of the 64-bit hash and not
// otherwise.
//
// So no variable, constant, type constant or type variable of a
// member's statement, and no constant or type a definition mints, holds
// a key word; a type's name holds none of the marks of a type's key
// either. Nothing rests its soundness on this: whatever admits a
// statement compares statements, since a name is one string concatenation
// away for whoever writes Go. It keeps every table of keys in the engine
// exact for the names the library does use.
func TestLintNamesSpellNoKeyWord(t *testing.T) {
	installBundles()
	var findings []string
	hold := func(owner, kind, name string, pieces ...[]string) {
		for _, list := range pieces {
			for _, piece := range list {
				if strings.Contains(name, piece) {
					findings = append(findings, fmt.Sprintf("%s: the %s %q holds %q, a piece of a key", owner, kind, name, piece))
					return
				}
			}
		}
	}
	for _, e := range registry.All() {
		names := namesOf(t, e.Statement().Prop)
		for _, name := range names.variables {
			hold(e.Name, "variable", name, keyWords)
		}
		for _, name := range append(names.constants, e.Defines()...) {
			hold(e.Name, "constant", name, keyWords)
		}
		for _, name := range names.typeVariables {
			hold(e.Name, "type variable", name, keyWords, typeKeyMarks)
		}
		if minted := e.DefinesType(); minted != "" {
			names.typeConstants = append(names.typeConstants, minted)
		}
		for _, name := range names.typeConstants {
			hold(e.Name, "type constant", name, keyWords, typeKeyMarks)
		}
	}
	if len(findings) > 0 {
		sort.Strings(findings)
		t.Errorf("%d names spell a piece of a key (core.TermKey). Rename each:\n    %s",
			len(findings), strings.Join(findings, "\n    "))
	}
}

// _StatementNames is the names a statement spells, each once, in order
// of first occurrence.
type _StatementNames struct {
	variables, constants, typeVariables, typeConstants []string
}

// namesOf reads every name of p: its variables, bound and free, its
// constants, and the type variables and type constants of their types.
func namesOf(t *testing.T, p core.Prop) *_StatementNames {
	names := &_StatementNames{}
	seen := map[string]bool{}
	note := func(list *[]string, kind, name string) {
		if !seen[kind+name] {
			seen[kind+name] = true
			*list = append(*list, name)
		}
	}
	seenType := map[core.TypeKey]bool{}
	var walkType func(h core.HolType)
	walkType = func(h core.HolType) {
		if seenType[h.Key()] {
			return
		}
		seenType[h.Key()] = true
		switch h := h.(type) {
		case core.VarType:
			note(&names.typeVariables, "type variable ", string(h.Name()))
		case core.CompositeType:
			note(&names.typeConstants, "type constant ", string(h.Meta().Name()))
			for i := range h.Meta().Arity() {
				walkType(h.SubType(i))
			}
		default:
			t.Fatalf("a type of kind %T", h)
		}
	}
	seenTerm := map[core.Term]bool{}
	var walk func(x core.Term)
	walk = func(x core.Term) {
		if seenTerm[x] {
			return
		}
		seenTerm[x] = true
		if v, ok := x.AsVar(); ok {
			note(&names.variables, "variable ", string(v.Name()))
			walkType(v.Type())
		} else if c, ok := x.AsConst(); ok {
			note(&names.constants, "constant ", string(c.Name()))
			walkType(c.Type())
		} else if a, ok := x.AsAppliedTerm(); ok {
			walk(a.Fun())
			walk(a.Arg())
		} else if l, ok := x.AsAbsTerm(); ok {
			walk(l.Var())
			walk(l.Body())
		} else {
			t.Fatalf("a term of kind %T", x)
		}
	}
	walk(p.Conclusion())
	for h := range p.HypIter() {
		walk(h)
	}
	return names
}

// The lint's words are the ones core spells a key with: a key of each
// kind is read here, and a change to how core spells one fails this
// before the lint goes on guarding the old spelling.
func TestKeyWordsAreTheOnesCoreSpells(t *testing.T) {
	boolType := core.TypeBool()
	unary := core.MakeFun(boolType, boolType)
	x, f := core.Var("x", boolType), core.Var("f", unary)
	for _, c := range []struct{ kind, key, want string }{
		{"a type variable", string(core.MakeVarType("A").Key()), "type_var_A"},
		{"a type constant", string(boolType.Key()), "type_bool"},
		{"a type constant over types", string(unary.Key()), "type_fun:[type_bool|type_bool]"},
		{"a variable", string(x.AlphaKey()), "var_x_type_bool"},
		{"a constant", string(core.MakeConstTerm(core.MetaEq(), core.MakeFun(boolType, unary)).AlphaKey()),
			"const_=_type_fun:[type_bool|type_fun:[type_bool|type_bool]]"},
	} {
		if c.key != c.want {
			t.Errorf("core spells the key of %s as %s, and the lint reads it as %s", c.kind, c.key, c.want)
		}
	}
	for _, c := range []struct{ kind, key, word string }{
		{"an application", string(core.Apply(f, x).AlphaKey()), "apply_"},
		{"an abstraction", string(core.Abs(x, x).AlphaKey()), "abs_"},
	} {
		digits, ok := strings.CutPrefix(c.key, c.word)
		if !ok || strings.Trim(digits, "0123456789abcdef") != "" {
			t.Errorf("core spells the key of %s as %s, and the lint reads it as %s and a hash", c.kind, c.key, c.word)
		}
	}
	spelled := map[string]bool{"type_": true, "var_": true, "const_": true, "apply_": true, "abs_": true}
	for _, word := range keyWords {
		if !spelled[word] {
			t.Errorf("the lint refuses %q, which no key above is spelled with", word)
		}
		delete(spelled, word)
	}
	for word := range spelled {
		t.Errorf("the lint does not refuse %q, which a key above is spelled with", word)
	}
}
