package core

import (
	"cmp"
	"fmt"
	"slices"
	"strings"
	"sync"
)

// definitions holds every name a definition has introduced in this
// process: a constant NewConstDef defined, a type NewTypeDef defined,
// and the two constants that type came with. It is what makes a
// definition conservative, on two counts.
//
// A name is defined once. A constant is identified by its name and a
// type by its name and arity, so a second definition under a name in
// use would be a second axiom about the one object, and the two
// together need not be consistent. The table keys a type by its name
// alone: two arities under one name are refused, though they would be
// two types. The kernel's own constants and types are in the table from
// the start, with nothing defining them.
//
// Definitions form no cycle. A constant or a type is made by hand under
// any name, so the term a definition is made from may mention the name
// it defines, or a name defined later whose own definition leads back:
// such a definition is an equation the name is to satisfy, and nothing
// need satisfy it. mentions and mentioned are the graph that is
// searched for the cycle.
var definitions = struct {
	mu     sync.Mutex
	consts map[TermName]ConstTermMeta
	types  map[TypeName]_TypeDefinition

	// mentions is, for each name a definition introduced, the names
	// the term it was defined from mentions. mentioned is the names
	// some such term mentions.
	mentions  map[_DefinedName][]_DefinedName
	mentioned map[_DefinedName]struct{}
}{
	consts: map[TermName]ConstTermMeta{
		metaEq.name:      metaEq,
		metaHilbert.name: metaHilbert,
	},
	types: map[TypeName]_TypeDefinition{
		metaTypeBool.name: {},
		metaTypeFun.name:  {},
	},
	mentions:  map[_DefinedName][]_DefinedName{},
	mentioned: map[_DefinedName]struct{}{},
}

// _TypeDefinition is what NewTypeDef returned for a type name. The zero
// value stands for a type of the kernel's own.
type _TypeDefinition struct {
	metaType MetaType
	abs, rep ConstTerm
}

// _DefinedName is the name of a constant or of a type. The two are
// named apart: a constant and a type may share a spelling.
type _DefinedName struct {
	name   string
	ofType bool
}

func constantNamed(n TermName) _DefinedName { return _DefinedName{name: string(n)} }

func typeNamed(n TypeName) _DefinedName { return _DefinedName{name: string(n), ofType: true} }

func (n _DefinedName) String() string {
	if n.ofType {
		return fmt.Sprintf("type %q", n.name)
	}
	return fmt.Sprintf("constant %q", n.name)
}

func (n _DefinedName) compare(m _DefinedName) int {
	if n.ofType != m.ofType {
		if m.ofType {
			return -1
		}
		return 1
	}
	return cmp.Compare(n.name, m.name)
}

// definedAs reports whether NewConstDef defined c as a term α-equal to
// t.
func (c ConstTermMeta) definedAs(t Term) bool {
	if c.def.IsZero() {
		return false
	}
	_, definiens, _ := MatchesEQ(c.def.Conclusion())
	return definiens.Type().Equals(t.Type()) && definiens.AlphaEquals(t)
}

// definedOn reports whether d is the type definition NewTypeDef made
// from source under the two constant names.
func (d _TypeDefinition) definedOn(source Prop, absName, repName TermName) bool {
	return !d.abs.IsZero() &&
		d.abs.meta.name == absName && d.rep.meta.name == repName &&
		d.abs.meta.defSource.AlphaEquals(source)
}

// refuseDefinedConst panics if a definition has introduced a constant
// named name, or the kernel has one of its own.
func refuseDefinedConst(door string, name TermName) {
	if _, ok := definitions.consts[name]; ok {
		panic(fmt.Sprintf(
			"%s: constant %q is already defined — a constant is identified by its name, "+
				"so a second definition would be a second axiom about it", door, name))
	}
}

// mentionsOf is the constants and the types t mentions, in order: every
// constant in it, and every type constructor in the type of a constant
// or a variable of it. What a closed term denotes depends on those and
// on nothing else.
func mentionsOf(t Term) []_DefinedName {
	found := map[_DefinedName]struct{}{}
	collectMentions(t, found, map[Term]struct{}{}, map[CompositeType]struct{}{})
	names := make([]_DefinedName, 0, len(found))
	for n := range found {
		names = append(names, n)
	}
	slices.SortFunc(names, _DefinedName.compare)
	return names
}

// collectMentions adds the names t mentions to found, over a shared
// DAG: terms and types hold the applied, abstraction and composite
// type nodes visited so far.
func collectMentions(t Term, found map[_DefinedName]struct{}, terms map[Term]struct{}, types map[CompositeType]struct{}) {
	switch t := t.(type) {
	case AppliedTerm:
		if _, seen := terms[t]; seen {
			return
		}
		terms[t] = struct{}{}
		collectMentions(t.fun, found, terms, types)
		collectMentions(t.arg, found, terms, types)
	case AbsTerm:
		if _, seen := terms[t]; seen {
			return
		}
		terms[t] = struct{}{}
		collectTypeMentions(t.v.holType, found, types)
		collectMentions(t.body, found, terms, types)
	case ConstTerm:
		found[constantNamed(t.meta.name)] = struct{}{}
		collectTypeMentions(t.holType, found, types)
	case VarTerm:
		collectTypeMentions(t.holType, found, types)
	default:
		panic(fmt.Sprintf("core: %T is no kernel term", t))
	}
}

func collectTypeMentions(t HolType, found map[_DefinedName]struct{}, types map[CompositeType]struct{}) {
	c, ok := t.(CompositeType)
	if !ok {
		return
	}
	if _, seen := types[c]; seen {
		return
	}
	types[c] = struct{}{}
	found[typeNamed(c.meta.name)] = struct{}{}
	for _, s := range c.subTypes {
		collectTypeMentions(s, found, types)
	}
}

// refuseDefinitionCycle panics if a definition introducing the names in
// introduced, made from a term mentioning mentions, would close a
// cycle: if the term mentions one of the names, or mentions a name
// whose definition leads to one.
func refuseDefinitionCycle(door string, mentions []_DefinedName, introduced ..._DefinedName) {
	for _, name := range introduced {
		path := definitionPath(mentions, name)
		if path == nil {
			continue
		}
		through := make([]string, len(path))
		for i, n := range path {
			through[i] = n.String()
		}
		panic(fmt.Sprintf(
			"%s: the definition of %s would close a cycle: it mentions %s — "+
				"a name defined through itself is an equation it is to satisfy, and nothing need satisfy it",
			door, name, strings.Join(through, ", whose definition mentions ")))
	}
}

// recordDefinition enters a definition into the graph: each name in
// introduced is defined from a term mentioning mentions.
func recordDefinition(mentions []_DefinedName, introduced ..._DefinedName) {
	for _, name := range introduced {
		definitions.mentions[name] = mentions
	}
	for _, name := range mentions {
		definitions.mentioned[name] = struct{}{}
	}
}

// definitionPath is a chain of names from one of from to target, each
// mentioned by the definition of the one before it, or nil if there is
// none. A name no definition mentions is reached from nowhere but the
// term itself.
func definitionPath(from []_DefinedName, target _DefinedName) []_DefinedName {
	if _, direct := slices.BinarySearchFunc(from, target, _DefinedName.compare); direct {
		return []_DefinedName{target}
	}
	if _, ok := definitions.mentioned[target]; !ok {
		return nil
	}
	visited := map[_DefinedName]struct{}{}
	parent := map[_DefinedName]_DefinedName{}
	stack := slices.Clone(from)
	for _, name := range from {
		visited[name] = struct{}{}
	}
	for len(stack) > 0 {
		name := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if name == target {
			path := []_DefinedName{name}
			for {
				before, ok := parent[path[0]]
				if !ok {
					return path
				}
				path = slices.Insert(path, 0, before)
			}
		}
		for _, next := range definitions.mentions[name] {
			if _, seen := visited[next]; !seen {
				visited[next] = struct{}{}
				parent[next] = name
				stack = append(stack, next)
			}
		}
	}
	return nil
}
