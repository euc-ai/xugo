// readings_sharing.go — the readings' statements kept in shared nodes.
//
// The view derives its readings by instantiating a structure's laws at
// the components a chain of projections pins, so the same subterms and
// the same types recur across tens of thousands of statements, and
// each derivation builds its own copy of every node it instantiates.
// The view keeps each readable's statement and sequent rebuilt from
// one table instead: a node is keyed by its children's shared copies,
// so two subterms alike in every name, type, type variable and
// metatype are one node, and the view holds each distinct node once.
// The derivations themselves are untouched: the walk reads every law
// at the instance it derived, and shares only what the view keeps.

package registry

import (
	"fmt"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// _sharing is the table of the view's shared nodes, one for every
// root's walk, dropped once every root is walked, or with a view whose
// walk was cut. A type variable is
// never merged with another of its
// name: the type matcher tells such variables apart by pointer
// (prover/typematch), so a shared statement holds each one where its
// derivation put it. A metatype and a constant's meta are keyed by
// pointer for the same reason.
type _sharing struct {
	mu     sync.Mutex
	types  map[_typeKey]core.CompositeType
	lists  map[_typeList]*_typeList
	apps   map[[2]core.Term]core.AppliedTerm
	abss   map[_absKey]core.AbsTerm
	consts map[_constKey]core.ConstTerm
	vars   map[_varKey]core.VarTerm
	// termCopies and typeCopies map the nodes of the readable being
	// shared to their shared copies, since a derived statement shares
	// nodes within itself; they are made afresh for each readable.
	termCopies map[core.Term]core.Term
	typeCopies map[core.HolType]core.HolType
}

// _typeList is a list of shared types, itself shared, so that a
// composite type of any arity is keyed by one pointer to its subtypes.
type _typeList struct {
	init *_typeList
	last core.HolType
}

type _typeKey struct {
	meta core.MetaType
	subs *_typeList
}

type _absKey struct {
	v    core.VarTerm
	body core.Term
}

type _constKey struct {
	meta core.ConstTermMeta
	typ  core.HolType
}

type _varKey struct {
	name core.TermName
	typ  core.HolType
}

func newSharing() *_sharing {
	return &_sharing{
		types:  map[_typeKey]core.CompositeType{},
		lists:  map[_typeList]*_typeList{},
		apps:   map[[2]core.Term]core.AppliedTerm{},
		abss:   map[_absKey]core.AbsTerm{},
		consts: map[_constKey]core.ConstTerm{},
		vars:   map[_varKey]core.VarTerm{},
	}
}

// share rebuilds each readable's statement and sequent from the
// table's nodes, adding the nodes the table does not hold yet. A walk
// shares its root's readables at once: the walks run in parallel, and
// a lock taken per readable keeps their workers parking and waking.
func (s *_sharing) share(readables []Readable) {
	s.mu.Lock()
	defer s.mu.Unlock()
	for i := range readables {
		s.termCopies, s.typeCopies = map[core.Term]core.Term{}, map[core.HolType]core.HolType{}
		readables[i].Statement = s.prop(readables[i].Statement)
		readables[i].sequent = s.prop(readables[i].sequent)
	}
	s.termCopies, s.typeCopies = nil, nil
}

func (s *_sharing) prop(p core.Prop) core.Prop {
	hyps := p.Hyps()
	for i, h := range hyps {
		hyps[i] = s.term(h)
	}
	return prop.MakeProp(s.term(p.Conclusion()), hyps...)
}

// term is t's shared copy. A node whose children's copies are its own
// children becomes the copy itself; any other is rebuilt over them.
func (s *_sharing) term(t core.Term) core.Term {
	t = t.Core()
	if shared, ok := s.termCopies[t]; ok {
		return shared
	}
	var shared core.Term
	switch x := t.(type) {
	case core.AppliedTerm:
		fun, arg := s.term(x.Fun()), s.term(x.Arg())
		key := [2]core.Term{fun, arg}
		app, ok := s.apps[key]
		if !ok {
			app = x
			if fun != x.Fun() || arg != x.Arg() {
				app = core.Apply(fun, arg)
			}
			s.apps[key] = app
		}
		shared = app
	case core.AbsTerm:
		v, body := s.term(x.Var()).(core.VarTerm), s.term(x.Body())
		key := _absKey{v, body}
		abs, ok := s.abss[key]
		if !ok {
			abs = x
			if v != x.Var() || body != x.Body() {
				abs = core.Abs(v, body)
			}
			s.abss[key] = abs
		}
		shared = abs
	case core.ConstTerm:
		typ := s.typ(x.Type())
		key := _constKey{x.Meta(), typ}
		c, ok := s.consts[key]
		if !ok {
			c = x
			if typ != x.Type() {
				c = core.MakeConstTerm(x.Meta(), typ)
			}
			s.consts[key] = c
		}
		shared = c
	case core.VarTerm:
		// A de Bruijn variable is kept as derived: core.Var makes named
		// variables only.
		if x.DeBruijnIndex() != 0 {
			shared = x
			break
		}
		typ := s.typ(x.Type())
		key := _varKey{x.Name(), typ}
		v, ok := s.vars[key]
		if !ok {
			v = x
			if typ != x.Type() {
				v = core.Var(x.Name(), typ)
			}
			s.vars[key] = v
		}
		shared = v
	default:
		panic(fmt.Sprintf("registry: a readable's statement holds a %T", x))
	}
	s.termCopies[t] = shared
	return shared
}

// typ is t's shared copy: a type variable itself, a composite type the
// table's node of its metatype over its subtypes' copies.
func (s *_sharing) typ(t core.HolType) core.HolType {
	c, ok := t.(core.CompositeType)
	if !ok {
		return t
	}
	if shared, ok := s.typeCopies[t]; ok {
		return shared
	}
	subs := make([]core.HolType, c.Meta().Arity())
	same := true
	var list *_typeList
	for i := range subs {
		subs[i] = s.typ(c.SubType(i))
		same = same && subs[i] == c.SubType(i)
		list = s.list(list, subs[i])
	}
	key := _typeKey{c.Meta(), list}
	shared, ok := s.types[key]
	if !ok {
		shared = c
		if !same {
			shared = core.MakeCompositeType(c.Meta(), subs...)
		}
		s.types[key] = shared
	}
	s.typeCopies[t] = shared
	return shared
}

// list is the shared list init followed by last.
func (s *_sharing) list(init *_typeList, last core.HolType) *_typeList {
	key := _typeList{init, last}
	if l, ok := s.lists[key]; ok {
		return l
	}
	l := &_typeList{init, last}
	s.lists[key] = l
	return l
}
