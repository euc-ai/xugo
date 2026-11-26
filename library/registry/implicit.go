// implicit.go — the family's side of implicit structure arguments:
// binding the names a chapter's derived operations read to the
// components of the instance the family works at.
//
// A structure law binds its explicit components, which may be record
// values. A family at an instance binds the same vocabulary through
// WithInstance: comm_ring_on(real_ring) binds R to real_ring and add,
// zero, neg, mul, one, sub and carrier to its normalized fields. The
// names come from the structure and record declarations, so a family
// does not restate concrete operations. The text DSL completes the
// arguments; this file supplies its bindings to every family Script.

package registry

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
)

// WithInstance binds the implicit binder names of s's components to
// the components of instance — a member of a carrier's chapter stating
// `<pred>(<concrete components>)` — so that this family's statements
// and claim texts may leave those components unspelled. Chained at
// declaration, like WithVocab:
//
//	var family = registry.NewFamily("vector/euclidean", familyCNF).
//		WithInstance(comm_ring.CommRingOn, real_ring.CommRing)
//
// The bindings are read from the instance entry's statement, which
// must be the predicate applied to one argument per component. A
// second instance of a DIFFERENT structure may be added by a further
// call; an explicit component name bound twice is an authoring error
// and panics. Record fields shared by several components retain their
// qualifiers and receive no unqualified alias.
func (f *Family) WithInstance(s StructureLike, instance EntryLike) *Family {
	structure := structureOf(s)
	if structure == nil || instance == nil {
		panic(fmt.Sprintf("registry.WithInstance(%s): the structure and its instance entry are both required", f.Name))
	}
	entry := instance.Entry()
	head, args := spineOf(entry.Statement().Prop.Conclusion())
	c, ok := head.AsConst()
	if !ok || string(c.Name()) != structure.Const || len(args) != len(structure.comps) {
		panic(fmt.Sprintf("registry.WithInstance(%s): %s does not state %s applied to its %d component(s): %s",
			f.Name, entry.Name, structure.Const, len(structure.comps), core.MakeProp(entry.Statement().Prop.Conclusion())))
	}
	if f.implicit == nil {
		f.implicit = map[string]core.Term{}
	}
	// Field aliases are derived from all resident records together. Two
	// endpoints can share their field names without making the instance
	// invalid; those aliases simply require a qualified record field.
	for name := range f.implicitFields {
		delete(f.implicit, name)
	}
	f.implicitFields = map[string]bool{}
	for i, comp := range structure.comps {
		if prev, dup := f.implicit[comp.name]; dup {
			panic(fmt.Sprintf("registry.WithInstance(%s): the name %s is already bound to %s",
				f.Name, comp.name, core.MakeProp(prev)))
		}
		f.implicit[comp.name] = args[i]
	}
	fields := map[string]core.Term{}
	counts := map[string]int{}
	normalize := RecordTermNormalizer()
	for _, recordTerm := range f.implicit {
		ct, isComposite := recordTerm.Type().(core.CompositeType)
		if !isComposite {
			continue
		}
		record := GetConstMetaManager().StructSyntax(string(ct.Meta().Name()))
		if record == nil {
			continue
		}
		for _, field := range record.Fields {
			meta := GetConstMetaManager().ConstMeta(field.Const)
			domain := ext.MatchesFun(meta.AbsType())[0]
			subst, fits := domain.Matches(recordTerm.Type(), func(core.VarType) bool { return true })
			if !fits {
				panic("registry.WithInstance: a field projection does not take its record")
			}
			term := core.Apply(core.MakeConstTerm(meta, meta.AbsType().Substitute(subst...)), recordTerm)
			counts[field.Name]++
			fields[field.Name] = normalize(term)
		}
	}
	for name, term := range fields {
		if counts[name] == 1 && f.implicit[name] == nil {
			f.implicit[name] = term
			f.implicitFields[name] = true
		}
	}
	return f
}

// spineOf splits an application spine into its head and arguments.
func spineOf(t core.Term) (head core.Term, args []core.Term) {
	for {
		app, ok := t.AsAppliedTerm()
		if !ok {
			break
		}
		args = append([]core.Term{app.Arg()}, args...)
		t = app.Fun()
	}
	return t, args
}

// ImplicitBindings returns the family's instance bindings for implicit
// structure arguments (name → component term), nil when it has none.
// The engine reads them for a session bound to the family, emit for
// the texts it renders into the chapter.
func (f *Family) ImplicitBindings() map[string]core.Term { return f.implicit }

// applyVocab installs the family's statement vocabulary on ctx: the
// vocab hook, the coercion domain a family without one declares on its
// handle, the instance bindings the completion pass reads, and the
// chapter's abbreviation table (WithAbbrev), under which a member's
// build installs its own (BuildSpec.installAbbreviations). Every
// Script the family hands out — a member's build script, the
// parse-only statement script, a lint's scope — goes through here.
func (f *Family) applyVocab(ctx *proof.Script) {
	if f.vocab != nil {
		f.vocab(ctx)
	}
	if f.coerce != nil {
		ctx.CoerceDomain(f.coerce)
	}
	if len(f.implicit) > 0 {
		ctx.ParseScope.ImplicitBindings = f.implicit
	}
	if f.abbrev != nil {
		ctx.UseAbbreviations(f.abbrev, nil)
	}
}
