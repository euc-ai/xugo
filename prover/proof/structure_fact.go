package proof

// structure_fact.go — a structure fact typed by its structure and its carriers.
//
// A structure on a set is a predicate whose carriers are components:
// `group_on(G)` is on the set G.carrier, `module_on(R, M)` on the
// carriers of its two records. A fact of such a structure — the
// hypothesis a law's closure receives, a projection read at it — is a
// StructureFact: the Fact itself, typed by a STRUCTURE phantom S (one per
// structure, generated beside its definition, which names its
// predicate and the argument positions of its carriers) and by a
// CARRIER phantom per carrier (ext/on). The family generator aliases
// the instantiations under the structure's stem — `group.GroupFact[on.G]`
// is `StructureFact[<group_on's phantom>, on.G]`, a group fact on
// G.carrier — and
// a law of the structure
// read at it takes members of its carrier alone (member.go): reading a
// law of another structure at it, or grounding it at a point of
// another carrier, is a compile error.
//
// The typed surface is 1:1 with the untyped one. A StructureFact IS its Fact —
// every verb that takes a premise or an instance reads it through
// AsFact — and a law's typed Read builds exactly the reading
// proof.Read builds. What the types add is the check, and what the
// content adds (a door-bound or projection-derived fact knows what it
// says before the proof runs) is that a closure law read at it can name
// the point it concludes a member (ReadMember).
//
// An untyped value is an instance too, at AnyStructure and on.Any: a
// Fact, a handle, an instance entry, a reading of a law whose structure
// has no phantom. Instance and Instance2 are what a typed Read accepts,
// read off a value's InstanceOf / InstanceOf2 method by inference, so
// one Read serves the typed fact (its phantoms inferred) and every
// untyped instance (AnyStructure and on.Any inferred), and the laws'
// untyped call sites read on unchanged.

import (
	"fmt"
	"reflect"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
)

// StructurePhantom is the constraint of the structure phantoms: a
// zero-size Go type naming one structure's predicate and the argument
// positions of its carriers, in order. The family generator declares
// one per structure on a set, beside the structure's definition.
type StructurePhantom interface {
	Predicate() string
	Carriers() []int
}

// AnyStructure is the structure of an untyped instance: no predicate
// is asserted of it before the proof runs.
type AnyStructure struct{}

func (AnyStructure) Predicate() string { return "" }
func (AnyStructure) Carriers() []int   { return nil }

// Instance is what the typed Read of a law of a one-carrier structure
// accepts: a value whose InstanceOf names its structure and carrier.
type Instance[S StructurePhantom, Car on.Carrier] interface{ InstanceOf(S, Car) }

// Instance2 is Instance for a structure with two carriers.
type Instance2[S StructurePhantom, Car1, Car2 on.Carrier] interface {
	InstanceOf2(S, Car1, Car2)
}

// InstanceOf and InstanceOf2 make every Fact an untyped instance: its
// structure and carriers are not known before the proof runs.
func (Fact) InstanceOf(AnyStructure, on.Any)          {}
func (Fact) InstanceOf2(AnyStructure, on.Any, on.Any) {}

// InstanceOf and InstanceOf2 make a handle an untyped instance, as the
// resident fact it names is.
func (*HypHandle) InstanceOf(AnyStructure, on.Any)          {}
func (*HypHandle) InstanceOf2(AnyStructure, on.Any, on.Any) {}

// StructureFact is a fact of the one-carrier structure S, on the carrier Car.
// The Fact is a field, not embedded, as a reading's is: StructureFact is read
// through AsFact by every verb, and embedding would compile Fact's
// whole method set once per instantiation.
type StructureFact[S StructurePhantom, Car on.Carrier] struct {
	fact Fact
	// content is the fact's statement where it is known before the proof
	// runs — bound by the door, or derived from a known instance — and
	// nil otherwise.
	content core.Term
}

// AsFact is the Fact the structure fact is.
func (h StructureFact[S, Car]) AsFact() Fact { return h.fact }

// InstanceOf names the structure and carrier a typed Read infers.
func (StructureFact[S, Car]) InstanceOf(S, Car) {}

// structureContent is the fact's statement, where it is known.
func (h StructureFact[S, Car]) structureContent() (core.Term, bool) {
	return h.content, h.content != nil
}

// StructureFact2 is a fact of the two-carrier structure S, on Car1 and Car2.
type StructureFact2[S StructurePhantom, Car1, Car2 on.Carrier] struct {
	fact    Fact
	content core.Term
}

// AsFact is the Fact the structure fact is.
func (h StructureFact2[S, Car1, Car2]) AsFact() Fact { return h.fact }

// InstanceOf2 names the structure and carriers a typed Read infers.
func (StructureFact2[S, Car1, Car2]) InstanceOf2(S, Car1, Car2) {}

func (h StructureFact2[S, Car1, Car2]) structureContent() (core.Term, bool) {
	return h.content, h.content != nil
}

// _StructureContent is a typed structure fact's statement.
type _StructureContent interface{ structureContent() (core.Term, bool) }

// instanceContent is what an instance says, where that is known before
// the proof runs: a typed structure fact's content, a resident fact's
// bound content or the content it was named by, or a bare reading's
// statement at its own instance's content (readingInst.content).
func instanceContent(instance any) (core.Term, bool) {
	switch v := instance.(type) {
	case _StructureContent:
		return v.structureContent()
	case Fact:
		if content, bound := v.BoundContent(); bound {
			return content, true
		}
		if v.residentContent != nil {
			return contentHypTerm("Read", v.residentContent), true
		}
		if r, ok := v.target.(readingInst); ok && v.claim == nil && len(v.witnesses) == 0 && len(v.named) == 0 {
			return r.content()
		}
		return nil, false
	case *HypHandle:
		if v.term != nil {
			return v.term, true
		}
		return nil, false
	case CiteTarget:
		return instanceContent(v.AsFact())
	}
	return nil, false
}

// projectionContent is a projection law's conclusion read at an
// instance whose statement is known — the structure fact the reading
// states — and nil where the instance's statement is not known.
func projectionContent(stated core.Prop, instance any) core.Term {
	content, ok := instanceContent(instance)
	if !ok {
		return nil
	}
	read, err := readLawStatementAt(stated, core.Assume(content))
	if err != nil {
		panic("proof.ReadAs: " + err.Error())
	}
	return read.Conclusion()
}

// ReadAs is a projection law — `∀comps. S(comps) ⇒ S'(…)`, its body
// another structure's fact — read at an instance, typed as the
// structure fact it concludes. The first argument only names the
// result's type, as the generated wrapper spells it: the reading is
// proof.Read's, and its content the conclusion read at the instance's
// statement where that is known.
func ReadAs[S StructurePhantom, Car on.Carrier](_ StructureFact[S, Car], law NamedDep, stated core.Prop, instance any) StructureFact[S, Car] {
	return StructureFact[S, Car]{fact: Read(law, instance), content: projectionContent(stated, instance)}
}

// ReadAs2 is ReadAs for a conclusion of a two-carrier structure.
func ReadAs2[S StructurePhantom, Car1, Car2 on.Carrier](_ StructureFact2[S, Car1, Car2], law NamedDep, stated core.Prop, instance any) StructureFact2[S, Car1, Car2] {
	return StructureFact2[S, Car1, Car2]{fact: Read(law, instance), content: projectionContent(stated, instance)}
}

// ---------------------------------------------------------------------------
// The reflection bridge: a structure fact as a law closure's parameter
// ---------------------------------------------------------------------------

// _StructureFactRuntime is the sealed hook describeStructureFactType reads.
type _StructureFactRuntime interface {
	structureFactRuntimeInfo() _StructureFactRuntimeInfo
}

// _StructureFactRuntimeInfo is one StructureFact instantiation's capabilities: the
// predicate it asserts, the argument positions of its carriers and the
// binder each carrier phantom names, the Go type, and the constructor.
type _StructureFactRuntimeInfo struct {
	predicate string
	carriers  []int
	binders   []string
	goType    reflect.Type
	adopt     func(f Fact, content core.Term) reflect.Value
}

func (StructureFact[S, Car]) structureFactRuntimeInfo() _StructureFactRuntimeInfo {
	var s S
	var car Car
	return _StructureFactRuntimeInfo{
		predicate: s.Predicate(),
		carriers:  s.Carriers(),
		binders:   []string{car.Binder()},
		goType:    reflect.TypeFor[StructureFact[S, Car]](),
		adopt: func(f Fact, content core.Term) reflect.Value {
			return reflect.ValueOf(StructureFact[S, Car]{fact: f, content: content})
		},
	}
}

func (StructureFact2[S, Car1, Car2]) structureFactRuntimeInfo() _StructureFactRuntimeInfo {
	var s S
	var c1 Car1
	var c2 Car2
	return _StructureFactRuntimeInfo{
		predicate: s.Predicate(),
		carriers:  s.Carriers(),
		binders:   []string{c1.Binder(), c2.Binder()},
		goType:    reflect.TypeFor[StructureFact2[S, Car1, Car2]](),
		adopt: func(f Fact, content core.Term) reflect.Value {
			return reflect.ValueOf(StructureFact2[S, Car1, Car2]{fact: f, content: content})
		},
	}
}

// describeStructureFactType reports whether rt is StructureFact or StructureFact2 at some
// phantoms, and its capabilities.
func describeStructureFactType(rt reflect.Type) (_StructureFactRuntimeInfo, bool) {
	if rt == nil || rt.Kind() != reflect.Struct {
		return _StructureFactRuntimeInfo{}, false
	}
	probe, ok := reflect.New(rt).Elem().Interface().(_StructureFactRuntime)
	if !ok {
		return _StructureFactRuntimeInfo{}, false
	}
	info := probe.structureFactRuntimeInfo()
	if info.goType != rt {
		return _StructureFactRuntimeInfo{}, false
	}
	return info, true
}

// IsStructureFactType reports whether a closure parameter of type rt
// binds a structure fact: Fact, or a typed structure fact. The structure
// door reads a law's closure through it.
func IsStructureFactType(rt reflect.Type) bool {
	if rt == factType {
		return true
	}
	_, ok := describeStructureFactType(rt)
	return ok
}

// checkStructureFact is the binding's check of a typed structure fact: the
// assumed antecedent is the structure's predicate applied to its
// components, and each carrier phantom's binder is the component at
// that carrier's position.
func (a *Argument) checkStructureFact(info _StructureFactRuntimeInfo, content core.Term) {
	head, args := ext.MatchesApply(content)
	c, isConst := head.AsConst()
	if !isConst || string(c.Name()) != info.predicate {
		panic(fmt.Sprintf("the parameter is a fact of %s, but the antecedent is\n  %s",
			info.predicate, ext.PrintTerm(content)))
	}
	if len(info.carriers) != len(info.binders) {
		panic(fmt.Sprintf("the structure %s has %d carrier(s) and the parameter names %d",
			info.predicate, len(info.carriers), len(info.binders)))
	}
	for i, pos := range info.carriers {
		if pos >= len(args) {
			panic(fmt.Sprintf("the structure %s places carrier %d at argument %d of %d",
				info.predicate, i+1, pos+1, len(args)))
		}
		want := a.carrierBinder(info.binders[i])
		if !args[pos].Equals(want) {
			panic(a.withAliasLegend(fmt.Sprintf("carrier %d of %s is %s, which is not the binder %s the parameter's phantom names",
				i+1, info.predicate, ext.PrintTerm(args[pos]), info.binders[i])))
		}
	}
}

// carrierBinder resolves a carrier phantom's binder to the section's
// own variable for that surface name, panicking — with the legend —
// when the name is not a binder in scope.
func (a *Argument) carrierBinder(name string) core.Term {
	if name == "" {
		panic("on.Any names no binder — a structure law's closure spells its carrier's letter (on.C, on.M, …)")
	}
	if v, ok := a.surfaceAliases()[name]; ok {
		return v
	}
	if ty, ok := a.s.ParseScope.Vars[name]; ok {
		return core.Var(core.TermName(name), ty)
	}
	panic(a.withAliasLegend(fmt.Sprintf(
		"the carrier letter %s is not a binder in scope — a carrier phantom names a binder of the statement", name)))
}

// carrierSet is the set a carrier phantom's binder stands for: the
// binder itself where it is a set, its record's carrier field where it
// is a record.
func (a *Argument) carrierSet(name string) core.Term {
	v := a.carrierBinder(name)
	if ext.IsFunType(v.Type()) {
		if parts := ext.MatchesFun(v.Type()); len(parts) == 2 && parts[1].Equals(ext.TypeBool) {
			return v
		}
	}
	return a.Term(name + ".carrier").Core()
}
