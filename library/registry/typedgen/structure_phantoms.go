// structure_phantoms.go — the carrier refinement of a structure law's
// reading: a structure on a set gets a phantom, its facts a type
// (proof.StructureFact), and a law of it a typed Read.
//
// A structure whose definition has one or two CARRIERS — a component
// that is a set, or a record whose `carrier` field is one — is declared
// in its family's generated file as a structure phantom
// (`GroupStructure`) and an alias of its facts
// (`GroupFact[Car] = proof.StructureFact[GroupStructure, Car]`, the
// carrier a phantom of package on). Both are named by the structure's
// stem: the definition's name without the word its constant ends in,
// `On` for `_on` and `In` for `_in`, since the carrier phantom already
// says where the fact lives — `GroupFact[on.C]`, a group fact on C. A law of such a structure is then read
// typed: its Read infers the structure and the carriers from the
// instance (proof.Instance), its reading's members are members of
// those carriers, a projection — a law whose body is another such
// structure's fact at the carriers — reads as that structure's typed
// fact, and a closure law — a body that says a term of the points lies
// in a carrier — reads, at its points, as the member it concludes.
// Every untyped instance still reads, at proof.AnyStructure and on.Any,
// so a law's untyped call sites are unchanged.

package typedgen

import (
	"fmt"
	"path"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
)

// structurePhantom is a structure on a set as the typed surface spells
// it.
type structurePhantom struct {
	pred string
	name string // the structure's stem, its Go name less On or In (Group)
	home string // the import path of the family defining it
	fam  *registry.Family
	// carriers are the argument positions of the carriers, in order.
	carriers []int
	// recordField is, per argument position, the projection constant of
	// a record component's carrier field, and "" for a set component or
	// a component that is no carrier.
	recordField []string
}

func (p *structurePhantom) typeName() string { return p.name + "Structure" }

// factName is the alias of the structure's facts at any carriers.
func (p *structurePhantom) factName() string { return p.name + "Fact" }

// structureStem is a structure's Go name less the word its predicate
// ends in: `GroupOn` of group_on is Group, a `CompactIn` of compact_in
// would be Compact, and a predicate with neither suffix keeps its name.
// A definition named otherwise than its constant breaks the naming rule
// the constitution states, and the generator refuses it.
func structureStem(entryName, pred string) string {
	for _, w := range []struct{ suffix, word string }{{"_on", "On"}, {"_in", "In"}} {
		if !strings.HasSuffix(pred, w.suffix) {
			continue
		}
		stem, cut := strings.CutSuffix(entryName, w.word)
		if !cut || stem == "" {
			panic(fmt.Sprintf("typedgen: structure %s of %s does not end in %s", entryName, pred, w.word))
		}
		return stem
	}
	return entryName
}

// qualifier is the selector prefix a generated file of the family at
// importPath spells the phantom's names with: none at home.
func (p *structurePhantom) qualifier(importPath string) string {
	if p.home == importPath {
		return ""
	}
	return path.Base(p.home) + "."
}

var phantomCache sync.Map // predicate → *structurePhantom (nil: none)

// phantomOf is the structure phantom of a predicate: a structure some
// family defines, with one or two carriers.
func phantomOf(pred string) (*structurePhantom, bool) {
	if v, ok := phantomCache.Load(pred); ok {
		p := v.(*structurePhantom)
		return p, p != nil
	}
	p := readPhantom(pred)
	phantomCache.Store(pred, p)
	return p, p != nil
}

// StructureFactAlias is the typed fact of a structure's predicate as a
// proof file of the family at importPath spells it — the alias its
// defining family's generated file declares, qualified by that
// family's package away from home (`comm_ring.CommRingFact`, bare in
// comm_ring's own files) — with the argument positions of its
// carriers, in the order the alias takes their phantoms; ok is false
// for a predicate with no phantom (no structure, or no carrier, or
// more than two). The emitter of session proofs spells a closure's
// structure-fact parameter through it.
func StructureFactAlias(pred, importPath string) (alias, home string, carriers []int, ok bool) {
	ph, ok := phantomOf(pred)
	if !ok {
		return "", "", nil, false
	}
	return ph.qualifier(importPath) + ph.factName(), ph.home, append([]int(nil), ph.carriers...), true
}

func readPhantom(pred string) *structurePhantom {
	s, ok := registry.StructureByPredicate(pred)
	if !ok || s.ProofEntry == nil || s.Family() == nil || s.IsWholeTypeView() {
		return nil
	}
	t := s.ProofEntry.Statement().Prop.Conclusion()
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		t = abs.Body()
	}
	left, _, isIff := ext.MatchesIFF(t)
	if !isIff {
		return nil
	}
	_, args := spine(left)
	ph := &structurePhantom{
		pred:        pred,
		name:        structureStem(strings.TrimPrefix(s.ProofEntry.Name, path.Base(s.Family().Name)+"."), pred),
		home:        chapterImportPath + familyDir(s.Family()),
		fam:         s.Family(),
		recordField: make([]string, len(args)),
	}
	for i, a := range args {
		switch {
		case isSetType(a.Type()):
			ph.carriers = append(ph.carriers, i)
		case recordCarrierField(a.Type()) != "":
			ph.carriers = append(ph.carriers, i)
			ph.recordField[i] = recordCarrierField(a.Type())
		}
	}
	if n := len(ph.carriers); n == 0 || n > 2 {
		return nil
	}
	return ph
}

// isSetType reports whether t is a set, `τ → bool`.
func isSetType(t core.HolType) bool {
	if !ext.IsFunType(t) {
		return false
	}
	parts := ext.MatchesFun(t)
	return len(parts) == 2 && parts[1].Equals(ext.TypeBool)
}

// recordCarrierField is the projection constant of a record type's
// `carrier` field, "" for any other type.
func recordCarrierField(t core.HolType) string {
	record, ok := t.(core.CompositeType)
	if !ok {
		return ""
	}
	syntax := registry.GetConstMetaManager().StructSyntax(string(record.Meta().Name()))
	if syntax == nil {
		return ""
	}
	for _, f := range syntax.Fields {
		if f.Name == "carrier" {
			return f.Const
		}
	}
	return ""
}

// lawPhantom is the reading's view of a law of a phantom structure:
// the phantom, and the law's own arguments to its predicate.
type lawPhantom struct {
	ph        *structurePhantom
	args      []core.Term
	normalize func(core.Term) core.Term
}

// lawStructure reads the structure a law's antecedent applies, where it
// has a phantom.
func lawStructure(p core.Prop) (*lawPhantom, bool) {
	t := p.Conclusion()
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		t = abs.Body()
	}
	antecedent, _, ok := ext.MatchesIMPLY(t)
	if !ok {
		return nil, false
	}
	head, args := spine(antecedent)
	c, isConst := head.AsConst()
	if !isConst {
		return nil, false
	}
	ph, ok := phantomOf(string(c.Name()))
	if !ok || len(args) != len(ph.recordField) {
		return nil, false
	}
	return &lawPhantom{ph: ph, args: args}, true
}

// carrierOf is the index, among the law structure's carriers, of the
// carrier a set term is: a set component itself, or a record
// component's carrier field. -1 for any other set.
func recordCarrierTerm(record core.Term, field string) core.Term {
	meta := registry.GetConstMetaManager().ConstMeta(field)
	domain := ext.MatchesFun(meta.AbsType())[0]
	inst, ok := domain.Matches(record.Type(), func(core.VarType) bool { return true })
	if !ok {
		panic("typedgen: a record carrier projection does not take its record type")
	}
	return core.Apply(core.MakeConstTerm(meta, meta.AbsType().Substitute(inst...)), record)
}

func (l *lawPhantom) carrierOf(set core.Term) int {
	if l.normalize != nil {
		set = l.normalize(set)
	}
	for i, pos := range l.ph.carriers {
		carrier := l.args[pos]
		if field := l.ph.recordField[pos]; field != "" {
			carrier = recordCarrierTerm(carrier, field)
		}
		if l.normalize != nil {
			carrier = l.normalize(carrier)
		}
		if set.AlphaEquals(carrier) {
			return i
		}
	}
	return -1
}

// recordCarrierNormalizer compares carriers through the same projection
// equations the instance boundary computes, without building a proof.
func recordCarrierNormalizer() func(core.Term) core.Term {
	return registry.RecordTermNormalizer()
}

// carrierParams are the reading's carrier type parameters, Car0, Car1.
func (l *lawPhantom) carrierParams() []string {
	out := make([]string, len(l.ph.carriers))
	for i := range out {
		out[i] = fmt.Sprintf("Car%d", i)
	}
	return out
}

// projection is a law whose body is another phantom structure's fact
// with each of its carriers one of the law structure's: the conclusion's
// phantom and, per conclusion carrier, the law carrier it is.
type projection struct {
	ph     *structurePhantom
	mapped []int
}

func (l *lawPhantom) projectionOf(body core.Term) (*projection, bool) {
	head, args := spine(body)
	c, isConst := head.AsConst()
	if !isConst {
		return nil, false
	}
	ph, ok := phantomOf(string(c.Name()))
	if !ok || len(args) != len(ph.recordField) {
		return nil, false
	}
	pr := &projection{ph: ph}
	for _, pos := range ph.carriers {
		carrier := args[pos]
		if field := ph.recordField[pos]; field != "" {
			carrier = recordCarrierTerm(carrier, field)
		}
		k := l.carrierOf(carrier)
		if k < 0 {
			return nil, false
		}
		pr.mapped = append(pr.mapped, k)
	}
	return pr, true
}

// closureCarrier reads a reading's body — its own ∀-binders, at most
// one guard, then the conclusion — as a membership in a carrier: the
// carrier's index and the member's type. -1 for any other body.
func (l *lawPhantom) closureCarrier(body core.Term) (int, core.HolType) {
	for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
		body = abs.Body()
	}
	if _, concl, ok := ext.MatchesIMPLY(body); ok {
		body = concl
	}
	head, args := spine(body)
	c, isConst := head.AsConst()
	if !isConst || string(c.Name()) != "set_member" || len(args) != 2 {
		return -1, nil
	}
	k := l.carrierOf(args[1])
	if k < 0 {
		return -1, nil
	}
	return k, args[0].Type()
}

// reachable is the set of families whose packages the family's package
// imports, directly or not, itself included: the families the
// generated file may import, read off the import graph of the chapter's
// hand-written files (chapterImports).
func reachable(fam *registry.Family) (map[*registry.Family]bool, error) {
	graph, err := chapterImports()
	if err != nil {
		return nil, err
	}
	imported := graph.closure(familyDir(fam))
	seen := map[*registry.Family]bool{fam: true}
	for _, f := range registry.Families() {
		if imported[familyDir(f)] {
			seen[f] = true
		}
	}
	return seen, nil
}

// isStructureFact reports whether t applies a structure's predicate: a
// statement or a body that is a structure's fact, which a typed Read
// may be handed as an untyped instance.
func isStructureFact(t core.Term) bool {
	head, _ := spine(t)
	c, isConst := head.AsConst()
	return isConst && registry.IsStructurePredicate(string(c.Name()))
}

// stripForAll is t under its leading ∀-binders.
func stripForAll(t core.Term) core.Term {
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		t = abs.Body()
	}
	return t
}

// refineCarriers reads a typed law's body as a projection or a closure
// law: a body that is another phantom structure's fact at the law's
// carriers, with no witnesses of its own, is a projection; a body that,
// at its witnesses, puts a term in one of the carriers is a closure law.
func refineCarriers(w *wrapper, body core.Term, reach map[*registry.Family]bool, usedTypedefs map[string]bool) {
	if len(w.slots) == w.components {
		if pr, ok := w.law.projectionOf(body); ok && reach[pr.ph.fam] {
			w.projection = pr
		}
		return
	}
	k, ty := w.law.closureCarrier(body)
	if k < 0 || !onlyMemberGuards(w.readingSlots, guardConjuncts(body)) {
		return
	}
	letterParam := map[string]string{}
	for i, l := range w.letters {
		letterParam[l] = fmt.Sprintf("Type%d", i)
	}
	elem, err := renderPhantom(ty, letterParam, usedTypedefs)
	if err != nil {
		return
	}
	w.closure, w.closureElem = k, elem
}

// onlyMemberGuards reports whether a reading's guards state only
// memberships of its member slots — what lets a closure law's reading
// at its points stand for the membership it concludes, every premise
// it needs being the points' own evidence.
func onlyMemberGuards(slots []witnessSlot, antecedents []core.Term) bool {
	members := map[string]bool{}
	for _, s := range slots {
		if s.member {
			members[s.binder] = true
		}
	}
	for _, a := range antecedents {
		head, args := spine(a)
		c, isConst := head.AsConst()
		if !isConst || string(c.Name()) != "set_member" || len(args) != 2 {
			return false
		}
		x, isVar := args[0].AsVar()
		if !isVar || !members[string(x.Name())] {
			return false
		}
	}
	return true
}

// markCarriers names each member slot's carrier: the reading's carrier
// parameter where the slot's guard set is a carrier of the law's
// phantom structure, on.Any otherwise.
func markCarriers(slots []witnessSlot, antecedents []core.Term, law *lawPhantom) {
	for i := range slots {
		s := &slots[i]
		if !s.member {
			continue
		}
		s.carrier = "on.Any"
		if law == nil {
			continue
		}
		for _, a := range antecedents {
			head, args := spine(a)
			c, isConst := head.AsConst()
			if !isConst || string(c.Name()) != "set_member" || len(args) != 2 {
				continue
			}
			if x, isVar := args[0].AsVar(); !isVar || string(x.Name()) != s.binder {
				continue
			}
			if k := law.carrierOf(args[1]); k >= 0 {
				s.carrier = fmt.Sprintf("Car%d", k)
			}
		}
	}
}

// renderStructurePhantoms declares, for each structure on a set the
// family defines, its phantom and the alias of its facts at any
// carriers (`GroupFact[Car]`), the one name a closure, a reading and a
// signature spell the fact by, its carriers always written.
func renderStructurePhantoms(b *strings.Builder, fam *registry.Family, selfPath string) {
	for _, s := range fam.Structures() {
		ph, ok := phantomOf(s.Const)
		if !ok || ph.home != selfPath {
			continue
		}
		positions := make([]string, len(ph.carriers))
		for i, pos := range ph.carriers {
			positions[i] = fmt.Sprint(pos)
		}
		fmt.Fprintf(b, "// %s is the structure phantom of %s: its predicate and the\n"+
			"// argument positions of its carriers, what a fact of it is typed by\n"+
			"// (proof.StructureFact).\n", ph.typeName(), ph.pred)
		fmt.Fprintf(b, "type %s struct{}\n\n", ph.typeName())
		fmt.Fprintf(b, "func (%s) Predicate() string { return %q }\n\n", ph.typeName(), ph.pred)
		fmt.Fprintf(b, "func (%s) Carriers() []int { return []int{%s} }\n\n", ph.typeName(), strings.Join(positions, ", "))
		if len(ph.carriers) == 1 {
			fmt.Fprintf(b, "// %s is a fact of %s on the carrier Car, a phantom of package on\n"+
				"// naming the carrier's binder: what a law of it is read at, typed.\n",
				ph.factName(), ph.pred)
			fmt.Fprintf(b, "type %s[Car on.Carrier] = proof.StructureFact[%s, Car]\n\n", ph.factName(), ph.typeName())
		} else {
			fmt.Fprintf(b, "// %s is a fact of %s on the carriers Car0 and Car1, phantoms of\n"+
				"// package on naming the carriers' binders: what a law of it is read\n"+
				"// at, typed.\n", ph.factName(), ph.pred)
			fmt.Fprintf(b, "type %s[Car0, Car1 on.Carrier] = proof.StructureFact2[%s, Car0, Car1]\n\n", ph.factName(), ph.typeName())
		}
	}
}
