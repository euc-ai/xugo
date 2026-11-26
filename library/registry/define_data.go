// define_data.go — family.DefineData: the form of the
// datatype definition move. The emitted / hand-written twin of the
// session `define` RPC's `data:` payload: ONE call whose registration
// MINTS the datatype (type + constructors, exclusive, at package var
// init — the Define two-phase rationale verbatim: identity must exist
// before any later parse) and registers one entry PER DERIVED-THEOREM
// FAMILY (INDUCT / RECURSION / INJ / DISTINCT — the latter two absent
// when the shape has none), under the names the chapter spells in
// DataEntry.Principles, each of whose Build re-derives its theorem
// through the same composite step the session recorded
// (proof.DefineDataStep) — the record/emit/replay principle at ENTRY
// granularity.
//
// The derived entries' statements are the door's own, keys computed
// from the statements at registration. The INDUCT and RECURSION entries carry ServesAs — the
// principle-name binding (btree_induction / btree_recursion) a read of
// which is a read of the entry, so the induction tactic
// and the recursion-schema compile resolve a datatype's principles
// through env.LibraryThms exactly as they resolve num/list/option's
// (the num_induction harness-overlay problem, solved in the dep model
// instead of per-name overlays).
//
// A recursive family.Define over a DefineData'd carrier declares its
// schema as a TYPED Dep on the Recursion entry (the datatypeByName
// table below), which both serves the schema under its conventional
// name (ServesAs) and keeps the dep DAG compiler-visible.

package registry

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// DataEntry declares one datatype: the handle's name (the door's var is
// `<Name>Data`), the minted type's name, its parameters, the
// constructors, and — in Principles — the registered names of the
// derived entries, spelled by the chapter.
type DataEntry struct {
	Name         string
	Type         string
	Params       []string
	Constructors []proof.DataConstructorSpec
	// Principles names the derived entries as the chapter registers
	// them: the SAME words the chapter's re-export vars carry
	// (`Induction = inductionThm{ListData.Induct}`), so a session
	// `with_lemmas` key, a brief's "Deps available" line and a Go cite
	// all spell one name. Induction and Recursion are always
	// required; Injective exactly when a constructor takes arguments,
	// Distinct exactly when there are two or more constructors — a
	// name for a principle the shape lacks, or a missing required one,
	// is refused at registration (nothing is derived by suffix).
	Principles DataPrinciples
	// Fields names the PARTS of a record — a datatype with one
	// constructor — one per constructor argument, in the constructor's
	// order. The door defines each part by its projection equation
	// (`complex_re(complex(a, b)) = a`), registered under the field's
	// Name; derives the record's extensionality, `u = v ⇔ p₁(u) = p₁(v)
	// ∧ … ∧ pₖ(u) = pₖ(v)`, registered under Principles.Extensionality;
	// and hands the chapter `Parts`, the rule set that rewrites an
	// equation between records into the equations between their parts
	// and computes each part at the constructor (DatatypeEntries.Parts).
	// A datatype with several constructors has no parts: a projection
	// would be partial. Refused there, and on a constructor without
	// arguments.
	Fields []DataField
	// Deps declares the entries the derived theorems' Builds read —
	// the recspace rows (recspace_recursion, recspace_node_injective, family_cons), the pair
	// projections and suc_not_zero / suc_injective — as the entries that prove
	// them (their ServesAs binds the names). Each derived entry
	// declares the subset its own derivation consumes; registration
	// panics when a name a derivation reads has no dep serving it.
	Deps []EntryLike
}

// DataPrinciples is a datatype's derived-theorem names, as the chapter
// registers them (see DataEntry.Principles). Extensionality is named
// exactly when the datatype declares Fields.
type DataPrinciples struct {
	Induction      string
	Recursion      string
	Injective      string
	Distinct       string
	Extensionality string
}

// DataField is one part of a record (DataEntry.Fields): the entry name
// its projection equation registers under, the constant it mints, and
// — optionally — the overloaded word a text may write for it
// (DefEntry.Overload), so that the part reads as `re(z)` while the
// constant carries its domain, `complex_re`; the name a text writes
// after the dot of a value of the record (Field: `R.add` for
// `ring_add(R)`); and the operator symbol a part that is an operation
// or a map carries (Symbol: `c + d` for `ring_add(R)(c, d)` under a
// binder R of the record), read at the operands' types
// (ext/dsl/struct_fields.go).
type DataField struct {
	Name     string
	Const    string
	Overload string
	Field    string
	Symbol   string
}

// name returns the registered (bare) name for one derived-theorem
// kind, "" when the chapter names none.
func (p DataPrinciples) name(k proof.DataTheoremKind) string {
	switch k {
	case proof.DataInduct:
		return p.Induction
	case proof.DataRecursion:
		return p.Recursion
	case proof.DataInj:
		return p.Injective
	case proof.DataDistinct:
		return p.Distinct
	}
	return ""
}

// DatatypeEntries is DefineData's handle: the registered derived
// entries (Inj/Distinct nil when the shape has none) plus the minted
// identity the Builds and the schema wiring read.
type DatatypeEntries struct {
	Induct    *ProofEntry
	Recursion *ProofEntry
	Inj       *ProofEntry
	Distinct  *ProofEntry

	// A record's parts (DataEntry.Fields): the projection equations in
	// field order, and the extensionality law. Empty / nil otherwise. The
	// family's generated file names each projection equation after its
	// field's entry (`RingAddDef`), the name a citation spells.
	Fields []*ProofEntry
	Ext    *ProofEntry
	// Parts is the record's componentwise reading as one rule set —
	// extensionality, then every projection equation — so that `Simp(Parts,
	// Fwd(<an operation's definition>))` turns an equation between records
	// into equations between their parts, computed.
	Parts proof.SimpRule

	md *proof.MintedDatatype
}

// Minted exposes the minted datatype (emit and tests read the
// constructor consts off it).
func (de *DatatypeEntries) Minted() *proof.MintedDatatype { return de.md }

// Entry returns the entry for one derived-theorem kind (nil when
// absent).
func (de *DatatypeEntries) Entry(k proof.DataTheoremKind) *ProofEntry {
	switch k {
	case proof.DataInduct:
		return de.Induct
	case proof.DataRecursion:
		return de.Recursion
	case proof.DataInj:
		return de.Inj
	case proof.DataDistinct:
		return de.Distinct
	}
	return nil
}

// datatypeByName maps a minted type name to its entries — the
// recursive Define's schema-dep wiring (see the file comment). Written
// only at registration (package init, single-goroutine).
var datatypeByName = map[core.TypeName]*DatatypeEntries{}

// DatatypeEntriesFor returns the registered entries for a
// DefineData'd type name.
func DatatypeEntriesFor(name core.TypeName) (*DatatypeEntries, bool) {
	de, ok := datatypeByName[name]
	return de, ok
}

// dataTheoremLibraryNames returns the library names each derived
// theorem's Build reads off env.LibraryThms — the entry's honest dep
// set, computed from the shape (a single-slot payload needs no pair
// rows; a two-constructor type needs no suc_injective; INDUCT is pure logic
// and needs none).
func dataTheoremLibraryNames(md *proof.MintedDatatype, k proof.DataTheoremKind) []string {
	dd := md.Def
	multiSlot := len(dd.PayloadSlots) > 1
	anyRecArg := false
	for j := range dd.Ctors {
		if len(dd.Ctors[j].RecPositions()) > 0 {
			anyRecArg = true
		}
	}
	switch k {
	case proof.DataInduct:
		return nil
	case proof.DataRecursion:
		out := []string{"recspace_recursion", "family_cons_definition"}
		if multiSlot {
			out = append(out, "fst_of_pair", "snd_of_pair")
		}
		return out
	case proof.DataInj:
		out := []string{"recspace_node_injective"}
		if anyRecArg {
			out = append(out, "family_cons_definition")
		}
		if multiSlot {
			out = append(out, "pair_injective")
		}
		return out
	case proof.DataDistinct:
		out := []string{"recspace_node_injective", "suc_not_zero"}
		if len(dd.Ctors) > 2 {
			out = append(out, "suc_injective")
		}
		return out
	}
	return nil
}

// DefineData registers a datatype's entries: mints the type and
// constructors NOW (registration time — see the file comment), and
// registers one entry per derived-theorem family, each
// closing through the define-data composite. Init-time failures panic
// — a datatype that cannot parse, analyze, or mint is a broken
// package, not a replay finding.
func (f *Family) DefineData(e DataEntry) *DatatypeEntries {
	e.Type = dsl.OneLine(e.Type)
	if e.Name == "" || e.Type == "" {
		panic("registry.DefineData: Name and Type are required")
	}
	checkDataFields(e)
	mgr := GetConstMetaManager()
	lookup := func(name core.TermName) core.ConstTermMeta {
		if meta, ok := mgr.LoadConstMeta(name); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}
	typeInUse := proof.TypeNameInUseProbe(mgr.Range)
	dd, err := proof.AnalyzeDataDefinition(e.Type, e.Params, e.Constructors, lookup, typeInUse)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineData(%s): %v", e.Name, err))
	}
	mintEnv := &proof.ProverEnv{ProofService: &proof.ProofService{
		LoadConstMeta:        mgr.LoadConstMeta,
		LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
		Syntax:               mgr,
		TypeArity:            mgr.TypeArity,
	}}
	md, err := proof.MintDataDefinition(mintEnv, dd)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineData(%s): %v", e.Name, err))
	}

	de := &DatatypeEntries{md: md}
	ctorTerms := make([]core.Term, len(md.Ctors))
	for i, c := range md.Ctors {
		ctorTerms[i] = c
	}
	// What the door mints: the type's abs and rep, then the constructors.
	mintedNames := []string{string(md.Mk.Name()), string(md.Dest.Name())}
	for _, c := range md.Ctors {
		mintedNames = append(mintedNames, string(c.Name()))
	}
	// The chapter's names, checked against the shape: every derived
	// kind has exactly one name, and no name is given for a kind the
	// shape does not derive.
	have := map[proof.DataTheoremKind]bool{}
	for _, k := range md.Kinds() {
		have[k] = true
		if e.Principles.name(k) == "" {
			panic(fmt.Sprintf("registry.DefineData(%s): the %v derivation has no registered name — spell it in Principles (%s)",
				e.Name, k, principlesFieldName(k)))
		}
	}
	for _, k := range []proof.DataTheoremKind{proof.DataInduct, proof.DataRecursion, proof.DataInj, proof.DataDistinct} {
		if !have[k] && e.Principles.name(k) != "" {
			panic(fmt.Sprintf("registry.DefineData(%s): Principles names %s %q, but this shape derives no %v (a constructor with arguments is what makes an injectivity law; two or more constructors, a distinctness law)",
				e.Name, principlesFieldName(k), e.Principles.name(k), k))
		}
	}
	minted := false
	for _, k := range md.Kinds() {
		kind := k
		stmt := md.Stmt(kind)
		// The entry's key is computed from its statement, not spelled:
		// this door registers several entries from one literal, and none
		// has a literal of its own to spell one in (ProofEntry.Key).
		normalized, _ := prop.Normalize(stmt)
		servesAs := ""
		if kind == proof.DataInduct || kind == proof.DataRecursion {
			servesAs = md.PrincipleName(kind)
		}
		var deps []EntryLike
		for _, name := range dataTheoremLibraryNames(md, kind) {
			dep, ok := depServing(e.Deps, name)
			if !ok {
				panic(fmt.Sprintf(
					"registry.DefineData(%s): the %v derivation reads %s, which no dep serves — "+
						"declare the entry that proves it in Deps", e.Name, kind, name))
			}
			deps = withDep(deps, dep)
		}
		entry := f.addDeclared(ProofEntry{
			Name:        e.Principles.name(kind),
			Key:         string(normalized.AlphaKey()),
			Definition:  proof.DataDefinitionShape(kind),
			defines:     mintedOnce(&minted, mintedNames),
			definesType: e.Type,
			ServesAs:    servesAs,
			Deps:        deps,
			// The statement was computed at registration: the entry's
			// statement and the Build's section goal are one value (the
			// Define precedent).
			stated: stmt,
			Build: Bare(func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
				ctx := f.NewScript(env)
				sec := ctx.Section(stmt)
				sec.Do(proof.DefineDataStep(md.Mk, ctorTerms...))
				if !sec.Proved() {
					panic(fmt.Sprintf(
						"registry.DefineData(%s): the %v derivation did not close — are "+
							"the recspace rows preloaded (Deps)?", e.Name, kind))
				}
				return sec.PromisedThm(), &ctx.Proof
			}),
		})
		entry.goRef = e.Name + "Data." + map[proof.DataTheoremKind]string{
			proof.DataInduct: "Induct", proof.DataRecursion: "Recursion", proof.DataInj: "Inj", proof.DataDistinct: "Distinct",
		}[kind]
		switch kind {
		case proof.DataInduct:
			de.Induct = entry
		case proof.DataRecursion:
			de.Recursion = entry
		case proof.DataInj:
			de.Inj = entry
		case proof.DataDistinct:
			de.Distinct = entry
		}
	}
	// Registered before the parts: a projection is a definition by cases
	// over this carrier, and the define door reads its schema here.
	datatypeByName[dd.TypeName] = de
	f.defineParts(e, de)
	stampDoor(DoorCall{Door: "DefineData", Name: e.Name, Type: e.Type, Fields: e.Fields},
		append([]*ProofEntry{de.Induct, de.Recursion, de.Inj, de.Distinct, de.Ext}, de.Fields...)...)
	return de
}

// defineParts registers a record's projections, its extensionality law
// and its Parts rule set (DataEntry.Fields).
func (f *Family) defineParts(e DataEntry, de *DatatypeEntries) {
	if len(e.Fields) == 0 {
		return
	}
	ctor := e.Constructors[0]
	typeText := e.Type
	if len(e.Params) > 0 {
		typeText += "(" + strings.Join(e.Params, ", ") + ")"
	}
	// The constructor's arguments, bound as a, b, c, … in the projection
	// equations: `∀a:real. ∀b:real. complex_re(complex(a, b)) = a`.
	binders := make([]string, len(ctor.Args))
	var quant strings.Builder
	for i, argType := range ctor.Args {
		binders[i] = string(rune('a' + i))
		fmt.Fprintf(&quant, "∀%s:%s. ", binders[i], argType)
	}
	pattern := ctor.Name + "(" + strings.Join(binders, ", ") + ")"
	for i, field := range e.Fields {
		// A projection's key is computed from its statement, not
		// spelled: the record's one literal registers every projection,
		// and none has a literal of its own to spell one in
		// (ProofEntry.Key).
		entry, _ := f.define(DefEntry{
			Name:        field.Name,
			Const:       field.Const,
			Type:        typeText + " → " + ctor.Args[i],
			Overload:    field.Overload,
			Equations:   []string{quant.String() + field.Const + "(" + pattern + ") = " + binders[i]},
			computedKey: true,
		})
		entry.recordField = fmt.Sprintf("%sData.Fields[%d]", e.Name, i)
		de.Fields = append(de.Fields, entry)
	}
	var named []dsl.StructField
	for _, field := range e.Fields {
		if field.Field != "" {
			named = append(named, dsl.StructField{Name: field.Field, Const: field.Const, Symbol: field.Symbol})
		}
	}
	if len(named) > 0 {
		if err := declareStruct(e.Type, named); err != nil {
			panic(fmt.Sprintf("registry.DefineData(%s): %v", e.Name, err))
		}
	}

	// Extensionality: `∀u v:T. u = v ⇔ p₁(u) = p₁(v) ∧ … ∧ pₖ(u) = pₖ(v)`.
	parts := make([]string, len(e.Fields))
	for i, field := range e.Fields {
		parts[i] = fmt.Sprintf("%s(u) = %s(v)", field.Const, field.Const)
	}
	extText := fmt.Sprintf("∀u v:%s. u = v ⇔ %s", typeText, strings.Join(parts, " ∧ "))
	mgr := GetConstMetaManager()
	parsed := dsl.ParsePropTextInScope(extText, &dsl.ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if meta, ok := mgr.LoadConstMeta(core.TermName(name)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
		Syntax:       mgr,
		TypeResolver: mgr.TypeArity,
	})
	if parsed.Prop == nil {
		panic(fmt.Sprintf("registry.DefineData(%s): the extensionality statement %q: %v", e.Name, extText, parsed.Errors))
	}
	stmt := parsed.Prop
	// The entry's key is computed from its statement, not spelled:
	// this door registers several entries from one literal, and none
	// has a literal of its own to spell one in (ProofEntry.Key).
	normalized, _ := prop.Normalize(stmt)
	deps := append([]EntryLike{de.Induct, de.Inj}, entriesLike(de.Fields)...)
	fields := de.Fields
	de.Ext = f.addDeclared(ProofEntry{
		Name:   e.Principles.Extensionality,
		Key:    string(normalized.AlphaKey()),
		Deps:   deps,
		stated: stmt,
		// By cases on both records: at the constructor the parts read back
		// as the constructor's arguments, and injectivity rewrites the
		// equation between the two constructions into the equations
		// between their arguments — both sides are then one conjunction,
		// with no search at any number of parts.
		Build: Bare(func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := f.NewScript(env)
			sec := ctx.Section(stmt)
			rules := make([]proof.SimpRule, 0, len(fields)+1)
			for _, fe := range fields {
				rules = append(rules, proof.Fwd(fe))
			}
			rules = append(rules, proof.Fwd(de.Inj))
			sec.Do(proof.Derive(func(a *proof.Argument) {
				a.Induct("u")
				a.Induct("v")
				a.Show("at the constructor the parts are its arguments, and the constructor is injective",
					proof.Simp(rules...), proof.Basic())
			}))
			sec.Qed()
			return sec.PromisedThm(), &ctx.Proof
		}),
	})

	de.Ext.goRef = e.Name + "Data.Ext"

	members := []proof.SimpRule{proof.Fwd(de.Ext)}
	for _, fe := range de.Fields {
		members = append(members, proof.Fwd(fe))
	}
	de.Parts = proof.RuleSet(members...)
}

// checkDataFields refuses a Fields declaration the shape cannot carry —
// before anything is minted, so a refused datatype leaves nothing
// behind: parts belong to a record (one constructor, with arguments),
// one per argument, and a record's parts derive its extensionality,
// which the chapter names.
func checkDataFields(e DataEntry) {
	if len(e.Fields) == 0 {
		if e.Principles.Extensionality != "" {
			panic(fmt.Sprintf("registry.DefineData(%s): Principles names Extensionality %q, but the datatype declares no Fields",
				e.Name, e.Principles.Extensionality))
		}
		return
	}
	if len(e.Constructors) != 1 {
		panic(fmt.Sprintf("registry.DefineData(%s): Fields are the parts of a record — a datatype with ONE constructor; this one has %d, so a projection would be partial",
			e.Name, len(e.Constructors)))
	}
	if n := len(e.Constructors[0].Args); n == 0 || len(e.Fields) != n {
		panic(fmt.Sprintf("registry.DefineData(%s): %d field(s) for a constructor of %d argument(s) — one field per argument, in the constructor's order",
			e.Name, len(e.Fields), n))
	}
	dotNames := map[string]bool{}
	for i, field := range e.Fields {
		if field.Name == "" || field.Const == "" {
			panic(fmt.Sprintf("registry.DefineData(%s): field %d needs a Name and a Const", e.Name, i))
		}
		if field.Symbol != "" && field.Field == "" {
			panic(fmt.Sprintf("registry.DefineData(%s): field %s carries %s but has no Field name — a symbol is read off a value's field",
				e.Name, field.Name, field.Symbol))
		}
		if field.Field == "" {
			continue
		}
		if strings.ContainsAny(field.Field, " ().,:'") {
			panic(fmt.Sprintf("registry.DefineData(%s): field %s: Field %q is not a name", e.Name, field.Name, field.Field))
		}
		if dotNames[field.Field] {
			panic(fmt.Sprintf("registry.DefineData(%s): Field %s is named twice", e.Name, field.Field))
		}
		dotNames[field.Field] = true
	}
	if e.Principles.Extensionality == "" {
		panic(fmt.Sprintf("registry.DefineData(%s): a record's Fields derive its extensionality — name it in Principles.Extensionality", e.Name))
	}
}

// entriesLike widens a list of entries to the EntryLike a Deps list takes.
func entriesLike(es []*ProofEntry) []EntryLike {
	out := make([]EntryLike, len(es))
	for i, e := range es {
		out[i] = e
	}
	return out
}

// principlesFieldName spells the DataPrinciples field a kind is named in.
func principlesFieldName(k proof.DataTheoremKind) string {
	switch k {
	case proof.DataInduct:
		return "Induction"
	case proof.DataRecursion:
		return "Recursion"
	case proof.DataInj:
		return "Injective"
	case proof.DataDistinct:
		return "Distinct"
	}
	return "?"
}

// depServing returns the dep that binds name in a consumer's env (by
// registered Name or ServesAs).
func depServing(deps []EntryLike, name string) (*ProofEntry, bool) {
	for _, d := range deps {
		if e := d.Entry(); e != nil && (e.Name == name || e.ServesAs == name) {
			return e, true
		}
	}
	return nil, false
}

// dataRecursionDep resolves the schema dep for a recursive Define
// whose carrier is a DefineData'd type: the typed Dep on the
// Recursion entry (its ServesAs binding serves the conventional
// name). ok=false for the corpus-served carriers (num/list/option),
// whose schema the member declares itself.
func dataRecursionDep(carrier core.HolType) (*ProofEntry, bool) {
	ct, isComposite := carrier.(core.CompositeType)
	if !isComposite {
		return nil, false
	}
	de, ok := datatypeByName[ct.Meta().Name()]
	if !ok || de.Recursion == nil {
		return nil, false
	}
	return de.Recursion, true
}
