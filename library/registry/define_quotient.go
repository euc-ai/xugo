// define_quotient.go — family.DefineQuotient: the quotient definition
// move as a chapter door. The emitted / hand-written twin of the
// session `define` RPC's `quotient:` payload: ONE call whose
// registration MINTS the type over the equivalence-class shape with
// its abs/rep pair and the class map (at package var init — the Define
// two-phase rationale: identity must exist before any later parse) and
// registers the seven theorems a quotient comes with, each an entry
// whose Build re-derives it through the same composite step the
// session records (proof.DefineQuotientStep; prover/proof/
// define_quotient.go is the shared spine) — the record/emit/replay
// principle at ENTRY granularity.
//
// The relation is the chapter's, in text — a constant it defined,
// possibly applied to its parameters. The one input is the entry
// proving equivalence(R) (the relations chapter's structure predicate),
// taken as the composite's child in every section: nothing is proved
// at init, and every derived theorem is derived at replay from that
// dep's certificate. The seven entries' statements are the door's own,
// keys computed from the statements at registration:
//
//	<Name>Surjectivity    ∀q:Q. ∃x:ρ. q = mk(x)
//	<Name>Induct          ∀P q. (∀x:ρ. P(mk(x))) ⇒ P(q)   ServesAs <Q>_induction
//	<Name>Sound           ∀x y:ρ. R(x, y) ⇒ mk(x) = mk(y)  ServesAs <Q>_sound
//	<Name>Exact           ∀x y:ρ. mk(x) = mk(y) ⇒ R(x, y)  ServesAs <Q>_exact
//	<Name>Eq              ∀x y:ρ. mk(x) = mk(y) ⇔ R(x, y)  (a use rule: imports install it)
//	<Name>ForallOnImage   ∀P. (∀q. P(q)) ⇔ (∀x. P(mk(x)))
//	<Name>ExistsOnImage   ∀P. (∃q. P(q)) ⇔ (∃x. P(mk(x)))
//
// The class map is spelled ⁅x⁆ and by the word `class`, the notation
// every quotient shares (the `|x|` precedent: one pair of delimiters
// under one overloaded word, the body's type picking the constant). A
// second quotient over the SAME carrier would be indistinguishable
// under the word, so it keeps its class map's name alone; the handle
// says which (ClassNotation).
//
// The mk/abs/rep names are claimed first (a name another chapter
// minted refuses). A recursive family.Define whose equations take the
// class map as a constructor pattern is a LIFT (define_lift.go); it
// declares the quotient's Sound and Exact entries as its deps through
// quotientByName below, the datatypeByName precedent.

package registry

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// ClassWord is the overloaded word every quotient's class map
// declares, ClassNotation the outfix it is spelled by.
const (
	ClassWord     = "class"
	ClassNotation = "⁅x⁆"
)

// QuotientEntry declares one quotient: the entry base name (the seven
// theorems register as Name+"Surjectivity", … — the var is `<Name>Def`),
// the minted type's name, the class map's and the typedef pair's
// constant names, the relation in text, and the entry proving it an
// equivalence.
type QuotientEntry struct {
	Name string
	// Type is the minted type's name; its parameters are the type
	// variables of the relation's carrier, in first-occurrence order.
	Type string
	// Mk names the class map mk : ρ → Q(σ); Abs and Rep the typedef
	// pair abs : set(ρ) → Q(σ), rep : Q(σ) → set(ρ) underneath it.
	Mk, Abs, Rep string
	// Relation is the equivalence relation — a closed term of type
	// ρ → ρ → bool spelled by a constant the chapter defined, possibly
	// applied to its parameters ("nadd_eq", "congruent(5)"). Every
	// constant it mentions must already resolve.
	Relation string
	// Equivalence is the chapter's entry proving `equivalence(R)` — the
	// relations chapter's predicate at the relation. The replay checks
	// the two agree (the proved statement must be the composite's own
	// child) — a mismatch fails the Build loudly.
	Equivalence EntryLike
	// Deps are further entries the derivations read; Equivalence is
	// always one.
	Deps []EntryLike
}

// QuotientEntries is DefineQuotient's handle: the seven registered
// theorem entries plus the minted identity.
type QuotientEntries struct {
	Surjectivity, Induct, Sound, Exact, Eq, ForallOnImage, ExistsOnImage *ProofEntry
	Meta                                                                 core.MetaType
	Mk, Abs, Rep                                                         core.ConstTerm
	Rel                                                                  core.Term
	// ClassNotation reports whether the class map spells ⁅x⁆ — false
	// for a second quotient over a carrier another already quotients.
	ClassNotation bool

	mq *proof.MintedQuotient
}

// Minted exposes the minted quotient (emit and the lift door read the
// class map and the statements off it).
func (qe *QuotientEntries) Minted() *proof.MintedQuotient { return qe.mq }

// Entry returns the entry for one derived-theorem kind.
func (qe *QuotientEntries) Entry(k proof.QuotientTheoremKind) *ProofEntry {
	switch k {
	case proof.QuotientSurjectivity:
		return qe.Surjectivity
	case proof.QuotientInduct:
		return qe.Induct
	case proof.QuotientSound:
		return qe.Sound
	case proof.QuotientExact:
		return qe.Exact
	case proof.QuotientEq:
		return qe.Eq
	case proof.QuotientForallOnImage:
		return qe.ForallOnImage
	case proof.QuotientExistsOnImage:
		return qe.ExistsOnImage
	}
	return nil
}

// quotientByName maps a minted type name to its entries — the lift
// door's dep wiring (the datatypeByName precedent). Written only at
// registration (package init, single-goroutine).
var quotientByName = map[core.TypeName]*QuotientEntries{}

// QuotientEntriesFor returns the registered entries for a
// DefineQuotient'd type name.
func QuotientEntriesFor(name core.TypeName) (*QuotientEntries, bool) {
	qe, ok := quotientByName[name]
	return qe, ok
}

// quotientEquivalenceLabel labels the composite's equivalence child in
// a chapter Build.
const quotientEquivalenceLabel = "the relation is an equivalence"

// DefineQuotient mints the quotient at registration and registers its
// seven theorems (see the file comment). Init-time failures panic — a
// relation that does not parse, a name that is not free, a type name
// that clashes at another arity — is a broken package.
func (f *Family) DefineQuotient(e QuotientEntry) *QuotientEntries {
	e.Type = dsl.OneLine(e.Type)
	if e.Name == "" || e.Type == "" || e.Mk == "" || e.Abs == "" || e.Rep == "" || e.Relation == "" {
		panic("registry.DefineQuotient: Name, Type, Mk, Abs, Rep and Relation are all required")
	}
	if err := proof.CheckMintedTypeName(e.Type); err != nil {
		panic(fmt.Sprintf("registry.DefineQuotient(%s): %v", e.Name, err))
	}
	if e.Equivalence == nil {
		panic(fmt.Sprintf("registry.DefineQuotient(%s): the quotient's one input is the entry proving equivalence(%s) — give Equivalence",
			e.Name, e.Relation))
	}
	equivalence := e.Equivalence.Entry()
	mgr := GetConstMetaManager()
	for _, n := range []string{e.Mk, e.Abs, e.Rep} {
		if err := mgr.ClaimName(core.TermName(n)); err != nil {
			panic(fmt.Sprintf("registry.DefineQuotient(%s): %v", e.Name, err))
		}
	}

	// The relation: read in the chapter's own dialect at the strict
	// door, exactly as a definition equation is.
	resolver := func(name string) core.ConstTermMeta {
		if meta, ok := mgr.LoadConstMeta(core.TermName(name)); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}
	base := &dsl.ParseScope{
		ConstResolver:    resolver,
		Syntax:           mgr,
		TypeResolver:     mgr.TypeArity,
		ImplicitBindings: f.implicit,
		CoerceDomain:     f.CoerceDomain(),
	}
	rel, err := proof.ParseQuotientRelation(e.Relation, base)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineQuotient(%s): %v", e.Name, err))
	}
	metaResolver := func(name core.TermName) core.ConstTermMeta { return resolver(string(name)) }
	qd, err := proof.AnalyzeQuotientDefinition(rel, metaResolver)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineQuotient(%s): %v", e.Name, err))
	}

	mintEnv := &proof.ProverEnv{ProofService: &proof.ProofService{
		LoadConstMeta:        mgr.LoadConstMeta,
		LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
		Syntax:               mgr,
		TypeArity:            mgr.TypeArity,
		RangeConstMeta:       mgr.Range,
	}}
	mq, err := proof.MintQuotientDefinition(mintEnv, qd, core.TypeName(e.Type), core.TermName(e.Abs), core.TermName(e.Rep), core.TermName(e.Mk))
	if err != nil {
		panic(fmt.Sprintf("registry.DefineQuotient(%s): %v", e.Name, err))
	}
	qe := &QuotientEntries{Meta: mq.Meta, Mk: mq.Mk, Abs: mq.Abs, Rep: mq.Rep, Rel: rel, mq: mq}
	qe.ClassNotation = RegisterClassNotation(mq)

	deps := withDep(nil, equivalence)
	for _, d := range e.Deps {
		deps = withDep(deps, d.Entry())
	}
	mintedNames := []string{e.Mk, e.Abs, e.Rep}
	minted := false
	// The class notation is the class map's; the kinds' entries all
	// carry the table, the one that defines the constants among them.
	var notations map[string]string
	if qe.ClassNotation {
		notations = notationsOf(e.Mk, ClassNotation)
	}
	for _, k := range proof.QuotientTheoremKinds {
		kind := k
		stmt := mq.Stmt(kind)
		// The entry's key is computed from its statement, not spelled:
		// this door registers several entries from one literal, and none
		// has a literal of its own to spell one in (ProofEntry.Key).
		normalized, _ := prop.Normalize(stmt)
		entry := f.addDeclared(ProofEntry{
			Name:        e.Name + kind.String(),
			Key:         string(normalized.AlphaKey()),
			Definition:  proof.QuotientDefinitionShape(kind),
			ServesAs:    mq.PrincipleName(kind),
			Deps:        deps,
			defines:     mintedOnce(&minted, mintedNames),
			definesType: e.Type,
			notations:   notations,
			// The statement was computed at registration: the entry's
			// statement and the Build's section goal are one value (the
			// Define precedent).
			stated: stmt,
			Build: Bare(func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
				ctx := f.NewScript(env)
				sec := ctx.Section(stmt)
				// The equivalence child closes by the dep's certificate —
				// harness-installed, never the promise — as a known
				// theorem: the dep must state the child (α-equal), the
				// same agreement the session door demands, so an entry
				// proving something else fails the Build loudly.
				eqv := ctx.Dep(equivalence)
				if eqv.NumHyps() != 0 || !eqv.Conclusion().AlphaEquals(qd.Equivalence.Conclusion()) {
					panic(fmt.Sprintf("registry.DefineQuotient(%s): %s proves %s, not the equivalence %s",
						e.Name, equivalence.Name, proof.PrintTerm(eqv.Conclusion()), proof.PrintTerm(qd.Equivalence.Conclusion())))
				}
				sec.Do(proof.DefineQuotientStep(mq.Mk, proof.MakeCase(quotientEquivalenceLabel, proof.CiteKnown(eqv))))
				if !sec.Proved() {
					panic(fmt.Sprintf("registry.DefineQuotient(%s): the %v derivation did not close — does %s prove the "+
						"equivalence as stated?", e.Name, kind, equivalence.Name))
				}
				return sec.PromisedThm(), &ctx.Proof
			}),
		})
		// The package reaches the theorem through the door's handle,
		// `<Name>Def` (the entry lint's handleName), and the field of
		// its kind: no variable is declared under the entry's name.
		entry.goRef = e.Name + "Def." + kind.String()
		switch kind {
		case proof.QuotientSurjectivity:
			qe.Surjectivity = entry
		case proof.QuotientInduct:
			qe.Induct = entry
		case proof.QuotientSound:
			qe.Sound = entry
		case proof.QuotientExact:
			qe.Exact = entry
		case proof.QuotientEq:
			qe.Eq = entry
		case proof.QuotientForallOnImage:
			qe.ForallOnImage = entry
		case proof.QuotientExistsOnImage:
			qe.ExistsOnImage = entry
		}
	}
	quotientByName[mq.Meta.Name()] = qe
	stampDoor(DoorCall{Door: "DefineQuotient", Name: e.Name, Type: e.Type},
		qe.Surjectivity, qe.Induct, qe.Sound, qe.Exact, qe.Eq, qe.ForallOnImage, qe.ExistsOnImage)
	return qe
}

// RegisterClassNotation declares ⁅x⁆ and the word `class` on a
// quotient's class map — the chapter door's and the session door's one
// registration — unless a class map already registered under the word
// takes an indistinguishable argument type (a second quotient over one
// carrier), in which case the class map is spelled by its name alone.
// Reports whether the notation was registered.
func RegisterClassNotation(mq *proof.MintedQuotient) bool {
	mgr := GetConstMetaManager()
	mkType := mq.Mk.Type()
	// The word reads by its argument's type alone, so two class maps
	// over one carrier — distinct codomains and all — are one word to
	// the parser: the carrier decides, not the constant's whole type.
	for _, prev := range mgr.OverloadConsts(ClassWord) {
		s := mgr.ConstSyntax(prev)
		if s == nil || s.Overload == nil {
			continue
		}
		dom, _, ok := funTypeParts(s.Overload.Type)
		if !ok {
			continue
		}
		_, ab := dom.Matches(mq.Def.Rho, func(core.VarType) bool { return true })
		_, ba := mq.Def.Rho.Matches(dom, func(core.VarType) bool { return true })
		if ab || ba {
			return false
		}
	}
	x := ext.Var("x", mq.Def.Rho)
	equation := core.MakeProp(ext.ForAll(x)(ext.Eq(ext.Apply(mq.Mk, x), ext.Apply(mq.Abs, ext.Apply(mq.Def.Rel, x)))).Core())
	syntax, err := constSyntaxOf(string(mq.Mk.Name()), equation, mkType, nil, ClassNotation, "", ClassWord, nil, false)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineQuotient: the class notation on %s: %v", mq.Mk.Name(), err))
	}
	mgr.RegisterConstSyntax(mq.Mk.Name(), syntax)
	return true
}

// quotientLiftDeps resolves the entries a lift reads at replay — each
// of its quotients' Sound and Exact, whose ServesAs bindings preload
// the conventional names. A quotient no family.DefineQuotient
// registered is an error by name.
func quotientLiftDeps(quotients []*proof.MintedQuotient) ([]*ProofEntry, error) {
	var out []*ProofEntry
	for _, mq := range quotients {
		qe, ok := quotientByName[mq.Meta.Name()]
		if !ok {
			return nil, fmt.Errorf("%s is a quotient type no family.DefineQuotient registered", mq.TypeText())
		}
		out = append(out, qe.Sound, qe.Exact)
	}
	return out, nil
}
