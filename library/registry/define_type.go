// define_type.go — family.DefineType: the type-definition move
// as a chapter door. The emitted / hand-written
// twin of the session `define` RPC's `typedef:` payload: ONE call whose
// registration MINTS the type with its abs/rep constant pair (at
// package var init — the Define two-phase rationale: identity must
// exist before any later parse) and registers the two theorems a type
// definition comes with, each an entry whose Build re-derives it
// through the same composite step the session records
// (proof.DefineTypeStep; prover/proof/define_type.go is the shared
// spine) — the record/emit/replay principle at ENTRY granularity.
//
// The predicate is the author's, in text. The inhabitation comes one
// of two ways. TRIVIAL — `∃x. P(x)` holds by normalization alone (the
// pair shape is inhabited by any pair, an equivalence-class shape by
// any class) — is proved at registration by the normalizer and
// recorded as a certificate: pure logic, no entry. An EXISTENCE entry
// — `⊢ ∃x. P(x)` with mathematical content (is_num at ind_zero, a slope)
// — is taken as a PROMISE: at init nothing is proved, the kernel
// records the existence statement only, and every proved theorem is
// derived at replay from the dep's certificate (the composite's one
// child is the inhabitation, closed by citing the dep). Forcing the
// promise itself — the corpus seam's TypeDefSourceThm path — runs the
// entry's proof through registry.ForceEntry, so no path trusts the
// inhabitation.
//
// A trivial inhabitation is never an entry: a statement the normalizer
// decides has the key of ⊤, which no entry may carry (two such entries
// would collide, and the identity relation reads every tautology as
// one theorem). So the door takes no Existence for it, and refuses one
// that the normalizer would have decided.
//
// The two entries' statements are the door's own, keys computed from
// the statements at registration:
//
//	<Name>Retraction   ∀a:T. abs(rep(a)) = a
//	<Name>Membership   ∀r:ρ. P(r) ⇔ rep(abs(r)) = r     (P(r) β-reduced)
//
// The abs/rep names are claimed first (a name another chapter minted
// refuses). MetaType identity is by name and arity, so every statement
// that spells the type denotes the one type the door minted.

package registry

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// TypeEntry declares one type definition: the entry base name (the
// two theorems register as Name+"Retraction" / Name+"Membership"), the
// minted type's name, the abs/rep constant names, the representing
// predicate as a closed λ in text, and the entry proving the type
// inhabited.
type TypeEntry struct {
	Name string
	// Type is the minted type's name; its parameters are the type
	// variables of Pred, in first-occurrence order.
	Type string
	// Abs and Rep name the bijection: abs : ρ → T(σ), rep : T(σ) → ρ.
	Abs, Rep string
	// Pred is the representing predicate — a closed λ over the
	// representation type ρ, e.g. "λr:(A → B → bool). ∃a:A. ∃b:B. r =
	// mk_pair(a, b)". Every constant it mentions must already resolve.
	Pred string
	// Existence is the chapter's inhabitation theorem, for a predicate
	// whose ∃x:ρ. Pred(x) the normalizer does not decide: its statement
	// must be exactly that, the predicate written out under the binder
	// — or, with Witness, the applied form Pred(Witness), the theorem
	// the basic type definition takes (`is_num(ind_zero)`). The replay
	// checks the two agree (the proved inhabitation must be the
	// composite's own child statement) — a mismatch fails the Build
	// loudly. Nil when the inhabitation is trivial.
	Existence EntryLike
	// Witness is the closed term of ρ at which Existence states the
	// membership, when it states the applied form rather than ∃. For a
	// λ-predicate the entry states that membership with the redex
	// reduced — `∀L. closed ⇒ L(w)`, not `(λa. …)(w)` — and the
	// composite bridges by β.
	Witness string
	// Deps are further entries the derivations read; Existence is
	// always one.
	Deps []EntryLike
}

// TypeEntries is DefineType's handle: the two registered theorem
// entries plus the minted identity.
type TypeEntries struct {
	Retraction *ProofEntry
	Membership *ProofEntry
	Meta       core.MetaType
	Abs, Rep   core.ConstTerm
	Pred       core.Term
}

// typeDefInhabitationLabel labels the composite's inhabitation child in
// a chapter Build.
const typeDefInhabitationLabel = "the representation type is inhabited"

// DefineType mints the type at registration and registers its two
// theorems (see the file comment). Init-time failures panic — a
// predicate that does not parse, a name that is not free, a type
// name already in use (proof.MintTypeDefinition refuses it: a second
// definition of one type is an inconsistency, not a shadowing) — is a
// broken package.
func (f *Family) DefineType(e TypeEntry) *TypeEntries {
	e.Type = dsl.OneLine(e.Type)
	if e.Name == "" || e.Type == "" || e.Abs == "" || e.Rep == "" || e.Pred == "" {
		panic("registry.DefineType: Name, Type, Abs, Rep and Pred are all required")
	}
	if err := proof.CheckMintedTypeName(e.Type); err != nil {
		panic(fmt.Sprintf("registry.DefineType(%s): %v", e.Name, err))
	}
	mgr := GetConstMetaManager()
	for _, n := range []string{e.Abs, e.Rep} {
		if err := mgr.ClaimName(core.TermName(n)); err != nil {
			panic(fmt.Sprintf("registry.DefineType(%s): %v", e.Name, err))
		}
	}

	// The predicate: a closed λ over ρ, read under the manager's
	// resolution with the strict switches on.
	scope := &dsl.ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if meta, ok := mgr.LoadConstMeta(core.TermName(name)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
		TypeResolver:       mgr.TypeArity,
		StrictResolution:   true,
		StrictMint:         true,
		FreshenMetaLetters: true,
	}
	res := dsl.ParseTermTextInScope(e.Pred, nil, scope, nil)
	if len(res.Errors) > 0 {
		panic(fmt.Sprintf("registry.DefineType(%s): parse Pred: %s", e.Name, res.Errors[0].Message))
	}
	pred := res.Term.Core()
	analyzed, err := proof.AnalyzeTypeDefinition(pred, nil)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineType(%s): %v", e.Name, err))
	}
	var witness core.Term
	if e.Witness != "" {
		wres := dsl.ParseTermTextInScope(e.Witness, nil, scope, analyzed.Rho)
		if len(wres.Errors) > 0 {
			panic(fmt.Sprintf("registry.DefineType(%s): parse Witness: %s", e.Name, wres.Errors[0].Message))
		}
		witness = wres.Term.Core()
		if analyzed, err = proof.AnalyzeTypeDefinition(pred, witness); err != nil {
			panic(fmt.Sprintf("registry.DefineType(%s): %v", e.Name, err))
		}
	}
	td := analyzed

	// The inhabitation the mint records — the ⊢ P(_) source every
	// derivation must hand TypeDefExpand. Trivial: the normalizer's
	// certificate. An entry: a promise that, if ever forced, proves
	// itself through the entry.
	var source core.Prop
	var existence *ProofEntry
	if e.Existence != nil {
		existence = e.Existence.Entry()
	}
	switch {
	case e.Witness != "" && existence == nil:
		panic(fmt.Sprintf("registry.DefineType(%s): Witness names the point Existence states the membership at — give Existence", e.Name))
	case td.Trivial && existence != nil:
		panic(fmt.Sprintf("registry.DefineType(%s): %s holds by normalization — its entry would carry the key of ⊤; "+
			"drop Existence", e.Name, proof.PrintTerm(td.Exists.Conclusion())))
	case td.Trivial:
		source = td.TrivialSource()
	case existence == nil:
		panic(fmt.Sprintf("registry.DefineType(%s): %s does not hold by normalization — "+
			"prove it as an entry and pass it as Existence",
			e.Name, proof.PrintTerm(td.Exists.Conclusion())))
	default:
		source = core.Promise(td.Applied, func(f core.Forcer) core.ThmCert {
			if ForceEntry == nil {
				panic(fmt.Sprintf("registry.DefineType(%s): the inhabitation promise was forced with no entry forcer "+
					"installed — replay derives from the proved dep %s; a corpus seam installs registry.ForceEntry",
					e.Name, existence.Name))
			}
			return f.Force(core.AsThm(td.SourceFromObligation(ForceEntry(f, existence))))
		})
	}

	mintEnv := &proof.ProverEnv{ProofService: &proof.ProofService{
		LoadConstMeta:        mgr.LoadConstMeta,
		LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
		Syntax:               mgr,
		TypeArity:            mgr.TypeArity,
		RangeConstMeta:       mgr.Range,
	}}
	md, err := proof.MintTypeDefinition(mintEnv, td, core.TypeName(e.Type), core.TermName(e.Abs), core.TermName(e.Rep), source)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineType(%s): %v", e.Name, err))
	}

	var deps []EntryLike
	if existence != nil {
		deps = withDep(deps, existence)
	}
	for _, d := range e.Deps {
		deps = withDep(deps, d.Entry())
	}
	te := &TypeEntries{Meta: md.Meta, Abs: md.Abs, Rep: md.Rep, Pred: pred}
	minted := false
	register := func(kind proof.TypeDefTheoremKind) *ProofEntry {
		stmt := md.Stmt(kind)
		// The entry's key is computed from its statement, not spelled:
		// this door registers several entries from one literal, and none
		// has a literal of its own to spell one in (ProofEntry.Key).
		normalized, _ := prop.Normalize(stmt)
		entry := f.addDeclared(ProofEntry{
			Name:        e.Name + kind.String(),
			Key:         string(normalized.AlphaKey()),
			Deps:        deps,
			defines:     mintedOnce(&minted, []string{e.Abs, e.Rep}),
			definesType: e.Type,
			// The statement was computed at registration: the entry's
			// statement and the Build's section goal are one value (the
			// Define precedent).
			stated: stmt,
			Build: Bare(func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
				ctx := f.NewScript(env)
				sec := ctx.Section(stmt)
				// The inhabitation child, when there is one, closes by
				// the dep's certificate — harness-installed, never the
				// promise — as a known theorem: the dep must state the
				// child (α-equal), the same agreement the promise's force
				// demands, so an entry proving something else fails the
				// Build loudly.
				var cases []proof.Case
				if existence != nil {
					inhabitation := ctx.Dep(existence)
					if inhabitation.NumHyps() != 0 || !inhabitation.Conclusion().AlphaEquals(td.Obligation.Conclusion()) {
						panic(fmt.Sprintf("registry.DefineType(%s): %s proves %s, not the inhabitation %s",
							e.Name, existence.Name, proof.PrintTerm(inhabitation.Conclusion()), proof.PrintTerm(td.Obligation.Conclusion())))
					}
					cases = append(cases, proof.MakeCase(typeDefInhabitationLabel, proof.CiteKnown(inhabitation)))
				}
				sec.Do(proof.DefineTypeStep(md.Abs, cases...))
				if !sec.Proved() {
					panic(fmt.Sprintf("registry.DefineType(%s): the %v derivation did not close — does %s prove the "+
						"inhabitation as stated?", e.Name, kind, existence.Name))
				}
				return sec.PromisedThm(), &ctx.Proof
			}),
		})
		// The package reaches the theorem through the door's handle,
		// `<Name>Def` (the entry lint's handleName), and the field of
		// its kind: no variable is declared under the entry's name.
		entry.goRef = e.Name + "Def." + kind.String()
		return entry
	}
	te.Retraction = register(proof.TypeDefRetraction)
	te.Membership = register(proof.TypeDefMembership)
	stampDoor(DoorCall{Door: "DefineType", Name: e.Name, Type: e.Type}, te.Retraction, te.Membership)
	return te
}
