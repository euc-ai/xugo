// define_spec.go — family.DefineSpec: the form of the
// definition move's `spec:` shape (the composite is
// prover/proof/step_define.go).
// One or more constants introduced by CHOICE against a
// specification, with the author's whole
// contribution reduced to the two surfaces that are mathematics: the
// SPECIFICATION statement, and the proof of its POINTWISE existence.
// The ε-witness Skolemization, the name-tag conditioning, and the
// bridge chain run inside the composite's reconstruct
// (CompileSpecExistence), never at the authoring site.
//
// The constants are minted HERE, at registration, as the nested
// tag-free ε chain — the define family's registration-time mint
// discipline, with the same exclusive ConstMetaManager registration.
// The door claims each name first, so a group is either wholly fresh
// or a collision with a chapter mint, which errors.

package registry

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
)

// SpecConst declares one constant of a spec definition: its name and
// its type in text form, and — for a name the text DSL keeps for its
// own surface (nat_div, nat_mod) or cannot spell — the stand-in the Spec text
// spells it by; the constant is minted under Const. Overload is the
// word a text may write for the constant among the constants of its
// kind (`div` on nat_div and int_div, `rem` on nat_mod and int_rem),
// read as DefEntry.Overload is: the arguments pick the constant, the
// chapter spelling prints the word, and the Spec text itself spells
// the constant by its stand-in, the word not being registered until
// the mint.
type SpecConst struct {
	Const    string
	Type     string
	Spelled  string
	Overload string
}

// SpecEntry declares one spec definition member.
type SpecEntry struct {
	// Name is the registered entry's bare name (family-prefixed by
	// Add, like any member).
	Name string
	// Key is the entry's own key, spelled in source: as DefEntry.Key.
	Key string
	// Consts are the spec-defined constants in DEFINITION ORDER — the
	// order the stored existence claims nest (the specification's
	// chain): each constant's claim may carry the later ones as inner
	// function existentials.
	Consts []SpecConst
	// Spec is the characterizing statement literal: the specification
	// at the constants, each applied at ONE fixed argument form over
	// the statement's ∀-binders.
	Spec string
	// Existence closes the pointwise obligation the composite surfaces —
	// ∀binders. ∃values. spec-at-values — the author's mathematics (only
	// ceremony is automated). The value form hosts env-free actions (the
	// claim sites' one-cite shape).
	Existence []proof.Action
	// ExistenceBody is Existence's ctx-hosted form — for a proof that
	// needs the section Script (const/var declarations, env-bound
	// constructors like InductStep or MakePropText). Called inside
	// Build with the entry's own Script; its result closes the same
	// obligation. This is the form emit-section renders. Exactly one
	// of Existence / ExistenceBody must be set.
	ExistenceBody func(ctx *proof.Script) []proof.Action
	// Deps — the usual dep declaration; the existence proof's
	// citations resolve here. A specification applying a constant at a
	// pair literal reads the pair-projection rows (fst/snd), so it
	// declares the entries serving them (the pairs chapter's);
	// registration panics when they are missing.
	Deps []EntryLike
}

// specExistenceLabel is the obligation Case's fixed label — the
// section's one child, whatever the specification.
const specExistenceLabel = "existence: the specification is satisfiable at every point"

// DefineSpec registers a spec definition member. Init-time failures
// panic — a specification that cannot parse, analyze, or (in fresh
// mode) mint is a broken package, not a replay finding. The entry's
// statement is the door's own; its Key is spelled in source
// (SpecEntry.Key), and registration computes none.
func (f *Family) DefineSpec(e SpecEntry) *ProofEntry {
	if e.Name == "" || len(e.Consts) == 0 || e.Spec == "" {
		panic("registry.DefineSpec: Name, Consts and Spec are all required")
	}
	if len(e.Existence) == 0 && e.ExistenceBody == nil {
		panic(fmt.Sprintf(
			"registry.DefineSpec(%s): an Existence proof is required — the "+
				"pointwise obligation is the author's (R1)", e.Name))
	}
	if len(e.Existence) > 0 && e.ExistenceBody != nil {
		panic(fmt.Sprintf(
			"registry.DefineSpec(%s): Existence and ExistenceBody are one proof "+
				"in two forms — set exactly one", e.Name))
	}

	mgr := GetConstMetaManager()
	// The specification reads in the chapter's own dialect, as a
	// definition's equations do (Define): the syntax table lowers a
	// declared notation (`|n|` is `int_abs(n)`) and the family's instance
	// bindings complete the implicit components it leaves out.
	base := &dsl.ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if meta, ok := mgr.LoadConstMeta(core.TermName(name)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
		Syntax:           mgr,
		TypeResolver:     mgr.TypeArity,
		ImplicitBindings: f.implicit,
		CoerceDomain:     f.CoerceDomain(),
	}

	spelled := make([]string, len(e.Consts))
	types := make([]string, len(e.Consts))
	names := make([]core.TermName, len(e.Consts))
	for i, sc := range e.Consts {
		if sc.Const == "" || sc.Type == "" {
			panic(fmt.Sprintf("registry.DefineSpec(%s): Consts[%d] needs Const and Type",
				e.Name, i))
		}
		// The chapter takes the name: an inventory copy is dropped, a
		// chapter mint errors.
		if err := mgr.ClaimName(core.TermName(sc.Const)); err != nil {
			panic(fmt.Sprintf("registry.DefineSpec(%s): %v", e.Name, err))
		}
		spelled[i], types[i], names[i] = sc.Const, sc.Type, core.TermName(sc.Const)
		if sc.Spelled != "" {
			spelled[i] = sc.Spelled
		}
	}
	stmt, defVars, err := proof.ParseSpecStatement(e.Spec, spelled, types, base)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineSpec(%s): %v", e.Name, err))
	}
	// The words the constants declare, read against their stated types;
	// registered once the mint has made the names constants.
	words := make([]*dsl.Overload, len(e.Consts))
	for i, sc := range e.Consts {
		if sc.Overload == "" {
			continue
		}
		o, err := overloadOf(sc.Overload, sc.Const, defVars[i].Type(), nil)
		if err != nil {
			panic(fmt.Sprintf("registry.DefineSpec(%s): Consts[%d] Overload %q: %v", e.Name, i, sc.Overload, err))
		}
		words[i] = o
	}
	mintEnv := &proof.ProverEnv{ProofService: &proof.ProofService{
		LoadConstMeta:        mgr.LoadConstMeta,
		LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
		Syntax:               mgr,
		TypeArity:            mgr.TypeArity,
	}}
	consts, goal, err := proof.MintSpecDefinitionAs(mintEnv, stmt, defVars, names)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineSpec(%s): %v", e.Name, err))
	}
	var notations map[string]string
	for i, o := range words {
		if o == nil {
			continue
		}
		mgr.RegisterConstSyntax(names[i], &dsl.ConstSyntax{Overload: o})
		if notations == nil {
			notations = map[string]string{}
		}
		notations[string(names[i])] = e.Consts[i].Overload
	}
	sd, err := proof.AnalyzeSpecGoal(goal, consts)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineSpec(%s): %v", e.Name, err))
	}
	// The pair-projection rows the compiler reads by name: typed deps
	// on the pairs chapter, whose ServesAs binds them under
	// the fst/snd names.
	if specNeedsPairRows(sd) {
		for _, row := range []string{proof.SpecFstName, proof.SpecSndName} {
			if !Serves(e.Deps, row) {
				panic(fmt.Sprintf(
					"registry.DefineSpec(%s): the specification applies a constant at a pair "+
						"literal, so its compile reads %s — declare the entry that proves it in Deps",
					e.Name, row))
			}
		}
	}

	constTerms := make([]core.Term, len(consts))
	for i, c := range consts {
		constTerms[i] = c
	}
	defined := make([]string, len(names))
	for i, n := range names {
		defined[i] = string(n)
	}
	existence := e.Existence
	existenceBody := e.ExistenceBody
	return f.addDeclared(ProofEntry{
		Name:        e.Name,
		Key:         e.Key,
		Definition:  proof.DefinitionSpec,
		defines:     defined,
		notations:   notations,
		Deps:        e.Deps,
		depsSpelled: true,
		// The characterizing statement was computed at registration:
		// the entry's statement and the Build's section goal are one
		// value, not two spellings.
		stated: goal,
		Build: Bare(func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := f.NewScript(env)
			acts := existence
			if existenceBody != nil {
				acts = existenceBody(ctx)
			}
			sec := ctx.Section(goal)
			sec.Do(proof.DefineSpecStep(constTerms,
				proof.MakeCase(specExistenceLabel, acts...)))
			if !sec.Proved() {
				panic(fmt.Sprintf(
					"registry.DefineSpec(%s): the spec section did not close — does "+
						"the Existence proof close the pointwise obligation?", e.Name))
			}
			return sec.PromisedThm(), &ctx.Proof
		}),
	})
}

// specNeedsPairRows reports whether any constant is applied at a pair
// literal — the shapes whose compile consumes the served fst/snd
// rows.
func specNeedsPairRows(sd *proof.SpecDefinition) bool {
	for _, args := range sd.AppArgs {
		for _, a := range args {
			if isPairLiteralTerm(a) {
				return true
			}
		}
	}
	return false
}

// isPairLiteralTerm matches the pair constructor applied to two
// arguments.
func isPairLiteralTerm(t core.Term) bool {
	head, args := ext.MatchesApply(t)
	hc, ok := head.AsConst()
	return ok && len(args) == 2 && hc.Name() == ext.CommaConstMeta.Name()
}
