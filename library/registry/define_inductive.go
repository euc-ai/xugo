// define_inductive.go — family.DefineInductive: the inductive-definition
// move as a chapter door (Isabelle's
// `inductive`). The emitted / hand-written twin of the session `define`
// RPC's `inductive:` payload: ONE call whose registration MINTS the
// relation as the smallest one closed under the stated rules (at
// package var init — the Define two-phase rationale: identity must
// exist before any later parse) and registers the theorems the
// definition comes with, each an entry whose Build re-derives it
// through the same composite step the session records
// (proof.DefineInductiveStep; prover/proof/define_inductive.go is the
// shared spine) — the record/emit/replay principle at ENTRY
// granularity, the DefineData / DefineType precedent.
//
// The rules are the author's, in text, with the definiendum applied at
// the declared parameters then its indices:
//
//	<Name>Rules    ∀p̄. rule₁ ∧ … ∧ ruleₘ                     (the rule set verbatim)
//	<Name>Induct   ∀p̄ P x̄. rules[P] ∧ R(p̄, x̄) ⇒ P(x̄)       (rule induction, the weak form)
//	<Name>Cases    ∀p̄. ∀ā. R(p̄, ā) ⇔ D₁(ā) ∨ … ∨ Dₘ(ā)      (one canonical disjunct per rule)
//	<Name>InductStrong  the same induction with each recursive premise
//	               carrying R(s̄) ALONGSIDE P(s̄) — absent when no rule
//	               has a premise to strengthen, since there it IS Induct
//
// A rule's canonical disjunct Dⱼ(ā) is `∃w̄. ā = t̄ ∧ Hs` — the rule's
// premises at the relation, with its variables existentially bound and
// its conclusion arguments equated to the subject — except that an
// index whose argument IS a rule variable is substituted rather than
// equated (the canonical form): finite's rules give `a = ∅ ∨ ∃x t. a
// = insert(x, t) ∧ finite(t)`, transitive closure's `R(a, b) ∨ ∃y.
// TC(R, a, y) ∧ TC(R, y, b)`.
//
// No definition entry is registered: the closure form the constant is
// minted with is not a proof surface — Unfold and def_expand refuse it
// by name — and a member that spells the relation names one of the
// entries in its Deps, as a datatype's consumers name the datatype's.
//
// The entries' statements are the door's; their keys are spelled in the
// literal (InductiveEntry.Keys), and registration normalizes nothing.

package registry

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
)

// InductiveEntry declares one inductive definition: the entry base
// name (the theorems register as Name+"Rules" / +"Induct" / +"Cases" /
// +"InductStrong"), the minted constant, its type, its parameters and
// its rules.
type InductiveEntry struct {
	Name string
	// Const is the minted relation's name; Type its type, which must
	// end in bool with at least one index beyond the parameters.
	Const string
	Type  string
	// Params names the leading arguments every occurrence of the
	// relation takes unchanged (the R of TC(R, x, y)); each is typed
	// off its slot of Type. Empty for an unparameterized relation.
	Params []string
	// Rules are the introduction rules, each `∀v̄. H₁ ∧ … ∧ Hₖ ⇒
	// Const(p̄, t̄)` or `∀v̄. Const(p̄, t̄)`, every Hᵢ a side condition
	// free of the relation or a positive premise `∀ū. G ⇒ Const(p̄,
	// s̄)` with G free of it — the supported fragment; anything else is
	// refused by name at registration.
	Rules []string
	// Deps declares the entries minting the constants the rules
	// spell; every derived entry carries them.
	Deps []EntryLike
	// Keys spells the keys of the entries the definition registers.
	Keys InductiveKeys
}

// InductiveKeys is the keys of an inductive definition's entries, one
// field per entry: each the normalized key of that entry's statement,
// as ProofEntry.Key is a member's, under the field named by the entry's
// suffix. The door reads them and normalizes nothing. A principle's
// statement grows with the rules and their binders — a relation of
// twenty rules has principles that take over a second each to
// normalize — and every process that links the corpus runs the door,
// so a computed key would be paid at every start. An entry whose key is
// left out registers unminted, and the key gate (TestEntryKeyIsOwnKey)
// reports the value and writes it under XUGO_PASTE_KEYS, as it does a
// member's. InductStrong is the key of the strengthened induction,
// spelled exactly where the definition has that entry.
type InductiveKeys struct {
	Rules        string
	Induct       string
	Cases        string
	InductStrong string
}

func (keys InductiveKeys) of(k proof.InductiveTheoremKind) string {
	switch k {
	case proof.InductiveRules:
		return keys.Rules
	case proof.InductiveInduct:
		return keys.Induct
	case proof.InductiveCases:
		return keys.Cases
	case proof.InductiveInductStrong:
		return keys.InductStrong
	}
	panic(fmt.Sprintf("InductiveKeys.of: unknown kind %v", k))
}

// InductiveEntries is DefineInductive's handle: the registered entries
// plus the minted identity.
type InductiveEntries struct {
	Rules  *ProofEntry
	Induct *ProofEntry
	Cases  *ProofEntry
	// InductStrong is nil when no rule has a premise to strengthen —
	// there the strengthened principle IS Induct.
	InductStrong *ProofEntry
	Const        core.ConstTerm
}

// Entry returns the entry for one derived-theorem kind.
func (ie *InductiveEntries) Entry(k proof.InductiveTheoremKind) *ProofEntry {
	switch k {
	case proof.InductiveRules:
		return ie.Rules
	case proof.InductiveInduct:
		return ie.Induct
	case proof.InductiveCases:
		return ie.Cases
	case proof.InductiveInductStrong:
		return ie.InductStrong
	}
	panic(fmt.Sprintf("InductiveEntries.Entry: unknown kind %v", k))
}

// DefineInductive mints the relation at registration and registers its
// theorems (see the file comment). Init-time failures panic — a
// rule that does not parse, a premise outside the fragment, a name that
// is not free — is a broken package, not a replay finding.
func (f *Family) DefineInductive(e InductiveEntry) *InductiveEntries {
	e.Type = dsl.OneLine(e.Type)
	if e.Name == "" || e.Const == "" || e.Type == "" {
		panic("registry.DefineInductive: Name, Const and Type are all required")
	}
	if len(e.Rules) == 0 {
		panic(fmt.Sprintf("registry.DefineInductive(%s): at least one rule is required", e.Name))
	}
	mgr := GetConstMetaManager()
	// The chapter takes the name first: a name that is not free names
	// why (another chapter's mint, or an engine built-in).
	if err := mgr.ClaimName(core.TermName(e.Const)); err != nil {
		panic(fmt.Sprintf("registry.DefineInductive(%s): %v", e.Name, err))
	}
	// The rules read in the chapter's own dialect, exactly as a
	// definition's equations do (define.go): the syntax table lowers a
	// declared notation and the family's instance bindings complete
	// the implicit components.
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
	mintEnv := &proof.ProverEnv{ProofService: &proof.ProofService{
		LoadConstMeta:        mgr.LoadConstMeta,
		LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
		Syntax:               mgr,
		TypeArity:            mgr.TypeArity,
	}}
	rules := make([]core.Prop, len(e.Rules))
	var defVar core.VarTerm
	var params []core.VarTerm
	for i, text := range e.Rules {
		r, dv, pv, err := proof.ParseInductiveRule(text, e.Const, e.Type, e.Params, base)
		if err != nil {
			panic(fmt.Sprintf("registry.DefineInductive(%s): %v", e.Name, err))
		}
		rules[i], defVar, params = r, dv, pv
	}
	d, err := proof.AnalyzeInductiveDefinition(defVar, params, rules)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineInductive(%s): %v", e.Name, err))
	}
	c, err := proof.MintInductiveDefinition(mintEnv, d)
	if err != nil {
		panic(fmt.Sprintf("registry.DefineInductive(%s): %v", e.Name, err))
	}

	paramTerms := make([]core.Term, len(d.Params))
	for i, p := range d.Params {
		paramTerms[i] = p
	}
	var deps []EntryLike
	for _, dep := range e.Deps {
		deps = withDep(deps, dep.Entry())
	}
	ie := &InductiveEntries{Const: c}
	minted := false
	kinds := d.Kinds()
	if e.Keys.InductStrong != "" && !slices.Contains(kinds, proof.InductiveInductStrong) {
		panic(fmt.Sprintf("registry.DefineInductive(%s): Keys spells InductStrong, and no rule has a premise to strengthen: "+
			"the definition registers no %sInductStrong entry — drop the key", e.Name, e.Name))
	}
	for _, kind := range kinds {
		stmt := d.Stmt(c, kind)
		entry := f.addDeclared(ProofEntry{
			Name: e.Name + kind.EntrySuffix(),
			// The literal spells the key (InductiveKeys); one left out
			// registers unminted.
			Key:        e.Keys.of(kind),
			Definition: proof.InductiveDefinitionShape(kind),
			defines:    mintedOnce(&minted, []string{e.Const}),
			Deps:       deps,
			// The statement was computed at registration: the entry's
			// statement and the Build's section goal are one value (the
			// Define precedent).
			stated: stmt,
			Build: Bare(func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
				ctx := f.NewScript(env)
				sec := ctx.Section(stmt)
				sec.Do(proof.DefineInductiveStep(c, paramTerms, d.RuleTerms))
				if !sec.Proved() {
					panic(fmt.Sprintf("registry.DefineInductive(%s): the %v derivation did not close",
						e.Name, kind))
				}
				return sec.PromisedThm(), &ctx.Proof
			}),
		})
		switch kind {
		case proof.InductiveRules:
			ie.Rules = entry
		case proof.InductiveInduct:
			ie.Induct = entry
		case proof.InductiveCases:
			ie.Cases = entry
		case proof.InductiveInductStrong:
			ie.InductStrong = entry
		}
	}
	stampDoor(DoorCall{Door: "DefineInductive", Name: e.Name}, ie.Rules, ie.Induct, ie.Cases, ie.InductStrong)
	return ie
}
