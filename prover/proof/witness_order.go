// witness_order.go — statement-order ground-cite witnesses.
//
// A ground cite (`Cite(dep, w…)` / `At(dep, w…)` in a By) installs the
// dep's canonical form (NormalizedThm ∘ Dep) and Specializes the
// installed ∀-hyp positionally. Normalize may REORDER the ∀-prefix
// relative to the dep's stated form (an implication's clause form puts
// each literal's variables in first-occurrence order; a sequent's
// ∀-closure runs in reverse free-occurrence order), so a positional
// witness tuple read against the install prefix is written in an order
// the dep's own statement does not show — a "witness order follows
// the NORMALIZED binder order" tax, paid in decoding comments at every
// affected site.
//
// The contract here removes the tax: THE WITNESS TUPLE IS READ IN THE
// DEP'S OWN STATED BINDER ORDER — the same left-to-right statement-slot
// rule the section-boundary closure parameters follow — and the engine
// computes the permutation onto the install prefix. The mapping is
// name-based: Normalize mostly preserves binder names, so the install
// prefix's names locate their slots in the statement.
//
// Normalize does not ALWAYS preserve a name: a binder that rides the
// DeBruijn round-trip's spare slot is restored under a fresh name
// (monoidal.Restrict's ∀P arrives in the prefix as Q), and a rewrite
// can mint a prefix binder no stated binder corresponds to at all
// (the set lemmas' ẋ). For a FULL grounding such a name must not fall
// back to positional silence — the measured failure mode is a
// type-correct WRONG instance whenever the reorder is a genuine
// permutation and two slots share a type (the Fibres-cites-Restrict
// incident). Instead, an unmatched prefix binder is resolved by
// ELIMINATION: at full arity the tuple grounds statement binders, so
// the unmatched slot's partner must be a stated binder that no other
// slot claimed, and its TYPE must agree — when exactly one such
// candidate exists the map is completed (correct even where the
// prefix also reordered), and otherwise the cite PANICS, naming both
// orders, rather than guess.
//
// A name the statement binds MORE THAN ONCE has no slot by name, but a
// binding of it on the statement's SPINE — the conclusion's ∀-chain
// read through its leading implications, the binders a stated-order
// tuple grounds — still has one by position. The monotonicity criteria
// state `… ∧ (∀x. a < x ∧ x < b ⇒ &0 ≤ f'(x)) ⇒ ∀x y. … ⇒ f(x) ≤ f(y)`:
// the antecedent's x stays existential under Normalize and the spine's
// x arrives in the prefix renamed (uʹ). So the elimination's candidates
// are the unclaimed once-bound names AND the spine's bindings of the
// twice-bound ones, each at the reading position of its own binding
// site.
//
// A PARTIAL grounding is read in the stated order too: its k witnesses
// name the statement's first k binders, which must then be the install
// prefix's k leading slots. On a named By premise that takes the clause
// form, the executor first moves them there — the ∀s of the clause's
// leading block commute (leadStatedBinders) — since the canonical
// labeling may put them anywhere in it.
//
// The remaining pass-through lanes are the deliberate, documented
// ones: no reference at all, a single witness, a partial grounding
// whose stated binders the install does not bind by name in its
// leading slots (renamed, or below a guard or an ∃), a prefix with
// duplicated names, and a reference that binds one name twice (the
// merged clause-pack shape — TestWitnessOrderCensus tracks those
// sites; the fix there is citing the right granularity, never witness
// order). In those lanes the tuple stays positional against the
// install prefix — up to the type-forced permutation below, which
// every lane but the single-witness one passes through.
//
// The permutation runs at consumption time, between install and
// Specialize, and only on the modern cite verbs (Cite / By): the
// legacy Action spellings and the recorded-replay surface
// (GoalStackNode.CiteSpecialize, package CiteSpecialize) are
// untouched, so their replay is bit-identical.
//
// A named dep now resolves to its STATED form (action.go,
// statedInstallForm) — what a witnessed premise, a spine cite, a
// grounding and an unpack install (a BARE By premise installs the
// closer's clause form instead, byPremise.clause, the stated form
// riding as the apply rung's head) — so the name map above is the
// identity for the common witnessed cite and the tuple's remaining
// work is TYPING. The tuple's
// types are hard constraints on the instance — Lean's explicit
// arguments fixing the implicit ones — and two doors here read them:
//
//   - witnessTypedForm types a polymorphic install form by its tuple
//     BEFORE the install, each guarded binder's type matched against
//     its witness's; where the tuple determines every type variable
//     the goal-anchored adaptation (typematch.TryAdaptLemmaTypes) has
//     no say, which is what keeps a goal holding two instances of one
//     constant (finite at A and at B) from steering the premise to the
//     wrong one.
//   - permuteByTypeIfIllTyped, after the install, reads a full tuple
//     whose positional order is ill-typed as the one type-consistent
//     order when the binder types are pairwise distinct — a tuple
//     authored against the prenex prefix (`∀m.∀P.` for a principle
//     stated `∀P.∀m.`) still grounds the stated form, and a tuple two
//     orders type-check stays positional so the grounding names it.

package proof

import (
	"fmt"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
)

// sectionReferenceForm keeps a section's stated binder names at the reference
// boundary. Reconstruction may rename them; WeakenTo derives the exact
// stated form from the certificate without forcing a deferred proof.
func sectionReferenceForm(n *GoalStackNode) Prop {
	stated := prop.WeakenTo(n.PromisedThm(), n.Goal)
	if stated == nil {
		panic("section cite: the certificate does not prove its stated goal")
	}
	return stated
}

// citeReferenceProp resolves the REFERENCE form of a cite target — the
// statement whose binder order the author's witness tuple follows.
// This is the target's RAW form (the dep cert as served, a section's
// certificate, an explicit Prop verbatim — and for a cross-type
// `ctx.AtTypes(dep, τ…)` target the dep's raw stated form at the
// instance types). resolveLemmaTarget's INSTALL form is the same
// statement for a hyp-free dep and its Normalize for a sequent-shaped
// one, so the two differ only where Normalize had to run. Returns nil
// when the target carries no reference (the permutation then stays
// identity).
func citeReferenceProp(s *Script, target any) Prop {
	switch t := target.(type) {
	case *TypedThm:
		return t.Reference()
	case typedInst:
		// Deferred AtTypes (proof.Inst): resolve, then the pair's raw
		// reference half exactly as the case above.
		return t.resolve(s).Reference()
	case _TypedSoleInst:
		// The sole-variable spelling of the case above (proof.InstSole).
		return t.resolve(s).Reference()
	case readingInst:
		// A law read at an instance (proof.Read): the derived statement
		// is its own stated form — under a resident hypothesis, at the
		// content the fact was bound to, no leaf being in hand
		// (resolveTargetAt derives it at a verb's leaf).
		return t.resolve(s, nil)
	case ThmCert:
		return t
	case *GoalStackNode:
		if !t.Proved() {
			return nil
		}
		return t.PromisedThm()
	case NamedDep:
		return s.Dep(t)
	case Prop:
		return t
	case Fact:
		// A Fact target (proof.Inst, a theorem wrapper's exact cite):
		// the reference is whatever the fact's own target carries — a
		// cite must not lose its reference to the spelling that
		// reached it (resolveLemmaTarget's Fact case, same doctrine;
		// without this the witness permutation silently degraded to
		// positional on the first normalized-reordered dep cited
		// through a wrapper).
		return citeReferenceProp(s, t.target)
	}
	return nil
}

// namedCiteReferenceProp reads the declaration's binder names for Where.
// Positional citations keep the certificate's reconstructed binder order.
func namedCiteReferenceProp(s *Script, target any) Prop {
	switch t := target.(type) {
	case *GoalStackNode:
		if !t.Proved() {
			return nil
		}
		return sectionReferenceForm(t)
	case Fact:
		return namedCiteReferenceProp(s, t.target)
	default:
		return citeReferenceProp(s, target)
	}
}

// forallPrefixBinders reads a term's leading ∀-binder variables,
// outer to inner. The second result is false when two binders share a
// name (no name-addressable slot map exists).
func forallPrefixBinders(t Term) ([]core.VarTerm, bool) {
	var vars []core.VarTerm
	seen := map[core.TermName]bool{}
	distinct := true
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			return vars, distinct
		}
		v := abs.Var()
		if seen[v.Name()] {
			distinct = false
		}
		seen[v.Name()] = true
		vars = append(vars, v)
		t = abs.Body()
	}
}

// guardedPrefixBinders reads the ∀-binders reachable through leading
// implications — the binders a witness tuple grounds under the guarded
// Specialize rung — and reports whether their names are distinct.
func guardedPrefixBinders(t Term) ([]core.VarTerm, bool) {
	vars, _ := ematch.StripGuardedForalls(t)
	seen := map[core.TermName]bool{}
	distinct := true
	for _, v := range vars {
		if seen[v.Name()] {
			distinct = false
		}
		seen[v.Name()] = true
	}
	return vars, distinct
}

// permuteByTypeIfIllTyped returns witnesses unchanged when they fit the
// binders positionally; otherwise, when every binder type is distinct
// and every witness matches exactly one of them, the permutation that
// fits. Any other case stays positional — the grounding then fails
// loudly, naming both. Runs on every full tuple at the end of the
// name map (see the header): a tuple authored against a prenex prefix
// that ordered the binders differently from the statement grounds the
// stated form wherever the types settle the order.
func permuteByTypeIfIllTyped(binders []core.VarTerm, witnesses []Term) []Term {
	if len(binders) != len(witnesses) {
		return witnesses
	}
	fits := true
	for i, b := range binders {
		if !b.Type().Equals(witnesses[i].Type()) {
			fits = false
			break
		}
	}
	if fits {
		return witnesses
	}
	for i := range binders {
		for j := range binders {
			if i != j && binders[i].Type().Equals(binders[j].Type()) {
				return witnesses
			}
		}
	}
	out := make([]Term, len(binders))
	used := make([]bool, len(witnesses))
	for i, b := range binders {
		found := -1
		for j, w := range witnesses {
			if !used[j] && b.Type().Equals(w.Type()) {
				found = j
				break
			}
		}
		if found < 0 {
			return witnesses
		}
		used[found] = true
		out[i] = witnesses[found]
	}
	return out
}

// forallPrefixNames is forallPrefixBinders reduced to the names — the
// spelling the census and the fixtures read. One traversal definition
// (a second walker that merely agreed today would drift silently).
func forallPrefixNames(t Term) ([]string, bool) {
	vars, distinct := forallPrefixBinders(t)
	names := make([]string, len(vars))
	for i, v := range vars {
		names[i] = string(v.Name())
	}
	return names, distinct
}

// spineBinder is one ∀ on a statement's spine — the conclusion's
// ∀-chain read through its leading implications, the binders a
// stated-order tuple grounds (ematch.StripGuardedForalls) — with the
// reading position of its own binding site.
type spineBinder struct {
	name string
	ty   core.HolType
	pos  int
}

// statementSlotOrder walks a statement and assigns each variable name
// its READING position: free variables at first occurrence and
// quantifier binders at their binding site, hypotheses before the
// conclusion. Every binding site takes a position of its own; a name's
// position is that of its FIRST binding. Names bound more than once
// (per-clause binders of a conjunction pack, an antecedent's binder
// reused on the spine) land in dup — they have no unique slot by name.
// binderType records, for each ∀/∃-BOUND name (not a free variable),
// the type it is first bound at, and spine the conclusion's spine
// binders in stated order — between them the candidate pool
// reorderWitnessesToInstall's elimination step draws from.
func statementSlotOrder(ref Prop) (pos map[string]int, dup map[string]bool, binderType map[string]core.HolType, spine []spineBinder) {
	pos = map[string]int{}
	dup = map[string]bool{}
	binderType = map[string]core.HolType{}
	next := 0
	bindQuant := func(v core.VarTerm, onSpine bool) {
		n := string(v.Name())
		slot := next
		next++
		if _, ok := pos[n]; ok {
			dup[n] = true
		} else {
			pos[n] = slot
		}
		if _, ok := binderType[n]; !ok {
			binderType[n] = v.Type()
		}
		if onSpine {
			spine = append(spine, spineBinder{name: n, ty: v.Type(), pos: slot})
		}
	}
	var walk func(t Term, onSpine bool)
	walk = func(t Term, onSpine bool) {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			bindQuant(abs.Var(), onSpine)
			walk(abs.Body(), onSpine)
			return
		}
		if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
			bindQuant(abs.Var(), false)
			walk(abs.Body(), false)
			return
		}
		if onSpine {
			// The spine runs through an implication's consequent; its
			// antecedent is read first, as the generic walk below reads it.
			if ante, rest, ok := ext.MatchesIMPLY(t); ok {
				walk(ante, false)
				walk(rest, true)
				return
			}
		}
		switch tt := t.(type) {
		case core.VarTerm:
			if _, ok := pos[string(tt.Name())]; !ok {
				pos[string(tt.Name())] = next
				next++
			}
		case core.AppliedTerm:
			walk(tt.Fun(), false)
			walk(tt.Arg(), false)
		case core.AbsTerm:
			walk(tt.Body(), false)
		}
	}
	pp := ref.AsProp()
	for i := 0; i < pp.NumHyps(); i++ {
		walk(pp.Hyp(i), false)
	}
	walk(pp.Conclusion(), true)
	return pos, dup, binderType, spine
}

// witnessOrderNote says, for a grounding that failed, which lane
// reorderWitnessesToInstall read the tuple in where that lane is not
// the name map an author assumes: a single witness grounds the install
// prefix's FIRST binder as written, and a tuple against a reference
// that binds a prefix name twice is read positionally against the
// install prefix (permuted by type only where that reading is
// ill-typed and the binder types are pairwise distinct). Empty where
// the tuple was mapped by name — then the failure is not the order's.
func witnessOrderNote(ref Prop, installed Term, witnesses []Term) string {
	prefix, _ := guardedPrefixBinders(installed)
	if len(prefix) < 2 || len(witnesses) == 0 {
		return ""
	}
	names := make([]string, len(prefix))
	for i, v := range prefix {
		names[i] = string(v.Name())
	}
	if len(witnesses) == 1 {
		return fmt.Sprintf("\n  (a single witness grounds the install prefix's first binder, %s, as written — the install prefix is (%s))",
			names[0], strings.Join(names, ", "))
	}
	if ref == nil {
		return ""
	}
	_, dup, _, _ := statementSlotOrder(ref)
	var twice []string
	for _, n := range names {
		if dup[n] {
			twice = append(twice, n)
		}
	}
	if len(twice) == 0 {
		return ""
	}
	distinct := true
	for i := range prefix {
		for j := i + 1; j < len(prefix); j++ {
			if prefix[i].Type().Equals(prefix[j].Type()) {
				distinct = false
			}
		}
	}
	permuted := "the binder types do not settle a permutation, so no slot was permuted"
	if distinct {
		permuted = "permuted by type only where that reading was ill-typed"
	}
	return fmt.Sprintf("\n  (the reference binds %s twice, so no slot is addressable by name: the tuple was read "+
		"positionally against the install prefix (%s), %s — write the tuple in that order, or restate the "+
		"reference so that each prefix binder is bound once)",
		strings.Join(twice, " and "), strings.Join(names, ", "), permuted)
}

// reorderWitnessesToInstall maps a witness tuple written in the
// reference statement's binder order onto the installed hyp's ∀-prefix
// order. A FULL grounding (one witness per prefix binder) is mapped by
// name; a PARTIAL one by name onto the leading slots when the stated
// binders are exactly those slots (see the header for how a clause
// install is made so). A single witness, a missing reference, a prefix
// with duplicated names and a reference that binds a prefix name twice
// (the clause-pack lane) pass through unchanged — positional against
// the install prefix. A prefix binder whose
// name the reference does not bind AT ALL is the rename/mint case and
// never falls back to positional at full arity: it is resolved by
// type-unique elimination — among the unclaimed once-bound names and
// the spine's bindings of the twice-bound ones — or the cite panics
// (see the header).
func reorderWitnessesToInstall(ref Prop, installed Term, witnesses []Term) []Term {
	if ref == nil || len(witnesses) < 2 {
		return witnesses
	}
	// The install's binders are read THROUGH its guards: a stated law
	// `∀op. A(op) ⇒ ∀f p s. …` grounds at [op f p s], exactly as the
	// Specialize rung instantiates it (ematch.StripGuardedForalls).
	prefix, distinct := guardedPrefixBinders(installed)
	if len(witnesses) < len(prefix) {
		// A PARTIAL tuple grounds the leading binders. It is read in
		// the STATED order like a full one: the reference's first k
		// binders are located in the prefix by name, and when they are
		// exactly the k leading slots (in any order — the prenex form
		// reorders) the tuple is mapped onto them; otherwise it stays
		// positional. (On a clause install the By executor has already
		// moved the stated binders to the front where the block binds
		// them — leadStatedBinders — so "otherwise" is a renamed or
		// guarded binder.) Either reading is then permuted by type where it
		// is ill-typed and the types settle it (a principle stated
		// `∀P.∀m. … ⇒ ∀x.P(x)` cited at (m, P) against its prenex habit).
		k := len(witnesses)
		leading := prefix[:k]
		if distinct {
			if mapped := mapStatedLeadingBinders(ref, leading, witnesses); mapped != nil {
				return permuteByTypeIfIllTyped(leading, mapped)
			}
		}
		return permuteByTypeIfIllTyped(leading, witnesses)
	}
	if !distinct || len(prefix) != len(witnesses) {
		return witnesses
	}
	pos, dup, binderType, spine := statementSlotOrder(ref)
	refPos := make([]int, len(prefix))
	matched := map[string]bool{}
	var unmatched []int
	for j, v := range prefix {
		n := string(v.Name())
		if dup[n] {
			// The reference binds this name more than once — the merged
			// clause-pack shape, or a stated principle whose consequent
			// re-binds a name its step hypothesis bound. No unique slot
			// exists; the contract is positional (TestWitnessOrderCensus
			// carries the site count) — and where the positional reading
			// is ILL-TYPED, the tuple is permuted by binder type when the
			// types are pairwise distinct (the prenex form presents
			// exactly that order, and such a tuple is authored against
			// it).
			return permuteByTypeIfIllTyped(prefix, witnesses)
		}
		if p, ok := pos[n]; ok {
			refPos[j] = p
			matched[n] = true
		} else {
			unmatched = append(unmatched, j)
		}
	}
	for _, j := range unmatched {
		refPos[j] = resolveRenamedPrefixBinder(ref, prefix, unmatched, j, matched, pos, dup, binderType, spine)
	}
	// Rank the install slots by reference position: the i-th author
	// witness fills the install slot with the i-th smallest reference
	// position. Insertion-ranking over the tiny slice.
	order := make([]int, 0, len(prefix))
	for j := range prefix {
		i := 0
		for i < len(order) && refPos[order[i]] < refPos[j] {
			i++
		}
		order = append(order, 0)
		copy(order[i+1:], order[i:])
		order[i] = j
	}
	identity := true
	out := make([]Term, len(witnesses))
	for i, j := range order {
		if i != j {
			identity = false
		}
		out[j] = witnesses[i]
	}
	if identity {
		return permuteByTypeIfIllTyped(prefix, witnesses)
	}
	return permuteByTypeIfIllTyped(prefix, out)
}

// maxWitnessReadingArity bounds the bijection search a full tuple's
// type reading runs when its positional reading is ill-typed.
const maxWitnessReadingArity = 7

// witnessTypeReading reads a witness tuple against an install form's
// guarded binders and returns the type instantiation the tuple FORCES:
// each binder's type matched against the type of the witness grounding
// it, every type variable of the form instantiable. A partial tuple
// grounds the leading binders. The positional reading is taken when it
// type-checks; when it does not, every bijection onto those binders is
// tried and a reading is accepted only when all type-consistent
// bijections agree on the instantiation (two that disagree would make
// the tuple's meaning the engine's guess, and the grounding names the
// miss instead). full reports that the tuple grounds every guarded
// binder; ok=false means no reading type-checks, or the tuple is
// longer than the prefix.
func witnessTypeReading(L Prop, witnesses []Term) (env []core.TypeSubst, full, ok bool) {
	env, _, full, ok = witnessTypeReadingWith(L, witnesses, utils.FullPredicate[core.VarType])
	return env, full, ok
}

// witnessTypeReadingWith uses the same tuple order while keeping the
// type letters excluded by instantiable rigid. Each witness is first
// read at its binder's type (FitWitness): a bare polymorphic constant's
// fresh letters take the binder's, and the tuple comes back so retyped
// (fitted), in the tuple's own order.
func witnessTypeReadingWith(L Prop, witnesses []Term, instantiable core.VarTypePredicate) (env []core.TypeSubst, fitted []Term, full, ok bool) {
	binders, _ := ematch.StripGuardedForalls(L.AsProp().Conclusion())
	n := len(witnesses)
	if n == 0 || n > len(binders) {
		return nil, nil, false, false
	}
	full = n == len(binders)
	binders = binders[:n] // a partial tuple grounds the leading binders
	read := func(order []int) ([]core.TypeSubst, []Term, bool) {
		var e []core.TypeSubst
		typed := make([]Term, n)
		for i, j := range order {
			w, fits := FitWitness(binders[j].Type(), witnesses[i], instantiable, e)
			if !fits || !core.MatchTypeInto(binders[j].Type(), w.Type(), instantiable, &e) {
				return nil, nil, false
			}
			typed[i] = w
		}
		return e, typed, true
	}
	order := make([]int, n)
	for i := range order {
		order[i] = i
	}
	if e, typed, ok := read(order); ok {
		return e, typed, full, true
	}
	if n > maxWitnessReadingArity {
		return nil, nil, full, false
	}
	var agreed []core.TypeSubst
	var agreedTyped []Term
	found, consistent := false, true
	forEachPermutation(order, func(o []int) {
		e, typed, ok := read(o)
		switch {
		case !ok:
		case !found:
			agreed, agreedTyped, found = e, typed, true
		case !sameTypeSubst(agreed, e):
			consistent = false
		}
	})
	if !found || !consistent {
		return nil, nil, full, false
	}
	return agreed, agreedTyped, full, true
}

// witnessTypedForm is the install form a WITNESSED polymorphic premise
// takes: the type instance its tuple forces, and — only where that
// leaves a type variable of the form undetermined (a partial tuple's
// later binders, a variable only the body mentions) — the goal-anchored
// adaptation for the rest, kept only where it agrees with the tuple.
// A form without type variables, and a tuple no reading type-checks,
// return as the goal-anchored adaptation alone would have them: the
// grounding then names the miss.
func witnessTypedForm(L Prop, witnesses []Term, goal Prop) Prop {
	if !ext.PropHasTypeVars(L) {
		return L
	}
	// The adaptation is of the form as handed in, so a theorem's
	// instance is a theorem (core.PropTypeInst) and a cite registers it
	// as known.
	adapt := func(p Prop) Prop {
		if adapted := typematch.TryAdaptLemmaTypes(p, goal); adapted != nil {
			return adapted
		}
		return p
	}
	env, _, ok := witnessTypeReading(L, witnesses)
	if !ok {
		return adapt(L)
	}
	// Identity entries (a type variable read at a same-named one) are
	// not instantiated: type variables are equal by name but the
	// adaptation sweep owns them by POINTER, and substituting the
	// goal's pointer for the lemma's makes the two look shared — the
	// sweep then renames the lemma's apart, and the instance lands at
	// fresh type variables the goal never meets.
	inst := L
	if subst := nonIdentityTypeSubst(env); len(subst) > 0 {
		inst = core.PropTypeInst(L, subst...)
	}
	if typeVarsDetermined(L, env) {
		return inst
	}
	if adapted := adapt(L); adapted != L {
		if _, _, ok := witnessTypeReading(adapted, witnesses); ok {
			return adapted
		}
	}
	return inst
}

// clauseTypedForWitnesses types a clause form for a witnessed premise.
//
// The tuple's STATED reading decides first: the witnesses' types, read
// against the binders the reference's stated order names
// (statedTypeReading), fix the instance the author wrote — the one the
// non-clause lane installs (witnessTypedForm). Where that reading
// determines every type letter of the form, that instance is the
// install and the goal is not consulted: a goal holding the law's
// constant at two instances (set_product.CrossSwap's leaf holds
// set_cross at (A, B) and at (B, A)) can then never take `At(InCross,
// s, t)` at the instance the author did not name, with the tuple
// permuted to fit it. Where the reading leaves a letter open (a partial
// tuple whose later binders or body alone mention it), the goal's
// adaptations of the read instance fill the rest, the first under which
// the stated reading still holds — the read letters rigid — and the read
// instance alone when none does; the grounding then names the miss.
//
// Without a stated reading — no reference, a stated binder the clause
// prefix does not bind once (Normalize renamed or merged it), a tuple
// ill-typed in the stated order (authored against the prenex prefix) —
// the positional reading decides: of every adaptation the goal offers
// (typematch.EnumerateLemmaTypeAdaptations — the single guess loses a
// goal that holds two instances of one constant), the first whose
// leading binder types the tuple fits; the unadapted form when none
// does. The tuple is read as the grounding will read it: in the
// REFERENCE's stated binder order, mapped onto the candidate's prefix by
// name (reorderWitnessesToInstall), then by type-permutation where the
// positional reading is ill-typed — a clause prefix that orders the
// binders differently from the statement (the normalizer's block sort
// puts `∀R. ∀op.` before a law stated `∀op. … ⇒ ∀R.`) would otherwise
// fit no candidate whenever two binders share a type, and the premise
// would install at its own letters and fail to ground.
func clauseTypedForWitnesses(L Prop, witnesses []Term, goal Prop, ref Prop) Prop {
	if env, ok := statedTypeReading(L, witnesses, ref, utils.FullPredicate[core.VarType]); ok {
		inst := L
		if subst := nonIdentityTypeSubst(env); len(subst) > 0 {
			inst = core.PropTypeInst(L, subst...)
		}
		if typeVarsDetermined(L, env) {
			return inst
		}
		read := map[core.TypeName]bool{}
		for _, e := range env {
			read[e.VarType.Name()] = true
		}
		rigid := func(v core.VarType) bool { return !read[v.Name()] }
		for _, cand := range typematch.EnumerateLemmaTypeAdaptations(inst.AsProp(), goal) {
			if _, ok := statedTypeReading(cand, witnesses, ref, rigid); ok {
				return cand
			}
		}
		return inst
	}
	for _, cand := range typematch.EnumerateLemmaTypeAdaptations(L.AsProp(), goal) {
		binders, _ := ematch.StripGuardedForalls(cand.Conclusion())
		if len(witnesses) > len(binders) {
			continue
		}
		fits := reorderWitnessesToInstall(ref, cand.Conclusion(), witnesses)
		fits = permuteByTypeIfIllTyped(binders[:len(witnesses)], fits)
		ok := true
		for i, b := range binders[:len(witnesses)] {
			if !b.Type().Equals(fits[i].Type()) {
				ok = false
				break
			}
		}
		if ok {
			return cand
		}
	}
	return L
}

// statedTypeReading reads a witness tuple's type instantiation of a
// clause form through the reference: the reference's first k stated
// binders (statedLeadingBinderNames) name the clause binders the tuple
// grounds, in the stated order, and each witness's type is matched
// against its binder's type in the form, the letters `instantiable`
// admits bound and the rest rigid. It is the author's reading of the
// tuple, the one a positional reading loses where the clause prefix
// orders the binders differently from the statement. ok=false when
// there is no reference, the reference binds fewer than k names, a
// stated name the form's prefix does not bind exactly once, or a
// witness's type does not match its binder's.
func statedTypeReading(L Prop, witnesses []Term, ref Prop, instantiable core.VarTypePredicate) (env []core.TypeSubst, ok bool) {
	if ref == nil || len(witnesses) == 0 {
		return nil, false
	}
	k := len(witnesses)
	stated := statedLeadingBinderNames(ref, k)
	if len(stated) != k {
		return nil, false
	}
	binders, _ := ematch.StripGuardedForalls(L.AsProp().Conclusion())
	slot := map[string]core.VarTerm{}
	twice := map[string]bool{}
	for _, b := range binders {
		n := string(b.Name())
		if _, seen := slot[n]; seen {
			twice[n] = true
		}
		slot[n] = b
	}
	for i, n := range stated {
		b := slot[n]
		if b.IsZero() || twice[n] {
			return nil, false
		}
		if !core.MatchTypeInto(b.Type(), witnesses[i].Type(), instantiable, &env) {
			return nil, false
		}
	}
	return env, true
}

// typeVarsDetermined reports whether every type variable occurring in
// p is read by env (mapped, or fixed at itself).
func typeVarsDetermined(p Prop, env []core.TypeSubst) bool {
	read := map[core.TypeName]bool{}
	for _, e := range env {
		read[e.VarType.Name()] = true
	}
	undetermined := func(v core.VarType) bool { return !read[v.Name()] }
	pp := p.AsProp()
	if ext.TermAnyTypeVar(pp.Conclusion(), undetermined) {
		return false
	}
	for h := range pp.HypIter() {
		if ext.TermAnyTypeVar(h, undetermined) {
			return false
		}
	}
	return true
}

// nonIdentityTypeSubst drops a reading's identity entries.
func nonIdentityTypeSubst(env []core.TypeSubst) []core.TypeSubst {
	var out []core.TypeSubst
	for _, e := range env {
		if !e.VarType.Equals(e.HolType) {
			out = append(out, e)
		}
	}
	return out
}

// sameTypeSubst compares two readings as maps from type variable to
// type, identity entries aside.
func sameTypeSubst(a, b []core.TypeSubst) bool {
	as := map[core.TypeName]core.HolType{}
	for _, e := range a {
		if !e.VarType.Equals(e.HolType) {
			as[e.VarType.Name()] = e.HolType
		}
	}
	seen := map[core.TypeName]bool{}
	for _, e := range b {
		if e.VarType.Equals(e.HolType) {
			continue
		}
		t, ok := as[e.VarType.Name()]
		if !ok || !t.Equals(e.HolType) {
			return false
		}
		seen[e.VarType.Name()] = true
	}
	return len(seen) == len(as)
}

// forEachPermutation calls f on every permutation of order (Heap's
// algorithm, in place — f must not retain the slice).
func forEachPermutation(order []int, f func([]int)) {
	n := len(order)
	c := make([]int, n)
	f(order)
	for i := 0; i < n; {
		if c[i] < i {
			if i%2 == 0 {
				order[0], order[i] = order[i], order[0]
			} else {
				order[c[i]], order[i] = order[i], order[c[i]]
			}
			f(order)
			c[i]++
			i = 0
		} else {
			c[i] = 0
			i++
		}
	}
}

// mapStatedLeadingBinders reads a partial tuple in the reference's
// stated order: the reference's first k distinct quantifier binders
// must be exactly the k leading install binders (by name, any order);
// the i-th witness then fills the slot of the i-th stated binder. nil
// when the reference does not bind them that way.
func mapStatedLeadingBinders(ref Prop, leading []core.VarTerm, witnesses []Term) []Term {
	k := len(leading)
	stated := statedLeadingBinderNames(ref, k)
	if len(stated) != k {
		return nil
	}
	slot := map[string]int{}
	for j, v := range leading {
		slot[string(v.Name())] = j
	}
	out := make([]Term, k)
	for i, n := range stated {
		j, ok := slot[n]
		if !ok {
			return nil
		}
		out[j] = witnesses[i]
	}
	return out
}

// statedLeadingBinderNames is the reference's first k distinct
// quantifier binders, read outside-in through leading implications —
// the binders a k-tuple written in the stated order grounds. Shorter
// than k when the statement binds fewer before its matrix.
func statedLeadingBinderNames(ref Prop, k int) []string {
	var stated []string
	seen := map[string]bool{}
	var walk func(t Term)
	walk = func(t Term) {
		if len(stated) >= k {
			return
		}
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			n := string(abs.Var().Name())
			if !seen[n] {
				seen[n] = true
				stated = append(stated, n)
			}
			walk(abs.Body())
			return
		}
		if _, rest, ok := ext.MatchesIMPLY(t); ok {
			walk(rest)
		}
	}
	walk(ref.AsProp().Conclusion())
	return stated
}

// leadStatedBinders completes the stated-order contract for a PARTIAL
// tuple on a CLAUSE install. A partial tuple grounds the leading slots
// of the install prefix, and mapStatedLeadingBinders reads it by name
// only when the statement's first k binders ARE those slots — but
// Normalize's canonical labeling may put them anywhere in the clause's
// leading ∀-block (LessEqTrans: stated ∀m n p, clause ∀n p m;
// SupMonoSubset: stated ∀s t b, clause ∀ẋ b s t with the pointwise ẋ
// of `s ≠ ∅` hoisted in front). Before this, the tuple then fell back
// to positional and grounded binders the author never named — silently
// the wrong instance when the types agreed. The ∀s of one block
// commute, so the install is re-generalized with the stated binders
// first, in stated order, the rest after in the clause's order — the
// kernel's instantiation of every binder, then re-generalization, a derivation from the clause form
// itself — and the tuple maps by name. nil when there is nothing to
// move (the stated binders already lead) or the reading is not total:
// a stated name the block does not bind (Normalize renamed it, or it
// sits below a guard or an ∃), or a name the block binds twice. Those
// keep the positional reading.
func leadStatedBinders(install, ref Prop, k int) Prop {
	if install == nil || ref == nil || k == 0 {
		return nil
	}
	stated := statedLeadingBinderNames(ref, k)
	if len(stated) != k {
		return nil
	}
	body, vars := prop.WrapProp(install).StripConclForAll()
	if k > len(vars) {
		return nil
	}
	slot := map[string]int{}
	for j, v := range vars {
		n := string(v.Name())
		if _, twice := slot[n]; twice {
			return nil
		}
		slot[n] = j
	}
	leading := true
	for _, n := range stated {
		j, ok := slot[n]
		if !ok {
			return nil
		}
		if j >= k {
			leading = false
		}
	}
	if leading {
		return nil
	}
	order := make([]core.VarTerm, 0, len(vars))
	placed := map[int]bool{}
	for _, n := range stated {
		j := slot[n]
		order = append(order, vars[j])
		placed[j] = true
	}
	for j, v := range vars {
		if !placed[j] {
			order = append(order, v)
		}
	}
	return body.ConclForAllList(order...)
}

// resolveRenamedPrefixBinder locates the stated binder behind install
// prefix binder j when Normalize did not preserve its name: at full
// arity the tuple grounds statement binders, so j's partner must be a
// stated quantifier binder no other prefix slot claimed, at j's own
// type. The candidates are the names the statement binds once, and the
// spine's bindings of the names it binds more than once: such a name
// has no slot by name, but its binding on the spine is one of the
// binders the tuple grounds, stays universal under Normalize, and was
// claimed by no prefix slot (a prefix that carries a twice-bound name
// took the positional lane before this one). Exactly one candidate
// completes the map, at the reading position of its own binding site —
// correct even where the prefix also REORDERED (the map is by
// identity, not position). Anything else panics: guessing positionally
// here is the measured silent-wrong-instance trap (a rename plus one
// shared type suffices), and the loud failure names both orders
// instead.
func resolveRenamedPrefixBinder(ref Prop, prefix []core.VarTerm, unmatched []int, j int,
	matched map[string]bool, pos map[string]int, dup map[string]bool,
	binderType map[string]core.HolType, spine []spineBinder) int {

	names := make([]string, len(prefix))
	for k, v := range prefix {
		names[k] = string(v.Name())
	}
	fail := func(diagnosis string) {
		panic(fmt.Sprintf(
			"ground cite: install binder %s : %s has no slot in the reference statement "+
				"(Normalize renamed or minted it) and %s — the stated-order witness tuple cannot "+
				"be mapped, and positional silence here is the wrong-instance trap.\n"+
				"install prefix: (%s)\nreference: %s\n"+
				"Fix: cite bare with the instance spelled in the claim, or align the dep's stated "+
				"binder order with its install prefix; XUGO_WITNESS_PROBE_DEP=<dep> prints both orders.",
			prefix[j].Name(), ext.FormatType(prefix[j].Type()), diagnosis,
			strings.Join(names, " "), prop.PrintProp(ref)))
	}
	// Two unmatched slots of one type admit two assignments — no
	// elimination can order them.
	for _, k := range unmatched {
		if k != j && prefix[k].Type().Equals(prefix[j].Type()) {
			fail(fmt.Sprintf("install binder %s shares its type (elimination cannot order the two)",
				prefix[k].Name()))
		}
	}
	var candidates []string
	slots := map[string]int{}
	for n, ty := range binderType {
		if !matched[n] && !dup[n] && ty.Equals(prefix[j].Type()) {
			candidates = append(candidates, n)
			slots[n] = pos[n]
		}
	}
	for _, b := range spine {
		if dup[b.name] && !matched[b.name] && b.ty.Equals(prefix[j].Type()) {
			candidates = append(candidates, b.name)
			slots[b.name] = b.pos
		}
	}
	switch len(candidates) {
	case 1:
		return slots[candidates[0]]
	case 0:
		fail("no unclaimed stated binder has its type (a normalization-minted binder cannot take a stated-order witness)")
	default:
		sort.Strings(candidates)
		fail(fmt.Sprintf("stated binders %v all have its type (ambiguous)", candidates))
	}
	panic("unreachable")
}
