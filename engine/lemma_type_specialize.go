package engine

import (
	"fmt"
	"sort"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/utils"
)

// buildSpecializedLemma applies an agent-supplied type substitution to a
// lemma's Prop. Each map entry is a (type-variable name, type
// spelling) pair: the spelling is parsed via dsl.ParseTypeText (so values
// like `?71152`, `num`, `num→bool`, `var:A` are all accepted), and the
// substitution `name := <parsed type>` is applied via core.PropTypeInst.
//
// Validates that every supplied name actually appears as a type variable
// in the lemma — a typo'd name fails fast with a list of the lemma's
// available type-var names, rather than silently producing a no-op
// substitution. Empty map returns the lemma unchanged.
//
// The targets are type expressions read in the goal's scope, so a
// letter a target spells that the goal spells too names the goal's own
// type variable: `{"A": "A"}` at a goal holding F : field_ops(A) asks
// for the instance at that A. goalLetters admits these letters, and the
// term pass that follows (resolveTermSpecializeWitnesses,
// buildTermSpecializedLemma) holds a letter it admits fixed — neither
// freshened apart from the goal's nor bound by a witness — so the
// instance installs at the letter asked for, where a letter taken for
// the lemma's own that no witness binds is renamed apart from the
// goal's (typematch.ResidualLetterNames). A target letter the goal does
// not spell stays the lemma's own: open to the witnesses, and keeping
// its name where none binds it.
//
// This is the single chokepoint where agent-supplied `type_specialize`
// (the JSON tactic-input field) becomes a specialized Prop. The
// specialized Prop then flows through the existing record / emit /
// replay infrastructure unchanged — see _LemmaPreserveTactic.lemma +
// _LemmaPreserveTactic.polymorphicSourceKey for the storage contract.
func buildSpecializedLemma(lemma core.Prop, m map[string]string, goal core.Prop) (specialized core.Prop, goalLetters core.VarTypePredicate, err error) {
	if len(m) == 0 {
		return lemma, utils.EmptyPredicate[core.VarType], nil
	}

	available := collectLemmaTypeVarNames(lemma)
	spelledByGoal := collectLemmaTypeVarNames(goal)
	fixed := map[string]bool{}

	substs := make([]core.TypeSubst, 0, len(m))
	for name, spelling := range m {
		if !available[name] {
			return nil, nil, fmt.Errorf(
				"type_specialize: type-variable %q not found in lemma; available: %v",
				name, sortedKeys(available))
		}
		t, perr := dsl.ParseTypeText(spelling)
		if perr != nil {
			return nil, nil, fmt.Errorf(
				"type_specialize: cannot parse type %q for variable %q: %w",
				spelling, name, perr)
		}
		for _, v := range t.TypeVars() {
			if spelledByGoal[string(v.Name())] {
				fixed[string(v.Name())] = true
			}
		}
		substs = append(substs, core.MakeTypeSubst(
			core.MakeVarType(core.TypeName(name)), t))
	}

	goalLetters = func(v core.VarType) bool { return fixed[string(v.Name())] }
	return core.PropTypeInst(lemma, substs...), goalLetters, nil
}

// collectLemmaTypeVarNames returns the set of free type-variable names
// appearing anywhere in the lemma's hypotheses or conclusion. Used for
// validating agent-supplied `type_specialize` keys.
func collectLemmaTypeVarNames(p core.Prop) map[string]bool {
	out := map[string]bool{}
	collect := func(v core.VarType) bool {
		out[string(v.Name())] = true
		return false // false = "keep visiting"; we want every type-var
	}
	pred := core.VarTypePredicate(collect)
	// TermAnyTypeVar short-circuits on `true`; we return `false` so the
	// walk visits every type-var. The bool return is discarded.
	_ = ext.TermAnyTypeVar(p.Conclusion(), pred)
	for i := range p.NumHyps() {
		_ = ext.TermAnyTypeVar(p.Hyp(i), pred)
	}
	return out
}

func sortedKeys(m map[string]bool) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}
