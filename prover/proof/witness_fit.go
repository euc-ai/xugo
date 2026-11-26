// witness_fit.go — how a witness is read against the binder it
// grounds: the one rule the session's term_specialize and a reading's
// witness tuple share, and the refusal where it fits no way.

package proof

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/solver/ematch"
)

// FitWitness reads a witness at the binder's type before the door's own
// match: a witness that is a bare polymorphic constant (`∅`, `𝕌`,
// `identity_map`) carries the constant's fresh letters, and the binder
// says at which type it is meant, as Go's TermAs reads the same text
// at its phantom's type (dsl.ReadTermAt). env is the type reading the
// door has made so far: a binder letter it binds is read at that
// binding and binds no further; the letters instantiable admits bind
// on the binder's side, every other letter is rigid. The witness comes
// back retyped at its fresh letters' bindings, for the door's match to
// read as it reads any witness; ok is false where it fits no reading.
func FitWitness(binder core.HolType, witness core.Term, instantiable core.VarTypePredicate, env []core.TypeSubst) (core.Term, bool) {
	bound := map[core.TypeName]bool{}
	for _, s := range env {
		bound[s.VarType.Name()] = true
	}
	open := func(v core.VarType) bool { return instantiable(v) && !bound[v.Name()] }
	return dsl.ReadTermAt(witness, binder.Substitute(nonIdentityTypeSubst(env)...), open)
}

// ReadingFixedLetters is the predicate of the type letters a reading's
// hypotheses spell: fixed in every reading of it, so that a witness
// tuple grounds the reading under the same resident facts.
func ReadingFixedLetters(reading Prop) core.VarTypePredicate {
	fixed := map[core.TypeName]bool{}
	for _, hyp := range reading.Hyps() {
		_ = ext.TermAnyTypeVar(hyp, func(v core.VarType) bool { fixed[v.Name()] = true; return false })
	}
	return func(v core.VarType) bool { return fixed[v.Name()] }
}

// witnessMisfit names the first witness of the tuple, read in binder
// order, that fits its binder no way: the binder with its type, the
// witness with its, and the tie that pins a fresh letter the witness
// carries. Empty where every witness fits its own binder (the tuple
// misfits as a whole: too long, or two readings of it disagree).
func witnessMisfit(reading Prop, witnesses []Term, instantiable core.VarTypePredicate) string {
	binders, _ := ematch.StripGuardedForalls(reading.AsProp().Conclusion())
	var env []core.TypeSubst
	for i, w := range witnesses {
		if i >= len(binders) {
			return ""
		}
		b := binders[i]
		fitted, fits := FitWitness(b.Type(), w, instantiable, env)
		if fits && core.MatchTypeInto(b.Type(), fitted.Type(), instantiable, &env) {
			continue
		}
		return fmt.Sprintf(": the witness %s of type %s does not fit the binder %s:%s%s",
			ext.PrintTerm(w), ext.FormatType(w.Type()), b.Name(), ext.FormatType(b.Type()), UnpinnedWitnessRepair(w, b.Type()))
	}
	return ""
}

// UnpinnedWitnessRepair is the edit that pins a witness's fresh letter
// — a bare polymorphic constant's, which no argument, partner or binder
// fixed — at the binder's type; empty for a witness carrying none.
func UnpinnedWitnessRepair(witness Term, binder core.HolType) string {
	unpinned := dsl.UnpinnedLettersIn(witness)
	if len(unpinned) == 0 {
		return ""
	}
	rows := make([]string, len(unpinned))
	for i, u := range unpinned {
		rows[i] = fmt.Sprintf("%s's %s — write %s⟨%s:τ⟩ at the type the binder %s wants",
			u.Const, u.Letter, u.Const, u.Letter, ext.FormatType(binder))
	}
	return " — the witness leaves a letter unpinned: " + strings.Join(rows, "; ")
}
