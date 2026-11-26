package proof

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/typematch"
)

// byBareInstall is a bare polymorphic premise as one attempt of a By
// installed it: the law, the leaf it was adapted to — the leaf as it
// stood before the install — and the one instance that became resident.
type byBareInstall struct {
	premise        string
	law, installed Prop
	leaf           Prop
}

// installReadingNote is the note a failed By carries for each bare
// polymorphic premise whose install misses a constant the leaf holds
// while another instance the leaf offers reads it (typematch.
// InstanceReadings): the law's constants disagree about the instance,
// no instance reads them all, and the closer received one the step may
// not have meant. It names the instance installed, the constants it
// misses and each instance offered, spelled as the pin that selects it.
// Empty for a By with no such premise.
func (step _ByStep) installReadingNote() string {
	var b strings.Builder
	for _, in := range step.bareInstalls {
		install, offered := typematch.InstanceReadings(in.law, in.leaf, in.installed)
		if len(offered) == 0 {
			continue
		}
		at := "its own letters"
		if !in.installed.AlphaEquals(in.law) {
			at = typeInstanceText(in.law, in.installed)
		}
		fmt.Fprintf(&b, "\npremise %s is a polymorphic law installed at ONE type instance, %s, and the leaf holds its %s "+
			"at no type that instance gives them: as installed it says nothing of the leaf's terms in them. "+
			"The leaf offers the law at:", in.premise, at, constantNames(install.Misses))
		for _, o := range offered {
			fmt.Fprintf(&b, "\n  %s: reads %s", typeInstanceText(in.law, o.Instance), constantNames(o.Reads))
			if len(o.Misses) > 0 {
				fmt.Fprintf(&b, ", not %s", constantNames(o.Misses))
			}
		}
		b.WriteString("\nNo instance reads every constant of the law the leaf holds, so the install is where the law's " +
			"anchors first met the leaf, and the closer receives the install alone. Pin the instance this step " +
			"needs: type_specialize on the premise in a session; in Go <Entry>.Inst[τ]() for one letter, " +
			"<Entry>.Inst(TypeBinder.BindA[τ](), …) for several, or a typed .At.")
	}
	return b.String()
}

func constantNames(names []core.TermName) string {
	out := make([]string, len(names))
	for i, n := range names {
		out[i] = string(n)
	}
	return strings.Join(out, ", ")
}
